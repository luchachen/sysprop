/*
 * Copyright (C) 2008 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include "propd.h"

#include <dirent.h>
#include <fcntl.h>
#include <paths.h>
#include <pthread.h>
#include <signal.h>
#include <stdlib.h>
#include <string.h>
#include <sys/eventfd.h>
#include <sys/mount.h>
#include <sys/signalfd.h>
#include <sys/types.h>
#include <sys/utsname.h>
#include <sys/wait.h>
#include <unistd.h>

#define _REALLY_INCLUDE_SYS__SYSTEM_PROPERTIES_H_
#include <sys/_system_properties.h>

#include <filesystem>
#include <fstream>
#include <functional>
#include <iostream>
#include <map>
#include <memory>
#include <mutex>
#include <optional>
#include <thread>
#include <vector>

#include <android-base/chrono_utils.h>
#include <android-base/file.h>
#include <android-base/logging.h>
#include <android-base/parseint.h>
#include <android-base/properties.h>
#include <android-base/stringprintf.h>
#include <android-base/strings.h>
#include <android-base/thread_annotations.h>
#include <android-base/scopeguard.h>

#include "epoll.h"
#include "property_service.h"
#include "proto_utils.h"
#include "property_service.pb.h"
#include "util.h"

#include "sigchld_handler.h"

using namespace std::chrono_literals;
using namespace std::string_literals;

using android::base::boot_clock;
using android::base::ConsumePrefix;
using android::base::GetProperty;
using android::base::ReadFileToString;
using android::base::SetProperty;
using android::base::StringPrintf;
using android::base::Timer;
using android::base::Trim;
using android::base::unique_fd; using android::base::make_scope_guard;

namespace android {
namespace init {

static int property_triggers_enabled = 0;

static int sigterm_fd = -1;
static int property_fd = -1;

static const int MIN_OOM_SCORE_ADJUST = -1000;
static const int MAX_OOM_SCORE_ADJUST = 1000;
// service with default score is unkillable
static const int DEFAULT_OOM_SCORE_ADJUST = MIN_OOM_SCORE_ADJUST;


// Init epolls various FDs to wait for various inputs.  It previously waited on property changes
// with a blocking socket that contained the information related to the change, however, it was easy
// to fill that socket and deadlock the system.  Now we use locks to handle the property changes
// directly in the property thread, however we still must wake the epoll to inform init that there
// is a change to process, so we use this FD.  It is non-blocking, since we do not care how many
// times WakeMainInitThread() is called, only that the epoll will wake.
static int wake_main_thread_fd = -1;
static void InstallInitNotifier(Epoll* epoll) {
    wake_main_thread_fd = eventfd(0, EFD_CLOEXEC);
    if (wake_main_thread_fd == -1) {
        PLOG(FATAL) << "Failed to create eventfd for waking init";
    }
    auto clear_eventfd = [] {
        uint64_t counter;
        TEMP_FAILURE_RETRY(read(wake_main_thread_fd, &counter, sizeof(counter)));
    };

    if (auto result = epoll->RegisterHandler(wake_main_thread_fd, clear_eventfd); !result.ok()) {
        LOG(FATAL) << result.error();
    }
}

static void WakeMainInitThread() {
    uint64_t counter = 1;
    TEMP_FAILURE_RETRY(write(wake_main_thread_fd, &counter, sizeof(counter)));
}

static class PropWaiterState {
  public:
    bool StartWaiting(const char* name, const char* value) {
        auto lock = std::lock_guard{lock_};
        if (waiting_for_prop_) {
            return false;
        }
        if (GetProperty(name, "") != value) {
            // Current property value is not equal to expected value
            wait_prop_name_ = name;
            wait_prop_value_ = value;
            waiting_for_prop_.reset(new Timer());
        } else {
            LOG(INFO) << "start_waiting_for_property(\"" << name << "\", \"" << value
                      << "\"): already set";
        }
        return true;
    }

    void ResetWaitForProp() {
        auto lock = std::lock_guard{lock_};
        ResetWaitForPropLocked();
    }

    void CheckAndResetWait(const std::string& name, const std::string& value) {
        auto lock = std::lock_guard{lock_};
        // We always record how long init waited for ueventd to tell us cold boot finished.
        // If we aren't waiting on this property, it means that ueventd finished before we even
        // started to wait.
        if (name == kColdBootDoneProp) {
            auto time_waited = waiting_for_prop_ ? waiting_for_prop_->duration().count() : 0;
            std::thread([time_waited] {
                SetProperty("ro.boottime.init.cold_boot_wait", std::to_string(time_waited));
            }).detach();
        }

        if (waiting_for_prop_) {
            if (wait_prop_name_ == name && wait_prop_value_ == value) {
                LOG(INFO) << "Wait for property '" << wait_prop_name_ << "=" << wait_prop_value_
                          << "' took " << *waiting_for_prop_;
                ResetWaitForPropLocked();
                WakeMainInitThread();
            }
        }
    }

    // This is not thread safe because it releases the lock when it returns, so the waiting state
    // may change.  However, we only use this function to prevent running commands in the main
    // thread loop when we are waiting, so we do not care about false positives; only false
    // negatives.  StartWaiting() and this function are always called from the same thread, so false
    // negatives are not possible and therefore we're okay.
    bool MightBeWaiting() {
        auto lock = std::lock_guard{lock_};
        return static_cast<bool>(waiting_for_prop_);
    }

  private:
    void ResetWaitForPropLocked() EXCLUSIVE_LOCKS_REQUIRED(lock_) {
        wait_prop_name_.clear();
        wait_prop_value_.clear();
        waiting_for_prop_.reset();
    }

    std::mutex lock_;
    GUARDED_BY(lock_) std::unique_ptr<Timer> waiting_for_prop_{nullptr};
    GUARDED_BY(lock_) std::string wait_prop_name_;
    GUARDED_BY(lock_) std::string wait_prop_value_;

} prop_waiter_state;

bool start_waiting_for_property(const char* name, const char* value) {
    return prop_waiter_state.StartWaiting(name, value);
}

void ResetWaitForProp() {
    prop_waiter_state.ResetWaitForProp();
}

void PropertyChanged(const std::string& name, const std::string& value) {
    // If the property is sys.powerctl, we bypass the event queue and immediately handle it.
    // This is to ensure that init will always and immediately shutdown/reboot, regardless of
    // if there are other pending events to process or if init is waiting on an exec service or
    // waiting on a property.
    // In non-thermal-shutdown case, 'shutdown' trigger will be fired to let device specific
    // commands to be executed.
    if (name == "sys.powerctl") {
        //TODO
        //trigger_shutdown(value);
    }

    if (property_triggers_enabled) {
        //TODO
        //ActionManager::GetInstance().QueuePropertyChange(name, value);
        WakeMainInitThread();
    }

    prop_waiter_state.CheckAndResetWait(name, value);
}


static pid_t ReapOneProcess() {
    siginfo_t siginfo = {};
    // This returns a zombie pid or informs us that there are no zombies left to be reaped.
    // It does NOT reap the pid; that is done below.
    if (TEMP_FAILURE_RETRY(waitid(P_ALL, 0, &siginfo, WEXITED | WNOHANG | WNOWAIT)) != 0) {
        PLOG(ERROR) << "waitid failed";
        return 0;
    }

    const pid_t pid = siginfo.si_pid;
    if (pid == 0) {
        DCHECK_EQ(siginfo.si_signo, 0);
        return 0;
    }

    DCHECK_EQ(siginfo.si_signo, SIGCHLD);

    // At this point we know we have a zombie pid, so we use this scopeguard to reap the pid
    // whenever the function returns from this point forward.
    // We do NOT want to reap the zombie earlier as in Service::Reap(), we kill(-pid, ...) and we
    // want the pid to remain valid throughout that (and potentially future) usages.
    auto reaper = make_scope_guard([pid] { TEMP_FAILURE_RETRY(waitpid(pid, nullptr, WNOHANG)); });

    //service->Reap(siginfo);

    return pid;
}

std::set<pid_t> ReapAnyOutstandingChildren() {
    std::set<pid_t> reaped_pids;
    for (;;) {
        const pid_t pid = ReapOneProcess();
        if (pid <= 0) {
            return reaped_pids;
        }
        reaped_pids.emplace(pid);
    }
}


static int ThreadCount() {
    std::unique_ptr<DIR, decltype(&closedir)> dir(opendir("/proc/self/task"), closedir);
    if (!dir) {
        return -1;
    }

    int count = 0;
    dirent* entry;
    while ((entry = readdir(dir.get())) != nullptr) {
        if (entry->d_name[0] != '.') {
            count++;
        }
    }
    return count;
}

// Must be called BEFORE any threads are created. See also the sigprocmask() man page.
static ::android::base::unique_fd CreateSigchldFd(){
    CHECK_EQ(ThreadCount(), 1);
    sigset_t mask;
    sigemptyset(&mask);
    sigaddset(&mask, SIGCHLD);
    if (sigprocmask(SIG_BLOCK, &mask, nullptr) < 0) {
        PLOG(FATAL) << "Failed to block SIGCHLD";
    }

    return unique_fd(signalfd(-1, &mask, SFD_CLOEXEC));
}

static int GetSigchldFd() {
    static int sigchld_fd = CreateSigchldFd().release();
    return sigchld_fd;
}


static void HandleSigtermSignal(const signalfd_siginfo& siginfo) {
    if (siginfo.ssi_pid != 0) {
        // Drop any userspace SIGTERM requests.
        LOG(DEBUG) << "Ignoring SIGTERM from pid " << siginfo.ssi_pid;
        return;
    }

    //HandlePowerctlMessage("shutdown,container");
}

static void HandleSignalFd(int signal) {
    signalfd_siginfo siginfo;
    const int signal_fd = signal == SIGCHLD ? GetSigchldFd() : sigterm_fd;
    ssize_t bytes_read = TEMP_FAILURE_RETRY(read(signal_fd, &siginfo, sizeof(siginfo)));
    if (bytes_read != sizeof(siginfo)) {
        PLOG(ERROR) << "Failed to read siginfo from signal_fd";
        return;
    }

    switch (siginfo.ssi_signo) {
        case SIGCHLD:
            ReapAnyOutstandingChildren();
            break;
        case SIGTERM:
            HandleSigtermSignal(siginfo);
            break;
        default:
            LOG(ERROR) << "signal_fd: received unexpected signal " << siginfo.ssi_signo;
            break;
    }
}

static void UnblockSignals() {
    struct sigaction act;
    memset(&act, 0, sizeof(struct sigaction));
    act.sa_handler = SIG_DFL;
    sigaction(SIGCHLD, &act, nullptr);

    sigset_t mask;
    sigemptyset(&mask);
    sigaddset(&mask, SIGCHLD);
    sigaddset(&mask, SIGTERM);

    if (sigprocmask(SIG_UNBLOCK, &mask, nullptr) == -1) {
        PLOG(FATAL) << "failed to unblock signals for PID " << getpid();
    }
}

static Result<void> RegisterSignalFd(Epoll* epoll, int signal, int fd) {
    return epoll->RegisterHandler(
            fd, [signal]() { HandleSignalFd(signal); }, EPOLLIN | EPOLLPRI);
}

static Result<int> CreateAndRegisterSignalFd(Epoll* epoll, int signal) {
    sigset_t mask;
    sigemptyset(&mask);
    sigaddset(&mask, signal);
    if (sigprocmask(SIG_BLOCK, &mask, nullptr) == -1) {
        return ErrnoError() << "failed to block signal " << signal;
    }

    unique_fd signal_fd(signalfd(-1, &mask, SFD_CLOEXEC));
    if (signal_fd.get() < 0) {
        return ErrnoError() << "failed to create signalfd for signal " << signal;
    }
    OR_RETURN(RegisterSignalFd(epoll, signal, signal_fd.get()));

    return signal_fd.release();
}

static void InstallSignalFdHandler(Epoll* epoll) {
    // Applying SA_NOCLDSTOP to a defaulted SIGCHLD handler prevents the signalfd from receiving
    // SIGCHLD when a child process stops or continues (b/77867680#comment9).
    struct sigaction act;
    memset(&act, 0, sizeof(struct sigaction));
    act.sa_flags = SA_NOCLDSTOP;
    act.sa_handler = SIG_DFL;
    sigaction(SIGCHLD, &act, nullptr);

    // Register a handler to unblock signals in the child processes.
    const int result = pthread_atfork(nullptr, nullptr, &UnblockSignals);
    if (result != 0) {
        LOG(FATAL) << "Failed to register a fork handler: " << strerror(result);
    }

    Result<void> cs_result = RegisterSignalFd(epoll, SIGCHLD, GetSigchldFd());
    if (!cs_result.ok()) {
        PLOG(FATAL) << cs_result.error();
    }

    //TODO
    //if (!IsRebootCapable()) {
    {
        Result<int> cs_result = CreateAndRegisterSignalFd(epoll, SIGTERM);
        if (!cs_result.ok()) {
            PLOG(FATAL) << cs_result.error();
        }
        sigterm_fd = cs_result.value();
    }
}

void SendLoadPersistentPropertiesMessage() {
    auto init_message = InitMessage{};
    init_message.set_load_persistent_properties(true);
    if (auto result = SendMessage(property_fd, init_message); !result.ok()) {
        LOG(ERROR) << "Failed to send load persistent properties message: " << result.error();
    }
}



}  // namespace init
}  // namespace android
using namespace android::init;
int main(int argc, char** argv) {

    // No threads should be spin up until signalfd
    // is registered. If the threads are indeed required,
    // each of these threads _should_ make sure SIGCHLD signal
    // is blocked. See b/223076262
    boot_clock::time_point start_time = boot_clock::now();

    LOG(INFO) << "init second stage started!";


    // Init should not crash because of a dependence on any other process, therefore we ignore
    // SIGPIPE and handle EPIPE at the call site directly.  Note that setting a signal to SIG_IGN
    // is inherited across exec, but custom signal handlers are not.  Since we do not want to
    // ignore SIGPIPE for child processes, we set a no-op function for the signal handler instead.
    {
        struct sigaction action = {.sa_flags = SA_RESTART};
        action.sa_handler = [](int) {};
        sigaction(SIGPIPE, &action, nullptr);
    }

    // Set init and its forked children's oom_adj.
    if (auto result =
                WriteFile("/proc/self/oom_score_adj", StringPrintf("%d", DEFAULT_OOM_SCORE_ADJUST));
        !result.ok()) {
        LOG(ERROR) << "Unable to write " << DEFAULT_OOM_SCORE_ADJUST
                   << " to /proc/self/oom_score_adj: " << result.error();
    }

    // Indicate that booting is in progress to background fw loaders, etc.
    close(open("/dev/.booting", O_WRONLY | O_CREAT | O_CLOEXEC, 0000));

    // See if need to load debug props to allow adb root, when the device is unlocked.
    const char* force_debuggable_env = getenv("INIT_FORCE_DEBUGGABLE");
    bool load_debug_prop = false;
    if (force_debuggable_env) {
        load_debug_prop = "true"s == force_debuggable_env;
    }

    PropertyInit();


    Epoll epoll;
    if (auto result = epoll.Open(); !result.ok()) {
        PLOG(FATAL) << result.error();
    }

    // We always reap children before responding to the other pending functions. This is to
    // prevent a race where other daemons see that a service has exited and ask init to
    // start it again via ctl.start before init has reaped it.
    epoll.SetFirstCallback(ReapAnyOutstandingChildren);

    InstallSignalFdHandler(&epoll);
    InstallInitNotifier(&epoll);
    StartPropertyService(&property_fd);


    // Restore prio before main loop
    while (true) {
        // By default, sleep until something happens. Do not convert far_future into
        // std::chrono::milliseconds because that would trigger an overflow. The unit of boot_clock
        // is 1ns.
        const boot_clock::time_point far_future = boot_clock::time_point::max();
        boot_clock::time_point next_action_time = far_future;

        std::optional<std::chrono::milliseconds> epoll_timeout;
        if (next_action_time != far_future) {
            epoll_timeout = std::chrono::ceil<std::chrono::milliseconds>(
                    std::max(next_action_time - boot_clock::now(), 0ns));
        }
        auto epoll_result = epoll.Wait(epoll_timeout);
        if (!epoll_result.ok()) {
            LOG(ERROR) << epoll_result.error();
        }
        //TODO
        //HandleControlMessages();
    }

    return 0;
}
