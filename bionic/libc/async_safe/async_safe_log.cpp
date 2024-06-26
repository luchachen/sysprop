/*
 * Copyright (C) 2010 The Android Open Source Project
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *  * Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *  * Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in
 *    the documentation and/or other materials provided with the
 *    distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 * COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
 * BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS
 * OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED
 * AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT
 * OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#include <assert.h>
#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <linux/net.h>
#include <pthread.h>
#include <stdarg.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/types.h>
#include <sys/uio.h>
#include <sys/un.h>
#include <time.h>
#include <unistd.h>

#include <async_safe/log.h>

#include "private/CachedProperty.h"
#include "private/ErrnoRestorer.h"
#include "private/ScopedPthreadMutexLocker.h"
void __assert(const char* file, int line, const char* failed_expression) {
  async_safe_fatal("%s:%d: assertion \"%s\" failed", file, line, failed_expression);
}

struct BufferOutputStream {
 public:
  BufferOutputStream(char* buffer, size_t size) : total(0), pos_(buffer), avail_(size) {
    if (avail_ > 0) pos_[0] = '\0';
  }
  ~BufferOutputStream() = default;

  void Send(const char* data, int len) {
    if (len < 0) {
      len = strlen(data);
    }
    total += len;

    if (avail_ <= 1) {
      // No space to put anything else.
      return;
    }

    if (static_cast<size_t>(len) >= avail_) {
      len = avail_ - 1;
    }
    memcpy(pos_, data, len);
    pos_ += len;
    pos_[0] = '\0';
    avail_ -= len;
  }

  size_t total;

 private:
  char* pos_;
  size_t avail_;
};

struct FdOutputStream {
 public:
  explicit FdOutputStream(int fd) : total(0), fd_(fd) {}

  void Send(const char* data, int len) {
    if (len < 0) {
      len = strlen(data);
    }
    total += len;

    while (len > 0) {
      ssize_t bytes = TEMP_FAILURE_RETRY(write(fd_, data, len));
      if (bytes == -1) {
        return;
      }
      data += bytes;
      len -= bytes;
    }
  }

  size_t total;

 private:
  int fd_;
};

/*** formatted output implementation
 ***/

/* Parse a decimal string from 'format + *ppos',
 * return the value, and writes the new position past
 * the decimal string in '*ppos' on exit.
 *
 * NOTE: Does *not* handle a sign prefix.
 */
static unsigned parse_decimal(const char* format, int* ppos) {
  const char* p = format + *ppos;
  unsigned result = 0;

  for (;;) {
    int ch = *p;
    unsigned d = static_cast<unsigned>(ch - '0');

    if (d >= 10U) {
      break;
    }

    result = result * 10 + d;
    p++;
  }
  *ppos = p - format;
  return result;
}

// Writes number 'value' in base 'base' into buffer 'buf' of size 'buf_size' bytes.
// Assumes that buf_size > 0.
static void format_unsigned(char* buf, size_t buf_size, uint64_t value, int base, bool caps) {
  char* p = buf;
  char* end = buf + buf_size - 1;

  // Generate digit string in reverse order.
  while (value) {
    unsigned d = value % base;
    value /= base;
    if (p != end) {
      char ch;
      if (d < 10) {
        ch = '0' + d;
      } else {
        ch = (caps ? 'A' : 'a') + (d - 10);
      }
      *p++ = ch;
    }
  }

  // Special case for 0.
  if (p == buf) {
    if (p != end) {
      *p++ = '0';
    }
  }
  *p = '\0';

  // Reverse digit string in-place.
  size_t length = p - buf;
  for (size_t i = 0, j = length - 1; i < j; ++i, --j) {
    char ch = buf[i];
    buf[i] = buf[j];
    buf[j] = ch;
  }
}

static void format_integer(char* buf, size_t buf_size, uint64_t value, char conversion) {
  // Decode the conversion specifier.
  int is_signed = (conversion == 'd' || conversion == 'i' || conversion == 'o');
  int base = 10;
  if (conversion == 'x' || conversion == 'X') {
    base = 16;
  } else if (conversion == 'o') {
    base = 8;
  }
  bool caps = (conversion == 'X');

  if (is_signed && static_cast<int64_t>(value) < 0) {
    buf[0] = '-';
    buf += 1;
    buf_size -= 1;
    value = static_cast<uint64_t>(-static_cast<int64_t>(value));
  }
  format_unsigned(buf, buf_size, value, base, caps);
}

template <typename Out>
static void SendRepeat(Out& o, char ch, int count) {
  char pad[8];
  memset(pad, ch, sizeof(pad));

  const int pad_size = static_cast<int>(sizeof(pad));
  while (count > 0) {
    int avail = count;
    if (avail > pad_size) {
      avail = pad_size;
    }
    o.Send(pad, avail);
    count -= avail;
  }
}

/* Perform formatted output to an output target 'o' */
template <typename Out>
static void out_vformat(Out& o, const char* format, va_list args) {
  int nn = 0;

  for (;;) {
    int mm;
    int padZero = 0;
    int padLeft = 0;
    char sign = '\0';
    int width = -1;
    int prec = -1;
    bool alternate = false;
    size_t bytelen = sizeof(int);
    int slen;
    char buffer[32]; /* temporary buffer used to format numbers */

    char c;

    /* first, find all characters that are not 0 or '%' */
    /* then send them to the output directly */
    mm = nn;
    do {
      c = format[mm];
      if (c == '\0' || c == '%') break;
      mm++;
    } while (1);

    if (mm > nn) {
      o.Send(format + nn, mm - nn);
      nn = mm;
    }

    /* is this it ? then exit */
    if (c == '\0') break;

    /* nope, we are at a '%' modifier */
    nn++;  // skip it

    /* parse flags */
    for (;;) {
      c = format[nn++];
      if (c == '\0') { /* single trailing '%' ? */
        c = '%';
        o.Send(&c, 1);
        return;
      } else if (c == '0') {
        padZero = 1;
        continue;
      } else if (c == '-') {
        padLeft = 1;
        continue;
      } else if (c == ' ' || c == '+') {
        sign = c;
        continue;
      } else if (c == '#') {
        alternate = true;
        continue;
      }
      break;
    }

    /* parse field width */
    if ((c >= '0' && c <= '9')) {
      nn--;
      width = static_cast<int>(parse_decimal(format, &nn));
      c = format[nn++];
    }

    /* parse precision */
    if (c == '.') {
      prec = static_cast<int>(parse_decimal(format, &nn));
      c = format[nn++];
    }

    /* length modifier */
    switch (c) {
      case 'h':
        bytelen = sizeof(short);
        if (format[nn] == 'h') {
          bytelen = sizeof(char);
          nn += 1;
        }
        c = format[nn++];
        break;
      case 'l':
        bytelen = sizeof(long);
        if (format[nn] == 'l') {
          bytelen = sizeof(long long);
          nn += 1;
        }
        c = format[nn++];
        break;
      case 'z':
        bytelen = sizeof(size_t);
        c = format[nn++];
        break;
      case 't':
        bytelen = sizeof(ptrdiff_t);
        c = format[nn++];
        break;
      default:;
    }

    /* conversion specifier */
    const char* str = buffer;
    if (c == 's') {
      /* string */
      str = va_arg(args, const char*);
    } else if (c == 'c') {
      /* character */
      /* NOTE: char is promoted to int when passed through the stack */
      buffer[0] = static_cast<char>(va_arg(args, int));
      buffer[1] = '\0';
    } else if (c == 'p') {
      uint64_t value = reinterpret_cast<uintptr_t>(va_arg(args, void*));
      buffer[0] = '0';
      buffer[1] = 'x';
      format_integer(buffer + 2, sizeof(buffer) - 2, value, 'x');
    } else if (c == 'm') {
      char buf[256];
      str = strerror_r(errno, buf, sizeof(buf));
    } else if (c == 'd' || c == 'i' || c == 'o' || c == 'u' || c == 'x' || c == 'X') {
      /* integers - first read value from stack */
      uint64_t value;
      int is_signed = (c == 'd' || c == 'i' || c == 'o');

      /* NOTE: int8_t and int16_t are promoted to int when passed
       *       through the stack
       */
      switch (bytelen) {
        case 1:
          value = static_cast<uint8_t>(va_arg(args, int));
          break;
        case 2:
          value = static_cast<uint16_t>(va_arg(args, int));
          break;
        case 4:
          value = va_arg(args, uint32_t);
          break;
        case 8:
          value = va_arg(args, uint64_t);
          break;
        default:
          return; /* should not happen */
      }

      /* sign extension, if needed */
      if (is_signed) {
        int shift = 64 - 8 * bytelen;
        value = static_cast<uint64_t>((static_cast<int64_t>(value << shift)) >> shift);
      }

      if (alternate && value != 0 && (c == 'x' || c == 'o')) {
        if (c == 'x') {
          buffer[0] = '0';
          buffer[1] = 'x';
          format_integer(buffer + 2, sizeof(buffer) - 2, value, c);
        } else {
          buffer[0] = '0';
          format_integer(buffer + 1, sizeof(buffer) - 1, value, c);
        }
      } else {
        /* format the number properly into our buffer */
        format_integer(buffer, sizeof(buffer), value, c);
      }
    } else if (c == '%') {
      buffer[0] = '%';
      buffer[1] = '\0';
    } else {
      __assert(__FILE__, __LINE__, "conversion specifier unsupported");
    }

    if (str == nullptr) {
      str = "(null)";
    }

    /* if we are here, 'str' points to the content that must be
     * outputted. handle padding and alignment now */

    slen = strlen(str);

    if (sign != '\0' || prec != -1) {
      __assert(__FILE__, __LINE__, "sign/precision unsupported");
    }

    if (slen < width && !padLeft) {
      char padChar = padZero ? '0' : ' ';
      SendRepeat(o, padChar, width - slen);
    }

    o.Send(str, slen);

    if (slen < width && padLeft) {
      char padChar = padZero ? '0' : ' ';
      SendRepeat(o, padChar, width - slen);
    }
  }
}

int async_safe_format_buffer_va_list(char* buffer, size_t buffer_size, const char* format,
                                     va_list args) {
  BufferOutputStream os(buffer, buffer_size);
  out_vformat(os, format, args);
  return os.total;
}

int async_safe_format_buffer(char* buffer, size_t buffer_size, const char* format, ...) {
  va_list args;
  va_start(args, format);
  int buffer_len = async_safe_format_buffer_va_list(buffer, buffer_size, format, args);
  va_end(args);
  return buffer_len;
}

int async_safe_format_fd_va_list(int fd, const char* format, va_list args) {
  FdOutputStream os(fd);
  out_vformat(os, format, args);
  return os.total;
}

int async_safe_format_fd(int fd, const char* format, ...) {
  va_list args;
  va_start(args, format);
  int result = async_safe_format_fd_va_list(fd, format, args);
  va_end(args);
  return result;
}

static inline int write_stderr(const char* tag, const char* msg) {
  iovec vec[4];
  vec[0].iov_base = const_cast<char*>(tag);
  vec[0].iov_len = strlen(tag);
  vec[1].iov_base = const_cast<char*>(": ");
  vec[1].iov_len = 2;
  vec[2].iov_base = const_cast<char*>(msg);
  vec[2].iov_len = strlen(msg);
  vec[3].iov_base = const_cast<char*>("\n");
  vec[3].iov_len = 1;

  int result = TEMP_FAILURE_RETRY(writev(STDERR_FILENO, vec, 4));
  return result;
}

int async_safe_write_log(int priority, const char* tag, const char* msg) {
    // Try stderr instead.
    return write_stderr(tag, msg);
}

int async_safe_format_log_va_list(int priority, const char* tag, const char* format, va_list args) {
  ErrnoRestorer errno_restorer;
  char buffer[1024];
  BufferOutputStream os(buffer, sizeof(buffer));
  out_vformat(os, format, args);
  return async_safe_write_log(priority, tag, buffer);
}

int async_safe_format_log(int priority, const char* tag, const char* format, ...) {
  va_list args;
  va_start(args, format);
  int result = async_safe_format_log_va_list(priority, tag, format, args);
  va_end(args);
  return result;
}

void async_safe_fatal_va_list(const char* prefix, const char* format, va_list args) {
  char msg[1024];
  BufferOutputStream os(msg, sizeof(msg));

  if (prefix) {
    os.Send(prefix, strlen(prefix));
    os.Send(": ", 2);
  }

  out_vformat(os, format, args);

  // Log to stderr for the benefit of "adb shell" users and gtests.
  struct iovec iov[2] = {
      {msg, strlen(msg)}, {const_cast<char*>("\n"), 1},
  };
  TEMP_FAILURE_RETRY(writev(2, iov, 2));

  // Log to the log for the benefit of regular app developers (whose stdout and stderr are closed).
  async_safe_write_log(ANDROID_LOG_FATAL, "libc", msg);

  //android_set_abort_message(msg);
}

void async_safe_fatal_no_abort(const char* fmt, ...) {
  va_list args;
  va_start(args, fmt);
  async_safe_fatal_va_list(nullptr, fmt, args);
  va_end(args);
}
