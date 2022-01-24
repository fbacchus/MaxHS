/***********[io.h]
Copyright (c) 2012-2013 Jessica Davies, Fahiem Bacchus

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

***********/
#ifndef IO_h
#define IO_h

#include <iomanip>
#include <ostream>

#ifdef GLUCOSE
#include "glucose/core/SolverTypes.h"
#include "glucose/mtl/Vec.h"
#else
#include "minisat/core/SolverTypes.h"
#include "minisat/mtl/Vec.h"
#endif

#include "maxhs/core/MaxSolverTypes.h"
#include "maxhs/ds/Packed.h"
#include "maxhs/utils/Params.h"

#ifdef GLUCOSE
namespace Minisat = Glucose;
#endif

// Floating point formatting (Stroustrup C++11 4th ediction)
class FloatFormat;

struct Bound_form {
  const FloatFormat& f;
  long double val;
};

class FloatFormat {
  friend std::ostream& operator<<(std::ostream&, const Bound_form&);
  int prc;
  std::ios_base::fmtflags fmt;
 public:
  explicit FloatFormat(int p = 4, std::ios_base::fmtflags f = std::ios_base::fixed) : prc{p}, fmt{f} {}
  Bound_form operator()(long double d) const { return Bound_form{*this, d}; }

  FloatFormat& scientific() {
    fmt = std::ios_base::scientific;
    return *this;
  }
  FloatFormat& fixed() {
    fmt = std::ios_base::fixed;
    return *this;
  }
  FloatFormat& general() {
    fmt = {};
    return *this;
  }
  FloatFormat& precision(int p) {
    prc = p;
    return *this;
  }
};

inline std::ostream& operator<<(std::ostream& os, const Bound_form& bf) {
  auto p = os.precision();
  os.precision(bf.f.prc);
  auto flags = os.flags();
  os.setf(bf.f.fmt, std::ios_base::floatfield);
  os << bf.val;
  os.precision(p);
  os.setf(flags);
  return os;
}
extern FloatFormat wt_fmt;
const FloatFormat time_fmt{};
const FloatFormat fix4_fmt{};


inline std::ostream& operator<<(std::ostream& os, const Minisat::Lit& l) {
  if (l == Minisat::lit_Undef)
    os << "lit_Undef";
  else if (l == Minisat::lit_Error)
    os << "lit_Error";
  else
    os << (Minisat::sign(l) ? "-" : "") << (Minisat::var(l) + 1);
  return os;
}

inline std::ostream& operator<<(std::ostream& os, const Minisat::lbool& l) {
  os << ((l == Minisat::l_Undef) ? "U" : (l == Minisat::l_True ? "T" : "F"));
  return os;
}

template <typename T>
std::ostream& operator<<(std::ostream& os, const std::vector<T>& v) {
  os << "[ ";
  for (size_t i = 0; i < v.size() && i < 30; ++i) os << v[i] << " ";
  if (v.size() > 30) os << "...";
  os << "] (" << v.size() << ")";
  return os;
}

template <typename T>
std::ostream& operator<<(std::ostream& os, const Minisat::vec<T>& v) {
  os << "[ ";
  for (int i = 0; i < v.size() && i < 30; i++) os << v[i] << " ";
  if (v.size() > 30) os << "...";
  os << "] (" << v.size() << ")";
  return os;
}

template <typename T>
std::ostream& operator<<(std::ostream& os, const Packed_vecs<T>& pv) {
  for (const auto& v : pv) {
    for (const auto& item : v) os << item << " ";
    os << "0 \n";
  }
  return os;
}

inline void log_(std::ostream& os) {
  os << '\n';
}

template <typename T, typename... Ts> 
void log_(std::ostream& os, T item, Ts... items) {
  os << item;
  log_(os, items...);
}

template <typename T, typename... Ts> 
void log(int level, T item, Ts... items) {
  if(params.verbosity >= level)
    log_(std::cout, item, items...);
}

template <typename T, typename... Ts> 
void log_if(bool cond, int level, T item, Ts... items) {
  if(cond && params.verbosity >= level)
    log_(std::cout, item, items...);
}
#endif
