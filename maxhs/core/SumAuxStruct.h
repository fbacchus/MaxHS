/***********[SumAuxStruct.h]
Copyright (c) 2019, Jeremias Berg, Fahiem Bacchus

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

#ifndef __SUM_AUXSTRUCT__
#define __SUM_AUXSTRUCT__

#include <iostream>
#include "maxhs/utils/io.h"
class SumManager;
#ifdef GLUCOSE
namespace Minisat = Glucose;
#endif

#ifdef GLUCOSE
#include "glucose/core/SolverTypes.h"
#else
#include "minisat/core/SolverTypes.h"
#endif

using Minisat::Lit;
using Minisat::lit_Undef;

class SortNet;
struct SRef {
  /* class for storing revefrences to summations */
  SRef(size_t i) : idx{static_cast<int>(i)} {}
  explicit SRef(int i) : idx{i} {}
  SRef() : idx{-1} {}
  int idx;
  explicit operator int() const { return idx; }
  SortNet* operator->() const;
};
const SRef NullSRef{};

inline bool operator==(const SRef& s1, const SRef& s2) {
  return s1.idx == s2.idx;
}

inline bool operator!=(const SRef& s1, const SRef& s2) {
  return s1.idx != s2.idx;
}

inline std::ostream& operator<<(std::ostream& os, const SRef& s) {
  std::cout << "SRef(" << s.idx << ")";
  return os;
}

// auxilary struct.
struct SOut {
  // as we build sub-sums we make some of their outputs assumptions
  // this struct holds information about these output literal
  Lit out_lit;  // output lit
  SRef sr;      // reference to the SortNet out_lit is an output of
  SOut() : out_lit{lit_Undef}, sr{NullSRef} {};
  SOut(Lit o, SRef s) : out_lit{o}, sr{s} {};
};

inline std::ostream& operator<<(std::ostream& os, const SOut& s) {
  std::cout << "SOut(" << s.out_lit << "," << s.sr << ")";
  return os;
}

#endif
