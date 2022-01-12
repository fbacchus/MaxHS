/***********[TotalizerAuxStruct.h]
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

Some code and ideas from

  Open-WBO, Copyright (c) 2013-2017, Ruben Martins, Vasco Manquinho, Ines Lynce

have been used;
  Open-WBO is subject to the following LICENSE
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
***********/

#ifndef __TOTALIZER_AUXSTRUCT__
#define __TOTALIZER_AUXSTRUCT__

#include <iostream>
#include "maxhs/utils/io.h"
class TotalizerManager;
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

struct TRef {
  /* class for storing revefrences to totalizers */
  TRef(size_t i) : idx{static_cast<int>(i)} {}
  TRef(int i) : idx{i} {}
  TRef() : idx{-1} {}
  int idx;
  operator int() const { return idx; }
};
const TRef NullTRef{};

inline bool operator==(const TRef& t1, const TRef& t2) {
  return t1.idx == t2.idx;
}

inline std::ostream& operator<<(std::ostream& os, const TRef& t) {
  std::cout << "TRef(" << t.idx << ")";
  return os;
}

// auxilary struct.
struct TOut {
  // as we build sub-totalizers we make some of their outputs assumptions
  // this struct holds information about these output literal
  Lit out_lit;  // output lit
  int toutIdx;  // output index
  TRef tr;      // reference to the totalizer out_lit is an output of
  TOut() : out_lit{lit_Undef}, toutIdx{0}, tr{NullTRef} {};
  TOut(Lit o, int idx, TRef t) : out_lit{o}, toutIdx{idx}, tr{t} {};
};

inline std::ostream& operator<<(std::ostream& os, const TOut& t) {
  std::cout << "TOut(" << t.out_lit << "," << t.toutIdx << "," << t.tr << ")";
  return os;
}

#endif
