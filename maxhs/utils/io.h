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

#include <ostream>

#ifdef GLUCOSE
#include "glucose/core/SolverTypes.h"
#include "glucose/mtl/Vec.h"
#else
#include "minisat/core/SolverTypes.h"
#include "minisat/mtl/Vec.h"
#endif

#include "maxhs/ds/Packed.h"

#ifdef GLUCOSE
namespace Minisat = Glucose;
#endif

using std::ostream;
using std::vector;

inline ostream& operator<<(ostream& os, const Minisat::Lit& l) {
  if(l == Minisat::lit_Undef) 
    os << "lit_Undef";
  else if (l == Minisat::lit_Error)
    os << "lit_Error";
  else
    os << (Minisat::sign(l) ? "-" : "") << (Minisat::var(l)+1);
  return os;
}

inline ostream& operator<<(ostream& os, const Minisat::lbool& l) {
  os << (
    (l == Minisat::l_Undef) ? "U" : 
          (l == Minisat::l_True ? "T" : "F")
    );
  return os;
}

template<typename T>
ostream& operator<<(ostream& os, const vector<T>& v) {
  os << "[ ";
  for(const auto& i : v) 
    os << i << " ";
  os << "] (" << v.size() << ")";
  return os;
}

template<typename T>
ostream& operator<<(ostream& os, const Minisat::vec<T>& v) {
  os << "[ ";
  for(int i = 0; i < v.size(); i++) 
    os << v[i] << " ";
  os << "] (" << v.size() << ")";
  return os;
}

template<typename T>
ostream& operator<<(ostream& os, const Minisat::LSet& v) {
  os << "[ ";
  for(int i = 0; i < v.size(); i++)
    os << v[i] << " ";
  os << "] (" << v.size() << ")";
  return os;
}

template<typename T>
ostream& operator<<(ostream& os, const Packed_vecs<T>& pv) {
  for(const auto& v : pv) {
    for(const auto& item : v) 
      os << item << " ";
    os << "0 \n";
  }
  return os;
}
#endif
