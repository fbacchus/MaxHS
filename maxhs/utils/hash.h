/***********[hash.h]
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
#ifndef HASH_h
#define HASH_h
#include <iostream>
#include <utility>
#include <unordered_map>

#ifdef GLUCOSE
#include "glucose/core/SolverTypes.h"
#else
#include "minisat/core/SolverTypes.h"
#endif

#include "maxhs/utils/io.h"

#ifdef GLUCOSE
namespace Minisat = Glucose;
#endif

using Minisat::Lit;
using Minisat::Var;
using std::pair;
using std::make_pair;
using std::swap;
using std::unordered_map;
extern  uint32_t rnd_table[256];


//hash a container range
template<class RAIterator>
uint32_t hashCode(RAIterator first, RAIterator last)
{
  uint32_t code = 0;
  
  /*cout << "hashing [";
  for(auto it = first; it != last; ++it) 
    cout << *it << ", ";
    cout << "] (" << last-first << ")\n";*/

  for(auto it = first; it != last; ++it) {
    auto item = *it;
    char* p = (char*) (&item);
    for(size_t i = 0; i < sizeof(*first); i++) {
      code += rnd_table[(uint8_t)*p];
      //cout << "xor-ing with " << (uint32_t) *p << "; ";
      p++;
    }
  }
  //cout << "\nFinal hash code: " << code << "\n";
  return code;
}

//hash a structure
template<class C>
uint32_t hashCode(const C c)
{
  uint32_t code = 0;
  char* p = (char*) (&c);
  for(size_t i = 0; i < sizeof(c); i++) {
    code += rnd_table[(uint8_t)*p];
    p++;
  }
  return code;
}

template<class C> 
class BinClsHash {
 public:
  size_t operator() (const pair<C, C> bin) const {
    return hashCode(bin);
  }
};

class BinClsTable {
  //has binary clauss 
 public:
  using BinMap = unordered_map<pair<Var, Var>, vector<Lit>, BinClsHash<Var>>;

 void insert(Lit l1, Lit l2);  //insert a binary clause 

  //return pointer to vector of binaries that contain v1 and v2.
  //The binaries are stored in sequence, every two elements of the
  //vector is a binary clause. If pointer is nil no binaries found
  vector<Lit>* get(Var v1, Var v2); 
  
  BinMap::iterator begin() { return bins.begin(); }
  BinMap::iterator end() { return bins.end(); }

 private:
  BinMap bins;

  pair<Var, Var> mkKey(Lit l1, Lit l2) {
    return mkKey(var(l1), var(l2));
  }

  pair<Var, Var> mkKey(Var v1, Var v2) {
    if(v1 > v2) swap(v1, v2);
    return make_pair(v1, v2);
  }
};

#endif
