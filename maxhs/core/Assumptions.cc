/***********[Assumptions.cc]
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

#include "maxhs/core/Assumptions.h"

using Minisat::l_True;
using Minisat::l_False;
using Minisat::l_Undef;
using Minisat::lit_Undef;


void Assumps::init(const vector<Lit>& ivals, CoreType coreType) {
  //initialize assumptions with set of b-lits. coreType determines
  //what kind of conflicts we are looking for. If looking for cores,
  //add only noncore vars (conflict will be negation == core), etc.

  assumps.clear();
  for(auto l : ivals) {
    assert(bvars.isBvar(l));
    if(satsolver->curVal(l) != l_True) 
      //Don't need true lits in assumption.
      switch(coreType) {
      case CoreType::cores:
        if(bvars.isNonCore(l))
          assumps.push_back(l);
        break;
      case CoreType::nonCores:
        if(bvars.isCore(l))
          assumps.push_back(l);
        break;
      case CoreType::mixed:
          assumps.push_back(l);
      }
    if (satsolver->curVal(l) == l_False)
      cout << "c WARNING assumptions being initialized with false lit\n";
  }
  setMap();  
}

void Assumps::all_softs_true() {
  //harden all softs not yet forced.
  assumps.clear();
  for(size_t i = 0; i < bvars.n_bvars(); i++)
    if(satsolver->curVal(bvars.varOfCls(i)) == l_Undef)
      assumps.push_back(~bvars.litOfCls(i));
  setMap();
}
   
void Assumps::exclude(const vector<Lit>& ex) {
  //Unlike update exclude removes the lits without regard for its polarity.
  for(auto l : ex)
    if(getIndex(l) >= 0)
      assumps[getIndex(l)] = lit_Undef;
  auto isUndef = [](Lit l) { return l == lit_Undef; };
  auto p = std::remove_if(assumps.begin(), assumps.end(), isUndef);
  assumps.erase(p, assumps.end());
  setMap();
}

void Assumps::update(const vector<Lit>& conflict, bool rm) {
  //Update assumptions with set of literals in conflict. Flip
  //flip the assumptions--if using Fb or remove the assumptions if
  //using Fbeq 
  if(rm)
    remove(conflict);
  else
    flip(conflict);
}

void Assumps::flip(const vector<Lit>& conflict) {
  //conflict variables must be in assumps. Update assumptions to agree
  //with conflict.
  for(auto l : conflict) {
    checkUpdate(l);
    if(assumps[getIndex(l)] == l)
      cout << "c WARNING conflict agrees with assumption---no real update in flip assumptions\n";
    assumps[getIndex(l)] = l;
  }
}
  
void Assumps::remove(const vector<Lit>& conflict) {
  //conflict variables must be in assumps.
  //perserve order of assumps.
  for(auto l : conflict)
    if(checkUpdate(l))
      assumps[getIndex(l)] = lit_Undef;
  auto isUndef = [](Lit l) { return l == lit_Undef; };
  auto p = std::remove_if(assumps.begin(), assumps.end(), isUndef);
  assumps.erase(p, assumps.end());
  setMap();
}
