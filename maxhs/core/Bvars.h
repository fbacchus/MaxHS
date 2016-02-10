/***********[Bvars.h]
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
#ifndef BVARS_h
#define BVARS_h

#include <vector>
#include "maxhs/ifaces/SatSolver.h"
#include "maxhs/core/Wcnf.h"

using Minisat::Lit;
using Minisat::var;
using Minisat::mkLit;
using Minisat::sign;

//We no longer add new b-vars to unit clauses...this means that units
//are modeled more like in fbeq than fb. That is, for a unit soft (l)
//the b-lit is -l. (B-lit false means soft clause must be
//satisfied). In Fb, the b-lit true does not force the clause to be
//falsified...but for units it does even when Fb is used.

class Bvars {
  //Helper class to manage mapping of b-variables to soft clauses. 
public:
  Bvars(const Wcnf* f);
  ~Bvars() {}

  //number and sizes
  size_t n() const { return theWcnf->nSofts(); }
  int nlits() const { return n()*2; }
  Var maxBvar() const { return maxbvar; }
  Var maxvar() const { return maxbvar > theWcnf->maxVar() ? maxbvar : theWcnf->maxVar(); }

  //blit of soft clause
  Var varOfCls(int i) const { assert(static_cast<size_t>(i) < theWcnf->nSofts()); return var(litOfCls(i)); }
  //making litOfCls(i) true relaxes soft clause i---incurring a cost
  //in fbeq it means that the clause is falsified
  Lit litOfCls(int i) const { assert(static_cast<size_t>(i) <theWcnf->nSofts()); return clsBlit[i]; }

  //return true if bvar appears positively in soft clause.
  //I.e., setting to true incurs cost of soft clause.
  bool isPos(Var v) const {assert(isBvar(v)); return !sign(litOfCls(clsIndex(v)));}

  //Soft clause index of a bvar/blit
  int clsIndex(Var v) const { assert(isBvar(v)); return bvarCls[v]; }
  int clsIndex(Lit l) const { assert(isBvar(l)); return clsIndex(var(l)); }

  //Variable is a bvar
  bool isBvar(Var v) const { return v < static_cast<int>(bvarCls.size()) && bvarCls[v]>=0; }
  bool isBvar(Lit l) const { return isBvar(var(l)); }
  bool isUnitBvar(Var v) const { return isBvar(v) && clsSize(v) == 1; }
  bool isUnitBvar(Lit l) const { return isUnitBvar(var(l)); }

  //is ordinary variable 
  bool isOvar(Var v) const { return v >= 0 && v < static_cast<int>(theWcnf->nVars()); }
  bool isOvar(Lit l) const { return isOvar(var(l)); }

  //Lit is a core bvar if it relaxes a clause (falsifies clause in Fbeq)
  //it can appear in a core constraint
  //non core bvars can appear in a non-core constraint
  bool isCore(Lit l) const { return isBvar(l) && l == litOfCls(clsIndex(l)); }
  bool isNonCore(Lit l) const { return isCore(~l); }

  //Map bvar or blit to a 0 based index---allowing
  //storing vector based data about bvars/blits
  int toIndex(Var v) const { assert(isBvar(v)); return clsIndex(v); }
  int toIndex(Lit l) const { assert(isBvar(l)); return clsIndex(l)*2+(int)sign(l); }

  //Weight of a bvar, blit. For blit this is the cost of making the
  //literal true (zero if the lit hardens rather than relaxes the
  //clause.
  Weight wt(Var v) const { assert(isBvar(v)); return theWcnf->getWt(clsIndex(v)); }
  Weight wtNcls(int i) const { assert((size_t)i < n()); return theWcnf->getWt(i); }
      
  Weight wt(Lit l) const { assert(isBvar(l)); return isCore(l) ?  theWcnf->getWt(clsIndex(l)) : 0; }
  int clsSize(Var v) const { assert(isBvar(v)); return theWcnf->softSize(clsIndex(v)); }
  int clsSize(Lit l) const { assert(isBvar(l)); return clsSize(var(l)); }

  Weight maxWt() const { return theWcnf->maxSftWt(); }
  Weight minWt() const { return theWcnf->minSftWt(); }

  //Return a vector containing all the bvars.
  vector<Var> getvars() {
    vector<Var> vars(n());
    for(size_t i = 0; i < n(); i++)
      vars[i] = varOfCls(i);
    return vars;
  }

private:
  const Wcnf* theWcnf;
  Var maxbvar;
  vector<Lit> clsBlit; //map from clause index to blit of clause
  vector<int> bvarCls; //map from b-var to clause index (sign determined by clsBlit)
};

#endif
