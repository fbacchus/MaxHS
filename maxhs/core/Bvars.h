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
#include <algorithm>
#include "maxhs/ifaces/SatSolver.h"
#include "maxhs/core/Wcnf.h"

using Minisat::Lit;
using Minisat::var;
using Minisat::mkLit;

class Bvars {
  //Helper class to manage mapping of b-variables to soft clauses. 
public:
  Bvars(const Wcnf* f) : theWcnf{f} {}
  ~Bvars() {}

  //number and sizes
  int n() const { return theWcnf->nSofts(); }
  int nlits() const { return n()*2; }
  Var maxBvar() const { return theWcnf->nOrigVars() + n() - 1; }
  Var minBvar() const { return theWcnf->nOrigVars(); }

  //Soft clause index to associated bvar/blit
  Var varOfCls(int i) const { assert(i<theWcnf->nSofts()); return theWcnf->nOrigVars() + i; }
  Lit litOfCls(int i) const { assert(i<theWcnf->nSofts()); return mkLit(varOfCls(i), false); }

  //Variable is a bvar
  bool isBvar(Var v) const { return v >= minBvar() && v <= maxBvar(); }
  bool isBvar(Lit l) const { return isBvar(var(l)); }
  //is ordinary variable 
  bool isOvar(Var v) const { return v >= 0 && v < minBvar(); }
  bool isOvar(Lit l) const { return isOvar(var(l)); }


  //Lit is a core bvar it can appear in a core constraint
  //    or a non core bvar---it can appear in a non-core constraint
  bool isCore(Lit l) const { return !sign(l) && isBvar(l); }
  bool isNonCore(Lit l) const { return sign(l) && isBvar(l); }
  
  //Map bvar or blit to a 0 based index---allowing
  //storing vector based data about bvars/blits
  int toIndex(Var v) const { assert(isBvar(v)); return clsIndex(v); }
  int toIndex(Lit l) const { assert(isBvar(l)); return toInt(l) - (theWcnf->nOrigVars() * 2); }

  //Soft clause index of a bvar/blit
  int clsIndex(Var v) const { assert(isBvar(v)); return v - theWcnf->nOrigVars(); }
  int clsIndex(Lit l) const { assert(isBvar(l)); return clsIndex(var(l)); }
  
  //Weight of a bvar, blit. For blit this is the cost of making the
  //literal true (zero if the lit hardens rather than relaxes the
  //clause.
  Weight wt(Var v) const { assert(isBvar(v)); return theWcnf->getWt(clsIndex(v)); }
  Weight wt(Lit l) const { assert(isBvar(l)); return sign(l) ? 0 : theWcnf->getWt(clsIndex(l)); }
  int clsSize(Var v) const { assert(isBvar(v)); return theWcnf->softs()[clsIndex(v)].size(); }
  int clsSize(Lit l) const { assert(isBvar(l)); return clsSize(var(l)); }

  Weight maxWt() const { return theWcnf->maxSftWt(); }
  Weight minWt() const { return theWcnf->minSftWt(); }

  //Return a vector containing all the bvars.
  vector<Var> getvars() {
    vector<Var> vars(n());
    for(int i = 0; i < n(); i++)
      vars[i] = varOfCls(i);
    return vars;
  }

private:
  const Wcnf* theWcnf;
};

#endif
