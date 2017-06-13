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
#include <ostream>
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


enum class Var_type : uint8_t {
    not_in_theory = 0,
    original = 1,
    bvar = 2,
    core_is_pos = 4,
    in_mutex = 8,
    orig_core_is_pos = 16,
    dvar = 32 };

constexpr Var_type operator| (Var_type x, Var_type y) {
  return static_cast<Var_type>(static_cast<uint8_t>(x) | static_cast<uint8_t>(y));
}
constexpr Var_type operator& (Var_type x, Var_type y) {
  return static_cast<Var_type>(static_cast<uint8_t>(x) & static_cast<uint8_t>(y));
}
constexpr bool to_bool(Var_type x) {
  return x != Var_type::not_in_theory;
}

ostream& operator<<(ostream& os, const Var_type& x);

class Bvars {
  //Helper class to manage mapping of b-variables to soft clauses. 
public:
  Bvars(const Wcnf* f);
  ~Bvars() {}

  //number and sizes
  size_t n_bvars() const { return theWcnf->nSofts(); }
  size_t n_blits() const { return n_bvars()*2; }
  Var maxBvar() const { return maxbvar; }
  Var maxvar() const { return std::max(theWcnf->maxVar(), maxbvar); }

  //blit of soft clause
  Var varOfCls(int i) const { return var(litOfCls(i)); }
  //making litOfCls(i) true relaxes soft clause i---incurring a cost
  //in fbeq it means that the clause is falsified
  Lit litOfCls(int i) const { assert(static_cast<size_t>(i) <theWcnf->nSofts()); return clsBlit[i]; }

  //Soft clause index of a bvar/blit
  int clsIndex(Var v) const { assert(isBvar(v)); return bvarCls[v]; }
  int clsIndex(Lit l) const { return clsIndex(var(l)); }

  //convert a b-variable to its core lit or non-core lit (core lit = True ==> relax corresponding soft clause)
  Lit coreLit(Var v) const { return litOfCls(clsIndex(v)); }
  Lit nonCoreLit(Var v) const { return ~coreLit(v); }

  //Variable is a bvar
  bool isBvar(Var v) const { return to_bool(var_types[v] & Var_type::bvar); }
  bool isBvar(Lit l) const { return isBvar(var(l)); }

  //return true if bvar appears positively/negatively in soft clause.
  //I.e., setting to true/false incurs cost of sone soft clause.
  bool coreIsPos(Var v) const { return isBvar(v) && to_bool(var_types[v] & Var_type::core_is_pos); }
  bool coreIsPos(Lit l) const { return coreIsPos(var(l)); }
  bool coreIsNeg(Var v) const { return isBvar(v) && !coreIsPos(v); }
  bool coreIsNeg(Lit l) const { return coreIsNeg(var(l)); }

  //Lit is a core bvar if it relaxes a clause when made true (falsifies clause in Fbeq)
  //it can appear in a core constraint
  //non core bvars can appear in a non-core constraint
  bool isCore(Lit l) const { return isBvar(l) && (sign(l) != coreIsPos(l)); }
  //bool isCore(Lit l) const { return isBvar(l) && l == litOfCls(clsIndex(l)); }
  bool isNonCore(Lit l) const { return isCore(~l); }

  //is original variable (could also be a bvar!)
  bool isOvar(Var v) const { return to_bool(var_types[v] & Var_type::original); }
  bool isOvar(Lit l) const { return isOvar(var(l)); }

  //appears in mutex
  bool inMutex(Var v) const { return to_bool(var_types[v] & Var_type::in_mutex); }
  bool inMutex(Lit l) const { return inMutex(var(l)); }

  //var appears in a mutex and making it postive/negative incurred the cost of that
  //original soft clause (i.e., before these softs were encoded into a
  //mutex)
  bool orig_coreIsPos(Var v) const { return inMutex(v) && to_bool(var_types[v] & Var_type::orig_core_is_pos); }
  bool orig_coreIsPos(Lit l) const { return orig_coreIsPos(var(l)); }
  bool orig_coreIsNeg(Var v) const { return inMutex(v) && !orig_coreIsPos(v); }
  bool orig_coreIsNeg(Lit l) const { return orig_coreIsNeg(var(l)); }

  //This literal was originally a core or non-core bvar (before mx processing)
  bool orig_IsCore(Lit l) const { return inMutex(l) && (sign(l) != orig_coreIsPos(l)); }
  bool orig_IsNonCore(Lit l) const { return orig_IsCore(~l); }

  int  getMxNum(Var v) const { return mxNum[v]; }
  int  getMxNum(Lit l) const { return getMxNum(var(l)); }

  bool inCoreMx(Var v) const { return inMutex(v) && theWcnf->get_SCMxs()[getMxNum(v)].is_core(); }
  bool inCoreMx(Lit l) const { return inCoreMx(var(l)); }
  bool inNonCoreMx(Var v) const { return inMutex(v) && !theWcnf->get_SCMxs()[getMxNum(v)].is_core(); }
  bool inNonCoreMx(Lit l) const { return inNonCoreMx(var(l)); }

  bool isDvar(Var v) const { return to_bool(var_types[v] & Var_type::dvar); }
  bool isDvar(Lit l) const { return isDvar(var(l)); }


  //Map bvar or blit to a 0 based index---allowing
  //storing vector based data about bvars/blits
  int toIndex(Var v) const { assert(isBvar(v)); return clsIndex(v); }
  int toIndex(Lit l) const { assert(isBvar(l)); return clsIndex(l)*2+(int)sign(l); }

  bool areSubsumedByMx(Lit l1, Lit l2) const {
    //binary clause (l1, l2) is subsumed by mutex information.
    return (inMutex(l1) && inMutex(l2)
            && getMxNum(l1) == getMxNum(l2)
            && ((orig_IsNonCore(l1) && orig_IsNonCore(l2) && inCoreMx(l1))
                || (orig_IsCore(l1) && orig_IsCore(l2) && inNonCoreMx(l1))));
  }

  //Weight of a bvar, blit. For blit this is the cost of making the
  //literal true (zero if the lit hardens rather than relaxes the
  //clause.
  Weight wt(Var v) const { assert(isBvar(v)); return theWcnf->getWt(clsIndex(v)); }
  Weight wtNcls(int i) const { assert((size_t)i < n_bvars()); return theWcnf->getWt(i); }

  Weight wt(Lit l) const { assert(isBvar(l)); return isCore(l) ?  theWcnf->getWt(clsIndex(l)) : 0; }
  int clsSize(Var v) const { assert(isBvar(v)); return theWcnf->softSize(clsIndex(v)); }
  int clsSize(Lit l) const { assert(isBvar(l)); return clsSize(var(l)); }

  Weight maxWt() const { return theWcnf->maxSftWt(); }
  Weight minWt() const { return theWcnf->minSftWt(); }


  //Return a vector containing all the bvars.
  vector<Var> getvars() {
    vector<Var> vars(n_bvars());
    for(size_t i = 0; i < n_bvars(); i++)
      vars[i] = varOfCls(i);
    return vars;
  }
  void printVars();
  void print_var_types();

private:
  const Wcnf* theWcnf;
  Var maxbvar;
  vector<Lit> clsBlit; //map from clause index to blit of clause
  vector<int> bvarCls; //map from b-var to clause index (sign determined by clsBlit)
  vector<Var_type> var_types;
  vector<int> mxNum;   //map from variables to mutex they are in
};

#endif
