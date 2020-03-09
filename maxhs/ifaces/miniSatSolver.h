/***********[miniSatSolver.h]
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

/* minisat interface
   The interface maintains a mapping between interally numbered
   variables and externally numbered variables.
   This is to ensure that the internal variables are consecutively ordered,
   so that the external theory can be fed to the sat solver in parts with
   generating huge gaps in the variable numbering.
   
   This also means however, that not all external variables will be given a value
   by a found sat model.
*/

#ifndef MINISATSOLVER_H
#define MINISATSOLVER_H

#ifdef GLUCOSE
#include "glucose/simp/SimpSolver.h"
#include "glucose/core/SolverTypes.h"
#else
#include "minisat/simp/SimpSolver.h"
#include "minisat/core/SolverTypes.h"
#endif

#include "maxhs/ifaces/SatSolver.h"

#ifdef GLUCOSE
namespace Minisat = Glucose;
#endif

using Minisat::vec;
using Minisat::var_Undef;
using Minisat::lit_Undef;
using Minisat::mkLit;
using Minisat::VMap;
using Minisat::Heap;
namespace MaxHS_Iface {

//Minisat Solver
class miniSolver : public SatSolver, protected Minisat::SimpSolver {
public:
  miniSolver();
  virtual ~miniSolver();
  bool status() const;

  bool findImplications(const vector<Lit> &assumps, vector<Lit>& unitImps);
  bool findImplications(Lit p, vector<Lit>& unitImps) {
    vector<Lit> tmp {p}; return findImplications(tmp, unitImps);
  }
  bool findImplications(Lit p, Lit q, vector<Lit>& unitImps) {
    vector<Lit> tmp {p,q}; return findImplications(tmp, unitImps);
  }
  bool isMX(Lit p, Lit q) {
    vector<Lit> tmp {p,q}; vector<Lit> tmp2; return !findImplications(tmp, tmp2);
  }

  template <class S>
    bool findImplicationsIf(Lit p, vector<Lit>& imps, S pred);

  vector<Lit> getForced(int index);
  int nForced() const  { return trail_lim.size() > 0 ? trail_lim[0] : trail.size(); }
  int nEliminated() const { return eliminated_vars; }
  int nAssigns() const { return Minisat::SimpSolver::nAssigns(); }
  int nClauses() const { return Minisat::SimpSolver::nClauses(); }
  int nInVars() const    { return Minisat::SimpSolver::nVars(); }
  size_t nVars() const { return ex2in_map.size(); }  //not all these externals exist
  bool inSolver(Var v) const { return ex2in(v) != var_Undef; }
  bool activeVar(Var v) const {
    return inSolver(v) && !isEliminated(ex2in(v)) && curVal(v) == l_Undef; }

  //get clauses currently in solver (e.g., after preprocessing)
  //_size counts clauses possibly deleted or already satisfied
  int get_clauses_size() const { return clauses.size(); }
  int get_learnts_size() const { return learnts.size(); }

  //getIth_clause filters deleted and satisfied clauses returning an empty vector
  //in those cases.
  vector<Lit> getIth_clauses(int ith) const;
  vector<Lit> getIth_learnts(int ith) const;

  bool reduceClause(vector<Lit>& lts) const;
  bool addClause(const vector<Lit>& lts);
  void setPolarity(Var v, lbool pol);
  void setDecisionVar(Var v, bool d);
  void newControlVar(Var b, bool dvar, lbool pol);
  void freeVar(Lit l);
  void printLit(Lit l) const;
  void invertVarActivities();
  void pruneLearnts();
  lbool modelValue(Lit p) const;
  lbool modelValue(Var x) const;
  lbool curVal(const Var x) const;
  lbool curVal(const Lit x) const;
  uint64_t getProps() const { return propagations; }
  uint64_t getConfs() const { return conflicts; }

  //preprocessing
  void freezeVar(Lit l) { freezeVar(var(l)); }
  void freezeVar(Var v);
  bool eliminate(bool turn_off_elim);
  bool simplify();
  int nEliminated() { return eliminated_vars; }  

protected:
  lbool solve_(const vector<Lit>& assumps, vector<Lit>& conflict,
	       int64_t confBudget, int64_t propBudget);
  lbool relaxSolve_(const vector<Lit>& assumps, const vector<Lit>& branchLits, 
		    int64_t propBudget);
  //void analyzeFinal(Lit p, Minisat::LSet& out_conflict);
  Lit pickBranchLit();
  void cancelUntil(int level);
  void ensure_mapping(const Var ex);
  void ensure_mapping(const Lit lt) {
    ensure_mapping(var(lt));
  }

  void updateForced(vector<Lit>& frc);
  vector<Lit> forced;

  //For relaxation search
  VMap<int> relaxVarRank;                 //During relaxation search branch on lower ranked vars first
  VMap<char> relaxVarSign;                //If true use signed literal for decisions, otherwise use unsigned literal.
  struct RelaxVarOrderLt {                //Operator < for heap.
    const VMap<int>&  relaxVarRank;
    bool operator () (Var x, Var y) const { return relaxVarRank[x] < relaxVarRank[y]; }
    RelaxVarOrderLt(const VMap<int>& rank) : relaxVarRank (rank) { }
  };
  Heap<Var,RelaxVarOrderLt> relaxOrder_heap;  //Used to select next relaxation literal to branch on (according to rank)
  vector<lbool> savedModel;                    //Used to save the current model (if relaxation search times
					     //out we restore the saved model)
  bool doingRelaxSearch;
  bool isRelaxVar(Var v) const { return relaxVarRank.has(v) && relaxVarRank[v] < std::numeric_limits<int>::max(); }
  void insertRelaxOrder(Var x) { if (!relaxOrder_heap.inHeap(x)) relaxOrder_heap.insert(x); }

  //External to internal mapping. 
  vector<Var>in2ex_map;
  vector<Var>ex2in_map;

  Lit in2ex(Lit lt) const {
    if(var(lt) >= (int) in2ex_map.size() ||
       in2ex_map[var(lt)] == var_Undef)
      return lit_Undef;
    else
      return mkLit(in2ex_map[var(lt)], sign(lt));
  }
  
  Var in2ex(Var v) const {
    if(v >= (int) in2ex_map.size())
      return var_Undef;
    else
      return in2ex_map[v];
  }

  
  //In most applications every internal literal of the SatSolver
  //is associated with an external literal on creation.
  //So this array function is safe...i.e., won't add var_Undef to output
  //vector. An array version of ex2in is typically not safe in this way.
  //so is not provided.

  
  void in2ex(const vec<Lit> &from, vector<Lit> &to) const {
    to.clear();
    for(int i = 0; i < from.size(); i++)
      to.push_back(in2ex(from[i]));
  }
  
  void in2ex(const vec<Var> &from, vector<Var> &to) const {
    to.clear();
    for(int i = 0; i < from.size(); i++)
      to.push_back(in2ex(from[i]));
  }
  
  Var ex2in(Var v) const {
    if(v >= static_cast<int>(ex2in_map.size()))
      return var_Undef;
    else
      return ex2in_map[v]; 
  }

  Lit ex2in(Lit lt) const {
    if(var(lt) >= static_cast<int>(ex2in_map.size()) ||
       ex2in_map[var(lt)] == var_Undef)
      return lit_Undef;
    else
      return mkLit(ex2in_map[var(lt)], sign(lt));
  }

};

template <class S>
bool miniSolver::findImplicationsIf(Lit p, vector<Lit>& imps, S pred) {
  imps.clear();
  if(!activeVar(var(p)))
    return false;

  Lit a = ex2in(p);
  trail_lim.push(trail.size());
  uncheckedEnqueue(a);
  
  unsigned trail_before = trail.size();
  bool     ret          = true;
  if (propagate() == Minisat::CRef_Undef) {
    for (int j = trail_before; j < trail.size(); j++) 
      if( in2ex(trail[j]) != lit_Undef && (pred(in2ex(trail[j]))) )
	imps.push_back(in2ex(trail[j]));
  }
  else
    ret = false;

  cancelUntil(0);
  return ret;
}
 
} //end namespace

#endif 
