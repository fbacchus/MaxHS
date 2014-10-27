/***********[miniSatSolver.cc]
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

/* Interface to minisat.
*/

#include <vector>
#include <algorithm>
#include <ostream>
#include "maxhs/ifaces/miniSatSolver.h"
#include "maxhs/core/MaxSolver.h"
#include "maxhs/utils/io.h"

using namespace MaxHS_Iface;
using namespace Minisat;


/*************************************************/
//Internal to external variable ordering mappings.


void miniSolver::ensure_mapping(const Var ex)
{
  if (ex >= (int) ex2in_map.size())
    ex2in_map.resize(ex+1,var_Undef);
  
  if(ex2in_map[ex] == var_Undef) {
    Var in {newVar()};
    ex2in_map[ex] = in;
    if (in >= (int) in2ex_map.size())
      in2ex_map.resize(in+1, var_Undef);
    in2ex_map[in] = ex;
  }
}


/*************************************************/
//Solver interface routines

bool miniSolver::status() const {
  return Minisat::Solver::okay();
}

lbool miniSolver::solve_(const vector<Lit>& assumps, vector<Lit>& conflict,
			 int64_t confBudget, int64_t propBudget) {
  conflict.clear();
  Minisat::Solver::assumptions.clear();
  for(auto lt : assumps) {
    ensure_mapping(lt);
    Minisat::Solver::assumptions.push(ex2in(lt));
  }
  if(confBudget < 0)
    conflict_budget = -1;
  else
    conflict_budget = conflicts + confBudget;
  
  if(propBudget < 0)
    propagation_budget = -1;
  else
    propagation_budget = propagations + propBudget;

  lbool val = Minisat::Solver::solve_();
  in2ex(Minisat::Solver::conflict.toVec(), conflict);
  return val;
}

bool miniSolver::simplify()
{
  return Minisat::Solver::simplify();
}

void miniSolver::cancelTrail(int level, vector<Lit>& bt_lits)
{
  if (decisionLevel() > level){
    bt_lits.clear();
    for (int c = trail.size()-1; c >= trail_lim[level]; c--) {
      bt_lits.push_back(trail[c]); 
      Var      x  = var(trail[c]);
      assigns [x] = l_Undef;
    }
    qhead = trail_lim[level];
    trail.shrink(trail.size() - trail_lim[level]);
    trail_lim.shrink(trail_lim.size() - level);
  } 
}

void miniSolver::analyzeFinal(Lit p, LSet& out_conflict)
{
  //Changes from original: stop resolving backwards when we hit an
  //assumption literal.

  out_conflict.clear();
  out_conflict.insert(p);
  
  if (decisionLevel() == 0)
    return;
  
  seen[var(p)] = 1;

  LSet assumps;
  for(int i = 0; i < assumptions.size(); i++) {
    assumps.insert(assumptions[i]);
  }
  
  for (int i = trail.size()-1; i >= trail_lim[0]; i--){
    Var x = var(trail[i]);
    if (seen[x]){
      if (reason(x) == CRef_Undef || assumps.has(trail[i])){
	//note assumptions has ~p in it and ~p was forced. So x == p won't trigger.
	assert(level(x) > 0);
	assert(x != var(p));
	out_conflict.insert(~trail[i]);
      }else{
	Clause& c = ca[reason(x)];
	for (int j = 1; j < c.size(); j++)
	  if (level(var(c[j])) > 0)
	    seen[var(c[j])] = 1;
      }
      seen[x] = 0;
    }
  }
  
  seen[var(p)] = 0;
}

bool miniSolver::findImplications(const vector<Lit> &assumps, vector<Lit>& imps)
{
  vec<Lit> a;
  for(auto lt : assumps) {
    ensure_mapping(lt);
    a.push(ex2in(lt));
  }
  imps.clear();

  vec<Lit> r;
  bool val = Minisat::Solver::implies(a, r);
  if(!val) return val;

  for(int i=0; i < r.size(); i++)
    imps.push_back(in2ex(r[i]));
  return true;
}

vector<Lit> miniSolver::getForced(int index) {
  static vector<Lit> forced {};
  updateForced(forced);
  vector<Lit> tmp;
  for(size_t i = index; i < forced.size(); i++)
    tmp.push_back(in2ex(forced[i]));
  return tmp;
}

void miniSolver::updateForced(vector<Lit>& frc) {
  int limit = Solver::trail_lim.size() > 0 ?
    Solver::trail_lim[0] : Solver::trail.size();
  int i {0};

  if(frc.size() > 0) {
    i = frc.size() - 1;
    while(i < limit && Solver::trail[i++] != frc.back());
  }

  for( ; i < limit; i++)
    if(in2ex(Solver::trail[i]) != lit_Undef)
      frc.push_back(Solver::trail[i]);
}

int miniSolver::nAssigns() const
{
  return Minisat::Solver::nAssigns();
}

int miniSolver::nClauses() const
{
  return Minisat::Solver::nClauses();
}

int miniSolver::nVars() const
{
  return Minisat::Solver::nVars();
}

bool miniSolver::reduceClause(vector<Lit>& lts) const
{
  // remove false/duplicate literals return false if true lits is present
  assert(decisionLevel() == 0);
  std::sort(lts.begin(), lts.end());

  //In this loop i is the (index of) next literal to examine. j is the index of
  //the last literal to keep. j=-1 means nothing has yet been kept.
  int j {-1};
  for(size_t i =0; i< lts.size(); i++) {
    Lit in = ex2in(lts[i]);
    lbool val {(in == lit_Undef) ? l_Undef : value(in)};
    if(val == l_True || (j > 0 && lts[i] == ~lts[j])) {
      return true; 
    }
    if(val == l_False || (j > 0 && lts[i] == lts[j]))
      continue;

    lts[++j] = lts[i];
  }
  lts.resize(j+1);

  return false; //clause not true
}

bool miniSolver::addClause(const vector<Lit>& lts) 
{
  vec<Lit> ps;
  for(auto lt: lts) {
    ensure_mapping(lt);
    ps.push(ex2in(lt));
  }

  //cout << "mini addCls: ext=" << lts << " int=" << ps << "\n";

  return Minisat::Solver::addClause_(ps); 
}

void miniSolver::newControlVar(Var b, bool dvar, lbool pol) {

  if (b >= static_cast<Var>(ex2in_map.size()))
    ex2in_map.resize(b+1, var_Undef);
  if (ex2in_map[b] != var_Undef)
    cout << "c ERROR: new control variable for variable that already exists (" << b << ")";
  else {
    Var c {newVar(pol, dvar)};
    ex2in_map[b] = c;
    if(c >= static_cast<Var>(in2ex_map.size()))
      in2ex_map.resize(c+1, var_Undef);
    in2ex_map[c] = b;
  }
}

void miniSolver::freeVar(Lit l) {
  //remove mapping and assert l to sat solver.
  Var in = var(l) < (int) ex2in_map.size()  ? ex2in_map[var(l)] : var_Undef;
  if(in != var_Undef) {
    ex2in_map[var(l)] = var_Undef;
    in2ex_map[in] = var_Undef;
    releaseVar(mkLit(in, sign(l)));
  }
}

void miniSolver::setNoDecision(Var b) {
  //unset b as a decision variable;
  Var in = b < (int) ex2in_map.size() ? ex2in_map[b] : var_Undef;
  if(in != var_Undef) {
    setDecisionVar(in, false);
  }
}

void miniSolver::printLit(const Lit l) const 
{
  cout << (sign(l) ? "-" : "") << var(l)+1 << ":";
  Lit in = ex2in(l);
  if(in == lit_Undef || value(in) == l_Undef)
    cout << 'U';
  else 
    cout << (value(in) == l_True ? 'T' : 'F');
}

void miniSolver::invertVarActivities() 
{
  double minAct = -1; // min non-zero activity
  for (int i = 0; i < nVars(); i++) {
    if (activity[i] > 0 && (minAct < 0 || activity[i] < minAct)) {
      minAct = activity[i];
    }
  }
  // If no variables have any activity, then there is no need to invert
  if (minAct < 0) return;
  
  for (int i = 0; i < nVars(); i++) {
    if (activity[i] > 0) {
      activity[i] = (1/activity[i])/(1/minAct);
    } else {
      activity[i] = 1;
    } 
  }
  rebuildOrderHeap();
}


void miniSolver::pruneLearnts(MaxHS::MaxSolver *S) 
//TODO: use a function pointer or allow a lambda to be passed
{
  int i, j;
  vector<Lit> exCls;
  for (i = j = 0; i < learnts.size(); i++){
    Clause& c = ca[learnts[i]];
    exCls.clear();
    for(int i = 0; i < c.size(); i++)
      exCls.push_back(c[i]);
    
    if (!locked(c) && S->deleteLearntTest(exCls))
            removeClause(learnts[i]);
        else
            learnts[j++] = learnts[i];
    }
    learnts.shrink(i - j);
    checkGarbage();
}

lbool miniSolver::modelValue(const Lit p) const 
{
  Lit in = ex2in(p);
  if (in == lit_Undef)
    return l_Undef;
  else
    return Minisat::Solver::modelValue(in);
}

lbool miniSolver::modelValue(const Var x) const 
{
  Var in = ex2in(x);
  if (in == var_Undef)
    return l_Undef;
  else
    return Minisat::Solver::modelValue(in);
}

lbool miniSolver::curVal(Var x) const {
  Var in = ex2in(x);
  if(in == var_Undef)
    return l_Undef;
  else  
    return Minisat::Solver::value(in);
}

lbool miniSolver::curVal(Lit x) const {
  Lit in = ex2in(x);
  if(in == lit_Undef)
    return l_Undef;
  else  
    return Minisat::Solver::value(in);
}

