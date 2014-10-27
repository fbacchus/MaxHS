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
#include "maxhs/ifaces/miniSatSolver.h"
#include "maxhs/core/MaxSolver.h"

using namespace MaxHS_Iface;
using namespace Minisat;

miniSolver::miniSolver() 
{ }

miniSolver::~miniSolver()
{ }

bool miniSolver::status() const
{
  return Minisat::Solver::okay();
}

lbool miniSolver::solve_(const vector<Lit>& assumps, vector<Lit>& conflict,
	     int64_t confBudget, int64_t propBudget) 
{
  vector2vec(assumps, Minisat::Solver::assumptions);
  if(confBudget < 0)
    conflict_budget = -1;
  else
    conflict_budget = conflicts + confBudget;
  
  if(propBudget < 0)
    propagation_budget = -1;
  else
    propagation_budget = propagations + propBudget;
  lbool val = Minisat::Solver::solve_();
  vec2vector(Minisat::Solver::conflict.toVec(), conflict);
  return val;
}

//Access conflict directly
lbool miniSolver::solve_(const vector<Lit>& assumps, 
	     int64_t confBudget, int64_t propBudget) 
{
  conflict.clear();
  vector2vec(assumps, Minisat::Solver::assumptions);
  if(confBudget < 0)
    conflict_budget = -1;
  else
    conflict_budget = conflicts + confBudget;
  
  if(propBudget < 0)
    propagation_budget = -1;
  else
    propagation_budget = propagations + propBudget;
  lbool val = Minisat::Solver::solve_();
  return val;
}

LSet& miniSolver::getConflict() {
  return Minisat::Solver::conflict;
}

bool miniSolver::simplify()
{
  return Minisat::Solver::simplify();
}

void miniSolver::cancelTrail(int level, vector<Lit>& bt_lits) {
  if (decisionLevel() > level){
    bt_lits.clear();
    for (int c = trail.size()-1; c >= trail_lim[level]; c--){
      bt_lits.push_back(trail[c]);
      Var      x  = var(trail[c]);
      assigns [x] = l_Undef;
    }
    qhead = trail_lim[level];
    trail.shrink(trail.size() - trail_lim[level]);
    trail_lim.shrink(trail_lim.size() - level);
  } 
}

bool miniSolver::findUnitImps(const Lit p, vector<Lit>& unitImps)
{
  int cur_dlevel = decisionLevel();
  newDecisionLevel();
  uncheckedEnqueue(p);
  CRef confl = propagate();
  if (confl != CRef_Undef) {
    cancelUntil(cur_dlevel);
    return false;
  }
  cancelTrail(cur_dlevel, unitImps);
  unitImps.pop_back(); // remove p itself
  return true;
}

int miniSolver::nAssigns() 
{
  return Minisat::Solver::nAssigns();
}

int miniSolver::nClauses()
{
  return Minisat::Solver::nClauses();
}

int miniSolver::nVars()
{
  return Minisat::Solver::nVars();
}

bool miniSolver::reduceClause(vector<Lit>& lts)
{
  // remove false/duplicate literals return false if true lits is present
  assert(decisionLevel() == 0);
  std::sort(lts.begin(), lts.end());
  Lit p; size_t i, j;
  for (i = j = 0, p = lit_Undef; i < lts.size(); i++)
    if ((var(lts[i]) < nVars() && value(lts[i]) == l_True) || lts[i] == ~p) { 
      return true; //clause is true
    } else if ((var(lts[i]) >= nVars() || value(lts[i]) != l_False) && lts[i] != p)
      lts[j++] = p = lts[i];
  lts.resize(lts.size() - (i - j));
  return false; //clause not true
}

void miniSolver::addVars(const vector<Lit>& lts)
{
  for (size_t i = 0; i < lts.size(); i++) {
    // All variables are decision variables 
    while (var(lts[i]) >= nVars()) newVar();  
  }
}

bool miniSolver::addClause(const vector<Lit> lts) 
{
  vec<Lit> ps;
  vector2vec(lts, ps);
  return Minisat::Solver::addClause_(ps); 

}

int miniSolver::clsSize(const int clsIndex) const
{
  return ca[clauses[clsIndex]].size();
}

Lit miniSolver::clsLit(const int clsIndex, const int litIndex) const
{
  return ca[clauses[clsIndex]][litIndex];
}

void miniSolver::printLit(const Lit l) const 
{
  printf(/*"%s%d"*/ "%s%d:%c",
	 sign(l) ? "-" : "",
	 var(l)+1 ,
	 value(l) == l_True ? '1' : (value(l) == l_False ? '0' : 'X'));
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
{
  int i, j;
  for (i = j = 0; i < learnts.size(); i++){
    Clause& c = ca[learnts[i]];
    if (!locked(c) && S->deleteLearntTest(c))
            removeClause(learnts[i]);
        else
            learnts[j++] = learnts[i];
    }
    learnts.shrink(i - j);
    checkGarbage();
}

//obtain last model (get full model if you need to get many)
vector<lbool> miniSolver::model() 
{
  vector<lbool> tmp;
  vec2vector(Minisat::Solver::model, tmp);
  return tmp; //exploit move semantics for C++11
}

lbool miniSolver::modelValue(Lit p) const 
{
  return Minisat::Solver::modelValue(p);
}

lbool miniSolver::modelValue(Var x) const 
{
  return Minisat::Solver::modelValue(x);
}

vector<lbool> miniSolver::curVals()
{
  vector<lbool> tmp;
  for(int i = 0; i < nVars(); i++) 
    tmp[i] = Minisat::Solver::value(i);
  return tmp;
}

lbool miniSolver::curVal(Var x) {
  return Minisat::Solver::value(x);
}

