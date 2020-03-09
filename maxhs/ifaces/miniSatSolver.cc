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

#ifdef GLUCOSE
namespace Minisat = Glucose;
#endif

using namespace Minisat;

miniSolver::miniSolver() :
  relaxOrder_heap (RelaxVarOrderLt(relaxVarRank)),
  doingRelaxSearch {false}
{}

miniSolver::~miniSolver() {}


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
  return Minisat::SimpSolver::okay();
}

lbool miniSolver::solve_(const vector<Lit>& assumps, vector<Lit>& conflict,
			 int64_t confBudget, int64_t propBudget) {
  conflict.clear();
  Minisat::SimpSolver::assumptions.clear();
  for(auto lt : assumps) {
    ensure_mapping(lt);
    Minisat::SimpSolver::assumptions.push(ex2in(lt));
  }
  if(confBudget < 0)
    conflict_budget = -1;
  else
    conflict_budget = conflicts + confBudget;
  
  if(propBudget < 0)
    propagation_budget = -1;
  else
    propagation_budget = propagations + propBudget;

  lbool val = Minisat::SimpSolver::solve_(false); //don't do simplification incrementally. 
  in2ex(Minisat::SimpSolver::conflict.toVec(), conflict);
  return val;
}

lbool miniSolver::relaxSolve_(const vector<Lit>& assumps, const vector<Lit>& branchLits, 
			      int64_t propBudget) {
  Minisat::SimpSolver::assumptions.clear();
  for(auto lt : assumps) {
    ensure_mapping(lt);
    Minisat::SimpSolver::assumptions.push(ex2in(lt));
  }

  relaxVarRank.clear();
  relaxOrder_heap.clear();
  for(int i = 0; i < static_cast<int>(branchLits.size()); i++) {
    auto lt = branchLits[i];
    ensure_mapping(lt);
    auto inLt = ex2in(lt);
    //If var is not a relax var, then either !relaxVarRank.has() or relaxVarRank = max()
    relaxVarRank.insert(var(inLt), i, std::numeric_limits<int>::max());
    relaxVarSign.insert(var(inLt), sign(inLt));
    //note all elements already in heap are already in relaxVarRank,
    //so new element can be inserted in correct place.
    relaxOrder_heap.insert(var(inLt)); 
  }

  if(propBudget < 0)
    propagation_budget = -1;
  else
    propagation_budget = propagations + propBudget;

  savedModel.clear();
  for(int i = 0; i < Minisat::SimpSolver::model.size(); i++)
    savedModel.push_back(Minisat::SimpSolver::model[i]);

  doingRelaxSearch = true;
  auto val = Minisat::SimpSolver::solve_(false);
  doingRelaxSearch = false;

  if(val != l_True) {
    Minisat::SimpSolver::model.clear();
    Minisat::SimpSolver::model.growTo(savedModel.size());
    for(int i = 0; i < static_cast<int>(savedModel.size()); i++)
      Minisat::SimpSolver::model[i] = savedModel[i];
  }
  return val;
}


Lit miniSolver::pickBranchLit() {
  if(!doingRelaxSearch)
    return Minisat::SimpSolver::pickBranchLit();
  Var next = var_Undef;
  while(next == var_Undef || value(next) != l_Undef)
    if(relaxOrder_heap.empty()) {
      next = var_Undef;
      break;
    }
    else
      next = relaxOrder_heap.removeMin();

  if(next == var_Undef)
    return Minisat::SimpSolver::pickBranchLit();
  else
    return mkLit(next, relaxVarSign[next]);
}

void miniSolver::cancelUntil(int level) {
  if (decisionLevel() > level) {
    for (int c = trail.size()-1; c >= trail_lim[level]; c--) {
      Var      x  = var(trail[c]);
      assigns [x] = l_Undef;
      if (phase_saving > 1 || (phase_saving == 1 && c > trail_lim.last()))
	polarity[x] = sign(trail[c]);
      if(doingRelaxSearch && isRelaxVar(x))
	insertRelaxOrder(x);
      insertVarOrder(x); //also insert into var order rank to restore for next non-relax search.
    }
    qhead = trail_lim[level];
    trail.shrink(trail.size() - trail_lim[level]);
    trail_lim.shrink(trail_lim.size() - level);
  }
}

void miniSolver::freezeVar(Var v)
{
  Var in = ex2in(v);
  if (in != var_Undef) {
    //if(!frozen[in]) cout << "mini freezevar " << in << " external " << v << "\n";
    Minisat::SimpSolver::freezeVar(in);
  }
  else 
    cout << "c ERROR. Tried to freeze variable " << v << " that is not yet in solver\n.";
}

bool miniSolver::eliminate(bool turn_off_elim) 
{
  return Minisat::SimpSolver::eliminate(turn_off_elim);
}

bool miniSolver::simplify()
{
  return Minisat::SimpSolver::simplify();
}


//REMOVE FOR NOW
#if 0
void miniSolver::analyzeFinal(Lit p, LSet& out_conflict)
{
  //Changes from original: stop resolving backwards when we hit an
  //assumption literal.

  out_conflict.clear();
  out_conflict.insert(p);
  
  if (decisionLevel() == 0)
    return;
  
  seen[var(p)] = 1;

  /*cout << "In analyzerFinal\n DLevel = " << decisionLevel() << "\n";
  cout << "False assumption = ";
  printLit(in2ex(p));
  cout << "\nTRAIL:\n";
  for(int i = trail.size()-1; i >= 0; i--) {
    cout << i << "." << level(var(trail[i])) << "\t";
    printLit(in2ex(trail[i]));
    if(reason(var(trail[i])) == CRef_Undef) 
      cout << "\tDecision\n";
    else {
      printf("\t<--[");
      Clause &c = ca[reason(var(trail[i]))];
      for(int j = 0; j < c.size()-1; j++) {
	printLit(in2ex(c[j])); cout << ", ";
      }
      printLit(in2ex(c[c.size()-1])); cout << "]\n";
    }
  }
  */
  
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

  /*printf("Final Conflict: [");
  auto& v = out_conflict.toVec();
  for(int j = 0; j < v.size()-1; j++) {
    printLit(in2ex(v[j])); cout << ", ";
  }
  printLit(in2ex(v[v.size()-1])); cout << "]\n";
  */
}
#endif

bool miniSolver::findImplications(const vector<Lit> &assumps, vector<Lit>& imps)
{
  vec<Lit> a;
  for(auto lt : assumps) {
    ensure_mapping(lt);
    a.push(ex2in(lt));
  }
  imps.clear();

  vec<Lit> r;
  bool val = Minisat::SimpSolver::implies(a, r);
  if(!val) return val;

  for(int i=0; i < r.size(); i++)
    imps.push_back(in2ex(r[i]));
  return true;
}

vector<Lit> miniSolver::getForced(int index) {
  //DEBUG
  //cout << "miniSolver::getForced: Forced =" << forced << "\n";

  updateForced(forced);

  //DEBUG
  //cout << "after update forced =" << forced << "\n";

  vector<Lit> tmp;
  for(size_t i = index; i < forced.size(); i++)
    tmp.push_back(in2ex(forced[i]));
  return tmp;
}

void miniSolver::updateForced(vector<Lit>& frc) {
  int limit = trail_lim.size() > 0 ?
    trail_lim[0] : trail.size();
  int i {0};

  //DEBUG
  /*cout << "MINISolver update Forced. TRAIL = \n[";
  for(int jj = 0; jj < limit; jj++)
    cout << "[" << jj << ". " << Solver::trail[jj] << "/" << in2ex(Solver::trail[jj]) << "] ";
    cout << "]\n";*/
  
  if(frc.size() > 0) {
    i = frc.size() - 1;
    while(i < limit && trail[i++] != frc.back());
  }

  for( ; i < limit; i++)
    if(in2ex(trail[i]) != lit_Undef)
      frc.push_back(trail[i]);
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
    if(isEliminated(var(ex2in(lt)))) {
      ps.clear();
      break;
    }
    ps.push(ex2in(lt));
  }

  //DEBUG
  //cout << "mini addCls: ext=" << lts << " int=" << ps << "\n";

  if(ps.size()>0)
    return Minisat::SimpSolver::addClause_(ps);
  else
    return true;
}

void miniSolver::setPolarity(Var v, lbool pol) {
  Var in = ex2in(v);
  assert(in != var_Undef);
  if(in != var_Undef) 
    Minisat::SimpSolver::setPolarity(in, pol);
}

void miniSolver::setDecisionVar(Var v, bool dvar) {
  Var in = ex2in(v);
  assert(in != var_Undef);
  if(in != var_Undef) 
    Minisat::SimpSolver::setDecisionVar(in, dvar);
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
  Var in = ex2in(var(l));
  if(in != var_Undef) {
    ex2in_map[var(l)] = var_Undef;
    in2ex_map[in] = var_Undef;
    releaseVar(mkLit(in, sign(l)));
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
  for (size_t i = 0; i < nVars(); i++) {
    if (activity[i] > 0 && (minAct < 0 || activity[i] < minAct)) {
      minAct = activity[i];
    }
  }
  // If no variables have any activity, then there is no need to invert
  if (minAct < 0) return;
  
  for (size_t i = 0; i < nVars(); i++) {
    if (activity[i] > 0) {
      activity[i] = (1/activity[i])/(1/minAct);
    } else {
      activity[i] = 1;
    } 
  }
  rebuildOrderHeap();
}


void miniSolver::pruneLearnts() 
{
  int i, j;
  for (i = j = 0; i < learnts.size(); i++){
    Clause& c = ca[learnts[i]];
    if (!locked(c) && c.size() > 6) 
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
    return Minisat::SimpSolver::modelValue(in);
}

lbool miniSolver::modelValue(const Var x) const 
{
  Var in = ex2in(x);
  if (in == var_Undef)
    return l_Undef;
  else
    return Minisat::SimpSolver::modelValue(in);
}

lbool miniSolver::curVal(const Var x) const {
  Var in = ex2in(x);
  if(in == var_Undef)
    return l_Undef;
  else  
    return Minisat::SimpSolver::value(in);
}

lbool miniSolver::curVal(const Lit x) const {
  Lit in = ex2in(x);
  if(in == lit_Undef)
    return l_Undef;
  else  
    return Minisat::SimpSolver::value(in);
}

vector<Lit> miniSolver::getIth_clauses(int ith) const {
  vector<Lit> cl {};
  if(ith >= clauses.size() || isRemoved(clauses[ith]))
    return cl;
  auto &c = ca[clauses[ith]];
  if(satisfied(c))
    return cl;
  for(int i=0; i< c.size(); i++)
    if(value(c[i]) != l_False)
      cl.push_back(in2ex(c[i]));
  return cl;
}

vector<Lit> miniSolver::getIth_learnts(int ith) const {
  vector<Lit> cl {};
  if(ith >= learnts.size() || isRemoved(learnts[ith]))
    return cl;
  auto &c = ca[learnts[ith]];
  if(satisfied(c))
    return cl;
  for(int i=0; i< c.size(); i++)
    if(value(c[i]) != l_False)
      cl.push_back(in2ex(c[i]));
  return cl;
}

