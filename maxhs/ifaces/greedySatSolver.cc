/***********[greedySatSolver.cc]
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

#include "maxhs/ifaces/greedySatSolver.h"
#include "minisat/core/SolverTypes.h"
#include "minisat/mtl/Sort.h"
#include "maxhs/core/MaxSolver.h"

using namespace MaxHS_Iface;
using namespace Minisat;

GreedySatSolver::GreedySatSolver(Bvars& b) : 
  bvars (b), 
  nsatClauses{0},
  sftcls_heap { ClsOrderLt(wt, satCount) }
 { }

GreedySatSolver::~GreedySatSolver() { }

void GreedySatSolver::ensureLit(Lit l) {
  //l is internal lit...ensure pos and neg
  size_t li = toInt(l) > toInt(~l) ? toInt(l) : toInt(~l);
  if(li >= satCount.size())
    satCount.resize(li+1,0);
  if(li >= wt.size())  {
    wt.resize(li+1, 0);
    wt[toInt(l)] = bvars.wt(in2ex(l)); //set once so dvar wts can be adjusted
    wt[toInt(~l)] = bvars.wt(in2ex(~l));
  }
  if(li >= occurList.size())
    occurList.resize(li+1);
}

void GreedySatSolver::ensureMxMap(Lit p) {
  size_t pi = toInt(p) > toInt(~p) ? toInt(p) : toInt(~p);
  if(pi >= mx_map.size())
    mx_map.resize(pi+1, noMutex);
}

bool GreedySatSolver::addClauseGreedy(const vector<Lit>& lts, bool count) {
  //add clause to solver and update occurance list.
  //adding clause might cause call to unchecked enqueue which
  //will adjust the sat counts. So set up the sat count structures
  //before adding clause to solver
  //cout << "addClauseGreedy " << lts << "\n";
  vec<Lit> ps;
  for(auto lt: lts) {
    ensure_mapping(var(lt));
    ensureLit(ex2in(lt));
    ps.push(ex2in(lt));
  }
  
  if(count) { //count towards greedy heuristic
    //first prepare ps---unchecked enqueue won't occur for already
    //valued lits---so don't want clause to count towards greedy
    //selection if it will already be true.
    Minisat::sort(ps);
    Lit p; int i, j;
    for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
      if (value(ps[i]) == l_True || ps[i] == ~p)
	return true;
      else if (value(ps[i]) != l_False && ps[i] != p)
	ps[j++] = p = ps[i];
    ps.shrink(i - j);
    
    vector<Lit> inClause;
    for(int i = 0; i < ps.size(); i++) {
      inClause.push_back(ps[i]);
      int index = toInt(ps[i]);
      occurList[index].push_back(inputClauses.size());
      satCount[index] += 1;
    }
    inputClauses.push_back(std::move(inClause));
    clsIsSat.push_back(lit_Undef);
  }
  
  return Minisat::Solver::addClause_(ps);
}

bool GreedySatSolver::addMutex(const vector<Lit>& mx, Var dvar) {
  //add an encoding of a mutual exclusion between the lits in mx.
  //use simple quadratic for now
  if(mx.size() <= 1)
    return true;

  vector<Lit> bin (2);
  for(size_t i = 0; i < mx.size(); i++)
    for(size_t j = i+1; j < mx.size(); j++) {
      bin[0] = ~mx[i];
      bin[1] = ~mx[j];
      if(!addClauseGreedy(bin,false)) //don't use this clause in greedy 
	return false;
    }
  ensure_mapping(dvar);
  auto inDvar = ex2in(dvar);
  ensureLit(mkLit(inDvar));
  wt[toInt(mkLit(inDvar))] = bvars.isCore(mx[0]) ? bvars.wt(mx[0]) : bvars.wt(~mx[0]);

  vector<Lit> imx;
  for(auto l : mx) {
    ensure_mapping(l);
    imx.push_back(ex2in(l));
  }

  //Adjust sat counts
  //Core d == (b1, ..., bk), and at most one bi can be true. So add satcount of d
  //to each bi. One will be picked---all others falsified and d is made true.
  //So total #clauses satisfied = satCount[bi] + satCount[d] (ASSUMING
  //no input core has both a d and a bi.

  //Non core -d == (-b1, .., -bk) at at least k-1 bi true. These are processed
  //at the start to first value all but one of the bi to true. This leaves -d == -bj
  //where bj is the only one not made true initially. Makeing bj true also makes d true
  //and again the #clauses satisfied =  satcount[bj] + satcount[d].
  //We can again add satcount[d] to each b---since only one will remain during
  //greedy heuristic selection phase.

  auto dlitPos = mkLit(inDvar);
  for(size_t j = 0; j < imx.size(); j++)
    if(bvars.isCore(mx[0]))
      satCount[toInt(imx[j])] += satCount[toInt(dlitPos)];
    else
      satCount[toInt(~imx[j])] += satCount[toInt(dlitPos)];
  
  int mxi = mutexes.size();
  mutexes.push_back(Mutex(inDvar, imx));
  ensureMxMap(mkLit(inDvar));
  mx_map[toInt(mkLit(inDvar))] = mx_map[toInt(mkLit(inDvar,true))] = mxi;
  for(auto il : imx) {
    ensureMxMap(il);
    mx_map[toInt(il)] = mx_map[toInt(~il)] = mxi;
  }
  return true;
}

Lit GreedySatSolver::pickBranchLit() {
  //cout << "GREEDY PICKBRANCHLIT\n";
  //cout << "  nonCoreMx size = " << nonCoreMxToProcess.size() << "\n";
  //cout << "  sftcls_heap is " << (sftcls_heap.empty() ? "empty" : "not empty") << "\n";
  Lit next = lit_Undef;
  while(next == lit_Undef && !nonCoreMxToProcess.empty()) {
    if(value(nonCoreMxToProcess.back()) != l_Undef)
      nonCoreMxToProcess.pop_back();
    else {
      next = nonCoreMxToProcess.back();
      nonCoreMxToProcess.pop_back();
      //cout << "Noncore forced " << in2ex(next) <<  " satcount " 
      //  << satCount[toInt(next)] << " wt = " << wt[toInt(next)] << "\n";
    }
  }
  while(next == lit_Undef && !sftcls_heap.empty()) {
    auto lt = sftcls_heap.removeMin();
    if(value(lt) == l_Undef) {
      //cout << "sftcls unvalued min = " << lt << " satcount " 
      //   << satCount[toInt(lt)] << " wt = " << wt[toInt(lt)] << "\n";
      next = lt;
    }
  }
  /*  if(next == lit_Undef) {
    next = Minisat::Solver::pickBranchLit();
    //cout << "pickBranchLit = " << next << " satcount " <<
    //  satCount[toInt(next)] << " wt = " << wt[toInt(next)] << "\n";
    }*/

  if(next != lit_Undef &&
     static_cast<size_t>(nsatClauses) == inputClauses.size() &&
     wt[toInt(next)] > 0)
    next = ~next;

  //cout << "PICKED " << next << " satcount " <<
  // satCount[toInt(next)] << " wt = " << wt[toInt(next)] << "\n";
  
  //debug
  /*if(static_cast<size_t>(nsatClauses) == inputClauses.size() && bvars.isCore(in2ex(next)))
    cout << "c Greedy solver WARNING...all clauses sat and picking core (costly) blit\n";
    if(static_cast<size_t>(toInt(next)) < mx_map.size() && mx_map[toInt(next)] != noMutex) {
    auto mxi = mx_map[toInt(next)];
    if(var(next) == mutexes[mxi].dVar)
      cout << "c greedy solver WARNING...selected dvar!\n";
      }*/
  return next;
}

void GreedySatSolver::cancelUntil(int level) {
  //cout << "greedy backtracking\n";
  
  if (decisionLevel() > level) {
    for (int c = trail.size()-1; c >= trail_lim[level]; c--) {
      Lit l = trail[c];
      Var x  = var(l);
      assigns [x] = l_Undef;
      if (phase_saving > 1 || (phase_saving == 1 && c > trail_lim.last()))
	polarity[x] = sign(trail[c]);
      insertVarOrder(x);

      //undo sat counts.
      int index = toInt(l);
      for(auto cls : occurList[index])
	if(clsIsSat[cls] == l) {
	  clsIsSat[cls] = lit_Undef;
	  --nsatClauses;
	  for(auto li : inputClauses[cls]) {
	    satCount[toInt(li)] += 1;
	    if(sftcls_heap.inHeap(li))
	      sftcls_heap.decrease(li);
	  }
	}
      if(!sftcls_heap.inHeap(l))
	sftcls_heap.insert(l);
    }
    qhead = trail_lim[level];
    trail.shrink(trail.size() - trail_lim[level]);
    trail_lim.shrink(trail_lim.size() - level);
  }
}

void GreedySatSolver::uncheckedEnqueue(Lit p, CRef from) {
  Solver::uncheckedEnqueue(p, from);
  //update sat counts
  int index = toInt(p);
  for(auto cls : occurList[index])
    if(clsIsSat[cls] == lit_Undef) {
      clsIsSat[cls] = p;
      ++nsatClauses;
      for(auto l : inputClauses[cls]) {
	satCount[toInt(l)] -= 1;
	if(sftcls_heap.inHeap(l))
	  sftcls_heap.increase(l);
      }
    }
}

lbool GreedySatSolver::solve_(const vector<Lit>& assumps, vector<Lit>& conflict,
			 int64_t confBudget, int64_t propBudget) {
  if(params.verbosity > 1)
    cout << "c Greedy has " << nClauses() << " clauses\n";

  //find non-cores to force initially.
  auto scount = [this](Lit x, Lit y) { return satCount[toInt(~x)] > satCount[toInt(~y)]; };
  auto isFalse = [this](Lit x) { return value(x) == l_False; };

  for(size_t i = 0; i < mutexes.size(); i++)
    if(bvars.isNonCore(in2ex(mutexes[i].mx[0]))) {
      vector<Lit> mutex { mutexes[i].mx }; //copy
      auto newEnd = std::remove_if(mutex.begin(), mutex.end(), isFalse);
      mutex.resize(std::distance(mutex.begin(), newEnd));
      std::sort(mutex.begin(), mutex.end(), scount);
      for(size_t j = 0; j < mutex.size()-1; j++) //force all but one
	nonCoreMxToProcess.push_back(~mutex[j]);
    }
  
  //Now reinit soft clause heap to account for any newly added clauses
  //and the new satcount scores.

  /*for(int i = 0; i < nInVars(); i++) {
    Lit pos = mkLit(i);
    Lit neg = mkLit(i, true);
    cout << in2ex(pos) << " In = " << pos << " satcount = " << satCount[toInt(pos)] << " wt = " << wt[toInt(pos)] << "\n";
    cout << in2ex(neg) << " In = " << neg << " satcount = " << satCount[toInt(neg)] << " wt = " << wt[toInt(neg)] << "\n";
    }*/

  sftcls_heap.clear();
  for(int i = 0; i < nInVars(); i++) {
      sftcls_heap.insert(mkLit(i));
      sftcls_heap.insert(mkLit(i,true));
  }

  return miniSolver::solve_(assumps, conflict, confBudget, propBudget);
}
