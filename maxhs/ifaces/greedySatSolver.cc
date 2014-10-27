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
#include "maxhs/core/MaxSolver.h"

using namespace MaxHS_Iface;
using namespace Minisat;

GreedySolver::GreedySolver(Bvars b) : bvars{b}, nclauses{0}, nsatClauses{0} { }

GreedySolver::~GreedySolver() { }

bool GreedySolver::addClause(const vector<Lit>& lts)
{
  //add clause to solver and update occurance list.
  vec<Lit> ps;
  for(auto lt: lts) {
    ensure_mapping(var(lt));
    ps.push(ex2in(lt));
  }
  bool retVal = Minisat::Solver::addClause_(ps);

  /*cout << "c GreedyCls: " << ps << "\n";*/

  size_t nl = static_cast<size_t>(Minisat::Solver::nVars()*2);
  if(nl > occurList.size()) {
    /*cout << "Growing OccurList old size = " << occurList.size()
      << " need " << nl << "\n";*/
    for(size_t j = occurList.size() ; j < nl; j++) {
      //ensure we allocate an occur list vector for both literals of var(ps[i])
      occurList.emplace_back();
      /*cout << "Added vector[" << j << "] " << occurList[j] << "\n";*/
    }
  }

  for(int i = 0; i < ps.size(); i++) {
    int index = Minisat::toInt(ps[i]);
    occurList[index].push_back(nclauses);
  }
  nclauses++;
  clsIsSat.push_back(lit_Undef);
  return retVal;
}

Lit GreedySolver::pickBranchLit() {
  syncTrails();
  Lit next = lit_Undef;
  int bstCount{};
  Weight bstWt{};

  if(nclauses == nsatClauses) {
    for(Var v = 0; v < Minisat::Solver::nVars(); v++)
      if(Minisat::Solver::value(v) == l_Undef) {
	Lit pos = mkLit(v,0);
	Lit neg = mkLit(v,1);
	return (litWt(pos) < litWt(neg) ? pos : neg);
      }
    return next;
  }

  for(Var v = 0; v < Minisat::Solver::nVars(); v++)
    if(Minisat::Solver::value(v) == l_Undef) 
      for(int s = 0; s < 2; s++) {
	Lit p = mkLit(v,s);
	if(next==lit_Undef) { 
	  next = p;
	  bstCount = satCount(p);
	  bstWt = litWt(p);
	}
	else if(better(satCount(p), litWt(p), bstCount, bstWt)) {
	  next = p;
	  bstCount = satCount(p);
	  bstWt = litWt(p);
	}
      }
  /*cout << "PBL lit = " << next << " count = " << bstCount
       << " wt = " << bstWt << "\n";*/
  return next;
}

int GreedySolver::satCount(Lit l)
{
  //return number of clauses satisfied by lit divided by lits wt.
  //Access bvars to get the weight of literal: Note bvars
  //expects externally ordered literals.
  int nsat {0};
  assert(Minisat::toInt(l) < occurList.size());
  for(auto cls : occurList[Minisat::toInt(l)]) {
    if (clsIsSat[cls] == lit_Undef)
      nsat++;
  }
  return nsat;
}

void GreedySolver::syncTrails() {
  //TODO this is n^2 down a trail. Could be faster if integrated
  //     more directly with sat solver's trail management.

  //update clsIsSat based on current status of sat solver's trail.
  //myTrail is the sequence of propagated lits we have accounted for.
  //1. Find sync point
  int i {0};
  for( ; i < Minisat::Solver::trail.size() &&
	 i < static_cast<int>(myTrail.size()) &&
	 Minisat::Solver::trail[i] == myTrail[i]
       ; i++) { }

  //2. Backtrack myTrail

  for(int j = myTrail.size()-1; j >= i ; j--) {
    Lit l = myTrail[j];
    int index = Minisat::toInt(l);
    for(auto cls : occurList[index]) 
      if (clsIsSat[cls] == l) {
	clsIsSat[cls] = lit_Undef;
	--nsatClauses;
      }
    myTrail.pop_back();
  }

  //3. sync with solver trail.
  for( ; i < Minisat::Solver::trail.size() ; i++) {
    Lit l = Minisat::Solver::trail[i];
    int index = Minisat::toInt(l);
    for(auto cls : occurList[index]) 
      if(clsIsSat[cls] == lit_Undef) {
	clsIsSat[cls] = l;
	++nsatClauses;
      }
    myTrail.push_back(l);
  }
}

lbool GreedySolver::solve_(const vector<Lit>& assumps, vector<Lit>& conflict,
			 int64_t confBudget, int64_t propBudget) {
  if(params.verbosity > 1)
    cout << "c Greedy has " << nclauses << " clauses\n";
  return miniSolver::solve_(assumps, conflict, confBudget, propBudget);
}

