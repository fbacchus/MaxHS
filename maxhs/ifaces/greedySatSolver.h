/***********[greedySatSolver.h]
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

/* greedysat interface
*/

#ifndef GREEDYSATSOLVER_H
#define GREEDYSATSOLVER_H

#include "maxhs/core/MaxSolverTypes.h"
#include "maxhs/core/Bvars.h"
#include "maxhs/ifaces/miniSatSolver.h"
#include "minisat/core/SolverTypes.h"

namespace MaxHS_Iface {
  class GreedySatSolver : public miniSolver {
  public:
    GreedySatSolver(Bvars& b);
    virtual ~GreedySatSolver();
    bool addClauseGreedy(const vector<Lit>& lts, bool count);
    bool addMutex(const vector<Lit>& mx, Var dvar);
    lbool solve() {
      return SatSolver::solve();
    }
  protected:
    Bvars& bvars;
    Lit pickBranchLit();
    void ensureLit(Lit l);
    void ensureMxMap(Lit p);
    void cancelUntil(int level); //override cancelUntil
    void uncheckedEnqueue(Lit, Minisat::CRef);
    vector<lbool> isDvar;  //l_Undef == not dvar, l_True == core Dvar l_False == noncore dvar

    //static
    vector<int> satCount;
    vector<Weight> wt;    
    vector<vector<Lit>> inputClauses; 
    vector<vector<int>> occurList; 
    vector<Lit> clsIsSat;
    int nsatClauses;

    const int noMutex {-1};
    vector<int> mx_map;
    struct Mutex {
      Var dVar; 
      vector<Lit> mx; 
      Mutex(Var d, vector<Lit> m) : dVar {d}, mx {m} {}
    };
    vector<Mutex> mutexes;
    vector<Lit> nonCoreMxToProcess;

    struct ClsOrderLt {
      //minisat heap is a min-heap. Want the "minimum" lit to be the lit
      //that satisfies the most clauses for the least wt. I.e., 
      //x < y if satcount(x)/wt(x) > satcount(x)/wt(y). Note lits have
      //been converted to indicies before putting into the heap.
      bool operator() (Lit x, Lit y) const {
	//cout << "ClsOrderLt(" << x << "," << y << ") sc(" << sc[toInt(x)] << "," << sc[toInt(y)] << ") "
	//   << " wt(" << wts[toInt(x)] << "," << wts[toInt(y)] << ")\n";

	if(sc[toInt(x)] == sc[toInt(y)] && wts[toInt(x)] == wts[toInt(y)])
	  return x < y;
	return better(sc[toInt(x)], wts[toInt(x)], sc[toInt(y)], wts[toInt(y)]);
      }
      bool better(int sc1, Weight wt1, int sc2, Weight wt2) const {
	//return true if the metric (sc1, w1) (satcount, litwt)
	//represents a better choice than (sc2, w2).
	if(wt1 == 0 && wt2 == 0)
	  return sc1 > sc2;
	else if(wt1 == 0 && wt2 > 0)
	  return (sc1 > 0 || sc2 == 0);
	else if(wt1 > 0 && wt2 == 0)
	  return (sc1 > 0 && sc2 == 0);
	else //(wt1 > 0 && wt2 > 0)
	  return sc1/wt1 > sc2/wt2;
      }
      vector<Weight>& wts;
      vector<int>& sc;
      ClsOrderLt(vector<Weight>& w,  vector<int>& c) : wts (w), sc (c) {}
    };

    Heap<Lit,ClsOrderLt,Minisat::MkIndexLit> sftcls_heap;

    lbool solve_(const vector<Lit>& assumps, vector<Lit>& conflict,
		 int64_t confBudget, int64_t propBudget);
  };
  
} //end namespace

#endif 
