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

/* Greedy solver. Limited functionality. Works only with cores not
   non-cores.  Input a set of cores as clauses of positive b-variables
   (setting them true relaxes/falsifies a soft clause). Returns a
   solution vector containing all b-variables. b-variables set to true
   are required to satisfy the given cores, those set to false mean
   that the corresponding soft clause must be satisfied. The subset of
   true b-variables in the solution are greedily constructed to be a
   small set sufficient to satisfy the cores.
*/

#ifndef GREEDYSOLVER_H
#define GREEDYSOLVER_H

#include "maxhs/core/MaxSolverTypes.h"
#include "maxhs/core/Bvars.h"
#include "maxhs/core/Wcnf.h"

namespace MaxHS_Iface {
  class GreedySolver {
  public:
    GreedySolver(Bvars& b);
    ~GreedySolver();
    //external interface is in terms of b-literals
    bool addClause(const vector<Lit>& lts); //should be core 
    bool addMutexConstraint(const SC_mx& mx);

    vector<Lit> solve() {
      stime = cpuTime();
      prevTotalTime = totalTime;
      auto tmp = solve_();
      totalTime += cpuTime() - stime;
      solves++;
      return tmp;
    }

    double solveTime() { return totalTime-prevTotalTime; }
    double total_time() { return totalTime; }
    int nSolves() { return (int) solves; }
    void printDS(); //debugging routine
    

  protected:
    void ensureSC(int);
    void ensureCore(int);
    bool inputUnit(Lit); //units can be non-cores (but must be blits)
    void processTrueB(int);
    void processFalseB(int);
    vector<Lit> solve_();

    Weight clsWt(int i) { return bvars.wtNcls(i); }
    Bvars& bvars;
    vector<int> init_sc;           //init_sc[ithSoftclause] = number of cores satisfied by ith soft clause
    vector<lbool> clsVal;          //clsVal[soft_clause_index] == l_True if soft clause has been
                                   //falsfied (and thus some cores satisfied)
    vector<vector<int>> cores;     //input cores; stored as sets of soft clause indices
    vector<vector<int>> occurList; //map from soft clause indices to input cores they appear in.
    vector<char> coreIsSat;        //mark satisifed clauses
    int nSatCores;                 //count how many satisfied cores via units.

    //Dynamic data used during greedy solver
    vector<int> solution;
    vector<int> dyn_satCount;      //dynamic count of cores satisfied by soft clause
    vector<char> dyn_coreIsSat;    //dynamic mark of satisfied clauses
    int dyn_nSatCores;             //dynamic count of satisfied cores

    struct ClsOrderLt {
      //minisat heap is a min-heap. Want the "minimum" soft clause to
      //satisfies the most cores for the least wt. I.e.,
      //x < y if satcount(x)/wt(x) > satcount(y)/wt(y)
      //assume that weights are non-zero.
      bool operator() (int x, int y) const {
        double x_score = sc[x]*1.0/bvars.wtNcls(x);
        double y_score = sc[y]*1.0/bvars.wtNcls(y);
        if(x_score >= y_score)
          return true;
        return false;
      }
      Bvars& bvars;
      vector<int>& sc;
    ClsOrderLt(Bvars& b, vector<int>& c) : bvars (b), sc (c) {}
    };
    ClsOrderLt heap_lt;
    Heap<int,ClsOrderLt> sftcls_heap;
    void add_sc_to_soln(int soft_clause_index);

    //Mutex processing
    vector<vector<Lit>> ncore_mxes;  //store the non-core mutexes
    int n_core_mxes;                  //number of core mutexes
    vector<int> core_mx_num;          //map from soft clause index to core-mx the soft clause
                                      //is in. -1 if not in a core-mx;
    vector<char> core_mx_in_solution;
    lbool blit_curval(Lit b);
    void solution_update_ncore_mxes();

    //stats
    int solves;
    double totalTime, prevTotalTime, stime;
  };

  
} //end namespace

#endif 
