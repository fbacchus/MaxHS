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

namespace MaxHS_Iface {
  class GreedySolver {
  public:
    GreedySolver(Bvars& b);
    ~GreedySolver();
    //external interface is in terms of b-literals
    bool addClause(const vector<Lit>& lts); //should be core 
    vector<Lit> solve() {
      stime = cpuTime();
      prevTotalTime = totalTime;
      auto tmp = solve_();
      totalTime += cpuTime() - stime;
      solves++;
      return std::move(tmp);
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
    vector<int> init_sc;        //init_sc[ithSoftclause] = number of cores satisfied by ith soft clause
    vector<lbool> clsVal;       //used to remember unit soft clauses passed in.
    vector<vector<int>> cores;     //input cores; stored as sets of soft clause indices
    vector<vector<int>> occurList; //map from soft clause indicies to input cores they appear in.
    vector<char> coreIsSat;         //mark satisifed clauses
    int nsatCores;                  //count how many satisfied cores via units.

    //stats
    int solves;
    double totalTime, prevTotalTime, stime;
  };

  
} //end namespace

#endif 
