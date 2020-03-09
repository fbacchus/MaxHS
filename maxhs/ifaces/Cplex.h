/***********[Cplex.h]
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

#ifndef CPLEX_H
#define CPLEX_H

#include <ilcplex/cplexx.h> 
#include <map>
#include <vector>

#ifdef GLUCOSE
#include "glucose/core/SolverTypes.h"
#include "glucose/utils/System.h"
#else
#include "minisat/core/SolverTypes.h"
#include "minisat/utils/System.h"
#endif

#include "maxhs/core/MaxSolverTypes.h"
#include "maxhs/core/Bvars.h"
#include "maxhs/core/Wcnf.h"

#ifdef GLUCOSE
namespace Minisat = Glucose;
#endif

using namespace Minisat;
using std::vector;

namespace MaxHS_Iface {
  class Cplex {
  public:
    Cplex(Bvars& b, vector<lbool>& ubModelSofts,
          vector<lbool>& ubModel, bool integerWts);
    ~Cplex();

    Weight solveBudget(vector<Lit>& solution, double UB, double timeLimit) {
      //return a setting of all bvars in solution. If the var is not
      //mentioned in the cplex problem, return the literal that has
      //zero weight in the solution. Also return the best lower bound found by Cplex.
      //If the cost of "solution" == lower bound returned, this was an optimal cplex solution
      stime = cpuTime();
      prevTotalTime = totalTime;
      auto val = solve_(solution, UB, timeLimit);
      totalTime += cpuTime() - stime;
      stime = -1;
      numSolves++;
      return val; 
    }

    Weight solve(vector<Lit>& solution, double UB) {
      return solveBudget(solution, UB, -1);
    }

    //try to populate cplex solutions using a time limit...don't return 
    //them return the number of solutions.
    int populate(double timeLimit, double gap);
    int populate(double gap) { return populate(-1, gap); }
    void getPopulatedSolution(int, vector<Lit>&);
    //Other special purpose solvers
    //  Does the conjunction of lits cause the problem to exceed UB?
    bool exceeds_bounds(vector<Lit>& lits, Weight UB, double timeLimit);
    bool exceeds_bounds(Lit l, Weight UB, double timeLimit)
      { vector<Lit> lits {l};
        return exceeds_bounds(lits, UB, timeLimit); }

    //solve the lp relaxation...return objective value of LP relaxation
    //vector of solution weights and reduced costs indexed by soft clause index
    //e.g., solution[i] = weight of blit of i-th soft clause. 
    Weight solve_lp_relaxation(vector<Weight>& solution, vector<Weight>& reduced_costs) {
      auto startTime = cpuTime();
      auto val = solve_lp_relaxation_(solution, reduced_costs);
      totalLPTime += cpuTime() - startTime;
      numLPSolves++;
      return val;
    }

    bool is_valid() { return solver_valid; }
    bool add_clausal_constraint(vector<Lit>& con);
    bool add_mutex_constraint(const SC_mx& mx);
    bool var_in_cplex(Var v) { return ex2in(v) != var_Undef; }
    bool lit_in_cplex(Lit l) { return var_in_cplex(var(l)); }

    //stats
    int nCnstr() { return numConstraints; }
    uint64_t totalCnstrSize() { return totalConstraintSize; }
    int nNonCores() { return numNonCoreConstraints; }
    uint64_t totalNonCore() { return totalNonCoreSize; }

    double solveTime() { return totalTime-prevTotalTime; }
    double total_time() {
      if (stime >= 0)
        totalTime += cpuTime() - stime;
      return totalTime;
    }

    double total_lp_time() { return totalLPTime; }
    int nSolves() { return numSolves; }
    int nLPSolves() { return numLPSolves; }

    //public for call back access --- friend should work?
    void processError(int status, bool terminal, const char *msg);

  protected:
    Bvars& bvars;
    vector<lbool>& ubModelSofts;
    vector<lbool>& ubModel;
    CPXENVptr env;
    CPXLPptr mip;
    CPXLPptr trial_mip; //use this mip to do lp-relaxation and trial hardening
    bool solver_valid;
    bool intWts;
    double LB;
    double absGap;

    //forced units (in external ordering)
    vector<lbool> exUnits;
    void setExUnits(Lit l);
    lbool getExUnits(Lit l);

    //main processing code
    void addNewVar(Var ex);
    Weight getSolution(vector<Lit> &solution, bool optimal); 
    Weight solve_(vector<Lit>& solution, double UB, double timeLimit);
    Weight solve_lp_relaxation_(vector<Weight>& solution, vector<Weight>& reduced_costs);

    //internal cplex routines
    void writeCplexModel();
    void useBestModelStart(CPXLPptr);

    //Stats
    int numSolves;
    double totalTime, stime, prevTotalTime;
    int numLPSolves;
    double totalLPTime;
    
    int numConstraints, numNonCoreConstraints;
    uint64_t totalConstraintSize, totalNonCoreSize;


    //External to Internal Mapping
    vector<Var>in2ex_map;
    vector<int>ex2in_map;
    
    void ensure_mapping(const Var ex);
    void ensure_mapping(const Lit lt) {
      ensure_mapping(var(lt));
    }

    Var in2ex(int v) const {
      if(v >= (int) in2ex_map.size())
	return var_Undef;
      else
	return in2ex_map[v];
    }

    //In most applications every internal variable of the Cplex Solver
    //is associated with an external literal on creation.
    //So this array function is safe...i.e., won't add var_Undef to output
    //vector. An array version of ex2in is typically not safe in this way.
    //so is not provided.
    void in2ex(const vec<int> &from, vector<Var> &to) const {
      to.clear();
      for(int i = 0; i < from.size(); i++)
	to.push_back(in2ex(from[i]));
    }
  
    int ex2in(Var v) const {
      if(v >= static_cast<int>(ex2in_map.size()))
	return var_Undef;
      else
	return ex2in_map[v]; 
    }

    int ex2in(Lit lt) const {
      return ex2in(var(lt));
    }

  };
} //namespace 
#endif


