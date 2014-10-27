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

#include <ilcplex/cplex.h> 
#include <map>
#include <vector>
#include "maxhs/core/MaxSolverTypes.h"
#include "maxhs/core/Bvars.h"
#include "minisat/core/SolverTypes.h"
#include "minisat/utils/System.h"

using namespace Minisat;
using std::vector;

namespace MaxHS_Iface {
  class Cplex {
  public:
    Cplex(Bvars b);
    ~Cplex();

    Weight solveBudget(vector<Lit>& solution, double timeLimit) {
      //return a setting of all bvars. If the var is not mentioned
      //in the cplex problem, return the literal that has zero weight
      //in the solution. 
      stime = cpuTime();
      prevTotalTime = totalTime;
      auto val = solve_(solution, timeLimit);
      totalTime += cpuTime() - stime;
      stime = -1;
      numSolves++;
      return val; 
    }
    
    Weight solve(vector<Lit>& solution) {
      return solveBudget(solution, -1);
    }

    bool is_valid() { return solver_valid; }
    bool add_clausal_constraint(const vector<Lit>& con);
    //void add_impl_constraint(Lit blit, const vector<Lit>& con);

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
    int nSolves() { return numSolves; }

  protected:
    Bvars bvars;
    CPXENVptr env;
    CPXLPptr mip;
    bool solver_valid;

    //Hold the Cplex variables---indexed by ints.
    //IloBoolVarArray bool_variables;
    //IloObjective cplex_obj;

    void processError(int status, bool terminal, const char *msg);
    void addNewVar(Var ex);

    //Stats
    int numSolves;
    double totalTime, stime, prevTotalTime;
    int numConstraints, numNonCoreConstraints;
    uint64_t totalConstraintSize, totalNonCoreSize;

    Weight getSolution(vector<Lit> &solution); 
    Weight solve_(vector<Lit>& solution, double timeLimit);

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


