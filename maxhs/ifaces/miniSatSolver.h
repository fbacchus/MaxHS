/***********[miniSatSolver.h]
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

/* minisat interface
   The interface maintains a mapping between interally numbered
   variables and externally numbered variables.
   This is to ensure that the internal variables are consecutively ordered,
   so that the external theory can be fed to the sat solver in parts with
   generating huge gaps in the variable numbering.
   
   This also means however, that not all external variables will be given a value
   by a found sat model.
*/

#ifndef MINISATSOLVER_H
#define MINISATSOLVER_H

#include "minisat/core/Solver.h"
#include "maxhs/ifaces/SatSolver.h"
#include "minisat/core/SolverTypes.h"

using Minisat::vec;
using Minisat::var_Undef;
using Minisat::lit_Undef;
using Minisat::mkLit;

namespace MaxHS_Iface {

//Minisat Solver
class miniSolver : public SatSolver, protected Minisat::Solver {
public:
  miniSolver() {}
  virtual ~miniSolver() {}
  bool status() const;
  bool simplify();
  bool findImplications(const vector<Lit> &assumps, vector<Lit>& unitImps);
  vector<Lit> getForced(int index);
  void updateForced(vector<Lit>& frc);


  int nAssigns() const;
  int nClauses() const;
  int nVars() const;
  bool reduceClause(vector<Lit>& lts) const;
  bool addClause(const vector<Lit>& lts);
  void newControlVar(Var b, bool dvar, lbool pol);
  void freeVar(Lit l);
  void setNoDecision(Var b);
  void printLit(Lit l) const;
  void invertVarActivities();
  void pruneLearnts(MaxHS::MaxSolver *S);
  lbool modelValue(Lit p) const;
  lbool modelValue(Var x) const;
  lbool curVal(Var x) const;
  lbool curVal(Lit x) const;
  uint64_t getProps() const { return propagations; }
  uint64_t getConfs() const { return conflicts; }

protected:
  lbool solve_(const vector<Lit>& assumps, vector<Lit>& conflict,
	       int64_t confBudget, int64_t propBudget);
  void cancelTrail(int level, vector<Lit> &bt_lits);
  void analyzeFinal(Lit p, Minisat::LSet& out_conflict);
  void ensure_mapping(const Var ex);
  void ensure_mapping(const Lit lt) {
    ensure_mapping(var(lt));
  }

    //External to internal mapping. 
  vector<Var>in2ex_map;
  vector<Var>ex2in_map;
  inline Lit in2ex(Lit lt) const {
    if(var(lt) >= (int) in2ex_map.size() ||
       in2ex_map[var(lt)] == var_Undef)
      return lit_Undef;
    else
      return mkLit(in2ex_map[var(lt)], sign(lt));
  }
  
  Var in2ex(Var v) const {
    if(v >= (int) in2ex_map.size())
      return var_Undef;
    else
      return in2ex_map[v];
  }

  
  //In most applications every internal literal of the SatSolver
  //is associated with an external literal on creation.
  //So this array function is safe...i.e., won't add var_Undef to output
  //vector. An array version of ex2in is typically not safe in this way.
  //so is not provided.

  
  void in2ex(const vec<Lit> &from, vector<Lit> &to) const {
    to.clear();
    for(int i = 0; i < from.size(); i++)
      to.push_back(in2ex(from[i]));
  }
  
  void in2ex(const vec<Var> &from, vector<Var> &to) const {
    to.clear();
    for(int i = 0; i < from.size(); i++)
      to.push_back(in2ex(from[i]));
  }
  
  Var ex2in(Var v) const {
    if(v >= static_cast<int>(ex2in_map.size()))
      return var_Undef;
    else
      return ex2in_map[v]; 
  }

  Lit ex2in(Lit lt) const {
    if(var(lt) >= static_cast<int>(ex2in_map.size()) ||
       ex2in_map[var(lt)] == var_Undef)
      return lit_Undef;
    else
      return mkLit(ex2in_map[var(lt)], sign(lt));
  }

};

} //end namespace

#endif 
