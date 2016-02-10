/***********[Cplex.cc]
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

#include <iostream>
#include <algorithm>
#include <string>
#include <cstring>
#include <cmath>
#include "maxhs/ifaces/Cplex.h"
#include "maxhs/utils/io.h"
#include "minisat/utils/System.h"
#include "maxhs/utils/Params.h"


//#include <stdexcept>

using namespace MaxHS_Iface;
using std::cout;
using std::endl;
using std::min;

Cplex::Cplex(Bvars& b, vector<lbool>& ubsofts) :
  bvars (b),
  ubModelSofts (ubsofts),
  env {nullptr},
  mip {nullptr},
  solver_valid {true},
  exUnits {},
  numSolves {0},
  totalTime {0},
  stime {-1},
  prevTotalTime {0},
  numConstraints {0},
  numNonCoreConstraints {0},
  totalConstraintSize {0},
  totalNonCoreSize {0},
  in2ex_map {},
  ex2in_map {}
{
  int status;
  env = CPXopenCPLEX(&status);
  if(env == nullptr) 
    processError(status, true, "Could not open CPLEX environment");

  if(params.cplex_output &&
     (status = CPXsetintparam(env, CPX_PARAM_SCRIND, CPX_ON)))
     cout << "c WARNING. failure to turn on CPLEX screen indicator, error " << status << "\n";

  cout << "c IBM CPLEX version " << CPXversion(env) << "\n";
  
  /*  if(!params.cplex_output) {
    env.setOut(env.getNullStream());
    env.setWarning(env.getNullStream());
    env.setError(env.getNullStream());
    }*/

  //model = IloModel(env);
  //bool_variables = IloBoolVarArray(env);
  //cplex_obj = IloMinimize(env);
  //model.add(bool_variables);
  //model.add(cplex_obj);
  //cplex = IloCplex(model);

  if(!(mip = CPXcreateprob(env, &status, "cplex_prob")))
    processError(status, true, "Could not create CPLEX problem");
  if(status = CPXchgprobtype(env, mip, CPXPROB_MILP))
    processError(status, false, "Could not change CPLEX problem to MIP");
  if(status = CPXsetdblparam(env, CPX_PARAM_EPAGAP, 0.0))
    processError(status, false, "Could not set CPLEX absolute gap");
  if(status = CPXsetdblparam(env, CPX_PARAM_EPGAP, 0.0))
    processError(status, false, "Could not set CPLEX relative gap");
  if(status = CPXsetintparam(env, CPX_PARAM_CLOCKTYPE, 1))
    processError(status, false, "Could not set CPLEX CLOCKTYPE");
  if(status = CPXsetintparam(env, CPX_PARAM_THREADS, params.cplex_threads))
    processError(status, false, "Could not set CPLEX global threads");
  if(status = CPXsetintparam(env, CPX_PARAM_DATACHECK, params.cplex_data_chk))
    processError(status, false, "Could not set CPLEX Data Check");

  //solution pool

  if(status = CPXsetintparam(env, CPX_PARAM_POPULATELIM, params.cplex_pop_nsoln))
    processError(status, false, "Could not set CPLEX Population limit");
  if(status = CPXsetdblparam(env, CPX_PARAM_SOLNPOOLAGAP, 0.0))
    processError(status, false, "Could not set CPLEX pool absolute gap");
  if(status = CPXsetdblparam(env, CPX_PARAM_SOLNPOOLGAP, 0.0))
    processError(status, false, "Could not set CPLEX pool relative gap");
}

Cplex::~Cplex(){
  int status;
  if(mip &&
     (status = CPXfreeprob(env, &mip)))
     processError(status, false, "Could not free the cplex mip model");
  if(env &&
     (status = CPXcloseCPLEX(&env)))
    processError(status, false, "Could not close the cplex environment");
}

void Cplex::processError(int status, bool terminal, const char *msg) {
  char errmsg[CPXMESSAGEBUFSIZE];
  auto errstr = CPXgeterrorstring(env, status, errmsg);
  cout << "c WARNING. " << msg << "\n";
  if(errstr)
    cout << "c WARNING. " << errmsg << "\n";
  else
    cout << "c WARNING. error code = " << status << "\n";
  if(terminal)
    solver_valid = false;
}

void Cplex::ensure_mapping(const Var ex) {
//Create new cplex bool variable if one does not already exist 
  if (ex >= (int) ex2in_map.size())
    ex2in_map.resize(ex+1,var_Undef);
  
  if(ex2in_map[ex] == var_Undef) {
    int newCplexVar = CPXgetnumcols(env, mip);
    ex2in_map[ex] = newCplexVar;
    if (newCplexVar >= (int) in2ex_map.size())
      in2ex_map.resize(newCplexVar+1, var_Undef);
    in2ex_map[newCplexVar] = ex;
    addNewVar(ex);
  }
}

void Cplex::addNewVar(Var ex) {
  //add bvar "ex" to Cplex as a new column with its weight being
  //in the objective fn.
  double clsWt {bvars.wt(ex)};
  double lb {0};
  double ub {1};
  char type {'B'};
  int status;
/*  double intPart;
    if(modf(clsWt, &intPart) > 0) { //reset abs gap to zero if dealing with non-int weights
    cout << "c Non-int weights detected Resetting cplex absolute gap to zero\n";
    if(status = CPXsetdblparam(env, CPX_PARAM_EPAGAP, 0))
      processError(status, false, "Could not set CPLEX absolute gap");
      }
*/
  
  status = CPXnewcols(env, mip, 1, &clsWt, &lb, &ub, &type, nullptr);
  if(status) {
    processError(status, false, "Could not create new CPLEX variable");
    cout << "c WARNING. var = " << ex << " wt = " << clsWt << "\n";
  }
}

void Cplex::setExUnits(Lit l) {
  //mark external lit as being true in exUnits.
  size_t i = bvars.toIndex(var(l));
  if(i  >= exUnits.size())
    exUnits.resize(i+1, l_Undef);
  if(exUnits[i] != l_Undef)
    cout << "c ERROR: positive and negative units of same variable added to Cplex\n";
  exUnits[i] = sign(l) ? l_False : l_True;

  /*
    cout << "setExUnits(" << l << ") exUnits[" << i << "] = " << exUnits[i] << "\n";
    */

}

lbool Cplex::getExUnits(Lit l) {
  //return value of lit l if its variable was previously added as a unit
  size_t i = bvars.toIndex(var(l));

/*  cout << "getExUnits(" << l << ") exUnits[" << i << "]\n";
  cout << "exUnits.size() = " << exUnits.size() << "\n";
  if(exUnits.size() > i) 
    cout << "exUnits[" << i << "] = " << exUnits[i] << "\n";*/


  if(i >= exUnits.size())
    return l_Undef;
  else if(exUnits[i] == l_True) 
    return sign(l) ? l_False : l_True;
  else if(exUnits[i] == l_False) 
    return sign(l) ? l_True : l_False;
  else
    return l_Undef;
}

bool Cplex::add_clausal_constraint(vector<Lit>& theCon) {
  //TODO: the return value is being used for two purposes, error and to indicate 
  //a non core...this should be fixed.

  //cout << "Cplex adding clause " << theCon;

  if(!solver_valid)
    return false;

  if(theCon.size() > 1) {
    //simplify non-unit based on already added units
    size_t cur_size, examine;
    for(cur_size = examine = 0; examine < theCon.size(); examine++) {
      if(!bvars.isBvar(theCon[examine])) {
	cout << "c ERROR: Cplex passed constraint with non-b-variable\n"
	     << theCon << "\n";
	return false;
      }
      lbool v = getExUnits(theCon[examine]);
      if(v == l_True) 
	return true; //tautological constraint
      else if(v == l_False)
	continue;       //can remove this lit
      else 
	theCon[cur_size++] = theCon[examine];
    }
    theCon.resize(cur_size);
  }

  if(theCon.size() == 1) {
    if(!bvars.isBvar(theCon[0])) {
      cout << "c ERROR: Cplex passed constraint with non-b-variable\n"
	   << theCon << "\n";
      return false;
    }
    setExUnits(theCon[0]);
    //If the bvar has never been seen before and is a non-core add it
    //into CPLEX. "getSolution" already returns the non-core (must satisfy
    //the soft clause) setting for all bvars not in Cplex's model
    if(ex2in(theCon[0]) == var_Undef && bvars.isNonCore(theCon[0]))
      return true; //Don't add constraint.
  }

  numConstraints++;
  totalConstraintSize += theCon.size();


  bool nonCore {false};
  vector<int> cplex_vars {};
  vector<double> cplex_coeff {};
  int numNeg {0};
  char sense {'G'};
  double rhs;
  int beg {0};

  for(auto lt: theCon) {
    ensure_mapping(lt);
    cplex_vars.push_back(ex2in(lt));
    if(bvars.isCore(lt))
      cplex_coeff.push_back(1.0);
    else {
      cplex_coeff.push_back(-1.0);
      nonCore = true;
      numNeg++;
    }
  }
  if(nonCore) {
    numNonCoreConstraints++;
    totalNonCoreSize += theCon.size();
  }
  rhs = 1.0 - numNeg;
  int status = CPXaddrows(env, mip, 0, 1, cplex_vars.size(), &rhs, &sense,
			  &beg, cplex_vars.data(), cplex_coeff.data(),
			  nullptr, nullptr);
  if(status) {
    processError(status, false, "Could not create CPLEX clausal constraint");
  }
  return (nonCore);
}

bool Cplex::add_mutex_constraint(vector<Lit>& theCon) {
  //At most one of the literals in theCon can be true.
  //cout << "Cplex adding Mutex " << theCon << "\n";

  if(!solver_valid)
    return false;

  if(theCon.size() <= 1) {
    cout << "c WARNING: Cplex passed a mutex of size less than 2\n"
	 << "c " << theCon << "\n";
    return false;
  }

  //simplify non-unit based on already added units
  bool oneTrue {false};
  size_t trueLitIndex {0};
  size_t cur_size, examine;
  for(cur_size = examine = 0; examine < theCon.size(); examine++) {
    if(!bvars.isBvar(theCon[examine])) {
      cout << "c ERROR: Cplex passed mutex with non-b-variable\n"
	   << "c " << theCon << "\n";
      return false;
    }
    lbool v = getExUnits(theCon[examine]);
    if(v == l_True) {
      if(oneTrue) {
	cout << "c ERROR: Cplex passed mutex with more than one lit forced to be true\n"
	     << "c " << theCon << "\n";
	return false;
      }
      oneTrue=true;
      trueLitIndex = cur_size;
      theCon[cur_size++] = theCon[examine];
    }
    else if(v == l_False)
      continue;       //can remove this lit
    else 
      theCon[cur_size++] = theCon[examine];
  }
  theCon.resize(cur_size);

  if(theCon.size() <= 1)
    //mutex has become redundant.
    return true;

  if(oneTrue) { //force remaining to false
    vector<Lit> forced (1);
    for(size_t i = 0; i < theCon.size(); i++)
      if(i != trueLitIndex) {
	forced[0] = ~theCon[i];
	add_clausal_constraint(forced);
      }
    return true;
  }

  vector<int> cplex_vars {};
  vector<double> cplex_coeff {};
  int numNeg {0};
  char sense {'L'};
  double rhs;
  int beg {0};

  for(auto lt: theCon) {
    ensure_mapping(lt);
    cplex_vars.push_back(ex2in(lt));
    if(bvars.wt(lt) > 0)
      cplex_coeff.push_back(1.0);
    else {
      cplex_coeff.push_back(-1.0);
      numNeg++;
    }
  }

  rhs = 1.0 - numNeg;
  int status = CPXaddrows(env, mip, 0, 1, cplex_vars.size(), &rhs, &sense,
			  &beg, cplex_vars.data(), cplex_coeff.data(),
			  nullptr, nullptr);
  if(status) {
    processError(status, false, "Could not create CPLEX mutex constraint");
  }
  return true;
}

/*void Cplex::add_impl_constraint(Lit blit, const vector<Lit>& theCon){
    IloExpr expr(env);
    numConstraints++;
    totalConstraintSize += theCon.size() + 1;
    int k = -theCon.size();
    ensure_mapping(blit);
    IloBoolVar& blitvar = bool_variables[ex2in(blit)];
    if(bvars.wt(blit) > 0) 
      expr += k * blitvar;
    else 
      expr += k * (1 - blitvar);
    for(auto lt: theCon) {
      ensure_mapping(lt);
      IloBoolVar &boolvar = bool_variables[ex2in(lt)];
        if(bvars.wt(lt) > 0)
	  expr += boolvar;
	else 
	  expr += (1 - boolvar);
    }
    model.add(0 <= expr);
    }*/

Weight Cplex::solve_(vector<Lit> &solution, double timeLimit) {   
  //return a setting of all bvariables.
  int status;

  timeLimit = (timeLimit < 0) ? 1e+75 : timeLimit;
  if(status = CPXsetdblparam(env, CPX_PARAM_TILIM, timeLimit))
    processError(status, false, "Could not set CPLEX time limit");
  if(status = CPXsetintparam(env, CPX_PARAM_MIPEMPHASIS,
			     CPX_MIPEMPHASIS_OPTIMALITY))
    processError(status, false, "Could not set CPLEX Optimality Emphasis");
  
  solution.clear();
  if(params.cplex_write_model) {
    auto fn_start = params.instance_file_name.find_last_of('/');
    std::string fname = "mip_" 
      + params.instance_file_name.substr(fn_start+1)
      + std::to_string(numSolves) + ".mps";
    if(status = CPXwriteprob(env, mip, fname.c_str(), nullptr))
      processError(status, false, "Could not write MIPS model");
    //cplex.exportModel(fname.c_str());
  }

  if(params.bestmodel_mipstart) {
    //clear old starts
    if(CPXgetnummipstarts(env, mip) > 0) {
      status = CPXdelmipstarts(env, mip, 0, CPXgetnummipstarts(env, mip)-1);
      if(status)
	processError(status, false, "CPLEX Failed to Delete MIP Starts");
    }
    vector<int> cplex_vars {};
    vector<double> cplex_vals {};
    int beg {0};
    int effort {1};
    for(size_t sftCls = 0; sftCls < bvars.n(); sftCls++) {
      auto ci = ex2in(bvars.varOfCls(sftCls));
      if(ci != var_Undef) {
	cplex_vars.push_back(ci);
	double val = (ubModelSofts[sftCls]==l_True) ? 0.0 : 1.0;
	cplex_vals.push_back(val);
      }
    }

    if(!cplex_vars.empty()) {
      status = CPXaddmipstarts(env, mip, 1, cplex_vars.size(), &beg, cplex_vars.data(), cplex_vals.data(), &effort, nullptr);
      if(status) 
	processError(status, false, "CPLEX Failed to add best model as MIP start");
    }
  }

  status = CPXmipopt(env, mip);
  if(status) 
    processError(status, false, "CPLEX Failed to optmize MIP");
  status = CPXgetstat(env, mip);
  
  if(status == CPXMIP_OPTIMAL || status == CPXMIP_OPTIMAL_TOL)
    return getSolution(solution);
  else {
    char buf[CPXMESSAGEBUFSIZE];
    char* p = CPXgetstatstring(env, status, buf);
    if(p)
      cout << "c WARNING. Cplex status = " << status << " " << buf << "\n";
    else
      cout << "c WARNING. Cplex status = " << status << "\n";
    return -1;
  }
}

Weight Cplex::getSolution(vector<Lit>& solution) {
  //bvars.litOfCls is the literal with non-zero wt (relaxing the soft clause)
  double objval {};
  int status;
  status = CPXgetobjval(env, mip, &objval);
  if(status)
    processError(status, false, "Problem getting mip objective value");

  int nvars = CPXgetnumcols(env, mip);
  vector<double> vals(nvars,0.0); 

  if(nvars>0) {
    status = CPXgetx(env, mip, vals.data(), 0, nvars-1);
    if(status)
      processError(status, false, "Problem getting mip variable assignments");
  }

  for(size_t sftCls=0; sftCls < bvars.n(); sftCls++) {
    auto ci = ex2in(bvars.varOfCls(sftCls));
    if(ci == var_Undef)
      solution.push_back(~bvars.litOfCls(sftCls));
    else {
      auto val = vals[ci];
      if(val > 0.99)
	solution.push_back(bvars.litOfCls(sftCls));
      else if (val < 0.01)
	solution.push_back(~bvars.litOfCls(sftCls));
      else { //found unset value
	solution.clear();
	return -1;
      }
    }
  }
  return objval;
}

int Cplex::populate(double timeLimit) {
  int status;
  timeLimit = (timeLimit < 0) ? 1e+75 : timeLimit;
  if(status = CPXsetdblparam(env, CPX_PARAM_TILIM, timeLimit))
    processError(status, false, "Could not set CPLEX time limit for populate");

  status = CPXpopulate(env, mip);
  if(status) 
    processError(status, false, "CPLEX Failed to Populate");
  int nsolns = CPXgetsolnpoolnumsolns(env, mip);
  if(nsolns == 0)
    cout << "c Tried populate but cplex Soln Pool found no solutions\n";
  return nsolns;
}

void Cplex::getPopulatedSolution(int i, vector<Lit>& solution) {
  int nvars = CPXgetnumcols(env, mip);
  int nsolns = CPXgetsolnpoolnumsolns(env, mip);
  vector<double> vals(nvars,0.0); 
  solution.clear();

  if(nvars>0 && nsolns > i) {
    auto status = CPXgetsolnpoolx(env, mip, i, vals.data(), 0, nvars-1);
    if(status) {
      processError(status, false, "Problem getting solution from solution pool");
      return;
    }

    
    for(size_t sftCls=0; sftCls < bvars.n(); sftCls++) {
      auto ci = ex2in(bvars.varOfCls(sftCls));
      if(ci == var_Undef)
	solution.push_back(~bvars.litOfCls(sftCls));
      else {
	auto val = vals[ci];
	if(val > 0.99)
	  solution.push_back(bvars.litOfCls(sftCls));
	else if (val < 0.01)
	  solution.push_back(~bvars.litOfCls(sftCls));
	else { //found unset value
	  solution.clear();
	  return;
	}
      }
    }
  }
}
