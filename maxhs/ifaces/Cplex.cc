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
#include "maxhs/ifaces/Cplex.h"
#include "maxhs/utils/io.h"
#include "minisat/utils/System.h"
#include "maxhs/utils/Params.h"


//#include <stdexcept>

using namespace MaxHS_Iface;
using std::cout;
using std::endl;
using std::min;

Cplex::Cplex(Bvars b) :
  bvars {b},
  env {nullptr},
  mip {nullptr},
  solver_valid {true},
  numSolves {0},
  totalTime {0},
  stime {0},
  prevTotalTime {0},
  numConstraints {0},
  numNonCoreConstraints {0},
  totalConstraintSize {0},
  totalNonCoreSize {0},
  in2ex_map {},
  ex2in_map{}
{
  int status;
  env = CPXopenCPLEX(&status);
  if(env == nullptr) 
    processError(status, true, "Could not open CPLEX environment");

  if(params.mip_output && 
     (status = CPXsetintparam(env, CPX_PARAM_SCRIND, CPX_ON)))
    cout << "c ERROR. Failure to turn on CPLEX screen indicator, error " << status << "\n";

  /*  if(!params.mip_output) {
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
  if(status = CPXsetdblparam(env, CPX_PARAM_EPAGAP, 0))
    processError(status, false, "Could not set CPLEX absolute gap");
  if(status = CPXsetdblparam(env, CPX_PARAM_EPGAP, 0.0))
    processError(status, false, "Could not set CPLEX relative gap");
  if(status = CPXsetintparam(env, CPX_PARAM_CLOCKTYPE, 1))
    processError(status, false, "Could not set CPLEX CLOCKTYPE gap");
  if(status = CPXsetintparam(env, CPX_PARAM_THREADS, params.mip_threads))
    processError(status, false, "Could not set CPLEX global threads");
  if(status = CPXsetintparam(env, CPX_PARAM_DATACHECK, params.mip_threads))
    processError(status, false, "Could not set CPLEX Data Check");

  /*cplex.setParam(IloCplex::EpAGap, 0);
  cplex.setParam(IloCplex::EpGap, 0);
  cplex.setParam(IloCplex::ClockType, 1);
  cplex.setParam(IloCplex::Threads, params.mip_threads);
  cplex.setParam(IloCplex::DataCheck, params.mip_data_chk);*/

  /*IloNumArray wts(env);
  for(int i = 0; i < bvars.n(); i++) {
    ensure_mapping(bvars.varOfCls(i));
    wts.add(bvars.wt(bvars.varOfCls(i)));
    }
    model.add(IloObjective(env, IloScalProd(wts, bool_variables)));
    varsInObj = bool_variables.getSize();*/
}

Cplex::~Cplex(){
  /*    bool_variables.end();
    cplex_obj.end();
    model.end();
    env.end();*/
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
  cout << "c ERROR. " << msg << "\n";
  if(errstr)
    cout << "c ERROR. " << errmsg << "\n";
  else
    cout << "c ERROR. error code = " << status << "\n";
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
  int status = CPXnewcols(env, mip, 1, &clsWt, &lb, &ub, &type, nullptr);
  if(status) {
    processError(status, false, "Could not create new CPLEX variable");
    cout << "c ERROR. var = " << ex << " wt = " << clsWt << "\n";
  }
}

bool Cplex::add_clausal_constraint(const vector<Lit>& theCon){
  if(!solver_valid)
    return false;

  bool nonCore {false};
  numConstraints++;
  totalConstraintSize += theCon.size();

  vector<int> cplex_vars {};
  vector<double> cplex_coeff {};
  int numNeg {0};
  char sense {'G'};
  double rhs;
  int beg {0};

  for(auto lt: theCon) {
    if(!bvars.isBvar(lt)) {
      cout << "c ERROR: Cplex passed constraint with non-b-variable\n"
	   << theCon << "\n";
      return false;
    }
    ensure_mapping(lt);
    cplex_vars.push_back(ex2in(lt));
    if(bvars.wt(lt) > 0)
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
    cout << "c ERROR. clause = " << theCon << " cplex_vars = " << cplex_vars
	 << " cplex_coefs = " << cplex_coeff << "rhs = " << rhs << "\n";
  }
  return (nonCore);
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
  /*cplex.setParam(IloCplex::TiLim, timeLimit);
    cplex.setParam(IloCplex::MIPEmphasis, CPX_MIPEMPHASIS_OPTIMALITY);*/
  
  //update object to include newly added variables
  /*if(varsInObj < bool_variables.getSize()) {
    if(params.verbosity > 1) 
      cout << "c Cplex::solve_: Adding " << bool_variables.getSize() - varsInObj
	<< " bvars to objective\n";
    IloNumArray wts(env);
    IloNumVarArray newVars(env);
    for(int i = varsInObj; i < bool_variables.getSize(); i++) {
      wts.add(bvars.wt(in2ex(i)));
      newVars.add(bool_variables[i]);
    }
    cplex_obj.setLinearCoefs(newVars, wts);
    varsInObj = bool_variables.getSize();
    if(params.verbosity > 2)
      cout << "c Cplex::solve_: new objective fn " << cplex_obj;
      }*/

  if(params.mip_write_model) {
    auto fn_start = params.instance_file_name.find_last_of('/');
    std::string fname = "mip_" 
      + params.instance_file_name.substr(fn_start+1)
      + std::to_string(numSolves) + ".mps";
    if(status = CPXwriteprob(env, mip, fname.c_str(), nullptr))
      processError(status, false, "Could not write MIPS model");
    //cplex.exportModel(fname.c_str());
  }

  if(CPXgetnummipstarts(env, mip) > 0) {
    status = CPXdelmipstarts(env, mip, 0, CPXgetnummipstarts(env, mip)-1);
    if(status)
      processError(status, false, "CPLEX Failed to Delete MIP Starts");
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
      cout << "c ERROR. Cplex status = " << status << " " << buf << "\n";
    else
      cout << "c ERROR. Cplex status = " << status << "\n";
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
  double *vals = new double[nvars];
  status = CPXgetx(env, mip, vals, 0, nvars-1);
  if(status)
    processError(status, false, "Problem getting mip variable assignments");

  for(int sftCls=0; sftCls < bvars.n(); sftCls++) {
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

/*void Cplex::printInfeasibility() {
 
    cout << model << endl;
    IloConstraintArray infeas(env);
    infeas.add(constraints);
    IloNumArray prefs(env); 
    for (IloInt i = 0; i < infeas.getSize(); i++) {
        prefs.add(1.0);
    }
    cplex.refineConflict(infeas, prefs);
    IloCplex::ConflictStatusArray conflict = cplex.getConflict(infeas);
    env.getImpl()->useDetailedDisplay(IloTrue);
    cout << "Conflict: " << endl;
    for (IloInt i = 0; i < infeas.getSize(); i++) {
        if (conflict[i] == IloCplex::ConflictMember) cout << "Proved: " << infeas[i] << endl;
        if (conflict[i] == IloCplex::ConflictPossibleMember) cout << "Possible: " << infeas[i] << endl;
    }
    for (int i = 0; i < bool_variables.getSize(); i++) {
        cout << "cplex var " << bool_variables[i] << " = sat var " << cplexvar_to_satvar[i] << endl;
    }
    prefs.end();
    infeas.end();
}*/
