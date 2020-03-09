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
#include <stdio.h>
#include <algorithm>
#include <string>
#include <cstring>
#include <cmath>

#ifdef GLUCOSE
#include "glucose/utils/System.h"
#else
#include "minisat/utils/System.h"
#endif

#include "maxhs/ifaces/Cplex.h"
#include "maxhs/utils/io.h"
#include "maxhs/utils/Params.h"


//#include <stdexcept>

using namespace MaxHS_Iface;
using std::cout;
using std::endl;
using std::min;

Cplex::Cplex(Bvars& b, vector<lbool>& ubmodelsofts, vector<lbool>& ubmodel, bool integerWts) :
  bvars (b),
  ubModelSofts (ubmodelsofts),
  ubModel (ubmodel),
  env {nullptr},
  mip {nullptr},
  trial_mip {nullptr},
  solver_valid {true},
  intWts {integerWts},
  LB {0}, //can't have incumbent with less than zero cost
  absGap {params.tolerance},
  exUnits {},
  numSolves {0},
  totalTime {0},
  stime {-1},
  prevTotalTime {0},
  numLPSolves {0}, 
  totalLPTime {0},
  numConstraints {0},
  numNonCoreConstraints {0},
  totalConstraintSize {0},
  totalNonCoreSize {0},
  in2ex_map {},
  ex2in_map {}
{
  if(integerWts)
    absGap = 0.75;
  int status;
  env = CPXXopenCPLEX(&status);
  if(env == nullptr)
    processError(status, true, "Could not open CPLEX environment");

  if(params.cplex_output &&
     (status = CPXXsetintparam(env, CPX_PARAM_SCRIND, CPX_ON)))
    cout << "c WARNING. failure to turn on CPLEX screen indicator, error " << status << "\n";

  cout << "c Using IBM CPLEX version " << CPXXversion(env)
       << " under IBM's Academic Initiative licencing program\n";

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

  if(!(mip = CPXXcreateprob(env, &status, "cplex_prob")))
    processError(status, true, "Could not create CPLEX problem");
  if(!(trial_mip = CPXXcreateprob(env, &status, "trial_cplex_prob")))
    processError(status, true, "Could not create CPLEX problem");
  if(status = CPXXchgprobtype(env, mip, CPXPROB_MILP))
    processError(status, false, "Could not change CPLEX problem to MIP");
  if(status = CPXXchgprobtype(env, trial_mip, CPXPROB_MILP))
    processError(status, false, "Could not change trail CPLEX problem to MIP");
  if(status = CPXXsetdblparam(env, CPX_PARAM_EPAGAP, absGap))
    processError(status, false, "Could not set CPLEX absolute gap");
  if(status = CPXXsetdblparam(env, CPX_PARAM_EPGAP, 0.0))
    processError(status, false, "Could not set CPLEX relative gap");
  if(status = CPXXsetintparam(env, CPX_PARAM_CLOCKTYPE, 1))
    processError(status, false, "Could not set CPLEX CLOCKTYPE");
  if(status = CPXXsetintparam(env, CPX_PARAM_THREADS, params.cplex_threads))
    processError(status, false, "Could not set CPLEX global threads");
  if(status = CPXXsetintparam(env, CPX_PARAM_DATACHECK, params.cplex_data_chk))
    processError(status, false, "Could not set CPLEX Data Check");
  if(status = CPXXsetintparam(env, CPX_PARAM_MIPEMPHASIS, CPX_MIPEMPHASIS_OPTIMALITY))
    processError(status, false, "Could not set CPLEX Optimality Emphasis");
  if(status = CPXXsetintparam(env, CPX_PARAM_POPULATELIM, params.cplex_pop_nsoln))
    processError(status, false, "Could not set CPLEX Population limit");
  if(status = CPXXsetintparam(env, CPX_PARAM_SOLNPOOLCAPACITY, params.cplex_pop_nsoln))
    processError(status, false, "Could not set CPLEX Solution Pool limit");
  if(status = CPXXsetintparam(env, CPX_PARAM_SOLNPOOLINTENSITY, 2))
    processError(status, false, "Could not set CPLEX Solution Pool limit");
  if(params.cplex_tune) {
    cout << "c Using cplex tune parameters\n";
    if(status = CPXXsetintparam(env, CPX_PARAM_MIPEMPHASIS, CPX_MIPEMPHASIS_BALANCED))
      processError(status, false, "Could not set CPLEX Optimality Emphasis");
    if(status = CPXXsetintparam(env, CPX_PARAM_HEURFREQ, -1))
      processError(status, false, "Could not set CPLEX heuristic frequency");
    if(status = CPXXsetintparam(env, CPX_PARAM_MIRCUTS, 1))
      processError(status, false, "Could not set CPLEX mir cuts");
    if(status = CPXXsetintparam(env, CPX_PARAM_FLOWCOVERS, 1))
      processError(status, false, "Could not set CPLEX mir cuts");
    if(status = CPXXsetdblparam(env, CPX_PARAM_BTTOL, 0.75))
      processError(status, false, "Could not set CPLEX backtrack tolerance");
    if(status = CPXXsetdblparam(env, CPX_PARAM_SOLNPOOLGAP, 0.0))
      processError(status, false, "Could not set CPLEX pool relative gap");
  }
}

Cplex::~Cplex() {
  int status;
  if(mip &&
     (status = CPXXfreeprob(env, &mip)))
    processError(status, false, "Could not free the cplex mip model");
  if(trial_mip &&
     (status = CPXXfreeprob(env, &trial_mip)))
    processError(status, false, "Could not free the trial cplex mip model");
  if(env &&
     (status = CPXXcloseCPLEX(&env)))
    processError(status, false, "Could not close the cplex environment");
}

void Cplex::processError(int status, bool terminal, const char *msg) {
  char errmsg[CPXMESSAGEBUFSIZE];
  auto errstr = CPXXgeterrorstring(env, status, errmsg);
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
    int newCplexVar = CPXXgetnumcols(env, mip);
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
  double lb {0};
  double ub {1};
  char type {'B'};
  double intPart;
  double clsWt;
  clsWt = bvars.isBvar(ex) ? bvars.wt(ex) : 0;

  if(modf(clsWt, &intPart) > 0) { //reset abs gap to zero if dealing with non-int weights
    cout << "c Non-int weights detected Resetting cplex absolute gap to zero\n";
    if(int status = CPXXsetdblparam(env, CPX_PARAM_EPAGAP, 0))
      processError(status, false, "Could not set CPLEX absolute gap");
  }

  if(int status = CPXXnewcols(env, mip, 1, &clsWt, &lb, &ub, &type, nullptr)) {
    processError(status, false, "Could not create new CPLEX variable");
    cout << "c WARNING. var = " << ex << " wt = " << clsWt << "\n";
  }
  if(int status = CPXXnewcols(env, trial_mip, 1, &clsWt, &lb, &ub, &type, nullptr)) {
    processError(status, false, "Could not create new CPLEX variable in trial mip");
    cout << "c WARNING. var = " << ex << " wt = " << clsWt << "\n";
  }
}

void Cplex::setExUnits(Lit l) {
  //mark external lit as being true in exUnits.
  size_t i = var(l);
  if(i  >= exUnits.size())
    exUnits.resize(i+1, l_Undef);
  auto val = sign(l) ? l_False : l_True;
  if(exUnits[i] != l_Undef) {
    cout << "c WARNING double add of unit to CPLEX lit = " << l << "\n";
    if(exUnits[i] != val)
      cout << "c ERROR: positive and negative units of same variable added to Cplex\n";
  }
  exUnits[i] = val;
  /*
    cout << "setExUnits(" << l << ") exUnits[" << i << "] = " << exUnits[i] << "\n";
  */
}

lbool Cplex::getExUnits(Lit l) {
  //return value of lit l if its variable was previously added as a unit
  size_t i = var(l);

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
      /*if(!bvars.isBvar(theCon[examine])) {
        cout << "c ERROR: Cplex passed constraint with non-b-variable\n"
        << theCon << "\n";
        return false;
        }*/
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
    /*if(!bvars.isBvar(theCon[0])) {
      cout << "c ERROR: Cplex passed constraint with non-b-variable\n"
      << theCon << "\n";
      return false;
      }*/
    setExUnits(theCon[0]);
    //If the bvar has never been seen before and is not a core bvar
    //then don't add it into CPLEX. Putting it into exunits will serve
    //to filter future passed constraints. But the value returned by
    //cplex from "getSolution" is unaffected by non-bvars and for 
    //b-vars the default setting is to return the non-core value for all
    //b-vars not in the cplex model.
    if(ex2in(theCon[0]) == var_Undef && !bvars.isCore(theCon[0]))
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
  CPXNNZ beg {0};

  for(auto lt: theCon) {
    ensure_mapping(lt);
    cplex_vars.push_back(ex2in(lt));
    if(bvars.isCore(lt) || (!bvars.isBvar(lt) && !sign(lt)))
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
  if(int status = CPXXaddrows(env, mip, 0, 1, cplex_vars.size(), &rhs, &sense,
                              &beg, cplex_vars.data(), cplex_coeff.data(),
                              nullptr, nullptr))
    processError(status, false, "Could not create CPLEX clausal constraint");
  if(int status = CPXXaddrows(env, trial_mip, 0, 1, cplex_vars.size(), &rhs, &sense,
                              &beg, cplex_vars.data(), cplex_coeff.data(),
                              nullptr, nullptr))
    processError(status, false, "Could not create trial CPLEX clausal constraint");
  return (nonCore);
}

bool Cplex::add_mutex_constraint(const SC_mx& mx) {
  if(!solver_valid)
    return false;

  //the ~encoding lit + all of the soft clause lits must sum to 1
  //If the encoding lit does not exist the soft clause lits must sum to <= 1
  //If a non-core, then the sum condition applies to the negated lits.

  auto mx_lits {mx.soft_clause_lits()};
  bool have_encoding_lit = (mx.encoding_lit() != lit_Undef);
  if(have_encoding_lit)
    mx_lits.push_back(~mx.encoding_lit());

  if(!mx.is_core())
    for(size_t i = 0; i < mx_lits.size(); i++)
      mx_lits[i] = ~mx_lits[i];

  //mx_lits must sum to <= 1. simplify if any are one set others to zero
  //if any are zero remove from mx_lits.

  bool oneTrue {false};
  size_t cur_size, examine;
  for(cur_size = examine = 0; examine < mx_lits.size(); examine++) {
    lbool val = getExUnits(mx_lits[examine]);
    if(val == l_True) {
      if(oneTrue) {
        cout << "c ERROR: Cplex passed mutex with more than one lit forced to be true\n"
             << "c " << mx << "\n";
        return false;
      }
      oneTrue=true;
    }
    else if(val == l_False)
      continue;
    else
      //keep the lit.
      mx_lits[cur_size++] = mx_lits[examine];
  }
  mx_lits.resize(cur_size);

  if(mx_lits.size() == 0)
    return true;

  if(oneTrue) { //force remaining to false
    vector<Lit> forced (1);
    for(size_t i = 0; i < mx_lits.size(); i++) {
      forced[0] = ~mx_lits[i];
      add_clausal_constraint(forced);
    }
    return true;
  }

  //Otherwise add the constraint that the lits sum to 1 or to <= 1

  vector<int> cplex_vars {};
  vector<double> cplex_coeff {};
  int numNeg {0};
  char sense {(have_encoding_lit ? 'E' : 'L')};
    double rhs {1.0};
  CPXNNZ beg {0};

  //add cplex constraint lt1 + lt2 ... ltk = (<=) 1
  for(auto lt: mx_lits) {
    ensure_mapping(lt);
    cplex_vars.push_back(ex2in(lt));
    if(bvars.isCore(lt) || (!bvars.isBvar(lt) && !sign(lt)))
      cplex_coeff.push_back(1.0);
    else {
      cplex_coeff.push_back(-1.0);
      numNeg++;
    }
  }

  rhs -= numNeg;
  if(int status = CPXXaddrows(env, mip, 0, 1, cplex_vars.size(), &rhs, &sense,
                              &beg, cplex_vars.data(), cplex_coeff.data(),
                              nullptr, nullptr))
    processError(status, false, "Could not create CPLEX mutex constraint");
  if(int status = CPXXaddrows(env, trial_mip, 0, 1, cplex_vars.size(), &rhs, &sense,
                              &beg, cplex_vars.data(), cplex_coeff.data(),
                              nullptr, nullptr))
    processError(status, false, "Could not create CPLEX mutex constraint");
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

/* Callbacks */

struct CBInfo {
  //we only add constraints to the model. So optimal solution to
  //previous solve is LB on this solve. Hence if we find an incumbent
  //with obj-value equal to LB we can terminate: that incumbent is optimal
  //(pointed out by George Katsirelos).
  Cplex* cplexObject;
  double LB;
  double UB;
  double absGap;
  double cplex_start_ticks;
  bool found_opt;
  bool found_better_soln;
};

extern "C" {
  static int CPXPUBLIC
  info_callback (CPXCENVptr env, void *cbdata, int wherefrom, void *cbhandle) {
    //Use info callback to all use of dynamic search.
    //Abort early if we found incumbent with cost < UB.
    //or if we found incmbent with cost == LB (then incumbent is optimal).
    int status {0};
    int hasincumbent {0};
    double objval {std::numeric_limits<double>::max()};

    CBInfo* info {static_cast<CBInfo *>(cbhandle)};

    if(status = CPXXgetcallbackinfo(env, cbdata, wherefrom, CPX_CALLBACK_INFO_MIP_FEAS, &hasincumbent))
      info->cplexObject->processError(status, false, "Could not get MIP_FEAS in CPLEX call back");

    if (hasincumbent) {
      if(status = CPXXgetcallbackinfo(env, cbdata, wherefrom, CPX_CALLBACK_INFO_BEST_INTEGER, &objval))
        info->cplexObject->processError(status, false, "Could not get incumbent value in CPLEX call back");

      //_LB should be a true lower bound on the cost of this model.
      //if we found a solution within our tolerance, we can stop declaring this solution
      //to be "optimal" (within tolerance).
      //If we have integer weights will also
      if ( fabs(objval - info->LB) <= info->absGap) {
        //printf("c CPLEX Terminating early on found incumbent achieving optimum\n");
        info->found_opt = true;
        return(1);
      }

      double cplex_current_ticks {};
      CPXXgettime(env, &cplex_current_ticks);

      /*cout << "c CPLEX start ticks = " << info->cplex_start_ticks
           << " current ticks = " << cplex_current_ticks
           << " min tick limit = " << params.cplex_min_ticks
           << " objective value gap = " << info->UB - objval
           << " (absgap = " << info->absGap
           << ")\n";*/

      if ((cplex_current_ticks - info->cplex_start_ticks) >= params.cplex_min_ticks
          && info->UB - objval > info->absGap)  {
        printf("c Cplex found better incumbent than UB (%f < %f)\n", objval, info->UB);
        info->found_better_soln = true;
        return(1);
      }
    }
    return(0);
  }
}

Weight Cplex::solve_(vector<Lit> &solution, double UB, double timeLimit) {
  //return a setting of all bvariables and lower bound on cplex model
  //as function value.
  //1. Return -1 as lower bound if error.
  //2. Will try to return solution of cost < UB.
  //4. If solution cost >= UB, solution will be optimal
  //5. If cost of solution == returned LB, solve_ found an optimal model
  //   of the cplex model.

  int status;

  //DEBUG
  //cout << "c Cplex solve passed UB = " << UB << " current LB = " << LB << "\n";

  timeLimit = (timeLimit < 0) ? 1e+75 : timeLimit;
  if(status = CPXXsetdblparam(env, CPX_PARAM_TILIM, timeLimit))
    processError(status, false, "Could not set CPLEX time limit");

  solution.clear();

  if(params.cplex_write_model)
    writeCplexModel();

  if(params.bestmodel_mipstart)
    useBestModelStart(mip);

  double cplex_start_ticks {};
  if(status = CPXXgettime(env, &cplex_start_ticks))
    processError(status, false, "Failed to get the Cplex deterministic start time");

  CBInfo myloginfo {this, LB, UB, absGap, cplex_start_ticks, false, false};
  if(status = CPXXsetinfocallbackfunc(env, info_callback, &myloginfo))
    processError(status, false, "Failed to set logging callback function");

  status = CPXXmipopt(env, mip);

  //DEBUG
  //cout << "Cplex after solve call back found_opt = " << myloginfo.found_opt
  //     << " call back better_soln = " << myloginfo.found_better_soln
  //     << "\n";

  //Check Call backs.
  if(myloginfo.found_opt) {
    if(params.verbosity > 0)
      cout << "c found incumbent of obj cost = " << LB << "\n";
    return getSolution(solution, true);
  }
  if(myloginfo.found_better_soln) {
    if(params.verbosity > 0)
      cout << "c found incumbent of cost better than UB (= " << UB << ")\n";
    return getSolution(solution, false);
  }

  //Else mipopt returned via normal means.
  if(status)
    processError(status, false, "CPLEX Failed to optmize MIP");

  status = CPXXgetstat(env, mip);
  if(params.verbosity > 2)
    cout << "c Solution Pool size " << CPXXgetsolnpoolnumsolns(env, mip) << "\n";
  if(params.verbosity > 2) {
    printf("c Solution Pool replaced %d\n", CPXXgetsolnpoolnumreplaced(env, mip));
    for(int i=0; i < CPXXgetsolnpoolnumsolns(env, mip); i++) {
      double objval {0.0};
      CPXXgetsolnpoolobjval(env, mip, i, &objval);
      printf("c Solution %d: objval = %.0f\n", i, objval);
    }
  }

  if(status == CPXMIP_OPTIMAL || status == CPXMIP_OPTIMAL_TOL) {
    //cout << "Cplex found standard solution " <<
    //(status == CPXMIP_OPTIMAL ? "OPTIMAL\n" : " WITHIN TOLERANCE\n");
    return getSolution(solution, true);
  }

  else {
    char buf[CPXMESSAGEBUFSIZE];
    char* p = CPXXgetstatstring(env, status, buf);
    if(p)
      cout << "c WARNING. Cplex status = " << status << " " << buf << "\n";
    else
      cout << "c WARNING. Cplex status = " << status << "\n";
    return -1;
  }
}

struct ebInfo {
  //callback data for testing if is forced
  Cplex* cplexObject;
  double UB;
  double LB;
};

extern "C" {
  static int CPXPUBLIC
  eb_callback (CPXCENVptr env, void *cbdata, int wherefrom, void *cbhandle) {
    //Use info callback for testing if forced.
    //we can abort early if best bound becomes >= UB.n
    int status {0};
    double bstobjval {0};

    ebInfo* info {static_cast<ebInfo *>(cbhandle)};

    if(status = CPXXgetcallbackinfo(env, cbdata, wherefrom, CPX_CALLBACK_INFO_BEST_REMAINING, &bstobjval))
      info->cplexObject->processError(status, false, "Could not get best objective in CPLEX test forced call back");

    //debug
    //cout << "eb_callback bstobjval = " << bstobjval << "\n";
    //cout << "eb_callback LB = " << info->LB << " UB = " << info->UB << "\n";

    if( bstobjval >= info->UB ) {
      //printf("c CPLEX test force Terminating early on found LB >= UB\n");
      info->LB = bstobjval;
      return(1);
    }
    return(0);
  }
}

bool Cplex::exceeds_bounds(vector<Lit>& lits, Weight upper_bound, double cpu_limit) {
  //test if making the literals in lits true forces the CPLEX model to
  //have cost greater than or equal to the upper_bound (so we can
  //force it to be false). Limit time to do test to cpu_limit.
  Weight increment {0};
  size_t cur_size, examine;
  lbool val;
  for(cur_size = examine = 0; examine < lits.size(); examine++) {
    auto l = lits[examine];
    //1. If l not in model---will increment the cost by its weight.
    if(ex2in(var(l)) == var_Undef)
      increment += (bvars.isBvar(l) ? bvars.wt(l) : 0);
    //2. Is already forced to true in cplex model---no change to weight.
    else if((val = getExUnits(l)) == l_True)
      continue;
    //3. If already forced to be false will cause infinite cost model
    //   (infeasible)
    else if(val == l_False)
      return true;
    //4. add to final testing constraint
    else
      lits[cur_size++] = lits[examine];
  }
  lits.resize(cur_size);

  //debug
  /*cout << "======Exceeds_bounds: increment = " << increment
    << " lits = " << lits << "\n";*/

  if(LB + increment > upper_bound)
    return true;
  if(lits.empty())
    return false;

  bool retval = false;
  //Now test with cplex.
  vector<int> cplex_vars {};
  vector<double> cplex_coeff {};
  int numNeg {0};
  char sense {'G'};
  double rhs;
  CPXNNZ beg {0};
  int status {0};

  for(auto lt: lits) {
    cplex_vars.push_back(ex2in(lt));
    if(bvars.isCore(lt) || (!bvars.isBvar(lt) && !sign(lt)))
      cplex_coeff.push_back(1.0);
    else {
      cplex_coeff.push_back(-1.0);
      numNeg++;
    }
  }
  rhs = lits.size() - numNeg;
  if(status = CPXXaddrows(env, trial_mip, 0, 1, cplex_vars.size(), &rhs, &sense,
                          &beg, cplex_vars.data(), cplex_coeff.data(),
                          nullptr, nullptr))
    processError(status, false, "Could not create CPLEX test forced constraint");
  if(status = CPXXsetdblparam(env, CPX_PARAM_TILIM, cpu_limit))
    processError(status, false, "Could not set CPLEX time limit in test forced constraint");
  ebInfo myebinfo {this, upper_bound, -1.0};
  if(status = CPXXsetinfocallbackfunc (env, eb_callback, &myebinfo))
    processError(status, false, "Failed to set callback function in test forced constraint");

  if(params.bestmodel_mipstart)
    useBestModelStart(trial_mip);

  status = CPXXmipopt(env, trial_mip);
  if(myebinfo.LB > 0) {
    //debug
    //cout << "exceeds_bounds call back found exceeds lb\n";
    retval = true;
  }
  else if(status) {
    char buf[CPXMESSAGEBUFSIZE];
    char* p = CPXXgetstatstring(env, status, buf);
    if(p)
      cout << "c exceed_bounds. Cplex status = " << status << " " << buf << "\n";
    else
      cout << "c WARNING. exceeds_bounds. Cplex status = " << status << "\n";
    retval = false;
  }
  else {
    double bstobjval {};
    if(status = CPXXgetbestobjval(env, trial_mip, &bstobjval)) {
      processError(status, false, "Problem getting mip best objective value");
      retval = false;
    }
    else {
      //debug
      //cout << "exceed_bounds found bstobjval = " << bstobjval << "\n";
      retval = bstobjval >= upper_bound;
    }
  }
  int nrows = CPXXgetnumrows(env, trial_mip);
  if(int status = CPXXdelrows(env, trial_mip, nrows-1, nrows-1))
    processError(status, false, "Could not delete added CPLEX test forced constraint");
  return retval;
}

Weight Cplex::solve_lp_relaxation_(vector<Weight>& solution, vector<Weight>& reduced_costs) {
  /* Solve lp relaxation. Return objective value and set the solution values
     and reduced costs---indexed by soft clause index (as in getsolution) */
  int status {0};
  bool extract {true};
  double objval {-1.0};
  int nvars = CPXXgetnumcols(env, trial_mip);
  solution.clear();
  reduced_costs.clear();
  if(nvars <= 0)
    return -1.0;

  vector<double> solnvals(nvars, 0.0);
  vector<double> redcosts(nvars, 0.0);

  if(status = CPXXchgprobtype(env, trial_mip, CPXPROB_LP)) {
    processError(status, false, "Could not change mip to lp in solve_lp_relaxation");
    extract = false;
  }
  if(extract) {
    if(status = CPXXlpopt(env, trial_mip)) {
      processError(status, false, "CPLEX Failed to optmize lp relaxation");
      extract = false;
    }
  }
  if(extract) {
    status = CPXXgetstat(env, trial_mip);
    if(status != CPX_STAT_OPTIMAL) {
      char buf[CPXMESSAGEBUFSIZE];
      char* p = CPXXgetstatstring(env, status, buf);
      if(p)
        cout << "c WARNING. Cplex status = " << status << " " << buf << "\n";
      else
        cout << "c WARNING. Cplex status = " << status << "\n";
    }
    else {
      if(status = CPXXgetobjval(env, trial_mip, &objval))
        processError(status, false, "Problem getting objective value of lp-relaxation");
      if(status = CPXXgetx(env, trial_mip, solnvals.data(), 0, nvars-1))
        processError(status, false, "Problem getting lp-relaxation variable assignments");
      if(status = CPXXgetdj(env, trial_mip, redcosts.data(), 0, nvars-1))
        processError(status, false, "Problem getting lp-relaxation variable assignments");

      solution.resize(bvars.n_bvars(), 0.0);
      reduced_costs.resize(bvars.n_bvars(), 0.0);

      //set output vectors. Note that if a soft clause variable does not exist in the
      //cplex model then its value is zero and its reduced cost is equal to its weight.
      for(size_t sftCls=0; sftCls < bvars.n_bvars(); sftCls++) {
        auto ci = ex2in(bvars.varOfCls(sftCls));
        if(ci != var_Undef) {
          solution[sftCls] = solnvals[ci];
          reduced_costs[sftCls] = redcosts[ci];
        }
        else {
          solution[sftCls] = 0.0;
          reduced_costs[sftCls] = bvars.wtNcls(sftCls);
        }
      }
    }
  }

  if(status = CPXXchgprobtype(env, trial_mip, CPXPROB_MILP))
    processError(status, true, "Could not change lp back into MIP in solve_lp_relaxation");
  vector<int> columns(nvars);
  vector<char> types(nvars, 'B');
  vector<char> u(nvars, 'U');
  vector<char> l(nvars, 'L');
  vector<double> ones(nvars, 1.0);
  vector<double> zeros(nvars, 0.0);
  for(size_t i=0; i < columns.size(); i++)
    columns[i] = i;

  if(status = CPXXchgctype(env, trial_mip, columns.size(), columns.data(), types.data()))
    processError(status, true, "Could not change variables back to binary in solve_lp_relaxation");
  if(status = CPXXchgbds(env, trial_mip, columns.size(), columns.data(), u.data(), ones.data()))
    processError(status, true, "Could not re-enforce upper bound of 1 on binary variables in solve_lp_relaxation");
  if(status = CPXXchgbds(env, trial_mip, columns.size(), columns.data(), l.data(), zeros.data()))
    processError(status, true, "Could not re-enforce lower bound of 0 on binary variables in solve_lp_relaxation");

  return objval;
}

void Cplex::writeCplexModel() {
  //write out the cplex models for debugging
  auto fn_start = params.instance_file_name.find_last_of('/');
  std::string fname = "mip_"
    + params.instance_file_name.substr(fn_start+1)
    + std::to_string(numSolves) + ".mps";
  if(int status = CPXXwriteprob(env, mip, fname.c_str(), nullptr))
    processError(status, false, "Could not write MIPS model");
}

void Cplex::useBestModelStart(CPXLPptr this_mip) {
  //use the current upper bound model as a mip start in the passed problem

  //clear old starts
  /*if(CPXXgetnummipstarts(env, this_mip) > 0) {
    if(int status = CPXXdelmipstarts(env, this_mip, 0, CPXXgetnummipstarts(env, this_mip)-1))
    processError(status, false, "CPLEX Failed to Delete MIP Starts");
    }*/
  vector<int> cplex_vars {};
  vector<double> cplex_vals {};
  CPXNNZ beg {0};
  int effort {1};
  for(size_t sftCls = 0; sftCls < bvars.n_bvars(); sftCls++) {
    auto ci = ex2in(bvars.varOfCls(sftCls));
    if(ci != var_Undef) {
      cplex_vars.push_back(ci);
      double val = (ubModelSofts[sftCls]==l_True) ? 0.0 : 1.0;
      cplex_vals.push_back(val);
    }
  }
  for(size_t v = 0; v < bvars.n_vars(); v++)
      if(!bvars.isBvar(v)) {
        auto ci = ex2in(v);
        if(ci != var_Undef) {
          cplex_vars.push_back(ci);
          double val = (ubModel[v]==l_True) ? 1.0 : 0.0;
          cplex_vals.push_back(val);
        }
      }

  if(!cplex_vars.empty()) {
    if(int status = CPXXaddmipstarts(env, this_mip, 1, cplex_vars.size(), &beg, cplex_vars.data(), cplex_vals.data(), &effort, nullptr))
      processError(status, false, "CPLEX Failed to add best model as MIP start");
  }
}

Weight Cplex::getSolution(vector<Lit>& solution, bool optimal) {
  //Return incumbent in solution and lower bound on objective value as function value
  //If passed bool "optimal" is true then cplex found optimal solution to its current model.

  double objval {};
  int status;
  if(status = CPXXgetobjval(env, mip, &objval))
    processError(status, false, "Problem getting mip objective value of incumbent");

  if(optimal) {
    if(objval > LB)
      LB = objval;
  }
  else {
    //set LB to current lower bound. Int weights ==> can round up.
    double bstobjval {};
    if(status = CPXXgetbestobjval(env, mip, &bstobjval))
      processError(status, false, "Problem getting mip best objective value");

    //DEBUG
    //cout << "Cplex getSolution objval = " << objval << " bstobjval = " << bstobjval
    //	<< " current LB = " << LB << " integer wts = " << intWts << "\n";

    if(bstobjval > LB)
      LB = bstobjval;
  }

  //cout << "Updated LB = " << LB << "\n";

  int nvars = CPXXgetnumcols(env, mip);
  vector<double> vals(nvars,0.0);

  if(nvars>0) {
    status = CPXXgetx(env, mip, vals.data(), 0, nvars-1);
    if(status)
      processError(status, false, "Problem getting mip variable assignments");
  }

  /*printf("Returned Optimum:\n[");
    for (int j = 0; j < nvars; j++)
    printf ("%d=%g, ", j+1, vals[j]);
    printf("]\n");*/

  for(size_t sftCls=0; sftCls < bvars.n_bvars(); sftCls++) {
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
  return LB;
}

int Cplex::populate(double timeLimit, double gap) {
  int status;
  timeLimit = (timeLimit < 0) ? 1e+75 : timeLimit;
  if(status = CPXXsetdblparam(env, CPX_PARAM_TILIM, timeLimit))
    processError(status, false, "Could not set CPLEX time limit for populate");

  if(status = CPXXsetdblparam(env, CPX_PARAM_SOLNPOOLAGAP, gap))
    processError(status, false, "Could not set CPLEX pool absolute gap in populate");

  if(status = CPXXsetinfocallbackfunc (env, NULL, NULL))
    processError(status, false, "Failed to unset logging callback function in populate");

  status = CPXXpopulate(env, mip);
  if(status)
    processError(status, false, "CPLEX Failed to Populate");
  int nsolns = CPXXgetsolnpoolnumsolns(env, mip);
  if(nsolns == 0)
    cout << "c Tried populate but cplex n Pool found no solutions\n";
  return nsolns;
}

void Cplex::getPopulatedSolution(int i, vector<Lit>& solution) {
  int nvars = CPXXgetnumcols(env, mip);
  int nsolns = CPXXgetsolnpoolnumsolns(env, mip);
  vector<double> vals(nvars,0.0);
  solution.clear();

  if(nvars>0 && nsolns > i) {
    auto status = CPXXgetsolnpoolx(env, mip, i, vals.data(), 0, nvars-1);
    if(status) {
      processError(status, false, "Problem getting solution from solution pool");
      return;
    }

    for(size_t sftCls=0; sftCls < bvars.n_bvars(); sftCls++) {
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
