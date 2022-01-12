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

#include <stdio.h>
#include <algorithm>
#include <cmath>
#include <cstring>
#include <iostream>
#include <string>

#ifdef GLUCOSE
#include "glucose/utils/System.h"
#else
#include "minisat/utils/System.h"
#endif

#include "maxhs/ifaces/Cplex.h"
#include "maxhs/utils/Params.h"
#include "maxhs/utils/io.h"

//#include <stdexcept>

using namespace MaxHS_Iface;
using std::cout;
using std::endl;
using std::min;

Cplex::Cplex(Bvars& b, TotalizerManager* t, vector<lbool>& ubmodelsofts,
             vector<lbool>& ubmodel, bool integerWts)
    : bvars(b),
      totalizers(t),
      ubModelSofts(ubmodelsofts),
      ubModel(ubmodel),
      solver_valid{true},
      intWts{integerWts},
      absGap{params.tolerance} {
  if (integerWts) absGap = 0.75;
  int status;
  env = CPXXopenCPLEX(&status);
  if (env == nullptr)
    processError(status, true, "Could not open CPLEX environment");

  if (params.cplex_output &&
      (status = CPXXsetintparam(env, CPX_PARAM_SCRIND, CPX_ON)))
    cout << "c WARNING. failure to turn on CPLEX screen indicator, error "
         << status << "\n";

  cout << "c Using IBM CPLEX version " << CPXXversion(env)
       << " under IBM's Academic Initiative licencing program\n";

  if (!(mip = CPXXcreateprob(env, &status, "cplex_prob")))
    processError(status, true, "Could not create CPLEX problem");
  if (!(linp = CPXXcreateprob(env, &status, "lp_cplex_prob")))
    processError(status, true, "Could not create CPLEX problem");
  if (status = CPXXchgprobtype(env, mip, CPXPROB_MILP))
    processError(status, false, "Could not change CPLEX problem to MIP");
  if (status = CPXXsetdblparam(env, CPX_PARAM_EPAGAP, absGap))
    processError(status, false, "Could not set CPLEX absolute gap");
  if (status = CPXXsetdblparam(env, CPX_PARAM_EPGAP, 0.0))
    processError(status, false, "Could not set CPLEX relative gap");
  if (status = CPXXsetintparam(env, CPX_PARAM_CLOCKTYPE, 1))
    processError(status, false, "Could not set CPLEX CLOCKTYPE");
  if (status = CPXXsetintparam(env, CPX_PARAM_THREADS, params.cplex_threads))
    processError(status, false, "Could not set CPLEX global threads");
  if (status = CPXXsetintparam(env, CPX_PARAM_DATACHECK, params.cplex_data_chk))
    processError(status, false, "Could not set CPLEX Data Check");
  if (status = CPXXsetintparam(env, CPX_PARAM_MIPEMPHASIS,
                               CPX_MIPEMPHASIS_OPTIMALITY))
    processError(status, false, "Could not set CPLEX Optimality Emphasis");
  if (status =
          CPXXsetintparam(env, CPX_PARAM_POPULATELIM, params.cplex_pop_nsoln))
    processError(status, false, "Could not set CPLEX Population limit");
  if (status = CPXXsetintparam(env, CPX_PARAM_SOLNPOOLCAPACITY,
                               params.cplex_pop_nsoln))
    processError(status, false, "Could not set CPLEX Solution Pool limit");
  if (status = CPXXsetintparam(env, CPX_PARAM_SOLNPOOLINTENSITY, 2))
    processError(status, false, "Could not set CPLEX Solution Pool limit");
  if (params.cplex_tune) {
    cout << "c Using cplex tune parameters\n";
    if (status = CPXXsetintparam(env, CPX_PARAM_MIPEMPHASIS,
                                 CPX_MIPEMPHASIS_BALANCED))
      processError(status, false, "Could not set CPLEX Optimality Emphasis");
    if (status = CPXXsetintparam(env, CPX_PARAM_HEURFREQ, -1))
      processError(status, false, "Could not set CPLEX heuristic frequency");
    if (status = CPXXsetintparam(env, CPX_PARAM_MIRCUTS, 1))
      processError(status, false, "Could not set CPLEX mir cuts");
    if (status = CPXXsetintparam(env, CPX_PARAM_FLOWCOVERS, 1))
      processError(status, false, "Could not set CPLEX mir cuts");
    if (status = CPXXsetdblparam(env, CPX_PARAM_BTTOL, 0.75))
      processError(status, false, "Could not set CPLEX backtrack tolerance");
    if (status = CPXXsetdblparam(env, CPX_PARAM_SOLNPOOLGAP, 0.0))
      processError(status, false, "Could not set CPLEX pool relative gap");
  }
}

Cplex::~Cplex() {
  int status;
  if (mip && (status = CPXXfreeprob(env, &mip)))
    processError(status, false, "Could not free the cplex mip model");
  if (linp && (status = CPXXfreeprob(env, &linp)))
    processError(status, false, "Could not free the trial cplex mip model");
  if (env && (status = CPXXcloseCPLEX(&env)))
    processError(status, false, "Could not close the cplex environment");
}

void Cplex::processError(int status, bool terminal, const char* msg) {
  char errmsg[CPXMESSAGEBUFSIZE];
  auto errstr = CPXXgeterrorstring(env, status, errmsg);
  cout << "c WARNING. " << msg << "\n";
  if (errstr)
    cout << "c WARNING. " << errmsg << "\n";
  else
    cout << "c WARNING. error code = " << status << "\n";
  if (terminal) solver_valid = false;
}

void Cplex::ensure_mapping(const Var ex) {
  // Create new cplex bool variable if one does not already exist
  if (ex >= (int)ex2in_map.size()) ex2in_map.resize(ex + 1, var_Undef);
  if (ex2in_map[ex] == var_Undef) {
    int newCplexVar = CPXXgetnumcols(env, mip);
    ex2in_map[ex] = newCplexVar;
    if (newCplexVar >= (int)in2ex_map.size())
      in2ex_map.resize(newCplexVar + 1, var_Undef);
    in2ex_map[newCplexVar] = ex;
    addNewVar(ex);
  }
}

void Cplex::addNewVar(Var ex) {
  // add bvar "ex" to Cplex as a new column with its weight being
  // in the objective fn.
  double lb{0};
  double ub{1};
  char type{'B'};
  double intPart;
  double varWt;
  varWt = bvars.isBvar(ex) ? bvars.wt(ex) : 0;

  if (modf(varWt, &intPart) >
      0) {  // reset abs gap to zero if dealing with non-int weights
    cout << "c Non-int weights detected Resetting cplex absolute gap to zero\n";
    if (int status = CPXXsetdblparam(env, CPX_PARAM_EPAGAP, 0))
      processError(status, false, "Could not set CPLEX absolute gap");
  }

  if (int status = CPXXnewcols(env, mip, 1, &varWt, &lb, &ub, &type, nullptr)) {
    processError(status, false, "Could not create new CPLEX variable");
    cout << "c WARNING. var = " << ex << " wt = " << varWt << "\n";
  }

  if (int status =
          CPXXnewcols(env, linp, 1, &varWt, &lb, &ub, nullptr, nullptr)) {
    processError(status, false,
                 "Could not create new CPLEX variable in trial mip");
    cout << "c WARNING. var = " << ex << " wt = " << varWt << "\n";
  }
}

void Cplex::setExUnits(Lit l) {
  // mark external lit as being true in exUnits.
  size_t i = var(l);
  if (i >= exUnits.size()) exUnits.resize(i + 1, l_Undef);
  auto val = sign(l) ? l_False : l_True;
  if (exUnits[i] != l_Undef) {
    if (!totalizers->isToutput(l))
      cout << "c WARNING double add of unit to CPLEX lit = " << l << "\n";
    if (exUnits[i] != val)
      cout << "c ERROR: positive and negative units of same variable added to "
              "Cplex\n";
  }
  exUnits[i] = val;
  /*
    cout << "setExUnits(" << l << ") exUnits[" << i << "] = " << exUnits[i] <<
    "\n";
  */
}

lbool Cplex::getExUnits(Lit l) {
  // return value of lit l if its variable was previously added as a unit
  size_t i = var(l);
  /*  cout << "getExUnits(" << l << ") exUnits[" << i << "]\n";
      cout << "exUnits.size() = " << exUnits.size() << "\n";
      if(exUnits.size() > i)
      cout << "exUnits[" << i << "] = " << exUnits[i] << "\n";*/
  if (i >= exUnits.size())
    return l_Undef;
  else if (exUnits[i] == l_True)
    return sign(l) ? l_False : l_True;
  else if (exUnits[i] == l_False)
    return sign(l) ? l_True : l_False;
  else
    return l_Undef;
}

bool Cplex::filter_by_units(vector<Lit>& theCon) {
  size_t cur_size, examine;
  for (cur_size = examine = 0; examine < theCon.size(); examine++) {
    lbool v = getExUnits(theCon[examine]);
    if (v == l_True) {
      return true;  // tautological constraint
    } else if (v == l_False)
      continue;  // can remove this lit
    else
      theCon[cur_size++] = theCon[examine];
  }
  theCon.resize(cur_size);
  return false;
}

void Cplex::add_clausal_constraint(vector<Lit>& theCon) {
  /*cout << "Cplex adding clause [";
  for(auto l : theCon) {
    cout << l << "[" << getExUnits(l) << ",";
    if(totalizers->isToutput(l)) {
      cout << "T:" << totalizers->get_olit_index(l) << "["
           << totalizers->get_olit_idx(l) << "]";
    }
    cout << "], ";
  }
  cout << "]\n";*/

  if (!solver_valid) return;
  if (filter_by_units(theCon)) return;
  if (theCon.empty()) {
    cout << "c ERROR cplex got contradictory clausal constraint\n";
    return;
  }

  if (theCon.size() == 1) {
    setExUnits(theCon[0]);
    if (totalizers->isToutput(theCon[0])) {
      add_tot_unit(theCon[0]);
      return;
    } else if (ex2in(theCon[0]) == var_Undef && bvars.isNonCore(theCon[0])) {
      // Non-core forced bvars never seen before need not be added
      // to CPLEX model. Instead we put these into exunits
      // and use them to reduce future passed constraints.
      // In particular, CPLEX will automatically set a b-var to its
      // non-core value, making the nonCore lit true---as this
      // adds zero cost to the hitting set.
      return;
    }
    // otherwise process unit core bvar as ordinary clausal constraint
  }

  for (auto lt : theCon) {
    // must do ensure_mapping after add_tot_output_defn
    if (totalizers->isToutput(lt)) add_tot_output_defn(lt);
    ensure_mapping(lt);
  }
  add_processed_clause(theCon);
}

void Cplex::add_processed_clause(const vector<Lit>& theCon) {
  numConstraints++;
  totalConstraintSize += theCon.size();

  bool nonCore{false};
  vector<int> cplex_vars{};
  vector<double> cplex_coeff{};
  int numNeg{0};
  char sense{'G'};
  double rhs;
  CPXNNZ beg{0};

  for (auto lt : theCon) {
    cplex_vars.push_back(ex2in(lt));
    if (bvars.isCore(lt) || totalizers->isPositiveToutput(lt) ||
        (!bvars.isBvar(lt) && !totalizers->isToutput(lt) && !sign(lt)))
      cplex_coeff.push_back(1.0);
    else {
      cplex_coeff.push_back(-1.0);
      // cout << "nonCore: " << lt<< "\n";
      nonCore = true;
      numNeg++;
    }
  }
  if (nonCore) {
    numNonCoreConstraints++;
    totalNonCoreSize += theCon.size();
  }
  rhs = 1.0 - numNeg;
  // cout << "rhs: " << rhs << ", numNeg: " << numNeg << "\n";
  if (int status =
          CPXXaddrows(env, mip, 0, 1, cplex_vars.size(), &rhs, &sense, &beg,
                      cplex_vars.data(), cplex_coeff.data(), nullptr, nullptr))
    processError(
        status, false,
        "add_processed_clause could not create CPLEX clausal constraint");
  if (int status =
          CPXXaddrows(env, linp, 0, 1, cplex_vars.size(), &rhs, &sense, &beg,
                      cplex_vars.data(), cplex_coeff.data(), nullptr, nullptr))
    processError(
        status, false,
        "add_processed_clause could not create trial CPLEX clausal constraint");
  return;
}

void Cplex::add_tot_unit(Lit tout) {
  assert(totalizers->isToutput(tout));
  assert(getExUnits(tout) == l_True);
  vector<Lit> forced_tot_outs;

  if (totalizers->isPositiveToutput(tout))
    for (auto idx = totalizers->get_olit_index(tout) - 1; idx >= 0; --idx) {
      auto t = totalizers->get_olits_from_olit(tout)[idx];
      auto val = getExUnits(t);
      if (val == l_True) continue;
      if (val == l_False) {
        cout
            << "c ERROR: forced totalizer out already set to opposite value in "
               "Cplex\n";
        return;
      }
      setExUnits(t);
      if (ex2in(t) != var_Undef) forced_tot_outs.push_back(t);
    }
  else if (totalizers->isNegativeToutput(tout))
    for (auto idx = totalizers->get_olit_index(tout) + 1;
         static_cast<size_t>(idx) <
         totalizers->get_olits_from_olit(tout).size();
         ++idx) {
      auto t = ~totalizers->get_olits_from_olit(tout)[idx];
      auto val = getExUnits(t);
      if (val == l_True) continue;
      if (val == l_False) {
        cout
            << "c ERROR: forced totalizer out already set to opposite value in "
               "Cplex\n";
        return;
      }
      setExUnits(t);
      if (ex2in(t) != var_Undef) forced_tot_outs.push_back(t);
    }

  for (auto t_forced : forced_tot_outs) add_processed_clause({t_forced});

  if (ex2in(tout) == var_Undef)
    // for unseen touts only add the implied summation constraint
    add_tot_output_constraint(tout);
  // add_tot_output_defn(tout);

  else
    add_processed_clause({tout});
}

void Cplex::add_tot_output_constraint(Lit tout) {
  // add only touts constraint on its input bvars.
  assert(totalizers->isToutput(tout));
  assert(ex2in(tout) == var_Undef);
  assert(getExUnits(tout) == l_True);

  // add constraint in terms of positive totalizer
  if (totalizers->isNegativeToutput(tout)) tout = ~tout;
  // Construct cplex constraints
  vector<int> cplex_vars{};
  vector<double> cplex_coeff{};
  char sense;
  double rhs;
  CPXNNZ beg{0};
  int nt{0}, nf{0};
  int tout_idx{totalizers->get_olit_index(tout)};
  int tout_coeff{tout_idx + 1};
  int tmax{static_cast<int>(totalizers->get_olits_from_olit(tout).size())};

  // add unvalued inputs to cplex constraint.
  for (auto l : totalizers->get_ilits_from_olit(tout)) {
    assert(bvars.isCore(l));
    auto val = getExUnits(l);
    if (val == l_True) {
      ++nt;
      continue;
    }
    if (val == l_False) {
      ++nf;
      continue;
    }
    ensure_mapping(l);
    cplex_vars.push_back(ex2in(l));
    cplex_coeff.push_back(1.0);
  }
  if (cplex_vars.empty()) {
    assert(getExUnits(tout) != l_True || tout_coeff <= nt);
    assert(getExUnits(tout) != l_False || tout_coeff > nt);
    return;
  }
  // 2. Add cplex constraints.
  if (getExUnits(tout) == l_True && nt < tout_coeff) {
    sense = 'G';
    rhs = tout_coeff - nt;
    if (cplex_vars.size() < rhs) {
      cout << "c ERROR in add_tout_constraint. Can't have " << rhs
           << " tins true since " << nf << " out of " << tmax
           << " are already false\n";
      return;
    }
    if (int status = CPXXaddrows(env, mip, 0, 1, cplex_vars.size(), &rhs,
                                 &sense, &beg, cplex_vars.data(),
                                 cplex_coeff.data(), nullptr, nullptr)) {
      processError(status, false,
                   "add_tout_constraint could not create CPLEX (A) constraint");
    }
    if (int status = CPXXaddrows(env, linp, 0, 1, cplex_vars.size(), &rhs,
                                 &sense, &beg, cplex_vars.data(),
                                 cplex_coeff.data(), nullptr, nullptr))
      processError(status, false,
                   "add_tout_constraint could not create trial CPLEX (A) "
                   "constraint");
  } else if (getExUnits(tout) == l_False &&
             static_cast<int>(cplex_vars.size()) >= (tout_coeff - nt)) {
    // constraint is trivial if less than tout_coeff-nt tins are left
    rhs = tout_coeff - nt - 1;  //'L' is <= not <
    sense = 'L';
    if (int status = CPXXaddrows(env, mip, 0, 1, cplex_vars.size(), &rhs,
                                 &sense, &beg, cplex_vars.data(),
                                 cplex_coeff.data(), nullptr, nullptr)) {
      processError(status, false,
                   "add_tout_constraint could not create CPLEX (B) constraint");
    }
    if (int status = CPXXaddrows(env, linp, 0, 1, cplex_vars.size(), &rhs,
                                 &sense, &beg, cplex_vars.data(),
                                 cplex_coeff.data(), nullptr, nullptr))
      processError(
          status, false,
          "add_tout_constraint could not create trial CPLEX (B) constraint");
  }
  return;
}

void Cplex::add_tot_output_defn(Lit tout) {
  assert(totalizers->isToutput(tout));
  if (ex2in(tout) != var_Undef)  // defn already in place.
    return;
  // add defn in terms of positive totalizer
  if (totalizers->isNegativeToutput(tout)) tout = ~tout;

  // add cplex constraints capturing the equivalence between
  // a totalizer output and its inputs
  // 1. check if the defn would be subsumed by a superseeding tout

  vector<int> cplex_vars{};
  vector<double> cplex_coeff{};
  char sense;
  double rhs;
  CPXNNZ beg{0};
  int nt{0}, nf{0};
  int tout_idx{totalizers->get_olit_index(tout)};
  int tout_coeff{tout_idx + 1};
  int tmax{static_cast<int>(totalizers->get_olits_from_olit(tout).size())};

  // add \sum unvalued inputs to cplex constraint.
  for (auto l : totalizers->get_ilits_from_olit(tout)) {
    assert(bvars.isCore(l) || totalizers->isPositiveToutput(l));
    auto val = getExUnits(l);
    if (val == l_True) {
      ++nt;
      continue;
    }
    if (val == l_False) {
      ++nf;
      continue;
    }
    ensure_mapping(l);
    cplex_vars.push_back(ex2in(l));
    cplex_coeff.push_back(1.0);
  }
  if (cplex_vars.empty()) {
    assert(getExUnits(tout) != l_True || tout_coeff <= nt);
    assert(getExUnits(tout) != l_False || tout_coeff > nt);
    return;
  }

  // 2. Add cplex constraints.
  //   Tout <==> \sum in >= tout_coeff
  //
  // A) Tout ==> \sum in >= tout_coeff
  //    CPLEX: \sum_in - tout_coeff * Tout >= 0
  //         Tout = 1 ==> \sum in >= tout_coeff; Tout = 0 ==> trivial
  //         constraint
  //    We sum over only unvalued inputs so we can subtract number true (nt)
  //    from both sizes FINAL CPLEX constraint: \sum unvalued_in - coeff*Tout
  //    >= -nt (A) is trivial if nt >= tout_coeff
  // if Tout is TRUE add only \sum in >= tout_coeff

  if (nt < tout_coeff &&
      getExUnits(tout) != l_False) {  // non-trivial constraint
    sense = 'G';
    rhs = -nt;
    bool tout_added{false};
    if (getExUnits(tout) == l_Undef) {
      ensure_mapping(var(tout));
      cplex_vars.push_back(ex2in(tout));
      cplex_coeff.push_back(-tout_coeff);
      tout_added = true;
    } else {  // tout is TRUE
      assert(getExUnits(tout) == l_True);
      rhs += tout_coeff;
    }

    /*cout << "Adding totalizer defn (A)\n"
         << tout << "[" << tout_coeff << ":" << getExUnits(tout) << ":"
         << totalizers->get_olit_idx(tout) << "]: ";
    for (size_t i = 0; i < cplex_vars.size(); ++i)
      cout << cplex_coeff[i] << "*" << in2ex(cplex_vars[i]) << " + ";
      cout << sense << " " << rhs << "\n";*/

    if (int status = CPXXaddrows(env, mip, 0, 1, cplex_vars.size(), &rhs,
                                 &sense, &beg, cplex_vars.data(),
                                 cplex_coeff.data(), nullptr, nullptr)) {
      processError(status, false,
                   "add_tot_output_defn could not create CPLEX (A) constraint");
    }
    if (int status = CPXXaddrows(env, linp, 0, 1, cplex_vars.size(), &rhs,
                                 &sense, &beg, cplex_vars.data(),
                                 cplex_coeff.data(), nullptr, nullptr))
      processError(status, false,
                   "add_tot_output_defn could not create trial CPLEX (A) "
                   "constraint");
    if (tout_added) {
      cplex_vars.pop_back();
      cplex_coeff.pop_back();
    }
  }
  //(B) \sum_in >= tout_coeff ==> TOut
  //    == TOut = 0 ==> \sum_in < tout_coeff
  //    == TOut = 0 ==> \sum_in <= tout_idx
  //
  //    CPLEX: \sum in - (max - tout_idx)*Tout <= tout_idx
  //         == \sum in -max*Tout + tout_idx*Tout <= tout_idx
  //         Tout = 1: sum in -max <= 0 -- trivial
  //         Tout = 0: \sum_in <= tout_idx <==> \sum_in < tout_coeff
  // As in (A) subtract nt from each side:
  //    FINAL CPLEX: \sum unvalued_in - (max-tout_idx)*TOut <= tout_idx - nt
  // We know that sum_in <= max - nf
  //     so TOut = 0 ==> \sum_in < tout_coeff becomes trival if we already
  //     have \sum_in < tout_coeff so max-nf < tout_coeff means constraint
  //     would be trivial and max-nf >= tout_coeff is when constraint is
  //     non-trivial
  if ((tmax - nf) >= tout_coeff && getExUnits(tout) != l_True) {
    rhs = tout_idx - nt;
    sense = 'L';
    if (getExUnits(tout) == l_Undef) {
      ensure_mapping(var(tout));
      cplex_vars.push_back(ex2in(tout));
      cplex_coeff.push_back(-(tmax - tout_idx));
    } else {
      assert(getExUnits(tout) == l_False);
    }

    /*cout << "Adding totalizer defn (B)\n"
         << tout << "[" << tout_coeff << ":" << getExUnits(tout) << ":"
         << totalizers->get_olit_idx(tout) << "]: ";
    for (size_t i = 0; i < cplex_vars.size(); ++i)
      cout << cplex_coeff[i] << "*" << in2ex(cplex_vars[i]) << " + ";
      cout << sense << " " << rhs << "\n";*/

    if (int status = CPXXaddrows(env, mip, 0, 1, cplex_vars.size(), &rhs,
                                 &sense, &beg, cplex_vars.data(),
                                 cplex_coeff.data(), nullptr, nullptr)) {
      processError(status, false,
                   "add_tot_output_defn could not create CPLEX (B) constraint");
    }
    if (int status = CPXXaddrows(env, linp, 0, 1, cplex_vars.size(), &rhs,
                                 &sense, &beg, cplex_vars.data(),
                                 cplex_coeff.data(), nullptr, nullptr))
      processError(
          status, false,
          "add_tot_output_defn could not create trial CPLEX (B) constraint");
  }
  return;
}

bool Cplex::add_mutex_constraint(const SC_mx& mx) {
  if (!solver_valid) return false;

  // the ~encoding lit + all of the soft clause lits must sum to 1
  // If the encoding lit does not exist the soft clause lits must sum to <= 1
  // If a non-core, then the sum condition applies to the negated lits.

  auto mx_lits{mx.soft_clause_lits()};
  bool have_encoding_lit = (mx.encoding_lit() != lit_Undef);
  if (have_encoding_lit) mx_lits.push_back(~mx.encoding_lit());

  if (!mx.is_core())
    for (size_t i = 0; i < mx_lits.size(); i++) mx_lits[i] = ~mx_lits[i];

  // mx_lits must sum to <= 1. simplify if any are one set others to zero
  // if any are zero remove from mx_lits.

  bool oneTrue{false};
  size_t cur_size, examine;
  for (cur_size = examine = 0; examine < mx_lits.size(); examine++) {
    lbool val = getExUnits(mx_lits[examine]);
    if (val == l_True) {
      if (oneTrue) {
        cout << "c ERROR: Cplex passed mutex with more than one lit forced to "
                "be true\n"
             << "c " << mx << "\n";
        return false;
      }
      oneTrue = true;
    } else if (val == l_False)
      continue;
    else
      // keep the lit.
      mx_lits[cur_size++] = mx_lits[examine];
  }
  mx_lits.resize(cur_size);

  if (mx_lits.size() == 0) return true;

  if (oneTrue) {  // force remaining to false
    vector<Lit> forced(1);
    for (size_t i = 0; i < mx_lits.size(); i++) {
      forced[0] = ~mx_lits[i];
      add_clausal_constraint(forced);
    }
    return true;
  }

  // Otherwise add the constraint that the lits sum to 1 or to <= 1

  vector<int> cplex_vars{};
  vector<double> cplex_coeff{};
  int numNeg{0};
  char sense{(have_encoding_lit ? 'E' : 'L')};
  double rhs{1.0};
  CPXNNZ beg{0};

  // add cplex constraint lt1 + lt2 ... ltk = (<=) 1
  for (auto lt : mx_lits) {
    ensure_mapping(lt);
    cplex_vars.push_back(ex2in(lt));
    if (bvars.isCore(lt) || (!bvars.isBvar(lt) && !sign(lt)))
      cplex_coeff.push_back(1.0);
    else {
      cplex_coeff.push_back(-1.0);
      numNeg++;
    }
  }

  rhs -= numNeg;
  if (int status =
          CPXXaddrows(env, mip, 0, 1, cplex_vars.size(), &rhs, &sense, &beg,
                      cplex_vars.data(), cplex_coeff.data(), nullptr, nullptr))
    processError(status, false, "Could not create CPLEX mutex constraint");
  if (int status =
          CPXXaddrows(env, linp, 0, 1, cplex_vars.size(), &rhs, &sense, &beg,
                      cplex_vars.data(), cplex_coeff.data(), nullptr, nullptr))
    processError(status, false, "Could not create CPLEX mutex constraint");
  return true;
}

bool Cplex::add_sum_constraint(vector<Lit>& sc_lits, int64_t k) {
  if (!solver_valid) return false;

  // all of the soft clause lits must sum to k, if is_exact = 'e'
  int sk = sc_lits.size() - k;
  cout << "sc_lits size: " << sc_lits.size() << " k: " << k << "\n";
  char exact = 'G';  // sc.is_exact();
  // sc_lits must sum to <= k. simplify if any are one set decrease k
  // if any are zero remove from sc_lits.
  // Otherwise add the constraint that the lits sum to k or to <= k
  bool k_True{false};
  bool sk_False{false};
  size_t cur_size, examine;

  // check to see which vars are already set
  for (cur_size = examine = 0; examine < sc_lits.size(); examine++) {
    lbool val = getExUnits(
        sc_lits[examine]);  // if previously defined as a unit set to true,
    if (val == l_True) {
      if (k_True) {
        cout << "c ERROR: Cplex passed sumcons with more than k lits forced to "
                "be true\n";
        return false;
      }
      k--;  // decrease size of k
      // check for exact cases
      if (k == 0 && (exact == 'E') || (exact == 'L')) {
        k_True = true;
      }
    } else if (val == l_False) {
      sk--;
      if (sk == 0) {
        sk_False = true;
      }
      continue;
    } else
      // keep the lit.
      sc_lits[cur_size++] = sc_lits[examine];
  }
  sc_lits.resize(cur_size);

  if (sc_lits.size() == 0)
    return true;  // no sum constraints to be added all vars assigned true or
                  // false
  cout << "sclits.size: " << sc_lits.size() << "\n";

  // Only if equal to K
  /*
    if(k_True) { //force remaining to false
      vector<Lit> forced (1);
      for(size_t i = 0; i < sc_lits.size(); i++) {
        forced[0] = ~sc_lits[i];
        add_clausal_constraint(forced);
      }
      return true;
    }
  */
  if (sk_False) {  // force remaining to true
    printf("A| sk is True, force remaining to true\n");
    vector<Lit> forced(1);
    for (size_t i = 0; i < sc_lits.size(); i++) {
      forced[0] = sc_lits[i];
      add_clausal_constraint(forced);
    }
    return true;
  }

  // Otherwise add the constraint that the lits sum to >=k

  vector<int> cplex_vars{};
  vector<double> cplex_coeff{};
  int numNeg{0};
  // char sense{'G'};
  char sense{exact};
  double rhs{static_cast<double>(k)};  // rhs = k?
  CPXNNZ beg{0};
  // std::cout << "a sc_lits:\n";
  // add cplex constraint lt1 + lt2 ... ltk = (<=) 1
  for (auto lt : sc_lits) {
    // std::cout << lt << " ";
    ensure_mapping(lt);
    cplex_vars.push_back(ex2in(lt));
    if (bvars.isCore(lt) || (!bvars.isBvar(lt) && !sign(lt)))
      cplex_coeff.push_back(1.0);
    else {
      // cout<< "neg coeff: "  << lt << "\n";
      cplex_coeff.push_back(-1.0);
      numNeg++;
    }
  }
  // std::cout<< "\n";
  rhs -= numNeg;

  /*std::cout << "cplex_vars: ";
  for (int l:cplex_vars){
    std::cout << "[" <<l << ", " << in2ex(l) << "]";
    }
    std::cout<< "\n";*/
  sort(cplex_vars.begin(), cplex_vars.end());
  for (size_t i = 0; i < cplex_vars.size() - 1; i++)
    if (cplex_vars[i] == cplex_vars[i + 1])
      cout << "ERROR: trying to add duplicate: " << in2ex(cplex_vars[i])
           << "\n";
  cout << "cplex vars.size(): " << cplex_vars.size()
       << " cplex coeff.size(): " << cplex_coeff.size() << "\n";
  printf("A| rhs: %f, numNeg: %d, sense: %c\n", rhs, numNeg, sense);
  if (int status =
          CPXXaddrows(env, mip, 0, 1, cplex_vars.size(), &rhs, &sense, &beg,
                      cplex_vars.data(), cplex_coeff.data(), nullptr, nullptr))
    processError(status, false, "Could not create CPLEX summation constraint");
  if (int status =
          CPXXaddrows(env, linp, 0, 1, cplex_vars.size(), &rhs, &sense, &beg,
                      cplex_vars.data(), cplex_coeff.data(), nullptr, nullptr))
    processError(status, false, "Could not create CPLEX summation constraint");
  return true;
}

/* Callbacks */

struct CBInfo {
  // we only add constraints to the model. So optimal solution to
  // previous solve is LB on this solve. Hence if we find an incumbent
  // with obj-value equal to LB we can terminate: that incumbent is optimal
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
static int CPXPUBLIC info_callback(CPXCENVptr env, void* cbdata, int wherefrom,
                                   void* cbhandle) {
  // Use info callback to all use of dynamic search.
  // Abort early if we found incumbent with cost < UB.
  // or if we found incmbent with cost == LB (then incumbent is optimal).
  int status{0};
  int hasincumbent{0};
  double objval{std::numeric_limits<double>::max()};

  CBInfo* info{static_cast<CBInfo*>(cbhandle)};

  if (status = CPXXgetcallbackinfo(env, cbdata, wherefrom,
                                   CPX_CALLBACK_INFO_MIP_FEAS, &hasincumbent))
    info->cplexObject->processError(
        status, false, "Could not get MIP_FEAS in CPLEX call back");

  if (hasincumbent) {
    if (status = CPXXgetcallbackinfo(env, cbdata, wherefrom,
                                     CPX_CALLBACK_INFO_BEST_INTEGER, &objval))
      info->cplexObject->processError(
          status, false, "Could not get incumbent value in CPLEX call back");

    //_LB should be a true lower bound on the cost of this model.
    // if we found a solution within our tolerance, we can stop declaring this
    // solution to be "optimal" (within tolerance). If we have integer weights
    // will also
    if (fabs(objval - info->LB) <= info->absGap) {
      // printf("c CPLEX Terminating early on found incumbent achieving
      // optimum\n");
      info->found_opt = true;
      return (1);
    }

    double cplex_current_ticks{};
    CPXXgettime(env, &cplex_current_ticks);

    /*cout << "c CPLEX start ticks = " << info->cplex_start_ticks
         << " current ticks = " << cplex_current_ticks
         << " min tick limit = " << params.cplex_min_ticks
         << " objective value gap = " << info->UB - objval
         << " (absgap = " << info->absGap
         << ")\n";*/

    if ((cplex_current_ticks - info->cplex_start_ticks) >=
            params.cplex_min_ticks &&
        info->UB - objval > info->absGap) {
      printf("c Cplex found better incumbent than UB (%f < %f)\n", objval,
             info->UB);
      info->found_better_soln = true;
      return (1);
    }
  }
  return (0);
}
}

Weight Cplex::solve_(vector<Lit>& solution, double UB, double timeLimit) {
  // return a setting of all bvariables and lower bound on cplex model
  // as function value.
  // 1. Return -1 as lower bound if error.
  // 2. Will try to return solution of cost < UB.
  // 4. If solution cost >= UB, solution will be optimal
  // 5. If cost of solution == returned LB, solve_ found an optimal model
  //   of the cplex model.

  int status;

  // DEBUG
  // cout << "c Cplex solve passed UB = " << UB << " current LB = " << LB <<
  // "\n";

  timeLimit = (timeLimit < 0) ? 1e+75 : timeLimit;
  if (status = CPXXsetdblparam(env, CPX_PARAM_TILIM, timeLimit))
    processError(status, false, "Could not set CPLEX time limit");

  solution.clear();

  if (params.cplex_write_model) writeCplexModel();

  if (params.bestmodel_mipstart) useBestModelStart(mip);

  double cplex_start_ticks{};
  if (status = CPXXgettime(env, &cplex_start_ticks))
    processError(status, false,
                 "Failed to get the Cplex deterministic start time");

  CBInfo myloginfo{this, LB, UB, absGap, cplex_start_ticks, false, false};
  if (status = CPXXsetinfocallbackfunc(env, info_callback, &myloginfo))
    processError(status, false, "Failed to set logging callback function");

  status = CPXXmipopt(env, mip);

  // DEBUG
  // cout << "Cplex after solve call back found_opt = " << myloginfo.found_opt
  //     << " call back better_soln = " << myloginfo.found_better_soln
  //     << "\n";

  // Check Call backs.
  if (myloginfo.found_opt) {
    if (params.verbosity > 0)
      cout << "c found incumbent of obj cost = " << LB << "\n";
    return getSolution(solution, true);
  }
  if (myloginfo.found_better_soln) {
    if (params.verbosity > 0)
      cout << "c found incumbent of cost better than UB (= " << UB << ")\n";
    return getSolution(solution, false);
  }

  // Else mipopt returned via normal means.
  if (status) processError(status, false, "CPLEX Failed to optmize MIP");

  status = CPXXgetstat(env, mip);
  if (params.verbosity > 2)
    cout << "c Solution Pool size " << CPXXgetsolnpoolnumsolns(env, mip)
         << "\n";
  if (params.verbosity > 2) {
    printf("c Solution Pool replaced %d\n",
           CPXXgetsolnpoolnumreplaced(env, mip));
    for (int i = 0; i < CPXXgetsolnpoolnumsolns(env, mip); i++) {
      double objval{0.0};
      CPXXgetsolnpoolobjval(env, mip, i, &objval);
      printf("c Solution %d: objval = %.0f\n", i, objval);
    }
  }

  if (status == CPXMIP_OPTIMAL || status == CPXMIP_OPTIMAL_TOL) {
    // cout << "Cplex found standard solution " <<
    //(status == CPXMIP_OPTIMAL ? "OPTIMAL\n" : " WITHIN TOLERANCE\n");
    return getSolution(solution, true);
  } else {
    if (status == CPXMIP_TIME_LIM_FEAS || CPXMIP_TIME_LIM_INFEAS) return -1;
    char buf[CPXMESSAGEBUFSIZE];
    char* p = CPXXgetstatstring(env, status, buf);
    if (p)
      cout << "c WARNING. Cplex status = " << status << " " << buf << "\n";
    else
      cout << "c WARNING. Cplex status = " << status << "\n";
    return -1;
  }
}

struct ebInfo {
  // callback data for testing if is forced
  Cplex* cplexObject;
  double UB;
  double LB;
};

Weight Cplex::solve_lp_relaxation_(vector<double>& solution,
                                   vector<double>& reduced_costs,
                                   vector<Var>& cplex_vars) {
  /* Unlike other solvers lp_relaxation returns the lp optimal value
     of all cplex variables---not just the bvars */

  int status{0};
  double objval{-1.0};
  int nvars = CPXXgetnumcols(env, linp);
  if (nvars <= 0) return -1.0;

  solution.clear();
  reduced_costs.clear();
  solution.resize(nvars, 0.0);
  reduced_costs.resize(nvars, 0.0);

  if (status = CPXXlpopt(env, linp)) {
    processError(status, false, "CPLEX Failed to optmize lp relaxation");
    return -1.0;
  }

  status = CPXXgetstat(env, linp);
  if (status != CPX_STAT_OPTIMAL) {
    char buf[CPXMESSAGEBUFSIZE];
    char* p = CPXXgetstatstring(env, status, buf);
    if (p)
      cout << "c WARNING. Cplex status = " << status << " " << buf << "\n";
    else
      cout << "c WARNING. Cplex status = " << status << "\n";
  } else {
    if (status = CPXXgetobjval(env, linp, &objval))
      processError(status, false,
                   "Problem getting objective value of lp-relaxation");
    if (status = CPXXgetx(env, linp, solution.data(), 0, nvars - 1))
      processError(status, false,
                   "Problem getting lp-relaxation variable assignments");
    if (status = CPXXgetdj(env, linp, reduced_costs.data(), 0, nvars - 1))
      processError(status, false,
                   "Problem getting lp-relaxation variable assignments");

    cplex_vars.clear();
    for (int i = 0; i < nvars; i++) cplex_vars.push_back(in2ex(i));
  }

  return objval;
}

void Cplex::writeCplexModel() {
  // write out the cplex models for debugging
  auto fn_start = params.instance_file_name.find_last_of('/');
  std::string fname = "mip_" + params.instance_file_name.substr(fn_start + 1) +
                      std::to_string(numSolves) + ".mps";
  if (int status = CPXXwriteprob(env, mip, fname.c_str(), nullptr))
    processError(status, false, "Could not write MIPS model");
}

void Cplex::useBestModelStart(CPXLPptr this_mip) {
  // use the current upper bound model as a mip start in the passed problem

  // clear old starts
  /*if (CPXXgetnummipstarts(env, this_mip) > 0) {
    if (int status = CPXXdelmipstarts(env, this_mip, 0,
                                      CPXXgetnummipstarts(env, this_mip) - 1))
      processError(status, false, "CPLEX Failed to Delete MIP Starts");
    }*/
  vector<int> cplex_vars{};
  vector<double> cplex_vals{};
  CPXNNZ beg{0};
  int effort{1};

  for (size_t sftCls = 0; sftCls < bvars.n_bvars(); sftCls++) {
    auto ci = ex2in(bvars.varOfCls(sftCls));
    if (ci != var_Undef) {
      cplex_vars.push_back(ci);
      double val = (ubModelSofts[sftCls] == l_True) ? 0.0 : 1.0;
      cplex_vals.push_back(val);
    }
  }
  for (size_t v = 0; v < bvars.n_ovars(); v++)
    if (!bvars.isBvar(v)) {
      auto ci = ex2in(v);
      if (ci != var_Undef) {
        cplex_vars.push_back(ci);
        double val = (ubModel[v] == l_True) ? 1.0 : 0.0;
        cplex_vals.push_back(val);
      }
    }

  if (!cplex_vars.empty()) {
    if (int status = CPXXaddmipstarts(env, this_mip, 1, cplex_vars.size(), &beg,
                                      cplex_vars.data(), cplex_vals.data(),
                                      &effort, nullptr))
      processError(status, false,
                   "CPLEX Failed to add best model as MIP start");
  }
}

Weight Cplex::getSolution(vector<Lit>& solution, bool optimal) {
  // Return incumbent in solution and lower bound on objective value as
  // function value If passed bool "optimal" is true then cplex found optimal
  // solution to its current model.

  double objval{};
  int status;
  if (status = CPXXgetobjval(env, mip, &objval))
    processError(status, false,
                 "Problem getting mip objective value of incumbent");

  if (optimal) {
    if (objval > LB) LB = objval;
  } else {
    // set LB to current lower bound. Int weights ==> can round up.
    double bstobjval{};
    if (status = CPXXgetbestobjval(env, mip, &bstobjval))
      processError(status, false, "Problem getting mip best objective value");

    // DEBUG
    // cout << "Cplex getSolution objval = " << objval << " bstobjval = " <<
    // bstobjval
    //	<< " current LB = " << LB << " integer wts = " << intWts <<
    //"\n";

    if (bstobjval > LB) LB = bstobjval;
  }

  // cout << "Updated LB = " << LB << "\n";

  int nvars = CPXXgetnumcols(env, mip);
  vector<double> vals(nvars, 0.0);

  if (nvars > 0) {
    status = CPXXgetx(env, mip, vals.data(), 0, nvars - 1);
    if (status)
      processError(status, false, "Problem getting mip variable assignments");
  }

  /*printf("Returned Optimum:\n[");
    for (int j = 0; j < nvars; j++)
    printf ("%d=%g, ", j+1, vals[j]);
    printf("]\n");*/

  for (size_t sftCls = 0; sftCls < bvars.n_bvars(); sftCls++) {
    auto ci = ex2in(bvars.varOfCls(sftCls));
    if (ci == var_Undef)
      solution.push_back(~bvars.litOfCls(sftCls));
    else {
      auto val = vals[ci];
      if (val > 0.99)
        solution.push_back(bvars.litOfCls(sftCls));
      else if (val < 0.01)
        solution.push_back(~bvars.litOfCls(sftCls));
      else {  // found unset value
        solution.clear();
        return -1;
      }
    }
  }
  return LB;
}

Weight Cplex::greedySolution(vector<Lit>& solution, int denom) {
  /* Round LP solution to greedy solution */
  vector<Weight> lp_sol;
  vector<Weight> red_costs_dummy;
  vector<Var> cplex_vars_dummy;
  Weight greedyCost =
      solve_lp_relaxation(lp_sol, red_costs_dummy, cplex_vars_dummy);
  double bound = 1.0 / (double)denom;
  solution.clear();

  for (size_t sftCls = 0; sftCls < bvars.n_bvars(); sftCls++) {
    auto blit = bvars.litOfCls(sftCls);
    auto val = lp_sol[sftCls];
    // cout << " v: " << val << " " << endl;
    if (val > bound)
      solution.push_back(blit);
    else
      solution.push_back(~blit);
  }
  return greedyCost;
}

int Cplex::populate(double timeLimit, double gap) {
  int status;
  timeLimit = (timeLimit < 0) ? 1e+75 : timeLimit;
  if (status = CPXXsetdblparam(env, CPX_PARAM_TILIM, timeLimit))
    processError(status, false, "Could not set CPLEX time limit for populate");

  if (status = CPXXsetdblparam(env, CPX_PARAM_SOLNPOOLAGAP, gap))
    processError(status, false,
                 "Could not set CPLEX pool absolute gap in populate");

  if (status = CPXXsetinfocallbackfunc(env, NULL, NULL))
    processError(status, false,
                 "Failed to unset logging callback function in populate");

  status = CPXXpopulate(env, mip);
  if (status) processError(status, false, "CPLEX Failed to Populate");
  int nsolns = CPXXgetsolnpoolnumsolns(env, mip);
  if (nsolns == 0)
    cout << "c Tried populate but cplex n Pool found no solutions\n";
  return nsolns;
}

void Cplex::getPopulatedSolution(int i, vector<Lit>& solution) {
  int nvars = CPXXgetnumcols(env, mip);
  int nsolns = CPXXgetsolnpoolnumsolns(env, mip);
  vector<double> vals(nvars, 0.0);
  solution.clear();

  if (nvars > 0 && nsolns > i) {
    auto status = CPXXgetsolnpoolx(env, mip, i, vals.data(), 0, nvars - 1);
    if (status) {
      processError(status, false,
                   "Problem getting solution from solution pool");
      return;
    }

    for (size_t sftCls = 0; sftCls < bvars.n_bvars(); sftCls++) {
      auto ci = ex2in(bvars.varOfCls(sftCls));
      if (ci == var_Undef)
        solution.push_back(~bvars.litOfCls(sftCls));
      else {
        auto val = vals[ci];
        if (val > 0.99)
          solution.push_back(bvars.litOfCls(sftCls));
        else if (val < 0.01)
          solution.push_back(~bvars.litOfCls(sftCls));
        else {  // found unset value
          solution.clear();
          return;
        }
      }
    }
  }
}
