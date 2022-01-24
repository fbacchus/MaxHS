/***********[MaxSolver.cc]
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

#include <zlib.h>
#include <algorithm>
#include <cmath>
#include <iomanip>
#include <iostream>
#include <map>
#include <unordered_set>
#include <utility>

#include "maxhs/core/Assumptions.h"
#include "maxhs/core/MaxSolver.h"
#include "maxhs/core/SumManager.h"
#include "maxhs/core/Wcnf.h"
#include "maxhs/ifaces/Cplex.h"
#include "maxhs/ifaces/GreedySolver.h"
#include "maxhs/ifaces/SatSolver.h"
#include "maxhs/ifaces/cadicalSatSolver.h"
#include "maxhs/ifaces/muser.h"
#include "maxhs/utils/Params.h"
#include "maxhs/utils/io.h"

#ifdef GLUCOSE
#include "glucose/utils/System.h"
#else
#include "minisat/utils/System.h"
#endif

using namespace MaxHS;
using namespace MaxHS_Iface;

using std::cout;
using std::pair;

MaxSolver::MaxSolver(Wcnf* f)
    :  // many of are already default initialized...but for clarity
      theWcnf{f},
      bvars{f},
      satsolver{new MaxHS_Iface::cadicalSolver()},
      muser{new MaxHS_Iface::Muser{satsolver, bvars}},
      //  greedySatSolver {nullptr},
      absGap{params.tolerance},
      UBmodel(bvars.n_vars(), l_Undef),
      UBmodelSofts(theWcnf->nSofts(), l_False),
      tmpModelSofts(theWcnf->nSofts(), l_False),
      nextNewVar{eqCvar + 1},
      bLitOccur(bvars.n_blits(), 0),
      blit_lt{&bLitOccur, bvars, false},
      blit_gt{&bLitOccur, bvars, true} {
  params.instance_file_name = theWcnf->fileName();
  if (theWcnf->integerWts())
    absGap = 0.75;
  else
    wt_fmt.precision(6);
  summations = new SumManager(bvars, this, muser, satsolver);
  cplex = new Cplex{bvars, summations, UBmodelSofts, UBmodel,
                    theWcnf->integerWts()};
  if (!cplex->is_valid())
    cout << "c ERROR. Problem initializing CPLEX solver\n";
  greedysolver = new MaxHS_Iface::GreedySolver{bvars, summations};
  satsolver->set_option("phase", false);
  if (params.sverbosity) {
    satsolver->set_option("verbose", params.sverbosity);
    satsolver->set_option("report", 1);
    satsolver->set_option("quiet", 0);
    if (params.sverbosity > 2) { satsolver->set_option("log", 1); }
  } else {
    satsolver->set_option("report", 0);
    satsolver->set_option("quiet", 1);
  }
}

MaxSolver::~MaxSolver() {
  if (satsolver) delete satsolver;
  if (greedysolver) delete greedysolver;
  // if (greedySatSolver)
  //  delete greedySatSolver;
  if (summations) delete summations;
  if (cplex) delete cplex;
}

Weight MaxSolver::UB() { return theWcnf->totalClsWt() - sat_wt; }

bool MaxSolver::check_termination() {
  if (fabs(UB() - LB()) <= absGap) return true;
  if (LB() > UB() + absGap) return true;
  return false;
}

bool MaxSolver::check_termination(const std::string& location) {
  if (fabs(UB() - LB()) <= absGap) {
    optFound("c Solved by " + location + ".");
    return true;
  }
  if (LB() > UB() + absGap) {
    if ((LB() - UB()) / UB() <= 1e-10) {
      optFound("c Solved to within CPLEX tolerance by " + location + ".");
      return true;
    }
    cout << "c ERROR after " << location << ". Lower bound " << wt_fmt(LB())
         << " exceeding upper bound " << wt_fmt(UB()) << "\n";
    return true;
  }
  return false;
}

void MaxSolver::solve() {
  globalStartTime = cpuTime();
  if (theWcnf->isUnsat()) {
    cout << "c Unsat Found by theWcnf\n";
    unsatFound();
    return;
  }
  //******************************************************************//
  // Set up sat solver                                                 //
  //******************************************************************//

  addHards(satsolver);
  addSofts(satsolver);
  // Non-unit softs sc contain b-variables b. -sc --> b. But sc does not imply
  // -b If params.fbeq then clauses will be added to make this implication.
  if (params.fbeq) addSoftEqs(satsolver, false);  // permanent eq clauses
  // If not, then we can periodically test if the soft is satisfied and force -b
  // by first setting up the appropriate data structures.
  if (params.fb) initSftSatisfied();

  if (params.verbosity > 0) printNclausesInSatSolver("Before solving");
  //******************************************************************//
  // Check if hards are satisfiable. If so get initial upper and      //
  // lower bounds                                                     //
  //******************************************************************//
  auto hards_are_sat = satsolver->solve();
  if (hards_are_sat == l_False) {
    unsatFound();
    return;
  }

  if (params.improve_model) improveModel();
  updateLB(getForcedWt());  // get forced weight.
  updateUB();
  if (check_termination("Init Bounds")) return;
  if (params.fb)  // add forced negated b-vars to sat solver
    satSolverAddBvarsFromSofts();
  satsolver->updateFixed();  // retrieve fixed values from sat solver
  if (params.verbosity > 0) {
    cout << "c Init Bnds: SAT Time " << time_fmt(satsolver->solveTime())
         << "\n";
    cout << "c Init Bnds: LB =" << wt_fmt(LB()) << " UB = " << wt_fmt(UB())
         << "\n";
    cout << "c Init Bnds: Forced " << satsolver->getNFixed() << " literals.\n";
  }

  // Seed CPLEX
  if (params.seed_type) seed_equivalence();

  // Disjoint Phase
  if (allClausesSeeded) {
    // when all clauses feed to cplex we will do a special greedy phase to
    // get a better upper bound model then start up cplex. We do
    // we want the greedy phase to start with only the disjoint cores.
    // and we do not want the found greedy cores to be given to cplex.
    greedyClauses.clear();
    if (params.verbosity > 0) cout << "c All clauses seeded into CPLEX\n";
  }

  // Disjoint Phase
  if (params.dsjnt_phase) disjointPhase();
  if (check_termination("disjoint phase")) return;

  // mutexes processing.
  processMutexes();

  // Solve.
  if (allClausesSeeded)
    allClausesSeeded_maxsat();
  else
    seqOfSAT_maxsat();
}

void MaxSolver::disjointPhase() {
  Assumps assumps(satsolver, bvars, summations);
  int num{0};
  int len{0};
  Weight lb_weight{0.0};
  if (params.verbosity > 0) cout << "c Disjoint Phase\n";
  // don't turn off mus minimizing during disjoint phase.
  auto save_mus_red_rate = params.mus_min_red;
  params.mus_min_red = -1;

  double beginTime = cpuTime();
  /*// at this stage the greedy solver has input and learnt cores of the
  // theory via seeding. We don't want disjoint to rediscover these,
  // initialize the assumed true softs with a greedy_solution.
  // As added effect, if the greedy solver respect the mutex constraints
  // then disjointPhase will always use assumptions repecting the mutexes.

  // Must use greedy solver and must return a solution.
  auto greedy_solution = greedySoln(true, true);
  assumps.init(greedy_solution, CoreType::cores);*/
  assumps.all_softs_true();

  if (params.sort_assumps == 1)
    assumps.sort(blit_gt);
  else if (params.sort_assumps == 2)
    assumps.sort(blit_lt);

  vector<Lit> conflict;
  lbool val;
  while (
      (val = satsolve_min(assumps, conflict,
                          num == 0 ? params.noLimit : params.dsjnt_cpu_per_core,
                          params.dsjnt_mus_cpu_lim)) == l_False) {
    // lbool val {l_False};
    // while(val == l_False) {
    //   cout << "Disjoint Phase satsolve. sat_cpu = " <<
    //   params.dsjnt_cpu_per_core << " mus_cpu = "
    //        << params.dsjnt_mus_cpu_lim << "\n";
    //   val = satsolve_min(assumps, conflict, params.dsjnt_cpu_per_core,
    //   params.dsjnt_mus_cpu_lim);

    if (params.verbosity > 1) {
      cout << "c Disjoint Conflict size = " << conflict.size() << "\n";
      if (params.verbosity > 2) cout << "c conflict = " << conflict << "\n";
    }
    store_cplex_greedy_cls(conflict);
    // Must remove assumptions now that we are adding forced negated bvars
    assumps.update(conflict, true);
    num++;
    len += conflict.size();
    Weight min_wt{std::numeric_limits<Weight>::max()};
    for (auto b : conflict)
      if (bvars.wt(b) < min_wt) min_wt = bvars.wt(b);
    lb_weight += min_wt;
  }

  // restore mus reduction rate requirement
  params.mus_min_red = save_mus_red_rate;

  // update Bounds (only UB could have changed)
  if (val == l_True) {
    if (params.improve_model) improveModel();
    updateUB();
  }
  updateLB(lb_weight);

  if (params.verbosity > 0) {
    cout << "c Dsjnt: #Cores " << num << " with total weight "
         << wt_fmt(lb_weight) << " LB " << wt_fmt(LB()) << " UB "
         << wt_fmt(UB()) << "\n";
    if (num > 0) {
      cout << "c Dsjnt: Avg Core Size "
           << fix4_fmt(num ? len / static_cast<double>(num) : 0) << "\n";
      cout << "c Dsjnt: Time " << time_fmt(cpuTime() - beginTime) << "\n";
    }
  }
}

vector<Lit> MaxSolver::extract_costBoundinglits(const vector<Lit>& soln) const {
  // assuming unvalued non-cores bvars and summation outputs bounds
  // cost of sat modele
  vector<Lit> cblits;
  for (auto l : soln)
    if (satsolver->fixedValue(l) == l_Undef &&
        (bvars.isNonCore(l) || summations->isSoutput(l)))
      cblits.push_back(l);
  return cblits;
}

vector<Lit> MaxSolver::extract_NonCoreBvars(const vector<Lit>& soln) const {
  vector<Lit> ncBlits;
  for (auto l : soln)
    if (satsolver->fixedValue(l) == l_Undef && bvars.isNonCore(l))
      ncBlits.push_back(l);
  return ncBlits;
}

vector<Lit> MaxSolver::extract_UnValued(const vector<Lit>& soln) const {
  vector<Lit> ncBvars;
  for (auto l : soln)
    if (satsolver->fixedValue(l) == l_Undef) ncBvars.push_back(l);
  return ncBvars;
}

bool MaxSolver::any_false(const vector<Lit>& soln) const {
  for (auto l : soln)
    if (satsolver->fixedValue(l) == l_False) return true;
  return false;
}

bool MaxSolver::all_bvars(const vector<Lit>& soln) const {
  for (auto l : soln)
    if (!bvars.isBvar(l)) return false;
  return true;
}

void MaxSolver::allClausesSeeded_maxsat() {
  auto n_cplex = cplexAddNewForcedBvars();
  n_cplex += cplexAddNewClauses();
  log_if(n_cplex > 0, 1, "c Initial solve: add to CPLEX ", n_cplex,
         " constraints");

  vector<Lit> cplexsoln;
  Weight cplexLB =
      cplex->solveBudget(cplexsoln, 0, params.all_seeded_first_cplex_cpu);
  if (cplexLB < 0) {
    summations->compute_abstraction(params.all_seeded_first_abs_cpu);
    if (haveUBModel && check_termination("building summations")) return;
    params.abstract_greedy_cores = 0;
    if (get_greedy_conflicts(
            params.seed_all_cpu,
            params.max_cores_before_cplex + cplexClauses.size()))
      return;

    params.conflicts_from_ub = 2;
    get_ub_conflicts(params.max_cpu_before_cplex);
    if (check_termination("conflicts from UB model")) return;

    // compute abstraction requesting all vars be grouped into one
    // cluster
    summations->compute_abstraction(params.all_seeded_2nd_abs_cpu, true);
    if (haveUBModel && check_termination("building summations")) return;

    // Add new units but not new touts to cplex
    n_cplex = cplexAddNewForcedBvars();
    n_cplex += cplexAddNewClauses();

    if (params.verbosity > 0 && n_cplex > 0)
      cout << "c Updated CPLEX model: add to CPLEX " << n_cplex
           << "  constraints\n";
    cplexsoln.clear();
    cplexLB = cplex->solve(cplexsoln, 0);
    if (cplexLB < 0) { printErrorAndExit("c ERROR: Cplex::solve() failed"); }
  }

  if (any_false(cplexsoln))
    printErrorAndExit("c ERROR cplex had full model returned false literal");

  auto cplexSolnWt = getWtOfBvars(cplexsoln);  // solution cost is UB
  reportCplex(cplexLB, cplexSolnWt);
  bool cplex_found_optimum = (fabs(cplexSolnWt - cplexLB) <= absGap);
  if (params.verbosity > 0) {
    cout << "c CPLEX solution cost = " << wt_fmt(cplexSolnWt)
         << " lower bound = " << wt_fmt(cplexLB) << "\n";
    if (cplex_found_optimum)
      cout << "c CPLEX found optimal solution to its current model\n";
  }
  if (cplexLB > LB()) updateLB(cplexLB);
  if (params.verbosity > 0) {
    cout << "c after CPLEX bnds: LB = " << wt_fmt(LB())
         << " UB = " << wt_fmt(UB()) << " gap = " << wt_fmt(UB() - LB())
         << "\n";
  }

  if (haveUBModel && check_termination("LB >= UB")) return;

  // now check the cplex soln (should be valid since cplex has full
  // model).

  Assumps assumps(satsolver, bvars, summations);
  assumps.init(extract_NonCoreBvars(cplexsoln));

  vector<Lit> conflict;
  auto val = satsolver->solve(assumps.vec(), conflict);
  if (val == l_False) {
    cout << "c ERROR cplex had full model but returned unsat "
            "solution\n";
  } else if (val == l_Undef) {
    cout << "c ERROR cplex had full model but sat solver could not "
            " verify its solution\n";
  } else {
    updateUB();
    if (!check_termination("CPLEX model"))
      cout << "c ERROR cplex had full model but returned non-optimal"
              " solution\n";
  }
  return;
}

bool MaxSolver::iteration_is_bad(Weight desired_delta, Weight delta,
                                 Weight gap) const {
  return delta <= desired_delta && delta <= gap * 0.25;
}

bool MaxSolver::do_abstraction() const {
  // based on progress so far decide whether or not to do abstraction
  // A finite state controller for this should be considered.
  int iter = track_abs_triggers.deltas.size();
  bool this_iteration_bad = iteration_is_bad(
      iter == 1 ? params.initial_abstract_gap : params.abstract_gap,
      track_abs_triggers.deltas.back(), track_abs_triggers.gaps.back());
  log(1, "c LP Bound delta = ", track_abs_triggers.deltas.back(),
      " ub-lb gap = ", track_abs_triggers.gaps.back(), " this iteration is",
      this_iteration_bad ? " bad." : " good.");

  if (iter == 1)
    // first iteration measures effectiveness of disjoint phase and seeding.
    // so if that is bad do abstraction.
    // if second iteration is bad this indicates that post disjoint
    // cores were not effective so do abstraction.
    return this_iteration_bad;
  // if this iteration is not bad don't do abstraction
  if (!this_iteration_bad) return false;

  // this iteration is bad. If prior iteration wasn't bad we wait for
  // two bad iterations.  But don't consider prior iteration good if
  // it was generated by an abstraction.

  // an iteration is the result of abstraction if abstraction occured during the
  // previous iteration
  bool prev_iteration_from_abstraction =
      (track_abs_triggers.did_abstraction.size() > 2) &&
      *(track_abs_triggers.did_abstraction.end() - 3);
  bool prev_iteration_good = !prev_iteration_from_abstraction &&
      !iteration_is_bad(params.abstract_gap,
                        *(track_abs_triggers.deltas.end() - 2),
                        *(track_abs_triggers.gaps.end() - 2));
  log(1, "c previous iteration was ", prev_iteration_good ? "good." : "bad.");
  return !prev_iteration_good;
}

void MaxSolver::seqOfSAT_maxsat() {
  vector<Lit> cplexsoln;
  vector<Lit> conflict;
  // for lp relaxation
  vector<double> lp_solvals;
  vector<double> lp_redvals;
  vector<Var> cplex_vars;
  Weight lp_objval{};
  Weight lp_delta{};
  Weight prev_lp_bnd{};
  // for loop control
  int iteration{-1};
  int n_abs{};
  Weight prev_cplex_solution_obj{};
  bool cplex_found_optimum{false};

  while (1) {
    log(1, "c **********Iter: ", ++iteration,
        " Elapsed Time = ", time_fmt(cpuTime() - globalStartTime));
    // update CPLEX and LP model
    int new_cplex_constraints{0};
    bool have_lp_soln{false};

    new_cplex_constraints += cplexAddNewForcedBvars();
    new_cplex_constraints += cplexAddNewClauses();

    // Try LP reduced cost fixing before calling cplex.
    if (params.lp_harden) {
      prev_lp_bnd = (lp_objval >= 0) ? lp_objval : 0;
      lp_objval =
          cplex->solve_lp_relaxation(lp_solvals, lp_redvals, cplex_vars);
      have_lp_soln = lp_objval >= 0;
      lp_delta = (lp_objval >= 0) ? lp_objval - prev_lp_bnd : 0;
      if (lp_objval > 0)
        if (tryHarden_with_lp_soln(lp_objval, lp_redvals, cplex_vars)) {
          new_cplex_constraints += cplexAddNewForcedBvars();
          if (check_termination("LP-Bound == UB")) return;
        }
    }

    // Solve CPLEX model and update Bounds.
    // CPLEX solve is dependent on what upper bound is passed.
    //       CPLEX will terminate on finding any feasible solution
    //       with cost < the upper bound. So passing zero forces
    //       CPLEX to find an optimal solution.
    //
    // If the previous solve found an optimal solution to its current
    // model or there was no prior solve, or the cplex model
    // has been improved (which must increase its cost) then stop
    // cplex when it finds a better model than the current UB
    // model. Since we are aborting on non-optimal solutions we
    // could have a sequence of non-optimal CPLEX solutions that
    // satisfy the SAT model.  In this case we want to ensure that
    // when CPLEX is called again it returns a better model than the
    // last time...to prevent cycling
    Weight cplex_UB;
    if (cplex_found_optimum || prev_cplex_solution_obj == 0 ||
        new_cplex_constraints)
      cplex_UB = UB();
    else
      cplex_UB = fmin(prev_cplex_solution_obj, UB());

    Weight cplexLB = cplex->solve(cplexsoln, cplex_UB);
    if (cplexLB < 0) { printErrorAndExit("c ERROR: Cplex::solve() failed"); }
    updateLB(cplexLB);

    // solution cost is UB
    auto cplexSolnWt = getWtOfBvars(cplexsoln);
    prev_cplex_solution_obj = cplexSolnWt;
    reportCplex(cplexLB, cplexSolnWt);
    cplex_found_optimum = (fabs(cplexSolnWt - cplexLB) <= absGap);
    if (cplex_found_optimum)
      log(1, "c CPLEX found optimal solution to its current model");

    log(1, "c after CPLEX bnds: LB = ", wt_fmt(LB()), " UB = ", wt_fmt(UB()),
        " GAP =", wt_fmt(UB() - LB()));

    if (check_termination("LB >= UB")) return;

    // Check to see if we need to abstract the b-vars

    if (params.abstract) {
      if (!have_lp_soln) {
        prev_lp_bnd = (lp_objval >= 0) ? lp_objval : 0;
        lp_objval =
            cplex->solve_lp_relaxation(lp_solvals, lp_redvals, cplex_vars);
        have_lp_soln = lp_objval >= 0;
        lp_delta = (lp_objval >= 0) ? lp_objval - prev_lp_bnd : 0;
      }
      if (lp_objval > 0) {
        track_abs_triggers.n_constraints.push_back(new_cplex_constraints);
        track_abs_triggers.deltas.push_back(lp_delta);
        track_abs_triggers.gaps.push_back(UB() - LB());
        track_abs_triggers.did_abstraction.push_back(false);
        if (do_abstraction()) {
          track_abs_triggers.did_abstraction.back() = true;
          double tb{params.abs_cpu};
          if (n_abs > 1) tb *= 2;
          if (n_abs > 2) tb *= 3;
          summations->compute_abstraction(tb);
          if (haveUBModel && check_termination("building summations")) return;
          ++n_abs;
        } else if (iteration_is_bad(params.abstract_gap, lp_delta,
                                    UB() - LB()) &&
                   !summations->all_summations_exhausted()) {
          summations->exhaust_top_level();
        }
      }
    }

    // Got CPLEX solution and perhaps abstraction. No collect cores
    // from CPLEX soln subject to resource limits
    auto cplex_iter_max_time = cpuTime() + params.max_cpu_before_cplex;
    int max_cores_remaining = params.max_cores_before_cplex;

    // generate conflicts from cplex solution
    log(1, "c finding conflicts from cplex solution");
    if (get_cplex_conflicts(cplexsoln, 'c', cplex_iter_max_time,
                            max_cores_remaining))
      return;

    // generate conflicts from greedy solutions.
    max_cores_remaining = params.max_cores_before_cplex - cplexClauses.size();
    if (max_cores_remaining > 0 && cpuTime() < cplex_iter_max_time)
      if (get_greedy_conflicts(cplex_iter_max_time, max_cores_remaining))
        return;

    // generate conflicts from other cplex solutions
    // from cplex
    max_cores_remaining = params.max_cores_before_cplex - cplexClauses.size();
    if (max_cores_remaining > 0 && cpuTime() < cplex_iter_max_time) {
      auto gap = fabs(UB() - cplexSolnWt) - absGap;
      if (get_populate_conflicts(cplex_iter_max_time, max_cores_remaining,
                                 gap <= absGap ? 0.0 : gap))
        return;
    }

    // if necessary and possible   .. get conflicts from new UB
    max_cores_remaining = params.max_cores_before_cplex - cplexClauses.size();
    if (max_cores_remaining > 0 && cpuTime() < cplex_iter_max_time)
      if (get_ub_conflicts(cplex_iter_max_time)) return;
  }
}

bool MaxSolver::get_cplex_conflicts(const vector<Lit>& cplexSoln, char type,
                                    double timeout, int max_cores) {
  // Input cplex solution and number of conflicts accumulated since CPLEX
  // called. Return true if we found an optimal solution. I.e., one with cost
  // equal to LB() that is SAT.  If not optimal solution but is SAT update
  // upper bound If UNSAT generate some conflicts to criticize this cplex
  // solution. But check first to ensure that we don't have a conflict already
  // criticizing this solution.
  if (params.verbosity > 1)
    cout << "c get_cplex_conflict processing "
         << (type == 'p' ? "populated " : "cplex") << "solution of cost "
         << wt_fmt(getWtOfBvars(cplexSoln)) << "\n";

  // compute conflict from abstract soln if requested
  bool found_abstract_solution{false};
  int n_conf{0};
  if (params.abstract_cplex_cores) {
    auto abscplexsoln = abstractSolution(cplexSoln);
    if (!abscplexsoln.empty()) {
      n_conf = get_seq_of_conflicts(
          abscplexsoln,
          cplexClauses.empty() ? params.noLimit : params.optcores_cpu_per,
          params.optcores_cpu_per, timeout, max_cores);
      found_abstract_solution = n_conf > 0;
      if (check_termination(type == 'p' ? "abstract populated CPLEX model"
                                        : "abstract CPLEX model"))
        return true;
      if ((type != 'p' || params.verbosity > 1) && params.verbosity > 0 &&
          n_conf > 0)
        cout << "c Cplex abstract solution yielded " << n_conf
             << " new conflicts\n";
    }
  }

  max_cores -= n_conf;
  if (!cplexClauses.empty() && (max_cores <= 0 || cpuTime() > timeout))
    return false;

  if (!found_abstract_solution || params.abstract_cplex_cores > 1) {
    n_conf = get_seq_of_conflicts(cplexSoln,
                                  (cplexClauses.empty() && cplexClauses.empty()
                                       ? params.noLimit
                                       : params.optcores_cpu_per),
                                  params.optcores_cpu_per, timeout, max_cores);
    if (check_termination(type == 'p' ? "populated CPLEX model"
                                      : "CPLEX model"))
      return true;
    if ((type != 'p' || params.verbosity > 1) && params.verbosity > 0 &&
        n_conf > 0)
      cout << "c Cplex concrete solution yielded " << n_conf
           << " new conflicts\n";
  }
  return false;
}

bool MaxSolver::get_greedy_conflicts(double timeout, int max_cores) {
  // accumulate more conflicts for CPLEX by criticizing sequence of greedy
  // solutions.
  int iter{0};
  int total_c_conflicts{0};
  int total_a_conflicts{0};
  if (params.verbosity > 0) cout << "c finding conflicts from greedy\n";

  while (1) {
    // Don't need to use greedy and don't need a solution
    // if no new solution is available
    if (max_cores <= 0 || cpuTime() > timeout) break;
    int n_conf = 0;
    bool iteration_succ = false;

    auto greedy_solution = greedySoln(false, false);
    ++iter;
    if (!greedy_solution.size()) break;
    if (params.verbosity > 1) cout << "c Greedy Solution # " << iter << "\n";

    if (params.abstract_greedy_cores != 1) {
      n_conf =
          get_seq_of_conflicts(greedy_solution, params.optcores_cpu_per,
                               params.optcores_cpu_per, timeout, max_cores);
      max_cores -= n_conf;
      total_c_conflicts += n_conf;
      iteration_succ |= n_conf > 0;
      if (check_termination("concrete greedy soln")) return true;
      if (params.verbosity > 1)
        cout << "c Greedy concrete solution yielded " << n_conf
             << " new conflicts\n";
    }

    if (max_cores <= 0 || cpuTime() >= timeout) break;

    if (params.abstract_greedy_cores) {
      auto absgreedysoln = abstractSolution(greedy_solution);
      if (!absgreedysoln.empty()) {
        n_conf =
            get_seq_of_conflicts(absgreedysoln, params.optcores_cpu_per,
                                 params.optcores_cpu_per, timeout, max_cores);
        max_cores -= n_conf;
        total_a_conflicts += n_conf;
        iteration_succ |= n_conf > 0;
        if (check_termination("abstract greedy soln")) return true;
        if (params.verbosity > 1)
          cout << "c Greedy abstract solution yielded " << n_conf
               << " new conflicts\n";
      }
    }
    if (!iteration_succ) break;
  }
  if (params.verbosity > 0)
    cout << "c Greedy: iters=" << iter
         << " concrete conflicts=" << total_c_conflicts
         << " abstract conflicts=" << total_a_conflicts << "\n";

  return false;
}

bool MaxSolver::assumps_are_blocked(const vector<Lit>& assumps) {
  // check if soln falsifies an already found clause. If it does then
  // the solution is already blocked so there is no need to generate
  // new conflicts from it.
  /*  vector<Lit> true_lits;
    vector<Lit> tinputs;
    vector<bool> mxes_seen(theWcnf->n_mxes(), false);
    for (auto l : soln) {
      if (bvars.isCore(l))
        if (summations->isSinput(l))
          tinputs.push_back(l);
        else if (bvars.inCoreMx(l) && !mxes_seen[bvars.getMxNum(l)]) {
          mxes_seen[bvars.getMxNum(l)] = true;
          if (summations->isSinput(bvars.getMxDLit(l)))
            tinputs.push_back(bvars.getMxDLit(l));
        } else
          true_lits.push_back(l);
    }
    summations->add_true_touts(tinputs, true_lits);*/

  vector<Lit> a(assumps);
  std::sort(a.begin(), a.end());
  auto is_falsified_by_assumps = [&](Lit l) {
    return std::binary_search(a.begin(), a.end(), ~l);
  };
  for (auto cls : cplexClauses)
    if (std::all_of(cls.begin(), cls.end(), is_falsified_by_assumps)) {
      if (params.verbosity > 1)
        cout << "c assumptions are blocked by previous clause\n";
      return true;
    }

  return false;
}

vector<Lit> MaxSolver::abstractSolution(const vector<Lit>& concrete_soln) {
  // replace concreteSoln with abstract one, return empty vector if
  // abstraction not possible.
  // Code no longer works with non-encoded mutexes. Currently Wcnf
  // encodes all mutexes it finds so unless non-encoded mutexes are
  // restored this should not be a problem.

  // CURRENT VERSION DOES APPLY ABSTRACTION TO CORE MXES
  // VERSION IN COMMENTS DOES BUT IT DOES NOT PERFORM AS WELL

  if (!summations->summations_active())
    // no abstraction possible
    return vector<Lit>{};

  vector<int> sum_n_true_inputs(summations->nb_summations(), 0);
  vector<char> sum_present(summations->nb_summations(), false);
  bool can_abstract{false};

  vector<Lit> abs_soln(concrete_soln);
  for (auto l : abs_soln)
    if (summations->isSinput(l)) {
      can_abstract = true;
      sum_present[summations->get_Sinput_idx(l)] = true;
      if (bvars.isCore(l))
        sum_n_true_inputs[summations->get_Sinput_idx(l)] += 1;
    }

  if (!can_abstract) return vector<Lit>{};

  auto e = std::remove_if(abs_soln.begin(), abs_soln.end(),
                          [&](Lit l) { return summations->isSinput(l); });
  abs_soln.erase(e, abs_soln.end());

  for (size_t tidx = 0; tidx < sum_present.size(); tidx++)
    if (sum_present[tidx]) {
      int n_true =
          std::max(sum_n_true_inputs[tidx], summations->get_n_true_outs(tidx));
      Lit nxt_out = summations->get_next_Soutput(tidx, n_true);
      if (n_true > 0) {
        while (nxt_out != lit_Undef &&
               satsolver->fixedValue(nxt_out) != l_Undef)
          nxt_out = summations->get_next_Soutput(tidx, ++n_true);
        if (nxt_out != lit_Undef) abs_soln.push_back(~nxt_out);
      } else {
        for (auto l : summations->get_ilits_from_sidx(tidx))
          abs_soln.push_back(~l);
      }
    }
  return abs_soln;
}

bool MaxSolver::tryHarden() {
  // Try to harden some of the soft clauses
  vector<double> lp_solvals;
  vector<double> lp_redvals;
  vector<Var> cplex_vars;
  auto lp_objval =
      cplex->solve_lp_relaxation(lp_solvals, lp_redvals, cplex_vars);
  if (lp_objval <= 0) return false;
  return tryHarden_with_lp_soln(lp_objval, lp_redvals, cplex_vars);
}

bool MaxSolver::tryHarden_with_lp_soln(const Weight lp_objval,
                                       vector<double>& lp_redvals,
                                       vector<Var>& cplex_vars) {
  // Try to harden some of the soft clauses with information
  // obtained from an lp solve.

  int hardened_softs_count{n_softs_forced_hard};
  int falsified_softs_count{n_softs_forced_false};
  int hardened_not_in_cplex_count{n_softs_forced_hard_not_in_cplex};
  int ovars_made_true_count{n_ovars_forced_true};
  int ovars_made_false_count{n_ovars_forced_false};
  int touts_made_true_count{n_touts_forced_true};
  int touts_made_false_count{n_touts_forced_false};

  bool some_forced{false};

  updateLB(lp_objval);

  if (fabs(UB() - LB()) <= absGap || LB() > UB() + absGap) return some_forced;
  if (lp_objval + bvars.maxWt() + 0.01 < UB()) return some_forced;

  for (auto blit : bvars.getCoreLits()) {
    if (sign(blit)) cout << "c ERROR blits not all positive!\n";
    if (satsolver->fixedValue(blit) != l_Undef || cplex->lit_in_cplex(blit))
      continue;
    if (lp_objval + bvars.wt(blit) > UB() + 0.01 ||
        (fabs(lp_objval + bvars.wt(blit) - UB()) < 0.001 &&
         UBmodel[var(blit)] == l_False)) {
      satsolver->addClause(~blit);
      ++n_softs_forced_hard_not_in_cplex;
    }
  }

  for (size_t i = 0; i < cplex_vars.size(); i++) {
    Var v = cplex_vars[i];
    if (satsolver->fixedValue(v) != l_Undef) { continue; }
    if (lp_redvals[i] > 0) {
      // var true incurs cost
      if (lp_redvals[i] + lp_objval > UB() + 0.01 ||
          (fabs(lp_redvals[i] + lp_objval - UB()) < 0.001 &&
           UBmodel[v] == l_False)) {
        // Lp is subject to rounding error. Greater than UB if gt by at least
        // 0.01 equal to UB if within 0.001
        //
        // if we make blit true we must incur cost >= UB. If cost >
        // UB force it false. If cost == UB and blit is false in UB
        // model (the corresponding soft is true in the UB model)
        // we can also force it false---no need to consider models
        // with it true as they can't be better than the UB model.
        satsolver->addClause(~mkLit(v));
        if (bvars.isBvar(v))
          ++n_softs_forced_hard;
        else if (summations->isSoutput(v))
          ++n_touts_forced_false;
        else
          ++n_ovars_forced_false;
        some_forced = true;
      }
    } else if (lp_redvals[i] < 0) {
      // var should be at its upper bound
      if (lp_objval - lp_redvals[i] > UB() + 0.01 ||
          (fabs(lp_objval - lp_redvals[i] - UB()) < 0.001 &&
           UBmodel[v] == l_True)) {
        satsolver->addClause(mkLit(v));
        if (bvars.isBvar(v))
          ++n_softs_forced_false;
        else if (summations->isSoutput(v))
          ++n_touts_forced_true;
        else
          ++n_ovars_forced_true;
        some_forced = true;
      }
    }
  }

  if (some_forced)
    // forcing via bounds goes beyond the implications of the hard
    // clauses.  So if this happens, previously exhausted summations
    // might no longer be exhausted.
    summations->unset_all_exhaust_flags();

  if (some_forced && params.verbosity) {
    log(1, "c tryharden: softs hardened              ",
        n_softs_forced_hard - hardened_softs_count);
    log(1, "c tryharden: softs falsified             ",
        n_softs_forced_false - falsified_softs_count);
    log(1, "c tryharden: softs not in cplex hardened ",
        n_softs_forced_hard_not_in_cplex - hardened_not_in_cplex_count);
    log(1, "c tryharden: ordinary vars made true     ",
        n_ovars_forced_true - ovars_made_true_count);
    log(1, "c tryharden: ordinary vars made false    ",
        n_ovars_forced_false - ovars_made_false_count);
    log(1, "c tryharden: touts  made true            ",
        n_touts_forced_true - touts_made_true_count);
    log(1, "c tryharden: touts made false            ",
        n_touts_forced_false - touts_made_false_count);
  }
  /*cout << "blit " << blit;
    if(lp_solvals[i] > 0)
    cout << " weight = " << bvars.wt(blit);
    cout << " LP solval = " << lp_solvals[i]
    << " LP redval = " << lp_redvals[i];
    if(lp_redvals[i] + lp_objval > UB())
    cout << "CAN BE FORCED";
    cout << "\n";*/
  return some_forced;
}

bool MaxSolver::get_ub_conflicts(double timeout) {
  // try reducing UB model---should be a new UB model on which
  // conflicts have not yet been generated before.
  if (!have_new_UB_model || !params.conflicts_from_ub) return false;
  if (params.conflicts_from_ub < 2 &&
      fabs(UB() - LB()) > 3 * theWcnf->minSftWt() && cplexClauses.size() >= 35)
    return false;
  log(1, "c Finding conflicts from UB");
  vector<Lit> ub_false, ub_true;  // store true and false b-lits (true and false
                                  // softs in UB-model)
  Assumps assumps(satsolver, bvars, summations);
  auto n_conf = cplexClauses.size();
  vector<Lit> conflict;

  // init true and false softs in ubmodel
  for (size_t i = 0; i < theWcnf->nSofts(); i++) {
    Lit blit = bvars.litOfCls(i);  // blit = false <==> soft is true
    if (satsolver->fixedValue(blit) == l_Undef) {
      if (UBmodelSofts[i] == l_True)
        ub_true.push_back(~blit);
      else
        ub_false.push_back(blit);
    }
  }

  // try to make false soft clauses true in order of their weight (process
  // from the back)
  auto wtLt = [this](const Lit bx, const Lit by) {
    return bvars.wt(bx) < bvars.wt(by);
  };
  std::sort(ub_false.begin(), ub_false.end(), wtLt);

  log(1, "c UB has ", ub_true.size(), " unforced true softs (false blits) and ",
      ub_false.size(), " unforced false softs (true blits)");

  while (!ub_false.empty()) {
    // try to make one more soft clause true in UB-model.
    auto blit = ub_false.back();
    ub_false.pop_back();
    // try to make false soft blit true
    ub_true.push_back(~blit);
    if (satsolver->fixedValue(blit) != l_Undef) continue;
    if (UBmodel[bvars.clsIndex(blit)] == l_True) continue;

    assumps.init(extract_UnValued(ub_true));
    auto val = satsolve_min(assumps, conflict, params.optcores_cpu_per,
                            params.mus_cpu_lim);
    if (val == l_True) {
      log(1, "c get_ub_conflicts found SAT better UB");
      if (params.improve_model) improveModel();
      updateUB();
      if (check_termination("conflicts from UB model")) return true;
      log(1, "c UB has ", ub_true.size(), " true softs (false blits) and ",
          ub_false.size(), " unforced false softs (true blits)");
    } else {
      if (val == l_False) store_cplex_greedy_cls(conflict);
      ub_true.pop_back();
    }
    if (timeout >= 0 && cpuTime() >= timeout) break;
  }
  have_new_UB_model = false;
  log(1, "c get_ub_conflicts found ", cplexClauses.size() - n_conf,
      " new conflicts");
  return false;
}

int MaxSolver::get_seq_of_conflicts(const vector<Lit>& solution,
                                    double first_core_cpu_lim,
                                    double other_cores_cpu_lim, double timeout,
                                    int max_cores) {
  // Just found a candidate solution (via cplex or greedy or...)
  // check if the solution satisfies whole theory, and if not generate
  // sequence of conflicts from it. Return number of conflicts found.
  // Solution might contain summation output variables
  Assumps assumps(satsolver, bvars, summations);

  assumps.init(extract_costBoundinglits(solution));
  if (assumps_are_blocked(assumps.vec())) return 0;
  assumps.permute();

  // cout << "get_seq_of_conflicts init soln " << solution << "\n";
  // cout << "get_seq_of_conflicts init assumptions " << assumps.vec() <<
  // "\n";
  vector<Lit> conflict;
  int n_conf{0};
  // cout << "satsolve_min\n";
  while (1) {
    // cout << "get_seq_of_conflicts satsolve. sat_cpu = "
    //      << (n_conf ? other_cores_cpu_lim: first_core_cpu_lim)
    //      << " n_conf = " << n_conf
    //      << " other_cores_cpu_lim = " << other_cores_cpu_lim
    //      << " first_core_cpu_lim = " << first_core_cpu_lim
    //      << " mus_cpu = "
    //      << params.mus_cpu_lim << "\n";

    // cout << "Assumptions " << assumps.vec() << "\n";
    auto val = satsolve_min(
        assumps, conflict, (!n_conf ? first_core_cpu_lim : other_cores_cpu_lim),
        params.mus_cpu_lim);
    // cout << "val: " << val << "\n";
    if (val == l_True) {
      if (params.improve_model) improveModel();
      auto w = updateUB();
      if (params.verbosity > 1)
        cout << "c New SAT solution found (get_seq_of_conflicts), cost = " << w
             << "\n";
      // cout << "c UnSat weights = " << unw << "\n";
      // auto wt = checkSolWt(solution);
      return n_conf;
    } else if (val == l_False) {
      ++n_conf;
      --max_cores;
      // cout << "got conflict: " << conflict << "\n";
      store_cplex_greedy_cls(conflict);
      assumps.update(conflict, true);
    } else
      // timed out
      return n_conf;

    if (max_cores <= 0 || cpuTime() > timeout) return n_conf;
  }
}

bool MaxSolver::get_populate_conflicts(double timeout, int max_cores,
                                       double gap) {
  if (!params.trypop) return false;
  if (params.trypop < 2 && cplexClauses.size() >= 35) return false;
  log(1, "c finding conflicts from cplex populated solutions");
  int n_conf = cplexClauses.size();
  int nsolns = cplex->populate(params.cplex_pop_cpu_lim, gap);
  log(2, "c populate found ", nsolns, " solutions");
  auto cores_remaining = max_cores;
  vector<Lit> cplexsoln;
  for (int i = 0; i < nsolns; i++) {
    cplex->getPopulatedSolution(i, cplexsoln);
    if (cplexsoln.size() == 0) {
      log(0, "c WARNING Cplex populate could not find solution");
      continue;
    }
    log(2, "c getting conflicts from solution #", i);
    if (get_cplex_conflicts(cplexsoln, 'p', timeout, cores_remaining))
      return true;
    cores_remaining = max_cores - (cplexClauses.size() - n_conf);
    if (cores_remaining <= 0 || cpuTime() > timeout) return false;
  }
  log(1, "c populate found ", cplexClauses.size() - n_conf, " conflicts");
  return false;
}

vector<Lit> MaxSolver::getAssumpUpdates(int nSinceCplex, vector<Lit>& core) {
  // return a subset of the core to update assumptions. Core should be
  // a conflict returned by trying to see if assumptions are
  // satisfiable...so it will contain only negations of the assumption
  // literals. Uses core for computation---modifies it!
  assert(!(params.coreType == CoreType::cores) || vec_isCore(core));

  switch (params.coreRelaxFn) {
    case CoreRelaxFn::maxoccur:
      return vector<Lit>{maxOccurring(core)};
    case CoreRelaxFn::frac:
      return fracOfCore(nSinceCplex, core);
    case CoreRelaxFn::dsjn:
      return core;
    default:
      return vector<Lit>{core[0]};
  }
}

vector<Lit> MaxSolver::fracOfCore(int nSinceCplex, vector<Lit>& core) {
  double fracToReturn = params.frac_to_relax;
  int nToReturn{1};
  if (nSinceCplex > params.frac_rampup_start) {
    if (nSinceCplex < params.frac_rampup_end)
      fracToReturn *= (nSinceCplex - params.frac_rampup_start) /
          (1.0 * (params.frac_rampup_end - params.frac_rampup_start));
    nToReturn = ceil(fracToReturn * ((double)core.size()));
  }
  if (nToReturn == 1) return vector<Lit>{maxOccurring(core)};

  // auto maxOccur = [this](Lit l1, Lit l2) { return
  // bLitOccur[bvars.toIndex(l1)] < bLitOccur[bvars.toIndex(l2)]; }; use a
  // heap here instead of fully sorting the vector.
  // std::make_heap(core.begin(), core.end(), maxOccur);
  std::make_heap(core.begin(), core.end(), blit_lt);

  vector<Lit> retVec;
  for (int i = 0; i < nToReturn; i++) {
    retVec.push_back(core.front());
    // std::pop_heap(core.begin(), core.end()-i, maxOccur);
    std::pop_heap(core.begin(), core.end() - i, blit_lt);
  }
  if (params.verbosity > 1)
    cout << "c fracOfCore returns a relaxation of size " << retVec.size()
         << "\n";
  return retVec;
}

Lit MaxSolver::maxOccurring(const vector<Lit>& core) {
  // return literal of core that appears in largest number of accumulated
  // CPLEX clauses
  Lit max = core[0];
  for (auto l : core)
    // if(bLitOccur[bvars.toIndex(l)] > bLitOccur[bvars.toIndex(max)])
    //
    if (blit_gt(l,
                max))  // Note blit_lt(max, l) is not same as blit_gt(l, max)
      max = l;
  return max;
}

void MaxSolver::incrBLitOccurrences(const vector<Lit>& core) {
  // all lits in core should be bvars!
  if (core.size() > static_cast<size_t>(top_freq)) { top_freq = core.size(); }
  for (auto l : core) { bLitOccur[bvars.toIndex(l)] += 1; }
}

// TODO: Consider unifying the add clause/add new forced bvar
//      across all solvers (including CPLEX).
//      Perhaps a solver class that CPLEX and SAT derive from.
//
void MaxSolver::cplexAddCls(vector<Lit>&& cls) {
  cplex->add_clausal_constraint(cls);
  if (params.verbosity > 2) {
    cout << "c Added clause to Cplex:\n";
    outputConflict(cls);
  }
}

// TODO Better abstraction to facilitate sharing of unit or other clauses
// between solvers.
//
int MaxSolver::cplexAddNewForcedBvars() {
  vector<Lit> forced{cplexNU.new_units(satsolver)};
  int nf{0};
  int tv{0};

  auto high_touts_first = [&](const Lit l1, const Lit l2) {
    if (summations->isSoutput(l1) && summations->isSoutput(l2)) {
      if (summations->isNegativeSoutput(l1) &&
          summations->isNegativeSoutput(l2))
        return summations->get_olit_index(l1) < summations->get_olit_index(l2);
      else if (summations->isNegativeSoutput(l1))
        return true;
      else if (summations->isNegativeSoutput(l2))
        return false;
      else
        return summations->get_olit_index(l1) > summations->get_olit_index(l2);
    } else if (summations->isSoutput(l1))
      return true;
    else if (summations->isSoutput(l2))
      return false;
    else
      return l1 < l2;
  };
  std::sort(forced.begin(), forced.end(), high_touts_first);

  /*cout << "FORCED:\n";
  for (auto l : forced) {
    if (summations->isSoutput(l))
      cout << '(' << l << ',' << summations->get_olit_idx(l) << ':'
           << summations->get_olit_index(l) << ")\n";
           }*/

  for (auto l : forced) {
    if (summations->isSoutput(l)) { tv++; }
    if (bvars.isBvar(l) || summations->isSoutput(l) || cplex->lit_in_cplex(l)) {
      nf++;
      cplexAddCls({l});
      // cout << "cplex add clause\n";
    }
  }
  log_if(nf, 1, "c CPLEX: += ", nf, " forced bvars; (", tv,
         " forced summation outputs)");
  return nf;
}

int MaxSolver::greedyAddNewForcedBvars() {
  // We pass only forced b-vars to the greedy solver
  int nf{0};
  // bvars.printVars();
  for (auto l : greedyNU.new_units(satsolver)) {
    if (bvars.isBvar(l)) {
      nf++;
      greedysolver->addClause({l});
    }
  }
  if (params.verbosity > 0 && nf > 0)
    cout << "c Add to greedysolver " << nf << " Forced bvars.\n";
  return nf;
}

void MaxSolver::satSolverAddBvarsFromSofts() {
  // If we are using only the Fb theory, when a soft is satisfied by forced
  // literals the corresponding b-variable will not be set. Use this routine
  // to add these forced b-variables to the sat solver. (This allows the sat
  // solver to delete these softs And also to pass the forced b-vars to CPLEX,
  // the muser and the greedy solver perhaps helping them as well.) Note we
  // can only process ordinary variables from the sat solver.
  int nf{};
  for (auto l : satBvarNU.new_units(satsolver))
    if (bvars.isOvar(l)) {
      for (auto sftIdx : sftSatisfied[toInt(l)]) {
        Lit blit = bvars.litOfCls(sftIdx);
        if (satsolver->fixedValue(blit) == l_Undef) {
          ++nf;
          satsolver->addClause({~blit});
          // debug
          // cout << "Adding forced negated blit to satsolver " << ~blit <<
          // "\n";
        }
      }
    }
  if (params.verbosity > 0 && nf > 0)
    cout << "c Add to satsolver " << nf << " forced negated bvars.\n";
}

int MaxSolver::cplexAddNewClauses() {
  auto n_new_constraints = cplexClauses.size();
  double totalLits = cplexClauses.total_size();
  log(1, "c CPLEX: += ", cplexClauses.size(), " Average size = ",
      fix4_fmt(cplexClauses.size() ? totalLits / cplexClauses.size() : 0));
  for (size_t i = 0; i < cplexClauses.size(); i++) {
    cplexAddCls(cplexClauses.getVec(i));
  }
  cplexClauses.clear();
  return n_new_constraints;
}

int MaxSolver::greedyAddNewClauses() {
  auto n_new_constraints = greedyClauses.size();

  if (params.verbosity > 1) {
    double totalLits = greedyClauses.total_size();
    cout << "c GREEDY: += " << greedyClauses.size();
    if (greedyClauses.size())
      cout << " Clauses. Average size ="
           << fix4_fmt(greedyClauses.size() ? totalLits / greedyClauses.size()
                                            : 0);
    cout << "\n";
  }
  for (size_t i = 0; i < greedyClauses.size(); i++) {
    greedysolver->addClause(greedyClauses.getVec(i));
  }
  greedyClauses.clear();
  return n_new_constraints;
}

void MaxSolver::processMutexes() {
  for (auto& mx : theWcnf->get_SCMxs()) {
    cplex->add_mutex_constraint(mx);
    greedysolver->addMutexConstraint(mx);
  }
}

void MaxSolver::seed_equivalence() {
  /*find clauses that can be feed into CPLEX.

    Utilize the fact that the sat solver (which has already done a
    solve of the hards) might have simplified the clauses. In previous
    version we did try explicitly calling cadical's simplifier, but
    this did not seem to make the problem better for feeding into
    CPLEX.  It remains to be seen what is the best simplification
    process for feeding into CPLEX.

    First we freeze all b-vars then call simplify with zero
    rounds. This has the property with cadical that it calls
    restore_clauses() to restore all clauses with b-vars. Otherwise on
    some instances, the set of clauses in the sat solver proper can be
    incomplete---some of the necessary clauses end up on the extension
    stack rather than in the sat solver's clause database.
  */

  printNclausesInSatSolver("Eqseed start:");
  for (auto blit : bvars.getCoreLits()) satsolver->freezeLit(blit);

  auto p_nfixed = satsolver->getNFixed();
  auto p_nsubs = satsolver->getNSubstituted();
  auto p_nelim = satsolver->getNEliminated();
  auto p_nclauses = satsolver->getNclauses();
  auto sim_start = cpuTime();
  satsolver->simplify(0);
  auto sim_time = cpuTime() - sim_start;
  log(1, "c cadical simplify took ", time_fmt(sim_time), '\n',
      "c fixed = ", satsolver->getNFixed() - p_nfixed,
      " substitued = ", satsolver->getNSubstituted() - p_nsubs,
      " eliminated = ", satsolver->getNEliminated() - p_nelim,
      " total variables removed = ",
      satsolver->getNFixed() - p_nfixed + satsolver->getNSubstituted() -
          p_nsubs + satsolver->getNEliminated() - p_nelim,
      " clauses in solver = ", satsolver->getNclauses(),
      " clauses removed = ", satsolver->getNclauses() - p_nclauses);

  auto satsolver_n_clauses = satsolver->getNclauses();

  vector<vector<Lit>> cplex_cores;
  vector<vector<Lit>> cplex_ncores;
  vector<vector<Lit>> cplex_mixed;
  vector<vector<Lit>> cplex_ordinary;
  bool seed_all =
      static_cast<size_t>(params.seed_all_limit) >= theWcnf->nVars();
  allClausesSeeded = true;
  bool is_core, is_ncore, is_mixed;

  bool isLearnt;
  for (size_t i = 0; i < satsolver_n_clauses; i++) {
    vector<Lit> seedingCls;
    isLearnt = satsolver->get_ith_clause(seedingCls, i);
    if (!params.seed_learnts && isLearnt) continue;
    if (seedingCls.empty()) continue;
    is_core = is_ncore = is_mixed = true;
    for (auto l : seedingCls) {
      is_core &= bvars.isCore(l);
      is_ncore &= bvars.isNonCore(l);
      is_mixed &= bvars.isBvar(l);
    }
    bool keep = seed_all || theWcnf->orig_all_lits_are_softs() || is_core ||
        (is_ncore && params.seed_type > 1) ||
        (is_mixed && params.seed_type > 2);
    if (!keep) {
      seedingCls.clear();
      if (!isLearnt) allClausesSeeded = false;
    }
    if (seedingCls.size() == 2 &&
        bvars.areSubsumedByMx(seedingCls[0], seedingCls[1])) {
      seedingCls.clear();
    }

    if (seedingCls.size() > 0) {
      if (is_core)
        cplex_cores.push_back(std::move(seedingCls));
      else if (is_ncore)
        cplex_ncores.push_back(std::move(seedingCls));
      else if (is_mixed)
        cplex_mixed.push_back(std::move(seedingCls));
      else
        cplex_ordinary.push_back(std::move(seedingCls));
    }
  }

  for (auto blit : bvars.getCoreLits()) satsolver->thawLit(blit);

  if (params.verbosity > 0) {
    auto n = cplex_cores.size() + cplex_ncores.size() + cplex_mixed.size() +
        cplex_ordinary.size();
    cout << "c EqSeed: found " << n << " seedable constraints.\n";
    cout << "c EqSeed: " << cplex_cores.size() << " cores "
         << cplex_ncores.size() << " non-cores " << cplex_mixed.size()
         << " mixed-cores " << cplex_ordinary.size() << " ordinary clauses\n";
  }

  // Now add the accumulated seed constraints up to the supplied limit.
  // prioritize. cores before nonCores before Mixed.
  // Short constraints before long ones.

  auto vecSizeLt = [](const vector<Lit>& v1, const vector<Lit>& v2) {
    return v1.size() < v2.size();
  };

  sort(cplex_cores.begin(), cplex_cores.end(), vecSizeLt);
  sort(cplex_ncores.begin(), cplex_ncores.end(), vecSizeLt);
  sort(cplex_mixed.begin(), cplex_mixed.end(), vecSizeLt);
  sort(cplex_ordinary.begin(), cplex_ordinary.end(), vecSizeLt);

  auto addUpTo = [this](vector<vector<Lit>>& c, int& lim, size_t& nAdd) {
    // add up to lim constraints to cplex. Update lim and number
    // added, return total length of constraints added
    size_t tl{};
    for (nAdd = 0; nAdd < c.size() && static_cast<int>(nAdd) < lim; ++nAdd) {
      tl += c[nAdd].size();
      store_cplex_greedy_cls(c[nAdd]);
    }
    lim -= c.size();
    return tl;
  };

  size_t n_cores, n_ncores, n_mixed, n_ordinary;
  size_t l_cores, l_ncores, l_mixed, l_ordinary;
  int limit = params.seed_max;

  l_cores = addUpTo(cplex_cores, limit, n_cores);
  l_ncores = addUpTo(cplex_ncores, limit, n_ncores);
  l_mixed = addUpTo(cplex_mixed, limit, n_mixed);
  l_ordinary = addUpTo(cplex_ordinary, limit, n_ordinary);

  if (limit < 0) allClausesSeeded = false;

  if (params.verbosity > 0) {
    cout << "c EqSeed: #seeded constraints " << params.seed_max - limit << "\n";
    cout << "c EqSeed: cores            " << n_cores << " Ave length "
         << fix4_fmt(n_cores ? l_cores / static_cast<float>(n_cores) : 0.0)
         << "\n";
    cout << "c EqSeed: non-cores        " << n_ncores << " Ave length "
         << fix4_fmt(n_ncores ? l_ncores / static_cast<float>(n_ncores) : 0.0)
         << "\n";
    cout << "c EqSeed: mixed cores      " << n_mixed << " Ave length "
         << fix4_fmt(n_mixed ? l_mixed / static_cast<float>(n_mixed) : 0.0)
         << "\n";
    cout << "c EqSeed: ordinary clauses " << n_ordinary << " Ave length "
         << fix4_fmt(n_ordinary ? l_ordinary / static_cast<float>(n_ordinary)
                                : 0.0)
         << "\n";
    if (allClausesSeeded) cout << "c CPLEX has full input theory\n";
  }
}

void MaxSolver::printStatsAndExit(int signum, int exitType) {
  if (!printStatsExecuted) {
    printStatsExecuted = true;
    double cpu_time = cpuTime();
    double mem_used = Minisat::memUsedPeak();

    if (signum >= 0) { cout << "c INTERRUPTED signal " << signum << "\n"; }
    if (!solved) {
      cout << "c unsolved\n";
      cout << "c Best LB Found: " << wt_fmt(LB() + theWcnf->baseCost()) << "\n";
      cout << "c Best UB Found: " << wt_fmt(UB() + theWcnf->baseCost()) << "\n";
      Weight solCost = UB() + theWcnf->baseCost();
      cout << "o " << wt_fmt(solCost) << "\n";
      cout << "s UNKNOWN\n";
      if (haveUBModel) {
        if (params.printBstSoln) {
          cout << "c Best Model Found:\n";
          printSolution(UBmodel);
        }
        int nfalseSofts;
        auto model_cost = theWcnf->checkModel(UBmodel, nfalseSofts);
        if (fabs(model_cost - solCost) > absGap)
          cout << "c ERROR incorrect model reported\n"
               << "c model cost = " << wt_fmt(model_cost)
               << " computed cost = " << wt_fmt(solCost) << "(UB = " << UB()
               << " basecost = " << wt_fmt(theWcnf->baseCost())
               << ") difference = " << wt_fmt(model_cost - solCost)
               << std::endl;
        else
          cout << "c Number of falsified softs = " << nfalseSofts << "\n";
      } else
        cout << "c No Model of hard clauses found\n";
    }

    cout << "c SAT: #calls " << satsolver->nSolves() << "\n";
    cout << "c SAT: Total time "
         << time_fmt(satsolver->total_time() + muser->total_time()) << "\n";
    cout << "c SAT: #muser calls " << muser->nSolves() << " ("
         << fix4_fmt(muser->nSolves()
                         ? muser->nSucc_Solves() * 100.0 / muser->nSolves()
                         : 0)
         << " % successful)\n";
    cout << "c SAT: Minimize time " << time_fmt(muser->total_time()) << " ("
         << time_fmt(satsolver->total_time() + muser->total_time()
                         ? muser->total_time() * 100.0 /
                             (satsolver->total_time() + muser->total_time())
                         : 0)
         << "%)\n";
    cout << "c SAT: Avg constraint minimization "
         << fix4_fmt(cplex->nCnstr() ? amountConflictMin /
                             static_cast<double>(cplex->nCnstr())
                                     : 0)
         << "\n";
    cout << "c SAT: number of variables substituted "
         << satsolver->getNSubstituted() << '\n';

    cout << "c GREEDY: #calls " << greedysolver->nSolves() << "\n";
    cout << "c GREEDY: Total time " << time_fmt(greedysolver->total_time())
         << "\n";

    cout << "c CPLEX: #calls " << cplex->nSolves() << "\n";
    cout << "c CPLEX: Total time " << time_fmt(cplex->total_time()) << "\n";
    cout << "c CPLEX: #constraints " << cplex->nCnstr() << "\n";
    if (cplex->nCnstr())
      cout << "c CPLEX: Avg constraint size "
           << fix4_fmt(cplex->totalCnstrSize() /
                       static_cast<double>(cplex->nCnstr()))
           << "\n";
    cout << "c CPLEX: #non-core constraints " << cplex->nNonCores() << "\n";
    if (cplex->nNonCores())
      cout << "c CPLEX: Ave non-core size "
           << fix4_fmt(cplex->nNonCores() ? (cplex->totalNonCore()) /
                               (double)cplex->nNonCores()
                                          : 0)
           << "\n";

    cout << "c LP-Bounds: Total time " << time_fmt(cplex->total_lp_time())
         << "\n";
    cout << "c LP-Bounds: #calls " << cplex->nLPSolves() << "\n";
    if (params.lp_harden) {
      cout << "c LP-Bounds: Forced "
           << n_softs_forced_hard + n_softs_forced_false +
              n_softs_forced_hard_not_in_cplex + n_ovars_forced_true +
              n_ovars_forced_false + n_touts_forced_true + n_touts_forced_false
           << " variables\n";
      if (n_softs_forced_hard > 0)
        cout << "c   hardened softs:              " << n_softs_forced_hard
             << "\n";
      if (n_softs_forced_false > 0)
        cout << "c   falsified softs:            " << n_softs_forced_false
             << "\n";
      if (n_softs_forced_hard_not_in_cplex > 0)
        cout << "c   hardened softs not in cplex: "
             << n_softs_forced_hard_not_in_cplex << "\n";
      if (n_ovars_forced_true > 0)
        cout << "c   ordinary vars made true:    " << n_ovars_forced_true
             << "\n";
      if (n_ovars_forced_false > 0)
        cout << "c   ordinary vars made false:   " << n_ovars_forced_false
             << "\n";
      if (n_touts_forced_true > 0)
        cout << "c   touts made true:            " << n_touts_forced_true
             << "\n";
      if (n_touts_forced_false > 0)
        cout << "c   touts made false:           " << n_touts_forced_false
             << "\n";
    }
    cout << "c MEM MB: " << fix4_fmt(mem_used) << "\n";
    cout << "c CPU: " << time_fmt(cpu_time) << "\n";
  }
  fflush(stdout);
  fflush(stderr);
  _exit(exitType);
}

void MaxSolver::reportCplex(Weight cplexLB, Weight solnWt) {
  if (params.verbosity > 0) {
    cout << "c CPLEX returns incumbent with cost " << wt_fmt(solnWt)
         << " and lower bound of " << wt_fmt(cplexLB)
         << " time = " << time_fmt(cplex->solveTime()) << "\n";
  }
}

void MaxSolver::reportSAT_min(lbool result, double iTime, size_t orig_size,
                              int nMins, double mTime, size_t final_size) {
  if (params.verbosity > 1) {
    cout << "c SAT_MIN: " << result;
    if (result == l_False)
      cout << ", In cnf size = " << orig_size
           << ", reduction = " << orig_size - final_size;
    cout << ", Init Sat time: " << time_fmt(iTime) << ", Min calls: " << nMins
         << ", Min time: " << time_fmt(mTime) << "\n";
  }
}

void MaxSolver::reportForced(const vector<Lit>& forced, Weight wt) {
  if (params.verbosity > 0 && forced.size() > 0) {
    cout << "c Forced Soft Clauses (#" << forced.size() << ", wt = " << wt
         << "\n";
    if (params.verbosity > 2) outputConflict(forced);
  }
}

lbool MaxSolver::satsolve_min(const Assumps& inAssumps,
                              vector<Lit>& outConflict, double sat_cpu_lim,
                              double mus_cpu_lim) {
  double isatTime{0};
  lbool result = (sat_cpu_lim > 0)
      ? satsolver->solveBudget(inAssumps.vec(), outConflict, sat_cpu_lim)
      : satsolver->solve(inAssumps.vec(), outConflict);
  if (params.verbosity > 2) {
    cout << "c satsolve_min sat result = " << result
         << " conflict = " << outConflict << "\n";
  }
  size_t origsize{outConflict.size()};
  isatTime = satsolver->solveTime();

  muser->startTimer();
  if (result == l_False) {
    if (params.min_type == 1 && outConflict.size() > 2) {
      minimize_muser(outConflict, mus_cpu_lim);
      amountConflictMin += origsize - outConflict.size();
      if (params.verbosity > 2) {
        cout << "c satsolve_min after minimizer conflict size = "
             << outConflict.size() << " origsize = " << origsize << "\n";
      }
    }
    if (outConflict.size() == 1 ||
        (origsize > outConflict.size() && outConflict.size() < 8)) {
      // add units found by assumption and short clauses reduced by
      // mus back to the solver
      satsolver->addClause(outConflict);
      if (params.verbosity > 1)
        cout << "c satsolve_min added new clause of size " << outConflict.size()
             << ": from conflict\n";
    }
  }
  if (params.fb) satSolverAddBvarsFromSofts();
  reportSAT_min(result, isatTime, origsize, muser->nSatSolvesSinceTimer(),
                muser->elapTime(), outConflict.size());
  return result;
}

void MaxSolver::minimize_muser(vector<Lit>& con, double mus_cpu_lim) {
  /* Muser tries to remove lits from end of con first.
     Sort so that better lits to remove are later in the vector.
  */

  /*static auto minConf = [this](Lit l1, Lit l2) {
    int sc1 = bLitOccur[bvars.toIndex(l1)]+1;
    int sc2 = bLitOccur[bvars.toIndex(l2)]+1;
    if(bvars.wt(l1) == 0 && bvars.wt(l2) == 0)
    return sc1 < sc2;
    else
    return bvars.wt(l1)/sc1 > bvars.wt(l2)/sc2;
    };*/
  if (!doMin) return;
  size_t reduction{0};
  size_t osize{0};
  if (doMin) {
    osize = con.size();
    // cout << "issue with sort\n";
    // std::sort(con.begin(), con.end(), minConf);
    std::sort(con.begin(), con.end(), blit_lt);
    // cout << "not issue with sort\n";
    if (mus_cpu_lim > 0)
      muser->musBudget(con, mus_cpu_lim);
    else
      muser->mus(con);
    // debug
    // check_mus(con);
    if (params.fb) satSolverAddBvarsFromSofts();
    reduction = osize - con.size();
  }

  if (osize > 1) {
    mtime += muser->solveTime();
    ++mcalls;
    m_sum_reduced_frac +=
        osize ? static_cast<double>(reduction) / static_cast<double>(osize) : 0;
  }

  doMin = params.mus_min_red <= 0
      //|| (mtime < 124.0) //give muser some time to allow rate computation
      // to be more accurate
      || mcalls < 4 || (mtime < 64.0)  // give muser some time to allow rate
                                       // computation to be more accurate
      || (mcalls && (m_sum_reduced_frac / mcalls) > params.mus_min_red);

  if (params.verbosity > 1)
    cout << "c doMin = " << doMin << " mtime = " << mtime
         << " average reduction = "
         << fix4_fmt(mcalls ? m_sum_reduced_frac / mcalls : 0.0) << "\n";
}

void MaxSolver::check_mus(vector<Lit>& con) {
  // Test to see if con is a MUS (DEBUGGING)
  size_t orig_size = con.size();
  vector<Lit> assumps;
  vector<Lit> critical;
  vector<Lit> tmp;
  auto litHash = [](const Lit l) { return std::hash<int>()(toInt(l)); };
  std::unordered_set<Lit, decltype(litHash)> inCon(con.size(), litHash);
  auto findInCon = [&inCon](Lit l) { return inCon.find(l) == inCon.end(); };

  // For sorting the conflict before it is minimized
  //   Can't make all lits in conflict true. Neg bvars:
  //   must make one true == relax one of these
  //   soft clauses. So try to remove low weight neg bvars
  //   so that we must relax a high weight soft.

  //   Pos bvar: must make one false == can't relax
  //   one of these softs. So try to remove high weight pos
  //   bvars, so that we are blocked only from relaxing low
  //   weight softs.

  //   Forcing relaxations is better than blocking.
  //   So try to remove all positives first.

  //   We remove from the end, so sort to put best removals at the end

  // auto mConf = [this](Lit i, Lit j) {
  //   return
  //   (sign(i) && !sign(j))
  //   || (sign(i) && sign(j) && (bvars.wt(var(i)) < bvars.wt(var(j))))
  //   || (!sign(i) && !sign(j) && (bvars.wt(var(i)) > bvars.wt(var(j)))); };

  // std::sort(con.begin(), con.end(), mConf);
  assumps.clear();
  for (size_t i = 0; i < con.size(); i++) assumps.push_back(~con[i]);
  if (satsolver->solve(assumps, tmp) == l_True)
    cout << "check_mus: ERROR mus not unsatisfiable\n";

  while (con.size() > 0) {
    Lit min = con.back();
    con.pop_back();

    assumps.clear();
    for (size_t i = 0; i < critical.size(); i++)
      assumps.push_back(~critical[i]);
    for (size_t i = 0; i < con.size(); i++) assumps.push_back(~con[i]);

    if (satsolver->solve(assumps, tmp) == l_True) {
      // min was critical
      critical.push_back(min);
    } else {
      inCon.clear();
      for (auto lt : tmp) inCon.insert(lt);
      auto p = std::remove_if(con.begin(), con.end(), findInCon);
      con.erase(p, con.end());
    }
  }
  con = critical;

  if (con.size() != orig_size) {
    cout << "check_mus: ERROR mus not minimal orig size = " << orig_size
         << " reduced size = " << con.size() << "\n";
    cout << " conflict = " << con << "\n";
  }
}

void MaxSolver::outputConflict(const vector<Lit>& con) {
  cout << "conflict clause (" << con.size() << "): ";
  for (size_t i = 0; i < con.size(); i++)
    cout << con[i] << ':' << satsolver->fixedValue(con[i]) << ' ';
  cout << "\n";
}

// Currently not used. But if we call satsolver->pruneLearnts
// This function will be used to determine which learnts to delete
// Potentially inefficient if called frequently...requires copying
// Sat solver's clause into passed std:vector.
bool MaxSolver::deleteLearntTest(const vector<Lit>& c) const {
  if (c.size() <= 3) return false;
  // keep hard learnts
  // if (!params.delete_hard_learnts) {
  bool containsBVar = false;
  for (size_t i = 0; i < c.size(); i++) {
    if (bvars.isBvar(c[i])) {
      containsBVar = true;
      break;
    }
  }
  // no b-var==> hard learnt
  if (!containsBVar) { return false; }
  return true;
}

void MaxSolver::unsatFound() {
  cout << "c Hard Clauses are UNSAT.\n";
  cout << "s UNSATISFIABLE\n";
  updateLB(theWcnf->dimacsTop());
  unsat = true;
  solved = true;
  cout << "c Final LB: " << wt_fmt(LB()) << "\n";
  cout << "c Final UB: " << wt_fmt(UB()) << "\n";
  fflush(stdout);
}

void MaxSolver::optFound(const std::string& reason) {
  cout << reason << "\n";
  Weight solCost = UB() + theWcnf->baseCost();
  cout << "o " << wt_fmt(solCost) << "\n";
  cout << "s OPTIMUM FOUND\n";
  solved = true;
  printSolution(UBmodel);
  int nfalseSofts;
  Weight model_cost = theWcnf->checkModelFinal(UBmodel, nfalseSofts);
  if (fabs(model_cost - solCost) > absGap)
    cout << "c ERROR incorrect model reported\n"
         << "c model cost = " << wt_fmt(model_cost)
         << " computed cost = " << wt_fmt(solCost) << "(UB = " << wt_fmt(UB())
         << " basecost = " << wt_fmt(theWcnf->baseCost())
         << ") difference = " << wt_fmt(model_cost - solCost) << std::endl;
  else
    cout << "c Solved: Number of falsified softs = " << nfalseSofts << "\n";
}

void MaxSolver::checkModel(const std::string& location) {
  cout << "c CHECKING model found at " << location << "\n";
  int nfalseSofts;
  auto soln_cost{theWcnf->checkModel(UBmodel, nfalseSofts)};
  cout << "c Model reported has cost " << wt_fmt(soln_cost) << " falsifying "
       << nfalseSofts << " softs.\n";
  cout << "c UB cost = " << wt_fmt(UB())
       << " base cost = " << wt_fmt(theWcnf->baseCost())
       << " totalclswt = " << wt_fmt(theWcnf->totalClsWt()) << '\n';
  cout << " Diff = " << wt_fmt((UB() + theWcnf->baseCost()) - soln_cost)
       << '\n';
}

void MaxSolver::printCurClause(const vector<Lit>& cls) {
  cout << '[';
  for (auto i = cls.begin(); i != cls.end() - 1; i++)
    cout << *i << ':' << satsolver->fixedValue(*i) << ", ";
  if (cls.size() > 0)
    cout << cls.back() << ':' << satsolver->fixedValue(cls.back());
  cout << ']';
}

void MaxSolver::printNclausesInSatSolver(const std::string& msg) {
  log(1, "c ", msg, " sat solver has ",
      satsolver->getNRedundant() + satsolver->getNIrredundant(),
      " clauses: ", satsolver->getNRedundant(), " redundant, ",
      satsolver->getNIrredundant(), " irredundant.");
}

void MaxSolver::printErrorAndExit(const char* msg) {
  cout << msg << "\n";
  printStatsAndExit(-1, 1);
}

void MaxSolver::printSolution(const vector<lbool>& model) {
  // For the Evaluation. Prints the "v " line, which contains the last
  // satisfying assignment found by the SAT solver (only original
  // literals, no b-vars).
  // Typically model is filled in before calling, but if model is
  // incomplete (contains l_Undef) these vars will be printed as false
  // in the code below.
  if (!params.printSoln) return;
  vector<lbool> external_model = theWcnf->rewriteModelToInput(model);

  if (params.printNewFormat) {
    std::string vline(external_model.size() + 2, ' ');
    vline[0] = 'v', vline[1] = ' ';
    for (size_t i = 0; i < external_model.size(); i++)
      vline[i + 2] = (external_model[i] == l_True ? '1' : '0');
    cout << vline << std::endl;
    // cout << "v ";
    // for (size_t i = 0; i < external_model.size(); i++) {
    //   cout << (external_model[i] == l_True ? '1' : '0');
    // }
    // cout << std::endl;
  } else {
    cout << 'v';
    for (size_t i = 0; i < external_model.size(); i++) {
      cout << ' ' << (external_model[i] == l_True ? "" : "-") << i + 1;
    }
    cout << std::endl;
  }
}

void MaxSolver::configBvar(Var bvar, SatSolver* slv) {
  // Configure any blits after they have been added to the sat solver
  // Should be passed literal appearing in soft clause (i.e.,
  // blit=false ==> enforce clause)
  // In particular we must stop the solver from eliminating
  // any b-variable.
  // slv->freezeVar(bvar);

  // set default polarity so as to make the b-var harden the clause
  //
  slv->setPolarity(
      (bvars.coreIsPos(bvar) || bvars.orig_coreIsPos(bvar)) ? l_False : l_True,
      bvar);
}

void MaxSolver::addHards(SatSolver* slv) {
  for (size_t i = 0; i < theWcnf->nHards(); i++) {
    for (auto lt : theWcnf->hards()[i])
      if (bvars.isBvar(lt) || (params.mx_seed_originals && bvars.inMutex(lt)))
        configBvar(var(lt), slv);
    slv->addClause(theWcnf->getHard(i));
  }
}

void MaxSolver::addSofts(SatSolver* slv) {
  for (size_t i = 0; i < theWcnf->nSofts(); i++) {
    Lit blit = bvars.litOfCls(i);
    /*cout << "Soft clause " << i << ' ' << theWcnf->getSoft(i) << "\n"
      << "blit = " << blit << "\n";*/
    if (theWcnf->softSize(i) > 1) {
      // Only non-unit softs get added to solver (units are handled in the
      // assumptions)
      vector<Lit> sftCls{theWcnf->getSoft(i)};
      sftCls.push_back(blit);
      // printCurClause(sftCls);
      // cout << "\n";
      for (auto lt : sftCls)
        if (bvars.isBvar(lt) || (params.mx_seed_originals && bvars.inMutex(lt)))
          configBvar(var(lt), slv);
      slv->addClause(sftCls);
    }
  }
}

void MaxSolver::addSoftEqs(SatSolver* slv, bool removable) {
  // add eqs to solver. Optionally make them removable
  // Note all softs processed here should have already been added
  // to the solver to config their b-vars.
  vector<Lit> eqcls(removable ? 3 : 2, lit_Undef);
  if (removable && eqCvarPos == lit_Undef) {
    eqCvar = bvars.newCtrlVar();
    eqCvarPos = mkLit(eqCvar);
  }
  for (size_t i = 0; i < theWcnf->nSofts(); i++) {
    if (theWcnf->softSize(i) <= 1) continue;
    Lit bneg = ~bvars.litOfCls(i);
    for (auto l : theWcnf->softs()[i]) {
      eqcls[0] = ~l;
      eqcls[1] = bneg;
      if (removable) eqcls[2] = eqCvarPos;
      // note addClause modifies eqcls
      slv->addClause(eqcls);
    }
  }
}

void MaxSolver::initSftSatisfied() {
  vector<vector<int>> satByLit(theWcnf->nVars() * 2, vector<int>{});
  for (size_t i = 0; i < theWcnf->nSofts(); i++)
    for (auto lt : theWcnf->softs()[i]) satByLit[toInt(lt)].push_back(i);
  for (auto& v : satByLit) sftSatisfied.addVec(v);
  // Debug
  /*cout << "Softs\n";
    cout << theWcnf->softs();
    cout << "\nFinal occurance list\n";
    cout << sftSatisfied;*/
}

void MaxSolver::improveModel() {
  // // Sat solver has found a model. Try to improve the cost of that model by
  //   // computing a muc.
  //   vector<Lit> assumps;
  //   vector<Lit> branchLits;
  //   Weight prevWt{0};
  //   if (params.verbosity > 0) {
  //     cout << "c Trying to improve Model\n";
  //     // cout << "totalClsWt() = " << theWcnf->totalClsWt() << "
  //     getSatClsWt() =
  //     // "
  //     // << getSatClsWt() << "\n";
  //     prevWt = theWcnf->totalClsWt() - getSatClsWt();
  //     cout << "c Current Model weight = " << prevWt << "\n";
  //   }

  //   for (size_t i = 0; i < bvars.n_bvars(); i++) {
  //     /*cout << "soft clause #" << i << " litofCls = " << bvars.litOfCls(i)
  //       << " model value = " << satsolver->modelValue(bvars.litOfCls(i)) <<
  //       "\n";*/
  //     if (satsolver->fixedValue(bvars.litOfCls(i)) ==
  //         l_Undef) {  // only try to change un-forced b's
  //       auto tval = satsolver->modelValue(bvars.litOfCls(i));
  //       if (tval == l_True)
  //         branchLits.push_back(~bvars.litOfCls(i));  // try to negate these
  //         bvars
  //       else
  //         assumps.push_back(~bvars.litOfCls(i));  // these bvars must
  //         remain false
  //     }
  //   }

  //   if (params.verbosity > 1) {
  //     cout << "c assumptions size = " << assumps.size()
  //          << " branchlits size = " << branchLits.size() << "\n";
  //     /*cout << "Assumps = " << assumps << "\n";
  //       cout << "branchlits = " << branchLits << "\n";*/
  //   }

  //   // if(params.improve_model_max_size > 0 &&
  //   // static_cast<int>(branchLits.size()) > params.improve_model_max_size)
  //   //  return;

  //   auto val =
  //       satsolver->relaxSolve(assumps, branchLits,
  //       params.improve_model_cpu_lim);

  //   if (params.verbosity > 0) {
  //     cout << "c Relaxation search yielded " << val << "\n";
  //     Weight newWt = theWcnf->totalClsWt() - getSatClsWt();
  //     cout << "c Old wt = " << prevWt << " new wt = " << newWt
  //          << " improvement = " << prevWt - newWt << "\n";
  //   }
  //
}

Weight MaxSolver::updateUB() {
  // return weight of new model...update UB if it is a better model.
  Weight w = getSatClsWt();
  if (!haveUBModel || w > sat_wt) {
    sat_wt = w;
    if (params.verbosity > 0) {
      cout << "c New UB found " << wt_fmt(UB()) << "\n";
      cout << "c Elapsed time " << time_fmt(cpuTime() - globalStartTime)
           << "\n";
    }
    have_new_UB_model = true;
    setUBModel();
    // checkModel("");
  }
  return theWcnf->totalClsWt() - w;
}
void MaxSolver::setUBModel() {
  // copy sat solvers model to UBmodel; Note sat solver's model might
  // be incomplete resulting in l_Undef as the value of some variables
  haveUBModel = true;
  if (bvars.n_vars() > UBmodel.size()) UBmodel.resize(bvars.n_vars(), l_Undef);
  for (size_t i = 0; i < bvars.n_vars(); i++)
    UBmodel[i] = satsolver->modelValue(i);
  for (size_t i = 0; i < theWcnf->nSofts(); i++) {
    UBmodelSofts[i] = tmpModelSofts[i];
    if (UBmodelSofts[i] == l_True) {
      // check if blit is set to true (it shouldn't be)
      auto blit = bvars.litOfCls(i);
      if (UBmodel[var(blit)] == (sign(blit) ? l_False : l_True) &&
          blit_true_warning) {
        cout << "c WARNING blit in model not set to false when soft is "
                "satisfied\n";
        blit_true_warning = false;
      } else if (UBmodel[var(blit)] == l_Undef) {
        cout << "c setting unset blit in UBmodel\n";
        UBmodel[var(blit)] = sign(blit) ? l_True : l_False;
      }
    }
  }
}

Weight MaxSolver::getSatClsWt() {
  // return sum of weight of satisfied clauses.
  // Note sat solver's model might be incomplete.
  // and bvars might not be set.
  Weight w{0.0};
  for (size_t i = 0; i < theWcnf->nSofts(); i++) {
    bool is_sat = false;
    // calling theWcnf->softs() avoids copying soft clauses.
    for (auto ell : theWcnf->softs()[i])
      if (satsolver->modelValue(ell) == l_True) {
        is_sat = true;
        break;
      }
    if (is_sat) {
      w += theWcnf->getWt(i);
      tmpModelSofts[i] = l_True;
    } else {
      tmpModelSofts[i] = l_False;
    }
    /*else {
      cout << i << "-th soft falsified bvar = "
      << bvars.litOfCls(i) << " value = "
      << satsolver->modelValue(bvars.litOfCls(i)) << "\n";
      cout << "[ ";
      for(auto ell : theWcnf->softs()[i]) {
      cout << ell << satsolver->modelValue(ell) << ' ';
      }
      cout << "]\n";
      }*/
  }
  return w;
}

Weight MaxSolver::getForcedWt() {
  // return weight of forced b-vars. Note that
  // this works with both fb and fbeq. In fb the solver could set some
  // b-vars arbitrarily. But it can't force them to be true.
  Weight forced_wt{};
  for (auto blit : bvars.getCoreLits()) {
    auto val = satsolver->fixedValue(blit);
    if (val == l_True) forced_wt += bvars.wt(blit);
  }
  return forced_wt;
}

Weight MaxSolver::getWtOfBvars(const vector<Lit>& blits) {
  Weight w{0};
  // cout << "true b lits: ";
  for (auto b : blits) {
    if (bvars.isBvar(b)) {
      w += bvars.wt(b);
      /*if (bvars.wt(b) > 0)
        cout << b << ' ';*/
    }
  }
  // cout << "\n";
  return w;
}

void MaxSolver::store_cplex_greedy_cls(const vector<Lit>& cls) {
  // clauses of size 1 are forced in sat solver and will
  // be added by AddNewForcedBvars; Only cores are added to the greedy
  // solver
  if (cls.size() <= 1) return;
  cplexClauses.addVec(cls);
  bool core{true}, core_summation{true};
  for (auto lt : cls) {
    core &= bvars.isCore(lt);
    core_summation &= (bvars.isCore(lt) || summations->isSoutput(lt));
  }
  if (core) {
    incrBLitOccurrences(cls);
    greedyClauses.addVec(cls);
  }
  if (params.abstract && core_summation) summations->add_core(cls);
}

vector<Lit> MaxSolver::greedySoln(bool useGreedy, bool need_soln) {
  // Compute a new greedy solution. Must use the greedy solver
  // if useGreedy, and must return a solution if need_soln.
  // Otherwise if we are using the greedy solver and no
  // new conficts have been added to it we do not return a solution
  //(return an empty vector)

  vector<Lit> soln;
  bool greedy{useGreedy || params.cplexgreedy == 0 || top_freq == 0 ||
              (params.cplexgreedy == 2 && !summations->summations_active())};
  if (greedy) {
    int nc{0};
    nc += greedyAddNewForcedBvars();
    nc += greedyAddNewClauses();
    if (need_soln || nc) {
      soln = greedysolver->solve();
      if (params.verbosity > 1) {
        cout << "c Greedy: soln cost = " << wt_fmt(getWtOfBvars(soln)) << "\n";
      }
    } else if (params.verbosity > 0) {
      cout << "c no new constraints for greedy skipping call to solver\n";
    }
  } else {  // cplex
    int nc{0};
    nc += cplexAddNewForcedBvars();
    nc += cplexAddNewClauses();
    if (need_soln || nc) {
      cplex->greedySolution(soln, top_freq);
      if (params.verbosity > 0) {
        cout << "c Cplex Greedy: soln cost = " << wt_fmt(getWtOfBvars(soln))
             << "\n";
      }
    } else if (params.verbosity > 0) {
      cout << "c no new constraints for greedy skipping call to cplex\n";
    }
  }
  /*else {
    auto val = greedySatSolver->solve();
    if(val == l_False)
    cout << "c ERROR. CPLEX clauses have no solution (or greedy solver
    couldn't find one)\n"; for(size_t i = 0; i < bvars.n_bvars(); i++) { Var v
    = bvars.varOfCls(i); lbool val = greedySatSolver->modelValue(v); if(val ==
    l_True) soln.push_back(mkLit(v, false)); else if(val == l_False)
    soln.push_back(mkLit(v, true));
    else if(val == l_Undef)
    soln.push_back(~bvars.litOfCls(i)); //harden clause if no value assigned
    }
    }*/
  /*cout<< "a Greedy sol cost:\n";
    for (Lit l: soln)
    cout << "a Lit : " << l << "\n";
  */
  return soln;
}

bool MaxSolver::vec_isCore(const vector<Lit>& core) {
  for (auto l : core)
    if (bvars.isNonCore(l)) return (false);
  return true;
}

bool MaxSolver::BLitOrderLt::operator()(const Lit l1, const Lit l2) const {
  // must be strict weak order:
  // if either L1 or L2 is a Tvar order it infront
  bool retval{0};
  if (!bvars.isBvar(l1) && !bvars.isBvar(l2))
    retval = (l1 < l2) ^ gt;
  else if (!bvars.isBvar(l1))
    retval = 1 ^ gt;
  else if (!bvars.isBvar(l2))
    retval = 0 ^ gt;
  else {
    int oc1 = (*occurCount)[bvars.toIndex(l1)];
    int oc2 = (*occurCount)[bvars.toIndex(l2)];
    Weight wt1 = bvars.wt(l1);
    Weight wt2 = bvars.wt(l2);
    // bool retval {0};

    if (wt1 == 0 && oc1 > 0) {  // l1 is super---satisfies cores at zero cost
      if (wt2 == 0 && oc2 > 0)  // so is l2
        if (oc1 == oc2)
          retval = (l1 < l2);  // order lits the same for gt and lt
        // when discriminators are equal
        else
          retval = (oc1 < oc2) ^ gt;  // XOR: we know that oc1 !=
      // oc2. So if (oc1 < oc2) == 0,
      // then l1 > l2.
      else                           // l2 is not super
        retval = gt;                 // l1 > l2
    } else if (wt2 == 0 && oc2 > 0)  // l1 is not super but l2 is
      retval = !gt;                  // l1 < l2
    else {
      // Neither is super compute merit
      Weight m1{0.0};
      Weight m2{0.0};

      // note since lits not super wt == 0 ==> oc == 0; no division by 0
      m1 = (oc1 == 0) ? -wt1 : oc1 / wt1;
      m2 = (oc2 == 0) ? -wt2 : oc2 / wt2;

      if (m1 == m2) {
        if (bvars.clsSize(l1) == bvars.clsSize(l2))
          retval = (l1 < l2);
        else
          retval = (bvars.clsSize(l1) < bvars.clsSize(l2)) ^ gt;
      } else
        retval = (m1 < m2) ^ gt;
    }
  }
  return retval;
}
