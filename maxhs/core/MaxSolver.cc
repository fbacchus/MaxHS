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

#include <cmath>
#include <algorithm>
#include <map>
#include <unordered_set>
#include <zlib.h>
#include <iostream>
#include <iomanip>
#include <utility>

#include "maxhs/core/MaxSolver.h"
#include "maxhs/utils/io.h"
#include "maxhs/ifaces/miniSatSolver.h"
#include "maxhs/ifaces/GreedySolver.h"
//#include "maxhs/ifaces/greedySatSolver.h"
#include "minisat/utils/System.h"

//using namespace Minisat;
using namespace MaxHS;
using namespace MaxHS_Iface;

using std::endl;
using std::cout;
using std::pair;

MaxSolver::MaxSolver(Wcnf *f) : //many of are already default initialized...but for clarity
  theWcnf {f},
  bvars {f},
  satsolver {new MaxHS_Iface::miniSolver{}},
  greedysolver {nullptr},
  //  greedySatSolver {nullptr},
  muser {new MaxHS_Iface::Muser{theWcnf, bvars}},
  sat_wt {0.0},
  forced_wt {0.0},
  lower_bnd {0.0},
  absGap {params.tolerance},
  UBmodel (theWcnf->nVars(), l_Undef),
  UBmodelSofts (theWcnf->nSofts(), l_False),
  tmpModelSofts (theWcnf->nSofts(), l_False),
  haveUBModel {false},
  have_new_UB_model {false},
  eqCvar {static_cast<Var>(bvars.maxvar()+1)},
  eqCvarPos (lit_Undef),
  nextNewVar {eqCvar+1},
  bLitOccur (bvars.n_blits(), 0),
  cplexClauses {},
  sftSatisfied {},
  cplexNU {},
  greedyNU {},
  muserNU {},
  satNU {},
  satBvarNU {},
  forcedWtNU {},
  amountConflictMin {0},
  globalStartTime {0},
  printStatsExecuted {false},
  solved {false},
  unsat {false},
  n_softs_forced_hard {0},
  n_softs_forced_relaxed {0},
  n_softs_forced_hard_not_in_cplex {0},
  nFailedLits {0},
  nForcedByBounds {0},
  allClausesSeeded {false},
  m_sum_reduced_frac {0},
  mtime {0.0},
  mcalls {0},
  doMin {true},
  blit_lt {&bLitOccur, bvars, false},
  blit_gt {&bLitOccur, bvars, true}
{
  params.instance_file_name = theWcnf->fileName();
  if(theWcnf->integerWts())
    absGap = 0.75;
  cplex  = new Cplex {bvars, UBmodelSofts, theWcnf->integerWts()};
  if(!cplex->is_valid())
    cout << "c ERROR. Problem initializing CPLEX solver\n";
  /*if(theWcnf->getMxs().size() > 0)
    greedySatSolver = new MaxHS_Iface::GreedySatSolver{bvars};
    else */
  greedysolver = new MaxHS_Iface::GreedySolver{bvars};
  // if(theWcnf->integerWts())
  cout << std::setprecision(8);
}

MaxSolver::~MaxSolver() {
  if (satsolver)
    delete satsolver;
  if (greedysolver)
    delete greedysolver;
  //if (greedySatSolver)
  //  delete greedySatSolver;
  if (cplex)
    delete cplex;
}

bool MaxSolver::doPreprocessing() {
  //test if we should do preprocessing.
  //We have to freeze all unit softs. So if this spans all variables we won't
  //be able to eliminate any variables in preprocessing.
  if(!params.preprocess)
    return false;

  const int not_seen {0}, seen {1};
  int toBeFrozen {0}, totalVars {0};
  vector<char> varStatus(theWcnf->nVars(), not_seen);

  //Run through the non-unit soft and hard clauses, marking all
  //variables as not-frozen, and count all newly seen variables
  for(auto hc: theWcnf->hards())
    for(auto lt: hc)
      if(varStatus[var(lt)] == not_seen) {
        ++totalVars;
        varStatus[var(lt)] = seen;
      }
  for(auto sc: theWcnf->softs())
    if(sc.size() > 1)
      for(auto lt: sc)
        if(varStatus[var(lt)] == not_seen) {
          ++totalVars;
          varStatus[var(lt)] = seen;
        }
  //Now go through the unit softs. Count those that appear in the
  //non-unit softs and hards as to be frozen
  for(auto sc: theWcnf->softs())
    if(sc.size() == 1) {
      Var v = var(sc[0]);
      if(varStatus[v] == seen) {
        ++toBeFrozen;
        varStatus[v] = not_seen; //only units once
      }
    }
  if(params.verbosity > 0)
    cout << "c Total used vars = " << totalVars << " vars to be frozen = " << toBeFrozen << "\n";
  return toBeFrozen < totalVars;
}

void MaxSolver::solve() {
  globalStartTime = cpuTime();

  if(theWcnf->isUnsat()) {
    cout << "c Unsat Found by theWcnf\n";
    unsatFound();
    return;
  }

  if(!doPreprocessing())
    satsolver->eliminate(true);

  addHards(satsolver);
  addSofts(satsolver);
  //add eq clauses if using fbeq.
  if(params.fbeq)
    addSoftEqs(satsolver, false); //permanent eq clauses
  //Otherwise we will add forced negated b-vars to the sat solver
  //after sat solving episodes---weaker than adding the eq clauses
  if(params.fb)
    initSftSatisfied();

  if(params.preprocess) {
    auto start = cpuTime();
    satsolver->eliminate(true);
    if(params.verbosity > 0)
      cout << "c MiniSat Preprocess eliminated " << satsolver->nEliminated() << " variables. took " << cpuTime()-start << " sec.\n";
  }

  if(params.verbosity > 0)
    cout << "c Before solving sat solver has " << satsolver->getNClauses(0) << " clauses and "
         << satsolver->getNClauses(1) << " learnts\n";

  //1. Compute an initial lower and upper bound by solving the theory
  //   Note only unsat if the hards are unsat, otherwise will set soft
  //   clauses in an arbitary way.
  auto hards_are_sat = satsolver->solve();
  if(hards_are_sat == l_False) {
    unsatFound();
    return;
  }

  if(params.verbosity > 0)
    cout << "c Init Bnds: SAT Time " << satsolver->solveTime() << "\n";
  if(params.improve_model)
    improveModel();
  updateLB(getForcedWt()); //get forced weight.
  updateUB();
  if(fabs(UB()-LB()) <= absGap) {
    optFound("c Solved by Init Bnds.");
    return;
  }

  if (params.verbosity > 0) {
    cout << "c Init Bnds: LB = " << LB() << " UB = " << UB() << "\n";
    cout << "c Init Bnds: Forced " << satsolver->nAssigns() << " literals.\n";
    cout << "c Init Bnds: after sat solver solver has " << satsolver->getNClauses(0) << " clauses and "
         << satsolver->getNClauses(1) << " learnts\n";
  }

  if(fabs(UB()-LB()) <= absGap) {
    optFound("c Solved by Initial Bnds.");
    return;
  }

  //DEBUG
  //cout << "Init Bnds: Forced " << satsolver->nAssigns() << " literals.\n"
  // << satsolver->getForced(0) << "\n";
  //

  if(params.fb) //add forced negated b-vars to sat solver
    satSolverAddBvarsFromSofts();

  if(params.prepro_output) {
    for(int isLearnt=0; isLearnt < 2; isLearnt++) {
      for(int i =0; i < satsolver->getNClauses(isLearnt); i++) {
        auto clause = satsolver->getIthClause(i, isLearnt);
        cout << (isLearnt ? "l#" : "c#") << i << " [ ";
        for (auto l : clause) {
          cout << l;
          if(bvars.isBvar(l))
            cout << " (B " << bvars.wt(l) << "), ";
          else
            cout << ", ";
        }
        cout << "] (" << clause.size() << ")\n";
      }
    }
  }

  //2. Seed CPLEX
  if (!satsolver->simplify()) //remove satisfied clauses before seeding
    printErrorAndExit("c ERROR: UNSAT detected when simplify clauses");

  if (params.seed_type)
    seed_equivalence();

  //4. Disjoint Phase
  if(allClausesSeeded)
    //when all clauses feed to cplex we will do a special greedy phase to
    //get a better upper bound model then start up cplex. We do
    //we want the greedy phase to start with only the disjoint cores.
    //and we do not want the found greedy cores to be given to cplex.
    greedyClauses.clear();

  //3. Disjoint Phase
  if (params.dsjnt_phase)
    disjointPhase();
  if(fabs(UB()-LB()) <= absGap) {
    optFound("c Solved by Disjoint phase.");
    return;
  }

  //4. mutexes processing.
  processMutexes();

  //5. Solve.
  seqOfSAT_maxsat();
}

void MaxSolver::disjointPhase() {
  Assumps assumps(satsolver, bvars);
  int num {0};
  int len {0};
  Weight lb_weight {0.0};

  if (params.verbosity > 0)
    cout << "c Disjoint Phase\n";

  double beginTime = cpuTime();
  //at this stage the greedy solver has input and learnt cores of the
  //theory via seeding. We don't want disjoint to rediscover these,
  //initialize the assumed true softs with a greedy_solution.
  //As added effect, if the greedy solver respect the mutex constraints
  //then disjointPhase will always use assumptions repecting the mutexes.
  auto greedy_solution = greedySoln();
  assumps.init(greedy_solution, CoreType::cores);
  if(params.sort_assumps == 1)
    assumps.sort(blit_gt);
  else if(params.sort_assumps == 2)
    assumps.sort(blit_lt);

  vector<Lit> conflict;
  lbool val;
  while((val = satsolve_min(assumps, conflict, params.dsjnt_cpu_per_core, params.dsjnt_mus_cpu_lim))
         == l_False) {
    if(params.verbosity > 1) {
      cout << "c Disjoint Conflict size = " << conflict.size() << "\n";
      if(params.verbosity > 2)
        cout << "c conflict = " << conflict << "\n";
    }
    store_cplex_greedy_cls(conflict);
    //Must remove assumptions now that we are adding forced negated bvars
    assumps.update(conflict, true);
    num++;
    len += conflict.size();
    Weight min_wt {0};
    for(auto b : conflict)
      if(min_wt == 0 || bvars.wt(b) < min_wt)
        min_wt = bvars.wt(b);
    lb_weight += min_wt;
  }

  //update Bounds (only UB could have changed)
  if(val == l_True) {
    if(params.improve_model)
      improveModel();
    updateUB();
  }
  updateLB(lb_weight);

  if (params.verbosity > 0) {
    cout << "c Dsjnt: #Cores " << num << " with total weight " << lb_weight << "\n";
    if(num > 0) {
      cout << "c Dsjnt: Avg Core Size " <<  len/((double) num) << "\n";
    cout << "c Dsjnt: Time " << cpuTime() - beginTime << "\n";
    }
  }
}

void MaxSolver::seqOfSAT_maxsat() {
  vector<Lit> cplexsoln;
  vector<Lit> conflict;
  Assumps assumps(satsolver, bvars);
  int iteration {0};
  Weight prev_cplex_solution_obj {0};
  Weight cplex_UB {0};
  bool cplex_found_optimum {false};
  auto n_conf = cplexClauses.size();
  bool first_time {true};

  while (1) {
    //1. Update cplex model
    if (params.verbosity > 0)
      cout << "c **********Iter: " << iteration++ << " Elapsed Time = "
           << cpuTime() - globalStartTime << "\n";

    cplexAddNewForcedBvars();
    cplexAddNewClauses();

    //1.5
    if(!allClausesSeeded && params.lp_harden)
      if(tryHarden()) {
        optFound("c UB proved optimal by LP-Bound");
        return;
      }

    if(first_time && allClausesSeeded) {
      //note any improved ub model will be passed to cplex as a mip start
      auto val = get_greedy_conflicts();
      if(val) {
        optFound("c solved by initial greedy solve");
        return;
      }
      //don't want these clauses feed to cplex.
      //if cplex already has full model.
      cplexClauses.clear();
    }
    first_time=false;

    //2. Solve CPLEX model and update Bounds
    if(cplex_found_optimum || prev_cplex_solution_obj == 0)
      cplex_UB = UB();
    else
      cplex_UB = fmin(prev_cplex_solution_obj, UB());

    Weight cplexLB = cplex->solve(cplexsoln, cplex_UB); //cplexLB is LB
    if (cplexLB < 0) {
      printErrorAndExit("c ERROR: Cplex::solve() failed");
    }
    auto cplexSolnWt = getWtOfBvars(cplexsoln); //solution cost is UB
    reportCplex(cplexLB, cplexSolnWt);

    cplex_found_optimum = (fabs(cplexSolnWt - cplexLB) <= absGap);
    if(params.verbosity > 0) {
      cout << "c CPLEX solution cost = " << cplexSolnWt << " lower bound = " << cplexLB << "\n";
      if(cplex_found_optimum)
        cout << "c CPLEX found optimal solution to its current model\n";
    }
    prev_cplex_solution_obj = cplexSolnWt;

    if(cplexLB > LB())
      updateLB(cplexLB);

    if(params.verbosity >0)
      cout << "c after CPLEX bnds: LB = " << LB() << " UB = " << UB() << "\n";
    if(haveUBModel)
      if(fabs(UB()-LB()) <= absGap) {
        optFound("c Solved by LB >= UB");
        return;
      }

    //3. Generate conflicts from solution or from abstracted solution or both
    //    Abstracted solution:  The
    //    CPLEX solution specifies a setting (satisfied/falsified) for
    //    each soft clause via a setting for the soft clause's
    //    corresponding b-var. An abstract solution does not specify
    //    the setting of all soft clauses. The property we need
    //    is that the abstract setting places the same constraint
    //    on the weight of any solution as the non-abstract solution.
    //    If our solution specifies that k-1 soft clauses in a core mx
    //    are satisfied, then we can remove that condition, as we know that
    //    it must always be the case that at least  k-1 of these softs must be satisfied.
    //    If our solution specifies that k-1 soft clauses in a non-core mx must be
    //    be false, then we can remove that condition, as we know that it must
    //    always be the case that at least k-1 of these softs must be falsified.

    bool found_abstracted_solution {false};
    if(params.mx_hs_use_abstraction && theWcnf->n_mxes()) {
      vector<int> mxes_in_soln (theWcnf->n_mxes(), 0);
      for(auto b : cplexsoln)
        if((bvars.inCoreMx(b) && bvars.isNonCore(b))
           || (bvars.inNonCoreMx(b) && bvars.isCore(b)))
          mxes_in_soln[bvars.getMxNum(b)]++;

      vector<char> mxes_to_remove (theWcnf->n_mxes(), false);
      for(size_t i=0; i < mxes_in_soln.size(); i++)
        if(mxes_in_soln[i] == theWcnf->ith_mx_size(i)-1) {
          mxes_to_remove[i] = true;
          found_abstracted_solution = true;
        }

      if(found_abstracted_solution) {
        auto mx_remove = [&mxes_to_remove, this] (Lit b) {
          return
          ((bvars.inCoreMx(b) && bvars.isNonCore(b) && mxes_to_remove[bvars.getMxNum(b)])
           ||(bvars.inNonCoreMx(b) && bvars.isCore(b) && mxes_to_remove[bvars.getMxNum(b)]));
        };

        auto abscplexsoln = cplexsoln; //keep original
        auto p = std::remove_if(abscplexsoln.begin(), abscplexsoln.end(), mx_remove);
        abscplexsoln.erase(p, abscplexsoln.end());
        if(params.verbosity)
          cout << "c CPLEX abstract solution reduced by " << cplexsoln.size() - abscplexsoln.size()
               << " lits\n";
        n_conf = cplexClauses.size();
        if(get_conflicts(abscplexsoln, false)) {
          optFound("c Solved by abstract CPLEX model");
          return;
        }
        if(params.verbosity)
          cout << "c CPLEX abstract solution yielded " << cplexClauses.size()-n_conf << " conflicts\n";
      }
    }
    if(!found_abstracted_solution || params.mx_hs_use_abstraction > 1) {
      n_conf = cplexClauses.size();
      if(get_conflicts(cplexsoln, false)) {
        optFound("c Solved by CPLEX model");
        return;
      }
      if(params.verbosity > 0)
        cout << "c CPLEX solution yielded " << cplexClauses.size()-n_conf << " conflicts\n";
    }
    bool cplex_solution_was_unsat = !cplexClauses.empty();

    //4. Generate conflicts from greedy solutions.
    n_conf = cplexClauses.size();
    if(cplex_solution_was_unsat && get_greedy_conflicts()) {
      optFound("c Solved by greedy model");
      return;
    }
    if(params.verbosity > 0)
      cout << "c Greedy yielded " << cplexClauses.size()-n_conf << " conflicts\n";

    //5. if needed find some more conflicts by extracting other solutions from cplex
    n_conf = cplexClauses.size();
    if(cplex_solution_was_unsat &&
       (params.trypop > 1 || (params.trypop > 0 && cplexClauses.size() < 35))) {
      double gap = fabs(UB()-cplexSolnWt);
      //want better solutions than UB
      if(theWcnf->integerWts())
        gap -= 1.0;
      else
        gap -= absGap;
      if(gap <= absGap)
        gap = 0.0;

      int nsolns = cplex->populate(params.cplex_pop_cpu_lim, gap);
      if(params.verbosity > 1)
        cout << "c populate found " << nsolns << " solutions\n";
      for(int i=0; i < nsolns; i++) {
        cplex->getPopulatedSolution(i, cplexsoln);
        if(cplexsoln.size() == 0) {
          cout << "c WARNING Cplex populate could not find solution " << i << "\n";
          continue;
        }
        if(params.verbosity > 1)
          cout << "c getting conflicts from solution #" << i << "\n";
        if(get_conflicts(cplexsoln, true)) {
          optFound("c Solved by populated model");
          return;
        }
        //5.5 if the populated solution has cost <= cplex solution wt
        //the keep track of its set of true blits...we need not try to
        //harden these blits.
        /*if(getWtOfBvars(cplexsoln) <= cplexSolnWt) {
          for(auto l : cplexsoln)
          if(bvars.isCore(l))
          cannot_exceed_bounds[bvars.clsIndex(l)] = 1;
          }*/
      }
    }
    if(params.verbosity > 0)
      cout << "c populate found " << cplexClauses.size() - n_conf << " conflicts\n";

    //6. if necessary and possible get conflicts from new UB
    n_conf = cplexClauses.size();

    /*cout << "have_new_UB_model = " << have_new_UB_model << " UB() = " << UB()
      << " conflicts_from_ub = " << params.conflicts_from_ub
      << " fabs(UB() - LB()) = " <<  fabs(UB() - LB())
      << " cplexClauses.size() = "  << cplexClauses.size() << "\n";*/

    if(have_new_UB_model && params.conflicts_from_ub > 0)
      if(params.conflicts_from_ub > 1
         || fabs(UB() - LB()) <= 3*theWcnf->minSftWt()
         || cplexClauses.size() < 35) {
        if(params.verbosity > 0)
          cout << "c trying UB conflicts\n";
        if(get_ub_conflicts()) {
          optFound("c Solved by conflicts from UB model\n");
          return;
        }
      }
    if(params.verbosity > 0)
      cout << "c ub-conflicts found " << cplexClauses.size() - n_conf << " conflicts\n";
  }
}

bool MaxSolver::tryHarden() {
  //Try to harden some of the soft clauses
  vector<Weight> lp_solvals;
  vector<Weight> lp_redvals;
  int hardened_count {n_softs_forced_hard};
  int relaxed_count {n_softs_forced_relaxed};
  int hardened_count_not_in_cplex {n_softs_forced_hard_not_in_cplex};
  bool some_forced {false};

  auto lp_objval = cplex->solve_lp_relaxation(lp_solvals, lp_redvals);
  if(lp_objval <=  0)
    return false;

  updateLB(lp_objval);
  if(fabs(UB() - LB()) <= absGap)
    return true;
  if(lp_objval + bvars.maxWt() + 0.01 < UB())
    return false;

  for(size_t i = 0; i < bvars.n_bvars(); i++) {
    auto blit = bvars.litOfCls(i);
    if(satsolver->curVal(blit) != l_Undef) {
      continue;
    }
    if(lp_redvals[i] > 0) {
      //var should be at its lower bound
      if(lp_redvals[i] + lp_objval > UB() + 0.01
         || (fabs(lp_redvals[i] + lp_objval - UB()) < 0.001 && UBmodelSofts[i] == l_True)) {
        //Lp is subject to rounding error. Greater than UB if gt by at least 0.01
        //equal to UB if within 0.001
        //
        //if we make blit true we must incur cost >= UB. If cost >
        //UB force it false. If cost == UB and blit is false in UB
        //model (the corresponding soft is true in the UB model)
        //we can also force it false---no need to consider models
        //with it true as they can't be better than the UB model.
        satsolver->addClause({~blit});
        n_softs_forced_hard++;
        if(!cplex->lit_in_cplex(blit))
          n_softs_forced_hard_not_in_cplex++;
        some_forced = true;
      }
    }
    else if(lp_redvals[i] < 0) {
      //var should be at its upper bound
      if(lp_objval - lp_redvals[i] > UB() + 0.01
         || (fabs(lp_objval - lp_redvals[i] - UB()) < 0.001 && UBmodelSofts[i] == l_False)) {
        //|| (lp_objval - lp_redvals[i] == UB() && UBmodelSofts[i] == l_False)) {
        satsolver->addClause({blit});
        n_softs_forced_relaxed++;
        some_forced = true;
      }
    }
  }

  if(some_forced) {
    cout << "c tryharden: hardened              "
         << n_softs_forced_hard - hardened_count << "\n"
         << "c tryharden: relaxed               "
         << n_softs_forced_relaxed - relaxed_count << "\n"
         << "c tryharden: hardened not in model "
         << n_softs_forced_hard_not_in_cplex - hardened_count_not_in_cplex << "\n";
    cplexAddNewForcedBvars();
  }

  /*cout << "blit " << blit;
    if(lp_solvals[i] > 0)
    cout << " weight = " << bvars.wt(blit);
    cout << " LP solval = " << lp_solvals[i]
    << " LP redval = " << lp_redvals[i];
    if(lp_redvals[i] + lp_objval > UB())
    cout << "CAN BE FORCED";
    cout << "\n";*/

  return false;
}

bool MaxSolver::get_conflicts(const vector<Lit>& cplexSoln, bool check_if_blocked) {
  //Input cplex solution and number of conflicts accumulated since CPLEX called.
  //Return true if we found an optimal solution.
  //I.e., one with cost equal to LB() that is SAT.  If not optimal
  //solution but is SAT update upper bound If UNSAT generate some
  //conflicts to criticize this cplex solution.  But check first to
  //ensure that we don't have a conflict already criticizing this
  //solution.

  if(params.verbosity > 1)
    cout << "c get_conflict processing solution of cost " << getWtOfBvars(cplexSoln) << "\n";

  //1. Check if already blocked by previous conflict.
  if(!cplexClauses.empty() && check_if_blocked) {
    vector<Lit> solnMap(bvars.n_bvars(), lit_Undef);
    for(auto a : cplexSoln)
      solnMap[bvars.clsIndex(a)] = a;

    bool isBlocked;
    for(auto con: cplexClauses) {
      isBlocked = true;
      for(auto a: con)
        if(solnMap[bvars.clsIndex(a)] == a) {
          //passed solution satisfies this conflict clause
          isBlocked = false;
          break;
        }
      if(isBlocked) {
        if(params.verbosity > 1)
          cout << "c    get_conflict conflict is already blocked\n";
        return false;
      }
    }
  }

  //Not Blocked, get conflicts from this solution
  auto n_conf = get_seq_of_conflicts(cplexSoln, params.noLimit, params.optcores_cpu_per);
  if(params.verbosity > 1)
    cout << "c Solution yielded " << n_conf << " new conflicts\n";
  if(fabs(UB()-LB()) < absGap) {
    return true;
  }
  else
    return false;
}

bool MaxSolver::get_ub_conflicts() {
  //try reducing UB model---should be a new UB model
  //generate conflicts from each reduction (or improve UB!)
  double start_time = cpuTime();
  if(params.verbosity > 0)
    cout << "c Finding conflicts from UB\n";
  vector<Lit> ub_false; //store true b-lits == set of falsified clauses in UB-model
  vector<Lit> ub_true;  //store false b-lits == set of true clauses in UB-model
  Assumps assumps(satsolver, bvars);
  auto n_conf = cplexClauses.size();
  vector<Lit> conflict;
  vector<char> ub_true_has_ncore_mx;
  vector<int> ncore_mxes_in_ub_true (theWcnf->n_mxes(), false);

  //UBmodel does not store the bvars---so we have to retrieve them from UBmodelSofts
  //which unfortunately has a reversed logic to the bvars---soft clause i is l_True
  //means that the bvar of this clause is l_False.
  for(size_t i=0; i < UBmodelSofts.size(); i++)
    if(UBmodelSofts[i] == l_False) {
      //this soft is falsified but not forced. (If forced
      //it is pointless to try to satisfy it).
      if(satsolver->curVal(bvars.litOfCls(i)) == l_Undef)
        ub_false.push_back(bvars.litOfCls(i));
    }
    else if(satsolver->curVal(bvars.litOfCls(i)) == l_Undef) {
      ub_true.push_back(~bvars.litOfCls(i));
      if(bvars.inNonCoreMx(ub_true.back())) {
        if(ub_true_has_ncore_mx[bvars.getMxNum(ub_true.back())])
          cout << "c ERROR get_ub_conflicts UB model makes more than one non-core mx true\n";
        ub_true_has_ncore_mx[bvars.getMxNum(ub_true.back())] = true;
      }
    }

  auto respects_mx_constraints = [&ub_true_has_ncore_mx, this](Lit b) {
    return !bvars.inNonCoreMx(b) || !ub_true_has_ncore_mx[bvars.getMxNum(b)];
  };

  //try to make false soft clauses true in order of their weight (process from the back)
  auto wtLt = [this](const Lit bx, const Lit by) { return bvars.wt(bx) < bvars.wt(by); };
  std::sort(ub_false.begin(), ub_false.end(), wtLt);

  if(params.verbosity > 0)
    cout << "c UB has " << ub_true.size() << " true softs (false blits) and "
         << ub_false.size() << " unforced false softs (true blits)\n";

  while(!ub_false.empty()) {
    //try to make one more soft clause true in UB-model.
    /*cout << "c UB has " << ub_true.size() << " true softs (false blits) and "
      << ub_false.size() << " unforced false softs (true blits)\n";*

      cout << "at top of loop ub_false = " << ub_false;*/

    if(satsolver->curVal(ub_false.back()) == l_Undef &&
       (!params.mx_constrain_hs || respects_mx_constraints(ub_false.back()))) {
      ub_true.push_back(~ub_false.back());
      ub_false.pop_back();
    }
    else {
      ub_false.pop_back();
      continue;
    }

    auto isforced = [this](Lit j) { return satsolver->curVal(j) != l_Undef; };
    auto p = std::remove_if(ub_true.begin(), ub_true.end(), isforced);
    ub_true.erase(p, ub_true.end());

    /*for(size_t i = 0; i < ub_true.size(); i++)
      if(satsolver->curVal(ub_true[i]) == l_False)
      cout << "Problem with ub_true " << ub_true[i] << " is already false index = " << i << "\n";*/

    assumps.init(ub_true, params.coreType);
    auto val = satsolve_min(assumps, conflict, params.optcores_cpu_per, params.mus_cpu_lim);
    if(val == l_True) {
      if(params.verbosity > 0)
        cout << "c get_ub_conflicts found SAT==better UB\n";
      if(params.improve_model)
        improveModel();
      auto w = updateUB();
      if(params.verbosity > 1)
        cout << "c New SAT solution found by UB_CONFLICTS cost = " << w << "\n";
      if(fabs(UB() - LB()) <= absGap)
        break;
      size_t cur_size = 0;
      for(size_t examine = 0; examine < ub_false.size(); examine++) {
        //remove from set of true blits all newly falsified blits (i.e., corresponding soft is true
        //in new UB model) and all newly forced false blits (no need to test these)
        auto blit = ub_false[examine];
        if(UBmodelSofts[bvars.clsIndex(blit)] == l_True)
          //this false soft is now true.
          ub_true.push_back(~blit);
        else if(satsolver->curVal(blit) != l_True)
          ub_false[cur_size++] = ub_false[examine];
      }
      ub_false.resize(cur_size);
      if(params.verbosity>1)
        cout << "c UB has " << ub_true.size() << " true softs (false blits) and "
             << ub_false.size() << " unforced false softs (true blits)\n";
    }
    else {
      if (val == l_False)
        store_cplex_greedy_cls(conflict);
      ub_true.pop_back();
    }
    if(cpuTime() - start_time > params.max_cpu_before_cplex)
      //this should be fixed...it doesn't account for time spent in greedy and populate.
      break;
  }
  if(params.verbosity >0)
    cout << "c get_ub_conflicts found " << cplexClauses.size() - n_conf << " new conflicts\n";
  have_new_UB_model = false;

  if(fabs(UB() - LB()) <= absGap)
    return true;
  return false;
}

bool MaxSolver::get_greedy_conflicts() {
  //accumulate more conflicts for CPLEX by criticizing sequence of greedy solutions.
  double start_time = cpuTime();
  int iter {0};
  while(1) {
    if(cplexClauses.size() > static_cast<size_t>(params.max_cores_before_cplex)
       || cpuTime() - start_time > params.max_cpu_before_cplex)
      return false;

    if(params.verbosity > 0)
      cout << "c Greedy Solution # " << iter << "\n";
    auto greedy_solution = greedySoln();
    auto n_conf = get_seq_of_conflicts(greedy_solution, params.optcores_cpu_per, params.optcores_cpu_per);
    if(fabs(UB() - LB()) <= absGap)
      return true;
    if(params.verbosity > 0)
      cout << "c Greedy Solution yielded " << n_conf << " conflicts\n";
    if(!n_conf)
      return false;
    iter++;
  }
}

int MaxSolver::get_seq_of_conflicts(const vector<Lit>& solution, double first_core_cpu_lim, double other_cores_cpu_lim) {
  //Just found a candidate solution (via cplex or greedy or...)
  //check if the solution satisfies whole theory, and if not generate sequence
  //of conflicts from it. Return number of conflicts found.
  Assumps assumps(satsolver, bvars);
  assumps.init(solution, params.coreType);
  vector<Lit> conflict;
  int n_conf {0};

  while(1) {
    auto val = satsolve_min(assumps, conflict, (n_conf ? other_cores_cpu_lim: first_core_cpu_lim), params.mus_cpu_lim);
    if(val == l_True) {
      if(params.improve_model)
        improveModel();
      auto w = updateUB();
      if(params.verbosity > 1)
        cout << "c New SAT solution found (get_seq_of_conflicts), cost = " << w << "\n";
      return n_conf;
    }
    else if (val == l_False) {
      n_conf++;
      store_cplex_greedy_cls(conflict);
      assumps.update(conflict, true);
    }
    else
      //timed out
      return n_conf;
  }
}

int MaxSolver::feedCplex(int gIter, Assumps& assumps,
                         int nSoFar, size_t sizeSoFar) {
  //accumulate some conflicts for CPLEX. Return number found.
  //Pre: Assumps is not know to be SAT.
  //     last two parameters are for collecting statistics only.

  vector<Lit> conflict;
  int iter {1}; //On call we already found one constraint for CPLEX
  int nCon {nSoFar};
  int nSinceGreedy {1}; //Count CPLEX as a greedy call
  int64_t totalCnfSize { static_cast<int64_t>(sizeSoFar) };

  double start_time = cpuTime();
  while(1) {
    iter++;
    if(iter > params.max_cores_before_cplex
       || cpuTime() - start_time > params.max_cpu_before_cplex)
      return nCon;

    lbool val = satsolve_min(assumps, conflict, params.optcores_cpu_per, params.mus_cpu_lim);
    if(val == l_True) {
      if(params.improve_model)
        improveModel();
      Weight w = updateUB();
      if(params.verbosity > 0) {
        cout << "c New SAT solution found, cost = " << w
             << " UB =" << UB() << " LB = " << LB() << "\n";
      }

      if(fabs(UB()-LB()) <= absGap) {
        optFound("c Solved by Sat Solution equal to LB");
        return nCon;
      }
      else if(nSinceGreedy == 0) //greedy solution was solvable. No
        return nCon;         //more clauses to feed to cplex

      else { //start with new set of assumptions
        auto tmp = greedySoln();
        assumps.init(tmp, params.coreType);
        if(params.sort_assumps == 1)
          assumps.sort(blit_gt);
        else if(params.sort_assumps == 2)
          assumps.sort(blit_lt);

        if(params.verbosity > 3) {
          cout << "Greedy Solution: " << tmp << "\n";
          cout << "Assumps after Greedy Solution" << assumps.vec() << "\n";
        }
        nSinceGreedy = 0;
      }
    }
    else if(val == l_False) {
      nCon++;
      nSinceGreedy++;
      totalCnfSize += conflict.size();
      store_cplex_greedy_cls(conflict);

      if (params.verbosity > 1
          || (params.verbosity > 0  && (iter % 50) == 0))
        cout << "c FeedCplex: " << gIter << "." << iter
             << " (#cons = " << nCon << " ave size = "
             << totalCnfSize/nCon << ").\n";

      auto tmp = getAssumpUpdates(nCon, conflict);
      //Must remove assumptions now that we are adding forced negated bvars
      //assumps.update(tmp, params.fbeq);
      assumps.update(tmp, true);

      if(params.verbosity > 2) {
        cout << "c FeedCplex conflict: " << conflict << "\n";
        cout << "c FeedCplex Conflict updates: " << tmp << "\n";
        if(params.verbosity > 3)
          cout << "c FeedCplex Updated Assumps: " << assumps.vec() << "\n";
      }
    }
    else { //timed out
      if(params.verbosity > 0)
        cout << "c feedCplex finding new core timedout\n";
      return nCon;
    }
  }
}


//This routine must be called right after an optimal cplex solution is
//computed.  We know that that solution satisfies all current cores
//(and non-cores).  A cplex solution is a complete setting of Bvars:
//i.e., it is a model.  If each of the new solutions in the pool are
//optimal, then all of them also satisfy all prior cores.

//We can stop any redundant cores from being generated by making sure
//that every solution we examine satisfies all new conflicts
//generated.  On entry we have one new conflict C0---the conflict that
//refutes the original optimal CPLEX solution. So we can discard a
//solution from the pool S0 if it fails to satisfy C0---C0 will block S0
//as well.  Otherwise we can refute S0---or if S0 is optimal and
//satisfiable we can declare S to be a maxsat solution.

//In refuting S0 we obtain another conflict C1. Now for the next
//solution from the pool S1, we should really check that S1 is not
//blocked by either C0 or C1. Similary for Sk from the solution pool
//we should check that it is not blocked by all prior conflicts
//generated in this routine.

//We preform this test as cplex often generated multiple copies of the
//same solution in the solution pool.

void MaxSolver::tryPopulate(vector<Lit>& conflict, double cplexOptSolnWt) {
  //Got conflict for first cplex solution. Try populate and see if we can't
  //get some more conflicts. Return the last one to initiate greedy feeding
  //of cplex.

  //Allow for non-optimal solution in solution pool. But
  //if solution is optimal (equal to the passed optimal solution weight
  //computed from an optimal solve) we can use it to declare that
  //a solution has been found.
  if(params.verbosity > 0)
    cout << "c Trying populate\n";
  int nsolns = cplex->populate(params.cplex_pop_cpu_lim);
  vector<Lit> cplexsoln;
  vector<vector<Lit>> foundConflicts;
  vector<Lit> newConflict;
  vector<Lit> solnMap(bvars.n_bvars(), lit_Undef);
  int nadded = 0;
  int nOpt = 0;
  int nOptAdded = 0;

  foundConflicts.push_back(std::move(conflict)); //empties conflict must restore.

  for(int i = 0; i < nsolns; i++) {
    cplex->getPopulatedSolution(i, cplexsoln);
    if(cplexsoln.size() == 0) {
      cout << "c WARNING Cplex populate could not find solution " << i << "\n";
      continue;
    }
    auto solnwt = getWtOfBvars(cplexsoln);
    bool isOpt = (solnwt == cplexOptSolnWt);
    if(isOpt)
      ++nOpt;

    for(auto l : cplexsoln)
      solnMap[bvars.clsIndex(l)] = l;
    bool isBlocked=false;
    for(auto con: foundConflicts) {
      isBlocked = true;
      for(auto l: con)
        if(solnMap[bvars.clsIndex(l)] == l)
          isBlocked = false;
      if(isBlocked) break;
    }
    if(!isBlocked) { //can obtain new conflict from this solution
      ++nadded;
      if(isOpt) ++nOptAdded;
      //Assumps assumps(satsolver, bvars, inMx);
      Assumps assumps(satsolver, bvars);
      assumps.init(cplexsoln, params.coreType);
      if(params.sort_assumps == 1)
        assumps.sort(blit_gt);
      else if(params.sort_assumps == 2)
        assumps.sort(blit_lt);
      if(satsolve_min(assumps, newConflict, params.noLimit, params.mus_cpu_lim) == l_True) {
        updateUB();
        if(isOpt) {
          optFound("c Solved by one of Cplex populated models");
          return;
        }
        else
          cout << "c Non optimal CPLEX populated model was SAT\n";
      }
      else {
        store_cplex_greedy_cls(newConflict);
        foundConflicts.push_back(std::move(newConflict));
      }
    }
  }
  if(params.verbosity>0)
    cout << "c populate added " << nadded << " conflicts\n";

  conflict = std::move(foundConflicts[0]);
}

vector<Lit> MaxSolver::getAssumpUpdates(int nSinceCplex, vector<Lit>& core) {
  //return a subset of the core to update assumptions. Core should be
  //a conflict returned by trying to see if assumptions are
  //satisfiable...so it will contain only negations of the assumption
  //literals. Uses core for computation---modifies it!
  assert(!(params.coreType == CoreType::cores) || vec_isCore(core));

  switch(params.coreRelaxFn) {
  case CoreRelaxFn::maxoccur:
    return vector<Lit> { maxOccurring(core) };
  case CoreRelaxFn::frac:
    return fracOfCore(nSinceCplex, core);
  case CoreRelaxFn::dsjn:
    return core;
  default:
    return vector<Lit> { core[0] };
  }
}

vector<Lit> MaxSolver::fracOfCore(int nSinceCplex, vector<Lit> &core) {
  double fracToReturn = params.frac_to_relax;
  int nToReturn {1};
  if(nSinceCplex > params.frac_rampup_start) {
    if(nSinceCplex < params.frac_rampup_end)
      fracToReturn *= (nSinceCplex - params.frac_rampup_start)/(1.0 * (params.frac_rampup_end - params.frac_rampup_start));
    nToReturn = ceil(fracToReturn*((double) core.size()));
  }
  if(nToReturn == 1)
    return vector<Lit> { maxOccurring(core) };

  //auto maxOccur = [this](Lit l1, Lit l2) { return bLitOccur[bvars.toIndex(l1)] < bLitOccur[bvars.toIndex(l2)]; };
  //use a heap here instead of fully sorting the vector.
  //std::make_heap(core.begin(), core.end(), maxOccur);
  std::make_heap(core.begin(), core.end(), blit_lt);

  vector<Lit> retVec;
  for (int i = 0; i < nToReturn; i++) {
    retVec.push_back(core.front());
    //std::pop_heap(core.begin(), core.end()-i, maxOccur);
    std::pop_heap(core.begin(), core.end()-i, blit_lt);
  }
  if(params.verbosity > 1)
    cout << "c fracOfCore returns a relaxation of size " << retVec.size() << "\n";
  return retVec;
}

Lit MaxSolver::maxOccurring(const vector<Lit>& core) {
  //return literal of core that appears in largest number of accumulated CPLEX clauses
  Lit max = core[0];
  for(auto l : core)
    //if(bLitOccur[bvars.toIndex(l)] > bLitOccur[bvars.toIndex(max)])
    //
    if(blit_gt(l, max)) //Note blit_lt(max, l) is not same as blit_gt(l, max)
      max = l;
  return max;
}


void MaxSolver::incrBLitOccurrences(const vector<Lit> &core) {
  //all lits in core should be bvars!
  for (auto l : core)
    bLitOccur[bvars.toIndex(l)] += 1;
}


//TODO: Consider unifying the add clause/add new forced bvar
//      across all solvers (including CPLEX).
//      Perhaps a solver class that CPLEX and SAT derive from.
//
bool MaxSolver::cplexAddCls(vector<Lit>&& cls) {
  bool isNonCore = cplex->add_clausal_constraint(cls);
  if(params.verbosity > 2) {
    cout << "c Added clause to Cplex:\n";
    outputConflict(cls);
  }
  return isNonCore;
}

//TODO Better abstraction to facilitate sharing of unit or other clauses between solvers.
//
void MaxSolver::cplexAddNewForcedBvars() {
  cplexNU.update(satsolver);
  vector<Lit>& forced = cplexNU.forced;
  int nf {0};
  for(auto l : forced)
    if(bvars.isBvar(l) || cplex->lit_in_cplex(l)) {
      nf++;
      cplexAddCls({l});
    }
  if (params.verbosity > 0 && nf > 0)
      cout << "c Add to CPLEX " << nf << " Forced bvars.\n";
}

void MaxSolver::greedyAddNewForcedBvars() {
  //We pass only forced b-vars to the greedy solver
  greedyNU.update(satsolver);
  vector<Lit>& forced = greedyNU.forced;
  int nf {0};
  for(auto l : forced)
    if(bvars.isBvar(l)) {
      nf++;
      greedysolver->addClause({l});
    }
  if (params.verbosity > 0 && nf > 0)
      cout << "c Add to greedysolver " << nf << " Forced bvars.\n";
}

void MaxSolver::muserAddNewForcedVars() {
  //We pass on ordinary variables and b-variables to the muser.
  //Note the sat solver might have addition control variables that
  //have been forced on its trail e.g., eqCVar. These should not be
  //sent to the muser.

  muserNU.update(satsolver);
  vector<Lit>& forced = muserNU.forced;

  if(params.verbosity > 2)
    cout << "Adding forced units to MUSER " << forced << "\n";

  int nf {0};
  for(auto l : forced)
    //Note muser might not know about l, but we inform it of l and its value
    //in case later on the muser has to deal with clauses involving l.
    //don't add forced control variables
    if(muser->curVal(l) == l_Undef) {
      nf++;
      if(!muser->addClause({l}))
        cout << "c ERROR: Adding unit to MUSER " << l << " current value "
             << muser->curVal(l) << " Caused UNSAT\n";
    }
  if (params.verbosity > 0 && nf > 0)
      cout << "c Add to muser " << nf << " newly forced vars.\n";
}

void MaxSolver::satSolverAddNewForcedVars() {
  //We pass on ordinary variables and b-variables from the muser to the sat solver.
  //muser control variables are ignored (They shouldn't be any that get through
  //the getForced interface in any event).

  satNU.update(muser);
  vector<Lit>& forced = satNU.forced;

  if(params.verbosity > 2)
    cout << "Adding forced units to satsolver " << forced << "\n";

  int nf {0};
  for(auto l : forced)
    if(satsolver->curVal(l) == l_Undef) {
      nf++;
      satsolver->addClause({l});
    }
  if (params.verbosity > 0 && nf > 0)
    cout << "c Add to satSolver " << nf << " newly forced from muser.\n";
}

void MaxSolver::satSolverAddBvarsFromSofts() {
  //If we are using only the Fb theory, when a soft is satisfied by forced literals
  //the corresponding b-variable will not be set. Use this routine to add these forced
  //b-variables to the sat solver. (This allows the sat solver to delete these softs
  //And also to pass the forced b-vars to CPLEX, the muser and the greedy solver
  //perhaps helping them as well.) Note we can only process ordinary variables
  //from the sat solver.

  satBvarNU.update(satsolver);
  vector<Lit>& forced = satBvarNU.forced;

  /*static int notSeen {0};
    vector<Lit> forced { satsolver->getForced(notSeen) }; //Get unprocessed forced
    notSeen += forced.size();*/

  if(params.verbosity > 2)
    cout << "Processing new forced units for adding satisfied softs to satsolver " << forced << "\n";

  int nf {0};
  for(auto l : forced)
    if(bvars.isOvar(l)) {
      for(auto sftIdx : sftSatisfied[toInt(l)]) {
        Lit blit = bvars.litOfCls(sftIdx);
        if(satsolver->curVal(blit) == l_Undef) {
          ++nf;
          satsolver->addClause({~blit});
          //debug
          //cout << "Adding forced negated blit to satsolver " << ~blit << "\n";
        }
      }
    }
  if(params.verbosity > 0 && nf > 0)
    cout << "c Add to satsolver " << nf << " forced negated bvars.\n";
}

void MaxSolver::cplexAddNewClauses() {
  if (params.verbosity > 0) {
    double totalLits = cplexClauses.total_size();
    cout << "c CPLEX: += " << cplexClauses.size() << " Clauses. Average size ="
         << totalLits/cplexClauses.size() << "\n";
  }
  for(size_t i = 0; i < cplexClauses.size(); i++)
    cplexAddCls(cplexClauses.getVec(i));
  cplexClauses.clear();
}

void MaxSolver::greedyAddNewClauses() {
  if (params.verbosity > 0) {
    double totalLits = greedyClauses.total_size();
    cout << "c GREEDY: += " << greedyClauses.size() << " Clauses. Average size ="
         << totalLits/greedyClauses.size() << "\n";
  }
  for(size_t i = 0; i < greedyClauses.size(); i++)
    greedysolver->addClause(greedyClauses.getVec(i));
 greedyClauses.clear();
}

void MaxSolver::processMutexes() {
  auto& mxs = theWcnf->get_SCMxs();
  /*For each mutex.
    (a) if mutex was transformed and cplex was seeded with some of the
        mx lits, then encode to clplex the relation between the mx
        encoding lit and the mx lits.
        Note1. the greedy solver does not get any such clauses, it
               only gets b-lit cores)
        Note2. cplex will be seeded with some mx lits only if we
               have params.mx_seed_originals

    (b) Otherwise there is no encoding lit so the mx is over blits.
        If params.mx_constrain_hs is true we inform cplex and the greedy
        solver of the mx over these blits
  */

  vector<int> in_cplex (bvars.maxvar()+1, 0);
  for(auto cls : cplexClauses) //not yet feed into cplex
    for(auto l : cls) 
      in_cplex[var(l)] = 1;
    for(size_t i=0; i < in_cplex.size(); i++) //already in cplex
    if(cplex->var_in_cplex(i))
      in_cplex[i] = 1;

  for(auto& mx : mxs) {
    if(mx.encoding_lit() != lit_Undef) {
      bool mx_lits_in_cplex {false};
      for(auto l : mx.soft_clause_lits())
        mx_lits_in_cplex |= in_cplex[var(l)];
      if(mx_lits_in_cplex)
        cplex->add_mutex_constraint(mx);
    }
    else if(params.mx_constrain_hs) {
      cplex->add_mutex_constraint(mx);
      greedysolver->addMutexConstraint(mx);
    }
  }
}

void MaxSolver::seed_equivalence() {
  /*find clauses that can be feed into CPLEX.

    If number of vars < params.seed_all_limit give CPLEX all clauses.
    Otherwise seed clauses that are composed solely of bvars. However,
    do not seed any clauses that are subsumed by mutexes as the mutex
    constraints will already be feed to cplex in a different form.

    If we find some core constraints, then these might also be found
    by the disjoint phase. To prevent the disjoint phase from finding
    redundant cores, we identify a maximal disjoint set of found cores
    and return the union of their bvars. Every core found here will
    have a non-empty intersection with this set. By blocking the
    disjoint phase from finding cores including these variables we
    ensure that it will find only new cores in that phase. */

  /*TODO this is way too complicated---should be simplified*/

  vector<vector<vector<Lit>>> cplex_cores (2);
  vector<vector<vector<Lit>>> cplex_ncores (2);
  vector<vector<vector<Lit>>> cplex_mixed (2);
  vector<vector<vector<Lit>>> cplex_ordinary (2);

  bool is_core, is_ncore, is_mixed;
  bool seed_all { params.seed_all_limit >= theWcnf->dimacsNvars() };
  allClausesSeeded = true;

  for(size_t isLearnt=0; isLearnt < (params.seed_learnts ? 2 : 1); isLearnt++) {
    for(int i =0; i < satsolver->getNClauses(isLearnt); i++) {
      auto seedingCls = satsolver->getIthClause(i, isLearnt);
      is_core = true;
      is_ncore = true;
      is_mixed = true;
      //cout << (isLearnt ? "l#" : "c#") << i << ". " << seedingCls << "\n";
      for(auto l : seedingCls) {
        is_core               &= bvars.isCore(l)    || (bvars.orig_IsCore(l) && params.mx_seed_originals);
        is_ncore              &= bvars.isNonCore(l) || (bvars.orig_IsNonCore(l) && params.mx_seed_originals);
        is_mixed              &= bvars.isBvar(l)    || (bvars.inMutex(l) && params.mx_seed_originals);
      }

      bool keep = seed_all || is_core || (is_ncore && params.seed_type > 1) || (is_mixed && params.seed_type > 2);
      if(!keep) {
        seedingCls.clear();
        if(!isLearnt)
          allClausesSeeded = false;
      }
      if(seedingCls.size() == 2
         && bvars.areSubsumedByMx(seedingCls[0], seedingCls[1]))
        seedingCls.clear();

      if (seedingCls.size() > 0) {
        if(is_core)
          cplex_cores[isLearnt].push_back(seedingCls);
        else if(is_ncore)
          cplex_ncores[isLearnt].push_back(seedingCls);
        else if(is_mixed)
          cplex_mixed[isLearnt].push_back(seedingCls);
        else
          cplex_ordinary[isLearnt].push_back(seedingCls);
      }
    }
  }

  if(params.verbosity > 0) {
    for(size_t isLearnt = 0; isLearnt < (params.seed_learnts ? 2 : 1); isLearnt++) {
      auto n = cplex_cores[isLearnt].size() + cplex_ncores[isLearnt].size() +
        cplex_mixed[isLearnt].size() + cplex_ordinary[isLearnt].size();

      cout << "c EqSeed: found " << n << " seedable constraints from "
           << (isLearnt ? " learnts\n" : "input clauses\n");
      cout << "c EqSeed: " << cplex_cores[isLearnt].size() << " cores "
           << cplex_ncores[isLearnt].size() << " non-cores "
           << cplex_mixed[isLearnt].size() << " mixed-cores "
           << cplex_ordinary[isLearnt].size() << " ordinary clauses\n";
    }
  }

  //Now add the accumulated seed constraints up to the supplied limit.
  //prioritize. cores before nonCores before Mixed.
  //Short constraints before long ones.

  auto mergeClauses = [](vector<vector<vector<Lit>>> &v) {
    vector<vector<Lit>> clauses {};
    for(auto cls_set : v)
      for(auto cls : cls_set)
        clauses.push_back(std::move(cls));
    return clauses;
  };

  auto cores {mergeClauses(cplex_cores)};
  auto ncores {mergeClauses(cplex_ncores)};
  auto mixed {mergeClauses(cplex_mixed)};
  auto ordinary {mergeClauses(cplex_ordinary)};

  auto vecSizeLt = [](const vector<Lit> &v1, const vector<Lit>& v2){ return v1.size() < v2.size(); };

  sort(cores.begin(), cores.end(), vecSizeLt);
  sort(ncores.begin(), ncores.end(), vecSizeLt);
  sort(mixed.begin(), mixed.end(), vecSizeLt);
  sort(ordinary.begin(), ordinary.end(), vecSizeLt);

  auto addUpTo = [this](vector<vector<Lit>> &c, int &lim, size_t &nAdd) {
    //add up to lim constraints to cplex. Update lim and number
    //added, return total length of constraints added
    double tl {};
    int i {};
    for(i = 0; static_cast<size_t>(i) < c.size() && i < lim; i++) {
      tl += c[i].size();
      store_cplex_greedy_cls(c[i]);
    }
    nAdd = i;
    lim -= i;
    return tl;
  };

  size_t n_cores {}, n_ncores {}, n_mixed {}, n_ordinary {};
  double l_cores {}, l_ncores {}, l_mixed {}, l_ordinary {};
  int limit {params.seed_max};

  l_cores    = addUpTo(cores, limit, n_cores);
  l_ncores   = addUpTo(ncores, limit, n_ncores);
  l_mixed    = addUpTo(mixed, limit, n_mixed);
  l_ordinary = addUpTo(ordinary, limit, n_ordinary);

  if(limit < 0)
     allClausesSeeded = false;

  if (params.verbosity > 0) {
    cout << "c EqSeed: #seeded constraints " << params.seed_max - limit << "\n";
    cout << "c EqSeed: cores            " <<  n_cores
         <<  " Ave length " << (n_cores > 0 ? l_cores/n_cores : 0.0) << "\n";
    cout << "c EqSeed: non-cores        " <<  n_ncores
         <<  " Ave length " << (n_ncores > 0 ? l_ncores/n_ncores : 0.0) << "\n";
    cout << "c EqSeed: mixed cores      " <<  n_mixed
         <<  " Ave length " << (n_mixed > 0 ? l_mixed/n_mixed : 0.0) << "\n";
    cout << "c EqSeed: ordinary clauses " <<  n_ordinary
         <<  " Ave length " << (n_ordinary > 0 ? l_ordinary/n_ordinary : 0.0) << "\n";

    if(allClausesSeeded)
      cout << "c CPLEX has full input theory\n";
  }
}

void MaxSolver::printStatsAndExit(int signum, int exitType) {
  if (!printStatsExecuted) {
    printStatsExecuted = true;
    double cpu_time = cpuTime();
    double mem_used = memUsedPeak();

    if(signum >= 0) {
      cout << "c INTERRUPTED signal " <<  signum << "\n";
    }
    if(!solved) {
      cout << "c unsolved\n";
      cout << "c Best LB Found: " << LB()+theWcnf->baseCost() << "\n";
      cout << "c Best UB Found: " << UB()+theWcnf->baseCost() << "\n";

      Weight solCost = UB() + theWcnf->baseCost();
      Weight intPart;
      auto p = cout.precision();
      if(modf(solCost, &intPart) > 0)
        cout << "o " << solCost << "\n";
      else
        cout << "o " << std::fixed << std::setprecision(0) << solCost << "\n";
      cout.precision(p);
      cout.unsetf(std::ios::fixed);

      if(params.printBstSoln) {
        cout << "c Best Model Found:\n";
        if(haveUBModel) {
          cout << "c ";
          for (int i = 0; i < theWcnf->nVars(); i++)
            cout << (UBmodel[i] == l_True ? "" : "-")  << i+1 << " ";
          cout << "\n";
        }
        else
          cout << "c No Model of hard clauses found\n";
      }
    }

    cout << "c CPLEX: #constraints " << cplex->nCnstr()  << "\n";
    cout << "c CPLEX: Avg constraint size "
         << cplex->totalCnstrSize()/(double)cplex->nCnstr()  << "\n";
    cout << "c CPLEX: #non-core constraints " << cplex->nNonCores() << "\n";
    cout << "c CPLEX: Ave non-core size "
         << (cplex->totalNonCore())/((double) (cplex->nNonCores())) << "\n";

    cout << "c SAT: #calls " << satsolver->nSolves() << "\n";
    cout << "c SAT: Total time " << satsolver->total_time() + muser->total_time() << "\n";
    cout << "c SAT: #muser calls " << muser->nSolves() << " ("
         << muser->nSucc_Solves()*100.0/muser->nSolves() << " % successful)\n";
    cout << "c SAT: Minimize time " << muser->total_time()
         << " (" << muser->total_time()*100/(satsolver->total_time()+muser->total_time()) << "%)\n";
    cout << "c SAT: Avg constraint minimization "
         << amountConflictMin/(double) cplex->nCnstr()  << "\n";
    cout << "c CPLEX: #calls " << cplex->nSolves() << "\n";
    cout << "c CPLEX: Total time " << cplex->total_time() << "\n";
    cout << "c GREEDY: #calls " << greedysolver->nSolves() << "\n";;
    cout << "c GREEDY: Total time " << greedysolver->total_time() << "\n";

    if(params.find_forced) {
      cout << "c FindForced: Total failed lits detecte   " << nFailedLits << "\n";
      cout << "c FindForced: Total lits forced by bounds " << nForcedByBounds << "\n";
    }

    if(params.lp_harden) {
      cout << "c LP-Bounds: Hardened " << n_softs_forced_hard << " softs ";
      cout << n_softs_forced_hard_not_in_cplex << " because not in cplex\n";
      cout << "c LP-Bounds: Relaxed " << n_softs_forced_relaxed << " softs\n";
      cout << "c LP-Bounds: Total time " << cplex->total_lp_time() << "\n";
      cout << "c LP-Bounds: #calls " << cplex->nLPSolves() << "\n";

    cout << "c CPLEX: #calls " << cplex->nSolves() << "\n";
    cout << "c CPLEX: Total time " << cplex->total_time() << "\n";

    }

    cout << "c MEM MB: " << mem_used << "\n";
    cout << "c CPU: " << cpu_time << "\n";
  }
  fflush(stdout);
  fflush(stderr);
  _exit(exitType);
}

void MaxSolver::reportCplex(Weight cplexLB, Weight solnWt) {
  if (params.verbosity > 0) {
    cout <<"c CPLEX returns incumbent with cost " << solnWt << " and lower bound of " << cplexLB
         << " time = " << cplex->solveTime() << "\n";
  }
}

void MaxSolver::reportSAT_min(lbool result, double iTime, size_t orig_size, int nMins, double mTime, size_t final_size) {
  if (params.verbosity > 1) {
    cout << "c SAT_MIN: " << result;
    if(result==l_False)
      cout << ", In cnf size = " << orig_size << ", reduction = " << orig_size - final_size;
    cout  << ", Init Sat time: " << iTime
          << ", Min calls: " << nMins
          << ", Min time: " << mTime << "\n";
  }
}

void MaxSolver::reportForced(const vector<Lit> &forced, Weight wt) {
  if (params.verbosity > 0 && forced.size() > 0) {
    cout << "c Forced Soft Clauses (#" << forced.size() << ", wt = " << wt << "\n";
    if (params.verbosity > 2)
      outputConflict(forced);
  }
}

lbool MaxSolver::satsolve_min(const Assumps& inAssumps, vector<Lit>& outConflict,
                              double sat_cpu_lim, double mus_cpu_lim) {
  double isatTime {0};
  //satsolver->pruneLearnts();
  lbool result = (sat_cpu_lim > 0) ?
    satsolver->solveBudget(inAssumps.vec(), outConflict, sat_cpu_lim) :
    satsolver->solve(inAssumps.vec(), outConflict);

  if(params.fb)
    satSolverAddBvarsFromSofts();

  size_t orig_size { outConflict.size() };

  isatTime = satsolver->solveTime();
  muser->startTimer();
  if (result == l_False && params.min_type == 1 && outConflict.size() > 2) {
    int origsize = outConflict.size();
    minimize_muser(outConflict, mus_cpu_lim);
    amountConflictMin += origsize - outConflict.size();
  }

  if(outConflict.size() == 1 && satsolver->curVal(outConflict[0]) == l_Undef) {
    //probably quite rare...but since units are propagated to all solvers why not?
    satsolver->addClause( {outConflict[0]} );
    cout << "c NOTE: added new unit via minimization\n";
  }

  reportSAT_min(result, isatTime, orig_size, muser->nSatSolvesSinceTimer(), muser->elapTime(), outConflict.size());
  return result;
}

void MaxSolver::minimize_muser(vector<Lit> &con, double mus_cpu_lim) {
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

  muserAddNewForcedVars();
  if(!doMin)
    return;

  size_t reduction {0};
  size_t osize {0};

  if(doMin) {
    osize = con.size();
    //std::sort(con.begin(), con.end(), minConf);
    std::sort(con.begin(), con.end(), blit_lt);
    if(mus_cpu_lim > 0)
      muser->musBudget(con, mus_cpu_lim);
    else
      muser->mus(con);
    //debug
    //check_mus(con);
    satSolverAddNewForcedVars();
    if(params.fb)
      satSolverAddBvarsFromSofts();
    reduction = osize - con.size();
  }

  if(osize > 1) {
    mtime += muser->solveTime();
    ++mcalls;
    m_sum_reduced_frac += static_cast<double>(reduction)/static_cast<double>(osize);
  }

  doMin = params.mus_min_red <= 0
    //|| (mtime < 124.0) //give muser some time to allow rate computation to be more accurate
    //|| mcalls < 64
    || (mtime < 64.0) //give muser some time to allow rate computation to be more accurate
    || (m_sum_reduced_frac/mcalls) > params.mus_min_red;

  if(params.verbosity > 1)
    cout << "c doMin = " << doMin << " mtime = " << mtime
         << " average reduction = " << m_sum_reduced_frac/mcalls << "\n";
}

void MaxSolver::check_mus(vector<Lit> &con) {
  //Test to see if con is a MUS (DEBUGGING)
  size_t orig_size = con.size();
  vector<Lit> assumps;
  vector<Lit> critical;
  vector<Lit> tmp;
  auto litHash = [](const Lit l) { return std::hash<int>()(toInt(l)); };
  std::unordered_set<Lit,decltype(litHash)> inCon(con.size(), litHash);
  auto findInCon = [&inCon](Lit l){ return inCon.find(l) == inCon.end(); };

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

  //std::sort(con.begin(), con.end(), mConf);
  assumps.clear();
  for (size_t i = 0; i < con.size(); i++)
    assumps.push_back(~con[i]);
  if(satsolver->solve(assumps,tmp) == l_True)
    cout << "check_mus: ERROR mus not unsatisfiable\n";

  while(con.size() > 0) {
    Lit min = con.back();
    con.pop_back();

    assumps.clear();
    for (size_t i = 0; i < critical.size(); i++)
      assumps.push_back(~critical[i]);
    for (size_t i = 0; i < con.size(); i++)
      assumps.push_back(~con[i]);

    if(satsolver->solve(assumps, tmp) == l_True) {
      //min was critical
      critical.push_back(min);
    }
    else {
      inCon.clear();
      for(auto lt : tmp)
        inCon.insert(lt);
      auto p = std::remove_if(con.begin(), con.end(), findInCon);
      con.erase(p, con.end());
    }
  }
  con = critical;

  if(con.size() != orig_size) {
    cout << "check_mus: ERROR mus not minimal orig size = " << orig_size
         << " reduced size = " << con.size() << "\n";
    cout << " conflict = " << con << "\n";
  }
}

void MaxSolver::outputConflict(const vector<Lit> &con) {
  cout << "conflict clause (" << con.size() << "): ";
  for (size_t i = 0; i < con.size(); i++) {
    satsolver->printLit(con[i]);
    cout << " ";
  }
  cout << "\n";
}

//Currently not used. But if we call satsolver->pruneLearnts
//This function will be used to determine which learnts to delete
//Potentially inefficient if called frequently...requires copying
//Sat solver's clause into passed std:vector.
bool MaxSolver::deleteLearntTest(const vector<Lit> &c) const {
  if (c.size() <= 3)
    return false;
  //keep hard learnts
  //if (!params.delete_hard_learnts) {
  bool containsBVar = false;
  for (size_t i = 0; i < c.size(); i++) {
    if (bvars.isBvar(c[i])) {
      containsBVar = true;
      break;
    }
  }
  // no b-var==> hard learnt
  if (!containsBVar) {
    return false;
  }
  return true;
}

void MaxSolver::unsatFound() {
  cout << "c Hard Clauses are UNSAT.\n";
  cout << "s UNSATISFIABLE\n";
  updateLB(theWcnf->dimacsTop());
  unsat = true;
  solved = true;
  cout << "c Final LB: " << LB() << "\n";
  cout << "c Final UB: " << UB() << "\n";
  fflush(stdout);
}

void MaxSolver::optFound(std::string reason) {
  cout << reason << "\n";
  Weight solCost = UB() + theWcnf->baseCost();
  Weight intPart;
  auto p = cout.precision();
  if(modf(solCost, &intPart) > 0)
    cout << "o " << solCost << "\n";
  else
    cout << "o " << std::fixed << std::setprecision(0) << solCost << "\n";
  cout.precision(p);
  cout.unsetf(std::ios::fixed);
  cout << "s OPTIMUM FOUND\n";
  solved = true;
  theWcnf->rewriteModelToInput(UBmodel);

  for(size_t i=0; i < UBmodel.size(); i++)
    if(UBmodel[i] == l_Undef)
      UBmodel[i] = l_True; //set unset vars to arbitary value (true)

  printSolution(UBmodel);
  fflush(stdout);
  int nfalseSofts;
  if(theWcnf->checkModelFinal(UBmodel, nfalseSofts) != UB() + theWcnf->baseCost()) //we cannot use wcnf after this!
    cout << "c ERROR incorrect model reported" << endl;
  else
    cout << "c Solved: Number of falsified softs = " << nfalseSofts << "\n";
}


void MaxSolver::printCurClause(const vector<Lit>& cls) {
  cout << "[";
  for (size_t i = 0; i < cls.size()-1; i++) {
    satsolver->printLit(cls[i]);
    cout << ", ";
  }
  if (cls.size() > 0)
    satsolver->printLit(cls.back());
  cout << "]";
}


void MaxSolver::printErrorAndExit(const char *msg) {
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
  if(!params.printSoln)
    return;

  cout << "v";
  for (size_t i = 0; i < model.size(); i++) {
    cout << " " << (model[i] == l_True ? "" : "-") << i+1;
  }
  cout << endl;
}

void MaxSolver::configBvar(Var bvar, SatSolver* slv) {
  //Configure any blits after they have been added to the sat solver
  //Should be passed literal appearing in soft clause (i.e.,
  //blit=false ==> enforce clause)
  if(params.preprocess)
    slv->freezeVar(bvar);

  if(!params.bvarDecisions && !bvars.isOvar(bvar))
    //keep unit b-vars (ordinary vars as decisions)
    slv->setDecisionVar(bvar, false);

  //setPolarity determines if sign should be true!  So if bvar appears
  //positively in clause, we want to set its default sign to true
  //(making it false and activating the clause by defaults)

  slv->setPolarity(bvar,
    (bvars.coreIsPos(bvar) || bvars.orig_coreIsPos(bvar)) ?
                   l_True : l_False);
}

void MaxSolver::addHards(SatSolver* slv) {
  for (size_t i = 0; i < theWcnf->nHards(); i++) {
    if (!slv->addClause(theWcnf->getHard(i))) {
      cout << "c Adding hard clauses caused unsat.\n";
      return;
    }
    for(auto lt : theWcnf->hards()[i])
      if(bvars.isBvar(lt) ||
         (params.mx_seed_originals && bvars.inMutex(lt)))
        configBvar(var(lt), slv);
  }
}


void MaxSolver::addHards(SatSolver* slv, const vector<int>& indicies) {
  for(auto i : indicies) {
    if (!slv->addClause(theWcnf->getHard(i))) {
      cout << "c Adding hard clauses caused unsat.\n";
      return;
    }
    for(auto lt : theWcnf->hards()[i])
      if(bvars.isBvar(lt) ||
         (params.mx_seed_originals && bvars.inMutex(lt)))
        configBvar(var(lt), slv);
  }
}

void MaxSolver::addSofts(SatSolver* slv) {
  for (size_t i = 0; i < theWcnf->nSofts(); i++) {
    Lit blit = bvars.litOfCls(i);

    /*cout << "Soft clause " << i << " " << theWcnf->getSoft(i) << "\n"
      << "blit = " << blit << "\n";*/

    if(theWcnf->softSize(i) > 1) {
      //Only non-unit softs get added to solver (units are handled in the assumptions)
      vector<Lit> sftCls {theWcnf->getSoft(i)};
      sftCls.push_back(blit);
      if(!slv->addClause(sftCls)) {
        cout << "c ERROR: soft clause " << i << " caused solver UNSAT state!\n";
        printCurClause(sftCls);
        return;
      }
      for(auto lt : sftCls)
        if(bvars.isBvar(lt) ||
           (params.mx_seed_originals && bvars.inMutex(lt)))
          configBvar(var(lt), slv);
    }
  }
}

void MaxSolver::addSofts(SatSolver* slv, const vector<int>& indicies) {
  for (auto i : indicies) {
    Lit blit = bvars.litOfCls(i);
    if(theWcnf->softSize(i) > 1) {
      //Only non-unit softs get added to solver (units are handled in the assumptions)
      vector<Lit> sftCls {theWcnf->getSoft(i)};
      sftCls.push_back(blit);
      if(!slv->addClause(sftCls)) {
        cout << "c ERROR: soft clause " << i << " caused solver UNSAT state!\n";
        printCurClause(sftCls);
        return;
      }
      for(auto lt : sftCls)
        if(bvars.isBvar(lt) ||
           (params.mx_seed_originals && bvars.inMutex(lt)))
          configBvar(var(lt), slv);
    }
  }
}

void MaxSolver::addSoftEqs(SatSolver* slv, bool removable) {
  //add eqs to solver. Optionally make them removable
  //Note all softs processed here should have already been added
  //to the solver to config their b-vars.
  vector<Lit> eqcls(removable ? 3 : 2, lit_Undef);
  for (size_t i = 0; i < theWcnf->nSofts(); i++)
    if(theWcnf->softSize(i) > 1) {
      if(removable && eqCvarPos == lit_Undef) {
        slv->newControlVar(eqCvar, false); //not a decision variable
        eqCvarPos = mkLit(eqCvar, false);
      }
      Lit bneg = ~bvars.litOfCls(i);
      for(auto l: theWcnf->softs()[i]) {
        eqcls[0] = ~l; eqcls[1] = bneg;
        if(removable) eqcls[2] = eqCvarPos;
        //note addClause modifies eqcls
        if(!slv->addClause(eqcls)) {
          cout << "c ERROR: equality clause (" << eqcls[0] << " "
               << eqcls[1];
          if(removable)
            cout << " " << eqcls[2];
          cout << ") causes solver UNSAT state!\n";
          return;
        }
      }
    }
}

void MaxSolver::addSoftEqs(SatSolver* slv, bool removable,
                           const vector<int>& indicies) {
  //Note all softs processed here should have already been added
  //to the solver to config their b-vars.
  vector<Lit> eqcls(removable ? 3 : 2, lit_Undef);
  for (auto i : indicies)
    if(theWcnf->softSize(i) > 1) {
      if(removable && eqCvarPos == lit_Undef) {
        slv->newControlVar(eqCvar, false); //not a decision variable
        eqCvarPos = mkLit(eqCvar, false);
      }
      Lit bneg = ~bvars.litOfCls(i);
      for(auto l: theWcnf->softs()[i]) {
        eqcls[0] = ~l; eqcls[1] = bneg;
        if(removable) eqcls[2] = eqCvarPos;
        //note addClause modifies eqcls
        if(!slv->addClause(eqcls)) {
          cout << "c ERROR: equality clause (" << eqcls[0] << " "
               << eqcls[1];
          if(removable)
            cout << " " << eqcls[2];
          cout << ") causes satsolver UNSAT state!\n";
          return;
        }
      }
    }
}

void MaxSolver::initSftSatisfied() {
  vector<vector<int>> satByLit(theWcnf->nVars()*2, vector<int>{});
  for(size_t i = 0; i < theWcnf->nSofts(); i++)
    for(auto lt: theWcnf->softs()[i])
      satByLit[toInt(lt)].push_back(i);
  for(auto& v : satByLit)
    sftSatisfied.addVec(v);
  //Debug
  /*cout << "Softs\n";
    cout << theWcnf->softs();
    cout << "\nFinal occurance list\n";
    cout << sftSatisfied;*/
}


void MaxSolver::setNoBvarDecisions() {
  for (size_t i = 0; i < theWcnf->nSofts(); i++) {
    Var b = bvars.varOfCls(i);
    if(!bvars.isOvar(b)) //don't change ordinary b-vars (from units)?
      satsolver->setDecisionVar(b, false);
  }
}

void MaxSolver::improveModel() {
  //Sat solver has found a model. Try to improve the cost of that model by computing a muc.
  vector<Lit> assumps;
  vector<Lit> branchLits;
  Weight prevWt {0};
  if(params.verbosity  > 0) {
    cout << "c Trying to improve Model\n";
    //cout << "totalClsWt() = " << theWcnf->totalClsWt() << " getSatClsWt() = " << getSatClsWt() << "\n";
    prevWt = theWcnf->totalClsWt() - getSatClsWt();
    cout << "c Current Model weight = " << prevWt << "\n";
  }

  for(size_t i = 0; i < bvars.n_bvars(); i++) {
    /*cout << "soft clause #" << i << " litofCls = " << bvars.litOfCls(i)
      << " model value = " << satsolver->modelValue(bvars.litOfCls(i)) << "\n";*/
    if(satsolver->curVal(bvars.litOfCls(i)) == l_Undef) { //only try to change un-forced b's
      auto tval = satsolver->modelValue(bvars.litOfCls(i));
      if(tval == l_True)
        branchLits.push_back(~bvars.litOfCls(i)); //try to negate these bvars
      else
        assumps.push_back(~bvars.litOfCls(i)); //these bvars must remain false
    }
  }

  if(params.verbosity > 1) {
    cout << "c assumptions size = " << assumps.size() << " branchlits size = " << branchLits.size() << "\n";
    /*cout << "Assumps = " << assumps << "\n";
      cout << "branchlits = " << branchLits << "\n";*/
  }

  //if(params.improve_model_max_size > 0 && static_cast<int>(branchLits.size()) > params.improve_model_max_size)
  //  return;

  auto val = satsolver->relaxSolve(assumps, branchLits, params.improve_model_cpu_lim);

  if(params.verbosity > 0) {
    cout << "c Relaxation search yielded " << val << "\n";
    Weight newWt = theWcnf->totalClsWt() - getSatClsWt();
    cout << "c Old wt = " << prevWt << " new wt = " << newWt << " improvement = " << prevWt - newWt << "\n";
  }
}

Weight MaxSolver::updateUB() {
  //return weight of new model...update UB if it is a better model.
  Weight w = getSatClsWt();
  if (!haveUBModel || w > sat_wt) {
    sat_wt = w;
    if(params.verbosity > 0) {
      cout << "c New UB found " << UB() << "\n";
      cout << "c Elapsed time " << cpuTime() - globalStartTime << "\n";
    }
    have_new_UB_model = true;
    setUBModel();

    if(params.find_forced)
      findForced();
  }
  return theWcnf->totalClsWt() - w;
}

void MaxSolver::setUBModel() {
  //copy sat solvers model to UBmodel; Note sat solver's model might
  //be incomplete resulting in l_Undef as the value of some variables
  haveUBModel = true;
  for(int i = 0; i < theWcnf->nVars(); i++)
    UBmodel[i] = satsolver->modelValue(i);
  for(size_t i = 0; i < theWcnf->nSofts(); i++)
    UBmodelSofts[i] = tmpModelSofts[i];
}

Weight MaxSolver::getSatClsWt() {
  //return sum of weight of satisfied clauses.
  //Note sat solver's model might be incomplete.
  //and bvars might not be set.
  Weight w {0.0};
  for(size_t i = 0; i < theWcnf->nSofts(); i++) {
    bool is_sat = false;
    //calling theWcnf->softs() avoids copying soft clauses.
    for(auto ell : theWcnf->softs()[i])
      if(satsolver->modelValue(ell) == l_True) {
        is_sat = true;
        break;
      }
    if(is_sat) {
      w += theWcnf->getWt(i);
      tmpModelSofts[i] = l_True;
    }
    else
      tmpModelSofts[i] = l_False;
    /*else {
      cout << i << "-th soft falsified bvar = "
      << bvars.litOfCls(i) << " value = "
      << satsolver->modelValue(bvars.litOfCls(i)) << "\n";
      cout << "[ ";
      for(auto ell : theWcnf->softs()[i]) {
      cout << ell << satsolver->modelValue(ell) << " ";
      }
      cout << "]\n";
      }*/
  }
  //cout << "Computed wt = " << w << " total wt = " << theWcnf->totalClsWt() << "\n";
  return w;
}

Weight MaxSolver::getForcedWt() {
  //return weight of forced b-vars. Note that
  //this works with both fb and fbeq. In fb the solver could set some
  //b-vars arbitrarily. But it can't force them to be true.

  forcedWtNU.update(satsolver);
  vector<Lit>& forced = forcedWtNU.forced;

  /*static int notSeen {0};
    vector<Lit> forced { satsolver->getForced(notSeen) };
    notSeen += forced.size();*/

  for(auto l : forced) {
    if(bvars.isBvar(l))
      forced_wt += bvars.wt(l); //If l is negated b-var its wt is zero.
  }
  return forced_wt;
}

Weight MaxSolver::getWtOfBvars(const vector<Lit>& blits) {
  Weight w {0};
  for(auto b : blits) {
    if(bvars.isBvar(b))
      w += bvars.wt(b);
  }
  return w;
}

void MaxSolver::store_cplex_greedy_cls(const vector<Lit>& cls) {
  //clauses of size 1 are forced in sat solver and will
  //be added by AddNewForcedBvars; Only cores are added to the greedy
  //solver
  if(cls.size() <= 1)
    return;
  cplexClauses.addVec(cls);
  bool core {true};
  for(auto lt : cls)
    core &= bvars.isCore(lt);
  if(core) {
    incrBLitOccurrences(cls);
    greedyClauses.addVec(cls);
  }
}

vector<Lit> MaxSolver::greedySoln() {
  //return a greedy solution of the clauses fed (and pending) to CPLEX
  if(params.verbosity > 0) {
    cout << "c Computing Greedy Solution\n";
  }
  vector<Lit> soln;
  greedyAddNewForcedBvars();
  greedyAddNewClauses();
  //if(greedysolver)
  soln = greedysolver->solve();
  /*else {
    auto val = greedySatSolver->solve();
    if(val == l_False)
    cout << "c ERROR. CPLEX clauses have no solution (or greedy solver couldn't find one)\n";
    for(size_t i = 0; i < bvars.n_bvars(); i++) {
    Var v = bvars.varOfCls(i);
    lbool val = greedySatSolver->modelValue(v);
    if(val == l_True)
    soln.push_back(mkLit(v, false));
    else if(val == l_False)
    soln.push_back(mkLit(v, true));
    else if(val == l_Undef)
    soln.push_back(~bvars.litOfCls(i)); //harden clause if no value assigned
    }
    }*/
  if(params.verbosity > 0) {
    cout << "c Greedy: soln cost = " << getWtOfBvars(soln) << "\n";
  }
  return soln;
}

bool MaxSolver::vec_isCore(const vector<Lit>& core) {
  for(auto l : core)
    if(bvars.isNonCore(l))
      return(false);
  return true;
}

void MaxSolver::findForced() {
  //Check if new UB allows any variables to be forced.
  //Try ordinary variables if there are few enough of them
  //else try only b-vars. Does not account for future forced lits changing the implication wt.
  auto nf = nFailedLits;
  auto nb = nForcedByBounds;
  for(size_t i = 0; i < satsolver->nVars(); i++) {
    if(!satsolver->activeVar(i))
      continue;
    for(int sign = 0; sign < 2; sign++) {
      Lit l = mkLit(i, sign);

      /*cout << " Active Lit " << l;
        cout << (impWtIsUnk(l) ? " Unknown Wt " :
        (impWtIsUB(l) ? " Upperbound " : " Exact "));
        if(!impWtIsUnk(l) && !impWtIsUB(l) && !impWtIsExact(l))
        cout << " ERROR weight type not set properly\n";
        else if(!impWtIsUnk(l))
        cout << " weight = " << getImpWt(l) << "\n";*/

      if(impWtIsUnk(l)) { //not computed. Compute now
        if(findImpWt(l))
          break; //was forced
      }
      else if(impWtIsUB(l)) {
        if(getImpWt(l) > UB()) {
          //potentially forced. Refine now
          if(findImpWt(l))
            break;
        }
      }
      else {//is exact
        assert(impWtIsExact(l));
        if(getImpWt(l) > UB()) {
          satsolver->addClause({~l});
          ++nForcedByBounds;
          break;
        }
      }
    }
  }
  if(params.verbosity>0)
    cout << "c findForced found " << nFailedLits-nf << " failed lits and "
         << nForcedByBounds-nb << " lits forced by bounding\n";
}

bool MaxSolver::findImpWt(Lit l) {
  vector<Lit> imps;
  //compute implied weight of l by UP. Return true if l was forced
  if(!satsolver->findImplications(l, imps)) {
    satsolver->addClause({~l});
    ++nFailedLits;
    return true;
  }
  auto wt = getWtOfBvars(imps);
  if(wt + getForcedWt() > UB()) {
    satsolver->addClause({~l});
    ++nForcedByBounds;
    return true;
  }
  setImpWt(l, wt, impWtExact);
  for(auto x : imps)
    if(impWtIsUnk(x) || (impWtIsUB(x) && wt < getImpWt(x)))
      setImpWt(x, wt, impWtUB);
  return false;
}

bool MaxSolver::BLitOrderLt::operator() (const Lit l1, const Lit l2) const {
  //must be strict weak order:

  int oc1 = (*occurCount)[bvars.toIndex(l1)];
  int oc2 = (*occurCount)[bvars.toIndex(l2)];
  double wt1 = bvars.wt(l1);
  double wt2 = bvars.wt(l2);
  bool retval {0};

  if(wt1 == 0 && oc1 > 0) {   //l1 is super---satisfies cores at zero cost
    if(wt2 == 0 && oc2 > 0)  //so is l2
      if(oc1 == oc2)
        retval = (l1 < l2); //order lits the same for gt and lt
    //when discriminators are equal
      else
        retval = (oc1 < oc2) ^ gt; //XOR: we know that oc1 !=
    //oc2. So if (oc1 < oc2) == 0,
    //then l1 > l2.
    else //l2 is not super
      retval = gt; //l1 > l2
  }
  else if(wt2 == 0 && oc2 > 0) //l1 is not super but l2 is
    retval = !gt; //l1 < l2
  else {
    //Neither is super compute merit
    double m1 {0.0};
    double m2 {0.0};

    //note since lits not super wt == 0 ==> oc == 0; no division by 0
    m1 = (oc1==0) ? -wt1 : oc1/wt1;
    m2 = (oc2==0) ? -wt2 : oc2/wt2;

    if(m1 == m2) {
      if(bvars.clsSize(l1) == bvars.clsSize(l2))
        retval =  (l1 < l2);
      else
        retval = (bvars.clsSize(l1) < bvars.clsSize(l2)) ^ gt;
    }
    else
      retval = (m1 < m2) ^ gt;
  }
  return retval;
}
