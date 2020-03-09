/***********[greedySatSolver.cc]
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

/* Interface to minisat.
 */

#include <vector>
#include <algorithm>
#include <ostream>

#ifdef GLUCOSE
#include "glucose/core/SolverTypes.h"
#include "glucose/utils/System.h"
#include "glucose/mtl/Heap.h"
#else
#include "minisat/core/SolverTypes.h"
#include "minisat/utils/System.h"
#include "minisat/mtl/Heap.h"
#endif


#include "maxhs/ifaces/GreedySolver.h"
#include "maxhs/utils/io.h"


using namespace MaxHS_Iface;

#ifdef GLUCOSE
namespace Minisat = Glucose;
#endif

using namespace Minisat;

GreedySolver::GreedySolver(Bvars& b) :
  bvars (b),
  nSatCores {0},
  dyn_nSatCores {0},
  heap_lt {bvars, dyn_satCount},
  sftcls_heap {heap_lt},
  n_core_mxes {0},
  solves {0},
  totalTime {0},
  prevTotalTime {0},
  stime{-1}
  {}

GreedySolver::~GreedySolver() { }

void GreedySolver::ensureSC(int clsi) {
  //make sure all data structures are initialized for soft clause clsi
  if(clsi >= static_cast<int>(clsVal.size()))
    clsVal.resize(clsi+1, l_Undef);
  if(clsi >= static_cast<int>(init_sc.size()))
    init_sc.resize(clsi+1, 0);
  if(clsi >= static_cast<int>(occurList.size()))
    occurList.resize(clsi+1,{});
  if(clsi >= static_cast<int>(core_mx_num.size()))
    core_mx_num.resize(clsi+1, -1);
}

void GreedySolver::ensureCore(int corei) {
  //make sure all data structures are initialized for core corei
  if(corei >= static_cast<int>(cores.size()))
    cores.resize(corei+1);
  if(corei >= static_cast<int>(coreIsSat.size()))
    coreIsSat.resize(corei+1, 0);
}

bool GreedySolver::addClause(const vector<Lit>& lts) {
  /* Internally the greedy solver stores cores and does it processing with soft clause indicies
     This is a more compact range than the b-vars */
  //cout << "Adding " << lts << " to greedy solver\n";
  for(auto l: lts)
    if(!bvars.isBvar(l)
       || (lts.size() > 1 && !bvars.isCore(l))) {
      cout << "c ERROR added non-unit non-core or unit non-bvar constraint to greedy solver: "
           << lts << "\n";
      return false;
    }
  if(lts.size() == 1)
    return inputUnit(lts[0]);

  vector<int> c;
  for(auto l: lts) {
    auto clsi = bvars.clsIndex(l);
    ensureSC(clsi);
    if(clsVal[clsi] == l_True) {
      //remove warning---can often happen as new b-vars are forced inbetween computing
      //the greedy clause and adding it to the greedy solver.
      //cout << "c WARNING added already satisfied constraint to greedy solver\n";
      //cout << lts << " soft cls " << l << "\n";
      return true; //ignore this core.
    }
    if(clsVal[clsi] != l_False) //if soft clauses is hard it cannot be used to satisfy this core.
      c.push_back(clsi);
  }

  if(c.size() == 0) {
    cout << "c ERROR added unsatisfiable core to greedy solver\n";
    cout << lts << "\n";
    return false;
  }

  auto corei = cores.size();
  ensureCore(corei);
  for(auto clsi : c) {
    occurList[clsi].push_back(corei);
    init_sc[clsi] += 1;
  }
  cores[corei] = std::move(c);
  return true;
}

lbool GreedySolver::blit_curval(Lit b) {
  auto clsi = bvars.clsIndex(b);
  ensureSC(clsi);
  return bvars.isCore(b) ? clsVal[clsi] : clsVal[clsi].neg();
}

bool GreedySolver::addMutexConstraint(const SC_mx& mx) {
  /* constrain the greedy solver to respect the mutex mx. Note
     the mx is only passed to the greedy if it has no encoding lit.
     This means that all soft-clause-lits in the mx correspond to b-lits.
  */
  if(mx.encoding_lit() != lit_Undef) {
    cout << "c ERROR greedysolver passed mx that has already been transformed:\n"
         << mx << "\n";
    return false;
  }

  if(mx.soft_clause_lits().size() <= 1) {
    cout << "c ERROR greedysolver passed mx that is too short (<= 1) in size:\n"
         << mx << "\n";
    return false;
  }

  //preprocess mutex
  auto mx_lits {mx.soft_clause_lits()}; //at most one of these lits can be true
  if(!mx.is_core())
    for(size_t i = 0; i < mx_lits.size(); i++)
      mx_lits[i] = ~mx_lits[i];

  bool oneTrue {false};
  size_t cur_size, examine;
  for(cur_size = examine = 0; examine < mx_lits.size(); examine++) {
    lbool val = blit_curval(mx_lits[examine]);
    if(val == l_True) {
      if(oneTrue) {
        cout << "c ERROR: Greedy passed mutex with more than one lit forced to be true\n"
             << "c " << mx << "\n";
        return false;
      }
      oneTrue=true;
    }
    else if(val == l_False)
      continue;
    else
      //keep the lit only if it is unvalued
      mx_lits[cur_size++] = mx_lits[examine];
  }
  mx_lits.resize(cur_size);
  if(mx_lits.size() == 0)
    return true;

  if(oneTrue) { //force remaining to false
    for(auto l : mx_lits)
        inputUnit(~l);
    return true;
  }

  //Otherwise add the constraint
  if(mx.is_core()) {
    for(auto l : mx_lits)
      core_mx_num[bvars.clsIndex(l)] = n_core_mxes;
    n_core_mxes++;
  }
  else {
    ncore_mxes.push_back(std::move(mx_lits));
  }
  return true;
}

bool GreedySolver::inputUnit(Lit  lt) {
  /* Special function to deal with input of unit bvars that have been
     discovered to have a forced value by the user of GreedySolver.

     (a) lt is core --- it satisfies some of the already known cores.
     Remove those cores and update the initial sat count of each
     literal in the removed core. Remove the cores from the literal
     occur lists. DO NOT renumber the remaining cores.

     (b) lt is a non-core --- it strengthens some of the already known
     cores---potentially making them unit!
     Remove ~lt from each of the cores containing it.
     If a core becomes unit (x) then we have to process x which
     is a core literal--case a--fortunately this will not cause any
     further propagation.
     In both cases the sftcls index corresponding to lt gets its value marked
     so that future input cores can be simplified on input, and the occurs list
     for that soft clause is emptied.
  */
  int clsi = bvars.clsIndex(lt);
  ensureSC(clsi);
  lbool clsival = bvars.isCore(lt) ? l_True : l_False;
  if(clsVal[clsi] == clsival)
    return true;  //redundant unit;
  if(clsVal[clsi] != l_Undef) {
    cout << "c ERROR adding unit whose opposite has already been added to or inferred by greedy solver \n";
    cout << lt << "\n";
    return false;
  }
  clsVal[clsi] = clsival;
  if(clsival == l_True)
    processTrueB(clsi);
  else
    processFalseB(clsi);
  return true;
}

void GreedySolver::processTrueB(int clsi) {
  //soft clause clsi has become relaxed. This satisfies some cores.
  for(auto corei : occurList[clsi]) {
    if(coreIsSat[corei])
      continue;
    for(auto ci : cores[corei])
      if(ci != clsi) {
        init_sc[ci] -= 1; //decrement sat count
        auto& olist = occurList[ci];
        size_t j {0};
        for(size_t i=0; i < olist.size(); i++)
          if(olist[i] != corei)
            olist[j++] = olist[i];
        olist.resize(j);
      }
    coreIsSat[corei] = 1;
    ++nSatCores;
  }
  vector<int> tmp;
  std::swap(occurList[clsi], tmp); //soft clause clsi now has a sat count of zero.
  init_sc[clsi] = 0;
}

void GreedySolver::processFalseB(int clsi) {
  //soft clause clsi has become hard. This reduces some cores.
  vector<int> newUnits;
  for(auto corei: occurList[clsi]) {
    if(coreIsSat[corei])
      continue;
    auto& core = cores[corei];
    size_t j {0};
    for(size_t i = 0; i < core.size(); i++)
      if(core[i] != clsi)
        core[j++] = core[i];
    core.resize(j);
    if(core.size() == 1) {//new positive unit.
      //cout << "Found new unit core " << bvars.litOfCls(core[0]) << "\n";
      newUnits.push_back(core[0]);
    }
  }
  vector<int> tmp;
  std::swap(occurList[clsi], tmp); //soft clause clsi now has a sat count of zero.
  init_sc[clsi] = 0;

  for(auto sci: newUnits)
    inputUnit(bvars.litOfCls(sci)); //This cannot generate any new units
}

vector<Lit> GreedySolver::solve_() {
  //Compute greedy solution.
  solution.clear();
  dyn_satCount = init_sc;
  dyn_coreIsSat = coreIsSat;
  dyn_nSatCores = nSatCores;

  core_mx_in_solution.clear();
  core_mx_in_solution.resize(n_core_mxes, false);

  solution_update_ncore_mxes();

  sftcls_heap.clear();
  for(size_t i = 0; i < dyn_satCount.size(); i++)
    if(dyn_satCount[i] > 0)
      sftcls_heap.insert(i);

  /*//DEBUG
  if(!sftcls_heap.check()) {
    cout << "HEAP CORRUPTED\n";
    for(int i = 0; i < sftcls_heap.size(); i++) {
      auto csli = sftcls_heap[i];
      cout << "sftcls_heap[" << i << " -- " << ((i-1) >> 1)
           << "/" << (i+1)*2 << "/" << i*2+1
           << "] = " << csli
           << " dyn_satCount[" << csli << "] = "
           << dyn_satCount[csli] << " wt = " << bvars.wtNcls(csli)
           << " ** " << i << " lt " << ((i-1) >> 1) << " (parent) "
           << heap_lt((i ? sftcls_heap[((i-1) >> 1)] : i), sftcls_heap[i])
           << "\n";
    }
  }
  //DEBUG*/

  while(dyn_nSatCores < static_cast<int>(cores.size()) && !sftcls_heap.empty()) {
    auto next = sftcls_heap.removeMin();

    /*//DEBUG
    cout << "Heap item " << heap_n << ". clsi = " << next << " dyn_satCount = " << dyn_satCount[next]
         << " wt = " << bvars.wtNcls(next) << " dyn_nSatCores = " << dyn_nSatCores
         << " total number of cores " << cores.size() << "\n";
    heap_n++;
    //DEBUG*/

    if(core_mx_num[next] >= 0 && core_mx_in_solution[core_mx_num[next]])
      continue; //only one soft clause in a core mx can be in the solution.

    /*//DEBUG
    if(clsVal[next] != l_Undef)
      cout << "Heap item #" << heap_n
           << " Greedy value next soft clause " << bvars.litOfCls(next) <<  " from heap not unvalued\n"
           << " value = " << clsVal[next]
           << " dyn_satCount = " << dyn_satCount[next]
           << " dyn_nSatCores = " << dyn_nSatCores << "\n";
    //DEBUG*/


    //cout << "Processing blit " << bvars.litOfCls(next) << "\n";
    //cout << "dyn_nSatCores = " << dyn_nSatCores << "\n";
    add_sc_to_soln(next);
  }

  /*cout << "Greedy solver solution: [";
    for(auto clsi : solution)
    cout << bvars.litOfCls(clsi) << ", ";
    cout << "]\n";*/

  vector<Lit> tmp;
  for(size_t i = 0; i < static_cast<size_t>(bvars.n_bvars()); i++)
    if(i < clsVal.size() && clsVal[i] == l_True)
      tmp.push_back(bvars.litOfCls(i));
    else
      tmp.push_back(~bvars.litOfCls(i)); //harden by default

  for(auto clsi : solution)
    tmp[clsi] = bvars.litOfCls(clsi);

  return tmp;
}

void GreedySolver::add_sc_to_soln(int clsi) {
  //add soft clause index to solution and update dynamic data
  //for greedy solver. Return vector of soft clauses whose
  //satCount's modified.
  solution.push_back(clsi);

  /*//DEBUG

  if(clsVal[clsi] != l_Undef)
    cout << "Added valued soft clause to solution " << bvars.litOfCls(clsi) << " value " << clsVal[clsi] << "\n";

//DEBUG*/

  auto mx_num = core_mx_num[clsi];
  if(mx_num >= 0) {
    if(core_mx_in_solution[mx_num])
      cout << "c ERROR greedy solver tried to add more than one soft clause of a core mx to solution\n";
    core_mx_in_solution[mx_num] = true;
  }

  for(auto corei : occurList[clsi])
    if(dyn_coreIsSat[corei]==0) {
      dyn_coreIsSat[corei] = 1;
      ++dyn_nSatCores;
      auto core = cores[corei];
      for(auto ci: core) { //update dyn_satCount of soft clauses in core.
        dyn_satCount[ci] -= 1;
        if(sftcls_heap.inHeap(ci)) {
          sftcls_heap.increase(ci);
        }
        /*//DEBUG
        if(!sftcls_heap.check()) {
          cout << "HEAP CORRUPTED in add_sc_to_soln\n";
          cout << "dyn_satCount[" << ci << "; = " << dyn_satCount[ci] << "\n";
          for(int i = 0; i < sftcls_heap.size(); i++) {
            auto csli = sftcls_heap[i];
            cout << "sftcls_heap[" << i << " -- " << ((i-1) >> 1)
                 << "/" << (i+1)*2 << "/" << i*2+1
                 << "] = " << csli
                 << " dyn_satCount[" << csli << "] = "
                 << dyn_satCount[csli] << " wt = " << bvars.wtNcls(csli)
                 << " ** " << i << " lt " << ((i-1) >> 1) << " (parent) "
                 << heap_lt((i ? sftcls_heap[((i-1) >> 1)] : i), sftcls_heap[i])
                 << "\n";
          }
        }
        //else
        //  cout << "HEAP OK in add_sc_to_soln\n";
        //DEBUG*/
      }
    }
  return;
}

void GreedySolver::solution_update_ncore_mxes() {
  //Process non-cores. All of the soft clauses except 1 must be set to l_True.

  /*//DEBUG
  int n_added_to_soln {0};
  //DEBUG*/

  for(auto ncore_mx : ncore_mxes) {
    int trueCount {0};
    bool has_unvalued {false};
    int minSatCount {-1};
    int minSatClsIndex {0};

    for(auto b : ncore_mx) {
      if(blit_curval(b) == l_True)
        trueCount++;
      else if(blit_curval(b) == l_Undef) {
        has_unvalued = true;

        /*//DEBUG
        if(dyn_satCount[bvars.clsIndex(b)] < 0)
          cout << "ERROR dynamic sat count is less than zero dyn_satCount["
               << bvars.clsIndex(b) << "] = " << dyn_satCount[bvars.clsIndex(b)]
               << "\n";
               //DEBUG*/

        if(minSatCount < 0 || minSatCount > dyn_satCount[bvars.clsIndex(b)]) {
          minSatCount = dyn_satCount[bvars.clsIndex(b)];
          minSatClsIndex = bvars.clsIndex(b);
        }
      }
    }
    if(trueCount > 1)
      cout << "c ERROR: Greedy encountered mutex with more than one lit true during solving\n"
           << "c " << ncore_mx << "\n";
    else if(trueCount && has_unvalued) {
      //add unvalued soft clauses to solution (a non-core lit is true, so
      //all other non-cores must be false). non-core = false ==> corresponding
      //core blit is true and part of greedy solution.
      for(auto b : ncore_mx)
        if(blit_curval(b) == l_Undef) {
          add_sc_to_soln(bvars.clsIndex(b));
          //n_added_to_soln++;
        }
    }
    else if(has_unvalued) {
      //add all unvalued softs except the first soft achieving minSatCount to solution
      for(auto b : ncore_mx)
        if(blit_curval(b) == l_Undef) {
          auto clsi = bvars.clsIndex(b);
          if(clsi != minSatClsIndex) {
            add_sc_to_soln(clsi);
            //n_added_to_soln++;
          }
        }
    }
  }
}

void GreedySolver::printDS() {
  cout << "GreedySolver Data Structures:\n";
  for(size_t i=0; i < cores.size(); ++i) {
    cout << "Core #" << i << ": [";
    for(auto sc: cores[i])
      cout << bvars.litOfCls(sc) << ", ";
    cout << "] (" << cores[i].size() << ") ";
    cout << " core is sat = " << ((coreIsSat[i] == 1) ? 1 : 0) << "\n";
  }
  cout << "Number of satisfied cores = " << nSatCores << "\n";

  for(size_t i=0; i < occurList.size(); ++i) {
    cout << "Lit " << bvars.litOfCls(i) << ": [";
    for(auto ci: occurList[i])
      cout << ci << ", ";
    cout << "] (" << occurList[i].size() << ") ";
    cout << " initial sat count = " << init_sc[i];
    cout << " initial value = " << clsVal[i];
    cout << "\n";
  }
}
