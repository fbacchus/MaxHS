/***********[Params.cc]
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
#include "minisat/utils/Options.h"
#include "maxhs/utils/Params.h"
#include <limits>
#include <iostream>
using std::cout;

using namespace Minisat;
static const char* maxhs = "A: General MaxHS";
static const char* disjoint = "B: Disjoint Phase";
static const char* seed = "C: Seeding";
static const char* seqOfSat = "D: Sequence of Sat";
static const char* muser = "E: Core Minimization";
static const char* cplex = "F: CPLEX";
static const char* pop = "G: CPLEX Solution Pool and Populate";
static const char* pre = "H: Preprocessing";
static const char* debug = "I: Debugging";


//General Controls
static IntOption    opt_verb(maxhs, "verb", "Verbosity level (0=silent, 1=some, 2=more, "
			     "3=debugging output, 4=more debugging output).", 1, IntRange(0, 5));
static BoolOption   opt_bvardecisions(maxhs, "bvardecisions", "FB: make bvars decision variables.", false);
static BoolOption   opt_fbeq(maxhs, "fbeq", "FB: Use FbEq theory. Independent of \"coretype\"", false);
static BoolOption opt_printBstSoln(maxhs, "printBstSoln", "Print best solution found", false);
static BoolOption opt_printSoln(maxhs, "printSoln", "Print solution", true);
static DoubleOption opt_tolerance(maxhs, "tolerance", "For floating point weights only: return solution when when |soln-cost - lower bound| <= tolerance\n", 
				  1e-6, DoubleRange(0.0, true, std::numeric_limits<double>::max(), true));

//Muser Controls
static IntOption    opt_mintype(muser, "mintype", "JD: 0 = no minimization of " 
				"constraints/cores,  1 = Use Muser", 1, IntRange(0, 1));
static DoubleOption opt_mus_cpu_lim(muser, "mus-cpu-lim",
				    "FB: CPU time limit for minimizing each core (-1 == no limit).", 
				    2.5, DoubleRange(-1.0, true,  std::numeric_limits<double>::max(), true));
static DoubleOption opt_mus_min_red(muser, "mus-min-red",
					 "FB: Run muser only if on average it can remove at least this "
					 "fraction of a core (-1 == no limit). (eventually the muser is turned off)", 
					 0.10, DoubleRange(-1.0, true,  1.0, true));
static IntOption muser_verb(muser, "mverb", "Muser verbosity level (0=silent, 1=some, 2=more,3=debugging output, 4=more debugging output).", 0, IntRange(0, 4));





//Disjoint Phase Controls
static BoolOption   opt_dsjnt(disjoint, "dsjnt", "JD: Find disjoint cores in a first phase.", true);

static DoubleOption opt_dsjnt_cpu_per_core(disjoint, "dsjnt-cpu-lim",
					   "FB: CPU time limit for finding each disjoint cores (-1 == no limit).", 
					   30.0, DoubleRange(-1.0, true,  std::numeric_limits<Weight>::max(), true));
static DoubleOption opt_dsjnt_mus_cpu_lim(disjoint, "dsjnt-mus-cpu-lim",
				    "FB: CPU time limit for minimizing each *disjoint* core (-1 == no limit).",
				    10.0, DoubleRange(-1.0, true,  std::numeric_limits<Weight>::max(), true));

// Noncore and Seeding Options
static BoolOption opt_seed_learnts(seed, "seed-learnts", "FB: seed any learnts available when seeding is performed.", true);

static IntOption  opt_coretype(maxhs, "coretype", "JD: Type of constraints to learn and"
			       " feed to CPLEX (0 = core constraints only) (1 = mixed constraints).", 0, IntRange(0,1));
static IntOption   opt_seedtype(seed, "seedtype", "FB: Type of seeded constraints allowed, 0 = no seeding, 1 = cores only, 2 = also allow non-cores, 3 = also allow mixed constraints", 3, 
				IntRange(0,3));
static IntOption    opt_maxseeds(seed, "seed-max", "FB: maximum number of seeded constraints", 1024*512, 
				 IntRange(0, std::numeric_limits<int>::max()));

static IntOption opt_seed_all_limit(seed, "seed-all-limit", "If the total number of variables is <= this limit then seed all clauses CPLEX (subject to \"seed-max\" limit...CPLEX will do most of the solving but SAT might assist in finding feasible solutions", 256*3, IntRange(0, std::numeric_limits<int>::max()));

//Populate and Soln Pool
//   limit
static IntOption opt_cplex_solnpool_cap(pop, "cplex-solnpool-cap", "Set the capacity of cplex solution pool", 256, IntRange(0,2100000000));

static IntOption opt_cplex_pop_nsoln(pop, "cplex-pop-nsoln", "Set the size of cplex population pool", 512/2, IntRange(0,std::numeric_limits<int>::max()));

static DoubleOption opt_cplex_pop_cpu_lim(pop, "cplextime-pop-cpu-lim", "CPU time limit on cplex populate (-1 == no limit)", 7.5, DoubleRange(-1.0, true, std::numeric_limits<double>::max(), true));

static IntOption opt_trypop(pop, "cplex-populate", "Use cplex populate to obtain more solutions (0=never) (1=when potentially useful) (2=always)",
			    1, IntRange(0,2));
static IntOption opt_conflicts_from_ub(pop, "ub-conflicts", "FB: Generate conflicts from upper bound (0=neve) (1=when potentially useful) (2=always)", 1, IntRange(0,2));

// Sequence of Sat Options
static DoubleOption opt_optcores_cpu_per(seqOfSat, "optcores-cpu-lim",
					 "FB: CPU time limit for finding each additional core (-1 == no limit).", 
					   -1, DoubleRange(-1.0, true,  std::numeric_limits<Weight>::max(), true));
static IntOption    opt_nonopt(seqOfSat, "nonopt", "JD: Method for relaxing clauses of current "
			       "core (0 = pick a random clause, 1 = pick clause appearing in most cores"
			       ", 2 = relax a fraction of each core (set fraction with \"relaxfrac\" parameter), 3 = remove all clauses in core making next core disjoint.",
			       3, IntRange(0,3));

static DoubleOption opt_relaxfrac(seqOfSat, "relaxfrac", "FB: After accumulating frac-rampup-end clauses "
				  "relax this fraction of current core, picking clauses most frequently " 
				  "occuring in cores (must have \"nonopt=2\").", 0.3, DoubleRange(0, false, 1.0, true));
static IntOption opt_frac_rampup_start(seqOfSat, "frac-rampup-start", "FB: When nonopt = 2 (relax a fraction) relax only"
				       " one clause until this many cores accumulated", 128, IntRange(0,std::numeric_limits<int>::max()));
static IntOption opt_frac_rampup_end(seqOfSat, "frac-rampup-end", "FB: When nonopt = 2 (relax a fraction) increase "
				     "fract of core relaxed linearly to reach final \"relaxfrac\"  after this many cores accumulated",
				     512, IntRange(0,std::numeric_limits<int>::max()));
static IntOption opt_max_cores_before_cplex(seqOfSat, "max-cores-before-cplex", 
					    "FB: Force a call to Cplex after this many constraints", 
					    1024+512, IntRange(0,std::numeric_limits<int>::max()));
static DoubleOption opt_max_cpu_before_cplex(seqOfSat, "max-cpu-before-cplex",
					     "FB: Force a call to Cplex after this many CPU seconds (-1 == no limit)",
					     300.0,  DoubleRange(-1.0, true, std::numeric_limits<double>::max(), true));

static BoolOption opt_b_m_s(seqOfSat, "use-ub-mipstart",
			    "FB: Use current Sat solver upper bound model as cplex start. This entails deleting all other starts",
			    true);

static IntOption opt_sort_assumps(seqOfSat, "sort-assumps",
				  "FB: (0=don't sort, 1=place best softs to relax at top of trail, 2 reverse of 1)",
				  0, IntRange(0,2));

static BoolOption opt_improve_model(seqOfSat, "improve-model",
				    "FB: When we find a Satisfying model try to improve its cost via relaxation search",
				    false);
static BoolOption opt_find_forced(seqOfSat, "find-forced",
				  "Check for forced variables by UP or by the upper bound",
				      false);

static IntOption opt_max_size_improve_model(seqOfSat, "max-size-improve-model",
					    "FB: Don't try to improve model if the number of falsified softs"
					    " is greater than this parameter (-1 == always try)",
					    -1, IntRange(-1, std::numeric_limits<int>::max()));

static DoubleOption opt_max_cpu_improve_model(seqOfSat, "max-cpu-improve-model",
					     "FB: CPU time limit on improve SAT model phase (-1 == no limit)",
					     10,  DoubleRange(-1.0, true, std::numeric_limits<double>::max(), true));

static BoolOption opt_lp_harden(seqOfSat, "lp-harden", "Use LP version of CPLEX model to force soft clauses", true);

// Other Controls
//CPLEX Solver Options
static IntOption opt_cplex_threads(cplex, "cplex-threads", "Allow cplex to use this many threads (1 = sequential processing)", 1, IntRange(1,124));
static BoolOption opt_cplex_tune(cplex, "cplex-tune", "Use cplex parameter setting recommended by cplex-tune", false);

// //Preprocessing
static BoolOption opt_preprocess(pre, "preprocess", "Use minisat preprocessor", true);
static BoolOption opt_prepro_wcnf_eqs(pre, "wcnf-eqs", "Find and reduce equalities in wcnf", false);
static BoolOption opt_prepro_wcnf_units(pre, "wcnf-units", "Reduce wcnf by hard units", true);
static BoolOption opt_prepro_wcnf_harden(pre, "wcnf-harden", "Try to harden soft clauses by satisfiability tests", true);

// //Mutexes
static IntOption opt_prepro_mx_find_mxes(pre, "mx-find-mxes", "Detect mutually exclusive soft clauses in the input formula (0=don't, 1= find at most one false (core-mxes), 2= find at most one true (non-core-mxes), 3=1&2)", 3, IntRange(0,3));

static IntOption opt_prepro_mx_mem_lim(pre, "mx-mem-lim", "Limit on memory usage in megabytes of the mutex finder", 512*3, IntRange(0, INT32_MAX));

static IntOption opt_prepro_mx_transform(pre, "mx-transform-mxes", "Rewrite the WCNF so that soft clause mutexes are re-encoded with single relaxation variable (0=don't, 1 = re-encode core mxes, 2 = re-encode non-core muxes, 3 = 1&2)", 2, IntRange(0,3));

static BoolOption opt_prepro_simplify_and_exit(pre, "simplify-only", "Write simplified WCNF file with new suffix then exit. If mx-exit-if-no-mutexes we exit before writing if no mutexes found", false);

static BoolOption opt_prepro_mx_seed_originals(pre, "mx-seed-mxes", "Allow original softs clauses in mutexes to be seeded to CPLEX when formula is transformed", true);

static BoolOption opt_prepro_mx_constrain_hs(pre, "mx-constrain-hs", "Ensure that computed hitting sets satisfy the discovered soft clause mutexes", true);

static IntOption opt_prepro_mx_hs_use_abstraction(pre, "mx-hs-use-abs", "When using untransformed core mxes use mx abstracted hitting sets to generate cores (0=don't, 1=use abstract hs, 2=use abstracted and unabstracted hs", 2, IntRange(0, 2));

static BoolOption opt_prepro_mx_sat_preprocess(pre, "mx-sat-prepro", "Use minisat preprocessor before detecting mx softs", false);

static DoubleOption opt_prepro_mx_max_cpu(pre, "mx-cpu-lim",
                                          "Max time to spend on mx detection (-1 == no limit)",
                                          15.0, DoubleRange(-1, true, std::numeric_limits<double>::max(), true));

// //Debugging
static BoolOption opt_cplex_data_chk(debug, "cplex-data-chk", "Run cplex data checker on its input", false);
static BoolOption opt_cplex_write_model(debug, "cplex-wrt-model", "Make cplex write out each of its models", false);
static BoolOption opt_cplex_output(debug, "cplex-output", "Turn on cplex output", false);
static BoolOption opt_prepro_output(debug, "dump-prepro", "Output the preprocessed formula", false);


Params::Params() : noLimit {-1.0} {}

void Params::readOptions() {
  verbosity = opt_verb;
  prepro_output = opt_prepro_output;
  mverbosity = muser_verb;

  printBstSoln = opt_printBstSoln;
  printSoln = opt_printSoln;
  tolerance = opt_tolerance;
  min_type = opt_mintype;
  mus_cpu_lim = (opt_mus_cpu_lim > 0) ? opt_mus_cpu_lim : noLimit;
  mus_min_red = (opt_mus_min_red > 0) ? opt_mus_min_red : noLimit;
  dsjnt_phase = opt_dsjnt;
  dsjnt_cpu_per_core = (opt_dsjnt_cpu_per_core > 0) ? opt_dsjnt_cpu_per_core : noLimit;
  dsjnt_mus_cpu_lim = (opt_dsjnt_mus_cpu_lim > 0) ? opt_dsjnt_mus_cpu_lim : noLimit;
  optcores_cpu_per = (opt_optcores_cpu_per > 0) ? opt_optcores_cpu_per : noLimit;
  improve_model = opt_improve_model;
  if(opt_max_size_improve_model > 0)
    improve_model_max_size = opt_max_size_improve_model;
  else if(opt_max_size_improve_model == 0)
    improve_model = false;
  else
    improve_model_max_size = -1;
  improve_model_cpu_lim = (opt_max_cpu_improve_model > 0) ? opt_max_cpu_improve_model : noLimit;

  find_forced = opt_find_forced;

  seed_type = opt_seedtype;
  seed_max = opt_maxseeds;
  seed_learnts = opt_seed_learnts;
  seed_all_limit = opt_seed_all_limit;
  frac_to_relax = opt_relaxfrac;
  frac_rampup_start = opt_frac_rampup_start;
  frac_rampup_end = opt_frac_rampup_end;
  max_cores_before_cplex = opt_max_cores_before_cplex;
  max_cpu_before_cplex = opt_max_cpu_before_cplex;
  lp_harden = opt_lp_harden;

  sort_assumps = opt_sort_assumps;
  bestmodel_mipstart = opt_b_m_s;
  bvarDecisions = opt_bvardecisions;
  fbeq = opt_fbeq;
  fb = !fbeq;
  
  int no = opt_nonopt;
  switch(no) {
  case 0:
    coreRelaxFn = CoreRelaxFn::rand;
    break;
  case 1:
    coreRelaxFn = CoreRelaxFn::maxoccur;
    break;
  case 2:
    coreRelaxFn = CoreRelaxFn::frac;
    break;
  case 3:
    coreRelaxFn = CoreRelaxFn::dsjn;
    break;
  }

  int ct = opt_coretype;
  switch(ct) {
  case 0:
    coreType = CoreType::cores;
    break;
  case 1:
    coreType = CoreType::mixed;
    break;
  default:
    coreType = CoreType::cores;
    break;
  }

  //cplex limits
  cplex_threads = opt_cplex_threads;
  cplex_tune = opt_cplex_tune;
  cplex_data_chk = opt_cplex_data_chk;
  cplex_write_model = opt_cplex_write_model;
  cplex_output = opt_cplex_output;

  //cplex_solnpool_cap = opt_cplex_solnpool_cap;
  cplex_pop_nsoln = opt_cplex_pop_nsoln;
  cplex_pop_cpu_lim = (opt_cplex_pop_cpu_lim > 0) ? opt_cplex_pop_cpu_lim : noLimit;
  //trypop_cplextime_ub = (opt_trypop_cplextime_ub > 0) ? opt_trypop_cplextime_ub : noLimit;
  //trypop_feedtime_lb = opt_trypop_feedtime_lb;
  //  trypop = opt_trypop;
  trypop = opt_trypop;
  conflicts_from_ub = opt_conflicts_from_ub;

  if(opt_cplex_pop_nsoln == 0)
    trypop = 0;

  //preprocess
  preprocess = opt_preprocess;
  wcnf_eqs = opt_prepro_wcnf_eqs;
  wcnf_harden = opt_prepro_wcnf_harden;
  wcnf_units = opt_prepro_wcnf_units;

  simplify_and_exit = opt_prepro_simplify_and_exit;
  mx_find_mxes = opt_prepro_mx_find_mxes;
  mx_mem_limit = opt_prepro_mx_mem_lim;
  mx_transform = opt_prepro_mx_transform;
  mx_seed_originals = opt_prepro_mx_seed_originals;
  mx_constrain_hs = opt_prepro_mx_constrain_hs;
  mx_hs_use_abstraction = opt_prepro_mx_hs_use_abstraction;
  mx_sat_preprocess = opt_prepro_mx_sat_preprocess;

  mx_cpu_lim = (opt_prepro_mx_max_cpu > 0) ? opt_prepro_mx_max_cpu : noLimit;
}

Params params;
