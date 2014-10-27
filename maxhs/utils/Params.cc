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

using namespace Minisat;
static const char* maxhs = "A: General MaxHS";
static const char* disjoint = "B: Disjoint Phase";
static const char* seed = "C: Seeding";
static const char* seqOfSat = "D: Sequence of Sat";
static const char* muser = "E: Core Minimization";
static const char* greedy = "F: Greedy Solver";
static const char* cplex = "G: MIP Solver";
static const char* debug = "H: Debugging";


//General Controls
static IntOption    opt_verb(maxhs, "verb", "Verbosity level (0=silent, 1=some, 2=more, "
			     "3=debugging output, 4=more debugging output).", 1, IntRange(0, 4));
static BoolOption   opt_bvardecisions(maxhs, "bvardecisions", "FB: make bvars decision variables.", false);
static BoolOption   opt_fbeq(maxhs, "fbeq", "FB: Use FbEq theory. Independent of \"coretype\"", false);
static BoolOption opt_printBstSoln(debug, "printBstSoln", "Print best solution found", false);
static BoolOption opt_printSoln(debug, "printSoln", "Print solution", true);


//Muser Controls
static IntOption    opt_mintype(muser, "mintype", "JD: 0 = no minimization of " 
				"constraints/cores,  1 = Use Muser", 1, IntRange(0, 1));
static DoubleOption opt_mus_cpu_lim(muser, "mus-cpu-lim",
				    "FB: CPU time limit for minimizing each core (<= 0 == no limit).", 
				    2.5, DoubleRange(-1.0, true,  std::numeric_limits<Weight>::max(), true));
static DoubleOption opt_mus_lits_per_sec(muser, "mus-litsper-sec",
					 "FB: Run muser only if it can remove at least this "
					 "many lits per CPU sec. (<= 0 == no limit).", 
					 10.0, DoubleRange(-1.0, true,  std::numeric_limits<Weight>::max(), true));
static IntOption muser_verb(muser, "mverb", "Muser verbosity level (0=silent, 1=some, 2=more,3=debugging output, 4=more debugging output).", 1, IntRange(0, 4));


//Disjoint Phase Controls
static BoolOption   opt_dsjnt(disjoint, "dsjnt", "JD: Find disjoint cores in a first phase.", true);

static DoubleOption opt_dsjnt_cpu_per_core(disjoint, "dsjnt-cpu-lim",
					   "FB: CPU time limit for finding each disjoint cores (<= 0 == no limit).", 
					   30.0, DoubleRange(-1.0, true,  std::numeric_limits<Weight>::max(), true));
static DoubleOption opt_dsjnt_mus_cpu_lim(disjoint, "dsjnt-mus-cpu-lim",
				    "FB: CPU time limit for minimizing each *disjoint* core (<= 0 == no limit).", 
				    20.0, DoubleRange(-1.0, true,  std::numeric_limits<Weight>::max(), true));


// Noncore and Seeding Options
static IntOption    opt_coretype(maxhs, "coretype", "JD: Type of constraints to learn and"
				 "feed to CPLEX (0 = core constraints only) (1 = mixed constraints).", 0, IntRange(0,1));
static IntOption   opt_seedtype(seed, "seedtype", "FB: Type of seeded constraints allowed, 0 = no seeding, 1 = cores only, 2 = mixed constraints", 2, 
				IntRange(0,2));
static IntOption    opt_maxseeds(seed, "seed-max", "FB: maximum number of seeded constraints", 1024*512, 
				 IntRange(0, std::numeric_limits<int>::max()));

// Sequence of Sat Options
static DoubleOption opt_optcores_cpu_per(seqOfSat, "optcores-cpu-lim",
					 "FB: CPU time limit for finding each additional core (<= 0 == no limit).", 
					   -1, DoubleRange(-1.0, true,  std::numeric_limits<Weight>::max(), true));
static IntOption    opt_nonopt(seqOfSat, "nonopt", "JD: Method for relaxing clauses of current "
			       "core (0 = pick a random clause, 1 = pick clause appearing in most cores"
			       ", 2 = relax a fraction of each core (set fraction with \"relaxfrac\" parameter).",
			       2, IntRange(0,2));
static DoubleOption opt_relaxfrac(seqOfSat, "relaxfrac", "FB: After accumulating frac-rampup-end clauses "
				  "relax this fraction of current core, picking clauses most frequently " 
				  "occuring in cores (must have \"nonopt=2\").", 0.3, DoubleRange(0, false, 1.0, true));
static IntOption opt_frac_rampup_start(seqOfSat, "frac-rampup-start", "FB: When nonopt = 2 (relax a fraction) relax only"
				       " one clause until this many cores accumulated", 128, IntRange(0,std::numeric_limits<int>::max()));
static IntOption opt_frac_rampup_end(seqOfSat, "frac-rampup-end", "FB: When nonopt = 2 (relax a fraction) relax "
				     "relaxfac of core after this many cores accumulated", 512, IntRange(0,std::numeric_limits<int>::max()));
static IntOption opt_max_before_cplex(seqOfSat, "max-before-cplex", "FB: Force a call to Cplex after this many constraints", 1024+512, IntRange(0,std::numeric_limits<int>::max()));

//Greedy Solver Options
static BoolOption opt_greedy_cores(greedy, "greedy-cores", "FB: Give only core constraints to the greedy solver", true);
// Other Controls

//MIP Solver Options
static IntOption opt_mip_threads(cplex, "mip-threads", "Allow the MIPs solver to use this many threads (1 = sequential processing)", 1, IntRange(1,124)); 

//Debugging
static BoolOption opt_mip_data_chk(debug, "mip-data-chk", "Run the MIP solver's data checker on its input", false);
static BoolOption opt_mip_write_model(debug, "mip-wrt-model", "Make the MIP solver write out each of its models", false);
static BoolOption opt_mip_output(debug, "mip-output", "Turn on the MIP solver's output", false);


Params::Params() : noTimeLimit {-1.0} {}

void Params::readOptions() {
  verbosity = opt_verb;
  printBstSoln = opt_printBstSoln;
  printSoln = opt_printSoln;
  min_type = opt_mintype;
  mus_cpu_lim = (opt_mus_cpu_lim > 0) ? opt_mus_cpu_lim : noTimeLimit;
  mus_lits_per_sec = (opt_mus_lits_per_sec > 0) ? opt_mus_lits_per_sec : noTimeLimit;
  dsjnt_phase = opt_dsjnt;
  dsjnt_cpu_per_core = (opt_dsjnt_cpu_per_core > 0) ? opt_dsjnt_cpu_per_core : noTimeLimit;
  dsjnt_mus_cpu_lim = (opt_dsjnt_mus_cpu_lim > 0) ? opt_dsjnt_mus_cpu_lim : noTimeLimit;
  optcores_cpu_per = (opt_optcores_cpu_per > 0) ? opt_optcores_cpu_per : noTimeLimit;
  int st = opt_seedtype;
  switch(st) {
  case 0:
    seedType = SeedType::none;
    break;
  case 1:
    seedType = SeedType::cores;
    break;
  case 2:
    seedType = SeedType::mixed;
    break;
  }
  seed_max = opt_maxseeds;
  frac_to_relax = opt_relaxfrac;
  frac_rampup_start = opt_frac_rampup_start;
  frac_rampup_end = opt_frac_rampup_end;
  max_before_cplex = opt_max_before_cplex;
  bvarDecisions = opt_bvardecisions;
  fbeq = opt_fbeq;
  fb = !fbeq;
  mverbosity = muser_verb;
  greedy_cores_only = opt_greedy_cores;
  
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

  mip_threads = opt_mip_threads;
  mip_data_chk = opt_mip_data_chk;
  mip_write_model = opt_mip_write_model;
  mip_output = opt_mip_output;
}

Params params;
