/***********[Params.h]
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
#ifndef PARAMS_h
#define PARAMS_h
#include <string>
#include "maxhs/core/MaxSolverTypes.h"


class Params {
  //MaxSolver helper class to manage its settable parameters. 
  //see MaxSlvParams.cc for description
public:
  Params();
  ~Params() {}
  void readOptions();
  int verbosity;
  int mverbosity;
  const double noLimit;
  int min_type;
  double mus_cpu_lim;
  double mus_min_red;
  bool dsjnt_phase;
  double dsjnt_cpu_per_core;
  double dsjnt_mus_cpu_lim;
  double optcores_cpu_per;

  bool fbeq;
  bool fb;
  bool printOptions;
  bool printBstSoln;
  bool printSoln;
  double tolerance;

  CoreType coreType;
  CoreRelaxFn coreRelaxFn;

  int seed_type;
  int seed_max;
  bool seed_learnts;
  int seed_all_limit;
  bool bvarDecisions;
  double frac_to_relax;
  int frac_rampup_start;
  int frac_rampup_end;
  int max_cores_before_cplex;
  int max_cpu_before_cplex;
  bool lp_harden;

  int sort_assumps;
  bool bestmodel_mipstart;
  bool nonopt_rand;
  bool nonopt_maxoccur;
  bool nonopt_frac;

  double improve_model_cpu_lim;
  int improve_model_max_size;
  bool improve_model;
  bool find_forced;

  double cplex_min_ticks;
  int cplex_threads;
  bool cplex_tune;
  bool cplex_data_chk;
  bool cplex_write_model;
  bool cplex_output;

  int cplex_pop_nsoln;
  double cplex_pop_cpu_lim;
  //int cplex_solnpool_cap;

  //double trypop_cplextime_ub;
  //double trypop_feedtime_lb;
  int trypop;
  int conflicts_from_ub;
  bool prepro_output;
  bool preprocess;
  bool wcnf_eqs;
  bool wcnf_harden;
  bool wcnf_units;

  bool simplify_and_exit;
  int mx_find_mxes;
  int mx_mem_limit;
  int mx_transform;
  bool mx_seed_originals;

  bool mx_constrain_hs;
  int mx_hs_use_abstraction;
  bool mx_sat_preprocess;
  double mx_cpu_lim;

  std::string instance_file_name;
};

extern Params params;

#endif
