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
  const double noTimeLimit;
  int min_type;
  double mus_cpu_lim;
  double mus_lits_per_sec;
  bool dsjnt_phase;
  double dsjnt_cpu_per_core;
  double dsjnt_mus_cpu_lim;
  double optcores_cpu_per;
  bool fbeq;
  bool fb;
  bool printBstSoln;
  bool printSoln;

  CoreType coreType;
  CoreRelaxFn coreRelaxFn;

  SeedType seedType;
  int seed_max;
  bool bvarDecisions;
  double frac_to_relax;
  int frac_rampup_start;
  int frac_rampup_end;
  int max_before_cplex;
  
  bool nonopt_rand;
  bool nonopt_maxoccur;
  bool nonopt_frac;

  bool greedy_cores_only;

  int mip_threads;
  bool mip_data_chk;
  bool mip_write_model;
  bool mip_output;

  std::string instance_file_name;
};

extern Params params;

#endif
