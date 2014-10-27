/***********[Cplex.h]
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

#ifndef CPLEX_H
#define CPLEX_H

#include "maxhs/core/MaxSolverTypes.h"
#include "minisat/core/SolverTypes.h"
#include <map>
#include <ilcplex/ilocplex.h> 
#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <set>

#define toString(x) (static_cast<ostringstream*>( &(ostringstream() <<  x) )->str())

ILOSTLBEGIN

using namespace Minisat;
using namespace std;

namespace MaxHS {

class Cplex {
private:

    IloEnv env;
    IloModel model;
    IloCplex cplex;
    
    IloRangeArray constraints;
    IloBoolVarArray bool_variables;
    IloNumArray varcosts; 
  
    int n_variables; 
    map<int, int> satvar_to_cplexvar;
    vector<int> cplexvar_to_satvar;

    int  cplex_nsoln;
    int  cplex_poolintensity;
    int  cplex_poolreplace;
    int  cplex_poolcapacity;
    int  cplex_populatelim;
    bool cplex_threads_off;

public:
    int numSolves;
    double totalTime;
    int numNonCoreConstraints;
    int maxNonCoreLength;
    int minNonCoreLength;
    int totalNonCoreLength;
    int totalNumOptSolutions;

    Cplex();
    ~Cplex();

    void initCplex(const vector<int> &satvars, const vector<Weight> &costs);
    bool add_clausal_constraint(vector<Lit> &con); 
    void add_impl_constraint(Lit blit, vector<Lit> &con); 
    Weight solve(vector<vector<Lit> > &solution); 
    bool approx(vector<Lit> &solution);
    void printInfeasibility();
    int getMaxNSolns() const;

private:
    bool getSolutionAtIndex(vector<Lit> &solution, int solnIndex); 
};
inline int Cplex::getMaxNSolns() const { return cplex_nsoln; }

} //namespace MaxHS
#endif


