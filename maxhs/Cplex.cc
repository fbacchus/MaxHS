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

#ifndef CPLEX_H
#include "maxhs/Cplex.h"
#endif

#include "minisat/utils/Options.h"

#include "minisat/utils/System.h"

#include <iostream>
#include <stdexcept>

static const char* category_mwhs_cplex = "Cplex";

static IntOption     opt_nsoln              (category_mwhs_cplex, "nsoln", "Ask CPLEX for this number of solutions.", 1, IntRange(1, INT32_MAX));
static IntOption     opt_poolintensity      (category_mwhs_cplex, "intensity", "CPLEX SolnPoolIntensity parameter.", 2, IntRange(0, 4));
// These defaults were chosen to collect the 10 most diverse solutions, from a maximum of 100 generated.
static IntOption     opt_poolreplace        (category_mwhs_cplex, "replace", "CPLEX SolnPoolReplace parameter.", 2, IntRange(0, 2));
static IntOption     opt_poolcapacity       (category_mwhs_cplex, "capacity", "CPLEX SolnPoolCapacity parameter.", 10, IntRange(0, INT32_MAX));
static IntOption     opt_populatelim        (category_mwhs_cplex, "poplim", "CPLEX PopulateLim parameter.", 100, IntRange(0, INT32_MAX));
static BoolOption    opt_threads_off        (category_mwhs_cplex, "threads-off", "Set the CPLEX Threads parameter to 1.", true); 

Cplex::Cplex() :
    n_variables(0)
    , cplex_nsoln        (opt_nsoln)
    , cplex_poolintensity(opt_poolintensity)
    , cplex_poolreplace  (opt_poolreplace)
    , cplex_poolcapacity (opt_poolcapacity)
    , cplex_populatelim  (opt_populatelim)
    , cplex_threads_off  (opt_threads_off)
    , numSolves          (0)
    , totalTime          (0) 
    , numNonCoreConstraints (0)
    , maxNonCoreLength(-1)
    , minNonCoreLength(-1)
    , totalNonCoreLength(0)
    , totalNumOptSolutions (0)
{
    //env.setNormalizer(false); 
    env.setOut(env.getNullStream());
    env.setWarning(env.getNullStream());
    env.setError(env.getNullStream());

   
    model = IloModel(env);
    bool_variables = IloBoolVarArray(env);
    varcosts = IloNumArray(env);
    constraints = IloRangeArray(env);
}

Cplex::~Cplex(){
    bool_variables.end();
    constraints.end();
    varcosts.end();
    env.end();
}

// costs specifies the cost incurred if the satvar is truthified (set to 1)
void Cplex::initCplex(vector<int> &satvars, vector<Weight> &costs){
   
    for (size_t i = 0; i < satvars.size(); i++) {
        int satvar = satvars[i];
        satvar_to_cplexvar[satvar] = n_variables++;
        cplexvar_to_satvar.push_back(satvar);
        bool_variables.add(IloBoolVar(env));
        varcosts.add(costs[i]);
    }
      
    model.add(bool_variables);
    model.add(constraints);

    model.add(IloObjective(env, IloScalProd(varcosts, bool_variables))); 

    cplex = IloCplex(env);
    cplex.extract(model);

    cplex.setParam(IloCplex::EpAGap, 0);
    cplex.setParam(IloCplex::EpGap, 0);

    if (cplex_threads_off) {
        cplex.setParam(IloCplex::Threads, 1);
    }
    if (cplex_nsoln > 1) {
        cplex.setParam(IloCplex::SolnPoolCapacity, cplex_poolcapacity);
        cplex.setParam(IloCplex::SolnPoolReplace, cplex_poolreplace);
        cplex.setParam(IloCplex::SolnPoolIntensity, cplex_poolintensity);
        cplex.setParam(IloCplex::PopulateLim, cplex_populatelim);
        cplex.setParam(IloCplex::SolnPoolAGap, 0); // so only optimal solutions are accumulated
    }

    //if (timeout > 0) cplex.setParam(IloCplex::TiLim, timeout);
    //if (!presolve) cplex.setParam(IloCplex::PreInd, CPX_OFF);
    /*cplex.setParam(IloCplex::RootAlg, 0);
    cplex.setParam(IloCplex::MIPEmphasis, 0);
    cplex.setParam(IloCplex::HeurFreq, 0);
    cplex.setParam(IloCplex::VarSel, 0); 
    cplex.setParam(IloCplex::NodeSel, 1); 
    cplex.setParam(IloCplex::AdvInd, 0);*/
    /* 
      cplex.setParam(IloCplex::AggInd, 0);
      cplex.setParam(IloCplex::Reduce, 0);
      cplex.setParam(IloCplex::PrePass, 0);
      cplex.setParam(IloCplex::DepInd, 0);
    */
}

bool Cplex::add_clausal_constraint(vec<Lit> &theCon){
    IloExpr expr(env);
    int numNeg = 0;
    for(int i = 0; i < theCon.size(); i++) {
        int cplexvarindex = satvar_to_cplexvar[var(theCon[i])];
        IloBoolVar &boolvar = bool_variables[cplexvarindex];
        if (sign(theCon[i])) {
            expr -= boolvar;
            numNeg++; 
        } else {
            expr += boolvar;
        }
    }

    if (numNeg > 0) {
        numNonCoreConstraints++;
        totalNonCoreLength += theCon.size();
        minNonCoreLength = (minNonCoreLength < 0 || (theCon.size() < minNonCoreLength)) ? theCon.size() : minNonCoreLength;
        maxNonCoreLength = (maxNonCoreLength < 0 || (theCon.size() > maxNonCoreLength)) ? theCon.size() : maxNonCoreLength;
    }
    IloRange con(env, 1-numNeg, expr);
    constraints.add(con);
    model.add(con);

    return (numNeg > 0);
}
void Cplex::add_impl_constraint(Lit blit, vec<Lit> &theCon){
    IloExpr expr(env);
    int k = -theCon.size();
    IloBoolVar blitvar = bool_variables[satvar_to_cplexvar[var(blit)]];
    if (sign(blit)) {
        expr += k * (1 - blitvar);
        //expr -= k * blitvar;
    } else {
        expr += k * blitvar;
    }
    for(int i = 0; i < theCon.size(); i++) {
        int cplexvarindex = satvar_to_cplexvar[var(theCon[i])];
        IloBoolVar &boolvar = bool_variables[cplexvarindex];
        if (sign(theCon[i])) {
            expr += (1 - boolvar);
        } else {
            expr += boolvar;
        }
    }

    IloRange con(env, 0, expr);
    constraints.add(con);
    model.add(con);
}

bool Cplex::approx(vector<Lit> &solution) {

    cplex.setParam(IloCplex::MIPEmphasis, CPX_MIPEMPHASIS_FEASIBILITY);
    cplex.setParam(IloCplex::IntSolLim, 1);
    double startTime = cpuTime(); 
    solution.clear();
    bool result = true;

    if (cplex.solve()) {
        IloCplex::CplexStatus status = cplex.getCplexStatus();
        if (status != CPXMIP_SOL_LIM && status != CPX_STAT_OPTIMAL && status != CPXMIP_OPTIMAL_TOL) {
            result = false;
        } else if (!getSolutionAtIndex(solution, -1)) {
            result = false;
            solution.clear();
        }
    } else {
        result = false;
    }
    totalTime += cpuTime() - startTime;
    return result; 
}

Weight Cplex::solve(vector<vector<Lit> > &solutions) {   
    IloNum objval = -1;
    solutions.clear();
    numSolves++;
    double startTime = cpuTime();
   
    cplex.setParam(IloCplex::MIPEmphasis, CPX_MIPEMPHASIS_OPTIMALITY);
    cplex.setParam(IloCplex::IntSolLim, 2100000000);

    if (cplex.solve()) {
        IloCplex::CplexStatus status = cplex.getCplexStatus();
        // CPXMIP_OPTIMAL_TOP means that an optimal solution was found within the EpGap or EpAGap
        if (status == CPX_STAT_OPTIMAL || status == CPXMIP_OPTIMAL_TOL) {
            objval = cplex.getObjValue();
            if (cplex_nsoln > 1) {
                cplex.populate(); 
            }
            int num = cplex_nsoln > 1 ? cplex.getSolnPoolNsolns() : 1;
            totalNumOptSolutions += min(cplex_nsoln, num);
            if (num > 0) {
                int maxSize = min(num, cplex_nsoln);
                solutions.resize(maxSize);
                for (int i = 0; (i < maxSize && objval >= 0); i++) {
                    if (!getSolutionAtIndex(solutions[i], cplex_nsoln > 1 ? i : -1)) {
                        objval = -1;
                        solutions.resize(i);
                    }
                }
                if (cplex_nsoln > 1) { 
                    cplex.delSolnPoolSolns(0, num-1);
                } 
            } else {
                objval = -1;
            }
        } else {
            objval = -1;
            //printf("status = %d\n", status); fflush(stdout);
        }
    } /*else {
        printf("status = %d\n", cplex.getCplexStatus()); fflush(stdout);

    }*/
    totalTime += cpuTime() - startTime;
    
    return objval;
}

bool Cplex::getSolutionAtIndex(vector<Lit> &solution, int solnIndex) {
    bool success = true;
    for (int i = 0; i < bool_variables.getSize(); i++) {
        IloNum val = cplex.getValue(bool_variables[i], solnIndex);
        if ((double)val > 0.99) {
            solution.push_back(mkLit(cplexvar_to_satvar[i], false));
        }
        else if ((double)val < 0.01) {
            solution.push_back(mkLit(cplexvar_to_satvar[i], true));
        } else {
            success = false;
        }
    }
    return success;
}

void Cplex::printInfeasibility() {
 
    cout << model << endl;
    IloConstraintArray infeas(env);
    infeas.add(constraints);
    IloNumArray prefs(env); 
    for (IloInt i = 0; i < infeas.getSize(); i++) {
        prefs.add(1.0);
    }
    cplex.refineConflict(infeas, prefs);
    IloCplex::ConflictStatusArray conflict = cplex.getConflict(infeas);
    env.getImpl()->useDetailedDisplay(IloTrue);
    cout << "Conflict: " << endl;
    for (IloInt i = 0; i < infeas.getSize(); i++) {
        if (conflict[i] == IloCplex::ConflictMember) cout << "Proved: " << infeas[i] << endl;
        if (conflict[i] == IloCplex::ConflictPossibleMember) cout << "Possible: " << infeas[i] << endl;
    }
    for (int i = 0; i < bool_variables.getSize(); i++) {
        cout << "cplex var " << bool_variables[i] << " = sat var " << cplexvar_to_satvar[i] << endl;
    }
    prefs.end();
    infeas.end();
}
