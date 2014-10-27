/****************************************************************************************[Dimacs.h]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef Minisat_Dimacs_h
#define Minisat_Dimacs_h

#include <stdio.h>

#include "minisat/utils/ParseUtils.h"
#include "minisat/core/SolverTypes.h"

#ifndef MaxSolver_h
#include "maxhs/MaxSolver.h"
#endif

namespace Minisat {

//=================================================================================================
// DIMACS Parser:

template<class B>
static void readClause(B& in, vec<Lit>& lits) {
    int     parsed_lit, var;
    lits.clear();
    for (;;){
        parsed_lit = parseInt(in);
        if (parsed_lit == 0) break;
        var = abs(parsed_lit)-1;
        lits.push( (parsed_lit > 0) ? mkLit(var) : ~mkLit(var) );
    }
}

// JD Read clauses with weights
template<class B>
static void readClause(B& in, vec<Lit>& lits, Weight *outW) {
    bool first_time = true;
    int     parsed_lit, var;
    lits.clear();
    for (;;){
        if (first_time) {
            first_time = false;
            *outW = (Weight) parseIntegerDouble(in);
            continue;
        }
        parsed_lit = parseInt(in);
        if (parsed_lit == 0) break;
        var = abs(parsed_lit)-1;
        lits.push( (parsed_lit > 0) ? mkLit(var) : ~mkLit(var) );
    }
}

template<class B>
static bool parse_DIMACS_main(B& in, MaxSolver *S) {
    vec<Lit> lits;
    int clauses = 0;
    // JD Note that partial maxsat clauses either have weight 1 or partial_Top  
    bool clausesHaveWeights = false;
 
    for (;;){
        skipWhitespace(in);
        if (*in == EOF) break;
        else if (*in == 'p'){
            // JD it could be unweighted or weighted CNF
            if (eagerMatch(in, "p cnf")){
                int nvars = parseInt(in);
                S->setNumOrigVars(nvars);
                clauses = parseInt(in);
                S->printOutput("c Dimacs Vars", nvars);
                S->printOutput("c Dimacs Clauses", clauses);
            // JD
            }else if (eagerMatch(in, "wcnf")) {
                clausesHaveWeights = true;
                int nvars = parseInt(in);
                S->setNumOrigVars(nvars);
                clauses = parseInt(in);
                S->printOutput("c Dimacs Vars", nvars);
                S->printOutput("c Dimacs Clauses", clauses);
                if (! eagerMatch(in, "\n")) {
                    Weight top = parseIntegerDouble(in);
		    S->setHardWeight(top);
                    S->printOutput("c Dimacs Top", top);
		}
            }else{
                S->printErrorAndExit("c PARSE ERROR! Unexpected char");
            }
        } else if (*in == 'c' || *in == 'p')
            skipLine(in);
        else{
            // JD parse the weights of clauses as well (default weight 1) 
            Weight w = 1;   
            clausesHaveWeights ? readClause(in, lits, &w) : readClause(in, lits);
            if (S->addClause(lits, w)) {
                return true;
            }
        }
    }
    return false;
}

// Inserts problem into solver.
//
static bool parse_DIMACS(gzFile input_stream, MaxSolver *S) {
    StreamBuffer in(input_stream);
    return parse_DIMACS_main(in, S); }

}

#endif
