/***************************************************************************************[Solver.cc]
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

#include <math.h>
#include <iostream>
#include "maxhs/utils/io.h"
#include "minisat/mtl/Alg.h"
#include "minisat/mtl/Sort.h"
#include "minisat/utils/System.h"
#include "minisat/core/Solver.h"

using namespace Minisat;
using std::cout;
//=================================================================================================
// Options:


static const char* _cat = "J: MINISAT solver";

static DoubleOption  opt_var_decay         (_cat, "var-decay",   "The variable activity decay factor",            0.95,     DoubleRange(0, false, 1, false));
static DoubleOption  opt_clause_decay      (_cat, "cla-decay",   "The clause activity decay factor",              0.999,    DoubleRange(0, false, 1, false));
static DoubleOption  opt_random_var_freq   (_cat, "rnd-freq",    "The frequency with which the decision heuristic tries to choose a random variable", 0, DoubleRange(0, true, 1, true));
static DoubleOption  opt_random_seed       (_cat, "rnd-seed",    "Used by the random variable selection",         91648253, DoubleRange(0, false, HUGE_VAL, false));
static IntOption     opt_ccmin_mode        (_cat, "ccmin-mode",  "Controls conflict clause minimization (0=none, 1=basic, 2=deep)", 2, IntRange(0, 2));
static IntOption     opt_phase_saving      (_cat, "phase-saving", "Controls the level of phase saving (0=none, 1=limited, 2=full)", 2, IntRange(0, 2));
static BoolOption    opt_rnd_init_act      (_cat, "rnd-init",    "Randomize the initial activity", false);
static BoolOption    opt_luby_restart      (_cat, "luby",        "Use the Luby restart sequence", true);
static IntOption     opt_restart_first     (_cat, "rfirst",      "The base restart interval", 100, IntRange(1, INT32_MAX));
static DoubleOption  opt_restart_inc       (_cat, "rinc",        "Restart interval increase factor", 2, DoubleRange(1, false, HUGE_VAL, false));
static DoubleOption  opt_garbage_frac      (_cat, "gc-frac",     "The fraction of wasted memory allowed before a garbage collection is triggered",  0.20, DoubleRange(0, false, HUGE_VAL, false));
static IntOption     opt_min_learnts_lim   (_cat, "min-learnts", "Minimum learnt clause limit",  0, IntRange(0, INT32_MAX));
static IntOption     opt_sat_verb          (_cat, "sverb",   "Verbosity level (0=silent, 1=some, 2=more).", 0, IntRange(0, 2));
static IntOption     opt_assump_verb       (_cat, "averb",   "Verbosity level for new assumption processing (0=silent, 1=some, 2=more).", 0, IntRange(0, 2));
static BoolOption    opt_assumption_2nd (_cat, "assump-reprocess", "Reprocess assumption conflict with separate assumption decision levels", true);


//=================================================================================================
// Constructor/Destructor:


Solver::Solver() :

    // Parameters (user settable):
    //
    verbosity        (opt_sat_verb)
    , var_decay        (opt_var_decay)
    , clause_decay     (opt_clause_decay)
    , random_var_freq  (opt_random_var_freq)
    , random_seed      (opt_random_seed)
    , luby_restart     (opt_luby_restart)
    , assump_2nd_process (opt_assumption_2nd)
    , averbosity       (opt_assump_verb)
    , ccmin_mode       (opt_ccmin_mode)
    , phase_saving     (opt_phase_saving)
    , rnd_pol          (false)
    , rnd_init_act     (opt_rnd_init_act)
    , garbage_frac     (opt_garbage_frac)
    , min_learnts_lim  (opt_min_learnts_lim)
    , restart_first    (opt_restart_first)
    , restart_inc      (opt_restart_inc)

    // Parameters (the rest):
    //
    , learntsize_factor((double)1/(double)3), learntsize_inc(1.1)

    // Parameters (experimental):
    //
    , learntsize_adjust_start_confl (100)
    , learntsize_adjust_inc         (1.5)

    // Statistics: (formerly in 'SolverStats')
    //
    , solves(0), starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0)
    , dec_vars(0), num_clauses(0), num_learnts(0), clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)
    , n_assump_conflicts(0)
    , assump_saved (0)
    , watches            (WatcherDeleted(ca))
    , order_heap         (VarOrderLt(activity))
    , ok                 (true)
    , remove_satisfied   (true)
    , cla_inc            (1)
    , var_inc            (1)
    , qhead              (0)
    , simpDB_assigns     (-1)
    , simpDB_props       (0)
    , progress_estimate  (0)
    , next_var           (0)

    // Resource constraints:
    //
    , conflict_budget    (-1)
    , propagation_budget (-1)
    , asynch_interrupt   (false)
{}


Solver::~Solver()
{
}


//=================================================================================================
// Minor methods:


// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var Solver::newVar(lbool upol, bool dvar)
{
    Var v;
    if (free_vars.size() > 0){
        v = free_vars.last();
        free_vars.pop();
    }else
        v = next_var++;

    watches  .init(mkLit(v, false));
    watches  .init(mkLit(v, true ));
    assigns  .insert(v, l_Undef);
    vardata  .insert(v, mkVarData(CRef_Undef, 0, l_Undef));
    activity .insert(v, rnd_init_act ? drand(random_seed) * 0.00001 : 0);
    seen     .insert(v, 0);
    polarity .insert(v, true);
    user_pol .insert(v, upol);
    decision .reserve(v);
    trail    .capacity(v+1);
    setDecisionVar(v, dvar);
    return v;
}


// Note: at the moment, only unassigned variable will be released (this is to avoid duplicate
// releases of the same variable).
void Solver::releaseVar(Lit l)
{
    if (value(l) == l_Undef){
        addClause(l);
        released_vars.push(var(l));
    }
}


bool Solver::addClause_(vec<Lit>& ps)
{
    assert(decisionLevel() == 0);
    if (!ok) return false;

    // Check if clause is satisfied and remove false/duplicate literals:
    sort(ps);
    Lit p; int i, j;
    for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
        if (value(ps[i]) == l_True || ps[i] == ~p)
            return true;
        else if (value(ps[i]) != l_False && ps[i] != p)
            ps[j++] = p = ps[i];
    ps.shrink(i - j);

    if (ps.size() == 0)
        return ok = false;
    else if (ps.size() == 1){
        uncheckedEnqueue(ps[0]);
        return ok = (propagate() == CRef_Undef);
    }else{
        CRef cr = ca.alloc(ps, false);
        clauses.push(cr);
        attachClause(cr);
    }

    return true;
}


void Solver::attachClause(CRef cr){
    const Clause& c = ca[cr];
    assert(c.size() > 1);
    watches[~c[0]].push(Watcher(cr, c[1]));
    watches[~c[1]].push(Watcher(cr, c[0]));
    if (c.learnt()) num_learnts++, learnts_literals += c.size();
    else            num_clauses++, clauses_literals += c.size();
}


void Solver::detachClause(CRef cr, bool strict){
    const Clause& c = ca[cr];
    assert(c.size() > 1);

    // Strict or lazy detaching:
    if (strict){
        remove(watches[~c[0]], Watcher(cr, c[1]));
        remove(watches[~c[1]], Watcher(cr, c[0]));
    }else{
        watches.smudge(~c[0]);
        watches.smudge(~c[1]);
    }

    if (c.learnt()) num_learnts--, learnts_literals -= c.size();
    else            num_clauses--, clauses_literals -= c.size();
}


void Solver::removeClause(CRef cr) {
    Clause& c = ca[cr];
    detachClause(cr);
    // Don't leave pointers to free'd memory!
    if (locked(c)) vardata[var(c[0])].reason = CRef_Undef;
    c.mark(1);
    ca.free(cr);
}


bool Solver::satisfied(const Clause& c) const {
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True)
            return true;
    return false; }


// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//
void Solver::cancelUntil(int level) {
    if (decisionLevel() > level){
        for (int c = trail.size()-1; c >= trail_lim[level]; c--){
            Var      x  = var(trail[c]);
            assigns [x] = l_Undef;
            if (phase_saving > 1 || (phase_saving == 1 && c > trail_lim.last()))
                polarity[x] = sign(trail[c]);
            insertVarOrder(x); }
        qhead = trail_lim[level];
        trail.shrink(trail.size() - trail_lim[level]);
        trail_lim.shrink(trail_lim.size() - level);
    } }


//=================================================================================================
// Major methods:


Lit Solver::pickBranchLit()
{
    Var next = var_Undef;
    // Random decision:
    if (drand(random_seed) < random_var_freq && !order_heap.empty()){
        next = order_heap[irand(random_seed,order_heap.size())];
        if (value(next) == l_Undef && decision[next])
            rnd_decisions++; }

    // Activity based decision:
    while (next == var_Undef || value(next) != l_Undef || !decision[next])
        if (order_heap.empty()){
            next = var_Undef;
            break;
        }else
            next = order_heap.removeMin();

    // Choose polarity based on different polarity modes (global or per-variable):
    if (next == var_Undef)
        return lit_Undef;
    else if (user_pol[next] != l_Undef)
        return mkLit(next, user_pol[next] == l_True);
    else if (rnd_pol)
        return mkLit(next, drand(random_seed) < 0.5);
    else
        return mkLit(next, polarity[next]);
}


/*_________________________________________________________________________________________________
  |
  |  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
  |
  |  Description:
  |    Analyze conflict and produce a reason clause.
  |
  |    Pre-conditions:
  |      * 'out_learnt' is assumed to be cleared.
  |      * Current decision level must be greater than root level.
  |
  |    Post-conditions:
  |      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
  |      * If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the
  |        rest of literals. There may be others from the same level though.
  |
  |________________________________________________________________________________________________@*/
void Solver::analyze(CRef confl, vec<Lit>& out_learnt, int& out_btlevel)
{
    int pathC = 0;
    Lit p     = lit_Undef;

    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    int index   = trail.size() - 1;

    do{
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        Clause& c = ca[confl];

        if (c.learnt())
            claBumpActivity(c);

        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
            Lit q = c[j];

            if (!seen[var(q)] && level(var(q)) > 0){
                varBumpActivity(var(q));
                seen[var(q)] = 1;
                if (level(var(q)) >= decisionLevel())
                    pathC++;
                else
                    out_learnt.push(q);
            }
        }

        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        p     = trail[index+1];
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

    }while (pathC > 0);
    out_learnt[0] = ~p;

    // Simplify conflict clause:
    //
    int i, j;
    out_learnt.copyTo(analyze_toclear);
    if (ccmin_mode == 2){
        for (i = j = 1; i < out_learnt.size(); i++)
            if (reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i]))
                out_learnt[j++] = out_learnt[i];

    }else if (ccmin_mode == 1){
        for (i = j = 1; i < out_learnt.size(); i++){
            Var x = var(out_learnt[i]);

            if (reason(x) == CRef_Undef)
                out_learnt[j++] = out_learnt[i];
            else{
                Clause& c = ca[reason(var(out_learnt[i]))];
                for (int k = 1; k < c.size(); k++)
                    if (!seen[var(c[k])] && level(var(c[k])) > 0){
                        out_learnt[j++] = out_learnt[i];
                        break; }
            }
        }
    }else
        i = j = out_learnt.size();

    max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    tot_literals += out_learnt.size();

    // Find correct backtrack level:
    //
    if (out_learnt.size() == 1)
        out_btlevel = 0;
    else{
        int max_i = 1;
        // Find the first literal assigned at the next-highest level:
        for (int i = 2; i < out_learnt.size(); i++)
            if (level(var(out_learnt[i])) > level(var(out_learnt[max_i])))
                max_i = i;
        // Swap-in this literal at index 1:
        Lit p             = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1]     = p;
        out_btlevel       = level(var(p));
    }

    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)
}


// Check if 'p' can be removed from a conflict clause.
bool Solver::litRedundant(Lit p)
{
    enum { seen_undef = 0, seen_source = 1, seen_removable = 2, seen_failed = 3 };
    assert(seen[var(p)] == seen_undef || seen[var(p)] == seen_source);
    assert(reason(var(p)) != CRef_Undef);

    Clause*               c     = &ca[reason(var(p))];
    vec<ShrinkStackElem>& stack = analyze_stack;
    stack.clear();

    for (uint32_t i = 1; ; i++){
        if (i < (uint32_t)c->size()){
            // Checking 'p'-parents 'l':
            Lit l = (*c)[i];

            // Variable at level 0 or previously removable:
            if (level(var(l)) == 0 || seen[var(l)] == seen_source || seen[var(l)] == seen_removable){
                continue; }

            // Check variable can not be removed for some local reason:
            if (reason(var(l)) == CRef_Undef || seen[var(l)] == seen_failed){
                stack.push(ShrinkStackElem(0, p));
                for (int i = 0; i < stack.size(); i++)
                    if (seen[var(stack[i].l)] == seen_undef){
                        seen[var(stack[i].l)] = seen_failed;
                        analyze_toclear.push(stack[i].l);
                    }

                return false;
            }

            // Recursively check 'l':
            stack.push(ShrinkStackElem(i, p));
            i  = 0;
            p  = l;
            c  = &ca[reason(var(p))];
        }else{
            // Finished with current element 'p' and reason 'c':
            if (seen[var(p)] == seen_undef){
                seen[var(p)] = seen_removable;
                analyze_toclear.push(p);
            }

            // Terminate with success if stack is empty:
            if (stack.size() == 0) break;

            // Continue with top element on stack:
            i  = stack.last().i;
            p  = stack.last().l;
            c  = &ca[reason(var(p))];

            stack.pop();
        }
    }

    return true;
}

/*----------------------------------------------------------------------------------------
  analyzeFinal. These are special versions of analyze designed to compute a conflict over
  the assumptions. That is a conflict clause containing only negated assumption literals.

  In search, analyzeFinal is called in two places. First to compute a conflict when all
  assumptions have been set as decisions at level 1, and second to recompute (reprocess)
  a conflict when assumptions as decisions at separate levels.

  The basic assumption is that all non-implied literals on the trail
  are positive assumption literals.

  There are options
  1. All decision conflict---does not seem to perform as well
  2. keep all negative assumption literals in the conflict (never resolve these away)
     this performs better but on conflict reprocess this can yield a longer conflict
     than the original
  3. all-uip conflict.

  Note that if all assumptions are set first at decision level 1, then all the above
  conflicts are the same. Also the all-uip code does not handle the case
  when all assumptions are made at the same level 1 (messes up the counts per level).

  Thus we have different versions.
---------------------------------------------------------------------------------------*/

/*_________________________________________________________________________________________________
  |
  |  analyzeFinal1 : (confl : CRef)  ->  [void]
  |
  |  Description:
  |    -handles all assumptions at level 1.
  |    -computes conflict of type 2.
  ____________________________________________________________________________________________*/

inline void Solver::af1_mark_conflict(CRef confl, bool atZero, int &n_toR, LSet& out_conflict) {
    //helper for analyzeFinal1--marks literals in conflict, adding some to out_conflict
    Clause& c = ca[confl];
    for (int i = (atZero ? 0 : 1); i < c.size(); i++) {
        Lit l = c[i]; Var y = var(l);
        if(level(y) == 0 || seen[y]) //level zero lits not needed, skip already processed
            continue;
        if(reason(y) == CRef_Undef || isAssumedFalse(l)) {
            out_conflict.insert(l);
            assert(isAssumedFalse(l));
            seen[y] = 2;
        }
        else { //must resolve later
            seen[y] = 1;
            ++n_toR;
        }
    }
}

void Solver::analyzeFinal1(CRef confl, LSet& out_conflict)
{
    out_conflict.clear();
    if (decisionLevel() == 0)
        return;
    int n_toR {0}; //keep track of number of ltierals still to resolve.
    assert(decisionLevel() >= 1);

    //uses seen markers to store the literals that need to be resolved
    //out of the conflict. Also uses seen markers to ensure that duplicate
    //lits not added to out_conflict.

    af1_mark_conflict(confl, true, n_toR, out_conflict);
    //now do resolutions required to obtain final conflict.
    for (int i = trail.size()-1;  n_toR > 0 && i >= trail_lim[0]; i--) {
        Var x = var(trail[i]);
        if(seen[x]) {
            if(seen[x] == 1) {
                //x has a reason and to be resolved away.
                --n_toR;
                af1_mark_conflict(reason(x), false, n_toR, out_conflict);
            }
            seen[x] = 0;
        }
    }
    //because of terminating when n_toR == 0, we might not have cleared seen for some literals in out_conflict.
    for(int i=0; i < out_conflict.size(); i++)
        seen[var(out_conflict[i])] = 0;
}

/*_________________________________________________________________________________________________
|
|  analyzeFinal1 : (p : Lit)  ->  [void]
|
|  Description:
|    Search has found a forced falsified assumption literal p.
|    Hence, given a NEGATED ASSUMPTION LITERAL p we compute a reason A -> p where A contains only positive
|    assumption literals. The result is a clause (-A\/p) consisting only of negated assumptions.
|    Requires at all decisions (non-implied literals on the trail) are postive assumption literals.
|________________________________________________________________________________________________@*/

void Solver::analyzeFinal1(Lit p, LSet& out_conflict)
{
    out_conflict.clear();
    out_conflict.insert(p);
    if (decisionLevel() == 0 || reason(var(p)) == CRef_Undef)
        return;
    int n_toR {0};  //keep track of number of literals still to resolve

    //if p is implied we need its reason as the start of A.
    af1_mark_conflict(reason(var(p)), false, n_toR, out_conflict);

    //now do resolutions required to obtain final conflict.
    for (int i = trail.size()-1; n_toR > 0 && i >= trail_lim[0]; i--) {
        Var x = var(trail[i]);
        if (seen[x]) { //resolve away x
            if(seen[x] == 1) {
                //x has a reason and to be resolved away.
                --n_toR;
                af1_mark_conflict(reason(x), false, n_toR, out_conflict);
            }
            seen[x] = 0;
        }
    }
    //because of terminating when n_toR == 0, we might not have cleared seen for some literals in out_conflict.
    for(int i=0; i < out_conflict.size(); i++)
        seen[var(out_conflict[i])] = 0;
}

/* analyzeFinal2 These versions compute all-UIP clause. So resulting conflict from
   reprocessing cannot be any bigger. However, they currently won't work with
   all assumptions at level 1. So only use when reprocessing the assumption.
*/

inline void Solver::af2_mark_conflict(CRef confl, bool atZero, int &n_toR,
                                      vec<int>& n_atLevel, LSet& out_conflict) {
    //helper for analyzeFinal2--marks literals in conflict, adding some to out_conflict
    Clause& c = ca[confl];
    for(int i = (atZero ? 0 : 1); i < c.size(); i++) {
        Lit l = c[i]; Var y = var(l);
        if(level(y) == 0 || seen[y])
            continue;
        if(reason(y) == CRef_Undef) {
            out_conflict.insert(l);
            assert(isAssumedFalse(l));
            seen[y] = 2;
            ++n_atLevel[level(y)];
        }
        else { //must check later to see if to be resolved
            seen[y] = 1;
            ++n_toR;
            ++n_atLevel[level(y)];
        }
    }
}

/*_________________________________________________________________________________________________
|
|  analyzeFinal2 : (p : Lit)  ->  [void]
|________________________________________________________________________________________________@*/
void Solver::analyzeFinal2(Lit p, LSet& out_conflict)
{
    out_conflict.clear();
    out_conflict.insert(p);
    if (decisionLevel() == 0 || reason(var(p)) == CRef_Undef) //(p) is the conflict
        return;
    int n_toR {0};  //keep track of number of literals still to resolve
    vec<int> n_atLevel (decisionLevel() + 1, 0); //n of lit in conflict at decision level.

    //if p is implied we need its reason as the start of A.
    af2_mark_conflict(reason(var(p)), false, n_toR, n_atLevel, out_conflict);

    //Now climb up trail materalizing conflict from seen markers---updating seen markers
    //as we do resolution steps.
    for (int i = trail.size()-1; n_toR > 0 && i >= trail_lim[0]; i--) {
        Lit l = trail[i]; Var y = var(l);
        if (seen[y]) {
            if(seen[y] == 1) {
                if(!isAssumedTrue(l) || n_atLevel[level(y)] > 1) {
                    //~l is not a negated assumption, or we have more than one at this level.
                    //so we must resolve it away.
                    af2_mark_conflict(reason(y), false, n_toR, n_atLevel, out_conflict);
                }
                else { //~l is sole remaining negated assumption at this level. Keep it.
                    out_conflict.insert(~l);
                    assert(isAssumedFalse(~l));
                    assert(n_atLevel[level(y)] == 1);
               }
                --n_atLevel[level(y)];
                --n_toR;
            }
            if(seen[y] == 2)
                --n_atLevel[level(y)];
            seen[y] = 0;
        }
    }
    for(int i=0; i < out_conflict.size(); i++)
        seen[var(out_conflict[i])] = 0;
}

/*_________________________________________________________________________________________________
  |
  |  analyzeFinal2 : (confl : CRef)  ->  [void]
  |________________________________________________________________________________________________*/

void Solver::analyzeFinal2(CRef confl, LSet& out_conflict)
{
    out_conflict.clear();
    if (decisionLevel() == 0)
        return;
    assert(decisionLevel() >= 1);
    int n_toR {0}; //keep track of number of ltierals still to resolve.
    vec<int> n_atLevel (decisionLevel() + 1, 0); //n of lit in conflict at decision level.

    //Start my marking conflict clause among the seen markers.
    af2_mark_conflict(confl, true, n_toR, n_atLevel, out_conflict);

    //no climb up trail doing resolutions
    for (int i = trail.size()-1;  n_toR > 0 && i >= trail_lim[0]; i--) {
        Lit l = trail[i]; Var y = var(l);
        if (seen[y]) {
            if(seen[y] == 1) {
                if(!isAssumedTrue(l) || n_atLevel[level(y)] > 1) {
                    //~l is not a negated assumption, or we have more than one at this level.
                    //so we must resolve it away.
                    af2_mark_conflict(reason(y), false, n_toR, n_atLevel, out_conflict);
                }
                else { //~l is sole remaining negated assumption at this level. Keep it.
                    out_conflict.insert(~l);
                    assert(isAssumedFalse(~l));
                    assert(n_atLevel[level(y)] == 1);
                }
                --n_atLevel[level(y)];
                --n_toR;
            }
            if(seen[y] == 2)
                --n_atLevel[level(y)];
            seen[y] = 0;
        }
    }
    for(int i=0; i < out_conflict.size(); i++)
        seen[var(out_conflict[i])] = 0;
}

void Solver::uncheckedEnqueue(Lit p, CRef from)
{
    assert(value(p) == l_Undef);
    assigns[var(p)] = lbool(!sign(p));
    vardata[var(p)].reason = from;
    vardata[var(p)].level = decisionLevel(); //vardata[var(p)].isAssumed is not changed
    trail.push_(p);
}


/*_________________________________________________________________________________________________
  |
  |  propagate : [void]  ->  [Clause*]
  |
  |  Description:
  |    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
  |    otherwise CRef_Undef.
  |
  |    Post-conditions:
  |      * the propagation queue is empty, even if there was a conflict.
  |________________________________________________________________________________________________@*/
[[gnu::hot]]
CRef Solver::propagate()
{
    CRef    confl     = CRef_Undef;
    int     num_props = 0;

    while (qhead < trail.size()){
        Lit            p   = trail[qhead++];     // 'p' is enqueued fact to propagate.
        vec<Watcher>&  ws  = watches.lookup(p);
        Watcher        *i, *j, *end;
        num_props++;

        for (i = j = (Watcher*)ws, end = i + ws.size();  i != end;){
            // Try to avoid inspecting the clause:
            Lit blocker = i->blocker;
            if (value(blocker) == l_True){
                *j++ = *i++; continue; }

            // Make sure the false literal is data[1]:
            CRef     cr        = i->cref;
            Clause&  c         = ca[cr];
            Lit      false_lit = ~p;
            if (c[0] == false_lit)
                c[0] = c[1], c[1] = false_lit;
            assert(c[1] == false_lit);
            i++;

            // If 0th watch is true, then clause is already satisfied.
            Lit     first = c[0];
            Watcher w     = Watcher(cr, first);
            if (first != blocker && value(first) == l_True){
                *j++ = w; continue; }

            // Look for new watch:
            for (int k = 2; k < c.size(); k++)
                if (value(c[k]) != l_False){
                    c[1] = c[k]; c[k] = false_lit;
                    watches[~c[1]].push(w);
                    goto NextClause; }

            // Did not find watch -- clause is unit under assignment:
            *j++ = w;
            if (value(first) == l_False){
                confl = cr;
                qhead = trail.size();
                // Copy the remaining watches:
                while (i < end)
                    *j++ = *i++;
            }else
                uncheckedEnqueue(first, cr);

        NextClause:;
        }
        ws.shrink(i - j);
    }
    propagations += num_props;
    simpDB_props -= num_props;

    return confl;
}


/*_________________________________________________________________________________________________
  |
  |  reduceDB : ()  ->  [void]
  |
  |  Description:
  |    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
  |    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
  |________________________________________________________________________________________________@*/
struct reduceDB_lt {
    ClauseAllocator& ca;
    reduceDB_lt(ClauseAllocator& ca_) : ca(ca_) {}
    bool operator () (CRef x, CRef y) {
        return ca[x].size() > 2 && (ca[y].size() == 2 || ca[x].activity() < ca[y].activity()); }
};
void Solver::reduceDB()
{
    int     i, j;
    double  extra_lim = cla_inc / learnts.size();    // Remove any clause below this activity

    sort(learnts, reduceDB_lt(ca));
    // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
    // and clauses with activity smaller than 'extra_lim':
    for (i = j = 0; i < learnts.size(); i++){
        Clause& c = ca[learnts[i]];
        if (c.size() > 2 && !locked(c) && (i < learnts.size() / 2 || c.activity() < extra_lim))
            removeClause(learnts[i]);
        else
            learnts[j++] = learnts[i];
    }
    learnts.shrink(i - j);
    checkGarbage();
}


void Solver::removeSatisfied(vec<CRef>& cs)
{
    int i, j;
    for (i = j = 0; i < cs.size(); i++){
        Clause& c = ca[cs[i]];
        if (satisfied(c))
            removeClause(cs[i]);
        else{
            // Trim clause:
            assert(value(c[0]) == l_Undef && value(c[1]) == l_Undef);
            for (int k = 2; k < c.size(); k++)
                if (value(c[k]) == l_False){
                    c[k--] = c[c.size()-1];
                    c.pop();
                }
            cs[j++] = cs[i];
        }
    }
    cs.shrink(i - j);
}


void Solver::rebuildOrderHeap()
{
    vec<Var> vs;
    for (Var v = 0; v < nVars(); v++)
        if (decision[v] && value(v) == l_Undef)
            vs.push(v);
    order_heap.build(vs);
}


/*_________________________________________________________________________________________________
  |
  |  simplify : [void]  ->  [bool]
  |
  |  Description:
  |    Simplify the clause database according to the current top-level assigment. Currently, the only
  |    thing done here is the removal of satisfied clauses, but more things can be put here.
  |________________________________________________________________________________________________@*/
bool Solver::simplify()
{
    assert(decisionLevel() == 0);

    if (!ok || propagate() != CRef_Undef)
        return ok = false;

    if (nAssigns() == simpDB_assigns || (simpDB_props > 0))
        return true;

    // Remove satisfied clauses:
    removeSatisfied(learnts);
    if (remove_satisfied){       // Can be turned off.
        removeSatisfied(clauses);

        // TODO: what todo in if 'remove_satisfied' is false?

        // Remove all released variables from the trail:
        for (int i = 0; i < released_vars.size(); i++){
            assert(seen[released_vars[i]] == 0);
            seen[released_vars[i]] = 1;
        }

        int i, j;
        for (i = j = 0; i < trail.size(); i++)
            if (seen[var(trail[i])] == 0)
                trail[j++] = trail[i];
        trail.shrink(i - j);
        //printf("trail.size()= %d, qhead = %d\n", trail.size(), qhead);
        qhead = trail.size();

        for (int i = 0; i < released_vars.size(); i++)
            seen[released_vars[i]] = 0;

        // Released variables are now ready to be reused:
        append(released_vars, free_vars);
        released_vars.clear();
    }
    checkGarbage();
    rebuildOrderHeap();

    simpDB_assigns = nAssigns();
    simpDB_props   = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)

    return true;
}


/*_________________________________________________________________________________________________
  |
  |  search : (nof_conflicts : int) (params : const SearchParams&)  ->  [lbool]
  |
  |  Description:
  |    Search for a model the specified number of conflicts.
  |    NOTE! Use negative value for 'nof_conflicts' indicate infinity.
  |
  |  Output:
  |    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
  |    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
  |    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
  |________________________________________________________________________________________________@*/
lbool Solver::search(int nof_conflicts)
{
    assert(ok);
    int         backtrack_level;
    int         conflictC = 0;
    vec<Lit>    learnt_clause;
    starts++;

    for (;;){
        CRef confl = propagate();
        if (confl != CRef_Undef){
            // CONFLICT
            conflicts++; conflictC++;
            if (decisionLevel() == 0) return l_False; //Conflict at level 0
            if (decisionLevel() == 1 && assumptions.size() > 0) {               //Conflict among assumptions
                analyzeFinal1(confl, conflict);
                int orig_size = conflict.size(); ++n_assump_conflicts;
                cancelUntil(0);
                if (conflict.size() == 1) {
                    //slight extra. Normally units could escape since they are computed by analyzeFinal (not analyze)
                    uncheckedEnqueue(conflict[0]);
                    if(propagate() != CRef_Undef) //could have an even stronger (empty conflict) after prop.
                        conflict.clear();
                    return l_False;
                }

                if(!assump_2nd_process)
                    return l_False;
                //with 2nd process we try to get a shorter conflict
                //by setting the assumption literals in conflict to true one per
                //decision level until one is set to false. Note conflict has negated
                //assumptions. First prepare level 0.
                if(propagate() != CRef_Undef) {
                    conflict.clear();
                    return l_False;
                }
                bool did_not_reprocess {true};
                for(int i = 0; i < conflict.size(); i++) { //
                    Lit a = conflict[i];    //a is a negative assumption literal
                    if(value(a) == l_False) //assumption is true
                        continue;
                    if(value(a) == l_True) { //assumption is false
                        analyzeFinal2(a, conflict); //note overwrites conflict, so for loop must be terminated after.
                        did_not_reprocess = false;
                        break;
                    }
                    //else make ~a a new decision and then propagate.
                    newDecisionLevel();
                    uncheckedEnqueue(~a);
                    CRef con = propagate();
                    //It is possible that a subet of the assumptions causes a conflict...
                    //instead of forcing an assumption to be falsified.
                    if(con != CRef_Undef) {
                        analyzeFinal2(con, conflict);
                        did_not_reprocess = false;
                        break;
                    }
                }
                cancelUntil(0);
                if(averbosity > 0 && conflict.size() != orig_size) {
                    cout << "c 2nd assumption processing changed size. Orig = "
                         << orig_size << " new = " << conflict.size() << " gain "
                         << orig_size - conflict.size() << "\n";
                    bool ok = true;
                    for(int i=0; i < conflict.size(); i++)
                        if(!isAssumedFalse(conflict[i]))
                            ok=false;
                    if(!ok)
                    cout << "conflict does not contain all negated assumptions\n";
                }
                assump_saved += orig_size - conflict.size();
                if(did_not_reprocess)
                    printf("C Warning 2nd attempt did not find second conflict!\n");

                if (conflict.size() == 1) {
                    //again might have learnt a new unit so add this to the solver and check if an even shorter conflict is possible
                    uncheckedEnqueue(conflict[0]);
                    if(propagate() != CRef_Undef) //could have an even stronger (empty conflict) after prop.
                        conflict.clear();
                }
                return l_False;
            }

            //otherwise we got a conflict at a deeper level...do ordinary clause learning
            learnt_clause.clear();
            analyze(confl, learnt_clause, backtrack_level);
            cancelUntil(backtrack_level);

            if (learnt_clause.size() == 1){
                uncheckedEnqueue(learnt_clause[0]);
            }else{
                CRef cr = ca.alloc(learnt_clause, true);
                learnts.push(cr);
                attachClause(cr);
                claBumpActivity(ca[cr]);
                uncheckedEnqueue(learnt_clause[0], cr);
            }

            varDecayActivity();
            claDecayActivity();

            if (--learntsize_adjust_cnt == 0){
                learntsize_adjust_confl *= learntsize_adjust_inc;
                learntsize_adjust_cnt    = (int)learntsize_adjust_confl;
                max_learnts             *= learntsize_inc;

                if (verbosity >= 1)
                    printf("| %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n",
                           (int)conflicts,
                           (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]), nClauses(), (int)clauses_literals,
                           (int)max_learnts, nLearnts(), (double)learnts_literals/nLearnts(), progressEstimate()*100);
            }

        }else{
            // NO CONFLICT
            if ((nof_conflicts >= 0 && conflictC >= nof_conflicts) || !withinBudget()){
                // Reached bound on number of conflicts:
                progress_estimate = progressEstimate();
                cancelUntil(0);
                return l_Undef; }

            // Simplify the set of problem clauses:
            if (decisionLevel() == 0 && !simplify())
                return l_False;

            if (learnts.size()-nAssigns() >= max_learnts)
                // Reduce the set of learnt clauses:
                reduceDB();

            if (decisionLevel() == 0 && assumptions.size() > 0) { //enqueue all assumptions if finished with dl 0
                newDecisionLevel();
                for (int i = 0; i < assumptions.size(); i++) {
                    Lit p = assumptions[i];
                    if(value(p) == l_False) {
                        conflict.insert(~p);
                        return l_False;
                    }
                    else if (value(p) == l_Undef)
                        uncheckedEnqueue(p);
                }
            }
            else {
                decisions++;
                Lit next = pickBranchLit();
                if(next == lit_Undef)
                    //Model found
                    return l_True;
                // Increase decision level and enqueue 'next'
                newDecisionLevel();
                uncheckedEnqueue(next);
            }
        }
    }
}

double Solver::progressEstimate() const
{
    double  progress = 0;
    double  F = 1.0 / nVars();

    for (int i = 0; i <= decisionLevel(); i++){
        int beg = i == 0 ? 0 : trail_lim[i - 1];
        int end = i == decisionLevel() ? trail.size() : trail_lim[i];
        progress += pow(F, i) * (end - beg);
    }

    return progress / nVars();
}

/*
  Finite subsequences of the Luby-sequence:

  0: 1
  1: 1 1 2
  2: 1 1 2 1 1 2 4
  3: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8
  ...


*/

static double luby(double y, int x){

    // Find the finite subsequence that contains index 'x', and the
    // size of that subsequence:
    int size, seq;
    for (size = 1, seq = 0; size < x+1; seq++, size = 2*size+1);

    while (size-1 != x){
        size = (size-1)>>1;
        seq--;
        x = x % size;
    }

    return pow(y, seq);
}

// NOTE: assumptions passed in member-variable 'assumptions'.
lbool Solver::solve_()
{
    model.clear();
    conflict.clear();
    if (!ok) return l_False;

    solves++;

    max_learnts = nClauses() * learntsize_factor;
    if (max_learnts < min_learnts_lim)
        max_learnts = min_learnts_lim;

    learntsize_adjust_confl   = learntsize_adjust_start_confl;
    learntsize_adjust_cnt     = (int)learntsize_adjust_confl;
    lbool   status            = l_Undef;

    if (verbosity >= 1){
        printf("============================[ Search Statistics ]==============================\n");
        printf("| Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
        printf("|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
        printf("===============================================================================\n");
    }

    //Initialize Assumptions
    for(int i=0; i < assumptions.size(); i++) {
        Lit p = assumptions[i];
        if(isAssumedFalse(p)) {
            conflict.clear(); conflict.insert(p); conflict.insert(~p);
            status = l_False;
            break;
        }
        setAssumption(p);
    }

    if(conflict.size() > 0)
        printf("c WARNING: Found conflict in assumptions\n");

    // Search:
    int curr_restarts = 0;
    while (status == l_Undef){
        double rest_base = luby_restart ? luby(restart_inc, curr_restarts) : pow(restart_inc, curr_restarts);
        status = search(rest_base * restart_first);
        if (!withinBudget()) break;
        curr_restarts++;
    }

    if (verbosity >= 1)
        printf("===============================================================================\n");

    if (status == l_True){
        // Extend & copy model:
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++) model[i] = value(i);
    }else if (status == l_False && conflict.size() == 0)
        ok = false;

    cancelUntil(0);
    for(int i=0; i< assumptions.size(); i++)
        unsetAssumption(assumptions[i]);
    return status;
}


bool Solver::implies(const vec<Lit>& assumps, vec<Lit>& out)
{
    trail_lim.push(trail.size());
    for (int i = 0; i < assumps.size(); i++){
        Lit a = assumps[i];

        if (value(a) == l_False){
            cancelUntil(0);
            return false;
        }else if (value(a) == l_Undef)
            uncheckedEnqueue(a);
    }

    unsigned trail_before = trail.size();
    bool     ret          = true;
    if (propagate() == CRef_Undef){
        out.clear();
        for (int j = trail_before; j < trail.size(); j++)
            out.push(trail[j]);
    }else
        ret = false;

    cancelUntil(0);
    return ret;
}

//=================================================================================================
// Writing CNF to DIMACS:
//
// FIXME: this needs to be rewritten completely.

static Var mapVar(Var x, vec<Var>& map, Var& max)
{
    if (map.size() <= x || map[x] == -1){
        map.growTo(x+1, -1);
        map[x] = max++;
    }
    return map[x];
}


void Solver::toDimacs(FILE* f, Clause& c, vec<Var>& map, Var& max)
{
    if (satisfied(c)) return;

    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) != l_False)
            fprintf(f, "%s%d ", sign(c[i]) ? "-" : "", mapVar(var(c[i]), map, max)+1);
    fprintf(f, "0\n");
}


void Solver::toDimacs(const char *file, const vec<Lit>& assumps)
{
    FILE* f = fopen(file, "wr");
    if (f == NULL)
        fprintf(stderr, "could not open file %s\n", file), exit(1);
    toDimacs(f, assumps);
    fclose(f);
}


void Solver::toDimacs(FILE* f, const vec<Lit>& assumps)
{
    // Handle case when solver is in contradictory state:
    if (!ok){
        fprintf(f, "p cnf 1 2\n1 0\n-1 0\n");
        return; }

    vec<Var> map; Var max = 0;

    // Cannot use removeClauses here because it is not safe
    // to deallocate them at this point. Could be improved.
    int cnt = 0;
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]]))
            cnt++;

    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]])){
            Clause& c = ca[clauses[i]];
            for (int j = 0; j < c.size(); j++)
                if (value(c[j]) != l_False)
                    mapVar(var(c[j]), map, max);
        }

    // Assumptions are added as unit clauses:
    cnt += assumps.size();

    fprintf(f, "p cnf %d %d\n", max, cnt);

    for (int i = 0; i < assumps.size(); i++){
        assert(value(assumps[i]) != l_False);
        fprintf(f, "%s%d 0\n", sign(assumps[i]) ? "-" : "", mapVar(var(assumps[i]), map, max)+1);
    }

    for (int i = 0; i < clauses.size(); i++)
        toDimacs(f, ca[clauses[i]], map, max);

    if (verbosity > 0)
        printf("Wrote DIMACS with %d variables and %d clauses.\n", max, cnt);
}


void Solver::printStats() const
{
    double cpu_time = cpuTime();
    double mem_used = memUsedPeak();
    printf("restarts              : %" PRIu64 "\n", starts);
    printf("conflicts             : %-12" PRIu64 "   (%.0f /sec)\n", conflicts   , conflicts   /cpu_time);
    printf("decisions             : %-12" PRIu64 "   (%4.2f %% random) (%.0f /sec)\n", decisions, (float)rnd_decisions*100 / (float)decisions, decisions   /cpu_time);
    printf("propagations          : %-12" PRIu64 "   (%.0f /sec)\n", propagations, propagations/cpu_time);
    printf("conflict literals     : %-12" PRIu64 "   (%4.2f %% deleted)\n", tot_literals, (max_literals - tot_literals)*100 / (double)max_literals);
    if (mem_used != 0) printf("Memory used           : %.2f MB\n", mem_used);
    printf("CPU time              : %g s\n", cpu_time);
}


//=================================================================================================
// Garbage Collection methods:

void Solver::relocAll(ClauseAllocator& to)
{
    // All watchers:
    //
    watches.cleanAll();
    for (int v = 0; v < nVars(); v++)
        for (int s = 0; s < 2; s++){
            Lit p = mkLit(v, s);
            vec<Watcher>& ws = watches[p];
            for (int j = 0; j < ws.size(); j++)
                ca.reloc(ws[j].cref, to);
        }

    // All reasons:
    //
    for (int i = 0; i < trail.size(); i++){
        Var v = var(trail[i]);

        // Note: it is not safe to call 'locked()' on a relocated clause. This is why we keep
        // 'dangling' reasons here. It is safe and does not hurt.
        if (reason(v) != CRef_Undef && (ca[reason(v)].reloced() || locked(ca[reason(v)]))){
            assert(!isRemoved(reason(v)));
            ca.reloc(vardata[v].reason, to);
        }
    }

    // All learnt:
    //
    int i, j;
    for (i = j = 0; i < learnts.size(); i++)
        if (!isRemoved(learnts[i])){
            ca.reloc(learnts[i], to);
            learnts[j++] = learnts[i];
        }
    learnts.shrink(i - j);

    // All original:
    //
    for (i = j = 0; i < clauses.size(); i++)
        if (!isRemoved(clauses[i])){
            ca.reloc(clauses[i], to);
            clauses[j++] = clauses[i];
        }
    clauses.shrink(i - j);
}


void Solver::garbageCollect()
{
    // Initialize the next region to a size corresponding to the estimated utilization degree. This
    // is not precise but should avoid some unnecessary reallocations for the new region:
    ClauseAllocator to(ca.size() - ca.wasted());

    relocAll(to);
    if (verbosity >= 2)
        printf("|  Garbage collection:   %12d bytes => %12d bytes             |\n",
               ca.size()*ClauseAllocator::Unit_Size, to.size()*ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}
