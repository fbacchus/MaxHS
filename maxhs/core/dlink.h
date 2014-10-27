/***********[dlink.h]
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

#ifndef DLINK_H
#define DLINK_H

// set cover matrix, implemented with doubly linked lists as in Knuth's dancing links paper

#include <set>
#include <vector>
#include <stdint.h>
#include <stdio.h>
#include "maxhs/core/MaxSolverTypes.h"
#include "minisat/core/SolverTypes.h"
#include "minisat/core/Solver.h"
#include "minisat/mtl/Heap.h"

//#define DLINK_DEBUG 1

using namespace Minisat;
using namespace std;

namespace MaxHS {

class dlink_node {
private:
    static uint64_t next_id;

public:
    int name;
    uint64_t id;

    // Up, down, right, left
    dlink_node *u;
    dlink_node *d;
    dlink_node *r;
    dlink_node *l;
    dlink_node *colhead;
    dlink_node *rowhead;

    // If this node is a row or column header, size is the number of nodes
    // currently in the row or column
    int size;

    // Next node in the undo stack
    dlink_node *undo_next;
    bool undo_mark;

    // For the H2 lower bound heuristic.
    bool flag;

    dlink_node() : name(-1), id(next_id++), u(NULL), d(NULL), r(NULL), l(NULL), colhead(NULL), rowhead(NULL), size(0), undo_next(NULL), undo_mark(false), flag(false) {}

    ~dlink_node() {}
    void print();
};

class dlink_matrix {

private:
    dlink_node *root;
    dlink_node *undo_stack;
    vector<Weight> &colcosts;

    struct BestColLt {
        const vector<Weight> &w;
        const dlink_matrix *m; 
        bool operator() (int x, int y) const {
            return (m->id_to_col[x])->size/((double) w[x]) > (m->id_to_col[y])->size/((double) w[y]); 
        }
        BestColLt(vector<Weight> &weights, const dlink_matrix *matrix) : w(weights), m(matrix) { }
    };
  Heap<int,BestColLt> bestcol_heap;

    // map column ID to the column header node 
    vector<dlink_node *> id_to_col;
 
public:

    dlink_matrix(vector<Weight> &costs);
    ~dlink_matrix();

    // For building the matrix (adding sets to cover)
    void add_row(int rowname, set<int> &cols);

    // To restore to previous state
    void mark_undo_stack() { /*printf("AT MARK\n"); print(); printf("END AT MARK\n");*/ dlink_node *m = new dlink_node(); 
                             m->undo_mark = true; push_undo_stack(m); };
    void undo_to_mark(vector<int> &rowvars, vector<int> &colvars, int resetval);
    
    // Use the indicated column to cover all of its rows
    void use_col(int name, vector<int> &removedrows);

    // Return column that covers the most rows for the least cost
    int best_col(); 

    bool has_row() { return root->d != root; }
    bool has_col() { return root->r != root; }

    bool col_in_matrix(int id) const;

    // Returns a hitting set and its cost 
    Weight greedy_hs(set<int> &hs);

    void print();
    void print_readable();
    
private:

    dlink_node *rl_find(dlink_node *list, int name);
    void rl_insert(dlink_node *prev, dlink_node *n);
    void ud_insert(dlink_node *prev, dlink_node *n);


    // Unlink a row from the matrix 
    void ulink_row(dlink_node *row);
    // Unlink a column from the matrix
    void ulink_col(dlink_node *col, vector<int> &newsingletons); 

    void push_undo_stack(dlink_node *n) { n->undo_next = undo_stack; 
                                          undo_stack = n; }
    void pop_undo_stack() { //assert(undo_stack); 
                            dlink_node *removed = undo_stack;
                            undo_stack = undo_stack->undo_next; 
                            removed->undo_next = NULL;}
    void print_row(dlink_node *row);
    void undo_to_mark();
};

inline bool dlink_matrix::col_in_matrix(int id) const {
    if (((unsigned int) id) >= id_to_col.size() || id_to_col[id] == NULL) return false;
    return id_to_col[id]->r->l == id_to_col[id];
}

} //namespace MaxHS 
#endif
