/***********[dlink.cc]
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

#include "maxhs/core/dlink.h"
#include <stdio.h>
#include <algorithm>
#include <queue>

using namespace MaxHS;

uint64_t dlink_node::next_id = 1;

dlink_matrix::dlink_matrix(vector<Weight> &costs) : colcosts(costs), bestcol_heap(BestColLt(costs, this)) { 
    root = new dlink_node(); 
    root->u = root; 
    root->d = root; 
    root->r = root; 
    root->l = root; 
    undo_stack = NULL;
}

dlink_matrix::~dlink_matrix() {
}

int dlink_matrix::best_col() {

    int bestcol = -1; 
    if (root->r != root) {
        // Removes some unlinked columns from the heap.
        while (!bestcol_heap.empty()) {
            int top = bestcol_heap.removeMin();  
            if (col_in_matrix(top)) {
                bestcol = top;
                bestcol_heap.insert(top);
                break; 
            }
        }
    }
    return bestcol;
}

// Returns the node in the list that n should come after, or the node in 
// the list with the same name as n if one exists.
// only searches from list rightwards to root, but does not check from root to list.
dlink_node *dlink_matrix::rl_find(dlink_node *list, int name) {

    dlink_node *cur = list;
    while (name > cur->name && cur->r->name >= 0 && name >= cur->r->name)  {
        cur = cur->r;
        if (cur == list) break;
    } 
    return cur;
}

// Insert node n after node prev
void dlink_matrix::rl_insert(dlink_node *prev, dlink_node *n) {
    
    n->l = prev;
    n->r = prev->r;
    prev->r->l = n;
    prev->r = n;
}

// Insert node n below node prev
void dlink_matrix::ud_insert(dlink_node *prev, dlink_node *n) {
    
    n->u = prev;
    n->d = prev->d;
    prev->d->u = n;
    prev->d = n;
}

void dlink_matrix::add_row(int rowname, set<int> &cols) {

    // Create the row header
    dlink_node *row_head = new dlink_node();
    row_head->name = rowname;
    row_head->size = cols.size();
    row_head->r = row_head;
    row_head->l = row_head;
    row_head->rowhead = row_head;
    ud_insert(root->u, row_head);
 
    dlink_node *currow = row_head; 
    dlink_node *curcol = root; 
    for (set<int>::iterator i = cols.begin(); i != cols.end(); i++) {
        dlink_node *col = NULL;
        dlink_node *prev = rl_find(curcol, *i);
        // New column header
        if (prev->name != *i) {
            col = new dlink_node();
            col->name = *i;
            col->u = col;
            col->d = col;
            col->colhead = col;
            rl_insert(prev, col); 

            if (id_to_col.size() <= (unsigned int) col->name) {
                id_to_col.resize(col->name+1, NULL);
            }
            id_to_col[col->name] = col;
        } else {
            col = prev;
        }
        dlink_node *newrow = new dlink_node();
        newrow->colhead = col;
        newrow->rowhead = row_head;
        ud_insert(col->u, newrow);
        newrow->colhead->size++;
        rl_insert(currow, newrow);
        currow = newrow;
        curcol = col;
        // use "update" in case it hasn't been inserted yet
        bestcol_heap.update(col->name); //must do after its size is updated (newrow->colhead->size++)
    }
}

void dlink_matrix::undo_to_mark() {
    dlink_node *cur = undo_stack;
    while (cur && !cur->undo_mark) {
        if (cur->u->d != cur) {
            cur->u->d = cur;
            cur->d->u = cur;
            // make sure this is not a row header
            if (cur->name < 0) {
                cur->colhead->size++;
                bestcol_heap.update(cur->colhead->name);
            }
        } else {
            cur->r->l = cur;
            cur->l->r = cur;
            if (cur->name < 0) cur->rowhead->size++;
            // adding back a column header
            else {
                bestcol_heap.update(cur->name);
            }
        }
        cur = cur->undo_next;
        pop_undo_stack();
    } 
    if (cur) {
        //assert(cur->undo_mark);
        pop_undo_stack();
        delete cur;
    }
}

void dlink_matrix::undo_to_mark(vector<int> &rowvars, vector<int> &colvars, int resetval) {

    dlink_node *cur = undo_stack;
    while (cur && !cur->undo_mark) {
        if (cur->u->d != cur) {
            cur->u->d = cur;
            cur->d->u = cur;
            // check if this is a row header
            if (cur->name < 0) {
                cur->colhead->size++;
                bestcol_heap.update(cur->colhead->name);
            }
            // this can't be a col header so it does belong to some row
            rowvars[cur->rowhead->name] = resetval;
        } else {
            cur->r->l = cur;
            cur->l->r = cur;
            if (cur->name < 0) cur->rowhead->size++;
            // adding back a column header
            else {
                bestcol_heap.update(cur->name);
            }
            colvars[cur->colhead->name] = resetval;
        }
        cur = cur->undo_next;
        pop_undo_stack();
    } 
    if (cur) {
        //assert(cur->undo_mark);
        pop_undo_stack();
        delete cur;
    }
    //printf("AFTER UNDO\n"); print(); printf("END AFTER UNDO\n");
}

void dlink_matrix::use_col(int name, vector<int> &removedrows) {

#if 0 
   dlink_node *head = rl_find(root, name);
   if (head == root || head->name != name) {
#else
   dlink_node *head = id_to_col[name];
   if (head == NULL) {
#endif
       fprintf(stdout, "c ERROR: dlink_matrix::use_col: did not find column with name %d\n", name);
       fflush(stdout);
       fflush(stderr);
       exit(0);
   }
   dlink_node *row = head->d;
   while (row != head) { 
       ulink_row(row);
       removedrows.push_back(row->rowhead->name);
       row = row->d;    
   } 
   // No singleton rows can be created in this case
   vector<int> temp;
   ulink_col(head, temp);
}

void dlink_matrix::ulink_row(dlink_node *row) {

    dlink_node *cur = row;
    do {
        cur->u->d = cur->d;
        cur->d->u = cur->u;
        if (cur->name < 0) {
            cur->colhead->size--; // make sure cur isn't the row header
            bestcol_heap.update(cur->colhead->name);
        }
        push_undo_stack(cur);
        cur = cur->r;
    } while (cur != row);
      
#ifdef DLINK_DEBUG
    // check if any column contains this row
    cur = root->r;
    while (cur != root) {
        dlink_node *cur2 = cur->d;
        while (cur2 != cur) {
            if (cur2->rowhead->name == rowname) {
                fprintf(stdout, "c ERROR: unlinked row %d is still in column %d\n", rowname, cur->name);
                //return false;
            } 
            cur2 = cur2->d;
        }
        cur = cur->r;
    }
#endif
}

void dlink_matrix::ulink_col(dlink_node *col, vector<int> &newsingletons) {

    dlink_node *cur = col;
    do {
        cur->r->l = cur->l;
        cur->l->r = cur->r;
        if (cur->name < 0) { // make sure cur is not the column header
            cur->rowhead->size--;
            if (cur->rowhead->size == 1) {
                // the remaining column in this singleton row
                newsingletons.push_back(cur->rowhead->r->colhead->name);
            }
        }
        push_undo_stack(cur);
        cur = cur->d;
    } while (cur != col);


#ifdef DLINK_DEBUG
    // check if any row contains this column 
    cur = root->d;
    while (cur != root) {
        dlink_node *cur2 = cur->r;
        while (cur2 != cur) {
            if (cur2->colhead->name == colname) {
                fprintf(stdout, "c ERROR: unlinked col %d is still in row %d\n", colname, cur->name);
                //return false;
            } 
            cur2 = cur2->r;
        }
        cur = cur->d;
    }
#endif
}

void dlink_matrix::print() {

    printf("dlink_matrix:\n");
    if (root == NULL) {
        printf("root is NULL\n");
        return;
    } else if (root->r == root && root->d == root) {
        printf("no rows and no columns\n");
        return;
    } else if (root->d == root) {
        printf("no rows\n");
        return;
    } else if (root->r == root) {
        printf("no columns\n");
        return;
    }

    dlink_node *cur = root;
    do {
        printf("Row: ");
        print_row(cur); printf("\n\n");
        cur = cur->d;         
    } while(cur != root);
    printf("end of dlink_matrix\n");
}

void dlink_matrix::print_row(dlink_node *head) {

   dlink_node *cur = head;
   do {
       cur->print(); printf(" ");
       cur = cur->r;
   } while (cur != head);
}

void dlink_node::print() {
    printf("id=%lu, name=%d, u=%lu, d=%lu, r=%lu, l=%lu, colhead=%lu, rowhead=%lu, size=%d, undo_next=%lu, undo_mark=%d", id, name, u?u->id:0, d?d->id:0, r?r->id:0, l?l->id:0, colhead?colhead->id:0, rowhead?rowhead->id:0, size, undo_next?undo_next->id:0, undo_mark); 
}

void dlink_matrix::print_readable() {
    printf("dlink_matrix readable (list of sets):\n");
    dlink_node *cur = root->d;
    while (cur != root) {
        printf("set %d: ", cur->name);
        dlink_node *col = cur->r;
        while (col != cur) {
            printf("%d, ", col->colhead->name);
            col = col->r;
        }
        printf("\n");
        cur = cur->d;        
    }
}

Weight dlink_matrix::greedy_hs(set<int> &hs) {

    Weight hscost = 0;
    vector<int> removedrows;

    mark_undo_stack();
    while (has_row()) {
        int bestcol = best_col();
        hs.insert(bestcol);
        hscost += colcosts[bestcol];
        removedrows.clear();
        use_col(bestcol, removedrows);
    }
    undo_to_mark();
    return hscost;
}
