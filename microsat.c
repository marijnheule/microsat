/*********************************************************************[microsat.c]***

  The MIT License

  Copyright (c) 2014-2018 Marijn Heule

  Permission is hereby granted, free of charge, to any person obtaining a copy
  of this software and associated documentation files (the "Software"), to deal
  in the Software without restriction, including without limitation the rights
  to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
  copies of the Software, and to permit persons to whom the Software is
  furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in all
  copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
  OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
  SOFTWARE.

*************************************************************************************/

#include <stdio.h>
#include <stdlib.h>

#define END        -9
#define MEM_MAX     100000000
#define MARK        2
#define UNSAT       0
#define SAT         1
#define UNKNOWN	    2
// #define STANDALONE

#ifndef STANDALONE
#include "microsat.h"
#endif

#ifdef STANDALONE
struct solver { // The variables in the struct are described in the allocate procedure
  int  *DB, nVars, nClauses, mem_used, mem_fixed, mem_max, maxLemmas, nLemmas,
       *assumptions, *assumeHead, restarts, nConflicts, *model, *reason, *falseStack,
       *false, *first, *heap, heapSize, *lookup, *score, *forced, *processed, *assigned; };
#endif

void assign (struct solver* S, int* reason, int forced) {         // Make the first literal of the reason true
  int lit = reason[0];                                            // Let lit be the first ltieral in the reason
  S->false[-lit] = 1 + 5 * forced;                                // Mark it as true and possibly forced
  *(S->assigned++) = -lit;                                        // Push it on the assignment stack
  S->reason[abs(lit)] = 1 + (int) ((reason)-S->DB);               // Set the reason clause of lit
  S->model[abs(lit)] = (lit > 0); }                               // Mark the literal as true in the model

void addWatch (struct solver* S, int lit, int mem) {              //
  S->DB[mem] = S->first[lit]; S->first[lit] = mem; }              //

void resetAssumptions (struct solver *S) {                        //
  S->assumeHead = S->assumptions; }                               //

void assume (struct solver* S, int lit) {                         //
  *S->assumeHead = lit; S->assumeHead++; }                        //

int* getMemory (struct solver* S, int mem_size) {                 //
#ifdef STANDALONE
  if (S->mem_used + mem_size > S->mem_max) {                      //
    printf("Out of Memory\n"); exit (0); }                        //
#endif
  if (S->mem_used + mem_size > S->mem_max) {                      //
    S->mem_max = (3 * S->mem_max) >> 1;                           //
    S->DB = realloc (S->DB, sizeof(int) * S->mem_max); }          //
  int *store = (S->DB + S->mem_used);                             //
  S->mem_used += mem_size;                                        //
  return store; }                                                 //

int* addClause (struct solver* S, int* input, int size) {         //
  if (size > 1) { addWatch (S, input[0], S->mem_used    );        //
                  addWatch (S, input[1], S->mem_used + 1); }      //
  int i, *clause = getMemory (S, size + 3) + 2;                   //
  for (i = 0; i < size; ++i) clause[i] = input[i]; clause[i] = 0; //
  return clause; }                                                //

void reduceDB (struct solver* S) {                                // Removes "less useful" lemmas from DB
  int* head    = (S->DB + S->mem_fixed);                          // Place head at the start of the lemmas
  int* tail    = (S->DB + S->mem_used);                           // Place tail at the end of the lemmas
  S->maxLemmas = (S->maxLemmas * 9) >> 3;                         // Allow more lemmas in the future
  S->mem_used  = S->mem_fixed;                                    // Virtually remove all lemmas
  S->nLemmas   = 0;                                               // Reset the number of lemmas

  int i; for (i = -S->nVars; i <= S->nVars; ++i) {                // Loop over the variables
    if (i == 0) continue; int* watch = &S->first[ i ];            // Get the pointer to the first watched clause
    while (*watch != END)                                         // As long as there are watched clauses
      if (*watch < S->mem_fixed) watch = (S->DB + *watch);        // Remove the watch if it points to a lemma
      else                      *watch =  S->DB[  *watch ]; }     // Otherwise (meaning an input clause) go to next watch

  while (head < tail) {                                           // While the old memory contains lemmas
    int size = 0, count = 0, *lem = head+2;                       // Get the lemma to which the head is pointing
    while (*lem) {                                      size++;   // Count the number of literals
      if ((*lem > 0) == S->model[ abs(*lem) ]) count++;  lem++; } // Count the number of satisfied literals
    if (count < 6) { addClause (S, head+2, size); S->nLemmas++; } // If the latter is smaller than four, add it back
    head = lem+1; } }                                             // Move the head to the next position after the lemma

void heapRemoveTop (struct solver* S) {                    // Removes the top of the binary heap
  S->lookup[ S->heap[0] ] = END;                           // Stamp the lookup of the top of the heap as out
  int last  = S->heap[S->heapSize--];                      // Obtain the last element in the heap
  int score = S->score[last], p = 0, c = 1;                // Obtain the score of that element, set p(arent)
  while (c <= S->heapSize) {                               // While there are children in the heap
    if ((S->score[S->heap[c]] < S->score[S->heap[c+1]]) && // If the score of the left child is smaller AND
        (c < S->heapSize)) c++;                            // A right child exists, point to the right child
    if  (S->score[S->heap[c]] < score) break;              // Break if the score of pointed child is smaller
    S->heap[p] = S->heap[c];                               // Swap last and its current child
    S->lookup[S->heap[c]] = p; p = c; c = (c<<1)+1; }	   // Update the heap lookup table and update the position
  S->heap[p] = last; S->lookup[last] = p; }                // Set the new position in the heap and update the lookup

void heapUp (struct solver* S, int var) {		   // Moves a var(iable) up in the binary heap
  int score = S->score[var], p = S->lookup[var];           // Obtain the score and the position of var in the heap
  while (p && (S->score[ S->heap[(p-1)>>1] ] < score)) {   // While its score is larger than the score of its parent
    S->heap[p] = S->heap[(p-1)>>1];                        // Swap var and its parent
    S->lookup[S->heap[p]] = p; p = (p-1)>>1; }             // Update the heap lookup table and update the position
  S->heap[p] = var; S->lookup[var] = p; }                  // Set the new position in the heap and update the lookup

void unassign (struct solver* S, int lit) {                //
  S->false[lit] = 0; int var = abs(lit);                   //
  if (S->lookup[var] == END) {                             //
    S->lookup[var] = ++S->heapSize; heapUp (S, var); } }   //

void setMark (struct solver* S, int lit) {                 // Update the involved mark and the score
  if (S->false[ lit ] != MARK) {                           // If the literal was not MARKed as involved yet
    S->score[abs(lit)] = (3 * S->score[abs(lit)] +         // Then increase the score of the corresponding variable
                         (S->nConflicts << 5)) >> 2;       // By averaging with the number of conflict clauses
    if (S->lookup[abs(lit)] != END) heapUp(S, abs(lit)); } // Update the heap to reflect the increased score
  S->false[ lit ] = MARK; }                                // And MARK the literal as involved

int implied (struct solver* S, int lit) {                  // Check if lit(eral) is implied by MARK literals
  if (S->false[lit] > MARK) return (S->false[lit] & MARK); // If checked before return old result
  if (!S->reason[abs(lit)]) return 0;                      // In case lit is a decision, it is not implied
  int *p = (S->DB + S->reason[abs(lit)] - 1);              // Get the reason of lit(eral)
  while (*(++p))                                           // While there are literals in the reason
    if ((S->false[*p] ^ MARK) && !implied(S, *p)) {        // Recursively check if non-MARK literals are implied
      S->false[lit] = 5; return 0; }                       // Return not implied (stamp 5 means not implied)
  S->false[lit] = 6; return 1; }                           // Return implied (stamp 6 means implied)

int* analyze (struct solver* S, int* clause) {     // Compute a resolvent from falsified clause
  S->nLemmas++; S->restarts++; S->nConflicts++;    // Bump restarts and bump maximum score

  while (*clause) setMark (S,*(clause++));         // MARK all literals in the falsified clause
  while (S->reason[abs(*(--S->assigned))]) {       // Loop on variables on falseStack
    if (S->false[*S->assigned] == MARK) {          // If the tail of the stack is MARK
      int *check = S->assigned;                    // Pointer to check if first-UIP is reached
      while (S->false[ *(--check) ] != MARK)	   // Check for a MARK literal before decision
        if (!S->reason[ abs(*check) ]) goto build; // Otherwise it is the first-UIP so break
      clause=(S->DB+S->reason[abs(*S->assigned)]); // Get the reason and ignore first literal
      while (*clause) setMark (S, *(clause++)); }  // MARK all literals in reason
    unassign (S, *S->assigned); }                  // Unassign the tail of the stack

  build:; int buffer[S->nVars], size = 0;
  int* p = S->assigned;                            // Loop from tail to front
  while (p >= S->forced) {                         // Only literals on the stack can be MARK
    if ((S->false[*p] == MARK) && !implied (S,*p)) // If MARK and not implied by other MARK literals
      buffer[size++] = *p;                         // Add literal to conflict clause
    if ((size == 1) && !S->reason[abs(*p)])
      S->processed = p;                            // Set backjump point (in the search)
    S->false[*(p--)] = 1; }                        // Reset the MARK flag for all variables on the stack

  while (S->assigned > S->processed)
    unassign (S, *(S->assigned--));                // Unassign all lits between tail & head
  unassign (S, *S->assigned);                      // Assigned now equal to processed
  return addClause (S, buffer, size); }            // Add new conflict clause to redundant DB

void analyzeFinal (struct solver* S, int* clause) {
  while (*clause) setMark (S, *(clause++));        // MARK all literals in the reason clause
  while (S->assigned > S->forced) {
    int lit = *(--S->assigned);
    if (S->false[lit] == MARK) {
      if (S->reason[abs(lit)]) {
        clause = (S->DB+S->reason[abs(lit)]);
        while (*clause) setMark (S, *(clause++)); }
      else printf("%i ", -lit); } }
  printf("0\n"); }

int propagate (struct solver* S) {                 // Performs unit propagation
  int forced = S->reason[abs(*S->processed)];      // Initialize forced flag
  while (S->processed < S->assigned) {             // While unprocessed false literals
    int i, lit = *(S->processed++);                // Get first unprocessed literal
    int* watch = &S->first[lit];                   // Obtain the first watch pointer
    while (*watch != END) {                        // While there are watched clauses (watched by lit)
      int* clause = (S->DB + *watch + 1);	   // Get the clause from DB
      if (!clause[-2]) clause++;                   // Set the pointer to the first literal in the clause
      if (clause[0] == lit) clause[0] = clause[1]; // Ensure that the other watched literal is in front
      for (i = 2; clause[i]; ++i)                  // Scan the non-watched literals
        if (!S->false[ clause[i] ]) {              // When clause[j] is not false, it is either true or unset
          clause[1] = clause[i]; clause[i] = lit;  // Swap literals
          int store = *watch;                      // Store the old watch
          *watch =  S->DB[*watch];                 // Remove the watch from the list of lit
          addWatch (S, clause[1], store);          // Add the watch to the list of clause[1]
          goto next_clause; }                      // Goto the next watched clause
      clause[1] = lit; watch = (S->DB + *watch);   // Set lit at clause[1] and set next watch
      if ( S->false[ -clause[0] ]) continue; 	   // If the other watched literal is satisfied continue
      if (!S->false[  clause[0] ]) {               // If the other watched literal is falsified,
        assign (S, clause, forced); }              // A unit clause is found, and the reason is set
      else if (forced) return UNSAT;               // Found a root level conflict -> UNSAT
      else { int *lemma = analyze (S, clause);	   // Analyze the conflict return a conflict clause
        assign (S, lemma, forced);                 // Assign the conflict clause as a unit
        forced = !lemma[1]; break; }               // In case a unit clause is found, set forced flag
      next_clause: ; } }                           // Set position for next clause
  if (forced) S->forced = S->processed;	           // Set S->forced if applicable
  return SAT; }	                                   // Finally, no conflict was found

int luby (int x) {                                 // Find the next number in the Luby sequence
  int size, seq;
  for (size = 1, seq = 0; size < x+1; seq++, size = 2*size+1);
  while (size-1 != x) { size = (size-1)>>1; seq--; x = x % size; }
  return seq; }

int solve (struct solver* S, int limit) {
  int restarts = 0, decision, shift = luby (restarts);
  S->mem_fixed = S->mem_used;                 // From now on, only redundant clauses will be added
  for (;;) {                                  // Main loop
    if (propagate (S) == UNSAT) return UNSAT; // UP returns UNSAT for root level conflict

    if ((limit > 0) && (S->nLemmas > limit)) return UNKNOWN;

    if (S->restarts > (100 << shift) || S->nLemmas > S->maxLemmas) {          // After more than (100 << shift) conflicts
      while (S->assigned > S->forced) unassign (S, *(--S->assigned));         // Remove all false lits from falseStack
      S->processed = S->forced; S->restarts = 0; shift = luby (++restarts); } // Reset pointers and restart counter

    if (S->nLemmas > S->maxLemmas) reduceDB (S);                  // Reduce the DB when it contains too many lemmas

    decision = 0;                                                 // Set decision literal to undefined
    if (S->assumptions < S->assumeHead) {                         // If there are unassigned assumptions
      int *cube = S->assumptions;                                 // Let cube be a pointer to the assumptions
      while (!decision && cube < S->assumeHead) {                 // While the decision is unassinged
        if (S->false[*cube]) {                                    // Check whether the top assumption is falsified
          int *reason = S->DB + S->reason[ abs(*cube) ];          // Set its reason and
          printf ("c UNSAT under the assumptions: %i ", *cube);   //
          analyzeFinal (S, reason); return UNSAT; }               // Analyze the conflicting assumption
        else if (S->false[-(*cube)]) cube++;                      // Otherwise assign the assumption to true and
        else decision = *cube; } }                                // Make it the decision literal

    while (!decision && S->heapSize) {                            // Get the next decision from the heap
      if (!S->false[S->heap[0]] && !S->false[-S->heap[0]]) break; // If the top of the heap is unassigned
      heapRemoveTop (S); }                                        // Otherwise remove the top from the heap
    if (!S->heapSize) return !UNSAT;                              // A solution is found when the heap is empty
    if (!decision)                                                // If no assumption and still free variable
      decision = S->model[S->heap[0]] ? S->heap[0] : -S->heap[0]; // Pick decision based on current model
    S->false[-decision] = 1;                                      // Assigned the decision literal to true
    *(S->assigned++) = -decision;                                 // And push it on the assigned stack
    S->reason[abs(decision)] = 0; } }                             // Decisions have no reason clauses

void allocate (struct solver* S, int n, int m) {
  if (n < 1)   n = 1;
  S->nVars       = n;
  S->nClauses    = m;
  S->mem_used    = 0;                  // The number of integers allocated in the DB
  S->nLemmas     = 0;                  // The number of learned clauses -- redundant means learned
  S->nConflicts  = 0;                  // Under of conflicts which is used to updates scores
  S->restarts    = 0;                  // Counter used for deciding when to restart
  S->maxLemmas   = 2 + (m >> 2);       // Initial maximum number of learnt clauses
  S->assumptions = getMemory (S, n+1); // List of assumptions (for incremental SAT)
  S->model       = getMemory (S, n+1); // Full assignment of the (Boolean) variables (initially set to false)
  S->score       = getMemory (S, n+1); // Variable score (based on involvement in recent conflicts).
  S->heap        = getMemory (S, n  ); // Binary heap of variables sorted by S->score
  S->heapSize    = n-1;                // Size of the heap
  S->lookup      = getMemory (S, n+1); // Lookup table for the position of a variable in the heap
  S->reason      = getMemory (S, n+1); // Array of clauses
  S->falseStack  = getMemory (S, n+1); // Stack of falsified literals -- this pointer is never changed
  S->forced      = S->falseStack;      // Points inside *falseStack at first decision (unforced literal)
  S->processed   = S->falseStack;      // Points inside *falseStack at first unprocessed literal
  S->assigned    = S->falseStack;      // Points inside *falseStack at last unprocessed literal
  S->false       = getMemory (S, 2*n+1); S->false += n; // Labels for variables, non-zero means false
  S->first       = getMemory (S, 2*n+1); S->first += n; // Offset of the first watched clause
  S->DB[S->mem_used++] = 0;            // Make sure there is a 0 before the clauses are loaded.

  int i; for (i = 1; i <= n; ++i) { S->heap[i-1] = i; S->lookup[i] = i-1; // Initialize the main datastructes:
    S->model[i] = 0; S->score[i] = 1; S->false[i] = S->false[-i] = 0;     // heap, lookup, model, score, false,
    S->first[i] = S->first[-i] = END; }                                   // and first.
  resetAssumptions (S); }                                                 // Reset the assumption array

int parse (struct solver* S, char* filename) {                            // Parse the formula and initialize
  int tmp; FILE* input = fopen (filename, "r");                           // Read the CNF file
  do { tmp = fscanf (input, " p cnf %i %i \n", &S->nVars, &S->nClauses);  // Find the first non-comment line
    if (tmp > 0 && tmp != EOF) break; tmp = fscanf (input, "%*s\n"); }    // In case a commment line was found
  while (tmp != 2 && tmp != EOF);                                         // Skip it and read next line

  allocate (S, S->nVars, S->nClauses);                     // Allocate the main datastructures

  int nZeros = S->nClauses, buffer [S->nVars], size = 0;   // Make a local buffer for parsing
  while (nZeros > 0) {                                     // While there are clauses in the file
    int lit; tmp = fscanf (input, " %i ", &lit);           // Read a literal.
    if (!lit) {                                            // If reaching the end of the clause
      int* clause = addClause (S, buffer, size);           // Then add the clause to data_base
      if (!size || ((size == 1) && S->false[ clause[0] ])) // Check for empty clause or conflicting unit
        return UNSAT;                                      // If either is found return UNSAT
      if ((size == 1) && !S->false[ -clause[0] ]) {        // Check for a new unit
        assign (S, clause, 1); }                           // Directly assign new units (forced = 1)
      size = 0; --nZeros; }                                // Reset buffer
    else buffer[size++] = lit; }                           // Add literal to buffer
  fclose (input);                                          // Close the formula file
  return SAT; }                                            // Return that no conflict was observed

void initCDCL (struct solver* S, int n, int m) {           //
   S->mem_max = MEM_MAX;                                   //
   S->DB = (int *) malloc (sizeof(int) * S->mem_max);      //
   allocate (S, n, m); }                                   //

inline int abs (int a) { return (a > 0)?(a):(-a); }        //

#ifdef STANDALONE
int memory[ MEM_MAX ];

int main (int argc, char** argv) {
  struct solver S; S.DB = memory; S.mem_max = MEM_MAX;
  if (parse (&S, argv[1]) == UNSAT) printf("s UNSATISFIABLE\n");  // Parse the DIMACS file in argv[1]
  else if  (solve (&S, 0) == UNSAT) printf("s UNSATISFIABLE\n");  // Solve without limit
  else                              printf("s SATISFIABLE\n")  ;
  printf("c statistics of %s: mem: %i conflicts: %i max_lemmas: %i\n", argv[1], S.mem_used, S.nConflicts, S.maxLemmas); }
#endif
