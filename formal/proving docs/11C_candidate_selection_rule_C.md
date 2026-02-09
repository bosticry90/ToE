11C_candidate_selection_rule_C.md
Purpose
This file defines a third explicit candidate selection principle (Rule C).
Rule C differs from Rule B only by restricting candidate neighbors to unassigned neighbors.
It is introduced to test whether reassignment pressure—rather than order symmetry or locality—is responsible for prior rule failures.
Rule C is not privileged, interpreted, or assumed to be correct.
It exists solely as a test object.
Failure of this rule does not falsify the framework.
Only failure of all admissible selection classes would do so.

1. Classification of this selection rule
This candidate selection rule belongs to the following classes:
    • Deterministic
    • Strictly local
    • Memoryless
    • Order-symmetric
    • Single-continuation
No global information, optimization, probability, or interpretation is used.

2. Context
This rule operates within the existing structure:
    • a parameter set P
    • an ordering relation <= on P (used only for deterministic tie-breaking)
    • a locality relation defining neighbors
    • a configuration set X
    • a constraint structure defining admissible pairs
    • a local consistency condition
    • the selection process semantics defined in 13_selection_process_semantics.md
No additional assumptions are introduced.

3. Informal description
At each applicable step, the rule extends a partial configuration assignment by selecting a locally admissible configuration on an unassigned neighboring node.
The rule does not:
    • privilege forward or backward direction along the ordering,
    • revisit or revise previously assigned nodes,
    • guarantee global consistency,
    • or avoid halting.
Continuation is symmetric with respect to the ordering and does not imply time, causation, or physical evolution.

4. Formal statement of the rule
Let p be a parameter value in P such that C_partial(p) is defined.
4.1 Unassigned neighbor set
Define the unassigned neighbor set:
N_unassigned(p) = { q in P | q is a neighbor of p and q not in Dom(C_partial) }
Only unassigned neighbors are considered as candidates.

4.2 Admissible extension set
Define the admissible extension set:
A(p) = { (q, x) | q in N_unassigned(p),
x in X,
(C_partial(p), x) satisfies the local consistency condition on edge (p, q) }

4.3 Selection rule S_C
If A(p) is non-empty, select a pair (q*, x*) such that:
    • q* is minimal with respect to the ordering <= among all q appearing in A(p)
    • x* is the unique configuration paired with q* if uniqueness holds;
otherwise, x* is the least element under a fixed ordering on X
Then extend the partial assignment by defining:
C_partial(q*) = x*
and update the active parameter value to:
p_active := q*

4.4 Undefined behavior
If A(p) is empty, the rule is undefined at p and the run halts with status HALTED_EMPTY.
If the rule attempts any operation outside its stated permissions, the run halts with status HALTED_UNDEFINED.
Reassignment is structurally impossible under this rule because assigned nodes are excluded from N_unassigned(p).

5. What this rule does not do
This rule does not:
    • consider assigned neighbors as candidates
    • reassign or revise configurations
    • backtrack or branch
    • search for alternative active nodes
    • use global information
    • optimize or minimize any quantity
    • assign probabilities or likelihoods
    • imply physical time, causation, or evolution
Undefined behavior is permitted and counts as failure.

6. Relationship to constraints and consistency
    • The rule operates strictly inside locally admissible pairs.
    • It never selects an inadmissible configuration.
    • It cannot repair inconsistency.
    • Contradictions are detected only via the contradiction check defined in 13_selection_process_semantics.md.
If the rule halts due to contradiction or emptiness, that outcome is attributed to the rule, not the framework.

7. Falsification behavior of this rule
This selection rule is considered unsuccessful if:
    • it almost always halts immediately,
    • it produces only trivial or frozen assignments,
    • it leads rapidly to contradiction even when global consistency exists,
    • or it requires modification to avoid failure.
No modifications or patches are permitted.

8. Scope and limitations
This file does not define:
    • equations of motion
    • time or temporal evolution
    • probabilities
    • optimization principles
    • physical interpretation
    • uniqueness or stability of outcomes
It defines one explicit, minimal selection rule for testing purposes only.

Status
This file introduces a third candidate selection principle consistent with:
    • 00_existence.md
    • 01_change.md
    • 02_constraints.md
    • 03_constraint_structure.md
    • 04_ordering.md
    • 05_locality.md
    • 06_local_consistency.md
    • 07_global_consistency.md
    • 08_global_consistency_analysis.md
    • 09_selection_principle.md
    • 10_selection_classes.md
    • 11_candidate_selection_rule_A.md
    • 11B_candidate_selection_rule_B.md
    • 13_selection_process_semantics.md
    • and the README
If this rule fails, it is discarded without prejudice.
End of file

