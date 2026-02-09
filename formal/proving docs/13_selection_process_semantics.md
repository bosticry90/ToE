13\_selection\_process\_semantics.md
Purpose
This file defines minimal, explicit process semantics for running a selection rule.
It does not introduce physical time, causation, probability, optimization, or interpretation.
Its only purpose is to make "apply a selection rule step-by-step" well-defined and falsifiable.

1. Context
   This file builds on:

* a parameter set P
* an ordering relation <= on P (used only as a deterministic tie-break unless explicitly stated otherwise)
* a locality relation defining neighbors (via an edge set E, or equivalent)
* a configuration set X
* edge relations R\_pq subset X x X defining local admissibility
  Edge-orientation convention (Option A): edges are treated as ordered pairs (p,q). For each unordered connection {p,q} both relations R\_pq and R\_qp must be supplied; if only one is provided, interpret R\_qp as the transpose of R\_pq (i.e., R\_qp = { (y,x) | (x,y) in R\_pq }) unless the rule explicitly states otherwise. With this convention checks on an oriented edge (p,q) are unambiguous. If neither R\_pq nor R\_qp is supplied for a neighboring pair, the edge is treated as unconstrained: by default, no constraint applies across that edge (i.e., all value pairs are permitted), rather than being treated as an error. Rules that require a different convention must state so explicitly.
* a local consistency condition (equivalently: (x,y) in R\_pq means locally consistent on edge (p,q))

2. Run state
   A run state is a triple (C\_partial, p\_active, status) where:

* C\_partial is a partial assignment: a function defined on a subset Dom(C\_partial) subset P
  such that for each p in Dom(C\_partial), C\_partial(p) is in X.
* p\_active is a parameter value in Dom(C\_partial) at which the next step is evaluated.
* status is one of: RUNNING, HALTED\_EMPTY, HALTED\_CONTRADICTION, HALTED\_UNDEFINED.

No assumption is made that a run exists for all seeds or all systems.

3. Step
   Given a RUNNING state (C\_partial, p\_active, RUNNING), a single step consists of:

* computing the candidate extension set A(p\_active) as specified by the selection rule being tested
* if A(p\_active) is empty, set status = HALTED\_EMPTY and stop
* otherwise, select one pair (q\*, x\*) from A(p\_active) per the selection rule
* check whether q\* ∈ Dom(C\_partial).
  * if q\* is already in Dom(C\_partial) then this attempted assignment is prohibited; set status = HALTED\_UNDEFINED and stop
  * otherwise, perform the assignment: set C\_partial(q\*) := x\* (a successful new assignment)
* perform the contradiction check described in Section 5 using the post-assignment value of q\*.
  * if the contradiction check fails, set status = HALTED\_CONTRADICTION and stop
  * otherwise (contradiction check passed), update p\_active := q\* and continue (state remains RUNNING)
If the rule attempts an operation not permitted by its definition (e.g., selecting or assigning where it forbids assignment), status = HALTED\_UNDEFINED and stop.

4. Halting conditions
   A run halts only by one of these explicit conditions:

* HALTED\_EMPTY: the selection rule produced an empty candidate set A(p\_active)
* HALTED\_CONTRADICTION: the contradiction check failed after an attempted extension
* HALTED\_UNDEFINED: the selection rule required an action outside its stated permissions
  No other halting notion is assumed.

5. Contradiction check timing and definition
   Contradiction is checked immediately after each successful new assignment of a node q\*.
   Let q\* be the newly assigned node. For every neighbor r of q\* that was already assigned prior to this step (i.e., r ∈ Dom(C\_partial) before the assignment), check the edge constraint relation R\_{q\*,r} using the post-assignment value of q\*:

* using the edge-orientation convention from Section 1, test that (C\_partial(q\*), C\_partial(r)) ∈ R\_{q\*,r}.
  If any required edge check fails, the run halts with status = HALTED\_CONTRADICTION and the attempted assignment is not considered a successful new assignment.

This check is local and static: it validates local consistency of the newly-assigned value against already-assigned neighbors at the moment immediately following the assignment.

6. Reassignment convention (semantics-level, not a patch)
   Selection Rule C is defined to prohibit reassignment by construction: it only considers unassigned neighbors as candidates. Therefore:

* if a rule's candidate set is defined to exclude already-assigned nodes, reassignment never occurs
* any reassignment event would indicate the rule was not applied as defined, and is treated as HALTED\_UNDEFINED

Note: rule definitions belong in rule-definition files (not behavior logs); if any rule is currently documented only in a behavior file, relocate or cross-reference the canonical rule-definition file (e.g., a file named along the lines of 'candidate\_selection\_rule\_C.md').

End of file

