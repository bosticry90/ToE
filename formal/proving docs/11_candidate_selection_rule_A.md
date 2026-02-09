11\_candidate\_selection\_rule\_A.md



Purpose

This file proposes a single, explicit candidate selection principle (Rule A).

It is introduced solely as a test object.

This selection rule is not privileged, not interpreted, and not assumed to be correct.

It exists to determine whether any admissible selection principle can generate nontrivial, internally consistent structure without violating prior constraints.

Failure of this rule does not falsify the framework.

Only failure of all admissible selection rules would do so.



1\. Classification of this selection rule

This candidate selection rule belongs to the following classes:

• Deterministic

• Strictly local

• Memoryless

• Order-asymmetric

• Single-continuation

No global information, optimization, probability, or interpretation is used.



2\. Context

This rule operates within the following existing structure:

• a parameter set P

• an ordering relation <= on P

• a locality relation defining neighbors

• a configuration set X

• a constraint structure defining admissible pairs

• a local consistency condition



This rule is evaluated under the execution semantics defined in 13\_selection\_process\_semantics.md.



Edge admissibility and edge checks use the edge-orientation convention (Option A) from 13\_selection\_process\_semantics.md:

• constraints are checked on oriented pairs (p,q)

• if only R\_pq is supplied for an unordered connection {p,q}, then R\_qp is interpreted as transpose(R\_pq)

• if neither orientation is supplied, the edge is treated as unconstrained



No additional assumptions are introduced.



3\. Informal description

At each applicable step, the rule extends a configuration assignment forward along the ordering by selecting the earliest admissible neighboring continuation.

This introduces a directed notion of continuation without invoking time, causation, or physical evolution.



4\. Formal statement of the rule

Let p be a parameter value in P for which a configuration C\_partial(p) is defined.



4.1 Forward neighbor set

Define the forward neighbor set:

F(p) = { q in P | p <= q and q is a neighbor of p }



This is the only difference from an order-symmetric neighbor definition: Rule A restricts candidate neighbors to those not preceding p under <=.



4.2 Admissible forward extension set

Define the admissible forward extension set:

A(p) = { (q, x) | q in F(p),

x in X,

and (C\_partial(p), x) satisfies the local consistency condition on the oriented edge (p, q) }



4.3 Selection rule S\_A

If A(p) is non-empty, select the pair (q\*, x\*) such that:

• q\* is minimal with respect to the ordering <= among all q appearing in A(p)

• x\* is the unique configuration paired with q\* if uniqueness holds;

otherwise select the least x\* under an arbitrary but fixed ordering on X



Then perform the step as specified by 13\_selection\_process\_semantics.md:

• attempt the assignment C\_partial(q\*) := x\*

• perform the contradiction check timing and definition from 13\_selection\_process\_semantics.md Section 5

• if the rule attempts an operation outside its stated permissions, halt with HALTED\_UNDEFINED



If A(p) is empty, the run halts with status HALTED\_EMPTY (per 13\_selection\_process\_semantics.md).



5\. What this rule does not do

This rule does not:

• guarantee that A(p) is non-empty

• guarantee global consistency

• resolve conflicts at future steps

• backtrack or revise prior selections

• use global information

• optimize or minimize any quantity

• assign probability or likelihood

• imply physical time or causation



Undefined behavior is permitted and counts as failure.



6\. Relationship to constraints and consistency

• The rule operates strictly inside locally admissible pairs.

• It never selects an inadmissible configuration.

• It cannot repair inconsistency.

• If local consistency cannot be satisfied at some step, the process halts.



If this rule fails due to inconsistency, that failure is attributed to the rule, not the framework.



7\. Falsification behavior of this rule

This selection rule is considered unsuccessful if:

• it almost always halts immediately,

• it produces only trivial or frozen assignments,

• it leads rapidly to contradiction even when global consistency exists,

• or it requires modification to avoid failure.



No modifications or patches are permitted.



8\. Scope and limitations

This file does not define:

• equations of motion

• time or temporal evolution

• probabilities

• optimization principles

• physical interpretation

• uniqueness or stability of outcomes



It defines one explicit, minimal selection rule for testing purposes only.



Status

This file introduces a single candidate selection principle consistent with:

• 00\_existence.md

• 01\_change.md

• 02\_constraints.md

• 03\_constraint\_structure.md

• 04\_ordering.md

• 05\_locality.md

• 06\_local\_consistency.md

• 07\_global\_consistency.md

• 08\_global\_consistency\_analysis.md

• 09\_selection\_principle.md

• 10\_selection\_classes.md

• and the README



If this rule fails, it is discarded without prejudice.



End of file



