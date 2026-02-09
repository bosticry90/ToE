11B\_candidate\_selection\_rule\_B.md



Purpose

This file proposes a second explicit candidate selection principle (Rule B).

It is introduced solely for controlled comparison with Rule A.

Rule B differs from Rule A only in that it is order-symmetric rather than order-asymmetric.



Order-symmetry here means that the rule does not privilege a forward or backward direction along the ordering; the ordering is used only as a tie-breaking convention, not as a notion of continuation.



It is not privileged, interpreted, or assumed to be correct.

Its sole purpose is to test whether order-asymmetry is responsible for the observed failures of Rule A.

Failure of this rule does not falsify the framework.

Only failure of all admissible selection classes would do so.



1\. Classification of this selection rule

This candidate selection rule belongs to the following classes:

• Deterministic

• Strictly local

• Memoryless

• Order-symmetric

• Single-continuation

No global information, optimization, probability, or interpretation is used.



2\. Context

This rule operates within the existing structure:

• a parameter set P

• an ordering relation <= on P

• a locality relation defining neighbors

• a configuration set X

• a constraint structure defining admissible pairs

• a local consistency condition



This rule is evaluated under the execution semantics defined in 13\_selection\_process\_semantics.md.

In particular, edge admissibility checks use the edge-orientation convention (Option A) from 13\_selection\_process\_semantics.md:

• constraints are checked on oriented pairs (p,q)

• if only R\_pq is supplied for an unordered connection {p,q}, then R\_qp is interpreted as transpose(R\_pq)

• if neither orientation is supplied, the edge is treated as unconstrained



No additional assumptions are introduced.



3\. Informal description

At each applicable step, the rule extends a configuration assignment by selecting a locally admissible neighboring configuration without privileging forward or backward direction along the ordering.

Continuation is symmetric with respect to the ordering and does not imply time, causation, or evolution.



4\. Formal statement of the rule

Let p be a parameter value in P for which a configuration C\_partial(p) is defined.



Define the neighbor set:

N(p) = { q in P | q is a neighbor of p }



Unlike Rule A, N(p) does not restrict neighbors by the ordering relation.



Define the admissible neighbor extensions:

A(p) = { (q, x) | q in N(p),

x in X,

and (C\_partial(p), x) satisfies the local consistency condition on the oriented edge (p, q) }



Selection rule S\_B:

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

• privilege forward continuation along <=

• guarantee that A(p) is non-empty

• guarantee global consistency

• backtrack or revise prior selections

• use global information

• optimize or minimize any quantity

• assign probability or likelihood

• imply physical time or causation



Undefined behavior is permitted and counts as failure.



6\. Relationship to constraints and consistency

• The rule operates strictly inside locally admissible pairs

• It never selects an inadmissible configuration

• It cannot repair inconsistency

• If local consistency cannot be satisfied at some step, the process halts



If this rule fails due to inconsistency, that failure is attributed to the rule, not the framework.



7\. Falsification behavior of this rule

This selection rule is considered unsuccessful if:

• it almost always halts immediately

• it produces only trivial or frozen assignments

• it leads rapidly to contradiction even when global consistency exists

• or it requires modification to avoid failure



No modifications or patches are permitted.



8\. Scope and limitations

This file does not define:

• equations of motion

• time or temporal evolution

• probabilities

• optimization principles

• physical interpretation

• uniqueness or stability of outcomes



It defines one explicit, order-symmetric selection rule for testing purposes only.



Status

This file introduces a second candidate selection principle consistent with:

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

• 11\_candidate\_selection\_rule\_A.md

• and the README



If this rule fails, it is discarded without prejudice.



End of file



