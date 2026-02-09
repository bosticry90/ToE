14\_rule\_C\_behavior.md



Purpose

This file records the behavior of Selection Rule C on minimal toy systems for the specific seed C\_partial(p1)=0 under the base ordering in each case; expanded runs over additional seeds and order variants are recorded in 14C\_rule\_C\_python\_trace.md.



This file is purely descriptive and contains no interpretation.

For each toy system, the file specifies:

• the parameter set P, edge set E, configuration set X, and edge relations R\_pq

• the ordering <= and neighbor (locality) relation

• an initial seed (p0, C(p0))

It then applies Rule C step-by-step and records only:

• whether A(p) was empty or non-empty

• which (q\*, x\*) was selected

• whether the process halts (and by which halt state)

• whether multiple nodes are assigned

• whether a contradiction occurs or the rule becomes undefined

No dynamics beyond Rule C are introduced.



Execution semantics

This file evaluates Rule C under the execution semantics defined in 13\_selection\_process\_semantics.md, including:

• halting states (HALTED\_EMPTY, HALTED\_CONTRADICTION, HALTED\_UNDEFINED)

• contradiction check timing (immediately after each attempted new assignment)

• reassignment is prohibited (attempting to assign an already-assigned node yields HALTED\_UNDEFINED)

• if a contradiction check fails, the attempted assignment is not counted as a successful new assignment



Common conventions used in this file

1\. Ordering

Unless otherwise stated:

p1 <= p2 <= p3 <= ...

Ordering is used only for deterministic tie-breaking among candidates.



2\. Neighbor relation (locality)

Neighbors are determined by edges E:

q is a neighbor of p iff (p, q) is in E or (q, p) is in E.



3\. Configuration set and tie-break

Unless otherwise stated:

X = {0, 1}

Fixed ordering on X for tie-break: 0 < 1.



4\. Constraint relation for "not-equal"

For any constrained edge (p, q):

R\_pq = {(0,1), (1,0)}.



5\. Edge-orientation convention (explicit)

Edge checks use the edge-orientation convention (Option A) from 13\_selection\_process\_semantics.md:

• constraints are checked on oriented pairs (p,q)

• if only R\_pq is supplied for an unordered connection {p,q}, then R\_qp is interpreted as transpose(R\_pq)

• if neither orientation is supplied, the edge is treated as unconstrained



6\. Rule C reminder (compressed)

Given a current active node p with C\_partial(p) defined:

• N\_unassigned(p) = { q | q is a neighbor of p and q not in Dom(C\_partial) }

• A(p) = { (q, x) | q in N\_unassigned(p) and (C\_partial(p), x) in R\_pq }

If A(p) is non-empty:

• choose minimal q\* under ordering <=

• choose unique x\* if unique, else least x\* under fixed ordering on X

• attempt to assign C\_partial(q\*) := x\*, then immediately contradiction-check against already-assigned neighbors of q\*

If contradiction check fails: halt with HALTED\_CONTRADICTION (attempted assignment not counted as successful).

If A(p) is empty: halt with HALTED\_EMPTY.



Note on order variants (descriptive only)

When multiple neighbors are admissible at a step, changing the total order used for tie-breaking can change which neighbor is selected first. This is expected and does not violate “order-symmetry” as defined (the ordering is used only as a deterministic tie-break, not as a privileged direction of continuation).



CASE 1 — 2-node chain

Test harness

P = {p1, p2}

E = {(p1, p2)}

Ordering: p1 <= p2

X = {0, 1}

R\_p1p2 = not-equal



Initial seed

p0 = p1

C\_partial(p1) = 0

p\_active = p1



Step log

Step at p = p1

N\_unassigned(p1) = {p2}

A(p1) = {(p2, 1)}

• A(p1): non-empty

• Selected (q\*, x\*) = (p2, 1)

• Attempt assignment: C\_partial(p2) := 1

• Contradiction check at q\* = p2 against already-assigned neighbor p1:

&nbsp; Using Option A, R\_p2p1 is interpreted as transpose(R\_p1p2), so (C\_partial(p2), C\_partial(p1)) = (1,0) is permitted.

• Update p\_active := p2



Step at p = p2

N\_unassigned(p2) = {} (only neighbor is p1, already assigned)

A(p2) = {}

• A(p2): empty

Result: halt with HALTED\_EMPTY



Outcome summary

• Halts: yes

• Halt state: HALTED\_EMPTY (no unassigned neighbor candidates)

• Assigns multiple nodes: yes (p1 and p2 assigned)

• Contradiction/undefined: no



CASE 2 — 3-node chain

Test harness

P = {p1, p2, p3}

E = {(p1, p2), (p2, p3)}

Ordering: p1 <= p2 <= p3

X = {0, 1}

R\_p1p2 = not-equal

R\_p2p3 = not-equal



Initial seed

p0 = p1

C\_partial(p1) = 0

p\_active = p1



Step log

Step at p = p1

N\_unassigned(p1) = {p2}

A(p1) = {(p2, 1)}

• Selected (p2, 1)

• Assign C\_partial(p2) := 1

• Contradiction check at p2 vs assigned neighbor p1: (1,0) permitted (using Option A orientation for the check on (p2,p1))

• Update p\_active := p2



Step at p = p2

N\_unassigned(p2) = {p3} (p1 assigned, p3 unassigned)

A(p2) = {(p3, 0)}

• Selected (p3, 0)

• Assign C\_partial(p3) := 0

• Contradiction check at p3 vs assigned neighbor p2: (0,1) permitted

• Update p\_active := p3



Step at p = p3

N\_unassigned(p3) = {} (only neighbor p2 is assigned)

A(p3) = {}

Result: halt with HALTED\_EMPTY



Outcome summary

• Halts: yes

• Halt state: HALTED\_EMPTY

• Assigns multiple nodes: yes (p1, p2, p3 assigned)

• Contradiction/undefined: no



CASE 3 — 3-cycle (odd cycle) with "not-equal"

Test harness

P = {p1, p2, p3}

E = {(p1, p2), (p2, p3), (p3, p1)}

Ordering: p1 <= p2 <= p3

X = {0, 1}

All edges: not-equal



Initial seed

p0 = p1

C\_partial(p1) = 0

p\_active = p1



Step log

Step at p = p1

N\_unassigned(p1) = {p2, p3}

A(p1) = {(p2, 1), (p3, 1)}

• A(p1): non-empty

• Minimal q\* is p2

• Selected (q\*, x\*) = (p2, 1)

• Assign attempt: C\_partial(p2) := 1

• Contradiction check at p2 vs assigned neighbor p1: (1,0) permitted

• Update p\_active := p2



Step at p = p2

N\_unassigned(p2) = {p3} (p1 assigned, p3 unassigned)

A(p2) = {(p3, 0)}

• Selected (q\*, x\*) = (p3, 0)

• Assign attempt: C\_partial(p3) := 0

• Contradiction check at p3 vs already-assigned neighbors {p2, p1}:

&nbsp; ? check with p2: (0,1) permitted

&nbsp; ? check with p1: (0,0) not permitted (violates not-equal on oriented edge (p3,p1))

Result: halt with HALTED\_CONTRADICTION (the attempted assignment to p3 is not counted as a successful new assignment)



Outcome summary

• Halts: yes

• Halt state: HALTED\_CONTRADICTION (contradiction detected immediately after attempting to assign p3)

• Assigns multiple nodes: yes (p1 and p2 assigned; p3 attempt triggers contradiction)

• Contradiction/undefined: contradiction occurs



CASE 4 — 4-cycle (even cycle) with "not-equal"

Test harness

P = {p1, p2, p3, p4}

E = {(p1, p2), (p2, p3), (p3, p4), (p4, p1)}

Ordering: p1 <= p2 <= p3 <= p4

X = {0, 1}

All edges: not-equal



Initial seed

p0 = p1

C\_partial(p1) = 0

p\_active = p1



Step log

Step at p = p1

N\_unassigned(p1) = {p2, p4}

A(p1) = {(p2, 1), (p4, 1)}

• Minimal q\* is p2

• Selected (p2, 1)

• Assign C\_partial(p2) := 1

• Contradiction check at p2 vs p1: (1,0) permitted

• Update p\_active := p2



Step at p = p2

N\_unassigned(p2) = {p3}

A(p2) = {(p3, 0)}

• Selected (p3, 0)

• Assign C\_partial(p3) := 0

• Contradiction check at p3 vs p2: (0,1) permitted

• Update p\_active := p3



Step at p = p3

N\_unassigned(p3) = {p4}

A(p3) = {(p4, 1)}

• Selected (p4, 1)

• Assign C\_partial(p4) := 1

• Contradiction check at p4 vs already-assigned neighbors {p3, p1}:

&nbsp; ? with p3: (1,0) permitted

&nbsp; ? with p1: (1,0) permitted

• Update p\_active := p4



Step at p = p4

N\_unassigned(p4) = {} (neighbors p3 and p1 are assigned)

A(p4) = {}

Result: halt with HALTED\_EMPTY



Outcome summary

• Halts: yes

• Halt state: HALTED\_EMPTY

• Assigns multiple nodes: yes (all four assigned)

• Contradiction/undefined: no contradiction observed



CASE 5 — 3-node branching "V" graph

Test harness

P = {p1, p2, p3}

E = {(p1, p2), (p1, p3)}

Ordering: p1 <= p2 <= p3

X = {0, 1}

Edges: not-equal on both (p1,p2) and (p1,p3)

No edge between p2 and p3



Initial seed

p0 = p1

C\_partial(p1) = 0

p\_active = p1



Step log

Step at p = p1

N\_unassigned(p1) = {p2, p3}

A(p1) = {(p2, 1), (p3, 1)}

• Minimal q\* is p2

• Selected (p2, 1)

• Assign C\_partial(p2) := 1

• Contradiction check at p2 vs p1: (1,0) permitted

• Update p\_active := p2



Step at p = p2

N\_unassigned(p2) = {} (only neighbor p1 is assigned)

A(p2) = {}

Result: halt with HALTED\_EMPTY



Note (descriptive only): p3 remains unassigned when the run halts.



Outcome summary

• Halts: yes

• Halt state: HALTED\_EMPTY

• Assigns multiple nodes: yes (p1 and p2 assigned; p3 unassigned)

• Contradiction/undefined: no



End of file



