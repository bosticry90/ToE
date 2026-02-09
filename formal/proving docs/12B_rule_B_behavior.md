12B_rule_B_behavior.md

Purpose
This file records the behavior of Selection Rule B on minimal toy systems.
It is purely descriptive and contains no interpretation.

For each toy system, this file specifies:
- the parameter set P
- the edge set E
- the configuration set X
- the edge relations R_pq
- the ordering <= and neighbor (locality) relation
- an initial seed (p0, C(p0))

It then applies Rule B step by step and records only:
- whether A(p) was empty or non-empty
- which (q*, x*) was selected
- whether the process halts
- whether multiple nodes are assigned
- whether a contradiction occurs or the rule becomes undefined

No dynamics beyond Rule B are introduced.

Execution semantics
All runs in this file are evaluated under the execution semantics defined in
13_selection_process_semantics.md, including:
- canonical halt states (HALTED_EMPTY, HALTED_CONTRADICTION, HALTED_UNDEFINED)
- contradiction check timing (immediately after an attempted new assignment)
- prohibition of reassignment at the semantics level

Assignment convention (harness-level)
Rule B itself does not prohibit reassignment. However, under the execution
semantics, any attempt to assign a value to a node already in Dom(C_partial)
is treated as an invalid operation and halts the run with status HALTED_UNDEFINED.

This is a harness-level convention used to align observed behavior with the
canonical halt states defined in 13_selection_process_semantics.md. It is not a
modification of Rule B.

Common conventions used in this file

1. Ordering
Unless otherwise stated:
p1 <= p2 <= p3 <= ...
The ordering is used only for deterministic tie-breaking among candidates and
carries no directional meaning.

2. Neighbor relation (locality)
Neighbors are determined by edges E:
q is a neighbor of p iff (p, q) ∈ E or (q, p) ∈ E.

3. Configuration set and tie-break
Unless otherwise stated:
X = {0, 1}
Fixed ordering on X for tie-break:
0 < 1

4. Constraint relation for "not-equal"
For any constrained edge (p, q):
R_pq = {(0,1), (1,0)}

5. Rule B reminder (compressed)
Given C(p) defined:
N(p) = { q | q is a neighbor of p }
A(p) = { (q, x) | q ∈ N(p) and (C(p), x) ∈ R_pq }

If A(p) is non-empty:
- choose minimal q* under ordering <=
- choose unique x* if unique, otherwise choose the least x* under the fixed
  ordering on X
- define C(q*) = x*

If A(p) is empty:
- the rule is undefined at p

Note: In Rule B, the ordering relation <= is used only as a deterministic
tie-break and does not encode directionality or continuation.

------------------------------------------------------------
CASE 1 — 2-node chain
------------------------------------------------------------

Test harness
P = {p1, p2}
E = {(p1, p2)}
Ordering: p1 <= p2
X = {0, 1}
R_p1p2 = not-equal

Initial seed
p0 = p1
C(p1) = 0

Step log
Step at p = p1
N(p1) = {p2}
A(p1) = {(p2, 1)}
- A(p1) non-empty
- Selected (p2, 1)
- Define C(p2) = 1

Step at p = p2
N(p2) = {p1}
A(p2) = {(p1, 0)}
- A(p2) non-empty
- Selected (p1, 0)
- Attempted assignment to already-assigned node p1

Result
The run halts with status HALTED_UNDEFINED.

Outcome summary
- Halts: yes
- Halt state: HALTED_UNDEFINED
- Assigns multiple nodes: yes
- Halt reason: attempted reassignment

------------------------------------------------------------
CASE 2 — 3-node chain
------------------------------------------------------------

Test harness
P = {p1, p2, p3}
E = {(p1, p2), (p2, p3)}
Ordering: p1 <= p2 <= p3
X = {0, 1}
All edges: not-equal

Initial seed
p0 = p1
C(p1) = 0

Step log
Step at p = p1
N(p1) = {p2}
A(p1) = {(p2, 1)}
- Selected (p2, 1)
- Define C(p2) = 1

Step at p = p2
N(p2) = {p1, p3}
A(p2) = {(p1, 0), (p3, 0)}
- Minimal q* is p1
- Attempted assignment to already-assigned node p1

Result
The run halts with status HALTED_UNDEFINED.

Outcome summary
- Halts: yes
- Halt state: HALTED_UNDEFINED
- Assigns multiple nodes: yes
- Halt reason: attempted reassignment

------------------------------------------------------------
CASE 3 — 3-cycle (odd cycle) with not-equal
------------------------------------------------------------

Test harness
P = {p1, p2, p3}
E = {(p1, p2), (p2, p3), (p3, p1)}
Ordering: p1 <= p2 <= p3
X = {0, 1}
All edges: not-equal

Initial seed
p0 = p1
C(p1) = 0

Step log
Step at p = p1
N(p1) = {p2, p3}
A(p1) = {(p2, 1), (p3, 1)}
- Selected (p2, 1)
- Define C(p2) = 1

Step at p = p2
N(p2) = {p1, p3}
A(p2) = {(p1, 0), (p3, 0)}
- Minimal q* is p1
- Attempted assignment to already-assigned node p1

Result
The run halts with status HALTED_UNDEFINED.

Outcome summary
- Halts: yes
- Halt state: HALTED_UNDEFINED
- Assigns multiple nodes: yes
- Halt reason: attempted reassignment

------------------------------------------------------------
CASE 4 — 4-cycle (even cycle) with not-equal
------------------------------------------------------------

Test harness
P = {p1, p2, p3, p4}
E = {(p1, p2), (p2, p3), (p3, p4), (p4, p1)}
Ordering: p1 <= p2 <= p3 <= p4
X = {0, 1}
All edges: not-equal

Initial seed
p0 = p1
C(p1) = 0

Step log
Step at p = p1
- Selected (p2, 1)
- Define C(p2) = 1

Step at p = p2
A(p2) includes (p1, 0) and (p3, 0)
- Minimal q* is p1
- Attempted assignment to already-assigned node p1

Result
The run halts with status HALTED_UNDEFINED.

Outcome summary
- Halts: yes
- Halt state: HALTED_UNDEFINED
- Assigns multiple nodes: yes
- Halt reason: attempted reassignment

------------------------------------------------------------
CASE 5 — 3-node branching V graph
------------------------------------------------------------

Test harness
P = {p1, p2, p3}
E = {(p1, p2), (p1, p3)}
Ordering: p1 <= p2 <= p3
X = {0, 1}
Edges: not-equal on (p1, p2) and (p1, p3)

Initial seed
p0 = p1
C(p1) = 0

Step log
Step at p = p1
A(p1) = {(p2, 1), (p3, 1)}
- Selected (p2, 1)
- Define C(p2) = 1

Step at p = p2
N(p2) = {p1}
A(p2) = {(p1, 0)}
- Attempted assignment to already-assigned node p1

Result
The run halts with status HALTED_UNDEFINED.

Outcome summary
- Halts: yes
- Halt state: HALTED_UNDEFINED
- Assigns multiple nodes: yes
- Halt reason: attempted reassignment

End of file
