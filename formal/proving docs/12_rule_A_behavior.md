12_rule_A_behavior.md

Purpose
This file records the behavior of Selection Rule A on minimal toy systems.
It is purely descriptive and contains no interpretation.

For each toy system, the file specifies:
• P, E, X, and edge relations R_pq
• ordering <= and neighbor relation
• an initial seed (p0, C(p0))

Then it applies Rule A step-by-step and records only:
• whether A(p) was empty or non-empty
• which (q*, x*) was selected
• whether the process halts
• whether it assigns multiple nodes
• whether it forces contradiction or becomes undefined

No dynamics beyond Rule A is introduced.

Common conventions used in this file
1. Ordering
Unless otherwise stated: p1 <= p2 <= p3 <= ...

2. Neighbor relation (locality)
Neighbors are determined by edges E:
q is a neighbor of p iff (p, q) is in E or (q, p) is in E.

3. Configuration set and tie-break
Unless otherwise stated:
X = {0, 1}
Fixed ordering on X for tie-break: 0 < 1

4. Constraint relation for "not-equal"
For an edge (p, q):
R_pq = {(0, 1), (1, 0)}

5. Rule A reminder (compressed)
Given C(p) defined:
F(p) = { q | p <= q and q neighbor of p }
A(p) = { (q, x) | q in F(p) and (C(p), x) in R_pq }
If A(p) non-empty:
• choose minimal q* among q in A(p)
• choose x* uniquely if unique, else least x* by fixed ordering on X
Set C(q*) = x*
If A(p) empty: rule undefined at p (halt)

CASE 1 — 2-node chain

Test harness
P = {p1, p2}
E = {(p1, p2)}
Ordering: p1 <= p2
Neighbors: p1 neighbor p2
X = {0, 1}
R_p1p2 = {(0, 1), (1, 0)}  (not-equal)

Initial seed
p0 = p1
C(p1) = 0

Step log
Step at p = p1
F(p1) = {p2}
A(p1) = {(p2, 1)}  (since (0,1) allowed)
A(p1): non-empty
Selected (q*, x*) = (p2, 1)
Define C(p2) = 1

Step at p = p2
F(p2) = {}  (no neighbor q with p2 <= q)
A(p2) = {}
A(p2): empty
Result: undefined at p2 (halt)

Outcome summary
A(p1): non-empty
Selected: (p2, 1)
Halts: yes (at p2)
Assigns multiple nodes: yes (p1 and p2 assigned)
Contradiction/undefined: undefined at p2 (no forward neighbor)

CASE 2 — 3-node chain

Test harness
P = {p1, p2, p3}
E = {(p1, p2), (p2, p3)}
Ordering: p1 <= p2 <= p3
Neighbors: edges define neighbors
X = {0, 1}
R_p1p2 = not-equal
R_p2p3 = not-equal

Initial seed
p0 = p1
C(p1) = 0

Step log
Step at p = p1
F(p1) = {p2}
A(p1) = {(p2, 1)}
A(p1): non-empty
Selected (q*, x*) = (p2, 1)
Define C(p2) = 1

Step at p = p2
F(p2) = {p3}  (p1 is not forward since p2 <= p1 is false)
A(p2) = {(p3, 0)}  (since (1,0) allowed)
A(p2): non-empty
Selected (q*, x*) = (p3, 0)
Define C(p3) = 0

Step at p = p3
F(p3) = {}
A(p3) = {}
A(p3): empty
Result: undefined at p3 (halt)

Outcome summary
A(p1): non-empty
Selected: (p2, 1)
A(p2): non-empty
Selected: (p3, 0)
Halts: yes (at p3)
Assigns multiple nodes: yes (p1, p2, p3 assigned)
Contradiction/undefined: undefined at p3 (no forward neighbor)

CASE 3 — 3-cycle (odd cycle) with "not-equal" constraint (from 08)

Test harness
P = {p1, p2, p3}
E = {(p1, p2), (p2, p3), (p3, p1)}
Ordering: p1 <= p2 <= p3
Neighbors: edges define neighbors
X = {0, 1}
All edges: not-equal

Initial seed
p0 = p1
C(p1) = 0

Step log
Step at p = p1
F(p1) = {p2, p3}  (both are neighbors and forward)
A(p1) includes:
• (p2, 1) from edge (p1,p2)
• (p3, 1) from edge (p1,p3)
A(p1): non-empty
Minimal q* is p2
Selected (q*, x*) = (p2, 1)
Define C(p2) = 1

Step at p = p2
F(p2) = {p3}  (p1 not forward)
A(p2) = {(p3, 0)}  (since (1,0) allowed on (p2,p3))
A(p2): non-empty
Selected (q*, x*) = (p3, 0)
Define C(p3) = 0

Check implied edge constraints with existing assignments (descriptive check)
Assigned: C(p1)=0, C(p2)=1, C(p3)=0
Edge (p3, p1) requires not-equal, but (0,0) violates R_p3p1

Outcome summary
A(p1): non-empty
Selected: (p2, 1)
A(p2): non-empty
Selected: (p3, 0)
Halts: not by emptiness during steps above
Assigns multiple nodes: yes (all three assigned)
Contradiction/undefined: contradiction occurs (edge (p3,p1) violated)

CASE 4 — 4-cycle (even cycle) with "not-equal"

Test harness
P = {p1, p2, p3, p4}
E = {(p1,p2), (p2,p3), (p3,p4), (p4,p1)}
Ordering: p1 <= p2 <= p3 <= p4
Neighbors: edges define neighbors
X = {0, 1}
All edges: not-equal

Initial seed
p0 = p1
C(p1) = 0

Step log
Step at p = p1
F(p1) = {p2, p4}
A(p1) includes:
• (p2, 1)
• (p4, 1)
A(p1): non-empty
Minimal q* is p2
Selected (q*, x*) = (p2, 1)
Define C(p2) = 1

Step at p = p2
F(p2) = {p3}
A(p2) = {(p3, 0)}
A(p2): non-empty
Selected (q*, x*) = (p3, 0)
Define C(p3) = 0

Step at p = p3
F(p3) = {p4}
A(p3) = {(p4, 1)}
A(p3): non-empty
Selected (q*, x*) = (p4, 1)
Define C(p4) = 1

Check implied edge constraints with existing assignments (descriptive check)
Assigned: C(p1)=0, C(p2)=1, C(p3)=0, C(p4)=1
All edges satisfy not-equal, including (p4,p1): (1,0) allowed

Step at p = p4
F(p4) = {}  (p1 not forward)
A(p4) = {}
A(p4): empty
Result: undefined at p4 (halt)

Outcome summary
A(p1): non-empty
Selected: (p2, 1)
A(p2): non-empty
Selected: (p3, 0)
A(p3): non-empty
Selected: (p4, 1)
Halts: yes (at p4)
Assigns multiple nodes: yes (all four assigned)
Contradiction/undefined: undefined at p4 (no forward neighbor), no contradiction observed

CASE 5 — 3-node branching "V" graph

Test harness
P = {p1, p2, p3}
E = {(p1,p2), (p1,p3)}
Ordering: p1 <= p2 <= p3
Neighbors: edges define neighbors
X = {0, 1}
Edges: not-equal on both (p1,p2) and (p1,p3)
No edge between p2 and p3

Initial seed
p0 = p1
C(p1) = 0

Step log
Step at p = p1
F(p1) = {p2, p3}
A(p1) includes:
• (p2, 1)
• (p3, 1)
A(p1): non-empty
Minimal q* is p2
Selected (q*, x*) = (p2, 1)
Define C(p2) = 1

Step at p = p2
F(p2) = {}  (p2 has only neighbor p1, which is not forward)
A(p2) = {}
A(p2): empty
Result: undefined at p2 (halt)

Unassigned node note (descriptive)
C(p3) remains undefined because the rule halted before selecting any continuation from p1 to p3.

Outcome summary
A(p1): non-empty
Selected: (p2, 1)
Halts: yes (at p2)
Assigns multiple nodes: yes (p1 and p2 assigned; p3 unassigned)
Contradiction/undefined: undefined at p2 (no forward neighbor)

End of file

