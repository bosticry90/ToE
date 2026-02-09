08_global_consistency_analysis.md
Purpose
This file provides a non-dynamical analysis of global consistency by giving a concrete representation of locality and constraints, and by stating explicitly and constructively that local satisfiability does not imply global satisfiability.
No dynamics, evolution, selection, causation, or time are introduced.
    1. Locality graph G = (P, E)
The locality graph is defined as follows:
Vertices: the parameter set P.
Edges: a pair (p, q) is an element of E if and only if p and q are neighbors under the locality relation.
The graph encodes which parameter values are locally comparable.
No assumptions are made about:
    • graph finiteness,
    • connectivity,
    • direction,
    • acyclicity,
    • or geometry.
The locality graph is static and fully determined by the locality definition.
    2. Constraints as relations on edges
Let X denote the set of all possible configurations.
For each edge (p, q) in E, the constraint structure induces a binary relation:
R_pq is a subset of X × X
such that:
(x, y) is an element of R_pq if and only if (x, y) satisfies the local consistency condition.
A global configuration assignment is a function:
C : P -> X
The assignment is globally consistent if, for every edge (p, q) in E,
(C(p), C(q)) is an element of R_pq.
Constraints are static admissibility relations.
They do not generate, rank, or select configurations.
    3. Local satisfiable does not imply global satisfiable
It is not generally true that local satisfiability implies global satisfiability.
That is:
    • Even if every edge relation R_pq is non-empty,
    • and even if every edge admits at least one locally consistent pair,
there may exist no global configuration assignment that satisfies all edge constraints simultaneously.
Minimal toy counterexample (odd cycle with "not-equal" constraint)
Parameter set:
P = {p1, p2, p3}
Locality graph:
E = {(p1, p2), (p2, p3), (p3, p1)}
(a 3-cycle)
Configuration set:
X = {0, 1}
Constraint on every edge:
R_pq = {(0, 1), (1, 0)}
(values must differ)
Local satisfiability:
Each edge admits allowed pairs.
Global inconsistency:
No assignment C : P -> {0, 1} can satisfy all three edges simultaneously.
Any attempt forces a contradiction on the cycle.
This demonstrates that local consistency everywhere does not guarantee global consistency.
Status
This file provides a concrete, static framework for analyzing global consistency, consistent with:
    • 00_existence.md
    • 01_change.md
    • 02_constraints.md
    • 03_constraint_structure.md
    • 04_ordering.md
    • 05_locality.md
    • 06_local_consistency.md
    • 07_global_consistency.md
    • and the README.
No dynamics or selection principles are introduced.
End of file

