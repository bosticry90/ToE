09_selection_principle.md
Purpose
This file introduces a minimal selection principle (a first form of genuine dynamics).
A selection principle is a rule that chooses which locally consistent configurations are realized along the ordering.
This file is the first place where the framework permits a rule-like “what happens next” statement. However, it does not assume physical time, causation, probability, or interpretation.
The goal is to define selection in the weakest possible sense without violating prior files.
    1. Context
This file builds on:
    • a parameter set P
    • an ordering relation <= on P
    • a configuration assignment form C(p)
    • a locality relation defining neighboring parameter values
    • a global constraint structure
    • a local consistency condition
    • global consistency / existence questions
No physical meaning is assumed.
    2. What selection adds (and what it does not add)
Selection adds one new idea:
    • among the many locally consistent possibilities, some are chosen and others are not.
Selection does not automatically add:
    • physical time,
    • causation,
    • probability,
    • optimization,
    • or interpretation.
Those may be introduced later only if explicitly stated and justified.
    3. Local extension set (what is available to choose from)
Fix a parameter value p in P.
Let N(p) be the set of neighbors of p under the locality relation.
A locally admissible neighbor-pair at p is any pair of configurations (x, y) such that:
    • x is a possible configuration for p
    • y is a possible configuration for some neighbor q in N(p)
    • and (x, y) satisfies the local consistency condition for the neighbor comparison between p and q.
This defines, in principle, a set of locally admissible options available around p.
This section does not claim these options exist or are finite.
    4. Selection principle (minimal definition)
A selection principle is a rule S that, whenever it is applicable, chooses a locally consistent continuation along the ordering.
Minimal requirements for S:
    • S must use only:
        ? the ordering on P,
        ? the locality relation,
        ? and the local consistency condition (constraint structure).
    • S must not require ad hoc exceptions tied to particular configurations.
    • S must not be defined solely to force a desired outcome.
One minimal form of selection is:
Given a parameter value p and the current configuration C(p),
S selects:
    • a neighbor q in N(p) with p <= q, and
    • a configuration C(q),
such that (C(p), C(q)) is locally consistent.
This introduces a directed notion of “continuation” along the ordering, but it does not claim that:
    • q is “later” in a physical sense,
    • C(p) causes C(q),
    • or that this continuation is unique.
    5. Distinction between constraints and selection
Constraints:
    • classify pairs as allowed or disallowed.
Selection:
    • chooses one allowed option (or a restricted set of allowed options) to be realized.
Selection is not permitted to change constraints.
Selection must operate inside the admissible space defined by constraints and locality.
    6. Relationship to global consistency
Two cases must be distinguished:
Case A: Global consistency exists
    • There exists at least one assignment that satisfies local consistency everywhere.
    • Selection may be used to choose one such assignment, or to generate a consistent chain that can extend toward a global assignment.
Case B: Global consistency does not exist
    • No assignment satisfies local consistency everywhere.
    • In this case, selection cannot rescue the framework by ignoring constraints or adding exceptions.
    • The hypothesis is rejected according to the README.
Selection is therefore subordinate to consistency: it may resolve underdetermination, but it may not repair contradiction.
    7. Minimal falsification criteria for selection
The selection principle is unacceptable (and the hypothesis fails) if any of the following occur:
    1. Selection requires violating constraints
If the rule can only operate by selecting inadmissible pairs, the selection principle is invalid.
    2. Selection requires ad hoc exceptions
If the rule only works by introducing case-by-case patches tied to particular configurations, it violates minimality.
    3. Selection forces unbounded complexity
If defining selection requires an ever-growing set of special rules to handle new situations, it violates the project’s simplicity constraint.
    4. Selection collapses into interpretation
If the rule cannot be stated without importing physical meaning (particles, forces, spacetime) at this stage, it violates the project’s sequencing principle.
    8. Scope and limitations
This file does not define:
    • a specific functional form of S,
    • a unique successor relation on P,
    • probabilities or stochastic rules,
    • optimization or minimization,
    • differential equations,
    • physical time,
    • physical interpretation.
It only defines what a selection principle is in the weakest sense and sets strict boundaries on its legitimacy.
Status
This file introduces the first genuine selection concept consistent with:
    • 00_existence.md
    • 01_change.md
    • 02_constraints.md
    • 03_constraint_structure.md
    • 04_ordering.md
    • 05_locality.md
    • 06_local_consistency.md
    • 07_global_consistency.md
    • 08_global_consistency_analysis.md
    • and the README.
If selection cannot be defined without violating constraints, requiring ad hoc exceptions, or importing interpretation prematurely, the hypothesis is rejected according to the README.
End of file

