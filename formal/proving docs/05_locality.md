05\_locality.md
Purpose
This file defines locality along the ordering.
Locality specifies which configuration comparisons are considered relevant along the parameter ordering.
It does not define dynamics, evolution, causation, or laws of change.
This file exists to test whether a notion of “neighboring” can be introduced without importing dynamics or interpretation.

1. Ordered parameter context
   This file builds on the existence of:
   • a parameter set P,
   • a comparison relation <= on P,
   • and a configuration assignment C(p) for each p in P.
   No additional structure on P is assumed beyond what is stated in 04\_ordering.md.
2. Local neighborhood relation
   A local neighborhood relation is a rule that identifies, for each parameter value p in P, a set of parameter values considered local to p.
   Local neighborhoods are defined abstractly and may vary with p.
   No assumption is made that neighborhoods:
   • have fixed size,
   • are symmetric,
   • are uniform across P,
   • or contain only a single element.
   The locality rule must be definable using only the parameter set P and the comparison relation <=, and must not depend on the values of any particular configuration.
3. Neighboring comparisons
   Two parameter values p1 and p2 are said to be neighbors if p2 lies within the local neighborhood of p1 (or vice versa).
   Neighboring does not imply:
   • immediate succession,
   • minimal distance,
   • causation,
   • or direction.
   It only defines relevance for comparison.
4. Locality as a restriction on admissible comparisons
   Locality restricts which pairs of configurations are compared when evaluating constraints.
   Constraints are evaluated only between configurations C(p1) and C(p2) where p1 and p2 are neighbors under the locality relation.
   This does not state that non-neighboring configurations cannot differ.
   It only states that constraints do not apply directly to non-local pairs.
5. Independence from dynamics and causation
   Locality does not imply:
   • that configurations influence one another,
   • that one configuration gives rise to another,
   • that change propagates,
   • or that evolution occurs.
   Locality only limits the scope of comparison, not the mechanism of change.
6. Minimality of locality
   Locality must be definable:
   • explicitly,
   • using finite conditions,
   • without reference to specific configurations,
   • and without requiring ad hoc exceptions.
   If locality cannot be defined without collapsing into a rule of evolution or optimization, the hypothesis is rejected according to the README.
7. Scope and limitations
   This file does not define:
   • dynamics or evolution,
   • equations of motion,
   • rates, derivatives, or continuity,
   • probabilities,
   • physical meaning.
   It only defines which comparisons are considered local along the ordering.

Status
This file introduces locality along the ordering consistent with:
• 00\_existence.md,
• 01\_change.md,
• 02\_constraints.md,
• 03\_constraint\_structure.md,
• 04\_ordering.md,
• and the README.
If locality cannot be defined without becoming a form of dynamics or causation, the hypothesis is rejected according to the README.

End of file

