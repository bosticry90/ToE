\# CAUS-01 — Structural Causality / Well-Posedness Gate (Locality / Admissibility)



\*\*Inventory linkage:\*\* CAUS-01  

\*\*Purpose:\*\* Structural admissibility gates for candidate deformation terms and/or operator extensions.  

\*\*Epistemic level:\*\* Structural / semantics-defined.  

\*\*Not a physical claim.\*\*



---



\## Scope and intent



This document defines \*\*causality / well-posedness–motivated structural gates\*\* for admissible extensions.

It does \*\*not\*\*:

\- Prove well-posedness

\- Derive energy estimates

\- Establish finite-speed propagation theorems

\- Perform analytic PDE classification (hyperbolic/parabolic/elliptic)

\- Upgrade epistemic status



It \*\*only\*\*:

\- Defines admissibility gates (CAUS-01)

\- Records PASS / FAIL / UNDECIDED under stated semantics

\- Specifies exclusion consequences (structural pruning)

\- Points to evidence artifacts (Lean/Python) when they exist



CAUS-01 does not attempt to classify hyperbolic/parabolic structure; locality is a structural proxy only.



Pattern enforced:



> \*\*Baseline → Gate → Consequence\*\*



---



\## Baseline principle



A candidate term/extension is admissible under CAUS-01 only if it does not structurally violate the baseline

“time-forward evolution” intent of EQ-01 / EQ-02 (and their operator packaging), under the semantics stated here.



This is a \*\*pruning constraint\*\*: passing is not validation; failing is sufficient for exclusion.



---



\## Gate semantics (binding within CAUS-01 only)



\### Gate C1 — No ψ-independent forcing (source-free admissibility)



\*\*Requirement:\*\*

The extension must vanish at zero field:

\- For deformation term `P\[ψ]`: `P\[0] = 0`

\- For operator form `E(ψ, …)`: `E(0, …) = 0` (no constant source injection)



\*\*Interpretation:\*\*

No ψ-independent forcing terms are permitted.



\*\*Consequence:\*\*

FAIL ⇒ excluded from FN-01 candidate admissible family (member-level exclusion).



---



\### Gate C2 — Time-forward evolution form (no elliptic-in-time behavior)



\*\*Requirement (structural):\*\*

The evolution form must not introduce “elliptic-in-time” constraints, i.e.:

\- No terms that require solving an elliptic equation in time at each step

\- No inversion of time-derivative operators as part of the definition

\- No dependence on future-time values (no acausal evaluation)



\*\*Allowed (structural):\*\*

\- Algebraic dependence on `ψ` and spatial derivatives

\- First-order-in-time evolution (NLSE-style) or second-order-in-time evolution (UCFF-style)

\- Finite compositions of such operators without inversion



\*\*Consequence:\*\*

FAIL ⇒ excluded.



\*\*Lean note:\*\* In Lean, C2 is represented as a \*\*caller-supplied semantic predicate\*\* `NoEllipticInTime(P)`; no PDE classification is performed.



---



\### Gate C3 — Locality admissibility (no nonlocal / integral / global coupling)



\*\*Requirement (structural):\*\*

The extension must be local in space under CAUS-01 semantics (structural proxy for causal propagation intent):

\- `P\[ψ](x)` may depend on `ψ` and finitely many spatial derivatives evaluated at `x`

\- Disallowed: explicit spatial integrals, global functionals, convolution kernels, or “depends on ψ elsewhere” definitions



\*\*Notes:\*\*

\- Spectral implementations are permitted as \*computational representations\* only if they represent a local operator (e.g., Laplacian).

\- Any explicitly nonlocal kernel is FAIL.



\*\*Consequence:\*\*

FAIL ⇒ excluded.



\*\*Lean note:\*\* In Lean, C3 is represented as a \*\*caller-supplied semantic predicate\*\* `IsLocal(P)`; CAUS-01 does not attempt to formalize locality from analytic structure.



---



\### Gate C4 — Operator-order sanity (bounded differential order and no mixed time-order escalation)



\*\*Requirement (structural):\*\*

\- Spatial differential order must be finite and declared

\- Time-order must remain within the intended packaging:

&nbsp; - For EQ-02-style (first-order-in-time) layer: do not introduce second-order-in-time terms

&nbsp; - For UCFF-style (second-order-in-time) layer: do not introduce higher-than-second time derivatives



**Consequence:**

FAIL ⇒ excluded under CAUS-01.



**Notes:**

Mixed time-order escalation suggests a different equation family, but that is handled outside CAUS-01 and does not alter the CAUS-01 outcome.


\*\*Lean note:\*\* In Lean, C4 is represented as a \*\*caller-supplied semantic predicate\*\* `TimeOrderSane(form, P)` parameterized by the declared evolution form; CAUS-01 does not attempt to inspect operators to infer time-derivative order.


---



\## Classification rule



| Outcome      | Meaning |

|-------------|--------|

| \*\*PASS\*\*     | Satisfies all CAUS-01 gates under stated semantics |

| \*\*FAIL\*\*     | Violates at least one gate |

| \*\*UNDECIDED\*\*| Not yet evaluated under current semantics |



No conditional exceptions or tuning are permitted.



---



\## Consequences



\- CAUS-01 gates are \*\*structural pruning constraints\*\*.

\- Passing CAUS-01 does \*\*not\*\* imply well-posedness or physical validity.

\- Failing CAUS-01 is sufficient grounds for \*\*member-level exclusion\*\*.

\- CAUS-01 is intended to be combined conjunctively with CT-01 and SYM-01.



---



\*\*End of CAUS-01\*\*



