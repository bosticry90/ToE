# Post-scalar-only-Yukawa deterministic packet-review scientific-response selection v0

Date: `2026-07-19`  
Target: `select_post_scalar_only_yukawa_deterministic_forward_model_packet_review_scientific_response_v0`  
Verdict: `SELECTED_FINAL_DETERMINISTIC_IDENTIFIABILITY_CONTRACT_REPAIR_PACKET_PREPARATION`

## Selected response

```text
route:
REPAIR_DETERMINISTIC_IDENTIFIABILITY_EXECUTION_CONTRACT

repair scope:
FOUR IDENTIFIABILITY INTERFACES ONLY

accepted v0 gates:
20 / 24 FROZEN

next target:
prepare_scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_packet_v1
```

The v0 review established a contract-completeness block, not physical
unidentifiability. No forward vector was produced, no Jacobian was computed,
and no deterministic execution occurred. This selection authorizes preparation
of one final, narrow v1 repair packet. It does not prepare that packet or
authorize execution.

## Frozen boundary

The twenty accepted gates remain immutable in v1. Only these failed interfaces
may change:

1. `G18_JACOBIAN_FINITE_DIFFERENCE_STEPS`
2. `G20_RANK_DEFICIENT_NUISANCE_PROJECTOR`
3. `G21_TRANSITION_DOMAIN_EXACTNESS`
4. `G22_IDENTIFIABILITY_REFINEMENT_STABILITY`

The harmonic convention, real-150 ordering, shared Newtonian/Yukawa kernel,
energy-to-torque path, analytic benchmarks, mutations, symmetry controls,
sixteen perturbation maps, common-amplitude degeneracy, serialization, and
Stage B firewall are preserved byte-for-byte or by frozen custody hash.

## Compared responses

| Response | Score | Disposition |
| --- | ---: | --- |
| Four-interface deterministic identifiability repair | 165 | Selected for final v1 packet preparation |
| Smaller exploratory deterministic calculation | 129 | Deferred unless v1 review finds a new foundation defect |
| Simplify the nuisance set | 121 | Deferred; would change the scientific question |
| Close the synthetic torsion-balance lane | 120 | Deferred until one fair repaired execution is considered |
| Redesign the internal apparatus | 80 | Deferred; premature before local identifiability is evaluated |

The selected response remains first in all 24 frozen one-at-a-time weight
variants. These scores select research order; they are not probabilities or
scientific results.

## Required v1 numerical contract

### Dimensionless coordinates and finite differences

The scalar coordinate is

\[
q_\lambda=\log(\lambda/10^{-3}\ {\rm m}).
\]

Every nuisance uses `q_j=(p_j-p_j0)/s_j`. The frozen scale `s_j` is the
positive half-width of the already accepted v0 test range: `0.02`, `0.01`,
`0.01`, `1e-4 m`, `1e-4 m`, `1e-5 m`, `1e-4 m`, `1e-4 m`, `1e-3 rad`,
`0.002`, and `1e-17 N m` for each of the six background columns, in the
accepted parameter order.

For every nonlinear column v1 must freeze the dimensionless ladder

```text
h = [1e-2, 3e-3, 1e-3]
```

with centered differences at interior points and the second-order three-point
forward or backward formula at a boundary. Exact-linear columns retain the
accepted analytic derivative path. The two finest valid steps define the
plateau test after the accepted global output scaling:

```text
RMS(D_3e-3 - D_1e-3)
  <= 1e-10 + 5e-3 * RMS(D_1e-3)
```

All perturbed evaluations must succeed. No result-dependent step adaptation is
allowed. Replacing the ladder by an oversized `h=0.3` or undersized `h=1e-8`
must fail a dedicated mutation control.

### Rank-deficient nuisance projector

The dimensionless nuisance derivatives are globally output-scaled, zero
columns are detected at `||n_j||_2 <= sqrt(150)*1e-12`, and every remaining
column is divided by its Euclidean norm. For

\[
\widetilde N=U\Sigma V^{\mathsf T},
\]

the central retained rank uses `sigma_i/sigma_1 > 1e-10`. Mandatory threshold
probes use `1e-9` and `1e-11`. The projector is

\[
P_\perp=I-U_rU_r^{\mathsf T},
\qquad
\eta_\lambda=\frac{\|P_\perp j_\lambda\|_2}{\|j_\lambda\|_2}.
\]

The implementation must fail closed if the scalar column meets the zero-column
floor. It must verify `||U_r^T U_r-I||_2 <= 1e-12` and relative retained-space
reconstruction residual `<=1e-9`. Exact duplicate columns must reduce rank
without a crash. Pairwise absolute correlation `>=0.999`, retained condition
number `>=1e8`, or threshold-probe rank disagreement is reported as a
near-degeneracy.

The already accepted decision bands remain frozen:

```text
eta_lambda <= 1e-6:
INDISTINGUISHABLE_AT_POINT

eta_lambda >= 1e-3:
IDENTIFIABLE_AT_POINT

otherwise:
IDENTIFIABILITY_CLASSIFICATION_UNRESOLVED
```

No arbitrary `eta_lambda > 0.5` rule is introduced.

### Exact transition domain

The accepted 25-point scalar grid remains

\[
\lambda_i=10^{-5+i/6}\ {\rm m},\qquad i=0,\ldots,24.
\]

With `d_min=1e-4 m` and `d_max=1e-2 m`, the exact decision-bearing transition
domain is the frozen index set `i=4,...,20`, the grid points satisfying
`d_min/3 <= lambda_i <= 3*d_max`. All rank, correlation, projector, `eta_lambda`,
and refinement comparisons are evaluated there. Five additional regime
sentinels are evaluated directly at

\[
\{d_{\min}/3,\ d_{\min},\ \sqrt{d_{\min}d_{\max}},\ d_{\max},\ 3d_{\max}\}.
\]

There is no post-result point selection. A single favorable or unstable point
cannot represent the domain. The accepted rule requiring five contiguous
identifiable grid points is adjudicated only inside indices `4,...,20`.
The five direct sentinels are mandatory regime diagnostics but cannot be used
to manufacture contiguity. After every numerical-stability rule passes, the
domain classification is frozen as follows:

```text
at least five contiguous transition-grid points with eta_lambda >= 1e-3:
DETERMINISTIC_PARAMETER_IDENTIFIABLE

all seventeen transition-grid points with eta_lambda <= 1e-6:
BLOCKED_PARAMETER_IDENTIFIABILITY

otherwise:
IDENTIFIABILITY_CLASSIFICATION_UNRESOLVED
```

Any unstable decision-bearing point produces the corresponding numerical
block before this physical classification is considered.

### Refinement stability

Across the final two accepted production refinements, v1 must require:

```text
retained rank:
identical

eta_lambda:
absolute change <= 0.02
and relative change <= 5% when max eta_lambda > 1e-6

maximum scalar-nuisance absolute correlation:
absolute change <= 0.02

largest nuisance-subspace principal angle:
<= 1 degree

decision-bearing log10 singular values:
absolute change <= 0.05 decades

exact/near-degeneracy labels and point classification:
identical
```

The three SVD thresholds must also agree on retained rank and point
classification, with `eta_lambda` spread `<=0.02`. Forward-vector convergence
does not override a Jacobian-stability failure.

## Mandatory production-path controls

V1 must require all ten controls through the production forward model,
Jacobian builder, scaler, projector, and refinement adjudicator:

1. Oversized finite-difference step fails plateau validation.
2. Undersized noise-dominated step fails plateau validation.
3. Exact duplicate nuisance columns reduce rank without crashing.
4. Near-duplicate nuisance columns trigger near-degeneracy.
5. A stable result survives all three SVD thresholds within tolerance.
6. One unstable transition point cannot stand for the full domain.
7. Converged forward vectors with unstable Jacobian classification remain blocked.
8. A scalar column proportional to calibration yields `eta_lambda=0` within `1e-12`.
9. An injected nuisance-orthogonal scalar direction yields `eta_lambda=1` within `1e-12`.
10. No test-only substitute may replace a production component.

## Authorized v1 review outcomes

```text
DETERMINISTIC_IDENTIFIABILITY_CONTRACT_READY
BLOCKED_FINITE_DIFFERENCE_PLATEAU
BLOCKED_NUISANCE_PROJECTOR_UNSTABLE
BLOCKED_TRANSITION_DOMAIN_CONTRACT
BLOCKED_IDENTIFIABILITY_REFINEMENT_STABILITY
```

Only the first outcome may make one deterministic execution eligible. Physical
`BLOCKED_PARAMETER_IDENTIFIABILITY` remains an execution result, not a packet
preparation or review result.

## Final-repair boundary

V1 is the last automatic Stage A contract repair. If independent v1 review
finds another foundational identifiability-contract defect, no v2 repair is
authorized automatically. A later selector must choose among nuisance-set
simplification, apparatus redesign, a smaller exploratory deterministic
calculation, or lane closure.

## Current exact posture

```text
Stage A packet v0:
BLOCKED_PARAMETER_IDENTIFIABILITY

physical unidentifiability:
NOT ESTABLISHED

accepted gates:
20 / 24 FROZEN

deterministic execution:
NOT AUTHORIZED / NOT PERFORMED

forward vector:
NOT PRODUCED

Jacobian:
NOT COMPUTED

Stage B:
DEFERRED / NOT AUTHORIZED

synthetic or empirical constraint:
NONE

current authority:
prepare_scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_packet_v1
```
