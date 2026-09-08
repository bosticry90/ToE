# Scalar-only Yukawa deterministic torsion-balance forward-model validation packet review v1

Date: `2026-07-19`  
Target: `review_scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_packet_v1_result`  
Verdict: `DETERMINISTIC_IDENTIFIABILITY_CONTRACT_READY`

## Independent review result

```text
contract review:
ACCEPTED

physical forward-model validation:
NOT PERFORMED

physical identifiability:
NOT DETERMINED

authorized execution count:
ONE

next target:
execute_scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_v1_once
```

V1 makes the future local-identifiability judgment numerically reproducible
without changing the accepted deterministic physics. This is a contract result,
not a benchmark, vector, Jacobian, rank, or identifiability result.

## V0 freeze audit

The review verified the complete SHA-256 custody chain for the v0 packet and
review. It then compared the thirteen embedded v0 contract surfaces directly
against the canonical v0 JSON values and independently recomputed every
canonical fragment hash. All thirteen compare equal.

The accepted-gate evidence map covers exactly the selector's twenty accepted
gate identifiers. It binds the harmonic convention, real-150 ordering,
production kernel, torque derivation, benchmarks, mutations, symmetries,
convergence floor, sixteen perturbation maps, Jacobian order and previously
accepted scale/bands, serialization, and Stage B boundary to frozen content.

Only the selector's failed interfaces are repaired:

```text
G18_JACOBIAN_FINITE_DIFFERENCE_STEPS
G20_RANK_DEFICIENT_NUISANCE_PROJECTOR
G21_TRANSITION_DOMAIN_EXACTNESS
G22_IDENTIFIABILITY_REFINEMENT_STABILITY
```

## G18 review — pass

The reviewer reconstructed the nuisance scales from the positive half-widths
of the sixteen accepted v0 perturbation ranges. They equal the v1 table. The
seventeen columns partition exactly into seven finite-difference columns and
ten accepted exact-linear columns, without omission or overlap.

The dimensionless ladder, centered formula, second-order one-sided formulas,
stencil-validity rule, finite real-150 output requirement, plateau rule, and
failed-evaluation outcome are numeric and deterministic. Adaptation,
extrapolation, and fallback steps are forbidden.

For the production ladder's largest step `h=0.01`, every preregistered scalar
decision point and sentinel supports a centered `q_lambda` stencil inside the
unchanged `1e-5 m` to `1e-1 m` scalar envelope. The smallest perturbed sentinel
is `(1e-4/3) exp(-0.01) > 1e-5 m`; the largest is
`3e-2 exp(0.01) < 1e-1 m`. Every nominal nuisance point has `q=0`, so its
centered stencil lies inside the frozen `[-1,1]` range. The one-sided rule is
therefore complete but is not silently invoked for the decision grid.

The oversized control uses `[1.0,0.6,0.3]`; the undersized control uses
`[1e-7,3e-8,1e-8]` with a frozen sign-keyed `1e-11 Y_*` mutation. Both retain a
real plateau comparison rather than failing merely for a missing second step.

## G20 review — pass

V1 defines one path:

```text
dimensionless derivatives
→ accepted global output scaling
→ zero-column detection
→ unit-norm nuisance columns
→ thin SVD
→ retained basis
→ truncated pseudoinverse and orthogonal projector
→ eta_lambda
→ threshold/refinement adjudication
```

The central relative cutoff is `1e-10`, with mandatory `1e-9` and `1e-11`
probes. Normal-equation projection is forbidden. Individual zero columns are
excluded safely; an all-zero nuisance matrix has frozen rank-zero,
zero-pseudoinverse, and identity-projector behavior. Exact duplicates reduce
rank without exception. Near-degeneracy triggers cover correlation, retained
condition number, and threshold-rank disagreement.

The scalar norm floor, projector residual, orthonormality residual,
pseudoinverse, and

\[
\eta_\lambda=\|P_\perp j_\lambda\|_2/\|j_\lambda\|_2
\]

are exact. The interval between `1e-6` and `1e-3` remains unresolved. Threshold
disagreement cannot be rounded into a favorable result.

## G21 review — pass

The reviewer independently solved

\[
d_{\min}/3\le10^{-5+i/6}\le3d_{\max}
\]

for integer `i` in `0,...,24`, using `d_min=1e-4 m` and `d_max=1e-2 m`.
The result is exactly `i=4,...,20`. The independently recomputed seventeen
values, five direct sentinels, and canonical registration SHA-256 equal the v1
packet.

All decision metrics are required at every registered point. Sentinels cannot
substitute for contiguity, and post-result selection or reordering blocks the
execution. A single favorable point cannot classify the apparatus.

## G22 review — pass

The synchronized medium/fine levels use values already present in the accepted
v0 convergence ladders:

```text
IDENT_R_MEDIUM: angular 256, cubature 16, energy check 2.5e-4 rad
IDENT_R_FINE:   angular 512, cubature 24, energy check 1.25e-4 rad
```

The reviewer verified numeric limits for retained rank, decision-bearing log
singular values, principal angle, maximum scalar–nuisance correlation,
`eta_lambda`, degeneracy labels, point classification, and rank-threshold
probes. Forward convergence has no override authority.

## Production-control review — pass

All ten controls name the same five production components:

```text
frozen v0 production forward model
v1 Jacobian builder
v1 dimensionless scaler
v1 thin-SVD projector
v1 refinement/classification adjudicator
```

Production-component test doubles are forbidden. Declared mutations act only
at frozen input or returned-array boundaries. The controls cover oversized and
undersized steps, exact and near duplicates, three rank thresholds, scalar
equality with calibration, an orthogonal scalar direction, transition-grid
tampering, refinement instability despite converged forward vectors, and
component provenance.

No control was executed during review. This review verifies the executable
contract and routing that the single authorized execution must instantiate.

## Review burden and authorization

All ten independent-review obligations pass. In particular, V1 and this review
record no forward-model call, benchmark, mutation, vector, Jacobian, singular
value, projector, `eta_lambda`, or physical classification.

This accepted review authorizes exactly one deterministic Stage A execution.
That execution must produce a canonical result package and stop for independent
result review. It may return:

```text
DETERMINISTIC_FORWARD_MODEL_VALIDATED
BLOCKED_PARAMETER_IDENTIFIABILITY
IDENTIFIABILITY_CLASSIFICATION_UNRESOLVED
BLOCKED_FINITE_DIFFERENCE_PLATEAU
BLOCKED_NUISANCE_PROJECTOR_UNSTABLE
BLOCKED_IDENTIFIABILITY_REFINEMENT_STABILITY
```

`DETERMINISTIC_FORWARD_MODEL_VALIDATED` must include identifiability support in
the tested domain under the frozen domain rule. It makes Stage B eligible only
for a fresh decision; it does not authorize Stage B.

## Final-attempt and scope firewall

```text
automatic V2:
NOT AUTHORIZED

Stage B:
NOT AUTHORIZED

noise / covariance / Monte Carlo / likelihood / forecast:
NONE AUTHORIZED

synthetic or empirical constraint:
NONE

alpha:
NOT SELECTED

scalar branch:
NOT ADOPTED
```

If the single execution encounters a final numerical or foundational block,
the next response must select among simplification, redesign, a smaller
nonauthoritative study, lane closure, or another ToE priority. It may not create
v2 automatically.

## Current exact posture

```text
Stage A V1 packet review:
DETERMINISTIC_IDENTIFIABILITY_CONTRACT_READY

deterministic executions authorized:
1

deterministic executions performed:
0

forward vector:
NOT PRODUCED

Jacobian / SVD / eta_lambda:
NOT COMPUTED

physical identifiability:
NOT DETERMINED

Stage B:
DEFERRED / NOT AUTHORIZED

current authority:
execute_scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_v1_once
```

