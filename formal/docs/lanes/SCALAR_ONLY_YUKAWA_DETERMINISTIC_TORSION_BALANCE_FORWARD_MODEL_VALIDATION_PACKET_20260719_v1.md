# Scalar-only Yukawa deterministic torsion-balance forward-model validation packet v1

Date: `2026-07-19`  
Target: `prepare_scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_packet_v1`  
Verdict: `PREPARED_FINAL_DETERMINISTIC_IDENTIFIABILITY_CONTRACT_REPAIR_PENDING_INDEPENDENT_REVIEW`

## Authority and boundary

This packet consumes the selected route

```text
REPAIR_DETERMINISTIC_IDENTIFIABILITY_EXECUTION_CONTRACT
```

and repairs only:

```text
G18_JACOBIAN_FINITE_DIFFERENCE_STEPS
G20_RANK_DEFICIENT_NUISANCE_PROJECTOR
G21_TRANSITION_DOMAIN_EXACTNESS
G22_IDENTIFIABILITY_REFINEMENT_STABILITY
```

The twenty accepted v0 gates are hash-pinned. The v0 apparatus, harmonic,
real-150, kernel, torque, benchmark, mutation, symmetry, perturbation,
serialization, convergence, output, work-package, execution-control, and Stage
B boundary surfaces are incorporated without semantic change.

No forward-model function is called by this preparation. No vector, Jacobian,
singular value, correlation, projector, or `eta_lambda` value is calculated.

## G18 — executable numerical derivative construction

The accepted parameter order remains one scalar-range column followed by the
sixteen nuisance columns. The scalar coordinate is

\[
q_\lambda=\log(\lambda/10^{-3}\ {\rm m}).
\]

Every nuisance uses

\[
q_j=(p_j-p_{j,0})/s_j,
\]

where `s_j` is the positive half-width of the accepted v0 test range. In the
accepted nuisance order the frozen scales are:

```text
TORQUE_CALIBRATION             0.02 fraction
SOURCE_DENSITY_SCALE           0.01 fraction
DETECTOR_DENSITY_SCALE         0.01 fraction
DETECTOR_LEVER_OFFSET          1e-4 m
ATTRACTOR_LEVER_OFFSET         1e-4 m
GAP_OFFSET                     1e-5 m
ATTRACTOR_AXIS_X_OFFSET        1e-4 m
ATTRACTOR_AXIS_Y_OFFSET        1e-4 m
ANGULAR_ZERO_OFFSET            1e-3 rad
HARMONIC_LEAKAGE               0.002 fraction
BACKGROUND_2RE                 1e-17 N m
BACKGROUND_2IM                 1e-17 N m
BACKGROUND_4RE                 1e-17 N m
BACKGROUND_4IM                 1e-17 N m
BACKGROUND_6RE                 1e-17 N m
BACKGROUND_6IM                 1e-17 N m
```

The finite-difference columns are exactly `LOG_LAMBDA`, both lever offsets,
`GAP_OFFSET`, both attractor-axis offsets, and `ANGULAR_ZERO_OFFSET`. The ten
remaining nuisance columns use their exact accepted linear derivative maps.

For each finite-difference column, after accepted global output scaling, use

```text
h ladder in q:
[1e-2, 3e-3, 1e-3]

interior:
[f(q+h)-f(q-h)]/(2h)

lower boundary:
[-3f(q)+4f(q+h)-f(q+2h)]/(2h)

upper boundary:
[3f(q)-4f(q-h)+f(q-2h)]/(2h)
```

The one-sided rule is used only when the centered stencil is invalid and all
three one-sided points are valid. Otherwise the column fails closed. All
perturbed forward evaluations must return finite real-150 vectors with the
canonical ordering.

The two finest valid steps define the preregistered plateau:

```text
RMS(D_3e-3 - D_1e-3)
  <= 1e-10 + 5e-3 * RMS(D_1e-3)
```

There is no result-dependent adaptation, fallback step, extrapolation, or
rounding into acceptance. Any required evaluation failure or plateau failure
returns `BLOCKED_FINITE_DIFFERENCE_PLATEAU`.

## G20 — executable rank-deficient nuisance projector

Let `Y_*` be the unchanged v0 global output scale. Derivatives are taken in the
dimensionless coordinates above and divided by `Y_*`. A nuisance column is a
zero column when

\[
\|n_j\|_2\le\sqrt{150}\,10^{-12}.
\]

Zero columns are reported and excluded from normalization. Each remaining
nuisance column is normalized to unit Euclidean norm to form
`N_tilde`. The only permitted factorization is a thin SVD:

\[
\widetilde N=U\Sigma V^\mathsf{T}.
\]

At threshold `t`, retain exactly the indices satisfying

\[
\sigma_i/\sigma_1>t.
\]

The central threshold is `1e-10`; mandatory probes are `1e-9` and `1e-11`.
No normal-equation projector is permitted. The truncated pseudoinverse and
orthogonal projector are

\[
\widetilde N^+=V_r\,\mathrm{diag}(1/\sigma_i)\,U_r^\mathsf{T},
\qquad
P_\perp=I-U_rU_r^\mathsf{T}.
\]

The implementation must verify:

```text
||U_r^T U_r - I||_2 <= 1e-12

||N_tilde-U_r U_r^T N_tilde||_F
-------------------------------- <= 1e-9
       max(||N_tilde||_F, 1e-30)
```

The scalar response uses the same dimensionless/output scaling. If its norm
meets the zero-column floor, classification is unresolved. Otherwise

\[
\eta_\lambda=
\frac{\|P_\perp j_\lambda\|_2}{\|j_\lambda\|_2}.
\]

Exact duplicate columns reduce rank without error. Near-degeneracy is reported
when any pairwise absolute correlation is at least `0.999`, the retained
condition number is at least `1e8`, or the three threshold probes disagree on
rank. The accepted point bands remain:

```text
eta_lambda <= 1e-6: INDISTINGUISHABLE_AT_POINT
eta_lambda >= 1e-3: IDENTIFIABLE_AT_POINT
otherwise:          IDENTIFIABILITY_CLASSIFICATION_UNRESOLVED
```

## G21 — exact preregistered transition domain

The unchanged scalar grid is

\[
\lambda_i=10^{-5+i/6}\ {\rm m},\qquad i=0,\ldots,24.
\]

For `d_min=1e-4 m` and `d_max=1e-2 m`, the decision-bearing transition indices
are exactly

```text
i = 4, 5, ..., 20
```

which are precisely the grid points satisfying
`d_min/3 <= lambda_i <= 3*d_max`. Rank, spectrum, correlation, projector,
`eta_lambda`, degeneracy, and refinement metrics are required at all seventeen
points.

Five direct regime sentinels are also mandatory:

\[
\left\{
d_{\min}/3,
d_{\min},
\sqrt{d_{\min}d_{\max}},
d_{\max},
3d_{\max}
\right\}.
\]

The serialized grid, indices, sentinels, and SHA-256 registration are frozen in
the canonical JSON packet before execution. Sentinels diagnose regimes but do
not create contiguity. Post-result point selection or reordering returns
`BLOCKED_TRANSITION_DOMAIN_CONTRACT`.

After all numerical-stability rules pass:

```text
at least five contiguous transition points with eta_lambda >= 1e-3:
DETERMINISTIC_PARAMETER_IDENTIFIABLE

all seventeen transition points with eta_lambda <= 1e-6:
BLOCKED_PARAMETER_IDENTIFIABILITY

otherwise:
IDENTIFIABILITY_CLASSIFICATION_UNRESOLVED
```

## G22 — executable refinement stability

The final two synchronized accepted production refinements are:

```text
IDENT_R_MEDIUM:
angular samples = 256
density cubature order = 16
energy-derivative check step = 2.5e-4 rad

IDENT_R_FINE:
angular samples = 512
density cubature order = 24
energy-derivative check step = 1.25e-4 rad
```

The analytic production torque remains unchanged; the energy-derivative step
belongs only to its accepted independent cross-check.

At every decision-bearing point, medium versus fine must satisfy:

```text
retained rank:                                  identical
abs change in eta_lambda:                       <= 0.02
relative change in eta_lambda when max eta>1e-6 <= 5%
abs change in max scalar-nuisance correlation:  <= 0.02
largest nuisance-subspace principal angle:      <= 1 degree
abs change in decision-bearing log10 sigma_i:   <= 0.05 decades
exact/near-degeneracy labels:                    identical
point classification:                           identical
```

The principal angle is `acos(sigma_min(U_medium^T U_fine))` after equal-rank
verification. All three rank thresholds must agree on rank and classification;
their `eta_lambda` spread must be at most `0.02`. Any failure returns
`BLOCKED_NUISANCE_PROJECTOR_UNSTABLE` or
`BLOCKED_IDENTIFIABILITY_REFINEMENT_STABILITY` as applicable. Forward-vector
convergence cannot override either block.

## Ten production-path controls

Every control invokes the frozen production forward model and the actual v1
Jacobian builder, dimensionless scaler, thin-SVD projector, and refinement
adjudicator. Test doubles for those five components are forbidden; declared
mutations may act only on their inputs or returned arrays.

1. Replace the ladder by `[1.0, 0.6, 0.3]`; curvature must fail plateau
   adjudication at the frozen mid-domain fixture.
2. Replace it by `[1e-7, 3e-8, 1e-8]` and add the frozen sign-keyed
   `1e-11 Y_*` deterministic output mutation; noise domination must fail the
   plateau.
3. Replace one nuisance column by an exact duplicate after actual Jacobian
   construction; rank must decrease safely.
4. Replace it by a `1e-6` near-duplicate mixture; near-degeneracy must be reported.
5. Run `1e-9`, `1e-10`, and `1e-11`; a stable fixture must retain rank,
   classification, and `eta_lambda` within `0.02`.
6. Replace the actual scalar column by the actual calibration column;
   `eta_lambda` must be zero within `1e-12`.
7. Inject the lexicographically first normalized coordinate-basis residual
   orthogonal to the actual nuisance basis; `eta_lambda` must be one within
   `1e-12`.
8. Attempt to replace the registered transition indices after the production
   metrics exist; classification must fail closed.
9. Preserve converged forward vectors while rotating one fine-refinement
   nuisance column by `2 degrees`; Jacobian stability must block.
10. Verify recorded production component identities and hashes at every control
    boundary; any test substitute must fail provenance.

## Independent review contract

The independent reviewer must verify ten items:

1. Twenty frozen gates are byte-identical or semantically unchanged.
2. All four repairs are executable.
3. Thresholds predate scientific outputs.
4. Parameter units cannot control singular-value rankings.
5. Rank-deficient cases fail safely.
6. Near-threshold cases remain unresolved.
7. All ten controls traverse the production path.
8. Preparation calculated no forward vector, Jacobian, or result.
9. Success authorizes exactly one deterministic Stage A execution.
10. A new foundational block cannot create v2 automatically.

The only packet-review outcomes are:

```text
DETERMINISTIC_IDENTIFIABILITY_CONTRACT_READY
BLOCKED_FINITE_DIFFERENCE_PLATEAU
BLOCKED_NUISANCE_PROJECTOR_UNSTABLE
BLOCKED_TRANSITION_DOMAIN_CONTRACT
BLOCKED_IDENTIFIABILITY_REFINEMENT_STABILITY
```

Only `DETERMINISTIC_IDENTIFIABILITY_CONTRACT_READY` may rotate authority to one
deterministic execution. V1 is the last automatic Stage A repair.

## Scope firewall

```text
packet preparation:
PERFORMED

independent review:
NOT PERFORMED

deterministic execution:
NOT AUTHORIZED / NOT PERFORMED

forward vector:
NOT PRODUCED

Jacobian:
NOT COMPUTED

Stage B:
DEFERRED / NOT AUTHORIZED

noise / Monte Carlo / likelihood / forecast:
NONE

synthetic or empirical constraint:
NONE

alpha:
NOT SELECTED

scalar branch:
NOT ADOPTED

automatic v2:
NOT AUTHORIZED

next authority:
review_scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_packet_v1_result
```
