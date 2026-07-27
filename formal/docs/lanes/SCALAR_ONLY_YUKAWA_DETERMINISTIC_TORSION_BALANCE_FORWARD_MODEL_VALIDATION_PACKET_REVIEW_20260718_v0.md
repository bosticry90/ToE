# Scalar-only Yukawa deterministic torsion-balance forward-model validation packet review v0

Date: `2026-07-18`  
Target: `review_scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_packet_v0_result`  
Verdict: `BLOCKED_PARAMETER_IDENTIFIABILITY`

## Principal result

```text
independent packet review:
COMPLETED

deterministic execution:
NOT AUTHORIZED

principal outcome:
BLOCKED_PARAMETER_IDENTIFIABILITY
```

The deterministic physics contract is substantially complete. The review
independently reproduces the harmonic convention, real-150 ordering, shared
uniform-sphere kernel, energy-to-torque sign, symmetry structure, deterministic
perturbation maps, exact amplitude degeneracy, and Stage B firewall.

Execution remains blocked because the decision-bearing Jacobian calculation is
not numerically unique. The packet freezes a derivative method and thresholds,
but not the actual finite-difference base steps, the numerical construction of
the nuisance-space projector in the presence of exact rank deficiency, the
transition-domain indices, or quantitative refinement-stability tolerances.

This is a contract block. It is not a finding that the apparatus is physically
unidentifiable.

No kernel, benchmark, mutation, deterministic vector, or Jacobian was executed
or produced during review. No noise, covariance, Monte Carlo, likelihood, or
forecast was introduced.

## Findings independently reproduced

### Harmonic convention and real-150 ordering are exact

With

\[
c_n=\frac{1}{2\pi}\int_0^{2\pi}\tau(\theta)e^{-in\theta}\,d\theta,
\]

the packet consistently uses

\[
a_n=2\operatorname{Re}c_n,
\qquad
b_n=-2\operatorname{Im}c_n.
\]

The positive-angle, positive-torque, phase-origin, continuous-transform, and
discrete-transform conventions agree. For each of 25 gaps the retained order is

```text
Re(c2), Im(c2), Re(c4), Im(c4), Re(c6), Im(c6)
```

and therefore

\[
25\times3\times2=150
\]

real values in `N m`. The packet creates neither a 150-complex nor a 300-real
observation surface.

### Shared production kernel and torque sign are coherent

Both Newtonian and Yukawa terms use the same pair distance, sphere geometry,
density-derived masses, energy, torque, harmonic, and serialization path. For
the two repeated pair classes,

\[
r_q^2=L_D^2+L_A^2+z^2-2qL_DL_A\cos\theta,
\qquad q\in\{-1,+1\},
\]

and

\[
U(\theta,d)=2\sum_q u(r_q).
\]

Since

\[
\frac{\partial r_q}{\partial\theta}
=\frac{qL_DL_A\sin\theta}{r_q},
\]

the frozen production torque

\[
\tau_z=-\frac{\partial U}{\partial\theta}
=-2\sum_q u'(r_q)\frac{qL_DL_A\sin\theta}{r_q}
\]

has the correct sign under the packet convention. The direct force/lever route
and five-point energy derivative are genuinely distinct checks of that analytic
production expression.

The non-overlapping uniform-sphere form factor and its scaled `H(x)` expression
are algebraically consistent. The point, uniform-sphere, and apparatus
benchmarks all require the production side of the comparison to traverse the
same functions. The reference density cubature remains deliberately independent.

### Symmetry and phase behavior are determined

The equal two-pair geometry gives

\[
U(\theta+\pi)=U(\theta),
\qquad U(-\theta)=U(\theta),
\qquad \tau(-\theta)=-\tau(\theta).
\]

Thus nominal odd harmonics and even cosine quadratures vanish, while allowed
even sine quadratures may remain. Relabeling the equal attractor spheres or the
equal detector spheres leaves the summed energy invariant. A rigid coordinate
shift `delta` gives `c_n -> exp(-i*n*delta)c_n`, consistently with the frozen
Fourier sign. Near-zero channels use the absolute `1e-22 N m` floor.

### Deterministic perturbation maps are compositionally defined

All sixteen directions have units, nominal values, bounded test domains, and
exact maps. Their frozen order

```text
geometry/density -> energy -> torque -> harmonics
-> calibration -> leakage -> additive backgrounds
```

defines their interactions. At the nominal point, torque calibration, source
density scale, and detector density scale generate the same global amplitude
direction. The packet correctly records this exact degeneracy instead of
claiming three separately observable quantities.

Angular-zero offset rotates harmonic phase, leakage mixes adjacent retained
complex harmonics, additive backgrounds span their declared channel basis, and
lever, gap, and axis offsets produce geometry-dependent shape directions.

## Decision-bearing identifiability block

### 1. Finite-difference base steps are not frozen

The packet says:

```text
CENTERED_DIFFERENCE_WITH_HALF_STEP_CHECK_EXCEPT_EXACT_LINEAR_COLUMNS
```

but does not assign a numerical base step to `LOG_LAMBDA` or to each nonlinear
geometry direction. The perturbation test ranges do not state whether the
derivative uses the full half-range, a fraction of it, or another scale.
`FROZEN_TEST_SCALE` is a label, not an executable numerical table.

Consequently two conforming implementations can produce different Jacobians,
ranks, correlations, and scalar-shape residuals.

### 2. The rank-deficient nuisance projector is underdefined

The nuisance block intentionally contains three exactly collinear amplitude
columns. The orthogonal subspace is mathematically well defined, but its
numerical construction is not. The packet does not freeze:

- the SVD or QR implementation used to construct `P_N`;
- the exact cutoff used in that projector when nuisance singular values vanish;
- the zero-column and zero-leading-singular-value failure rules;
- whether reported condition numbers use the full or effective-rank matrix; or
- a reconstruction/idempotence tolerance for `P_N`.

The general rank threshold `s_k/s_1 >= 1e-10` does not by itself define all of
these operations.

### 3. The transition domain is not an exact set

Stage A requires five contiguous identifiable scalar-range points “in the
transition domain,” but no grid indices or mathematical range predicate define
that domain. The result can therefore depend on an after-the-fact choice of
which points count as transitional.

### 4. Identifiability refinement lacks quantitative acceptance tolerances

The packet requires classifications to “survive” angular and derivative
refinement but does not freeze numerical limits for changes in:

- singular values;
- numerical rank;
- pairwise correlations;
- `eta_lambda`;
- nuisance-space projection residuals; or
- the boundaries between identifiable, near-degenerate, and indistinguishable.

The forward-vector convergence tolerances do not automatically determine stable
Jacobian or SVD classifications.

## Gate result

The review evaluated 24 gates:

```text
passed:
20

failed:
4
```

All four failures concern the executable identifiability contract. No failure
was assigned to the harmonic, kernel, torque, benchmark, symmetry, perturbation,
serialization, or scope firewalls.

## Exact unblock requirements

1. Freeze a numeric base step and half-step for `LOG_LAMBDA` and every nonlinear
   perturbation, with invalid-domain and boundary behavior.
2. Freeze a numerical parameter-standardization table and a rank-deficient
   nuisance-projector algorithm, cutoff, reconstruction tolerance, and
   condition-number reporting rule.
3. Define the transition domain by exact scalar-grid indices or a mathematical
   predicate fixed before execution.
4. Freeze quantitative refinement tolerances for singular values, rank,
   correlations, `eta_lambda`, projector residuals, and classification changes.

## Claim ceiling

This review establishes that the deterministic physics surface is coherent but
the identifiability calculation is not yet uniquely executable. It does not
authorize packet repair, deterministic execution, Stage B preparation, noise,
simulation, forecasting, empirical inference, a numerical `lambda0` or `alpha`
result, scalar-branch adoption, a native scalar bridge, or a gravitational
action.

## Current exact posture

```text
Stage A packet review:
COMPLETED

principal outcome:
BLOCKED_PARAMETER_IDENTIFIABILITY

review gates:
20 / 24 PASSED

deterministic execution:
NOT AUTHORIZED

work packages:
0 / 10 EXECUTED

deterministic vectors:
0 PRODUCED

Jacobian:
NOT COMPUTED

Stage B:
DEFERRED / NOT AUTHORIZED

empirical constraint:
NONE

alpha:
NOT SELECTED

scalar branch:
NOT ADOPTED

current authority:
select_post_scalar_only_yukawa_deterministic_forward_model_packet_review_scientific_response_v0
```

