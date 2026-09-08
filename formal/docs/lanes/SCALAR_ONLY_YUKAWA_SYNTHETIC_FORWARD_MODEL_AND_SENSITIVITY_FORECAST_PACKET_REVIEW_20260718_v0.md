# Scalar-only Yukawa synthetic forward-model and sensitivity-forecast packet review v0

Date: `2026-07-18`  
Target: `review_scalar_only_yukawa_synthetic_forward_model_and_sensitivity_forecast_packet_v0_result`  
Verdict: `BLOCKED_SYNTHETIC_NOISE_OR_NUISANCE_CONTRACT`

## Principal result

```text
packet review:
COMPLETED

synthetic execution:
NOT AUTHORIZED

principal outcome:
BLOCKED_SYNTHETIC_NOISE_OR_NUISANCE_CONTRACT
```

The packet defines a scientifically useful internal experiment, and its basic
geometry, range coverage, covariance construction, trial resolution, and claim
firewalls survive review. It is not yet sufficiently complete for a 27,026-trial
synthetic execution. Seven decision-bearing interfaces remain underdefined.

No forecast, synthetic dataset, Eöt-Wash reproduction, empirical constraint, or
numerical `lambda0`/`alpha` result was produced during review.

## Findings that independently reproduce

### The frozen geometry does not cancel the intended even harmonics

For detector and attractor arm radii `L` and center-plane separation `z`, the
four sphere-pair distances reduce to two repeated distances:

\[
r_-^2=z^2+2L^2(1-\cos\theta),
\qquad
r_+^2=z^2+2L^2(1+\cos\theta).
\]

For either the Newtonian or the radial Yukawa pair kernel,

\[
U(\theta)=2\,[u(r_-)+u(r_+)].
\]

Therefore

\[
U(\theta+\pi)=U(\theta),
\qquad
U(-\theta)=U(\theta),
\]

and `tau = -dU/dtheta` is pi-periodic and odd. Only sine-phase even harmonics
occur in the nominal aligned geometry. A representative dimensionless
Newtonian check at `L=0.03 m`, `z=0.011 m` produced nonzero `n=2,4,6`
coefficients and odd harmonics at numerical zero. Thus the declared even
harmonics are not accidentally cancelled.

This also exposes an important convention obligation: the nominal cosine
quadratures are structural zeros, while an angular offset rotates power into
them. The exact complex-Fourier sign and normalization must be frozen before
execution.

### The observation vector is 150 real values

The packet's intended representation is:

```text
25 gaps
x 3 harmonics
x 2 real quadratures
= 150 real components
```

It is not 150 complex observations and not a 300-component vector. The future
repair must state the exact coefficient definition and preserve a real
`150 x 150` covariance.

### The mathematical covariance is positive definite

The unambiguous reading of the packet is

\[
C=R_d\otimes\operatorname{diag}(\sigma_{2I}^2,\ldots,\sigma_{6Q}^2),
\]

with

\[
(R_d)_{jk}=\exp[-|\ln(d_j/d_k)|/0.55].
\]

For the 25 distinct frozen log-spaced gaps, the review reproduced:

```text
minimum eigenvalue of R_d:
0.1733442158

condition number of R_d:
30.7757013

condition number of full C:
69.2453279

maximum symmetry residual:
2.6e-49 in SI-scaled entries
```

The covariance is therefore mathematically symmetric positive definite and not
near singular. The packet still lacks a frozen Cholesky/factorization method,
failure behavior, and explicit prohibition or specification of jitter,
eigenvalue clipping, or covariance repair.

### The range grid and Monte Carlo resolution are bounded correctly

The 25 positive log-spaced ranges from `1e-5 m` to `1e-1 m` cover all three
required gap regimes. The exact maps to `m0` and `alpha_packet` are frozen.

The declared trials imply:

```text
null trials:
2000

positive-range injection trials:
25 x 1000 = 25000

zero-noise trials:
26

total synthetic datasets if later authorized:
27026
```

At 1,000 injections, the maximum binomial standard error is about `1.6%`. The
smallest directly resolved null-tail probability is about `1/2001`. This is
adequate for an ordinary bounded 95-percent forecast, not a five-sigma claim.
The packet already requires Monte Carlo uncertainty and makes no stronger claim.

## Decision-bearing blocks

### 1. Harmonic coefficient definition is incomplete

The packet freezes angle samples and named quadratures but not the exact DFT or
integral convention, normalization, exponent sign, torque phase origin, or
alias handling. These choices control the sign and phase-reversal tests.

### 2. Production-kernel benchmark routing is incomplete

The packet requires analytic and direct-density agreement but does not freeze
the production pair-energy expression, the torque differentiation method, the
direct cubature rule/refinement sequence, or mutation tests demonstrating that
a sign or normalization defect fails the benchmark gates.

### 3. Covariance numerical behavior is incomplete

Positive definiteness is established, but the factorization, conditioning
threshold, failure status, and any regularization policy are absent. Numerical
repair may not be chosen after a failure.

### 4. Nuisance truth values, bounds, and effects are incomplete

The eleven priors have widths, but the packet does not freeze all injected truth
values, optimizer bounds, exact background/leakage maps, or invalid-domain
handling. In particular, the gap offset must not permit nonpositive physical
gaps and multiplicative scales must have a frozen valid domain.

### 5. Two multiplicative nuisances are exactly data-degenerate

At the nominal point, global torque calibration and combined density/mass scale
both multiply the entire torque prediction. Their data-Jacobian columns are
identical. Independent Gaussian priors make a penalized optimizer finite, but
they do not make the two quantities separately identifiable from the synthetic
observations.

The repair must either combine them into one amplitude nuisance or define a
genuinely distinct forward-model effect and require rank/conditioning checks.
The current description incorrectly calls this merely a near degeneracy.

### 6. The computational execution plan is absent

The run may require at least `27000 x 25 = 675000` outer range-profile fits,
before optimizer iterations and convergence variants. The packet does not
freeze optimizer, derivatives, initial points, warm starts, iteration and
evaluation limits, fit-convergence tolerances, retry policy, parallelization,
failed-fit classification, wall-time cap, memory cap, or checkpoint policy.

A failed fit may not silently count as nondetection.

### 7. Required adversarial controls are missing

The eleven controls do not explicitly include:

- phase/sign reversal under source rotation;
- deliberately mutated force sign or normalization;
- nuisance-fixed sensitivity no worse than profiled sensitivity; or
- profile-Jacobian/Hessian rank checks at null and injected points.

These are required before the headline forecast can be trusted.

## Gate result

The review evaluated 22 gates:

```text
passed:
15

failed:
7
```

The failures are preparation defects, not scientific results about the scalar
model or torsion balances.

## Exact unblock requirements

1. Freeze a real-150 harmonic coefficient convention with normalization, phase,
   sign, and alias rules.
2. Freeze the production pair kernel, torque derivative, direct cubature, and
   mutation-gate route used by every benchmark and apparatus calculation.
3. Freeze covariance factorization, conditioning threshold, and fail-closed
   repair policy.
4. Freeze every nuisance truth, bound, exact forward effect, and invalid-domain
   behavior.
5. Remove or explicitly resolve the exact calibration/mass-scale Jacobian
   degeneracy and require representative rank diagnostics.
6. Freeze the optimizer, derivative, initialization, warm-start, iteration,
   retry, parallelization, resource, and failed-fit contracts.
7. Add phase/sign reversal, deliberate mutation, nuisance-removal monotonicity,
   and identifiability controls.

## Claim ceiling

This review establishes that the v0 packet is promising but not execution-ready.
It does not authorize packet repair, execute simulations, produce forecast
outputs, use measured evidence, reproduce Eöt-Wash, compute empirical or
synthetic exclusion bounds, select `alpha`, adopt the scalar branch, identify a
native scalar bridge, or select a gravitational action.

## Current exact posture

```text
packet review:
COMPLETED

principal outcome:
BLOCKED_SYNTHETIC_NOISE_OR_NUISANCE_CONTRACT

synthetic execution:
NOT AUTHORIZED

work packages:
0 / 8 EXECUTED

synthetic observations:
0 PRODUCED

null trials:
0 / 2000

injection trials:
0 / 25000

forecast outputs:
0 / 8

empirical constraint:
NONE

alpha:
NOT SELECTED

scalar branch:
NOT ADOPTED

current authority:
select_post_scalar_only_yukawa_synthetic_forward_model_and_sensitivity_forecast_packet_review_scientific_response_v0
```

