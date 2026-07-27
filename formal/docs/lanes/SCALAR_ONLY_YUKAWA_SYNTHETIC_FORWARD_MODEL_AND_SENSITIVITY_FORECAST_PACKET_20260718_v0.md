# Scalar-only Yukawa synthetic forward-model and sensitivity-forecast packet v0

Date: `2026-07-18`  
Target: `prepare_scalar_only_yukawa_synthetic_forward_model_and_sensitivity_forecast_packet_v0`  
Verdict: `PREPARED_SYNTHETIC_FORECAST_CONTRACT_READY_PENDING_INDEPENDENT_REVIEW`

## Status and claim firewall

```text
result type:
SYNTHETIC COMPUTATIONAL FORECAST

measured evidence:
NONE

Eöt-Wash reproduction:
NO

empirical constraint:
NO

scalar branch adoption:
NO

simulation execution:
NOT AUTHORIZED
```

This packet prepares one transparent, internal synthetic experiment. It does
not reconstruct the 2020 Eöt-Wash apparatus or data. Public torsion-balance
methods may motivate generic design choices, but all geometry, noise, nuisance,
and trial settings below are project-chosen simulation assumptions.

The standing prohibition on outbound research contact, private-data dependence,
and waiting on third-party cooperation remains binding.

## Frozen comparison model

The supplied comparison potential is

\[
V(r)=-\frac{GMm}{r}\left(1+A_Ye^{-r/\lambda_0}\right),
\qquad A_Y=\frac13.
\]

The exact parameter maps are

\[
m_0=\lambda_0^{-1}\;[\mathrm{m}^{-1}],
\qquad
\alpha_{\rm packet}=-\frac{\lambda_0^2}{6}\;[\mathrm{m}^2].
\]

`m_0` is an inverse-length parameter, not a particle mass. No value or interval
of `lambda0` or `alpha_packet` is selected by packet preparation.

## Work packages

The future bounded execution contains exactly eight shared-path work packages:

1. Derive and test analytic Yukawa benchmarks.
2. Implement the frozen idealized extended-source apparatus.
3. Extract complex torque harmonics through one angular path.
4. Generate synthetic observations under the frozen covariance and nuisance model.
5. Execute null and fixed-strength injection/recovery trials.
6. Calibrate boundary-aware detection and confidence procedures by simulation.
7. Quantify nuisance degeneracy and numerical convergence.
8. Produce forecast-only outputs and stop for independent review.

All are currently `NOT_EXECUTED`.

## Analytic benchmark level

The forward model must first pass four independently derived benchmarks:

1. Point-mass Newtonian and Yukawa force, including the factor
   `(1 + r/lambda0) exp(-r/lambda0)` in the force.
2. Exterior Yukawa field of one uniform sphere.
3. Non-overlapping uniform-sphere pair interaction.
4. Infinite parallel-slab force per area, used only as a kernel/integration check.

For a uniform sphere of radius `a`, the expected exterior form-factor oracle is

\[
F(a/\lambda_0)=
\frac{3\left[(a/\lambda_0)\cosh(a/\lambda_0)
-\sinh(a/\lambda_0)\right]}{(a/\lambda_0)^3}.
\]

The future calculation must derive or independently verify this oracle and use
a scaled/log-domain implementation when direct hyperbolic evaluation would
overflow. Direct density integration at representative small, comparable, and
large ranges must agree with the analytic non-overlapping-sphere result within
the frozen numerical tolerances.

## Idealized torsion-balance geometry

The apparatus is an internal symmetric sphere-pair torsion balance—not an
Eöt-Wash reconstruction.

```text
detector bodies:
2 uniform tungsten spheres

attractor bodies:
2 uniform tungsten spheres

density of every sphere:
19250 kg m^-3

detector sphere radius a_D:
5.0e-3 m

attractor sphere radius a_A:
5.0e-3 m

detector arm radius L_D:
3.0e-2 m

attractor orbit radius L_A:
3.0e-2 m

surface gap d:
25 logarithmically spaced values from 1.0e-4 m to 1.0e-2 m

vertical center separation:
z(d) = a_D + a_A + d

attractor angle:
theta in [0, 2*pi)
```

Detector centers are `(±L_D, 0, 0)`. Attractor centers are
`±(L_A cos(theta), L_A sin(theta), -z(d))`. The support beam is massless and
only the gravitational interaction of the four spheres is modeled.

For each detector-attractor pair, one shared kernel computes

\[
U_N=-G\int d^3x\,d^3x'\frac{\rho_D\rho_A}{s},
\qquad
U_Y=-GA_Y\int d^3x\,d^3x'\rho_D\rho_A
\frac{e^{-s/\lambda_0}}{s}.
\]

The torque is

\[
\tau_z(\theta,d)=-\frac{\partial}{\partial\theta}(U_N+U_Y).
\]

Production evaluation may use the verified non-overlapping sphere form factor.
The same pair geometry, differentiation rule, and harmonic extraction must be
used for Newtonian, null, and Yukawa paths.

## Harmonic extraction

The future calculation samples 256 equally spaced angles and extracts complex
Fourier coefficients at `n = 2, 4, 6`. It retains both in-phase and quadrature
components. Refinement to 512 angular samples is mandatory.

The synthetic observation vector is gap-major:

```text
[Re tau_2, Im tau_2, Re tau_4, Im tau_4, Re tau_6, Im tau_6]
```

at each of 25 gaps, for 150 values per synthetic trial.

## Frozen range grid

The injection and recovery grid contains exactly 25 logarithmically spaced
positive values from

```text
lambda0_min = 1.0e-5 m
lambda0_max = 1.0e-1 m
```

plus one exact software null sentinel. It covers `lambda0 << d_min`,
`lambda0 ~ d`, and `lambda0 >> d_max`. Every positive grid value must be
round-tripped through `m0 = 1/lambda0` and
`alpha_packet = -lambda0^2/6` in SI.

## Synthetic observation model

For each trial,

\[
\mathbf y=
\mathbf y_N+
\mathbf y_Y(\lambda_0,A_Y=1/3)+
\mathbf y_{\rm nuisance}+\boldsymbol\epsilon.
\]

The noise is zero-mean multivariate Gaussian. Channels are independent, while
the 25 gaps within each channel have correlation

\[
R_{jk}=\exp\left(-\frac{|\ln(d_j/d_k)|}{0.55}\right).
\]

The channel standard deviations are, in `(2I,2Q,4I,4Q,6I,6Q)` order,

```text
[2.0e-17, 2.0e-17, 2.5e-17, 2.5e-17, 3.0e-17, 3.0e-17] N m.
```

The resulting 150-by-150 covariance is frozen before any trial.

## Nuisance model

Exactly eleven Gaussian-constrained nuisances are profiled:

1. Global torque calibration: fractional width `0.01`.
2. Combined density/mass scale: fractional width `0.005`.
3. Surface-gap offset: width `2.0e-6 m`.
4. Angular zero offset: width `2.0e-4 rad`.
5. Nearest-neighbor harmonic leakage coefficient: width `1.0e-3`.
6–11. One additive background for each retained harmonic quadrature, with
   width equal to that channel's white-noise standard deviation.

The angular offset acts as `z_n -> exp(i n delta_theta) z_n`. Harmonic leakage
uses one frozen tridiagonal complex-harmonic mixing matrix. The global
calibration and mass scale are intentionally both retained so their near
degeneracy is measured rather than hidden.

## Randomness and trial counts

The base seed is `2026071801`. A deterministic counter-based or `SeedSequence`
policy must create disjoint streams for geometry checks, null trials, and each
injection range. No seed may be chosen after inspecting results.

The future execution uses:

```text
null trials:
2000

injection trials per positive lambda0 grid point:
1000

zero-noise trials:
1 null plus 1 per positive grid point
```

Monte Carlo binomial uncertainty must accompany reported false-positive,
coverage, and detection probabilities.

## Recovery and boundary-aware inference

The likelihood is the frozen Gaussian covariance likelihood plus all eleven
Gaussian nuisance penalties. `A_Y=1/3` is fixed in physical injections and
fits. `A_Y=0` is used only as a software null.

The detection statistic is the best fixed-strength grid improvement over the
Einstein/null fit. Its 95-percent critical value is the empirical 95th
percentile of the 2,000 null trials. Wilks or a textbook chi-square threshold
is not authorized.

Pointwise 95-percent confidence-set acceptance thresholds are calibrated from
the 1,000 trials at each injected positive grid point. Coverage is measured,
not assumed. A range is classified as `UNIDENTIFIABLE_UNDER_FROZEN_APPARATUS`
when its signal is numerically or statistically indistinguishable from the null;
the execution may not report a spurious recovered range there.

Required recovery metrics are:

- bias and median absolute error in `log10(lambda0)` for identifiable injections;
- 68-percent and 95-percent interval coverage;
- null false-positive rate;
- detection probability versus range;
- residual goodness of fit;
- nuisance pulls and correlations; and
- failure/identifiability classification.

## Degeneracy experiments

Using the same pipeline, the execution must compare the full fit with controlled
variants that freeze one class at a time:

- torque calibration;
- density/mass scale;
- gap offset;
- angular alignment;
- background harmonics;
- harmonic leakage; and
- correlated noise replaced by its diagonal.

These variants diagnose information loss. They are not alternative headline
forecasts and may not be used to cherry-pick the strongest sensitivity.

## Shared controls and convergence

All eleven controls are frozen and unexecuted:

1. `A_Y=0` software null.
2. `lambda0 -> 0`/underflow-safe Einstein limit.
3. Known fixed-strength injections.
4. Zero-noise recovery.
5. Two-times-noise degradation.
6. Analytic benchmark agreement.
7. Direct-density versus sphere-form-factor agreement at representative points.
8. 256-versus-512 angular-harmonic convergence.
9. Direct-density cubature/geometry refinement.
10. 25-versus-49 gap-design forecast robustness.
11. SI round trip among `lambda0`, `m0`, and `alpha_packet`.

Harmonic convergence must meet relative error `1.0e-8` or absolute error
`1.0e-22 N m`. Analytic/direct-transport checks must meet relative error
`1.0e-6` or a separately frozen absolute floor. The forecast must stop as
`BLOCKED_NUMERICAL_CONVERGENCE_CONTRACT` if these conditions are not met.

## Required forecast outputs

The later execution must produce exactly eight output classes:

1. Newtonian and Yukawa torque versus gap.
2. Complex harmonic amplitudes versus `lambda0`.
3. Expected signal-to-noise versus `lambda0`.
4. Injection-recovery bias and error.
5. Detection probability and null false-positive rate.
6. Calibrated confidence-set coverage.
7. Nuisance-degeneracy diagnostics.
8. Analytic and numerical-convergence diagnostics.

No output class has been produced by this packet.

## Packet review outcomes

The independent packet review must issue exactly one principal result:

```text
SYNTHETIC_FORECAST_CONTRACT_READY
BLOCKED_EXTENDED_SOURCE_FORWARD_MODEL_INCOMPLETE
BLOCKED_SYNTHETIC_NOISE_OR_NUISANCE_CONTRACT
BLOCKED_BOUNDARY_COVERAGE_CONTRACT
BLOCKED_NUMERICAL_CONVERGENCE_CONTRACT
BLOCKED_SCOPE_OR_PROVENANCE
```

Acceptance authorizes one bounded synthetic execution and nothing empirical.

## Preparation controls

All 24 preparation controls pass. They freeze authority, comparison-only
provenance, two model levels, extended-source transport, apparatus geometry,
range grid, covariance, nuisance priors, seeds, trial counts, boundary
calibration, degeneracy variants, shared controls, convergence, outputs, and
the no-contact/no-empirical/no-adoption firewalls.

## Current exact posture

```text
synthetic forecast packet:
PREPARED_PENDING_INDEPENDENT_REVIEW

preparation controls:
24 / 24 PASSED

work packages:
0 / 8 EXECUTED

forecast outputs:
0 / 8 PRODUCED

shared controls:
0 / 11 EXECUTED

measured evidence:
NONE

Eöt-Wash reproduction:
NO

simulation execution:
NOT AUTHORIZED

alpha:
NOT SELECTED

scalar branch:
NOT ADOPTED

current authority:
review_scalar_only_yukawa_synthetic_forward_model_and_sensitivity_forecast_packet_v0_result
```
