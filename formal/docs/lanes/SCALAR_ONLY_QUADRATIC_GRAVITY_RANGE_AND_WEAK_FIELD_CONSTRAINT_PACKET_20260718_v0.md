# Scalar-Only Quadratic-Gravity Range and Weak-Field Constraint Packet v0

Date: `2026-07-18`  
Target: `prepare_scalar_only_quadratic_gravity_range_and_weak_field_constraint_packet_v0`  
Verdict: `PREPARED_BLOCKED_PRIMARY_DATA_OR_COVARIANCE_INCOMPLETE_PENDING_INDEPENDENT_REVIEW`

## Boundary

This packet prepares one comparison-only weak-field constraint analysis for the
accepted supplied scalar branch. It does not run a likelihood, calculate a
range bound, select alpha, adopt the scalar branch, identify a native scalar,
or select a ToE gravitational action.

```text
comparison model:
SUPPLIED R + alpha R^2 BRANCH

fixed relative Yukawa amplitude:
A_Y = 1 / 3

primary observable class:
EOT-WASH 2020 SHORT-RANGE ISL TORSION BALANCE

real data analysis:
NOT EXECUTED

numerical lambda0 or alpha bound:
NONE

provisional execution readiness:
BLOCKED_PRIMARY_DATA_OR_COVARIANCE_INCOMPLETE
```

The block is an evidence-custody result, not a claim that the underlying
experimental files do not exist. The audited sources did not yield a frozen,
complete numerical vector, uncertainty/nuisance contract, and executable
extended-source torque model sufficient for an independent fixed-`1/3`
reanalysis.

## Frozen comparison model

The accepted stationary point-source response is retained as

\[
h_{00}(r)=-\frac{2GM}{c^2r}
\left(1+\frac13e^{-r/\lambda_0}\right).
\]

With `g_00 = 1 + 2 Phi / c^2`, the supplied comparison potential is

\[
\Phi(r)=-\frac{GM}{r}
\left(1+A_Y e^{-r/\lambda_0}\right),
\qquad A_Y=\frac13.
\]

The parameter maps are

\[
\lambda_0=\sqrt{-6\alpha_{\rm packet}},
\qquad
\alpha_{\rm packet}=-\frac{\lambda_0^2}{6}<0,
\]

\[
m_0=\lambda_0^{-1}\;[\mathrm{m}^{-1}],
\qquad
M_0=\frac{\hbar}{c\lambda_0}\;[\mathrm{kg}],
\qquad
M_0c^2=\frac{\hbar c}{\lambda_0}.
\]

`m_0` is an inverse-length pole parameter. `M_0` is the corresponding particle
mass. The packet forbids using the word "mass" without distinguishing them.

`beta = 0` remains a comparison restriction reached through a supplied
ghost-avoidance criterion. Neither `beta = 0` nor `alpha < 0` is adopted as a
native ToE law.

## Observable selection

Three candidate classes were audited.

| Candidate | Disposition | Reason |
| --- | --- | --- |
| Eot-Wash 2020 short-range torsion balance | Selected for the packet contract only | Direct extended-source Yukawa test over 52 micrometres to 3.0 millimetres with gravitational-strength sensitivity |
| 2024-2026 optically levitated vector-force sensor | Deferred | Its reported sensitivity is of order `A_Y ~ 10^6` or larger in the relevant range, far above the fixed `1/3` signal |
| Solar-system orbital class | Deferred | Requires a full observable/ephemeris likelihood and explicit `G`, `M`, or `GM` calibration; light propagation also needs more metric content than the accepted `h_00` input |

Only one observable class is selected. No cross-check dataset is selected in
v0.

## Selected primary experiment

The primary contract is based on J. G. Lee et al., *New Test of the
Gravitational 1/r^2 Law at Separations down to 52 micrometres*, Physical Review
Letters 124, 101101 (2020), DOI `10.1103/PhysRevLett.124.101101`,
[arXiv:2002.11761](https://arxiv.org/abs/2002.11761).

The paper describes:

- 95 detector-attractor displacement settings.
- Three fitted harmonic torques, `18 omega`, `54 omega`, and `120 omega`.
- 285 torque entries in the primary fit.
- A prediction depending on 17 experimental parameters.
- Five materially important profiled nuisance parameters: `x0`, `y0`, `s0`, a
  surface-roughness correction, and the autocollimator torque scale `gamma`.
- A Newtonian baseline of `chi_squared = 275.0` for `nu = 285`, with
  `P = 0.654`.

The published gravitational-strength range limit is an oracle for later
reproduction. It is not this packet's fixed-`A_Y=1/3` result.

## Exact theory-to-observable transport

For a point source, differentiation gives

\[
a_r(r)=-\frac{GM}{r^2}
\left[1+A_Y\left(1+\frac{r}{\lambda_0}\right)
e^{-r/\lambda_0}\right].
\]

The selected experiment cannot use this point-source expression directly. The
Yukawa interaction between detector and attractor density distributions must be
computed as

\[
U_Y(\phi)=-G A_Y
\int d^3x\,d^3x'\,
\rho_D(\mathbf x)\rho_A(\mathbf x')
\frac{e^{-|\mathbf x-\mathbf x'|/\lambda_0}}
{|\mathbf x-\mathbf x'|},
\]

followed by

\[
N_Y(\phi)=-\frac{\partial U_Y}{\partial\phi}
\]

and the same harmonic extraction used for `N_18omega`, `N_54omega`, and
`N_120omega`.

One verified Fourier-Bessel or direct density-integration implementation must
generate both the Newtonian baseline and the fixed-amplitude Yukawa response.
Separate imported formulas are prohibited.

## Extended-source contract

Execution requires the following frozen numerical inputs:

1. Detector and attractor density masks.
2. Material densities and removed masses.
3. Detector and attractor thicknesses.
4. Hole-filling glue density and geometry.
5. Isolation foil and face-layer thicknesses.
6. The complete `x`, `y`, and `s` displacement record.
7. Attractor runout and tilt.
8. Surface-roughness model.
9. Rotation phase convention.
10. Torque calibration and transfer function.

A point-source approximation is forbidden unless a quantified form-factor error
is below a preregistered numerical tolerance over the complete scanned
`lambda0` domain.

## Primary data sufficiency audit

| Required item | Audit status | Consequence |
| --- | --- | --- |
| Paper and accepted manuscript | Available and inspected | Defines the scientific observable and likelihood structure, but is not executable by itself |
| Complete 95-by-3 numerical torque vector | Not obtained and frozen | Blocks the fit |
| Publisher Supplemental Material | Identified but not ingested | The paper says it contains numerical torques and analysis details; its bytes and content remain outside packet custody |
| Numerical uncertainty/covariance model | Structure described; complete numerical custody absent | Blocks reproducible weighting and coverage |
| Extended-source geometry and torque model | Described; not executable in packet custody | Blocks fixed-`1/3` templates |
| University of Washington methods dissertation | Available | Supports method reconstruction; does not substitute for the data vector and likelihood inputs |
| Published generic Yukawa limit | Available as oracle only | Cannot be read off or rescaled into the packet result |

The supporting methods record is J. G. Lee, *A Fourier-Bessel Test of the
Gravitational Inverse-Square Law*, University of Washington (2020),
[repository record](https://digital.lib.washington.edu/researchworks/items/971237d1-100a-41ae-9027-d1bbce8cf315/full).

The audit therefore issues the provisional preparation finding:

```text
BLOCKED_PRIMARY_DATA_OR_COVARIANCE_INCOMPLETE
```

This finding must be independently reviewed. A reviewer may upgrade the packet
to ready only after every unblock requirement below is satisfied.

## Calibration and degeneracy contract

The short-range harmonic geometry mitigates the simple long-range `GM`
degeneracy, but it does not eliminate calibration and source-model nuisance
parameters. A later execution must:

- Profile `gamma` with its primary Gaussian prior.
- Profile `x0`, `y0`, and `s0` with their primary priors.
- Profile the surface-roughness correction.
- Freeze the remaining 12 experimental parameters only after reproducing the
  primary conclusion that their propagated effect is negligible.

The long-range orbital class remains deferred. When `lambda0` is much greater
than the source-test separation, the response tends toward a `4/3` rescaling
that may be absorbed into fitted `G`, `M`, or `GM`. No orbital limit is valid
without an independent calibration and ephemeris covariance model.

## Frozen statistical rule

If and only if the data block is cleared, one execution must use:

- The primary penalized Gaussian chi-square structure, including torque errors,
  propagated separation uncertainty, and five Gaussian nuisance priors.
- One physical parameter, `lambda0 > 0`, with fixed `A_Y = 1/3`.
- Nuisance profiling at every `lambda0`.
- A log-spaced range scan limited to the validated data/geometry domain, with
  adaptive refinement only near likelihood transitions.
- No dataset combination in v0.

The Einstein null is the boundary limit `lambda0 -> 0`. `A_Y -> 0` is retained
only as a software null control. Because the null is on a parameter boundary and
the analysis scans a range, a textbook `Delta chi_squared` threshold is not
preauthorized. Coverage and scan effects must be calibrated by a parametric
bootstrap or an equivalent validated Neyman construction.

The future result must report the full connected or disconnected 95-percent
allowed set. It may report a single `lambda_max` only after demonstrating the
required topology and monotonicity.

## Future shared-path controls

No control has run. A later authorized execution must pass all nine:

1. `lambda0 -> 0` Einstein/infinite-mass limit.
2. `A_Y -> 0` software null.
3. Published Newtonian baseline reproduction.
4. Synthetic fixed-amplitude signal recovery.
5. Synthetic null coverage.
6. Extended-geometry integration convergence.
7. Point-source-shortcut rejection.
8. Nuisance-prior and profile recovery.
9. SI round trip among `lambda0`, `m0`, `M0`, and `alpha_packet`.

## Unblock requirements

All five are mandatory:

1. Freeze the complete 95-by-3 torque vector and displacement metadata.
2. Freeze the complete numerical uncertainty model and five nuisance priors.
3. Freeze or independently reproduce a verified extended-source torque model.
4. Reproduce the published Newtonian baseline before exposing `A_Y = 1/3`.
5. Pass null and signal-injection coverage controls under the frozen scan rule.

## Interpretation firewall

If later data support `0 < lambda0 < lambda_max`, the packet convention maps
that interval to

\[
-\frac{\lambda_{\max}^2}{6}<\alpha_{\rm packet}<0.
\]

Finite data cannot prove `lambda0 = 0` or `alpha = 0`. A finite-range anomaly
would not uniquely identify `R^2` gravity, and a null result would not establish
the ToE's native gravitational action.

## Preparation controls

All 20 preparation controls pass. They check authority custody, comparison-only
provenance, the fixed amplitude, the single observable class, extended-source
transport, data sufficiency gates, nuisance and boundary handling, SI maps,
future controls, the fail-closed result, and the prohibition on theory adoption.

## Current posture

```text
scalar-only comparison:
COMPLETED AND ACCEPTED

native relevance:
UNESTABLISHED

weak-field packet:
PREPARED WITH PROVISIONAL EXECUTION BLOCK

primary observable class:
EOT-WASH 2020 SHORT-RANGE ISL TORSION BALANCE

cross-check:
DEFERRED

real data likelihood:
NOT EVALUATED

numerical lambda0 or alpha bound:
NONE

alpha:
NOT SELECTED

scalar branch:
NOT ADOPTED

native gravitational principle:
NOT IDENTIFIED

gravitational action:
NOT SELECTED

next authority:
review_scalar_only_quadratic_gravity_range_and_weak_field_constraint_packet_v0_result
```

The independent review must decide whether the public-source custody really is
insufficient and whether any newly supplied supplemental material closes every
data, covariance, geometry, nuisance, and coverage obligation. It must not run
the fit during packet review.
