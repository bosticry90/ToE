# Scalar-only quadratic-gravity range and weak-field constraint packet review v0

## Verdict

```text
packet review:
COMPLETE

principal verdict:
BLOCKED_PRIMARY_DATA_OR_COVARIANCE_INCOMPLETE

experiment scientifically suitable:
YES

independent project fit executable:
NO

likelihood:
NOT EXECUTED

scalar-range or alpha bound:
NONE
```

The review confirms the packet's fail-closed preparation result. The 2020
Eot-Wash torsion-balance experiment is scientifically well matched to the
fixed-amplitude scalar comparison, but the project does not possess the
decision-bearing numerical evidence and executable transport needed for an
independent likelihood.

This is a data-contract block. It is not a rejection of the experiment, the
published result, or the scalar comparison branch.

## Frozen comparison boundary

The reviewed signal remains

\[
\Phi(r)=-\frac{GM}{r}
\left[1+\frac13 e^{-r/\lambda_0}\right],
\qquad
\lambda_0=\sqrt{-6\alpha_{\rm packet}}.
\]

```text
status:
SUPPLIED SCALAR-ONLY QUADRATIC-GRAVITY COMPARISON

fixed Yukawa amplitude:
A_Y = 1/3

beta = 0:
COMPARISON RESTRICTION ONLY

alpha:
NOT SELECTED

scalar branch:
NOT ADOPTED
```

No result in this review identifies the scalar with a ToE field or promotes
the comparison action into project dynamics.

## Independent source reproduction

The primary paper was independently checked. It reports:

- detector-attractor separations from 52 micrometres to 3.0 millimetres;
- 95 displacement settings;
- three measured torque harmonics, `18 omega`, `54 omega`, and `120 omega`;
- 285 torque measurements in total;
- 17 experimental parameters;
- five profiled nuisance parameters: `x0`, `y0`, `s0`, surface roughness, and
  the autocollimator scale `gamma`;
- a penalized chi-square including torque errors, transported separation
  error, and five Gaussian nuisance penalties; and
- a Newtonian baseline of `chi_squared=275.0` for `nu=285`, with `P=0.654`.

The paper also assigns numerical gravitational torques and analysis details to
Supplemental Material. That statement proves that a supplement was intended;
it does not put the supplement's numerical bytes into verified project
custody.

The published gravitational-strength range limit remains a scientific oracle.
It is not the output of this project and has not been independently reproduced
for the fixed `A_Y=1/3` comparison.

## Why the experiment is suitable

The patterned attractor and detector directly probe finite-range departures
from the inverse-square law over the micrometre-to-millimetre region. The
required observable chain is structurally correct:

\[
\Phi_Y
\longrightarrow
U_Y[\rho_D,\rho_A]
\longrightarrow
N_Y(\phi)=-\partial_\phi U_Y
\longrightarrow
\{N_{18\omega},N_{54\omega},N_{120\omega}\}.
\]

Thus the experiment is suitable for asking whether the fixed-strength scalar
signal is allowed. Suitability does not make the project likelihood
executable.

## Decision-bearing missing inputs

| Missing item | Required likelihood operation | Why guessing fails |
| --- | --- | --- |
| Complete `95 x 3` torque vector and displacement metadata | Construct the 285-component residual vector at every `lambda0` | The fitted observations and geometry row mapping would be invented |
| Numerical uncertainty and correlation model | Weight residuals and determine effective information | A diagonal guess can overstate exclusion power |
| Five numerical nuisance priors | Profile calibration, centering, separation, and roughness | Analyst-selected priors can hide or expose the Yukawa template |
| Verified extended-source torque implementation | Convert `A_Y=1/3` into the three measured harmonics | Point-source or approximate geometry is not this experiment |
| Boundary-aware coverage calibration | Issue a valid 95 percent exclusion with `lambda0=0` at the null boundary | An uncalibrated textbook threshold can have wrong coverage |

These omissions are scientific inputs to the result. They are not optional
documentation.

## Principal and subordinate diagnostics

The principal outcome is:

```text
BLOCKED_PRIMARY_DATA_OR_COVARIANCE_INCOMPLETE
```

The independent review also records:

```text
OBSERVATION_VECTOR_CUSTODY_INCOMPLETE
UNCERTAINTY_OR_COVARIANCE_CONTRACT_INCOMPLETE
NUISANCE_PRIOR_CONTRACT_INCOMPLETE
EXTENDED_SOURCE_FORWARD_MODEL_ABSENT
BOUNDARY_COVERAGE_PROCEDURE_UNCALIBRATED
```

The primary-data/covariance block has precedence because the residual vector
and its numerical weight cannot be constructed at all. The forward-model and
coverage defects remain binding even after data custody is repaired.

## No-bypass probes

Eight adversarial substitutions were rejected:

1. Treating a supplement citation as numerical custody.
2. Digitizing plotted points as the complete primary observation vector.
3. Reading or rescaling the published generic exclusion curve at `A_Y=1/3`.
4. Substituting the UW dissertation for the calibrated data and likelihood
   inputs.
5. Assuming independent diagonal errors from visible error bars.
6. Inventing “reasonable” priors for the five nuisance parameters.
7. Replacing the patterned extended-source model with a point-source formula.
8. Applying an uncalibrated asymptotic threshold at the null boundary.

The UW dissertation remains a valuable primary methods source. It is not a
substitute for the missing numerical vector, priors, covariance justification,
or executable geometry model.

## Review gates

| Gate | Result | Finding |
| --- | --- | --- |
| `G1_EXACT_PACKET_AUTHORITY_AND_CUSTODY` | PASS | Five packet artifacts match frozen custody. |
| `G2_COMPARISON_ONLY_PROVENANCE_RETAINED` | PASS | The signal and branch remain supplied and unadopted. |
| `G3_SELECTED_EXPERIMENT_SUITABLE_FOR_FIXED_ONE_THIRD_SIGNAL` | PASS | The experiment probes the relevant range and strength. |
| `G4_PRIMARY_PAPER_DIMENSIONS_AND_FIT_STRUCTURE_REPRODUCED` | PASS | The `95 x 3`, 17-parameter, five-nuisance structure is independently reproduced. |
| `G5_OBSERVATION_VECTOR_CUSTODY_IS_DECISION_BEARING` | PASS | The residual vector cannot be constructed without the complete data. |
| `G6_UNCERTAINTY_AND_CORRELATION_CONTRACT_INCOMPLETE` | PASS | Error bars are not a covariance contract. |
| `G7_FIVE_NUISANCE_PRIORS_CANNOT_BE_GUESSED` | PASS | The priors directly affect signal absorption. |
| `G8_EXTENDED_SOURCE_FORWARD_MODEL_NOT_EXECUTABLE` | PASS | No verified numerical torque implementation is frozen. |
| `G9_POINT_SOURCE_APPROXIMATION_REMAINS_FORBIDDEN` | PASS | Patterned sources require the full geometry transport. |
| `G10_DISSERTATION_REMAINS_SUPPORTING_METHODS_ONLY` | PASS | Methods evidence cannot replace calibrated numerical evidence. |
| `G11_PLOTS_SECONDARY_SUMMARIES_AND_APPROXIMATE_GEOMETRY_CANNOT_BYPASS` | PASS | Approximate reconstruction is rejected. |
| `G12_PUBLISHED_GENERIC_LIMIT_IS_ORACLE_NOT_PACKET_RESULT` | PASS | No published curve is imported as this project's result. |
| `G13_BOUNDARY_COVERAGE_REMAINS_UNCALIBRATED` | PASS | No numerical threshold is selected. |
| `G14_BASELINE_AND_INJECTION_CONTROLS_REMAIN_UNEXECUTED` | PASS | Baseline reproduction and injection controls remain at zero. |
| `G15_SCIENTIFIC_SUITABILITY_AND_PROJECT_EXECUTABILITY_SEPARATED` | PASS | Suitable experiment, non-executable project fit. |
| `G16_PRINCIPAL_BLOCK_AND_SUBORDINATE_DIAGNOSTICS_EXCLUSIVE` | PASS | One principal verdict and five diagnostics are preserved. |
| `G17_NO_LIKELIHOOD_BOUND_OR_THEORY_ADOPTION` | PASS | No fit, bound, principle, branch, or action is issued. |
| `G18_ROTATION_ONLY_TO_SCIENTIFIC_RESPONSE_SELECTION` | PASS | Only a future response-selection step is authorized. |

## Binding unblock requirements

No unblock requirement is currently satisfied. A future executable packet
would have to:

1. freeze the complete `95 x 3` numerical torque vector and displacement
   metadata;
2. freeze the complete numerical uncertainty model and five nuisance priors;
3. freeze or independently reproduce a verified extended-source torque model;
4. reproduce the published Newtonian baseline before exposing `A_Y=1/3`; and
5. pass null and signal-injection coverage controls under a frozen scan rule.

Meeting those requirements is not authorized by this review. It would require
a separately selected response.

## Next authority

The review rotates only to:

```text
select_post_scalar_only_quadratic_gravity_range_and_weak_field_constraint_packet_review_scientific_response_v0
```

That response selection may compare, without automatically activating:

- bounded acquisition and custody of the exact supplement;
- a legitimate request for primary numerical inputs;
- another experiment with complete data, covariance, and geometry; or
- a publication-level supplied-constraint reinterpretation that does not claim
  an independent fit.

## Current posture

```text
scalar-only comparison:
BOUNDEDLY VIABLE, NATIVE RELEVANCE UNESTABLISHED

weak-field packet review:
BLOCKED_PRIMARY_DATA_OR_COVARIANCE_INCOMPLETE

selected experiment:
2020 EOT-WASH TORSION BALANCE

primary-data custody:
INCOMPLETE

covariance and nuisance contract:
INCOMPLETE

extended-source torque model:
NOT EXECUTABLE

coverage calibration:
NOT AVAILABLE

likelihood:
NOT EXECUTED

scalar-range bound:
NONE

alpha:
NOT SELECTED

scalar branch:
NOT ADOPTED

native gravitational principle:
NOT IDENTIFIED

gravitational action:
NOT SELECTED
```

The packet has reached a confirmed data-contract block, not a scientific
conclusion about the scalar branch.
