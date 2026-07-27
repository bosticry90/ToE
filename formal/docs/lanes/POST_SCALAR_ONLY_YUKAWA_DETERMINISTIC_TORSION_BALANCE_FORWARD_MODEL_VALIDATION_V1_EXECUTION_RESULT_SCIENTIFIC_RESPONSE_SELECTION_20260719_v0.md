# Post-Yukawa Stage A execution-result scientific-response selection 20260719 v0

Date: `2026-07-19`  
Target: `select_post_scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_v1_execution_result_scientific_response_v0`  
Verdict: `SELECTED_BOUNDED_PRODUCTION_KERNEL_DIAGNOSIS_AND_REFERENCE_ORACLE_PACKET_PREPARATION`

## Selected response

```text
route:
BOUNDED_PRODUCTION_KERNEL_DIAGNOSIS_AND_REFERENCE_ORACLE

selected candidate:
SPHERE_KERNEL_DIAGNOSIS_AND_INDEPENDENT_REFERENCE_ORACLE

next target:
prepare_scalar_only_yukawa_sphere_kernel_diagnosis_and_reference_oracle_packet_v0

authority:
PACKET PREPARATION ONLY
```

The accepted Stage A result remains `BLOCKED_PRODUCTION_KERNEL_VALIDATION`.
The deterministic apparatus model is not validated, but physical
unidentifiability was not tested or established. This selection authorizes one
small diagnostic packet so the project can determine whether the failure is an
implementation defect, numerical-method inadequacy, or reference-oracle
inadequacy before choosing a repair.

It does not prepare the diagnosis packet, execute a diagnostic calculation,
change the integration method, rerun Stage A, or authorize Stage B.

## Compared responses

| Response | Weighted score | Disposition |
| --- | ---: | --- |
| Bounded sphere-kernel diagnosis and independent oracle | 172 | Selected for packet preparation |
| Direct integration-method replacement | 116 | Deferred pending diagnosis |
| Simplify or redesign apparatus | 89 | Deferred as premature |
| Close synthetic torsion-balance lane | 80 | Deferred until one bounded diagnosis is considered |

The diagnosis route remains first in all 24 frozen one-at-a-time criterion
weight variants. The scores order work; they are not truth probabilities or
scientific evidence.

## Why diagnosis precedes replacement

The accepted failure is compatible with at least three materially different
causes:

```text
IMPLEMENTATION_DEFECT
NUMERICAL_METHOD_INADEQUACY
REFERENCE_ORACLE_INADEQUACY
```

An implementation error calls for a localized correction. Fixed-order
cubature failure calls for a different integration strategy. An unconverged
reference calls for a stronger oracle before production is judged. Immediate
replacement would select a method before determining which problem it must
solve.

## Required packet-preparation boundary

The diagnosis packet must freeze all numerical grids, tolerances, precision
levels, computational budgets, and stop rules before diagnostic execution. It
must forbid post-result selection of favorable gaps, ranges, subdomains, or
reference methods.

### Separate physical components

Newtonian and Yukawa sphere interactions must be recorded separately. Each
requires an absolute result, relative error, convergence record, dimensional
check, and limiting behavior. A combined total cannot substitute because it
could conceal cancellation or allow the Newtonian component to mask a poor
Yukawa calculation.

### Independent reference oracle

A nearby order of the same fixed tensor-product cubature is not a sufficient
oracle. The packet must select a genuinely independent route from analytic
uniform-sphere evaluation, a semi-analytic reduced integral, adaptive
high-precision quadrature, arbitrary precision, or an independent coordinate,
convolution, or momentum-space transformation. The oracle must demonstrate its
own convergence under preregistered tolerances.

### Gap, range, and near-contact strata

The packet must freeze a small grid covering:

```text
lambda << gap
lambda ~ gap
lambda >> gap
```

and multiple closest-surface separations. It must record minimum separation,
local kernel variation, subdomain contributions, adaptive-subdivision
resolution, and tensor-product node efficiency so near-contact localization can
be distinguished from a global implementation error.

### Precision and cancellation

Required probes include standard versus higher precision, separate versus
combined components, stable summation, symmetry reduction, coordinate scaling,
and both absolute and relative error behavior.

### Angular DFT isolation

The DFT path must first be tested on analytic synthetic torque with known
`n=2,4,6` coefficients. Production torque may be tested only after kernel
accuracy is established. The diagnostic must distinguish insufficient angular
resolution from kernel noise contaminating otherwise adequate harmonic
extraction.

## Bounded outputs

Authorized packet outputs are limited to kernel accuracy, oracle convergence,
error versus resolution/gap/range, analytic and production DFT convergence,
root-cause classification, a recommended numerical method, and estimated
computational cost.

The packet must forbid:

```text
final real-150 apparatus vector
Jacobian
SVD
eta_lambda
identifiability result
synthetic noise
sensitivity forecast
```

## Frozen diagnostic outcome vocabulary

```text
IMPLEMENTATION_DEFECT_LOCALIZED
FIXED_ORDER_CUBATURE_INADEQUATE
REFERENCE_ORACLE_INADEQUATE
NEAR_CONTACT_DOMAIN_DECOMPOSITION_REQUIRED
ANGULAR_DFT_RESOLUTION_INDEPENDENTLY_INADEQUATE
KERNEL_NOISE_DRIVES_DFT_FAILURE
INTERNAL_APPARATUS_FORWARD_MODEL_NOT_ECONOMICALLY_VALIDATABLE
```

These are future diagnostic outcomes, not findings of this selector.

## Firewalls

```text
diagnosis packet prepared now:       NO
diagnostic execution authorized:     NO
integration replacement authorized:  NO
apparatus redesign authorized:       NO
lane closure authorized:             NO
additional Stage A execution:        NO
automatic V2:                        NO
Stage B:                             NO
```

Any method change after diagnosis requires a fresh selector. Any future full
Stage A execution requires a fresh packet and independent review.
