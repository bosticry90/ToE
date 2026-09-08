# Scalar-only Yukawa deterministic torsion-balance execution 20260719 v1

Document ID:

- `SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_FORWARD_MODEL_VALIDATION_EXECUTION_20260719_v1`

Status:

- `EXECUTION_COMPLETED_ONCE_PENDING_INDEPENDENT_RESULT_REVIEW`
- `BLOCKED_PRODUCTION_KERNEL_VALIDATION`
- `NO_IDENTIFIABILITY_CALCULATION_DUE_TO_EARLY_PHYSICAL_CONTROL_FAILURE`

Machine-readable execution record:

- `formal/docs/release/SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_FORWARD_MODEL_VALIDATION_EXECUTION_20260719_v1.json`
- SHA-256: `86d9c3a2b93ccf3ec480264522d532e9c3924536459e897fc74bf154abd64a13`

Custody addendum:

- `formal/docs/release/SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_FORWARD_MODEL_VALIDATION_EXECUTION_CUSTODY_ADDENDUM_20260719_v1.json`

Runtime sources:

- production module SHA-256: `4995c467f766466583c53c7904e2f1bb35b7c02970aece4a20e2315403ed8cac`
- executor SHA-256: `ec0209a433027d8e8523d9e0f21ba3662ccec559de33ea042cb0a765b64571ae`

## Outcome

The one authorized Stage A execution is consumed. The run stopped at the
preregistered physical-control firewall and did not construct the 17-column
Jacobian, compute singular values, project the scalar response, or evaluate
physical identifiability.

```text
authorized deterministic executions: 1
consumed deterministic executions:   1

principal outcome:
BLOCKED_PRODUCTION_KERNEL_VALIDATION

secondary outcome:
NO_IDENTIFIABILITY_CALCULATION_DUE_TO_EARLY_PHYSICAL_CONTROL_FAILURE

Stage B:       NOT AUTHORIZED
automatic V2: NOT AUTHORIZED
```

This is not `BLOCKED_PARAMETER_IDENTIFIABILITY`. The run established no result
about whether the scalar-range derivative lies inside the nuisance span.

## Control results

| Control family | Passed | Total | Result |
| --- | ---: | ---: | --- |
| Analytic benchmark groups | 3 | 4 | failed |
| Deliberate mutations | 5 | 5 | passed |
| Symmetry/sign/phase controls | 6 | 6 | passed |
| Convergence controls | 4 | 6 | failed |
| V1 identifiability controls | 0 | 0 | not reached |

The point-Newtonian, point-Yukawa, and apparatus torque/symmetry benchmark
groups passed. The uniform-sphere form-factor group failed:

```text
production form factor versus order-24 density cubature:
maximum relative error = 6.86790204140759891e-02

order-16 versus order-24 density cubature:
maximum relative error = 4.20277601862804162e-01

required density-cubature tolerance = 1.0e-06
```

Two preregistered convergence checks failed:

```text
angular DFT, 256 versus 512:
metric    = 1.48161245680641391e-06
tolerance = 1.0e-08

density cubature, order 16 versus 24:
metric    = 4.20277601862804162e-01
tolerance = 1.0e-06
```

All five deliberate mutations were detected. All six symmetry, sign, and phase
controls passed. The analytic torque agreed with the force/lever construction
to `2.48994395364869938e-16`, and the finest five-point energy derivative
agreed to `9.79011086691829908e-13` under the frozen combined error rule.

## Outputs and firewall behavior

The execution preserved the Newtonian real-150 vector, 25 Yukawa real-150
vectors, and the total reference real-150 vector for diagnosis. It emitted ten
hash-manifested pre-identifiability artifacts. The Jacobian table contains one
explicit `NOT_COMPUTED_EARLY_PHYSICAL_CONTROL_BLOCK` status row and no numerical
Jacobian columns because the physical firewall stopped execution first.

The completed canonical execution performed its required internal repeat. All
ten pre-result artifacts were byte-identical across the two internal passes.

No random noise, covariance, synthetic observation, Monte Carlo, likelihood,
sensitivity forecast, empirical datum, or parameter bound was used or created.
No value or sign of `alpha` was selected, no scalar branch was adopted, and no
native ToE gravitational principle or action was claimed.

## Launch-recovery disclosure

Before the canonical result was committed, one file-path launch failed before
any model call, and a second launch reached one in-memory deterministic compute
pass but failed while serializing a NumPy integer to JSON. It wrote no output
and exposed no scientific values. The only recovery change added explicit
NumPy-to-native canonical JSON conversion; no scientific parameter, threshold,
geometry, or kernel changed. The completed launch then performed the two frozen
byte-comparison passes.

The machine-readable custody addendum records all three launch attempts and
must be considered by the independent reviewer. This execution report does not
self-adjudicate whether that recovery satisfies execution custody.

## Required next authority

```text
review_scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_v1_execution_result
```

That review may accept or reject execution custody and may interpret only the
recorded early physical-control block. It may not authorize another deterministic
execution, repair V2, or Stage B automatically.
