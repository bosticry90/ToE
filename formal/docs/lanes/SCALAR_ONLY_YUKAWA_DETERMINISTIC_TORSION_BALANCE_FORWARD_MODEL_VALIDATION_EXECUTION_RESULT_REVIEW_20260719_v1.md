# Scalar-only Yukawa deterministic torsion-balance execution result review 20260719 v1

Document ID:

- `SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_FORWARD_MODEL_VALIDATION_EXECUTION_RESULT_REVIEW_20260719_v1`

Status:

- `INDEPENDENT_RESULT_REVIEW_COMPLETE`
- `11 / 11 GATES PASSED`
- `BLOCKED_PRODUCTION_KERNEL_VALIDATION`
- `ACCEPTED_CONSERVATIVE_STAGE_A_EXECUTION_RESULT`

Machine-readable review:

- `formal/docs/release/SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_FORWARD_MODEL_VALIDATION_EXECUTION_RESULT_REVIEW_20260719_v1.json`
- SHA-256: `c6a7278025714753144e429d47fe065eb8a40bdd8d45e3f609a25c0ffd6aa968`

Review generator:

- `formal/python/tools/scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_execution_result_review_v1.py`
- SHA-256: `51f3a90eba53d334e557eab151056b8ca11e50100317628300dd8c59f092a6ab`

## Accepted result

```text
principal result:
BLOCKED_PRODUCTION_KERNEL_VALIDATION

deterministic apparatus model:
NOT VALIDATED

scientific real-150 vector:
NOT ACCEPTED

Jacobian / SVD / eta_lambda:
NOT COMPUTED

physical identifiability:
NOT TESTED

Stage B:
NOT ELIGIBLE AND NOT AUTHORIZED

automatic V2:
NOT AUTHORIZED
```

The review accepts only the early physical-control block. It does not accept a
scalar-versus-nuisance degeneracy, reject the apparatus design, or draw any
conclusion about the physical scalar branch.

## Independent reproduction

The review hash-verified seven execution surfaces and all ten manifested
pre-identifiability artifacts. The release and output execution-result copies
are byte-identical, and the canonical output directory contains exactly the
manifested files plus its execution-result copy.

The reproduced uniform-sphere failures are:

```text
production versus order 24:
6.86790204140759891e-02

order 16 versus order 24:
4.20277601862804162e-01

required tolerance:
1.00000000000000000e-06
```

Order 24 is not accepted as a converged oracle. The large order-16/order-24
disagreement establishes that the comparison integration itself is unresolved.

The independent closed-form energies used to audit the three relative-error
denominators have absolute magnitudes:

```text
3.2252273146491470e-24 J
2.2746185717513740e-16 J
1.2700907357438663e-14 J
```

All are finite and well above the `1e-300 J` denominator floor. The reported
failure is therefore not an artifact of division by a zero or floored reference.

## Kernel and cubature path audit

The frozen source uses:

- `G = 6.67430e-11` SI;
- Yukawa amplitude `A_Y = 1/3`;
- `19250 kg/m^3` source and detector densities;
- `5 mm` source and detector radii;
- the uniform-sphere factor
  `3 (x cosh(x) - sinh(x)) / x^3`;
- the same Yukawa `exp(-r/lambda)/r` kernel in the analytic and density paths.

The reduced density comparison includes both sphere radii, both polar cosines,
the radial `r^2` volume factors, and two analytically reduced azimuthal factors.
The requested Gauss-Legendre order supplies all four numerical dimensions.
Thus the execution did not merely leave a dimension fixed at the wrong order.

This static correctness is not evidence of numerical convergence. It supports
the narrower conclusion that the analytic and cubature paths disagree despite
having the intended formulas and measures.

## Harmonic refinement and structural controls

The DFT path retains the frozen uniform angular grid, `exp(-i n theta)` phase,
and `1/N` normalization. Its reproduced refinement result is:

```text
256 versus 512 angular samples:
1.48161245680641391e-06

required tolerance:
1.00000000000000000e-08
```

All five mutations and all six symmetry, sign, and phase controls passed. These
checks establish structural routing and symmetry behavior, not absolute
extended-source accuracy.

## Firewall and component custody

The output preserves 150 Newtonian rows, 150 total-reference rows, and 3,750
Yukawa rows as separate diagnostic components. These vectors are not accepted
as scientific predictions.

The Jacobian table contains only:

```text
NOT_COMPUTED_EARLY_PHYSICAL_CONTROL_BLOCK
```

No Jacobian column, singular value, nuisance projector, `eta_lambda`, or
physical-identifiability classification was produced.

## Launch-custody qualification

The review accepts the custody record with its disclosed technical relaunch.
One file-path launch failed before a model call. A second launch completed one
in-memory compute pass and then failed before writing outputs because NumPy
`int64` was not JSON serializable. The completed launch followed a
serialization-only change and wrote the sole canonical output directory.

No scientific parameter, threshold, geometry, or production kernel changed,
and no prior scientific value was exposed or used to choose the recovery. This
is not represented as a pristine single process launch. It is accepted only as
one committed canonical execution with a disclosed precommit technical
relaunch and no silent replacement.

## Fresh selector boundary

The independent review authorizes only:

```text
select_post_scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_v1_execution_result_scientific_response_v0
```

That selector may compare:

1. `NUMERICAL_KERNEL_DIAGNOSIS`
2. `REPLACE_PRODUCTION_INTEGRATION_METHOD`
3. `SIMPLIFY_OR_REDESIGN_APPARATUS`
4. `CLOSE_SYNTHETIC_TORSION_BALANCE_LANE`

The review does not select among them. It authorizes no numerical diagnosis,
replacement kernel, apparatus redesign, lane closure, deterministic rerun, V2,
or Stage B work by itself.
