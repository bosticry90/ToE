# CV03 UCFF Dispersion v1 Front Door Contract

Schema ID: `OV-CV-03_ucff_dispersion_comparator/v1`

Role: `discriminative_candidate`

Domain ID: `DRBR-DOMAIN-UCFF-01`

## Top-level required keys

- `schema`
- `date`
- `observable_id`
- `domain_id`
- `comparator_role`
- `tolerance_profile`
- `status`
- `inputs`
- `rows`
- `summary`
- `scope_limits`
- `fingerprint`

## Required row keys

- `artifact_id`
- `source`
- `input_fingerprint`
- `input_data_fingerprint`
- `metric_vector`
- `passed`
- `reason_codes`
- `diagnostics`

## Failure reason taxonomy

- `FAIL_DISPERSION_SHAPE_MISMATCH`
- `FAIL_DISPERSION_SIGN`
- `FAIL_DISPERSION_MONOTONICITY`
- `FAIL_K_GRID_ORDER`
- `FAIL_K_GRID_ALIGNMENT`
- `FAIL_DISPERSION_NONDETERMINISTIC`

Comparator pass reason:

- `cv03_dispersion_constraints_satisfied`

## Scope limits

- `front_door_only`
- `typed_artifacts_only`
- `deterministic_record_only`
- `discriminative_candidate`
- `no_external_truth_claim`
