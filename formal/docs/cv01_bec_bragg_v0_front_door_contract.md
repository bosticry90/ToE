# CV01 BEC-Bragg v0 Front Door Contract

Schema ID: `OV-CV-01_bec_bragg_v0_comparator/v1`

Role: `integrity_only`

## Top-level required keys

- `schema`
- `date`
- `observable_id`
- `domain_id`
- `comparator_role`
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

## Allowed reason codes (v1 contract)

- `cv01_metric_constraints_satisfied`
- `cv01_fail_nonpositive_cs2`
- `cv01_fail_metric_signature_identity`
- `cv01_fail_nonunit_gxx`
- `cv01_fail_nonpositive_declared_cs`
- `cv01_fail_declared_vs_metric_cs_mismatch`
- `cv01_fail_nonpositive_declared_c0`
- `cv01_fail_declared_vs_metric_c0_mismatch`

## Scope limits

- `front_door_only`
- `typed_artifacts_only`
- `deterministic_record_only`
- `integrity_only`
- `no_external_truth_claim`
