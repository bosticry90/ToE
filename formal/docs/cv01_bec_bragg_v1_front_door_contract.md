# CV01 BEC-Bragg v1 Front Door Contract

Schema ID: `OV-CV-01_bec_bragg_v1_comparator/v1`

Role: `discriminative_candidate`

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
- `cross_artifact`
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

## Required cross-artifact keys

- `check_id`
- `input_fingerprints`
- `input_data_fingerprints`
- `speed_linear`
- `speed_curved`
- `speed_residual`
- `tolerance`
- `passed`
- `reason_codes`

## Allowed reason codes (v1 contract)

- `cv01_metric_constraints_satisfied`
- `cv01_fail_nonpositive_cs2`
- `cv01_fail_metric_signature_identity`
- `cv01_fail_nonunit_gxx`
- `cv01_fail_nonpositive_declared_cs`
- `cv01_fail_declared_vs_metric_cs_mismatch`
- `cv01_fail_nonpositive_declared_c0`
- `cv01_fail_declared_vs_metric_c0_mismatch`
- `cv01_v1_cross_artifact_speed_consistent`
- `cv01_fail_linear_vs_curved_speed_inconsistent`
- `cv01_fail_cross_artifact_nonpositive_speed`

## Scope limits

- `front_door_only`
- `typed_artifacts_only`
- `deterministic_record_only`
- `discriminative_candidate`
- `no_external_truth_claim`
