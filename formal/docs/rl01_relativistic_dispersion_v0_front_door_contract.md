# RL01 Relativistic Dispersion Front Door Contract v0

Schema ID:
- OV-RL-01_relativistic_dispersion_comparator/v0

Input artifact schema:
- RL/dispersion_front_door_report/v1

Required fields:
- schema
- config_tag
- regime_tag
- params: {c, m}
- k
- omega2
- fingerprint

Blocked conditions:
- missing reference or candidate artifacts

Reason codes (non-exhaustive; v0):
- FAIL_K_GRID_ORDER
- FAIL_K_GRID_ALIGNMENT
- FAIL_REGIME_MISMATCH
- FAIL_REL_LIMIT_SHAPE_MISMATCH
- FAIL_REL_LIMIT_NONDETERMINISTIC
- rl01_relativistic_dispersion_constraints_satisfied

Scope limits:
- front_door_only
- typed_artifacts_only
- deterministic_record_only
- discriminative_candidate
- within_rep_only
- no_external_truth_claim
