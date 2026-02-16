# RL04 Continuity Front Door Contract v0

Schema ID:
- OV-RL-04_continuity_comparator/v0

Input artifact schema:
- RL/continuity_front_door_report/v1

Required fields:
- schema
- config_tag
- regime_tag
- params: {length, nx, dt, nt, k, omega, amplitude}
- boundary
- t
- x
- rho
- j
- fingerprint

Blocked conditions:
- missing reference or candidate artifacts

Reason codes (non-exhaustive; v0):
- FAIL_T_GRID_ORDER
- FAIL_X_GRID_ORDER
- FAIL_T_GRID_ALIGNMENT
- FAIL_X_GRID_ALIGNMENT
- FAIL_DOMAIN_PARAMETER_INCONSISTENT
- FAIL_CONTINUITY_RESIDUAL
- FAIL_NONDETERMINISTIC_FINGERPRINT
- rl04_continuity_constraints_satisfied

Scope limits:
- front_door_only
- typed_artifacts_only
- deterministic_record_only
- discriminative_candidate
- within_rep_only
- no_external_truth_claim
