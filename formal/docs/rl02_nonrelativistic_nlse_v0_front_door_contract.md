# RL02 Nonrelativistic NLSE Front Door Contract v0

Schema ID:
- OV-RL-02_nonrelativistic_nlse_comparator/v0

Input artifact schema:
- RL/nr_nlse_front_door_report/v1

Required fields:
- schema
- config_tag
- regime_tag
- params: {m, mu, epsilon}
- k
- omega
- fingerprint

Blocked conditions:
- missing reference or candidate artifacts

Reason codes (non-exhaustive; v0):
- FAIL_K_GRID_ORDER
- FAIL_K_GRID_ALIGNMENT
- FAIL_DOMAIN_PARAMETER_INCONSISTENT
- FAIL_LIMIT_SCALING_MISMATCH
- FAIL_DISPERSION_MISMATCH
- FAIL_NONDETERMINISTIC_FINGERPRINT
- rl02_nonrelativistic_limit_constraints_satisfied

Scope limits:
- front_door_only
- typed_artifacts_only
- deterministic_record_only
- discriminative_candidate
- within_rep_only
- no_external_truth_claim
