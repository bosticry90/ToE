# RL10 Entropy Balance Front Door Contract v0

Schema ID:
- OV-RL-10_entropy_balance_comparator/v0

Input artifact schema:
- RL/entropy_balance_front_door_report/v1

Pinned inputs (domain)
- N=3
- eps_balance=1e-8
- eps_entropy=1e-3
- P_pos rows: [0.7, 0.2, 0.1], [0.2, 0.6, 0.2], [0.1, 0.2, 0.7]
- P_neg rows: [0.7, 0.25, 0.05], [0.05, 0.7, 0.25], [0.25, 0.05, 0.7]

Required fields:
- schema
- config_tag
- regime_tag
- domain_tag
- params: {state_count, eps_balance, eps_entropy}
- boundary
- cases[{case_id, kind, transition_matrix, stationary_pi, sigma_proxy, db_residual}]
- fingerprint

Case kinds
- positive_control
- negative_control

Expectation-aware pass semantics
- positive_control: sigma_proxy <= eps_balance and db_residual <= eps_balance
- negative_control: sigma_proxy >= eps_entropy or db_residual >= eps_entropy

Blocked conditions
- missing reference or candidate artifacts

Reason codes (non-exhaustive; v0)
- FAIL_DOMAIN_PARAMETER_INCONSISTENT
- FAIL_ENTROPY_BALANCE
- FAIL_ENTROPY_PRODUCTION_NOT_DETECTED
- FAIL_NONDETERMINISTIC_FINGERPRINT
- rl10_entropy_balance_ok
- rl10_entropy_production_detected

Scope limits
- front_door_only
- typed_artifacts_only
- deterministic_record_only
- discriminative_candidate
- within_rep_only
- no_external_truth_claim
