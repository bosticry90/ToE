# RL11 Causality Signal-Cone Front Door Contract v0

Schema ID:
- OV-RL-11_causality_signal_cone_comparator/v0

Input artifact schema:
- RL/causality_signal_cone_front_door_report/v1

Pinned inputs (domain)
- L=6.283185307179586
- N=256
- dt_pos=0.01
- dt_neg=0.05
- steps=10
- c0=1.0
- CFL_max=1.0
- eps_causal=1e-10
- eps_acausal=1e-3

Required fields:
- schema
- config_tag
- regime_tag
- domain_tag
- params: {length, nx, dx, c0, cfl_max, dt_pos, dt_neg, steps, eps_causal, eps_acausal}
- boundary
- x
- x0
- cases[{case_id, kind, dt, t_end, cfl, radius, radius_cells, leakage_outside_cone, psi}]
- fingerprint

Case kinds
- positive_control
- negative_control

Expectation-aware pass semantics
- positive_control: cfl <= cfl_max and leakage_outside_cone <= eps_causal
- negative_control: cfl > cfl_max and leakage_outside_cone >= eps_acausal

Blocked conditions
- missing reference or candidate artifacts

Reason codes (non-exhaustive; v0)
- FAIL_DOMAIN_PARAMETER_INCONSISTENT
- FAIL_CFL_BOUND
- FAIL_CAUSAL_LEAKAGE
- FAIL_ACAUSAL_LEAKAGE_NOT_DETECTED
- FAIL_NONDETERMINISTIC_FINGERPRINT
- rl11_causality_cone_ok
- rl11_acausal_leakage_detected

Scope limits
- front_door_only
- typed_artifacts_only
- deterministic_record_only
- discriminative_candidate
- within_rep_only
- no_external_truth_claim
