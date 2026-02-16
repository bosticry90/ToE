# RL09 Dispersion-Topology Bridge Front Door Contract v0

Schema ID:
- OV-RL-09_dispersion_topology_bridge_comparator/v0

Input artifact schema:
- RL/dispersion_topology_front_door_report/v1

Pinned inputs (domain)
- L=6.283185307179586
- N_k=256
- eps_winding=1e-8
- positive control: t1=0.5, t2=1.0
- negative control: t1=1.0, t2=0.5

Required fields:
- schema
- config_tag
- regime_tag
- domain_tag
- params: {length, nk, t1_pos, t2_pos, t1_neg, t2_neg, eps_winding}
- boundary
- k
- cases[{case_id, kind, t1, t2, dx, dy, energy, theta, theta_delta, winding_raw, winding_rounded, abs_err, min_energy}]
- fingerprint

Case kinds
- positive_control
- negative_control

Expectation-aware pass semantics
- positive_control: abs(winding_raw - 1) <= eps_winding
- negative_control: abs(winding_raw - 0) <= eps_winding

Blocked conditions
- missing reference or candidate artifacts

Reason codes (non-exhaustive; v0)
- FAIL_K_GRID_ORDER
- FAIL_K_GRID_ALIGNMENT
- FAIL_DOMAIN_PARAMETER_INCONSISTENT
- FAIL_WINDING_TARGET_MISMATCH
- FAIL_NONDETERMINISTIC_FINGERPRINT
- rl09_winding_target_satisfied

Scope limits
- front_door_only
- typed_artifacts_only
- deterministic_record_only
- discriminative_candidate
- within_rep_only
- no_external_truth_claim
