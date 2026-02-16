# RL07 Energy/Noether Conservation Front Door Contract v0

Schema ID:
- OV-RL-07_energy_noether_conservation_comparator/v0

Input artifact schema:
- RL/energy_noether_front_door_report/v1

Pinned inputs (domain)
- L=6.283185307179586
- N=128
- dx=L/N
- c=1.0
- dt=0.1*dx
- steps=2000
- gamma_negative=0.02
- eps_drift=5e-3
- eps_drop=0.10
- initial condition: u(x,0)=sin(x), v(x,0)=0

Required fields:
- schema
- config_tag
- regime_tag
- domain_tag
- params: {length, nx, dx, c, dt, steps, eps_drift, eps_drop}
- boundary
- x
- cases[{case_id, kind, gamma, e0, et, rel_drift, rel_drop, max_rel_drift}]
- fingerprint

Case kinds
- positive_control
- negative_control

Expectation-aware pass semantics
- positive_control: rel_drift <= eps_drift and max_rel_drift <= eps_drift
- negative_control: rel_drop >= eps_drop

Blocked conditions
- missing reference or candidate artifacts

Reason codes (non-exhaustive; v0)
- FAIL_X_GRID_ORDER
- FAIL_X_GRID_ALIGNMENT
- FAIL_DOMAIN_PARAMETER_INCONSISTENT
- FAIL_ENERGY_DRIFT_EXCEEDS
- FAIL_ENERGY_DROP_INSUFFICIENT
- FAIL_NONDETERMINISTIC_FINGERPRINT
- rl07_energy_conservation_ok
- rl07_energy_drop_detected

Scope limits
- front_door_only
- typed_artifacts_only
- deterministic_record_only
- discriminative_candidate
- within_rep_only
- no_external_truth_claim
