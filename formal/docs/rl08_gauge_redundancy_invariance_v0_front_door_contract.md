# RL08 Gauge Redundancy Invariance Front Door Contract v0

Schema ID:
- OV-RL-08_gauge_redundancy_invariance_comparator/v0

Input artifact schema:
- RL/gauge_redundancy_front_door_report/v1

Pinned inputs (domain)
- L=6.283185307179586
- N=128
- dx=L/N
- alpha=0.2
- eps_invariant=1e-10
- eps_break=1e-3
- gauge transform: psi(x) -> psi(x) * exp(i*phi(x))
- phi(x)=alpha*sin(2*pi*x/L)
- initial field: deterministic complex field defined in front door

Required fields:
- schema
- config_tag
- regime_tag
- domain_tag
- params: {length, nx, dx, alpha, eps_invariant, eps_break}
- boundary
- x
- psi_real
- psi_imag
- phi
- rho
- rho_gauge
- obs_bad
- obs_bad_gauge
- cases[{case_id, kind, residual_maxabs}]
- fingerprint

Case kinds
- positive_control
- negative_control

Expectation-aware pass semantics
- positive_control: residual_maxabs <= eps_invariant
- negative_control: residual_maxabs >= eps_break

Blocked conditions
- missing reference or candidate artifacts

Reason codes (non-exhaustive; v0)
- FAIL_X_GRID_ORDER
- FAIL_X_GRID_ALIGNMENT
- FAIL_DOMAIN_PARAMETER_INCONSISTENT
- FAIL_GAUGE_INVARIANCE
- FAIL_GAUGE_BREAK_NOT_DETECTED
- FAIL_NONDETERMINISTIC_FINGERPRINT
- rl08_gauge_invariance_ok
- rl08_gauge_break_detected

Scope limits
- front_door_only
- typed_artifacts_only
- deterministic_record_only
- discriminative_candidate
- within_rep_only
- no_external_truth_claim
