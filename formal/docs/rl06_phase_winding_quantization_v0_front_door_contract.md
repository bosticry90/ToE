# RL06 Phase Winding Quantization Front Door Contract v0

Schema ID:
- OV-RL-06_phase_winding_quantization_comparator/v0

Input artifact schema:
- RL/phase_winding_front_door_report/v1

Required fields:
- schema
- config_tag
- regime_tag
- params: {length, nx, k_target, alpha_nonint, amplitude}
- boundary
- unwrap_method
- x
- cases[{case_id, kind, k_target, psi_real, psi_imag}]
- fingerprint

Blocked conditions:
- missing reference or candidate artifacts

Reason codes (non-exhaustive; v0):
- FAIL_X_GRID_ORDER
- FAIL_X_GRID_ALIGNMENT
- FAIL_DOMAIN_PARAMETER_INCONSISTENT
- FAIL_WINDING_NOT_INTEGER
- FAIL_WINDING_TARGET_MISMATCH
- FAIL_WINDING_NEGATIVE_CONTROL_NOT_DETECTED
- FAIL_NONDETERMINISTIC_FINGERPRINT
- rl06_phase_winding_quantized
- rl06_phase_winding_negative_control_detected

Scope limits:
- front_door_only
- typed_artifacts_only
- deterministic_record_only
- discriminative_candidate
- within_rep_only
- no_external_truth_claim
