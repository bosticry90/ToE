# PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_18_PHASE6_SIXTH_LIVE_MATRIX_PACKET_20260407_v0

## Tranche name
PHYS_MATH_THROUGHPUT_T18_PHASE6_SIXTH_LIVE_MATRIX_PACKET

## Objective
Execute the sixth bounded live-matrix packet under non-live control posture while preserving conservative promotion policy invariance and bounded progression controls.

## Matrix packet contract
- packet_size: exactly one primary pillar objective plus one primary seam objective.
- primary_pillar: QM.
- primary_seam: SEAM_GR_QM.
- lane_selection_required_before_execution: true.
- non_selected_lanes_policy: explicit paused status required.
- live_authorization_expiry_hours: 72.
- promotion_policy: conservative, two consecutive green live packets required before scope escalation.

## Allowed files
- formal/docs/release/PHYS_MATH_THROUGHPUT_REMEDIATION_PROGRAM_v0.md (edit)
- formal/docs/release/PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_18_PHASE6_SIXTH_LIVE_MATRIX_PACKET_20260407_v0.md (new)
- formal/output/reports/physics_math_throughput_phase6_t18_sixth_live_matrix_packet_20260407_v0.json (new)
- formal/python/tests/test_physics_math_throughput_phase6_t18_sixth_live_matrix_packet_gate.py (new)
- formal/python/tests/test_physics_math_throughput_phase6_live_promotion_policy_gate.py (edit)
- formal/python/tests/test_physics_math_throughput_program_closeout_summary_gate.py (edit)
- formal/python/tools/physics_math_throughput_rolling_window_metrics.py (edit)
- formal/python/tools/physics_math_throughput_phase6_live_matrix_packet_metrics.py (edit)

## Out of scope
- release-gate contract edits
- packet/scalar policy edits
- theorem-body claim promotion

## Rollback anchor
WORKING_TREE_BASELINE_20260407_T18_EXECUTION
