# PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_13_PHASE6_FIRST_LIVE_MATRIX_PACKET_20260407_v0

## Tranche name
PHYS_MATH_THROUGHPUT_T13_PHASE6_FIRST_LIVE_MATRIX_PACKET

## Objective
Declare a bounded first live matrix packet pre-execution contract with explicit execution-required lane selection, fixed authorization expiry, paused non-selected lanes, and conservative promotion policy.

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
- formal/docs/release/PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_13_PHASE6_FIRST_LIVE_MATRIX_PACKET_20260407_v0.md (new)
- formal/output/reports/physics_math_throughput_phase6_t13_first_live_matrix_packet_20260407_v0.json (new)
- formal/python/tests/test_physics_math_throughput_phase6_t13_first_live_matrix_packet_gate.py (new)
- formal/python/tests/test_physics_math_throughput_phase6_live_matrix_objective_gate.py (new)
- formal/python/tests/test_physics_math_throughput_phase6_live_authorization_expiry_gate.py (new)
- formal/python/tests/test_physics_math_throughput_phase6_live_invariance_continuity_gate.py (new)
- formal/python/tests/test_physics_math_throughput_phase6_live_promotion_policy_gate.py (new)
- formal/python/tools/physics_math_throughput_phase6_live_matrix_packet_metrics.py (new)
- formal/python/tests/test_physics_math_throughput_program_closeout_summary_gate.py (edit)

## Out of scope
- live execution enablement in this tranche
- lane selection mutation in this tranche
- release-gate contract edits
- packet/scalar policy edits

## Rollback anchor
WORKING_TREE_BASELINE_20260407_T13_PREEXECUTION
