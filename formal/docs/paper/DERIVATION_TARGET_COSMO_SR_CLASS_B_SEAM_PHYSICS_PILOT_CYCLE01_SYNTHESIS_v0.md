# Derivation Target: COSMO-SR Class-B Seam Physics Pilot Cycle01 Synthesis v0

Spec ID:
- DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_SYNTHESIS_v0

Target ID:
- TARGET-COSMO-SR-CLASS-B-SEAM-PHYSICS-PILOT-CYCLE01-SYNTHESIS-v0

Classification:
- P-PHYSICS

Purpose:
- Provide a compact synthesis checkpoint after COSMO-SR Cycle01.
- Record what Cycle01 establishes, what remains blocked, and the explicit next decision rule.
- Keep this surface bounded and non-claim.

Adjudication token:
- COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_SYNTHESIS_ADJUDICATION: NOT_YET_DISCHARGED

Synthesis anchors:
- formal/docs/paper/DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_v0.md
- formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle01_v0.json
- formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle01_gate.py

Checkpoint synthesis tokens:
- COSMO_SR_CYCLE01_CONTRIBUTION_v0: BOUNDED_LOW_Z_KINEMATIC_ALIGNMENT_WITNESS_PINNED
- COSMO_SR_LOW_Z_COVERAGE_STATE_v0: LINEAR_ALIGNMENT_ONLY_ON_BOUNDED_LOW_Z_WINDOW
- COSMO_SR_HIGH_Z_EXCLUSION_STATE_v0: LINEARIZATION_DRIFT_EXCLUDED_AS_NONCOMPATIBLE
- COSMO_SR_PROMOTION_BLOCKER_STATE_v0: THEOREM_LINKED_DISCHARGE_AND_CLASS_FLIP_NOT_READY
- COSMO_SR_NONCLAIM_BOUNDARY_STATE_v0: CLASS_FLIP_AND_FULL_DISCHARGE_NOT_CLAIMED

Decision boundary rule:
- COSMO_SR_NEXT_DECISION_RULE_v0: IF_ONE_BOUNDED_ADDITIVE_COSMO_SR_PAYLOAD_IS_READY_THEN_CYCLE02_ELSE_RETURN_QM_STAT_CYCLE03
- COSMO_SR_DECISION_BOUNDARY_STATUS_v0: SYNTHESIS_CHECKPOINT_READY

Non-claim boundary:
- no seam class flip claim,
- no full theorem discharge claim,
- no global cosmology completion claim,
- no external truth claim.

Synthesis status lock:
- COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_SYNTHESIS_STATUS_v0: CHECKPOINT_PINNED_NONCLAIM
- COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_SYNTHESIS_GATE_v0: formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle01_synthesis_gate.py
