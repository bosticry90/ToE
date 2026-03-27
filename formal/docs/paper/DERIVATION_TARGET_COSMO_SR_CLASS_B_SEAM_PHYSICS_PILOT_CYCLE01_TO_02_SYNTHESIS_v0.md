# Derivation Target: COSMO-SR Class-B Seam Physics Pilot Cycle01-to-02 Synthesis v0

Spec ID:
- DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_TO_02_SYNTHESIS_v0

Target ID:
- TARGET-COSMO-SR-CLASS-B-SEAM-PHYSICS-PILOT-CYCLE01-TO-02-SYNTHESIS-v0

Classification:
- P-PHYSICS

Purpose:
- Provide a bounded synthesis checkpoint after COSMO-SR Cycle01 and Cycle02.
- Record the additive substance introduced in Cycle02 beyond Cycle01.
- State low-z compatibility impact, second-order exclusion meaning, remaining promotion blockers, and next branch boundary.
- Keep this surface bounded and non-claim.

Adjudication token:
- COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_TO_02_SYNTHESIS_ADJUDICATION: NOT_YET_DISCHARGED

Synthesis anchors:
- formal/docs/paper/DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_v0.md
- formal/docs/paper/DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE02_v0.md
- formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle01_v0.json
- formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle02_v0.json
- formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle01_gate.py
- formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle02_gate.py

Checkpoint synthesis tokens:
- COSMO_SR_CYCLE01_BASELINE_v0: LOW_Z_LINEAR_ALIGNMENT_WITNESS_PINNED
- COSMO_SR_CYCLE02_ADDITIVE_DELTA_v0: LOW_Z_SECOND_ORDER_MATCH_IMPROVEMENT_AND_EXCLUSION_PINNED
- COSMO_SR_LOW_Z_COMPATIBILITY_IMPACT_v0: SECOND_ORDER_SURROGATE_REDUCES_EXACT_MAP_RESIDUALS_ON_BOUNDED_WINDOW
- COSMO_SR_SECOND_ORDER_EXCLUSION_MEANING_v0: HIGH_Z_SERIES_DRIFT_EXCLUDED_AS_NONCOMPATIBLE
- COSMO_SR_PROMOTION_BLOCKER_STATE_v0: CLASS_FLIP_AND_FULL_THEOREM_DISCHARGE_NOT_READY
- COSMO_SR_NONCLAIM_BOUNDARY_STATE_v0: CLASS_FLIP_AND_FULL_DISCHARGE_NOT_CLAIMED

Decision boundary rule:
- COSMO_SR_NEXT_DECISION_RULE_v0: IF_ONE_BOUNDED_ADDITIVE_COSMO_SR_PAYLOAD_IS_READY_THEN_CYCLE03_ELSE_RETURN_QM_STAT_CYCLE04
- COSMO_SR_DECISION_BOUNDARY_STATUS_v0: SYNTHESIS_CHECKPOINT_READY

Non-claim boundary:
- no seam class flip claim,
- no full theorem discharge claim,
- no global cosmology completion claim,
- no external truth claim.

Synthesis status lock:
- COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_TO_02_SYNTHESIS_STATUS_v0: CHECKPOINT_PINNED_NONCLAIM
- COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_TO_02_SYNTHESIS_GATE_v0: formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle01_to_02_synthesis_gate.py
