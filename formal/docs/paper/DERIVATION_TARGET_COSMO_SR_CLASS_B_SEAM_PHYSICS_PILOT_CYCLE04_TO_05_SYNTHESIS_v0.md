# Derivation Target: COSMO-SR Class-B Seam Physics Pilot Cycle04-to-05 Synthesis v0

Spec ID:
- DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE04_TO_05_SYNTHESIS_v0

Target ID:
- TARGET-COSMO-SR-CLASS-B-SEAM-PHYSICS-PILOT-CYCLE04-TO-05-SYNTHESIS-v0

Classification:
- P-PHYSICS

Purpose:
- Provide a bounded synthesis checkpoint after COSMO-SR Cycle04 and Cycle05.
- Record the additive substance introduced in Cycle05 beyond Cycle04.
- State low-z compatibility impact, octic drift exclusion meaning, remaining promotion blockers, and next branch boundary.
- Keep this surface bounded and non-claim.

Adjudication token:
- COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE04_TO_05_SYNTHESIS_ADJUDICATION: NOT_YET_DISCHARGED

Synthesis anchors:
- formal/docs/paper/DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE04_v0.md
- formal/docs/paper/DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE05_v0.md
- formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle04_v0.json
- formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle05_v0.json
- formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle04_gate.py
- formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle05_gate.py

Checkpoint synthesis tokens:
- COSMO_SR_CYCLE04_BASELINE_v0: LOW_Z_SEXTIC_MATCH_IMPROVEMENT_AND_EXCLUSION_PINNED
- COSMO_SR_CYCLE05_ADDITIVE_DELTA_v0: LOW_Z_OCTIC_MATCH_IMPROVEMENT_AND_EXCLUSION_PINNED
- COSMO_SR_LOW_Z_COMPATIBILITY_IMPACT_v0: OCTIC_SURROGATE_REDUCES_OR_MATCHES_SEXTIC_RESIDUALS_ON_BOUNDED_WINDOW
- COSMO_SR_OCTIC_DRIFT_EXCLUSION_MEANING_v0: HIGH_Z_OCTIC_SERIES_DRIFT_EXCLUDED_AS_NONCOMPATIBLE
- COSMO_SR_PROMOTION_BLOCKER_STATE_v0: CLASS_FLIP_AND_FULL_THEOREM_DISCHARGE_NOT_READY
- COSMO_SR_NONCLAIM_BOUNDARY_STATE_v0: CLASS_FLIP_AND_FULL_DISCHARGE_NOT_CLAIMED

Decision boundary rule:
- COSMO_SR_NEXT_DECISION_RULE_v0: IF_ONE_BOUNDED_ADDITIVE_COSMO_SR_PAYLOAD_IS_READY_THEN_CYCLE06_ELSE_RETURN_QM_STAT_CYCLE05
- COSMO_SR_DECISION_BOUNDARY_STATUS_v0: SYNTHESIS_CHECKPOINT_READY

Non-claim boundary:
- no seam class flip claim,
- no full theorem discharge claim,
- no global cosmology completion claim,
- no external truth claim.

Synthesis status lock:
- COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE04_TO_05_SYNTHESIS_STATUS_v0: CHECKPOINT_PINNED_NONCLAIM
- COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE04_TO_05_SYNTHESIS_GATE_v0: formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle04_to_05_synthesis_gate.py
