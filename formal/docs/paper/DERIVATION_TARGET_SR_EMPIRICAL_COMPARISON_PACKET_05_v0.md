# Derivation Target: SR Empirical Comparison Packet 05 v0

Spec ID:
- `DERIVATION_TARGET_SR_EMPIRICAL_COMPARISON_PACKET_05_v0`

Target ID:
- `TARGET-SR-EMPIRICAL-COMPARISON-PACKET-05-v0`

Classification:
- `P-POLICY`

Purpose:
- Start a selective SR packet-05 lane under bounded non-claim controls.
- Preserve complete-v1 terminal posture while increasing discriminator sensitivity for the unresolved SR lane.

Non-claim boundary:
- bounded packet/control surface only.
- no external-truth claim.
- no maturity status promotion.

Packet bundle (bounded non-claim):
- `SR_EMPIRICAL_PACKET_05_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM`
- `SR_EMPIRICAL_PACKET_05_ARTIFACT_v0: sr_empirical_comparison_packet_05_v0`
- `SR_EMPIRICAL_PACKET_05_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
- `SR_EMPIRICAL_PACKET_05_SCHEMA_GATE_v0: REQUIRED_FIELDS_AND_STATUS_DECISION_ENFORCED`
- `SR_EMPIRICAL_PACKET_05_DECISION_v0: RETAIN_v0`
- `SR_EMPIRICAL_PACKET_05_EVIDENCE_TIER_v0: INTERMEDIATE_v0`
- `SR_EMPIRICAL_PACKET_05_DECISION_RECORD_POINTER_v0: formal/docs/paper/DERIVATION_TARGET_SR_EMPIRICAL_PACKET_05_DECISION_RECORD_v0.md`
- `SR_EMPIRICAL_PACKET_05_FALSIFICATION_SURFACE_POINTER_v0: formal/docs/paper/DERIVATION_TARGET_SR_EMPIRICAL_PACKET_05_FALSIFICATION_SURFACE_v0.md`
- `SR_EMPIRICAL_PACKET_05_OVERRIDE_CRITERIA_POINTER_v0: formal/docs/paper/DERIVATION_TARGET_SR_EMPIRICAL_PACKET_05_OVERRIDE_CRITERIA_v0.md`
- artifact path: `formal/output/sr_empirical_comparison_packet_05_v0.json`
- coupling gate path: `formal/python/tests/test_sr_empirical_comparison_packet_05_gate.py`
- schema gate path: `formal/python/tests/test_sr_empirical_packet_05_artifact_schema_gate.py`

Coupled pointers:
- state pointer: `State_of_the_Theory.md`
- roadmap pointer: `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
