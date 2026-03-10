# Derivation Target: SR Empirical Comparison Packet 01 v0

Spec ID:
- `DERIVATION_TARGET_SR_EMPIRICAL_COMPARISON_PACKET_01_v0`

Target ID:
- `TARGET-SR-EMPIRICAL-COMPARISON-PACKET-01-v0`

Classification:
- `P-POLICY`

Purpose:
- Pin the first bounded empirical comparison packet for SR.

Non-claim boundary:
- bounded packet/control surface only.
- no external-truth claim.

Packet bundle (bounded non-claim):
- `SR_EMPIRICAL_PACKET_01_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM`
- `SR_EMPIRICAL_PACKET_01_ARTIFACT_v0: sr_empirical_comparison_packet_01_v0`
- `SR_EMPIRICAL_PACKET_01_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
- `SR_EMPIRICAL_PACKET_01_DECISION_v0: INCONCLUSIVE_v0`
- `SR_EMPIRICAL_PACKET_01_EVIDENCE_TIER_v0: INTERMEDIATE_v0`
- artifact path: `formal/output/sr_empirical_comparison_packet_01_v0.json`
- coupling gate path: `formal/python/tests/test_sr_empirical_comparison_packet_01_gate.py`

Canonical pointers:
- evidence promotion pointer: `formal/docs/paper/DERIVATION_TARGET_SR_EMPIRICAL_PACKET_01_EVIDENCE_PROMOTION_v0.md`
- discriminator pointer: `formal/docs/paper/DERIVATION_TARGET_SR_EMPIRICAL_DISCRIMINATOR_EMP_SR_01_v0.md`
- protocol pointer: `formal/docs/release/FOUNDATIONAL_EMPIRICAL_COMPARISON_PROTOCOL_v0.md`
