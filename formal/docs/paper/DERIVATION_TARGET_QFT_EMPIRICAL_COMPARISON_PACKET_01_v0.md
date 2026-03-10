# Derivation Target: QFT Empirical Comparison Packet 01 v0

Spec ID:
- `DERIVATION_TARGET_QFT_EMPIRICAL_COMPARISON_PACKET_01_v0`

Target ID:
- `TARGET-QFT-EMPIRICAL-COMPARISON-PACKET-01-v0`

Classification:
- `P-POLICY`

Purpose:
- Pin the first bounded empirical comparison packet for QFT.

Non-claim boundary:
- bounded packet/control surface only.
- no external-truth claim.

Packet bundle (bounded non-claim):
- `QFT_EMPIRICAL_PACKET_01_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM`
- `QFT_EMPIRICAL_PACKET_01_ARTIFACT_v0: qft_empirical_comparison_packet_01_v0`
- `QFT_EMPIRICAL_PACKET_01_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
- `QFT_EMPIRICAL_PACKET_01_DECISION_v0: INCONCLUSIVE_v0`
- `QFT_EMPIRICAL_PACKET_01_EVIDENCE_TIER_v0: INTERMEDIATE_v0`
- artifact path: `formal/output/qft_empirical_comparison_packet_01_v0.json`
- coupling gate path: `formal/python/tests/test_qft_empirical_comparison_packet_01_gate.py`

Canonical pointers:
- evidence promotion pointer: `formal/docs/paper/DERIVATION_TARGET_QFT_EMPIRICAL_PACKET_01_EVIDENCE_PROMOTION_v0.md`
- discriminator pointer: `formal/docs/paper/DERIVATION_TARGET_QFT_EMPIRICAL_DISCRIMINATOR_EMP_QFT_01_v0.md`
- protocol pointer: `formal/docs/release/FOUNDATIONAL_EMPIRICAL_COMPARISON_PROTOCOL_v0.md`
