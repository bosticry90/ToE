# Derivation Target: QM Empirical Comparison Packet 01 v0

Spec ID:
- `DERIVATION_TARGET_QM_EMPIRICAL_COMPARISON_PACKET_01_v0`

Target ID:
- `TARGET-QM-EMPIRICAL-COMPARISON-PACKET-01-v0`

Classification:
- `P-POLICY`

Purpose:
- Pin the first bounded empirical comparison packet for QM.
- Link artifact -> bridge -> prediction -> discriminator output -> decision.

Non-claim boundary:
- bounded packet/control surface only.
- no external-truth claim.
- no pillar adjudication promotion.

Packet bundle (bounded non-claim):
- `QM_EMPIRICAL_PACKET_01_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM`
- `QM_EMPIRICAL_PACKET_01_ARTIFACT_v0: qm_empirical_comparison_packet_01_v0`
- `QM_EMPIRICAL_PACKET_01_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
- `QM_EMPIRICAL_PACKET_01_DECISION_v0: INCONCLUSIVE_v0`
- `QM_EMPIRICAL_PACKET_01_EVIDENCE_TIER_v0: INTERMEDIATE_v0`
- artifact path: `formal/output/qm_empirical_comparison_packet_01_v0.json`
- coupling gate path: `formal/python/tests/test_qm_empirical_comparison_packet_01_gate.py`

Evidence promotion pointer:
- `formal/docs/paper/DERIVATION_TARGET_QM_EMPIRICAL_PACKET_01_EVIDENCE_PROMOTION_v0.md`

Canonical pointers:
- discriminator pointer: `formal/docs/paper/DERIVATION_TARGET_QM_EMPIRICAL_DISCRIMINATOR_EMP_QM_01_v0.md`
- protocol pointer: `formal/docs/release/FOUNDATIONAL_EMPIRICAL_COMPARISON_PROTOCOL_v0.md`
