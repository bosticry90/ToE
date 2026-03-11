# Derivation Target: SR Empirical Comparison Packet 02 v0

Spec ID:
- `DERIVATION_TARGET_SR_EMPIRICAL_COMPARISON_PACKET_02_v0`

Target ID:
- `TARGET-SR-EMPIRICAL-COMPARISON-PACKET-02-v0`

Classification:
- `P-POLICY`

Purpose:
- Pin the second bounded empirical comparison packet for SR.
- Open a controlled lane where `RETAIN_v0`, `PRUNE_v0`, or `INCONCLUSIVE_v0` is eligible under protocol guards.

Non-claim boundary:
- bounded packet/control surface only.
- no external-truth claim.
- no pillar adjudication promotion.

Packet bundle (bounded non-claim):
- `SR_EMPIRICAL_PACKET_02_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM`
- `SR_EMPIRICAL_PACKET_02_ARTIFACT_v0: sr_empirical_comparison_packet_02_v0`
- `SR_EMPIRICAL_PACKET_02_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
- `SR_EMPIRICAL_PACKET_02_DECISION_v0: INCONCLUSIVE_v0`
- `SR_EMPIRICAL_PACKET_02_EVIDENCE_TIER_v0: INTERMEDIATE_v0`
- `SR_EMPIRICAL_PACKET_02_DECISION_ELIGIBILITY_v0: RETAIN_OR_PRUNE_OR_INCONCLUSIVE_ALLOWED_WITH_PROTOCOL_GUARDS`
- artifact path: `formal/output/sr_empirical_comparison_packet_02_v0.json`
- coupling gate path: `formal/python/tests/test_foundational_empirical_packet02_matrix_consistency_gate.py`

Canonical pointers:
- decision record pointer: `formal/docs/paper/DERIVATION_TARGET_SR_EMPIRICAL_PACKET_02_DECISION_RECORD_v0.md`
- packet-01 pointer: `formal/docs/paper/DERIVATION_TARGET_SR_EMPIRICAL_COMPARISON_PACKET_01_v0.md`
- protocol pointer: `formal/docs/release/FOUNDATIONAL_EMPIRICAL_COMPARISON_PROTOCOL_v0.md`
- discriminator pointer: `formal/docs/paper/DERIVATION_TARGET_SR_EMPIRICAL_DISCRIMINATOR_EMP_SR_01_v0.md`
