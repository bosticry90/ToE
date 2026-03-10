# Derivation Target: STAT Empirical Comparison Packet 03 v0

Spec ID:
- `DERIVATION_TARGET_STAT_EMPIRICAL_COMPARISON_PACKET_03_v0`

Target ID:
- `TARGET-STAT-EMPIRICAL-COMPARISON-PACKET-03-v0`

Classification:
- `P-POLICY`

Purpose:
- Start packet-03 maturity for STAT so packet-02 is not terminal.

Non-claim boundary:
- bounded packet/control surface only.
- no external-truth claim.

Packet bundle (bounded non-claim):
- `STAT_EMPIRICAL_PACKET_03_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM`
- `STAT_EMPIRICAL_PACKET_03_ARTIFACT_v0: stat_empirical_comparison_packet_03_v0`
- `STAT_EMPIRICAL_PACKET_03_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
- `STAT_EMPIRICAL_PACKET_03_DECISION_v0: INCONCLUSIVE_v0`
- `STAT_EMPIRICAL_PACKET_03_EVIDENCE_TIER_v0: INTERMEDIATE_v0`
- artifact path: `formal/output/stat_empirical_comparison_packet_03_v0.json`
- coupling gate path: `formal/python/tests/test_stat_empirical_comparison_packet_03_gate.py`
