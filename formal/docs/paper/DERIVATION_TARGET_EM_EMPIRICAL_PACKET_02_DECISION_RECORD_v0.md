# Derivation Target: EM Empirical Packet 02 Decision Record v0

Spec ID:
- `DERIVATION_TARGET_EM_EMPIRICAL_PACKET_02_DECISION_RECORD_v0`

Target ID:
- `TARGET-EM-EMPIRICAL-PACKET-02-DECISION-RECORD-v0`

Classification:
- `P-POLICY`

Purpose:
- Pin the first bounded non-inconclusive decision record for EM packet-02.
- Keep the decision auditable and strictly non-claim.

Non-claim boundary:
- bounded decision-record surface only.
- no external-truth adjudication claim.
- no pillar promotion by itself.

Decision bundle:
- `EM_EMPIRICAL_PACKET_02_DECISION_RECORD_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM`
- `EM_EMPIRICAL_PACKET_02_DECISION_RESULT_v0: RETAIN_v0`
- `EM_EMPIRICAL_PACKET_02_DECISION_BASIS_v0: CYCLE02_GUARD_SATISFIED_RETAIN`
- `EM_EMPIRICAL_PACKET_02_DECISION_GUARD_v0: PROTOCOL_COMPLIANT_INTERMEDIATE_TIER`

Canonical pointers:
- packet-02 target: `formal/docs/paper/DERIVATION_TARGET_EM_EMPIRICAL_COMPARISON_PACKET_02_v0.md`
- packet-02 artifact: `formal/output/em_empirical_comparison_packet_02_v0.json`
- protocol: `formal/docs/release/FOUNDATIONAL_EMPIRICAL_COMPARISON_PROTOCOL_v0.md`
- gate: `formal/python/tests/test_em_empirical_packet_02_decision_record_gate.py`
