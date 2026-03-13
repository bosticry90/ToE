# Derivation Target: GR Empirical Packet 05 Decision Record v0

Spec ID:
- `DERIVATION_TARGET_GR_EMPIRICAL_PACKET_05_DECISION_RECORD_v0`

Classification:
- `P-POLICY`

Purpose:
- Record the explicit bounded decision state for the GR packet-05 lane.
- Make the packet-05 decision basis auditable under override-mode non-inconclusive decisions.

Non-claim boundary:
- decision-record surface only.
- no external-truth claim.
- no pillar promotion.

Decision record bundle:
- `GR_EMPIRICAL_PACKET_05_DECISION_RECORD_STATUS_v0: RECORDED_v0_NONCLAIM`
- `GR_EMPIRICAL_PACKET_05_DECISION_BASIS_v0: PACKET04_INCONCLUSIVE_INTERMEDIATE_BASELINE_PRESERVED`
- `GR_EMPIRICAL_PACKET_05_DECISION_RESULT_v0: RETAIN_v0`
- `GR_EMPIRICAL_PACKET_05_DECISION_GUARD_v0: PROTOCOL_COMPLIANT_INTERMEDIATE_TIER_OVERRIDE`