# Derivation Target: SR Empirical Packet 01 Evidence Promotion v0

Spec ID:
- `DERIVATION_TARGET_SR_EMPIRICAL_PACKET_01_EVIDENCE_PROMOTION_v0`

Target ID:
- `TARGET-SR-EMPIRICAL-PACKET-01-EVIDENCE-PROMOTION-v0`

Classification:
- `P-POLICY`

Purpose:
- Define a controlled, bounded transition lane from `SCAFFOLD_v0` to `INTERMEDIATE_v0` evidence tier for `SR_EMPIRICAL_PACKET_01`.
- Keep promotion criteria explicit, machine-checkable, and non-claim.

Non-claim boundary:
- bounded transition-control surface only.
- no direct `PRUNE_v0` authorization by itself.
- no external-truth claim.

Promotion lane tokens:
- `SR_EMPIRICAL_PACKET_01_EVIDENCE_PROMOTION_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM`
- `SR_EMPIRICAL_PACKET_01_EVIDENCE_PROMOTION_TARGET_TIER_v0: INTERMEDIATE_v0`
- `SR_EMPIRICAL_PACKET_01_EVIDENCE_PROMOTION_GATE_v0: CRITERIA_AND_POINTERS_REQUIRED`
- `SR_EMPIRICAL_PACKET_01_EVIDENCE_PROMOTION_CRITERIA_v0: CYCLE01_CRITERIA_PINNED`

Criteria bundle (all required):
1. `SR_EMPIRICAL_PACKET_01_CRITERION_RESIDUAL_OBSERVABLE_LINK_v0: SATISFIED_v0`
2. `SR_EMPIRICAL_PACKET_01_CRITERION_COMPARATOR_MAPPING_PIN_v0: SATISFIED_v0`
3. `SR_EMPIRICAL_PACKET_01_CRITERION_UNCERTAINTY_BUDGET_BOUNDED_v0: SATISFIED_v0`

Canonical pointers:
- `formal/docs/paper/DERIVATION_TARGET_SR_EMPIRICAL_COMPARISON_PACKET_01_v0.md`
- `formal/docs/release/FOUNDATIONAL_EMPIRICAL_COMPARISON_PROTOCOL_v0.md`
- `formal/python/tests/test_sr_empirical_packet_01_evidence_promotion_gate.py`
