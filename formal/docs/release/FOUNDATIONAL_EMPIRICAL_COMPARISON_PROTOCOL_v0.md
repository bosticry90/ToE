# Foundational Empirical Comparison Protocol v0

Spec ID:
- `FOUNDATIONAL_EMPIRICAL_COMPARISON_PROTOCOL_v0`

Classification:
- `P-POLICY`

Purpose:
- Define a bounded protocol for empirical comparison packets derived from residual-law and prediction scaffold outputs.
- Keep empirical comparison machine-checkable, auditable, and non-overclaiming.

Non-claim boundary:
- protocol/control artifact only.
- no external-truth adjudication by itself.
- no pillar promotion by itself.
- no canonical action promotion by itself.

Canonical anchors:
- `formal/docs/release/FOUNDATIONAL_DERIVATION_CHAIN_EXECUTION_PLAN_v0.md`
- `formal/docs/release/FOUNDATIONAL_PREDICTION_SCAFFOLD_PLAN_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_TOE_EMPIRICAL_COMPARISON_PACKET_01_v0.md`
- `formal/python/tests/test_toe_empirical_comparison_packet_01_gate.py`

Protocol tokens:
- `FOUNDATIONAL_EMPIRICAL_COMPARISON_PROTOCOL_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM`
- `FOUNDATIONAL_EMPIRICAL_COMPARISON_PROTOCOL_DECISION_SET_v0: RETAIN_PRUNE_INCONCLUSIVE_ONLY`
- `FOUNDATIONAL_EMPIRICAL_COMPARISON_PRUNE_GUARD_v0: NO_DIRECT_PRUNE_WITH_SCAFFOLD_UNCERTAINTY`
- `FOUNDATIONAL_EMPIRICAL_COMPARISON_PROGRESSION_MODE_v0: CYCLE_ORDERED_BOUNDED_NONCLAIM`
- `FOUNDATIONAL_EMPIRICAL_PACKET_01_BASELINE_DECISION_v0: INCONCLUSIVE_ONLY_UNTIL_PACKET02_OR_HIGHER`
- `FOUNDATIONAL_EMPIRICAL_PACKET_02_DECISION_ELIGIBILITY_v0: RETAIN_OR_PRUNE_ALLOWED_WITH_PROTOCOL_GUARDS`
- `FOUNDATIONAL_EMPIRICAL_PACKET_03_BASELINE_DECISION_v0: INCONCLUSIVE_ONLY_UNTIL_PACKET04_OR_HIGHER`
- `FOUNDATIONAL_EMPIRICAL_PACKET_04_BASELINE_DECISION_v0: INCONCLUSIVE_ONLY_UNTIL_PACKET05_OR_HIGHER`
- `FOUNDATIONAL_EMPIRICAL_COMPARISON_EVIDENCE_TIERS_v0: SCAFFOLD_INTERMEDIATE_DISCHARGE_GRADE`
- `FOUNDATIONAL_EMPIRICAL_COMPARISON_PRUNE_MIN_EVIDENCE_TIER_v0: INTERMEDIATE_v0`

Required packet chain:
1. artifact -> bridge pointer
2. bridge -> prediction pointer
3. prediction -> discriminator output
4. discriminator output -> bounded decision token

Allowed bounded decision tokens:
- `RETAIN_v0`
- `PRUNE_v0`
- `INCONCLUSIVE_v0`

Protocol constraints:
- comparison packets must declare explicit bounded validity window.
- uncertainty annotations are required.
- no hidden comparator-lane expansion.
- no decision token outside the allowed set.
- `PRUNE_v0` is disallowed when uncertainty annotation is scaffold-level.
- each packet payload must declare `evidence_tier` in `{SCAFFOLD_v0, INTERMEDIATE_v0, DISCHARGE_GRADE_v0}`.
- `PRUNE_v0` is disallowed unless `evidence_tier` is at least `INTERMEDIATE_v0`.
- cycle progression must remain explicit and bounded non-claim.
- packet-02 (or higher) may emit `RETAIN_v0` or `PRUNE_v0` only with explicit guard-satisfying eligibility payload fields.
- packet-03 baseline remains `INCONCLUSIVE_v0` across pillars until packet-04-or-higher policy transition is explicitly pinned.
- packet-04 baseline remains `INCONCLUSIVE_v0` across pillars until packet-05-or-higher policy transition is explicitly pinned.
