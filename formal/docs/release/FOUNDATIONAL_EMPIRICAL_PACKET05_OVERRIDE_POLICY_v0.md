# Foundational Empirical Packet-05 Override Policy v0

Spec ID:
- `FOUNDATIONAL_EMPIRICAL_PACKET05_OVERRIDE_POLICY_v0`

Classification:
- `P-POLICY`

Purpose:
- Define lane-specific override criteria that allow packet-05 to move beyond inconclusive baseline decisions.
- Keep override decisions bounded, auditable, and coupled to discriminator and falsification surfaces.

Non-claim boundary:
- override-policy surface only.
- no external-truth adjudication by itself.
- no pillar promotion by itself.

Canonical anchors:
- `formal/docs/release/FOUNDATIONAL_EMPIRICAL_PACKET05_PROGRESSION_POLICY_v0.md`
- `formal/docs/paper/FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET05_MATRIX_v0.json`
- `formal/output/empirical_packet05_decision_ledger_v0.json`
- `formal/python/tests/test_foundational_empirical_packet05_override_policy_gate.py`

Override policy tokens:
- `FOUNDATIONAL_EMPIRICAL_PACKET_05_OVERRIDE_MODE_v0: GR_SR_ACTIVE_OVERRIDE_CRITERIA_PINNED`
- `FOUNDATIONAL_EMPIRICAL_PACKET_05_OVERRIDE_ALLOWED_DECISIONS_v0: RETAIN_OR_PRUNE_WITH_EXPLICIT_CRITERIA`
- `FOUNDATIONAL_EMPIRICAL_PACKET_05_OVERRIDE_MIN_REQUIREMENTS_v0: PACKET04_INTERMEDIATE_PLUS_DISCRIMINATOR_PLUS_FALSIFICATION_SURFACE`

Cycle01 override activation:
- enabled lanes: `GR`, `SR`.
- current lane-specific decisions are allowed to be non-inconclusive only when the per-lane override criteria surface is pinned and satisfied.