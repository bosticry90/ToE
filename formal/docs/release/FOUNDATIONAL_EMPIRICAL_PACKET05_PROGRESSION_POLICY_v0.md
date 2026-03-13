# Foundational Empirical Packet-05 Progression Policy v0

Spec ID:
- `FOUNDATIONAL_EMPIRICAL_PACKET05_PROGRESSION_POLICY_v0`

Classification:
- `P-POLICY`

Purpose:
- Define bounded lane-eligibility rules for packet-05 expansion beyond the packet-04 baseline.
- Enable selective lane rollout while preserving complete-v1 terminal posture and non-claim semantics.

Non-claim boundary:
- policy/control surface only.
- no adjudication promotion by itself.
- no matrix-status promotion by itself.

Canonical anchors:
- `formal/docs/release/FOUNDATIONAL_EMPIRICAL_COMPARISON_PROTOCOL_v0.md`
- `formal/docs/paper/FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET04_MATRIX_v0.json`
- `formal/docs/paper/FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET05_MATRIX_v0.json`

Packet-05 progression tokens:
- `FOUNDATIONAL_EMPIRICAL_PACKET_05_ENABLEMENT_v0: SELECTIVE_LANE_ENABLEMENT_ALLOWED_WITH_PACKET04_INCONCLUSIVE_AND_INTERMEDIATE_EVIDENCE`
- `FOUNDATIONAL_EMPIRICAL_PACKET_05_ALLOWED_LANE_BOOTSTRAP_v0: GR_SR_CYCLE01`
- `FOUNDATIONAL_EMPIRICAL_PACKET_05_DECISION_BASELINE_v0: INCONCLUSIVE_ONLY_UNTIL_LANE_SPECIFIC_ELIGIBILITY_OVERRIDE`
- `FOUNDATIONAL_EMPIRICAL_PACKET_05_OVERRIDE_MODE_v0: GR_SR_ACTIVE_OVERRIDE_CRITERIA_PINNED`

Eligibility contract for packet-05 lane admission:
1. packet-04 artifact exists for the same lane.
2. packet-04 decision is `INCONCLUSIVE_v0`.
3. packet-04 evidence tier is `INTERMEDIATE_v0` or higher.
4. packet-05 target doc, artifact, and gate pointers are pinned on state and roadmap surfaces.

Cycle01 selective rollout:
- enabled lanes: `GR`, `SR`.
- non-enabled lanes remain governed by packet-04 baseline policy.

Guardrail:
- packet-05 baseline for enabled lanes remains `INCONCLUSIVE_v0` until a lane-specific override tranche is pinned.
- once the override tranche is pinned, the lane-specific decision may be non-inconclusive if the override criteria surface is satisfied.
