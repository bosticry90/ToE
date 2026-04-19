# Sandbox Promotion Canonical Mutation Protocol 2026-04-19 v0

Spec ID:
- `SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_20260419_v0`

Classification:
- `P-POLICY`

Purpose:
- Define the exact mutation envelope that a governed sandbox-promotion `promote` decision must emit.
- Keep `hold` and `reject` as explicit no-mutation outcomes.
- Fail closed before any canonical row or seam state change can be described as authorized.

Required protocol tokens:
- `SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM`
- `SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_EMISSION_RULE_v0: EMIT_ONLY_ON_GOVERNED_PROMOTION_REVIEW_PROMOTE_DECISION`
- `SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_REQUIRED_FIELDS_v0: TARGET_ROW_PLUS_TARGET_SEAM_PLUS_SOURCE_ARTIFACT_PLUS_SOURCE_PAYLOAD_PLUS_DECISION_RECORD_PLUS_SURFACE_DELTA_PLUS_PRESTATE_PLUS_POSTSTATE_PLUS_ROLLBACK_ANCHOR_PLUS_NONCLAIM_BOUNDARY`
- `SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_NOOP_RULE_v0: HOLD_OR_REJECT_DECISION_EMITS_NO_CANONICAL_MUTATION`
- `SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_FAIL_CLOSED_RULE_v0: MISSING_SURFACE_DELTA_OR_PREPOST_STATE_OR_ROLLBACK_ANCHOR_BLOCKS_PROMOTE`
- `SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_PILOT_SCOPE_v0: ONE_ROW_SEAM_COSMO_SR_CYCLE07_ONLY_UNTIL_WIDER_AUTHORIZATION`
- `SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_GATE_v0: formal/python/tests/test_sandbox_promotion_governed_review_wrapper_cosmo_sr_cycle07_report.py`

Required mutation fields:
- `target_row`: canonical row to mutate.
- `target_seam`: canonical seam to mutate.
- `source_artifact`: sandbox artifact under review.
- `source_payload`: governed payload record that entered review.
- `decision_record`: explicit `promote`, `hold`, or `reject` decision and rationale.
- `surface_delta`: exact canonical files and tokens that would change on promote.
- `prestate`: current canonical posture before mutation.
- `poststate`: expected canonical posture after mutation.
- `rollback_anchor`: explicit anchor for reverting or auditing the emitted promote instruction.
- `nonclaim_boundary`: non-claim statement attached to the mutation envelope.

Pilot mutation envelope:
- The first bounded pilot may only target `ROW-SEAM-COSMO-SR-001` and `SEAM-COSMO-SR`.
- Candidate canonical surfaces for a future promote are limited to:
  - `State_of_the_Theory.md`
  - `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
  - `formal/docs/release/TOE_GLOBAL_COMPLETION_MATRIX_v0.md`
- No other canonical mutation surface may be implied during the bounded pilot.

Failure posture:
- A governed `hold` decision must preserve the current canonical state unchanged.
- A governed `reject` decision must preserve the current canonical state unchanged.
- A promote instruction without a surface delta, prestate, poststate, and rollback anchor is invalid.

Canonical bindings:
- `formal/docs/release/PROMOTION_GOVERNANCE_LANE_POLICY_20260418_v0.md`
- `formal/docs/release/SANDBOX_PROMOTION_PAYLOAD_REQUIREMENTS_20260419_v0.md`
- `formal/docs/release/SANDBOX_PROMOTION_GOVERNED_REVIEW_WRAPPER_COSMO_SR_CYCLE07_20260419_v0.json`
- `formal/docs/release/TOE_CANONICAL_ACTION_PROMOTION_STANDARD_v0.md`
- `formal/python/tests/test_sandbox_promotion_governed_review_wrapper_cosmo_sr_cycle07_report.py`

Non-claim boundary:
- This protocol defines repository-local mutation discipline only.
- This protocol does not itself authorize canonical promotion, scientific adequacy, or external truth claims.