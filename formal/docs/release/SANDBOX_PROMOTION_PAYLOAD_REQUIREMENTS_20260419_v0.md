# Sandbox Promotion Payload Requirements 2026-04-19 v0

Spec ID:
- `SANDBOX_PROMOTION_PAYLOAD_REQUIREMENTS_20260419_v0`

Classification:
- `P-POLICY`

Purpose:
- Define the governed payload required before a promotion-candidate sandbox artifact may enter promotion review.
- Make promotion inputs explicit, auditable, and fail closed for one bounded pilot track before broader rollout.
- Keep promotion review subordinate to contradiction discipline, target binding, and governed test selection.

Required payload tokens:
- `SANDBOX_PROMOTION_PAYLOAD_REQUIREMENTS_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM`
- `SANDBOX_PROMOTION_PAYLOAD_REQUIRED_FIELDS_v0: ARTIFACT_POINTER_PLUS_METADATA_RECORD_PLUS_TARGET_BINDING_PLUS_CONTRADICTION_CHECK_RESULT_PLUS_GOVERNED_TEST_SELECTION_PLUS_MUTATION_PLAN_PLUS_DECISION_BOUNDARY`
- `SANDBOX_PROMOTION_PAYLOAD_ELIGIBILITY_RULE_v0: ONLY_PROMOTION_CANDIDATE_SANDBOX_ARTIFACTS_WITH_NONNONE_DELTA_CLASS_MAY_ENTER_PROMOTION_REVIEW`
- `SANDBOX_PROMOTION_PAYLOAD_DECISION_SET_v0: PROMOTE_PLUS_HOLD_PLUS_REJECT_ONLY`
- `SANDBOX_PROMOTION_PAYLOAD_FAIL_CLOSED_RULE_v0: MISSING_METADATA_OR_TARGET_BINDING_OR_CONTRADICTION_CHECK_OR_MUTATION_PLAN_IS_HARD_FAIL`
- `SANDBOX_PROMOTION_PAYLOAD_PILOT_BINDING_v0: formal/docs/release/SANDBOX_PROMOTION_BOUNDED_PILOT_BINDING_COSMO_SR_CYCLE07_20260419_v0.json`
- `SANDBOX_PROMOTION_PAYLOAD_GATE_v0: formal/python/tests/test_sandbox_promotion_phase2_phase4_contract_gate.py`

Required payload fields:
- `artifact_pointer`: sandbox artifact path.
- `metadata_record_pointer`: metadata schema-compliant record.
- `target_binding`: explicit row or seam target.
- `contradiction_check_result`: surfaced contradiction outcome against current canonical state.
- `governed_test_selection`: bounded governed test subset or full-suite rationale.
- `mutation_plan`: exact canonical surfaces that would change if promoted.
- `decision_boundary`: explicit `promote`, `hold`, or `reject` decision slot.

Pilot-track rule:
- The first bounded pilot track is `ROW-SEAM-COSMO-SR-001` / `SEAM-COSMO-SR` using Cycle07 sandbox artifacts.
- Pilot binding does not authorize promotion by itself; it only constrains what the future promotion-review wrapper must consume.

Failure posture:
- A passing sandbox gate is insufficient without a payload record.
- Missing mutation-plan detail is a hard fail for promotion review entry.
- Payload completeness does not override contradiction evidence or release-gate truth.

Canonical bindings:
- `formal/docs/release/PROMOTION_GOVERNANCE_LANE_POLICY_20260418_v0.md`
- `formal/docs/release/SANDBOX_ARTIFACT_CLASSIFICATION_METADATA_SCHEMA_20260419_v0.md`
- `formal/docs/release/SANDBOX_PROMOTION_BOUNDED_PILOT_BINDING_COSMO_SR_CYCLE07_20260419_v0.json`
- `formal/python/tests/test_sandbox_promotion_phase2_phase4_contract_gate.py`

Non-claim boundary:
- This payload contract governs repository-local promotion review entry only.
- This contract does not itself authorize promotion, writeback, or scientific closure.