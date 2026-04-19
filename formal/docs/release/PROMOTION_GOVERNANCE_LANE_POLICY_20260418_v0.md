# Promotion Governance Lane Policy 2026-04-18 v0

Spec ID:
- `PROMOTION_GOVERNANCE_LANE_POLICY_20260418_v0`

Classification:
- `P-POLICY`

Purpose:
- Concentrate heavyweight governance at explicit promotion boundaries.
- Require a governed review before any sandbox artifact may alter canonical state.
- Preserve fail-closed authority, provenance, and contradiction discipline.

Required policy tokens:
- `PROMOTION_GOVERNANCE_LANE_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM`
- `PROMOTION_GOVERNANCE_LANE_TRIGGER_v0: PROMOTABLE_SANDBOX_ARTIFACT_ONLY`
- `PROMOTION_GOVERNANCE_LANE_REQUIRED_INPUTS_v0: PROVENANCE_PLUS_SCOPE_PLUS_CONTRADICTION_CHECK_PLUS_TARGET_ROW_BINDING_PLUS_GOVERNED_TEST_SELECTION`
- `PROMOTION_GOVERNANCE_LANE_PAYLOAD_SCHEMA_v0: formal/docs/release/SANDBOX_PROMOTION_PAYLOAD_REQUIREMENTS_20260419_v0.md`
- `PROMOTION_GOVERNANCE_LANE_PILOT_BINDING_v0: formal/docs/release/SANDBOX_PROMOTION_BOUNDED_PILOT_BINDING_COSMO_SR_CYCLE07_20260419_v0.json`
- `PROMOTION_GOVERNANCE_LANE_REVIEW_WRAPPER_v0: formal/docs/release/SANDBOX_PROMOTION_GOVERNED_REVIEW_WRAPPER_COSMO_SR_CYCLE07_20260419_v0.json`
- `PROMOTION_GOVERNANCE_LANE_MUTATION_PROTOCOL_v0: formal/docs/release/SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_20260419_v0.md`
- `PROMOTION_GOVERNANCE_LANE_AUTHORITY_OWNER_v0: formal/docs/release/PROMOTION_GOVERNANCE_LANE_POLICY_20260418_v0.md`
- `PROMOTION_GOVERNANCE_LANE_AUTHORITY_MATRIX_v0: formal/docs/release/SANDBOX_PROMOTION_AUTHORITY_OWNERSHIP_MATRIX_20260419_v0.md`
- `PROMOTION_GOVERNANCE_LANE_CUTOVER_GATE_v0: formal/python/tests/test_sandbox_promotion_authority_ownership_cutover_gate.py`
- `PROMOTION_GOVERNANCE_LANE_BOUNDARY_ENFORCEMENT_FAMILY_v0: formal/docs/release/SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_FAMILY_20260419_v0.md`
- `PROMOTION_GOVERNANCE_LANE_BOUNDARY_ENFORCEMENT_CLOSEOUT_GATE_v0: formal/python/tests/test_sandbox_promotion_boundary_enforcement_family_gate.py`
- `PROMOTION_GOVERNANCE_LANE_HARD_BOUNDARY_v0: NO_CANONICAL_PROMOTION_WITHOUT_PROMOTION_REVIEW`
- `PROMOTION_GOVERNANCE_LANE_PROMOTION_RULE_v0: CANONICAL_ROW_AND_SEAM_STATE_CHANGE_ONLY_AFTER_GOVERNED_PROMOTION_PASS`
- `PROMOTION_GOVERNANCE_LANE_FAILURE_RULE_v0: FAIL_CLOSED_ON_MISSING_PROVENANCE_SCOPE_OR_CONTRADICTION_EVIDENCE`
- `PROMOTION_GOVERNANCE_LANE_PHYSICS_FIRST_RULE_v0: SUPPORT_ONLY_SANDBOX_OUTPUTS_CANNOT_BECOME_ACTIVE_SCIENTIFIC_TRANCHE_WITHOUT_DELTA_CLASS`
- `PROMOTION_GOVERNANCE_LANE_GATE_v0: formal/python/tests/test_sandbox_promotion_lane_policy_gate.py`

Required review payload:
- Provenance pointer for the sandbox artifact family.
- Declared scope and non-claim boundary.
- Contradiction check outcome against the active row or seam truth surfaces.
- Explicit target-row or target-seam binding.
- Governed test subset or full-suite selection rationale.
- Mutation plan aligned to `formal/docs/release/SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_20260419_v0.md`.

Promotion outcomes:
- `promote` only when the governed review passes and the resulting canonical mutation is explicitly declared.
- `hold` when evidence is incomplete, contradictory, or mis-scoped.
- `reject` when the artifact is support-only, non-provenanced, or attempts to bypass authority surfaces.

Failure posture:
- Missing provenance, missing contradiction evidence, or missing target binding is a hard fail.
- A passing sandbox result is not self-promoting.
- Promotion governance remains subordinate to release-gate truth and existing branch-health rules.

Canonical bindings:
- `formal/docs/release/PHYSICS_FIRST_EXECUTION_RULE_v0.md`
- `formal/docs/release/SANDBOX_PHYSICS_LANE_EXECUTION_POLICY_20260418_v0.md`
- `formal/docs/release/SANDBOX_PROMOTION_PAYLOAD_REQUIREMENTS_20260419_v0.md`
- `formal/docs/release/SANDBOX_PROMOTION_BOUNDED_PILOT_BINDING_COSMO_SR_CYCLE07_20260419_v0.json`
- `formal/docs/release/SANDBOX_PROMOTION_GOVERNED_REVIEW_WRAPPER_COSMO_SR_CYCLE07_20260419_v0.json`
- `formal/docs/release/SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_20260419_v0.md`
- `formal/docs/release/SANDBOX_PROMOTION_AUTHORITY_OWNERSHIP_MATRIX_20260419_v0.md`
- `formal/docs/release/SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_FAMILY_20260419_v0.md`
- `formal/python/tests/test_sandbox_promotion_authority_ownership_cutover_gate.py`
- `formal/python/tests/test_sandbox_promotion_boundary_enforcement_family_gate.py`
- `formal/python/tests/test_sandbox_promotion_lane_policy_gate.py`

Non-claim boundary:
- This policy governs promotion review only.
- This policy does not itself assert scientific adequacy, external truth, or automatic row closure.