# Sandbox Physics Lane Execution Policy 2026-04-18 v0

Spec ID:
- `SANDBOX_PHYSICS_LANE_EXECUTION_POLICY_20260418_v0`

Classification:
- `P-POLICY`

Purpose:
- Permit lightweight physics exploration under bounded non-claim conditions.
- Keep exploratory work moving without forcing full governance overhead on every intermediate artifact.
- Preserve hard promotion boundaries so sandbox work cannot silently become canonical truth.

Required policy tokens:
- `SANDBOX_PHYSICS_LANE_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM`
- `SANDBOX_PHYSICS_LANE_MODE_v0: EXPLORATION_ONLY_WITH_MINIMAL_LIVE_GUARDRAILS`
- `SANDBOX_PHYSICS_LANE_ALLOWED_OUTPUTS_v0: HYPOTHESIS_LOCAL_DERIVATION_RETAIN_PRUNE_INCONCLUSIVE_AND_DESIGN_ONLY`
- `SANDBOX_PHYSICS_LANE_FORBIDDEN_OUTPUTS_v0: NO_CANONICAL_ROW_MUTATION_NO_RELEASE_GATE_TRUTH_CHANGE_NO_SEAM_CLASS_FLIP_NO_EXTERNAL_TRUTH_CLAIM`
- `SANDBOX_PHYSICS_LANE_LIVE_GUARDRAILS_v0: NONCLAIM_PLUS_PROVENANCE_PLUS_FAIL_CLOSED_CONTRADICTION_PLUS_DECLARED_SCOPE`
- `SANDBOX_PHYSICS_LANE_PHYSICS_FIRST_RULE_v0: DECLARE_SCIENTIFIC_DELTA_CLASS_OR_REMAIN_SUPPORT_ONLY_NONPROMOTABLE`
- `SANDBOX_PHYSICS_LANE_METADATA_SCHEMA_v0: formal/docs/release/SANDBOX_ARTIFACT_CLASSIFICATION_METADATA_SCHEMA_20260419_v0.md`
- `SANDBOX_PHYSICS_LANE_AUTHORITY_OWNER_v0: formal/docs/release/SANDBOX_PHYSICS_LANE_EXECUTION_POLICY_20260418_v0.md`
- `SANDBOX_PHYSICS_LANE_AUTHORITY_MATRIX_v0: formal/docs/release/SANDBOX_PROMOTION_AUTHORITY_OWNERSHIP_MATRIX_20260419_v0.md`
- `SANDBOX_PHYSICS_LANE_BOUNDARY_ENFORCEMENT_FAMILY_v0: formal/docs/release/SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_FAMILY_20260419_v0.md`
- `SANDBOX_PHYSICS_LANE_BOUNDARY_v0: RESULTS_STAY_SANDBOX_ONLY_UNTIL_PROMOTION_GATE_SATISFIED`
- `SANDBOX_PHYSICS_LANE_GATE_v0: formal/python/tests/test_sandbox_promotion_lane_policy_gate.py`

Allowed actions:
- Run bounded derivation attempts, local consistency checks, and targeted seam or pillar exploration.
- Emit repository-local `retain`, `prune`, `inconclusive`, and design-only outputs.
- Prepare promotable artifacts with explicit provenance, target-row binding, and contradiction context.

Disallowed actions:
- Mutate canonical row truth directly from sandbox output.
- Reclassify seam status, pillar status, or release-gate truth from sandbox output alone.
- Treat exploratory notes as canonical authority surfaces.
- Claim scientific adequacy or external truth.

Physics-first binding:
- Sandbox work may carry a scientific delta class when it directly advances an active closure path.
- If no scientific delta class is declared, sandbox work is support-only and remains non-promotable by default.
- This lane does not weaken `PHYSICS_FIRST_EXECUTION_RULE_v0`.

Canonical bindings:
- `formal/docs/release/PHYSICS_FIRST_EXECUTION_RULE_v0.md`
- `formal/docs/release/SANDBOX_ARTIFACT_CLASSIFICATION_METADATA_SCHEMA_20260419_v0.md`
- `formal/docs/release/SANDBOX_PROMOTION_AUTHORITY_OWNERSHIP_MATRIX_20260419_v0.md`
- `formal/docs/release/SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_FAMILY_20260419_v0.md`
- `formal/docs/release/PROMOTION_GOVERNANCE_LANE_POLICY_20260418_v0.md`
- `formal/python/tests/test_sandbox_promotion_lane_policy_gate.py`

Non-claim boundary:
- This policy authorizes bounded sandbox exploration only.
- This policy does not authorize canonical promotion, release-gate truth changes, or external scientific claims.