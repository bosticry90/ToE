# Sandbox Promotion Boundary Enforcement Family 2026-04-19 v0

Spec ID:
- `SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_FAMILY_20260419_v0`

Classification:
- `P-POLICY`

Purpose:
- Close the remaining boundary-enforcement family for the sandbox-first promotion-gated governance architecture.
- Make the enforcement stack explicit rather than leaving it distributed across status text alone.
- Fail closed if any required boundary surface, gate pointer, or hold/nonwidened result drifts.

Required family tokens:
- `SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_FAMILY_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM`
- `SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_SCOPE_v0: POLICY_SPLIT_PLUS_SCHEMA_PAYLOAD_PLUS_GOVERNED_AUDIT_PLUS_AUTHORITY_CUTOVER_PLUS_POST_PILOT_NONWIDENED_BOUNDARY`
- `SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_GATES_v0: LANE_POLICY_PLUS_PHASE2_PHASE4_PLUS_PHASE2_PHASE6_PLUS_AUTHORITY_CUTOVER_PLUS_PHASE7_PHASE3_PLUS_PHASE5_CLOSEOUT`
- `SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_FAIL_CLOSED_RULE_v0: ANY_MISSING_BOUNDARY_SURFACE_GATE_POINTER_OR_NONWIDENED_HOLD_DRIFT_BLOCKS_PHASE5_CLOSEOUT`
- `SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_REPORT_TOOL_v0: formal/python/tools/sandbox_promotion_boundary_enforcement_family_report.py`
- `SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_REPORT_JSON_v0: formal/output/reports/sandbox_promotion_boundary_enforcement_family_20260419_v0.json`
- `SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_CLOSEOUT_GATE_v0: formal/python/tests/test_sandbox_promotion_boundary_enforcement_family_gate.py`

## Enforcement family

- `formal/python/tests/test_sandbox_promotion_lane_policy_gate.py`
- `formal/python/tests/test_sandbox_promotion_phase2_phase4_contract_gate.py`
- `formal/python/tests/test_sandbox_promotion_governed_review_wrapper_cosmo_sr_cycle07_report.py`
- `formal/python/tests/test_sandbox_promotion_authority_ownership_cutover_gate.py`
- `formal/python/tests/test_sandbox_promotion_post_pilot_decision_phase3_followthrough_gate.py`
- `formal/python/tests/test_sandbox_promotion_boundary_enforcement_family_gate.py`

## Boundary family rules

- Sandbox outputs remain sandbox-only unless the promotion lane produces a governed `promote` decision.
- Promotion review remains fail-closed on missing provenance, contradiction evidence, or target binding.
- Hold or reject outcomes emit no canonical mutation.
- The bounded pilot remains nonwidened after the governed hold outcome unless a later explicit tranche says otherwise.
- Mixed authority residency between sandbox-only and canonical mutation surfaces remains blocked by the cutover gate.

## Cross-pinned surfaces

- `formal/docs/release/SANDBOX_PHYSICS_LANE_EXECUTION_POLICY_20260418_v0.md`
- `formal/docs/release/PROMOTION_GOVERNANCE_LANE_POLICY_20260418_v0.md`
- `formal/docs/release/SANDBOX_PROMOTION_PAYLOAD_REQUIREMENTS_20260419_v0.md`
- `formal/docs/release/SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_20260419_v0.md`
- `formal/docs/release/SANDBOX_PROMOTION_AUTHORITY_OWNERSHIP_MATRIX_20260419_v0.md`
- `formal/output/reports/sandbox_promotion_governed_review_wrapper_cosmo_sr_cycle07_20260419_v0.json`
- `formal/output/reports/sandbox_promotion_post_pilot_decision_cosmo_sr_cycle07_20260419_v0.json`

Non-claim boundary:
- This family governs repository-local enforcement surfaces only.
- This family does not itself widen the pilot, promote a canonical mutation, or assert scientific truth.