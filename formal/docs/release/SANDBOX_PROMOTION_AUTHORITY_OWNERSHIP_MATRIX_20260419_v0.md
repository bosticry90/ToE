# Sandbox Promotion Authority Ownership Matrix 2026-04-19 v0

Spec ID:
- `SANDBOX_PROMOTION_AUTHORITY_OWNERSHIP_MATRIX_20260419_v0`

Classification:
- `P-POLICY`

Purpose:
- Make authority ownership explicit across the two-lane sandbox-promotion architecture.
- Prevent mixed authority residency between sandbox-only execution surfaces and promotion/canonical mutation surfaces.
- Provide one fail-closed matrix that the cutover gate can enforce.

Required matrix tokens:
- `SANDBOX_PROMOTION_AUTHORITY_MATRIX_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM`
- `SANDBOX_PROMOTION_AUTHORITY_CUTOVER_RULE_v0: SANDBOX_SURFACES_OWN_SANDBOX_OUTPUT_AUTHORITY_PROMOTION_SURFACES_OWN_CANONICAL_MUTATION_AUTHORITY`
- `SANDBOX_PROMOTION_AUTHORITY_FAIL_CLOSED_RULE_v0: MISSING_OWNER_OR_PARITY_OR_GATE_POINTER_BLOCKS_CUTOVER`
- `SANDBOX_PROMOTION_AUTHORITY_MATRIX_ROW_COUNT_v0: 5`
- `SANDBOX_PROMOTION_AUTHORITY_CUTOVER_GATE_v0: formal/python/tests/test_sandbox_promotion_authority_ownership_cutover_gate.py`

## Authority owner matrix

| authority_surface | canonical_owner | parity_surface | enforcement_gate |
| --- | --- | --- | --- |
| sandbox_lane_policy | formal/docs/release/SANDBOX_PHYSICS_LANE_EXECUTION_POLICY_20260418_v0.md | State_of_the_Theory.md + formal/docs/paper/PHYSICS_ROADMAP_v0.md | formal/python/tests/test_sandbox_promotion_authority_ownership_cutover_gate.py |
| promotion_lane_policy | formal/docs/release/PROMOTION_GOVERNANCE_LANE_POLICY_20260418_v0.md | State_of_the_Theory.md + formal/docs/paper/PHYSICS_ROADMAP_v0.md | formal/python/tests/test_sandbox_promotion_authority_ownership_cutover_gate.py |
| canonical_mutation_protocol | formal/docs/release/SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_20260419_v0.md | State_of_the_Theory.md + formal/docs/paper/PHYSICS_ROADMAP_v0.md | formal/python/tests/test_sandbox_promotion_authority_ownership_cutover_gate.py |
| post_pilot_decision_surface | formal/output/reports/sandbox_promotion_post_pilot_decision_cosmo_sr_cycle07_20260419_v0.json | State_of_the_Theory.md + formal/docs/paper/PHYSICS_ROADMAP_v0.md | formal/python/tests/test_sandbox_promotion_authority_ownership_cutover_gate.py |
| authority_cutover_status | State_of_the_Theory.md | formal/docs/paper/PHYSICS_ROADMAP_v0.md | formal/python/tests/test_sandbox_promotion_authority_ownership_cutover_gate.py |

Interpretation rules:
- The sandbox lane owns repository-local sandbox-output authority only.
- The promotion lane owns governed canonical mutation decision authority only.
- The canonical mutation protocol owns the exact shape of any future `promote` writeback envelope.
- The post-pilot decision surface owns widening-or-nonwidening disposition for the bounded pilot.
- The state mirror is the active checkpoint owner and the roadmap is parity-only for this matrix row.

Failure posture:
- No matrix row may assign canonical mutation authority to the sandbox lane.
- No matrix row may omit an enforcing gate pointer.
- If the state mirror and roadmap drift on any matrix-bound token, the cutover gate must fail closed.

Canonical bindings:
- formal/docs/release/SANDBOX_PHYSICS_LANE_EXECUTION_POLICY_20260418_v0.md
- formal/docs/release/PROMOTION_GOVERNANCE_LANE_POLICY_20260418_v0.md
- formal/docs/release/SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_20260419_v0.md
- formal/output/reports/sandbox_promotion_post_pilot_decision_cosmo_sr_cycle07_20260419_v0.json
- formal/python/tests/test_sandbox_promotion_authority_ownership_cutover_gate.py

Non-claim boundary:
- This matrix governs repository-local authority ownership only.
- This matrix does not by itself authorize widening, promotion, or scientific adequacy claims.