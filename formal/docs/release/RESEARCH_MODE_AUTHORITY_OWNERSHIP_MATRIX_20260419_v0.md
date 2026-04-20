# Research Mode Authority Ownership Matrix 2026-04-19 v0

Spec ID:
- `RESEARCH_MODE_AUTHORITY_OWNERSHIP_MATRIX_20260419_v0`

Classification:
- `P-POLICY`

Purpose:
- Make authority ownership explicit across the four-stage research ladder.
- Prevent research-mode outputs from silently assuming sandbox, promotion, or canonical authority.
- Provide one fail-closed matrix that the research-mode gate can enforce.

Required matrix tokens:
- `RESEARCH_MODE_AUTHORITY_MATRIX_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM`
- `RESEARCH_MODE_AUTHORITY_LADDER_v0: RESEARCH_MODE_TO_SANDBOX_TO_PROMOTION_GOVERNANCE_TO_CANONICAL`
- `RESEARCH_MODE_AUTHORITY_FAIL_CLOSED_RULE_v0: MISSING_OWNER_OR_PARITY_OR_GATE_POINTER_BLOCKS_ESCALATION`
- `RESEARCH_MODE_AUTHORITY_MATRIX_ROW_COUNT_v0: 4`
- `RESEARCH_MODE_AUTHORITY_GATE_v0: formal/python/tests/test_research_mode_lane_policy_gate.py`

## Authority owner matrix

| authority_surface | canonical_owner | parity_surface | enforcement_gate |
| --- | --- | --- | --- |
| research_mode_policy | formal/docs/release/RESEARCH_MODE_EXECUTION_POLICY_20260419_v0.md | State_of_the_Theory.md + formal/docs/paper/PHYSICS_ROADMAP_v0.md | formal/python/tests/test_research_mode_lane_policy_gate.py |
| research_artifact_schema | formal/docs/release/RESEARCH_ARTIFACT_CLASSIFICATION_METADATA_SCHEMA_20260419_v0.md | State_of_the_Theory.md + formal/docs/paper/PHYSICS_ROADMAP_v0.md | formal/python/tests/test_research_mode_metadata_schema_gate.py |
| research_retention_policy | formal/docs/release/RESEARCH_ARTIFACT_RETENTION_POLICY_20260419_v0.md | State_of_the_Theory.md + formal/docs/paper/PHYSICS_ROADMAP_v0.md | formal/python/tests/test_research_mode_lane_policy_gate.py |
| promotion_boundary_binding | formal/docs/release/PROMOTION_GOVERNANCE_LANE_POLICY_20260418_v0.md | State_of_the_Theory.md + formal/docs/paper/PHYSICS_ROADMAP_v0.md | formal/python/tests/test_research_mode_lane_policy_gate.py |

Interpretation rules:
- Research mode owns repository-local discovery authority only.
- Sandbox owns the first promotable staging authority only.
- Promotion governance owns canonical mutation decision authority only.
- Canonical mirrors remain the checkpoint owners after a governed promotion pass.

Failure posture:
- No matrix row may assign canonical mutation authority to research mode.
- No matrix row may omit an enforcing gate pointer.
- If state and roadmap drift on any research-mode matrix-bound token, the gate must fail closed.

Canonical bindings:
- `formal/docs/release/RESEARCH_MODE_EXECUTION_POLICY_20260419_v0.md`
- `formal/docs/release/RESEARCH_ARTIFACT_CLASSIFICATION_METADATA_SCHEMA_20260419_v0.md`
- `formal/docs/release/RESEARCH_ARTIFACT_RETENTION_POLICY_20260419_v0.md`
- `formal/docs/release/PROMOTION_GOVERNANCE_LANE_POLICY_20260418_v0.md`
- `formal/python/tests/test_research_mode_lane_policy_gate.py`

Non-claim boundary:
- This matrix governs repository-local authority ownership only.
- This matrix does not by itself authorize promotion, canonical mutation, or scientific adequacy claims.