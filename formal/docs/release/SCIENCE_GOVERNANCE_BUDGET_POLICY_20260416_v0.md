# Science Governance Budget Policy (2026-04-16)

## Status
- ACTIVE
- Date: 2026-04-16
- Class: POLICY_NONCLAIM

## Objective
Define one canonical representative budgeting report that compares science-facing versus governance/control surface share and couples that balance to blocker-burn signals from the blocker dashboard.

## Required source bundle
- `formal/output/reports/blocker_burn_dashboard_20260416_v0.json`
- `formal/docs/paper/SCIENTIFIC_CORE_INDEX_v0.md`
- `formal/docs/release/PHYSICS_FIRST_EXECUTION_RULE_v0.md`
- `formal/docs/release/PHYS_MATH_THROUGHPUT_REMEDIATION_PROGRAM_v0.md`

## Required report fields
- `schema_id`
- `status`
- `captured_at_utc`
- `representative_surface_counts`
- `phase_target_assessment`
- `dashboard_coupling`
- `execution_boundary`
- `budget_posture`
- `source_bundle`

## Phase target bands
- `PHASE2_LANE_SPLIT`: minimum science-to-control ratio `1.0`
- `PHASE3_THEOREM_DEPTH`: minimum science-to-control ratio `1.5`
- `PHASE4_SEAM_THROUGHPUT`: minimum science-to-control ratio `1.25`
- `PHASE5_SSOT_MIGRATION`: minimum science-to-control ratio `1.0`
- `PHASE6_LIVE_AUTHORIZATION`: minimum science-to-control ratio `1.5`

## Budget rules
- The budgeting report is representative-surface based and must not create a second blocker authority.
- Dashboard movement status and exception requirement must be surfaced in the budget report.
- When blocker movement is flat or increasing, the report must state whether additional governance growth should be constrained.
- Allowed support-only work remains bounded by `PHYSICS_FIRST_EXECUTION_RULE_v0` and may not be promoted as the primary scientific lane.
- The budgeting report remains advisory until a later explicit enforcement upgrade is authorized.

## Verification entry point
- Gate: `formal/python/tests/test_science_governance_budget_live_gate.py`
- Tool test: `formal/python/tests/test_science_governance_budget_generate.py`

## Non-claim boundary
This policy governs repository-local planning balance and does not authorize scientific scope expansion or stronger claim posture by itself.