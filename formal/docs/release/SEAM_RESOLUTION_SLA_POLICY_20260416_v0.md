# Seam Resolution SLA Policy (2026-04-16)

## Status
- ACTIVE
- Date: 2026-04-16
- Class: POLICY_NONCLAIM

## Objective
Define one canonical seam-resolution ledger that applies cadence, review ownership, and escalation timing to active seam rows using the blocker dashboard as the shared signal surface.

## Required source bundle
- `formal/docs/release/TOE_GLOBAL_COMPLETION_MATRIX_v0.md`
- `formal/output/reports/blocker_burn_dashboard_20260416_v0.json`
- `formal/docs/release/WS_10_PACKET41_PACKET42_HOLD_RECONSIDERATION_POLICY_20260408_v0.md`
- `formal/docs/release/GOVERNANCE_AUDIT_PACKET_CLOSURE_OWNER_MAP_20260410_v0.json`
- `formal/docs/paper/TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md`

## Required ledger fields
- `schema_id`
- `status`
- `captured_at_utc`
- `policy`
- `dashboard_coupling`
- `summary`
- `entries`
- `source_bundle`

## Required owner/deadline completeness fields
- `policy.decision_owner_assignment_status`
- `summary.missing_owner_rows`
- `summary.owner_completion_rate`
- `summary.missing_seam_status_rows`
- `summary.seam_status_coverage_rate`
- `entries[].seam_id`
- `entries[].seam_class`
- `entries[].governance_complete`
- `entries[].physics_complete`
- `entries[].seam_status_read`
- `entries[].seam_status_resolution`
- `entries[].primary_owner`
- `entries[].secondary_owner`
- `entries[].next_review_due_utc`
- `entries[].escalation_due_utc`
- `entries[].required_evidence_surface`
- `entries[].exit_criterion`

## Cadence and escalation
- Active seam review cadence: `24` hours
- Held seam review cadence: `168` hours
- Escalation trigger: `2` missed review windows
- Decision owner role: `WS_10_LANE_AUTHORITY_OWNER`

## Decision-state rules
- `PARITY_DRIFT` seam rows remain held until parity is restored.
- Flat blocker windows with exception requirement must surface an explicit branch-exception decision need.
- Decreasing blocker windows may be marked review-eligible for bounded continuation, but the ledger alone does not authorize continuation.
- Owner/deadline completeness is mandatory for every seam row, but owner signoff workflow remains out of scope for this tranche.
- Canonical seam-status coverage is mandatory as a reported field; missing seam semantics must be exposed as `MISSING_CANONICAL_SEAM_STATUS` rather than silently inferred.
- The seam ledger remains report-first until a later explicit enforcement upgrade is authorized.

## Unified live seam semantics
- The seam ledger is the single live seam execution surface for row cadence, ownership, and seam-status completeness reads.
- `governance_complete` and `physics_complete` are copied from canonical seam-status surfaces when pinned.
- Missing seam-status coverage must remain visible in the summary and row payload until an explicit canonical seam-status source is added.

## Authority pins
- `formal/output/reports/seam_resolution_sla_ledger_20260416_v0.json`
- `formal/python/tools/seam_resolution_sla_ledger_generate.py`
- `formal/python/tests/test_seam_resolution_sla_generate.py`
- `formal/python/tests/test_seam_resolution_sla_live_gate.py`

## Linked contradiction surface
- `formal/docs/release/SCIENCE_MATURITY_CONTRADICTION_REPORT_POLICY_20260416_v0.md`
- `formal/output/reports/science_maturity_contradiction_report_20260416_v0.json`
- `formal/python/tests/test_science_maturity_contradiction_report_live_gate.py`

## Verification entry point
- Gate: `formal/python/tests/test_seam_resolution_sla_live_gate.py`
- Tool test: `formal/python/tests/test_seam_resolution_sla_generate.py`

## Non-claim boundary
This policy governs repository-local seam review cadence and does not authorize seam continuation or global closure claims by itself.