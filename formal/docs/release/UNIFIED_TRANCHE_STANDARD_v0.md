# UNIFIED_TRANCHE_STANDARD_v0

## Status
- ACTIVE
- Date: 2026-03-26
- Classification: P-POLICY

## Objective
Define one standard tranche contract for active execution so all lane work uses the same lifecycle shape, required fields, and validation semantics.

## Scope
In scope:
- one tranche schema for kickoff, increment, synthesis, and decision.
- required metadata fields for scientific deltas, boundaries, and evidence.
- compatibility mapping for existing WS/T-cycle tasks.

Out of scope:
- release-gate truth changes.
- non-claim boundary relaxation.
- packet hold release or scalar freeze release.

## Tranche Modes
Allowed `mode` values:
1. `kickoff`
2. `increment`
3. `synthesis`
4. `decision`

No additional modes are authorized unless this standard is version-bumped.

## Required Fields
Every tranche record must include:
- `id`
- `lane`
- `mode`
- `scientific_delta_class`
- `scientific_delta_summary`
- `target_blocker_state_change`
- `actual_blocker_state_change`
- `progress_classification`
- `predecessor`
- `stop_condition`
- `non_claim_boundary`
- `evidence_artifact`
- `gate_test`
- `status_transition`

## Scientific Delta Classes
Allowed `scientific_delta_class` values:
- `math_strengthening`
- `physics_compatibility`
- `blocker_discharge`
- `assumption_narrowing`
- `prediction_or_exclusion`

`support_only` is not an active scientific delta class and cannot be used for active lane progression.

## Status Transition Semantics
Required transition fields:
- `from`
- `to`
- `decision_basis`

Allowed transition posture values:
- `ACTIVE`
- `STOPPED_AT_SYNTHESIS_BOUNDARY`
- `PENDING_BRANCH_DECISION`
- `CLOSED_AUTHORIZED`
- `DONE`
- `PAUSED`

## Progress Classification Semantics
Allowed `progress_classification` values:
- `PROGRESS`
- `MAINTENANCE`
- `REWORK_ROUTED`

Classification rule:
- `PROGRESS` requires blocker-state movement evidence in `actual_blocker_state_change`.
- `MAINTENANCE` is valid when governance/control work is complete without blocker movement.
- `REWORK_ROUTED` is required when branch policy routes to theorem-gap or blocker-facing rework.

## Compatibility Rule
Existing WS/T-cycle artifacts remain valid while migration is in progress, but any newly opened tranche must be represented as a Unified Tranche record.

## Enforcement Rule
A tranche is execution-eligible only if:
- its mode is one of the four allowed values,
- all required fields are present,
- `scientific_delta_class` is one of the allowed scientific classes,
- `target_blocker_state_change` and `actual_blocker_state_change` are explicit,
- `progress_classification` is one of `PROGRESS`, `MAINTENANCE`, or `REWORK_ROUTED`,
- `gate_test` and `evidence_artifact` paths exist,
- `non_claim_boundary` is explicit.

## Verification Entry Point
- Gate: `formal/python/tests/test_state_core_schema_v0_gate.py`
- Source schema: `formal/docs/release/STATE_CORE_SCHEMA_v0.json`
- Source instance: `formal/docs/release/state_core_v0.json`
