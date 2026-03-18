# Deprecated Gate Retirement Policy v0

Spec ID:
- DEPRECATED_GATE_RETIREMENT_POLICY_v0

Classification:
- P-POLICY

Status:
- ACTIVE

Purpose:
- Define a bounded, auditable lifecycle for governance and gate surfaces that are no longer default execution paths.
- Prevent silent removal or indefinite zombie retention of deprecated gates.

Non-claim boundary:
- control artifact only.
- no theorem promotion.
- no status promotion.

## Scope

This policy applies to governance and gate artifacts in release and test control surfaces when a newer canonical path supersedes prior behavior.

## Disposition States

- CANDIDATE: identified for possible retirement, still in default review scope.
- DEPRECATED: superseded and non-default for routine runs, retained for traceability.
- RETIRED: removed from active governance execution path with archival/reference disposition recorded.

## Required Fields Per Retirement Record

- retirement_id
- surface_or_family
- disposition_state
- superseded_by
- rationale
- owner
- date_marked
- evidence_link
- reactivation_condition
- notes

## Lifecycle Rules

1. Entry rule:
   - A surface enters CANDIDATE only with an explicit superseding path and bounded rationale.
2. Deprecation rule:
   - Transition to DEPRECATED requires evidence that the superseding path is active and reviewable.
3. Retirement rule:
   - Transition to RETIRED requires a documented archival or removal decision and no active dependency blockers.
4. Reactivation rule:
   - Any reactivation must satisfy the recorded reactivation condition and add fresh evidence.
5. Traceability rule:
   - Every state transition is evidence-linked and date-stamped; no silent transitions are allowed.

## Review Cadence

- Baseline cadence: once per major release-note cycle.
- Escalation cadence: immediate review when a deprecated surface appears in an active blocking path.
- Audit cadence: verify that DEPRECATED and RETIRED entries still reference valid superseding surfaces.

## Integration Contract

- This policy is executed under WS-08 governance right-sizing and tracked in the master remediation tracker.
- Quarantine and retirement policies are complementary: quarantine controls non-default review status; retirement controls supersession lifecycle.
