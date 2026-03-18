# WS_08_GOVERNANCE_RIGHT_SIZING_PLAN_v0

## Workstream
- ID: WS-08
- Name: Governance Right-Sizing
- Status: ACTIVE
- Priority: PRIMARY

## Objective
Preserve rigor while reducing governance ceremony and long-tail maintenance burden to satisfy CE-04 through CE-06 without reopening theorem-route expansion.

## Scope
In scope:
- define active quarantine operation policy and review cadence.
- define deprecated gate retirement policy with explicit disposition controls.
- identify bounded governance suite selection simplification opportunities.

Out of scope during WS-08:
- theorem-route expansion.
- new packet family introduction.
- broad refactors outside governance right-sizing deliverables.

## Baseline Snapshot (WS-08-T01)
- Existing quarantine authority: `formal/docs/release/QUARANTINE_REGISTER_v0.md`.
- Existing phase charter target for WS-08 deliverables: `formal/docs/release/ARCHITECTURE_CONSOLIDATION_PHASE_v0.md`.
- No dedicated WS-08 execution plan existed prior to this file.
- No dedicated release-surface deprecated gate retirement policy artifact exists yet.

## Task Plan
| ID | Task | Status | Blocked By | Deliverable | Evidence Required |
| --- | --- | --- | --- | --- | --- |
| WS-08-T01 | Define refresh scope and baseline snapshot | DONE | none | WS-08 plan baseline and bounded deliverable contract | Plan file + tracker linkage |
| WS-08-T02 | Draft active quarantine operation policy and review cadence | DONE | WS-08-T01 | Quarantine operation policy section or artifact with cadence controls | Bounded policy text + tracker evidence row |
| WS-08-T03 | Draft deprecated gate retirement policy | DONE | WS-08-T02 | Deprecated gate retirement policy artifact with disposition states | Policy artifact + tracker evidence |
| WS-08-T04 | Identify and record governance suite simplification candidates | ACTIVE | WS-08-T03 | Candidate list with bounded adoption criteria | Candidate matrix + tracker evidence |
| WS-08-T05 | Record WS-08 completion checkpoint | TODO | WS-08-T04 | WS-08 closure row in tracker | Closure row with evidence chain |

## Active Quarantine Operation Policy (WS-08-T02)
This policy governs how quarantine rows are added, reviewed, and transitioned while preserving bounded-slice rigor.

### Operating Rules
1. Admission gate:
	- Any new quarantine row must include: measurable re-entry condition, explicit owner, and bounded reason tied to maintenance burden or review-surface control.
2. Status vocabulary:
	- Allowed lifecycle states are `ACTIVE` and `RETIRED` only; quarantine never implies theorem promotion or deletion by default.
3. Review contract:
	- Each active quarantine row must be re-reviewed at the cadence defined below and annotated in the row notes when disposition remains unchanged.
4. Re-entry trigger:
	- A row may transition from `ACTIVE` to `RETIRED` only when its measurable re-entry condition is satisfied with linked evidence.
5. Non-bypass constraint:
	- Quarantined surfaces remain auditable dependencies and may not be silently ignored in release/governance summaries.

### Review Cadence
- Baseline cadence: once per major release-note cycle.
- Escalation cadence: immediate review when a quarantined family blocks an active consolidation task.
- Evidence cadence: each review outcome records date and disposition summary in the corresponding quarantine row notes.

### Evidence Surfaces
- Primary register: `formal/docs/release/QUARANTINE_REGISTER_v0.md`.
- Workstream execution log: this WS-08 plan evidence log and tracker completed-task row.

## Evidence Log
- 2026-03-18 WS-08-T01: Created WS-08 workstream plan, pinned baseline references, and linked tracker activation to this plan.
- 2026-03-18 WS-08-T02: Added explicit quarantine operation policy and review cadence section in this plan, anchored to `formal/docs/release/QUARANTINE_REGISTER_v0.md` maintenance rules and lifecycle controls.
- 2026-03-18 WS-08-T03: Added deprecated gate retirement policy artifact `formal/docs/release/DEPRECATED_GATE_RETIREMENT_POLICY_v0.md` with explicit disposition states, lifecycle rules, and review cadence.

## Exit Criteria
- Quarantine operation policy and cadence are explicit and auditable.
- Deprecated gate retirement policy is explicit and auditable.
- Governance suite simplification candidates are bounded and evidence-linked.
- CE-04 through CE-06 have evidence-ready pathways in tracker and WS-08 plan.

## Notes
- WS-08 begins after WS-07 closure checkpoint commit `026ad47`.
- Existing unrelated working-tree drift remains out of scope.
