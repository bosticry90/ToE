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
| WS-08-T02 | Draft active quarantine operation policy and review cadence | ACTIVE | WS-08-T01 | Quarantine operation policy section or artifact with cadence controls | Bounded policy text + tracker evidence row |
| WS-08-T03 | Draft deprecated gate retirement policy | TODO | WS-08-T02 | Deprecated gate retirement policy artifact with disposition states | Policy artifact + tracker evidence |
| WS-08-T04 | Identify and record governance suite simplification candidates | TODO | WS-08-T03 | Candidate list with bounded adoption criteria | Candidate matrix + tracker evidence |
| WS-08-T05 | Record WS-08 completion checkpoint | TODO | WS-08-T04 | WS-08 closure row in tracker | Closure row with evidence chain |

## Evidence Log
- 2026-03-18 WS-08-T01: Created WS-08 workstream plan, pinned baseline references, and linked tracker activation to this plan.

## Exit Criteria
- Quarantine operation policy and cadence are explicit and auditable.
- Deprecated gate retirement policy is explicit and auditable.
- Governance suite simplification candidates are bounded and evidence-linked.
- CE-04 through CE-06 have evidence-ready pathways in tracker and WS-08 plan.

## Notes
- WS-08 begins after WS-07 closure checkpoint commit `026ad47`.
- Existing unrelated working-tree drift remains out of scope.
