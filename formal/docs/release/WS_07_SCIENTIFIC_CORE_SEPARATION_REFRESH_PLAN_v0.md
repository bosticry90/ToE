# WS_07_SCIENTIFIC_CORE_SEPARATION_REFRESH_PLAN_v0

## Workstream
- ID: WS-07
- Name: Scientific Core Separation Refresh
- Status: ACTIVE
- Priority: PRIMARY

## Objective
Refresh the scientific-core separation surface to satisfy CE-03 using explicit science-vs-governance boundaries and a bounded restart subset definition.

## Scope
In scope:
- refresh `formal/docs/release/SCIENTIFIC_CORE_INDEX_v0.md` classification structure where needed.
- define explicit restart subset boundaries for post-consolidation theory work.
- keep changes bounded to separation/indexing surfaces and tracker evidence.

Out of scope during WS-07:
- theorem-route expansion.
- new packet family introduction.
- broad multi-surface refactors outside scientific-core separation refresh.

## Baseline Snapshot (WS-07-T01)
- Canonical refresh target: `formal/docs/release/SCIENTIFIC_CORE_INDEX_v0.md`.
- Baseline indexed active surfaces: 12 (`SCI-0001`..`SCI-0012`).
- Baseline science:ceremony ratio: 7:5.
- CE-03 requirement target: explicit science vs governance separation and restart subset committed with tracker evidence.

## Task Plan
| ID | Task | Status | Blocked By | Deliverable | Evidence Required |
| --- | --- | --- | --- | --- | --- |
| WS-07-T01 | Define refresh scope and baseline snapshot | DONE | none | Baseline counts and target surface pinned in this plan | Plan file + tracker linkage |
| WS-07-T02 | Define explicit science-vs-governance separation criteria refresh | ACTIVE | WS-07-T01 | Updated criteria section for scientific-core index refresh | Updated index section + bounded diff evidence |
| WS-07-T03 | Define restart subset boundary for post-consolidation theory work | TODO | WS-07-T02 | Restart subset table in scientific-core index | Section committed in index |
| WS-07-T04 | Apply bounded refresh update to scientific-core index and tracker CE-03 row | TODO | WS-07-T03 | CE-03 marked done with concrete evidence | Tracker and index updates + targeted checks |
| WS-07-T05 | Record WS-07 completion checkpoint | TODO | WS-07-T04 | WS-07 closure row in tracker | Closure row with evidence chain |

## Evidence Log
- 2026-03-18 WS-07-T01: Baseline pinned from `SCIENTIFIC_CORE_INDEX_v0.md` (12 indexed active surfaces; science:ceremony ratio 7:5) and CE-03 target scoped.

## Exit Criteria
- Scientific-core index includes explicit science vs governance separation criteria refresh.
- Restart subset boundaries are explicit and reviewable.
- Tracker CE-03 row is marked DONE with file+commit evidence.

## Notes
- WS-07 starts immediately after WS-06 closure checkpoint commit `d72ad68`.
- Existing unrelated working-tree drift remains out of scope.
