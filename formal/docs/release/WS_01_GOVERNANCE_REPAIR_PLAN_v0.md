# WS_01_GOVERNANCE_REPAIR_PLAN_v0

## Workstream
- ID: WS-01
- Name: Governance Repair
- Status: DONE
- Priority: COMPLETED

## Objective
Repair governance drift and restore confidence in architecture-schema enforcement.

## Task Plan
| ID | Task | Status | Blocked By | Deliverable | Evidence Required |
| --- | --- | --- | --- | --- | --- |
| WS-01-T01 | Run and fix architecture schema enforcement gate | DONE | none | Green architecture-schema gate run | Pytest output attached |
| WS-01-T02 | Classify each governance failure by type | DONE | WS-01-T01 | Failure classification table | Failure classes listed |
| WS-01-T03 | Repair missing phase coverage issues | DONE | WS-01-T02 | Updated canonical surfaces | Diff + validation output |
| WS-01-T04 | Repair disallowed adjudication values | DONE | WS-01-T02 | Clean adjudication tokens | Diff + validation output |
| WS-01-T05 | Re-run governance sample suite | DONE | WS-01-T03, WS-01-T04 | Bounded governance rerun | Pytest output attached |
| WS-01-T06 | Close governance repair checkpoint | DONE | WS-01-T05 | WS-01 closure entry | Tracker evidence row |

## Evidence Log
- 2026-03-17 WS-01-T01: `c:/Users/psboy/Documents/ToE/.venv/Scripts/python.exe -m pytest -q formal/python/tests/test_architecture_schema_enforcement.py` -> `4 passed in 0.87s`.
- 2026-03-17 WS-01-T02: classification result `NO_RUNTIME_FAILURES_OBSERVED_IN_WS01_SCOPE`.
- 2026-03-17 WS-01-T03: no missing phase-coverage repairs required after clean T01 run.
- 2026-03-17 WS-01-T04: no disallowed adjudication repairs required after clean T01 run.
- 2026-03-17 WS-01-T05: `c:/Users/psboy/Documents/ToE/.venv/Scripts/python.exe -m pytest -q formal/python/tests/test_architecture_schema_enforcement.py formal/python/tests/test_br01_front_door_enforced.py` -> `5 passed in 2.51s`.
- 2026-03-17 WS-01-T06: WS-01 exit criteria satisfied and closure recorded in master tracker.

## Blockers
- none

## Exit Criteria
- `formal/python/tests/test_architecture_schema_enforcement.py` passes.
- No unresolved disallowed adjudication values remain.
- Repaired files are logged in the master tracker with evidence.
