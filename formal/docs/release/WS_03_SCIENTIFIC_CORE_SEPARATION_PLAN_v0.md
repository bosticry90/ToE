# WS_03_SCIENTIFIC_CORE_SEPARATION_PLAN_v0

## Workstream
- ID: WS-03
- Name: Scientific Core Separation
- Status: DONE
- Priority: COMPLETED

## Objective
Separate scientific-core surfaces from governance and ceremony-heavy surfaces so progress signals are clearer.

## Required Classification Categories
- governance control
- theorem surface
- numerical model
- bridge logic
- empirical protocol
- evidence bookkeeping

## Task Plan
| ID | Task | Status | Blocked By | Deliverable | Evidence Required |
| --- | --- | --- | --- | --- | --- |
| WS-03-T01 | Create SCIENTIFIC_CORE_INDEX_v0.md | DONE | WS-01-T06 | Scientific core index file | File path + initial index rows |
| WS-03-T02 | Classify active canonicals by required categories | DONE | WS-03-T01 | Fully tagged active canonical list | Category completeness check |
| WS-03-T03 | Identify science-critical surfaces | DONE | WS-03-T02 | Science-critical surface list | Explicit list in index |
| WS-03-T04 | Identify ceremony-heavy surfaces | DONE | WS-03-T02 | Ceremony-heavy surface list | Explicit list in index |
| WS-03-T05 | Produce ratio summary | DONE | WS-03-T03, WS-03-T04 | Category ratio summary | Ratio table + date stamp |

## Evidence Log
- 2026-03-17 WS-03-T01: `formal/docs/release/SCIENTIFIC_CORE_INDEX_v0.md` present with indexed rows (`SCI-0001`..`SCI-0012`).
- 2026-03-17 WS-03-T02: category completeness table present with all required categories marked `COVERED`.
- 2026-03-17 WS-03-T03: `Science-Critical Surfaces (WS-03-T03)` section present in the index.
- 2026-03-17 WS-03-T04: `Ceremony-Heavy Surfaces (WS-03-T04)` section present in the index.
- 2026-03-17 WS-03-T05: `Ratio Summary (WS-03-T05)` section present with `Science:ceremony ratio = 7:5`.

## Blockers
- none

## Exit Criteria
- All active canonical surfaces are tagged.
- Critical scientific surfaces are explicitly listed.
- Governance-heavy surfaces are explicitly listed.
- Ratio summary is committed and referenced from the master tracker.
