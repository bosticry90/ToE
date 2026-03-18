# WS_05_AUTHORITY_SURFACE_CONSOLIDATION_PLAN_v0

## Workstream
- ID: WS-05
- Name: Authority Surface Consolidation
- Status: ACTIVE
- Priority: PRIMARY

## Objective
Define and ratify a primary authority residency model that reduces cross-surface coordination burden across state, inventory, and roadmap surfaces without weakening bounded governance rigor.

## Scope
In scope:
- authority residency rules for canonical status tokens and pointers.
- explicit role boundaries for compact State, central inventory, and roadmap surfaces.
- elimination of at least one repeated cross-surface fallback pattern.
- gate-alignment planning for residency-aware consistency checks.

Out of scope during WS-05:
- theorem-route expansion.
- new packet family expansion not required by consolidation.
- new governance family creation that does not replace existing duplicated behavior.

## Residency Model Draft (WS-05-T01)
- Pillar status value authority: `formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json` plus pillar discharge docs.
- Seam status value authority: `formal/docs/paper/TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md` plus seam registries.
- Compact state role (`State_of_the_Theory.md`): posture summary and bounded canonical pointers.
- Central inventory role (`formal/docs/paper/TOE_MATH_PHYSICS_INVENTORY_v0.md`): broad object-level dependency and pointer inventory.
- Roadmap role (`formal/docs/paper/PHYSICS_ROADMAP_v0.md`): planning and sequencing; not fallback value authority.

## Task Plan
| ID | Task | Status | Blocked By | Deliverable | Evidence Required |
| --- | --- | --- | --- | --- | --- |
| WS-05-T01 | Write and ratify authority residency model | DONE | none | Residency model in this plan + tracker linkage | File commit + tracker row update |
| WS-05-T02 | Baseline representative canonical-change coordination cost | DONE | WS-05-T01 | Before-state touch matrix (3 workflows) | `formal/docs/release/WS_05_AUTHORITY_COORDINATION_BASELINE_MATRIX_v0.md` |
| WS-05-T03 | Select and remove one repeated cross-surface fallback pattern | ACTIVE | WS-05-T02 | Removed fallback pattern and explicit replacement rule | Diff + targeted gate run |
| WS-05-T04 | Align authority consistency gate expectations to residency model | TODO | WS-05-T03 | Updated gate assumptions for authority vs pointer roles | Targeted pytest output |
| WS-05-T05 | Record WS-05 completion checkpoint | TODO | WS-05-T04 | WS-05 closure row in master tracker | Exit criteria all satisfied |

## Evidence Log

- 2026-03-18 WS-05-T01: Residency model drafted and linked in this plan; tracker linkage active.
- 2026-03-18 WS-05-T02: Baseline matrix committed in `formal/docs/release/WS_05_AUTHORITY_COORDINATION_BASELINE_MATRIX_v0.md` with conservative before-state touch/edit counts for WF-01 through WF-03.

## Candidate Baseline Workflows for WS-05-T02
1. Pillar status promotion workflow.
2. Seam packet progression workflow.
3. Deep-maturity target rollover workflow.

## Exit Criteria
- Primary authority residency model is documented and linked from the master tracker.
- At least one repeated cross-surface fallback pattern is eliminated.
- Representative canonical change requires fewer coordinated surface edits than baseline.
- Relevant authority-consistency gates are aligned and pass in bounded verification.

## Notes
- This plan starts from consolidation Phase-0 commit `adbd3b5`.
- Unrelated existing test/comparator drift remains out of scope for WS-05 kickoff.
