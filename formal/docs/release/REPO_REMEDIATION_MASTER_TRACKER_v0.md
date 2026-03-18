# REPO_REMEDIATION_MASTER_TRACKER_v0

## Architecture Consolidation Phase Activation (2026-03-18)
- Phase: `ARCHITECTURE_CONSOLIDATION_PHASE_v0`
- Program posture: ACTIVE
- Scope posture: consolidation-only
- Theory expansion posture: PAUSED_UNTIL_CONSOLIDATION_EXIT_GATE
- Consolidation charter pointer: `formal/docs/release/ARCHITECTURE_CONSOLIDATION_PHASE_v0.md`
- Canonical state mirror pointer: `State_of_the_Theory.md`
- Canonical roadmap mirror pointer: `formal/docs/paper/PHYSICS_ROADMAP_v0.md`

## Objective
Establish a bounded remediation program with explicit workstreams, blockers, evidence, and hard exit criteria. This tracker is the canonical top-level source of truth for active, blocked, completed, and next work.

## Current Status
- Primary workstream: WS-06
- Active task: WS-06-T03
- WS-01 through WS-04: DONE
- WS-05: DONE
- WS-06: ACTIVE
- WS-07 through WS-08: TODO (architecture consolidation phase)
- Program state: ACTIVE
- Active WS-05 plan pointer: `formal/docs/release/WS_05_AUTHORITY_SURFACE_CONSOLIDATION_PLAN_v0.md`
- Active WS-05 baseline pointer: `formal/docs/release/WS_05_AUTHORITY_COORDINATION_BASELINE_MATRIX_v0.md`
- Active WS-06 plan pointer: `formal/docs/release/WS_06_REPETITION_REDUCTION_PHASE2_PLAN_v0.md`

## Workstreams
| ID | Workstream | Status | Primary | Scope Summary |
| --- | --- | --- | --- | --- |
| WS-01 | Governance Repair | DONE | NO | Restore governance credibility and schema enforcement integrity. |
| WS-02 | Surface Reduction | DONE | NO | Reduce duplicated test and gate surface via registry and parametrization. |
| WS-03 | Scientific Core Separation | DONE | NO | Separate scientific-core surfaces from governance-heavy surfaces. |
| WS-04 | Math and Evidence Deepening | DONE | NO | Deepen theorem content and broaden empirical confrontation. |
| WS-05 | Authority Surface Consolidation | DONE | NO | Define primary authority residency and reduce cross-surface coordination burden. |
| WS-06 | Repetition Reduction Phase 2 | ACTIVE | YES | Consolidate repeated gate families using shared helpers and registry-driven tests. |
| WS-07 | Scientific Core Separation Refresh | TODO | NO | Refresh scientific-core tagging and restart subset boundaries for theory work. |
| WS-08 | Governance Right-Sizing | TODO | NO | Operationalize quarantine and retirement controls while preserving rigor. |

## Status Labels
- TODO
- ACTIVE
- BLOCKED
- REVIEW
- DONE
- ARCHIVED

## Sequencing Rules
- Only one task per workstream may be ACTIVE at a time.
- Only one workstream may be primary at a time.
- No new packet families during WS-01 unless required for an already-started bounded slice.
- No repo-wide refactors until WS-01 is green.
- Every completed task must attach evidence: test output, commit hash, file path, short result note.
- During WS-05 through WS-08, no new theorem-route expansion is allowed.
- During WS-05 through WS-08, no new packet families are allowed unless required by active consolidation tasks.
- During WS-05 through WS-08, no new governance family is allowed unless it replaces or retires existing duplicated surface.
- Theory work restart is blocked until all consolidation exit-gate rows are marked satisfied with evidence.

## Consolidation Exit Gate (Hard)
Theory work may restart only when all rows below are satisfied:

| Exit ID | Requirement | Status | Evidence |
| --- | --- | --- | --- |
| CE-01 | Documented primary authority model with explicit residency rules across state/inventory/roadmap. | DONE | `formal/docs/release/WS_05_AUTHORITY_SURFACE_CONSOLIDATION_PLAN_v0.md`, commits `b43a60e` and `484f351` |
| CE-02 | One major repeated family reduced to shared helper or registry-driven form. | TODO | Pending |
| CE-03 | Scientific core index refreshed with explicit science vs governance separation and restart subset. | TODO | Pending |
| CE-04 | Quarantine and deprecated gate retirement policy documented and active. | TODO | Pending |
| CE-05 | Relevant governance and seam checks pass after simplification changes. | TODO | Pending |
| CE-06 | Anti-regrowth guardrails committed to prevent reintroducing architecture overgrowth. | TODO | Pending |

## Active Tasks
| ID | Workstream | Task | Status | Owner | Blocked By | Evidence | Exit Criteria |
| --- | --- | --- | --- | --- | --- | --- | --- |
| WS-06-T03 | Repetition Reduction Phase 2 | Implement shared helper and representative parametrized gate | ACTIVE | user | WS-06-T02 | `formal/docs/release/WS_06_DRYRUN_TOKEN_FLIP_FAMILY_MAPPING_v0.md` | First reduced slice committed with targeted pytest evidence |

## Blocked Tasks
| ID | Workstream | Task | Status | Owner | Blocked By | Evidence | Exit Criteria |
| --- | --- | --- | --- | --- | --- | --- | --- |
| none | n/a | n/a | n/a | n/a | n/a | n/a | n/a |

## Completed Tasks
| ID | Workstream | Task | Status | Owner | Blocked By | Evidence | Exit Criteria |
| --- | --- | --- | --- | --- | --- | --- | --- |
| WS-01-T01 | Governance Repair | Run and fix architecture schema enforcement gate | DONE | user | none | 2026-03-17: `c:/Users/psboy/Documents/ToE/.venv/Scripts/python.exe -m pytest -q formal/python/tests/test_architecture_schema_enforcement.py` -> 4 passed in 0.87s | formal/python/tests/test_architecture_schema_enforcement.py passes cleanly |
| WS-01-T02 | Governance Repair | Classify all governance failures by type | DONE | user | WS-01-T01 | 2026-03-17: no runtime failures observed in WS-01 scope | Failure classes recorded in WS-01 plan |
| WS-01-T03 | Governance Repair | Repair missing phase coverage issues | DONE | user | WS-01-T02 | 2026-03-17: no repairs required after clean T01 run | No unresolved phase coverage violations |
| WS-01-T04 | Governance Repair | Repair disallowed adjudication values | DONE | user | WS-01-T02 | 2026-03-17: no repairs required after clean T01 run | No unresolved disallowed adjudication values |
| WS-01-T05 | Governance Repair | Re-run governance sample suite | DONE | user | WS-01-T03, WS-01-T04 | 2026-03-17: `c:/Users/psboy/Documents/ToE/.venv/Scripts/python.exe -m pytest -q formal/python/tests/test_architecture_schema_enforcement.py formal/python/tests/test_br01_front_door_enforced.py` -> 5 passed in 2.51s | Governance sample run passes |
| WS-01-T06 | Governance Repair | Close governance checkpoint | DONE | user | WS-01-T05 | 2026-03-17: WS-01 exit criteria satisfied and logged | WS-01 exit criteria met and logged |
| WS-02-T01 | Surface Reduction | Create quarantine register | DONE | user | WS-01-T06 | 2026-03-17: `formal/docs/release/QUARANTINE_REGISTER_v0.md` exists with active rows | Quarantine register exists |
| WS-02-T02 | Surface Reduction | Create seam packet registry | DONE | user | WS-02-T01 | 2026-03-17: `formal/docs/paper/QFT_GR_SEAM_PACKET_REGISTRY_v0.json` exists with packet42-54 scope | Registry exists and is referenced |
| WS-02-T03 | Surface Reduction | Select one repeated gate family to parametrize | DONE | user | none | 2026-03-17: selected packet42-54 gate family baseline measured at 91 files | Family selected and documented |
| WS-02-T04 | Surface Reduction | Extract shared helper utilities | DONE | user | WS-02-T03 | 2026-03-17: helper module present (`formal/python/tests/qft_gr_seam_registry_helpers.py`) and representative gate test passed (1 passed in 0.71s) | Shared helpers committed |
| WS-02-T05 | Surface Reduction | Replace one cloned family with parametrized tests | DONE | user | WS-02-T04 | 2026-03-17: parametrized eligibility family and wrappers validated (6 passed in 2.70s); baseline 91 files with wrapper after-state 21 lines across packet42/43/44 | One family consolidated |
| WS-02-T06 | Surface Reduction | Define filename shortening convention | DONE | user | WS-02-T05 | 2026-03-17: filename convention section added in WS-02 plan | Convention documented in WS-02 plan |
| WS-03-T01 | Scientific Core Separation | Create scientific core index | DONE | user | WS-01-T06 | 2026-03-17: scientific core index artifact exists with indexed active canonicals | Scientific core index exists |
| WS-03-T02 | Scientific Core Separation | Classify active canonical surfaces by category | DONE | user | WS-03-T01 | 2026-03-17: category completeness table present with all required categories covered | All active canonicals tagged |
| WS-03-T03 | Scientific Core Separation | Identify science-critical surfaces | DONE | user | WS-03-T02 | 2026-03-17: science-critical section present in scientific core index | Science-critical list committed |
| WS-03-T04 | Scientific Core Separation | Identify ceremony-heavy surfaces | DONE | user | WS-03-T02 | 2026-03-17: ceremony-heavy section present in scientific core index | Ceremony-heavy list committed |
| WS-03-T05 | Scientific Core Separation | Produce ratio summary | DONE | user | WS-03-T03, WS-03-T04 | 2026-03-17: ratio summary present in scientific core index (7:5) | Ratio summary committed |
| WS-04-T01 | Math and Evidence Deepening | Select 2-3 theorem surfaces | DONE | user | WS-03-T05 | 2026-03-17: selected THM-01..THM-03 shortlist in WS_04_MATH_AND_EVIDENCE_DEEPENING_PLAN_v0.md | Theorem shortlist committed |
| WS-04-T02 | Math and Evidence Deepening | Classify theorem surfaces as contract, bridge, derivation | DONE | user | WS-04-T01 | 2026-03-17: theorem classification table added in WS_04_MATH_AND_EVIDENCE_DEEPENING_PLAN_v0.md | Classification table committed |
| WS-04-T03 | Math and Evidence Deepening | Identify shallow theorem targets | DONE | user | WS-04-T02 | 2026-03-17: shallow-target remediation list added in WS_04_MATH_AND_EVIDENCE_DEEPENING_PLAN_v0.md | Shallow-target list committed |
| WS-04-T04 | Math and Evidence Deepening | Choose one empirical lane to broaden | DONE | user | WS-04-T03 | 2026-03-17: empirical lane selection section added in WS_04_MATH_AND_EVIDENCE_DEEPENING_PLAN_v0.md | Lane selection committed |
| WS-04-T05 | Math and Evidence Deepening | Define falsification criteria for selected lane | DONE | user | WS-04-T04 | 2026-03-17: falsification criteria section added in WS_04_MATH_AND_EVIDENCE_DEEPENING_PLAN_v0.md | Falsification criteria committed |
| WS-04-T06 | Math and Evidence Deepening | Complete one substantive upgrade | DONE | user | WS-04-T05 | 2026-03-17: packet44 protocol extension validated with targeted gate (`3 passed in 0.72s`) | One theorem or lane upgrade completed |
| WS-05-T03 | Authority Surface Consolidation | Select and remove one repeated cross-surface fallback pattern | DONE | user | WS-05-T02 | 2026-03-18: `formal/python/tests/test_pillar_deep_maturity_program_gate.py` and `State_of_the_Theory.md` updated; targeted gate run `2 passed in 0.93s`; commit `b43a60e` | One repeated fallback pattern removed and replacement rule committed with bounded gate evidence |
| WS-05-T04 | Authority Surface Consolidation | Align authority consistency gate expectations to residency model | DONE | user | WS-05-T03 | 2026-03-18: `formal/python/tests/test_pillar_deep_maturity_m2_completion_gate.py` aligned and verified `2 passed in 0.73s`; commit `484f351` | At least one authority consistency gate family aligned to residency model and passes bounded verification |
| WS-05-T05 | Authority Surface Consolidation | Record WS-05 completion checkpoint | DONE | user | WS-05-T04 | 2026-03-18: WS-05 closure checkpoint row recorded with evidence chain (`51c9a65`, `b43a60e`, `484f351`) | WS-05 closure checkpoint row recorded with evidence |
| WS-06-T01 | Repetition Reduction Phase 2 | Select repeated family and baseline clone surface | DONE | user | none | 2026-03-18: selected family `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_*_cycle*_gate.py`, baseline count 14 files, plan `formal/docs/release/WS_06_REPETITION_REDUCTION_PHASE2_PLAN_v0.md` | Selected family and baseline documented with tracker linkage |
| WS-06-T02 | Repetition Reduction Phase 2 | Define reduction contract and helper interface | DONE | user | WS-06-T01 | 2026-03-18: helper API and full cycle mapping drafted in `formal/docs/release/WS_06_DRYRUN_TOKEN_FLIP_FAMILY_MAPPING_v0.md`; plan updated to activate WS-06-T03 | Helper API and parametrization contract drafted for selected family |

## Workstream Task Ledger
| ID | Workstream | Task | Status | Owner | Blocked By | Evidence | Exit Criteria |
| --- | --- | --- | --- | --- | --- | --- | --- |
| WS-01-T01 | Governance Repair | Run and fix architecture schema enforcement gate | DONE | user | none | 2026-03-17: architecture schema gate passed (4 passed in 0.87s) | formal/python/tests/test_architecture_schema_enforcement.py passes cleanly |
| WS-01-T02 | Governance Repair | Classify all governance failures by type | DONE | user | WS-01-T01 | 2026-03-17: no runtime failures observed in WS-01 scope | Failure classes recorded in WS-01 plan |
| WS-01-T03 | Governance Repair | Repair missing phase coverage issues | DONE | user | WS-01-T02 | 2026-03-17: no repairs required after clean T01 run | No unresolved phase coverage violations |
| WS-01-T04 | Governance Repair | Repair disallowed adjudication values | DONE | user | WS-01-T02 | 2026-03-17: no repairs required after clean T01 run | No unresolved disallowed adjudication values |
| WS-01-T05 | Governance Repair | Re-run governance sample suite | DONE | user | WS-01-T03, WS-01-T04 | 2026-03-17: bounded governance sample passed (5 passed in 2.51s) | Governance sample run passes |
| WS-01-T06 | Governance Repair | Close governance checkpoint | DONE | user | WS-01-T05 | 2026-03-17: WS-01 exit criteria satisfied and logged | WS-01 exit criteria met and logged |
| WS-02-T01 | Surface Reduction | Create quarantine register | DONE | user | WS-01-T06 | 2026-03-17: `formal/docs/release/QUARANTINE_REGISTER_v0.md` exists with active rows | Quarantine register exists |
| WS-02-T02 | Surface Reduction | Create seam packet registry | DONE | user | WS-02-T01 | 2026-03-17: `formal/docs/paper/QFT_GR_SEAM_PACKET_REGISTRY_v0.json` exists with packet42-54 scope | Registry exists and is referenced |
| WS-02-T03 | Surface Reduction | Select one repeated gate family to parametrize | DONE | user | none | 2026-03-17: selected packet42-54 gate family baseline measured at 91 files | Family selected and documented |
| WS-02-T04 | Surface Reduction | Extract shared helper utilities | DONE | user | WS-02-T03 | 2026-03-17: helper module present (`formal/python/tests/qft_gr_seam_registry_helpers.py`) and representative gate test passed (1 passed in 0.71s) | Shared helpers committed |
| WS-02-T05 | Surface Reduction | Replace one cloned family with parametrized tests | DONE | user | WS-02-T04 | 2026-03-17: parametrized eligibility family and wrappers validated (6 passed in 2.70s); baseline 91 files with wrapper after-state 21 lines across packet42/43/44 | One family consolidated |
| WS-02-T06 | Surface Reduction | Define filename shortening convention | DONE | user | WS-02-T05 | 2026-03-17: filename convention section added in WS-02 plan | Convention documented in WS-02 plan |
| WS-03-T01 | Scientific Core Separation | Create scientific core index | DONE | user | WS-01-T06 | 2026-03-17: scientific core index artifact exists with indexed active canonicals | Scientific core index exists |
| WS-03-T02 | Scientific Core Separation | Classify active canonical surfaces by category | DONE | user | WS-03-T01 | 2026-03-17: category completeness table present with all required categories covered | All active canonicals tagged |
| WS-03-T03 | Scientific Core Separation | Identify science-critical surfaces | DONE | user | WS-03-T02 | 2026-03-17: science-critical section present in scientific core index | Science-critical list committed |
| WS-03-T04 | Scientific Core Separation | Identify ceremony-heavy surfaces | DONE | user | WS-03-T02 | 2026-03-17: ceremony-heavy section present in scientific core index | Ceremony-heavy list committed |
| WS-03-T05 | Scientific Core Separation | Produce ratio summary | DONE | user | WS-03-T03, WS-03-T04 | 2026-03-17: ratio summary present in scientific core index (7:5) | Ratio summary committed |
| WS-04-T01 | Math and Evidence Deepening | Select 2-3 theorem surfaces | DONE | user | WS-03-T05 | 2026-03-17: selected THM-01..THM-03 shortlist in WS_04_MATH_AND_EVIDENCE_DEEPENING_PLAN_v0.md | Theorem shortlist committed |
| WS-04-T02 | Math and Evidence Deepening | Classify theorem surfaces as contract, bridge, derivation | DONE | user | WS-04-T01 | 2026-03-17: theorem classification table added in WS_04_MATH_AND_EVIDENCE_DEEPENING_PLAN_v0.md | Classification table committed |
| WS-04-T03 | Math and Evidence Deepening | Identify shallow theorem targets | DONE | user | WS-04-T02 | 2026-03-17: shallow-target remediation list added in WS_04_MATH_AND_EVIDENCE_DEEPENING_PLAN_v0.md | Shallow-target list committed |
| WS-04-T04 | Math and Evidence Deepening | Choose one empirical lane to broaden | DONE | user | WS-04-T03 | 2026-03-17: empirical lane selection section added in WS_04_MATH_AND_EVIDENCE_DEEPENING_PLAN_v0.md | Lane selection committed |
| WS-04-T05 | Math and Evidence Deepening | Define falsification criteria for selected lane | DONE | user | WS-04-T04 | 2026-03-17: falsification criteria section added in WS_04_MATH_AND_EVIDENCE_DEEPENING_PLAN_v0.md | Falsification criteria committed |
| WS-04-T06 | Math and Evidence Deepening | Complete one substantive upgrade | DONE | user | WS-04-T05 | 2026-03-17: packet44 protocol extension validated with targeted gate (`3 passed in 0.72s`) | One theorem or lane upgrade completed |

## Decision Log
- DEC-001: Governance repair precedes new route expansion.
- DEC-002: Packet seam progression remains bounded and separately committed.
- DEC-003: State, inventory, roadmap authority split remains transitional pending consolidation.
- DEC-004: No new quarantine without register entry.

## Risks
- RISK-001: Governance exemptions may expand faster than they are retired.
- RISK-002: Surface reduction work can stall if WS-01 is not cleanly closed.
- RISK-003: Ceremony-heavy gate growth can obscure scientific progress signals.
- RISK-004: Math deepening can drift without explicit falsification criteria.

## Exit Criteria
Program exits when all are true:
- WS-01 exit criteria met and logged with evidence.
- WS-02 exit criteria met and logged with measurable duplication reduction.
- WS-03 exit criteria met with complete canonical classification.
- WS-04 exit criteria met with at least one substantive theorem or evidence upgrade.
- No ACTIVE or BLOCKED tasks remain.
