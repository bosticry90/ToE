# REPO_REMEDIATION_MASTER_TRACKER_v0

## Architecture Consolidation Phase Activation (2026-03-18)
- Phase: `ARCHITECTURE_CONSOLIDATION_PHASE_v0`
- Program posture: ACTIVE
- Scope posture: consolidation-only
- Theory expansion posture: RESTART_AUTHORIZED_POST_CONSOLIDATION_EXIT_GATE
- Consolidation exit-gate posture: SATISFIED_CE01_TO_CE06
- Consolidation charter pointer: `formal/docs/release/ARCHITECTURE_CONSOLIDATION_PHASE_v0.md`
- Canonical state mirror pointer: `State_of_the_Theory.md`
- Canonical roadmap mirror pointer: `formal/docs/paper/PHYSICS_ROADMAP_v0.md`

## Objective
Establish a bounded remediation program with explicit workstreams, blockers, evidence, and hard exit criteria. This tracker is the canonical top-level source of truth for active, blocked, completed, and next work.

## Current Status
- Primary workstream: WS-10
- Active task: WS-10-T05
- WS-01 through WS-04: DONE
- WS-05: DONE
- WS-06: DONE
- WS-07: DONE
- WS-08: DONE (architecture consolidation phase)
- WS-09: DONE (CE-05 post-simplification verification sweep)
- WS-10: ACTIVE (first pilot phase closed; next bounded slice selected)
- Program state: ACTIVE
- Active WS-05 plan pointer: `formal/docs/release/WS_05_AUTHORITY_SURFACE_CONSOLIDATION_PLAN_v0.md`
- Active WS-05 baseline pointer: `formal/docs/release/WS_05_AUTHORITY_COORDINATION_BASELINE_MATRIX_v0.md`
- Active WS-06 plan pointer: `formal/docs/release/WS_06_REPETITION_REDUCTION_PHASE2_PLAN_v0.md`
- Active WS-07 plan pointer: `formal/docs/release/WS_07_SCIENTIFIC_CORE_SEPARATION_REFRESH_PLAN_v0.md`
- Active WS-08 plan pointer: `formal/docs/release/WS_08_GOVERNANCE_RIGHT_SIZING_PLAN_v0.md`
- Active WS-09 plan pointer: `formal/docs/release/WS_09_POST_SIMPLIFICATION_VERIFICATION_SWEEP_PLAN_v0.md`
- Active WS-10 plan pointer: `formal/docs/release/WS_10_THEORY_RESTART_PILOT_PLAN_v0.md`
- Active CE-06 guardrail pointer: `formal/docs/release/CE_06_ANTI_REGROWTH_GUARDRAILS_v0.md`

## Bounded Theory Restart Activation (2026-03-18)
- Restart workstream: `WS-10`
- Restart task: `WS-10-T05`
- Restart slice pointer: `formal/docs/release/WS_10_THEORY_RESTART_PILOT_PLAN_v0.md`
- First restart target: `TOE_GR01_FUNCTION_SPACE_REGULARITY_SURFACE_v0`
- First restart theorem note: bounded GR01 boundary-term regularity lemma only.
- First restart evidence goal: local theorem-surface deepening with no governance-family expansion.
- First restart verification path: `formal/python/tests/test_state_theory_dag.py`, `formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py`, `formal/python/tests/test_gr01_function_space_completion_criteria_gate.py`, `formal/python/tests/test_gr01_function_space_discrete_regularity_evidence_gate.py`, optional `formal/python/tests/test_gr01_publication_grade_discharge_package_gate.py`.
- Restart activation verification result: `5 passed in 2.54s`.
- Restart guardrails: no new governance family, no cloned gate proliferation, no duplicated authority residency without explicit decision, bounded slice only.

## WS-10 First Pilot Checkpoint (2026-03-18)
- Pilot phase status: `CLOSED_WITH_BOUNDED_EVIDENCE`
- Activation commit: `a055921`
- First theorem-deepening commit: `da6e6c5`
- Completed bounded slice: `WS-10-T02_GR01_BOUNDARY_TERM_REGULARITY`
- Completed theorem result: GR01 local boundary-term regularity lemma contract pinned without reopening tracker/state/roadmap/package-control churn.
- Completed theorem verification result: `3 passed in 1.94s` via `formal/python/tests/test_gr01_function_space_completion_criteria_gate.py`, `formal/python/tests/test_gr01_function_space_discrete_regularity_evidence_gate.py`, `formal/python/tests/test_gr01_publication_grade_discharge_package_gate.py`.
- Next bounded slice: `WS-10-T05_GR_QM_SEAM_DISCHARGE`
- Next bounded target: `DERIVATION_TARGET_GR_QM_CLASS_B_SEAM_PROMOTION_DISCHARGE_CYCLE02_v0`
- Next target path: `formal/docs/paper/DERIVATION_TARGET_GR_QM_CLASS_B_SEAM_PROMOTION_DISCHARGE_CYCLE02_v0.md`
- Next bounded verification path: `formal/python/tests/test_gr_qm_seam_promotion_cycle02_discharge_gate.py` plus pre-slice control-surface parity checks.

## Workstreams
| ID | Workstream | Status | Primary | Scope Summary |
| --- | --- | --- | --- | --- |
| WS-01 | Governance Repair | DONE | NO | Restore governance credibility and schema enforcement integrity. |
| WS-02 | Surface Reduction | DONE | NO | Reduce duplicated test and gate surface via registry and parametrization. |
| WS-03 | Scientific Core Separation | DONE | NO | Separate scientific-core surfaces from governance-heavy surfaces. |
| WS-04 | Math and Evidence Deepening | DONE | NO | Deepen theorem content and broaden empirical confrontation. |
| WS-05 | Authority Surface Consolidation | DONE | NO | Define primary authority residency and reduce cross-surface coordination burden. |
| WS-06 | Repetition Reduction Phase 2 | DONE | NO | Consolidate repeated gate families using shared helpers and registry-driven tests. |
| WS-07 | Scientific Core Separation Refresh | DONE | NO | Refresh scientific-core tagging and restart subset boundaries for theory work. |
| WS-08 | Governance Right-Sizing | DONE | NO | Operationalize quarantine and retirement controls while preserving rigor. |
| WS-09 | Post-Simplification Verification Sweep | DONE | NO | Completed bounded CE-05 verification ladder with evidence-backed closure checkpoint. |
| WS-10 | Theory Restart Pilot | ACTIVE | YES | Execute one bounded post-consolidation theory slice under anti-regrowth guardrails before any broader theory churn. |

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
| CE-02 | One major repeated family reduced to shared helper or registry-driven form. | DONE | `formal/python/tests/qft_full_derivation_token_flip_dryrun_helpers.py`, `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_representative_cycles37_50_gate.py`, `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_remaining_cycles38_49_gate.py`, commits `dd9bb12` and `8fecd0e` |
| CE-03 | Scientific core index refreshed with explicit science vs governance separation and restart subset. | DONE | `formal/docs/release/SCIENTIFIC_CORE_INDEX_v0.md` sections `Separation Criteria Refresh (WS-07-T02)` and `Restart Subset Boundary (WS-07-T03)`, commits `0c48e25` and `0addd8b` |
| CE-04 | Quarantine and deprecated gate retirement policy documented and active. | DONE | `formal/docs/release/WS_08_GOVERNANCE_RIGHT_SIZING_PLAN_v0.md` section `Active Quarantine Operation Policy (WS-08-T02)` and `formal/docs/release/DEPRECATED_GATE_RETIREMENT_POLICY_v0.md` (`Status: ACTIVE`) |
| CE-05 | Relevant governance and seam checks pass after simplification changes. | DONE | `formal/docs/release/CE_05_POST_SIMPLIFICATION_VERIFICATION_CHECKPOINT_v0.md` (targeted checks `51 passed`; failing tranche reduced `11/3 -> 18/1 -> 19/0`; canonical `governance_suite.ps1` unchanged rerun `422 passed in 141.30s`) |
| CE-06 | Anti-regrowth guardrails committed to prevent reintroducing architecture overgrowth. | DONE | `formal/docs/release/CE_06_ANTI_REGROWTH_GUARDRAILS_v0.md`; cross-surface references pinned in `State_of_the_Theory.md` and `formal/docs/paper/PHYSICS_ROADMAP_v0.md` |

## Active Tasks
| ID | Workstream | Task | Status | Owner | Blocked By | Evidence | Exit Criteria |
| --- | --- | --- | --- | --- | --- | --- | --- |
| WS-10-T05 | Theory Restart Pilot | Open next bounded theory slice: GR-QM seam discharge | ACTIVE | user | WS-10-T04 | 2026-03-18: WS-10 first pilot checkpoint recorded; next bounded target pinned to `DERIVATION_TARGET_GR_QM_CLASS_B_SEAM_PROMOTION_DISCHARGE_CYCLE02_v0` without starting seam work in this commit | Next slice activation note exists and the bounded GR-QM target, theorem pointer family, and gate path are explicit |

## Blocked Tasks
| ID | Workstream | Task | Status | Owner | Blocked By | Evidence | Exit Criteria |
| --- | --- | --- | --- | --- | --- | --- | --- |
| none | none | none | none | none | none | none | none |

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
| WS-06-T03 | Repetition Reduction Phase 2 | Implement shared helper and representative parametrized gate | DONE | user | WS-06-T02 | 2026-03-18: added shared helper `formal/python/tests/qft_full_derivation_token_flip_dryrun_helpers.py` and representative parametrized gate `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_representative_cycles37_50_gate.py`; targeted pytest `6 passed in 0.73s` | First reduced slice committed with targeted pytest evidence |
| WS-06-T04 | Repetition Reduction Phase 2 | Fold remaining selected family members to reduced pattern | DONE | user | WS-06-T03 | 2026-03-18: added reduced-pattern remaining-cycles gate `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_remaining_cycles38_49_gate.py`; bounded family-level reduced-path pytest `42 passed in 1.68s` | Family reduction committed with bounded family-level pytest evidence |
| WS-06-T05 | Repetition Reduction Phase 2 | Record WS-06 completion checkpoint | DONE | user | WS-06-T04 | 2026-03-18: WS-06 closure checkpoint recorded with evidence chain (`e96adbb`, `dd9bb12`, `8fecd0e`) | WS-06 closure checkpoint row recorded with evidence |
| WS-07-T01 | Scientific Core Separation Refresh | Define refresh scope and baseline snapshot | DONE | user | none | 2026-03-18: baseline pinned in `formal/docs/release/WS_07_SCIENTIFIC_CORE_SEPARATION_REFRESH_PLAN_v0.md` (12 indexed active surfaces; science:ceremony ratio 7:5) | Baseline snapshot and CE-03 target scope committed with tracker linkage |
| WS-07-T02 | Scientific Core Separation Refresh | Define explicit science-vs-governance separation criteria refresh | DONE | user | WS-07-T01 | 2026-03-18: `Separation Criteria Refresh (WS-07-T02)` section added in `formal/docs/release/SCIENTIFIC_CORE_INDEX_v0.md` and linked in WS-07 plan evidence log | Updated criteria section for scientific-core index refresh committed with bounded evidence |
| WS-07-T03 | Scientific Core Separation Refresh | Define restart subset boundary for post-consolidation theory work | DONE | user | WS-07-T02 | 2026-03-18: `Restart Subset Boundary (WS-07-T03)` section with restart subset table (`RS-01`..`RS-07`) added in `formal/docs/release/SCIENTIFIC_CORE_INDEX_v0.md` and linked in WS-07 plan evidence log | Restart subset table committed with explicit inclusion and exclusion rules |
| WS-07-T04 | Scientific Core Separation Refresh | Apply bounded refresh update to scientific-core index and tracker CE-03 row | DONE | user | WS-07-T03 | 2026-03-18: CE-03 marked DONE in consolidation exit gate and index completion anchor note added; evidence chain includes commits `0c48e25` and `0addd8b` | CE-03 row marked DONE with concrete index and commit evidence |
| WS-07-T05 | Scientific Core Separation Refresh | Record WS-07 completion checkpoint | DONE | user | WS-07-T04 | 2026-03-18: WS-07 marked DONE and primary workstream advanced to WS-08 activation in tracker and WS-07 plan | WS-07 closure row recorded with complete evidence chain |
| WS-08-T01 | Governance Right-Sizing | Define refresh scope and baseline snapshot | DONE | user | none | 2026-03-18: baseline pinned in `formal/docs/release/WS_08_GOVERNANCE_RIGHT_SIZING_PLAN_v0.md` with WS-08 deliverable scope and tracker linkage | WS-08 baseline and bounded deliverable scope committed with tracker linkage |
| WS-08-T02 | Governance Right-Sizing | Draft active quarantine operation policy and review cadence | DONE | user | WS-08-T01 | 2026-03-18: quarantine operating rules, lifecycle states, and review cadence documented in `formal/docs/release/WS_08_GOVERNANCE_RIGHT_SIZING_PLAN_v0.md` with register linkage to `formal/docs/release/QUARANTINE_REGISTER_v0.md` | Quarantine policy and cadence controls are explicitly documented with bounded evidence |
| WS-08-T03 | Governance Right-Sizing | Draft deprecated gate retirement policy | DONE | user | WS-08-T02 | 2026-03-18: retirement policy artifact `formal/docs/release/DEPRECATED_GATE_RETIREMENT_POLICY_v0.md` created with disposition states (`CANDIDATE`, `DEPRECATED`, `RETIRED`) and lifecycle/review rules | Deprecated gate retirement policy artifact with explicit disposition states is drafted and linked |
| WS-08-T04 | Governance Right-Sizing | Identify and record governance suite simplification candidates | DONE | user | WS-08-T03 | 2026-03-18: candidate matrix `formal/docs/release/WS_08_GOVERNANCE_SUITE_SIMPLIFICATION_CANDIDATES_v0.md` added with bounded adoption criteria and rollout guardrails derived from current governance suite script surfaces | Candidate list with bounded adoption criteria is documented with evidence linkage |
| WS-08-T05 | Governance Right-Sizing | Record WS-08 completion checkpoint | DONE | user | WS-08-T04 | 2026-03-18: WS-08 marked DONE in tracker and WS-08 plan closure checkpoint recorded with evidence chain (`ea34c61`, `7d262c9`, `28b5ba9`, `601c9ff`) | WS-08 closure row is recorded with full evidence chain |
| WS-09-T01 | Post-Simplification Verification Sweep | Align compact state surface with tracker checkpoint fields | DONE | user | none | 2026-03-18: aligned consolidation primary workstream/active task/checkpoint wording between `State_of_the_Theory.md` and tracker while opening CE-05 slice | Compact state checkpoint fields match active tracker authority for CE-05 kickoff |
| WS-09-T02 | Post-Simplification Verification Sweep | Define bounded CE-05 validation matrix | DONE | user | WS-09-T01 | 2026-03-18: CE-05 bounded validation matrix and command ladder recorded in `formal/docs/release/WS_09_POST_SIMPLIFICATION_VERIFICATION_SWEEP_PLAN_v0.md` | Validation matrix maps required bounded checks and command set for CE-05 evidence |
| WS-09-T03 | Post-Simplification Verification Sweep | Run targeted post-simplification checks | DONE | user | WS-09-T02 | 2026-03-18: targeted command set executed with result `51 passed in 4.19s`; evidence recorded in `formal/docs/release/CE_05_POST_SIMPLIFICATION_VERIFICATION_CHECKPOINT_v0.md` | Targeted architecture/authority/seam representative checks pass and are recorded with command evidence |
| WS-09-T04A | Post-Simplification Verification Sweep | Create failing-governance-tranche triage note | DONE | user | none | 2026-03-18: triage note `formal/docs/release/WS_09_T04A_FAILING_GOVERNANCE_TRANCHE_TRIAGE_NOTE_v0.md` recorded exact failing tests, grouped root causes, remediation order, and verification commands | Failing-governance-tranche triage note exists and is linked for bounded remediation |
| WS-09-T04B | Post-Simplification Verification Sweep | Remediate smallest shared governance-tranche root-cause family | DONE | user | WS-09-T04A | 2026-03-18: Family-B subset passed (`2 passed in 0.82s`) and failing-tranche rerun reduced to single residual (`1 failed, 18 passed in 7.66s`); evidence recorded in CE-05 checkpoint artifact | Remaining failing subset reduced from 3 to <=1 with bounded diff evidence |
| WS-09-T04C | Post-Simplification Verification Sweep | Re-run failing subset then canonical governance suite | DONE | user | WS-09-T04B | 2026-03-18: failing-tranche rerun passed (`19 passed in 7.21s`) and unchanged `governance_suite.ps1` rerun passed (`422 passed in 141.30s`) after bounded residual fixes; evidence recorded in CE-05 checkpoint artifact | Green failing subset and green canonical governance suite recorded in CE-05 checkpoint artifact |
| WS-09-T05 | Post-Simplification Verification Sweep | Record CE-05 closure checkpoint | DONE | user | WS-09-T04C | 2026-03-18: CE-05 row marked DONE with full evidence chain in tracker; WS-09 plan task table reflects T05 DONE | CE-05 closure is explicitly recorded and WS-09 closure state is consistent across tracker and WS-09 plan |
| WS-10-T01 | Theory Restart Pilot | Open bounded restart slice and pin first theorem target | DONE | user | none | 2026-03-18: tracker/state/roadmap activation notes and `formal/docs/release/WS_10_THEORY_RESTART_PILOT_PLAN_v0.md` created; bounded validation `5 passed in 2.54s` via `test_state_theory_dag.py`, `test_pillar_matrix_roadmap_coverage_gate.py`, `test_gr01_function_space_completion_criteria_gate.py`, `test_gr01_function_space_discrete_regularity_evidence_gate.py` | Tracker/state/roadmap activation notes exist, first bounded target is pinned, and targeted parity verification is recorded |
| WS-10-T02 | Theory Restart Pilot | Deepen GR01 boundary-term regularity lemma | DONE | user | WS-10-T01 | 2026-03-18: bounded GR01 theorem-surface deepening committed in `da6e6c5`; local verification `3 passed in 1.94s` via `test_gr01_function_space_completion_criteria_gate.py`, `test_gr01_function_space_discrete_regularity_evidence_gate.py`, `test_gr01_publication_grade_discharge_package_gate.py` | GR01 theorem surfaces are deepened with bounded scope and local GR01 verification ladder passes |
| WS-10-T03 | Theory Restart Pilot | Run bounded GR01 verification ladder | DONE | user | WS-10-T02 | 2026-03-18: exact bounded GR01 ladder recorded and green (`3 passed in 1.94s`) | Local GR01 gate results are recorded with exact command and exit status |
| WS-10-T04 | Theory Restart Pilot | Record WS-10 first-slice checkpoint | DONE | user | WS-10-T03 | 2026-03-18: tracker/state/roadmap/WS-10 plan updated to close first pilot phase and select next bounded slice explicitly | First WS-10 pilot phase is closed with evidence and next bounded target is explicit |

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
