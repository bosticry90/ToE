# WS_10_THEORY_RESTART_PILOT_PLAN_v0

## Workstream
- ID: WS-10
- Name: Theory Restart Pilot
- Status: ACTIVE
- Priority: PRIMARY

## Objective
Resume post-consolidation theory work through bounded, explicitly checkpointed slices that prove restart can proceed under the CE-06 anti-regrowth guardrails without reopening broad governance churn.

## Scope
In scope:
- pin one bounded restart slice in tracker, state, and roadmap surfaces.
- deepen one GR01 theorem-facing surface with a single nontrivial boundary-term regularity lemma.
- verify the slice through the smallest local gate ladder that matches the touched surfaces.
- record bounded evidence and close the restart activation task explicitly.
- close the first pilot checkpoint before activating a new theory or seam tranche.
- select the next bounded theory slice explicitly in the control surfaces.

Out of scope during WS-10:
- broad seam-physics promotion work.
- new governance-family creation.
- cloned gate expansion.
- authority-residency redistribution without explicit decision.
- broad README or architecture cleanup.

## Restart Slice Target
- Active slice ID: `WS-10-T05_GR_QM_SEAM_DISCHARGE`
- Active pillar: `SEAM-GR-QM`
- Primary target surface: `formal/docs/paper/DERIVATION_TARGET_GR_QM_CLASS_B_SEAM_PROMOTION_DISCHARGE_CYCLE02_v0.md`
- Supporting theorem surfaces:
	- `formal/docs/paper/DERIVATION_TARGET_GR_QM_CLASS_B_SEAM_PROMOTION_CYCLE01_v0.md`
	- `formal/docs/paper/TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md`
	- `formal/docs/paper/TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md`
- Evidence goal: bounded GR-QM seam discharge target is now explicitly activated as the next post-pilot scientific slice without mixing seam work into this activation commit.

## Verification Ladder
1. `./py.ps1 -m pytest -q formal/python/tests/test_state_theory_dag.py formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py`
2. `./py.ps1 -m pytest -q formal/python/tests/test_gr_qm_seam_promotion_cycle02_discharge_gate.py`
3. Optional only if slice activation touches inventory or registry parity surfaces: `./py.ps1 -m pytest -q formal/python/tests/test_gr_qm_seam_promotion_cycle01_theorem_gate.py formal/python/tests/test_gr_qm_seam_promotion_cycle03_class_flip_gate.py`

Execution contract:
- Run tracker/state/roadmap parity checks before theorem-surface edits.
- Keep this activation commit control-surface only and avoid mixing in GR-QM theorem edits.
- Do not expand verification beyond the local gate ladder unless a touched surface forces it.
- Record exact command text and results in the evidence log below.

## Task Plan
| ID | Task | Status | Blocked By | Deliverable | Evidence Required |
| --- | --- | --- | --- | --- | --- |
| WS-10-T01 | Open bounded restart slice and pin first theorem target | DONE | none | Tracker/state/roadmap activation notes plus bounded restart plan artifact | Bounded diff evidence plus targeted parity verification |
| WS-10-T02 | Deepen GR01 boundary-term regularity lemma | DONE | WS-10-T01 | Local theorem-surface deepening in GR01 regularity and support notes | Theorem-surface diff plus local GR01 gate ladder green |
| WS-10-T03 | Run bounded GR01 verification ladder | DONE | WS-10-T02 | Local gate results recorded in artifact | Exact command outputs and exit status |
| WS-10-T04 | Record WS-10 first-slice checkpoint | DONE | WS-10-T03 | Tracker and WS-10 evidence closure note | Commit hash, touched files, and result summary |
| WS-10-T05 | Open next bounded theory slice: GR-QM seam discharge | ACTIVE | WS-10-T04 | Control-surface activation for the GR-QM seam discharge target | Bounded diff evidence plus targeted parity verification |

## Guardrails
- No unnecessary governance-family expansion.
- No cloned gate proliferation where shared or registry patterns already exist.
- No duplicated authority residency without explicit decision.
- Bounded theory slices only.

## Evidence Log
- 2026-03-18 WS-10 kickoff: activated bounded theory restart pilot with first target `TOE_GR01_FUNCTION_SPACE_REGULARITY_SURFACE_v0` and supporting authority pointer set `formal/docs/release/WS_10_THEORY_RESTART_PILOT_PLAN_v0.md`.
- 2026-03-18 WS-10-T01: bounded activation validation passed via `c:/Users/psboy/Documents/ToE/.venv/Scripts/python.exe -m pytest -q formal/python/tests/test_state_theory_dag.py formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py formal/python/tests/test_gr01_function_space_completion_criteria_gate.py formal/python/tests/test_gr01_function_space_discrete_regularity_evidence_gate.py` -> `5 passed in 2.54s`.
- 2026-03-18 WS-10-T02/T03: bounded GR01 theorem-deepening slice committed in `da6e6c5` and validated via `c:/Users/psboy/Documents/ToE/.venv/Scripts/python.exe -m pytest -q formal/python/tests/test_gr01_function_space_completion_criteria_gate.py formal/python/tests/test_gr01_function_space_discrete_regularity_evidence_gate.py formal/python/tests/test_gr01_publication_grade_discharge_package_gate.py` -> `3 passed in 1.94s`.
- 2026-03-18 WS-10-T04: first pilot checkpoint closed with bounded evidence; activation commit `a055921` plus theorem-deepening commit `da6e6c5` now define the first restart phase.
- 2026-03-18 WS-10-T05 selection: next bounded target pinned to `formal/docs/paper/DERIVATION_TARGET_GR_QM_CLASS_B_SEAM_PROMOTION_DISCHARGE_CYCLE02_v0.md` with local gate `formal/python/tests/test_gr_qm_seam_promotion_cycle02_discharge_gate.py` reserved for the next scientific slice.
- 2026-03-18 WS-10-T05 activation: control surfaces promoted the GR-QM seam discharge slice from selected to active and recorded parity validation via `c:/Users/psboy/Documents/ToE/.venv/Scripts/python.exe -m pytest -q formal/python/tests/test_state_theory_dag.py formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py` -> `3 passed in 1.42s`.

## Exit Criteria
- WS-10-T01 activation note is mirrored in the canonical control surfaces and verified.
- WS-10-T02 deepens GR01 theorem content without broadening scope beyond the bounded slice.
- Local GR01 verification ladder passes and is recorded.
- The first restart slice closes with explicit evidence and no governance-family regrowth.
- The next bounded theory slice is explicitly selected before any additional theorem or seam work begins.
- The active next slice is explicitly activated in the control surfaces before any GR-QM scientific edits begin.