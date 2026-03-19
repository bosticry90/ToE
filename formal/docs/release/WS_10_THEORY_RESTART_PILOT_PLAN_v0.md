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
- Active slice ID: `WS-10-T05_GR_QM_COMPLETION_PARITY_WIDER_TRANCHE`
- Active pillar: `SEAM-GR-QM`
- Handoff anchor: `e118b72`
- Primary tranche target surfaces:
	- `formal/docs/paper/DERIVATION_TARGET_GR_QM_CLASS_B_SEAM_PROMOTION_DISCHARGE_CYCLE02_v0.md`
	- `formal/docs/paper/DERIVATION_TARGET_GR_QM_CLASS_B_SEAM_PROMOTION_CLASS_FLIP_CYCLE03_v0.md`
	- `formal/toe_formal/ToeFormal/Bridges/GR_QM_SeamPromotion.lean`
- Declared wider-baseline control surfaces:
	- `formal/docs/paper/TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md`
	- `formal/docs/paper/TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md`
- Evidence goal: wider GR-QM completion-parity tranche is explicitly activated from the `e118b72` checkpoint boundary so bounded regime-closure semantics work can run against a named inventory/registry-aware baseline rather than the prior same-lane exception posture.

## Verification Ladder
1. `./py.ps1 -m pytest -q formal/python/tests/test_state_theory_dag.py formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py`
2. `./py.ps1 -m pytest -q formal/python/tests/test_gr_qm_seam_promotion_cycle01_theorem_gate.py formal/python/tests/test_gr_qm_seam_promotion_cycle02_discharge_gate.py formal/python/tests/test_gr_qm_seam_promotion_cycle03_class_flip_gate.py formal/python/tests/test_toe_master_action_class_b_inventory_gate.py formal/python/tests/test_toe_master_action_seam_registry_gate.py`
3. No broader validation expansion unless this five-gate baseline itself forces a further named authorization step.

Execution contract:
- Run tracker/state/roadmap parity checks before theorem-surface edits.
- Keep this activation commit control-surface only and avoid mixing in GR-QM theorem edits.
- Keep tranche scientific edits confined to `DERIVATION_TARGET_GR_QM_CLASS_B_SEAM_PROMOTION_DISCHARGE_CYCLE02_v0.md`, `DERIVATION_TARGET_GR_QM_CLASS_B_SEAM_PROMOTION_CLASS_FLIP_CYCLE03_v0.md`, and `GR_QM_SeamPromotion.lean`.
- Do not widen the scientific file set in the first widened slice; the widening is in the declared baseline, not in silent surface spread.
- First widened scientific slice must validate against the five-gate ladder before any further tranche decision is considered.
- Stop immediately once the first widened slice lands unless that five-gate baseline itself forces a new explicit decision.
- Record exact command text and results in the evidence log below.

## Task Plan
| ID | Task | Status | Blocked By | Deliverable | Evidence Required |
| --- | --- | --- | --- | --- | --- |
| WS-10-T01 | Open bounded restart slice and pin first theorem target | DONE | none | Tracker/state/roadmap activation notes plus bounded restart plan artifact | Bounded diff evidence plus targeted parity verification |
| WS-10-T02 | Deepen GR01 boundary-term regularity lemma | DONE | WS-10-T01 | Local theorem-surface deepening in GR01 regularity and support notes | Theorem-surface diff plus local GR01 gate ladder green |
| WS-10-T03 | Run bounded GR01 verification ladder | DONE | WS-10-T02 | Local gate results recorded in artifact | Exact command outputs and exit status |
| WS-10-T04 | Record WS-10 first-slice checkpoint | DONE | WS-10-T03 | Tracker and WS-10 evidence closure note | Commit hash, touched files, and result summary |
| WS-10-T05 | Hold wider GR-QM tranche at regime-closure semantics checkpoint | ACTIVE | WS-10-T04 | Control-surface activation anchored on `e118b72`, explicit five-gate validation ladder, first widened scientific checkpoint, and bounded regime-closure semantics increment under the declared baseline | Bounded diff evidence plus targeted parity verification |

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
- 2026-03-18 WS-10-T05 scientific increment 1: commit `6adf4a3` added the bounded cycle02 bridge increment and local validation via `c:/Users/psboy/Documents/ToE/.venv/Scripts/python.exe -m pytest -q formal/python/tests/test_gr_qm_seam_promotion_cycle02_discharge_gate.py` -> `1 passed in 0.73s`.
- 2026-03-18 WS-10-T05 scientific increment 2: commit `f587707` added the cycle02 compatibility-persistence corollary and local validation via `c:/Users/psboy/Documents/ToE/.venv/Scripts/python.exe -m pytest -q formal/python/tests/test_gr_qm_seam_promotion_cycle02_discharge_gate.py` -> `1 passed in 0.75s`.
- 2026-03-18 WS-10-T05 scientific increment 3: commit `4b74614` added the cycle02 retention transport corollary and local validation via `c:/Users/psboy/Documents/ToE/.venv/Scripts/python.exe -m pytest -q formal/python/tests/test_gr_qm_seam_promotion_cycle02_discharge_gate.py` -> `1 passed in 0.75s`.
- 2026-03-18 WS-10-T05 progress checkpoint: three bounded cycle02-local increments are now recorded and widening to `formal/python/tests/test_gr_qm_seam_promotion_cycle01_theorem_gate.py` plus `formal/python/tests/test_gr_qm_seam_promotion_cycle03_class_flip_gate.py` remains deferred unless shared-coupling changes.
- 2026-03-18 WS-10-T05 widened validation checkpoint: `c:/Users/psboy/Documents/ToE/.venv/Scripts/python.exe -m pytest -q formal/python/tests/test_gr_qm_seam_promotion_cycle01_theorem_gate.py formal/python/tests/test_gr_qm_seam_promotion_cycle02_discharge_gate.py formal/python/tests/test_gr_qm_seam_promotion_cycle03_class_flip_gate.py` -> `3 passed in 1.95s`; no hidden cross-lane coupling detected in the shared `GR_QM_SeamPromotion.lean` bridge surface.
- 2026-03-18 WS-10-T05 broader scientific slice: commit `bf9a5fe` added the first cross-cycle authorization bridge linking cycle02 retention transport to the cycle03 authorization surface and validated it via `c:/Users/psboy/Documents/ToE/.venv/Scripts/python.exe -m pytest -q formal/python/tests/test_gr_qm_seam_promotion_cycle01_theorem_gate.py formal/python/tests/test_gr_qm_seam_promotion_cycle02_discharge_gate.py formal/python/tests/test_gr_qm_seam_promotion_cycle03_class_flip_gate.py` -> `3 passed in 2.10s`.
- 2026-03-18 WS-10-T05 multi-cycle checkpoint: GR-QM has advanced from cycle02-local foundation work into bounded multi-cycle authorization structure and the standing local validation baseline is now the widened three-gate GR-QM ladder.
- 2026-03-18 WS-10-T05 broader scientific slice: commit `24422a7` added the authorization-retention bridge as a second bounded cross-cycle theorem and validated it via `c:/Users/psboy/Documents/ToE/.venv/Scripts/python.exe -m pytest -q formal/python/tests/test_gr_qm_seam_promotion_cycle01_theorem_gate.py formal/python/tests/test_gr_qm_seam_promotion_cycle02_discharge_gate.py formal/python/tests/test_gr_qm_seam_promotion_cycle03_class_flip_gate.py` -> `3 passed in 2.00s`.
- 2026-03-18 WS-10-T05 tranche-decision checkpoint: the GR-QM lane now has a stable widened three-gate baseline plus a two-object broader cross-cycle theorem chain, so the next slice should be opened deliberately as a larger discharge tranche unless one last same-lane theorem is equally clean and still confined to the same three-file, three-gate scope.
- 2026-03-19 WS-10-T05 larger-tranche activation: the tranche-decision boundary at `0d023e1` is now converted into the active bounded slice `WS-10-T05_GR_QM_LARGER_DISCHARGE_TRANCHE`, restricted to the cycle02 discharge target, the cycle03 class-flip target, and the shared `formal/toe_formal/ToeFormal/Bridges/GR_QM_SeamPromotion.lean` surface under the standing three-gate ladder; control-surface parity validation via `c:/Users/psboy/Documents/ToE/.venv/Scripts/python.exe -m pytest -q formal/python/tests/test_state_theory_dag.py formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py` -> `3 passed in 1.41s`.
- 2026-03-19 WS-10-T05 first larger scientific increment checkpoint: activation commit `ad6ca2b` is now followed by bounded scientific commit `1f37ccc`, which added the cycle02 handoff-readiness contract plus the cycle03 class-flip-ready package theorem inside the same two target docs and shared `formal/toe_formal/ToeFormal/Bridges/GR_QM_SeamPromotion.lean` surface; standing ladder validation via `c:/Users/psboy/Documents/ToE/.venv/Scripts/python.exe -m pytest -q formal/python/tests/test_gr_qm_seam_promotion_cycle01_theorem_gate.py formal/python/tests/test_gr_qm_seam_promotion_cycle02_discharge_gate.py formal/python/tests/test_gr_qm_seam_promotion_cycle03_class_flip_gate.py` -> `3 passed in 2.00s`; stop conditions were respected because no control-surface or inventory/registry edits were required and no widening beyond the standing three-gate ladder occurred.
- 2026-03-19 WS-10-T05 checkpoint parity rerun: control-surface checkpoint validation via `c:/Users/psboy/Documents/ToE/.venv/Scripts/python.exe -m pytest -q formal/python/tests/test_state_theory_dag.py formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py` -> `3 passed in 1.38s`.
- 2026-03-19 WS-10-T05 second same-lane increment checkpoint: bounded scientific commit `32cd56c` added the cycle03 normalized class-flip package theorem inside the same two target docs and shared `formal/toe_formal/ToeFormal/Bridges/GR_QM_SeamPromotion.lean` surface; standing ladder validation via `c:/Users/psboy/Documents/ToE/.venv/Scripts/python.exe -m pytest -q formal/python/tests/test_gr_qm_seam_promotion_cycle01_theorem_gate.py formal/python/tests/test_gr_qm_seam_promotion_cycle02_discharge_gate.py formal/python/tests/test_gr_qm_seam_promotion_cycle03_class_flip_gate.py` -> `3 passed in 2.08s`; stop conditions were again respected because no control-surface, inventory, or registry edits were required and no widening beyond the standing three-gate ladder occurred.
- 2026-03-19 WS-10-T05 second checkpoint parity rerun: control-surface checkpoint validation via `c:/Users/psboy/Documents/ToE/.venv/Scripts/python.exe -m pytest -q formal/python/tests/test_state_theory_dag.py formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py` -> `3 passed in 1.35s`.
- 2026-03-19 WS-10-T05 wider-tranche authorization: control surfaces now convert the post-`32cd56c` stop boundary into explicit wider tranche `WS-10-T05_GR_QM_COMPLETION_PARITY_WIDER_TRANCHE`, still bounded to the same GR-QM scientific files but with declared control-surface parity through `formal/docs/paper/TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md` and `formal/docs/paper/TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md`; the standing widened scientific baseline is now the five-gate ladder formed by the three GR-QM theorem gates plus `formal/python/tests/test_toe_master_action_class_b_inventory_gate.py` and `formal/python/tests/test_toe_master_action_seam_registry_gate.py`.
- 2026-03-19 WS-10-T05 widened-slice checkpoint: widened activation ladder validation via `c:/Users/psboy/Documents/ToE/.venv/Scripts/python.exe -m pytest -q formal/python/tests/test_state_theory_dag.py formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py formal/python/tests/test_gr_qm_seam_promotion_cycle01_theorem_gate.py formal/python/tests/test_toe_master_action_class_b_inventory_gate.py formal/python/tests/test_toe_master_action_seam_registry_gate.py` -> `8 passed in 3.21s`; first widened scientific slice validation via `c:/Users/psboy/Documents/ToE/.venv/Scripts/python.exe -m pytest -q formal/python/tests/test_gr_qm_seam_promotion_cycle01_theorem_gate.py formal/python/tests/test_gr_qm_seam_promotion_cycle02_discharge_gate.py formal/python/tests/test_gr_qm_seam_promotion_cycle03_class_flip_gate.py formal/python/tests/test_toe_master_action_class_b_inventory_gate.py formal/python/tests/test_toe_master_action_seam_registry_gate.py` -> `7 passed in 3.09s`; the widened slice adds the cycle03 completion-parity package theorem under the same authorized GR-QM scientific surfaces, and the stop condition remains unchanged: no new surfaces beyond the authorized GR-QM tranche without another explicit authorization.
- 2026-03-19 WS-10-T05 regime-closure checkpoint: bounded regime-closure semantics validation via `c:/Users/psboy/Documents/ToE/.venv/Scripts/python.exe -m pytest -q formal/python/tests/test_gr_qm_seam_promotion_cycle01_theorem_gate.py formal/python/tests/test_gr_qm_seam_promotion_cycle02_discharge_gate.py formal/python/tests/test_gr_qm_seam_promotion_cycle03_class_flip_gate.py formal/python/tests/test_toe_master_action_class_b_inventory_gate.py formal/python/tests/test_toe_master_action_seam_registry_gate.py` -> `7 passed in 3.40s`; the increment adds the cycle03 regime-closure semantics package theorem under the same authorized GR-QM scientific surfaces, and the stop condition remains unchanged: no new surfaces beyond the authorized GR-QM tranche without another explicit authorization.

## Exit Criteria
- WS-10-T01 activation note is mirrored in the canonical control surfaces and verified.
- WS-10-T02 deepens GR01 theorem content without broadening scope beyond the bounded slice.
- Local GR01 verification ladder passes and is recorded.
- The first restart slice closes with explicit evidence and no governance-family regrowth.
- The next bounded theory slice is explicitly selected before any additional theorem or seam work begins.
- The active next slice is explicitly activated in the control surfaces before any GR-QM scientific edits begin.
- WS-10-T05 progress checkpoints must record bounded GR-QM local increments, local validation evidence, and the current decision on whether validation widening remains deferred.
- When a widened GR-QM validation ladder is run, the result must explicitly record whether hidden coupling was detected before broader scientific scope is authorized.
- When a broader GR-QM multi-cycle bridge slice lands, the checkpoint must record the scientific scope transition and the standing widened validation baseline before the next seam theorem slice begins.
- Once the broader GR-QM lane contains more than one cross-cycle theorem object under the standing widened baseline, the next checkpoint must elevate the decision to tranche level unless an equally clean same-lane theorem remains available inside the same three-file, three-gate scope.
- Once tranche-level activation is recorded, all further GR-QM work in WS-10-T05 must remain inside the two target docs plus `GR_QM_SeamPromotion.lean`, use the standing three-gate ladder, and halt at tranche completion or the predeclared same-lane exception boundary.
- Once the first larger-tranche scientific increment is checkpointed, any next same-lane GR-QM increment must still remain inside the same two target docs plus `GR_QM_SeamPromotion.lean` and use the same standing three-gate ladder unless that ladder itself forces an explicit widening decision.
- Once the second same-lane GR-QM increment is checkpointed, the next move must be either explicit wider-tranche authorization with a new validation baseline or an explicit stop; no third same-lane increment is authorized by default.
- Once the wider tranche is explicitly authorized, the first widened GR-QM scientific slice must pass the declared five-gate ladder before any further tranche broadening or adjacent-surface expansion is considered.
- Once the first widened GR-QM scientific slice is checkpointed, the next step must be a deliberate target choice under the same five-gate baseline, with no new surfaces beyond the authorized GR-QM tranche unless explicit reauthorization is recorded first.
- Once a bounded regime-closure semantics increment is checkpointed under the widened tranche, the next step must again be a deliberate target choice under the same five-gate baseline, with no new surfaces beyond the authorized GR-QM tranche unless explicit reauthorization is recorded first.