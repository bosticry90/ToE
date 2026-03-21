# Slice A GR-QM Seam Implementation Brief v0

Spec ID:
- `SLICE_A_GR_QM_SEAM_IMPLEMENTATION_BRIEF_v0`

Date:
- `2026-03-20`

Planning boundary:
- This brief is the active bounded execution contract for Slice A.
- It is derived from `SCIENTIFIC_CORE_EXTRACTION_MEMO_v0`.

Non-claim boundary:
- Implementation-planning artifact only.
- No theorem promotion or adjudication change by itself.

## 1) Slice objective

Primary objective:
- Increase theorem-depth on the GR-QM seam by deepening one named theorem bottleneck while keeping the change envelope minimal.

One-line target:
- Convert one tag-transport-heavy seam theorem into a stronger semantics-bearing theorem statement without widening into broad cross-surface governance churn.

## 2) Named theorem bottleneck (first deepen)

Bottleneck theorem to deepen first:
- `gr_qm_cycle03_shared_dynamics_transport_semantics_package`
- Surface: `formal/toe_formal/ToeFormal/Bridges/GR_QM_SeamPromotion.lean`

Why this theorem first:
- It sits at the exact handoff between regime-closure semantics and blocker-discharge packaging in cycle03.
- It is currently a high-leverage location where theorem content can be made less tag-transport-only and more semantics-bearing.
- It is already pinned by cycle03 target and gate surfaces, so deepening here yields immediate measurable effect with minimal file spread.

## 3) Exact files allowed to change

Strict allowed-change envelope for Slice A:

Required edit surfaces:
1. `formal/toe_formal/ToeFormal/Bridges/GR_QM_SeamPromotion.lean`
2. `formal/docs/paper/DERIVATION_TARGET_GR_QM_CLASS_B_SEAM_PROMOTION_CLASS_FLIP_CYCLE03_v0.md`

Conditionally allowed only if test updates are strictly required by theorem-surface delta:
3. `formal/python/tests/test_gr_qm_seam_promotion_cycle03_class_flip_gate.py`

Disallowed by default in Slice A:
- `State_of_the_Theory.md`
- `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
- `formal/docs/paper/TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md`
- `formal/docs/paper/TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md`
- Any non-GR-QM pillar target or gate family
- Any new file creation in governance or registry families

## 4) Minimal gate subset to run

Use only the GR-QM seam minimal ladder:

1. `./py.ps1 -m pytest -q formal/python/tests/test_gr_qm_seam_promotion_cycle03_class_flip_gate.py`
2. `./py.ps1 -m pytest -q formal/python/tests/test_gr_qm_seam_promotion_cycle02_discharge_gate.py`
3. `./py.ps1 -m pytest -q formal/python/tests/test_gr_qm_seam_promotion_cycle01_theorem_gate.py`

Execution note:
- Run in the order above (deepest touched surface first, then immediate lineage guards).
- No full-suite or broad governance run is in-scope for Slice A.

## 5) Explicit stop conditions (anti-widening)

Stop immediately and re-scope if any of the following occur:

1. More than 3 files are required to make Slice A green.
2. Any required change spills into state/roadmap/inventory/registry control surfaces.
3. Any change request introduces a new gate family, new cycle file, or new governance token block.
4. The proof edit in `GR_QM_SeamPromotion.lean` turns into broad refactoring outside cycle03 seam semantics.
5. Gate fixes demand non-GR-QM pillars or non-seam surfaces.

Escalation outcome on stop:
- Record blocker and produce a narrowed Slice A.1 brief before further edits.

## 6) Acceptance criteria

Slice A is complete when all are true:

1. `gr_qm_cycle03_shared_dynamics_transport_semantics_package` has a deeper semantics-bearing theorem formulation in `GR_QM_SeamPromotion.lean`.
2. `DERIVATION_TARGET_GR_QM_CLASS_B_SEAM_PROMOTION_CLASS_FLIP_CYCLE03_v0.md` reflects the updated theorem semantics with no scope expansion.
3. The 3-test minimal GR-QM ladder is green.
4. No disallowed surfaces were touched.
5. No new governance family or broad parity campaign was opened.

## 7) Bounded implementation approach

Edit order:
1. Lean theorem surface first (`GR_QM_SeamPromotion.lean`).
2. Cycle03 target derivation surface second.
3. Gate adjustment only if required.
4. Run minimal ladder and stop.

Change-shape constraint:
- Prefer strengthening theorem content over adding new status-token scaffolding.
- Any doc updates must be derivative of theorem changes, not vice versa.

## 8) Post-slice decision gate

If Slice A completes cleanly:
- Open Slice B only if theorem-depth gain is demonstrated without control-surface widening.

If Slice A hits a stop condition:
- Freeze, publish blocker note, and issue narrowed follow-on brief instead of widening the slice.
