# Slice B GR-QM Seam Implementation Brief v0

Spec ID:
- `SLICE_B_GR_QM_SEAM_IMPLEMENTATION_BRIEF_v0`

Date:
- `2026-03-20`

Boundary anchor:
- Start point commit: `eed0cccb93453183f14a27c6545108fbb6119200`
- Branch posture at open: `main` synced with `origin/main`
- Slice A status: completed and published

Planning boundary:
- This brief opens Slice B from the published Slice A checkpoint.
- Scope stays inside the same GR-QM seam scientific core discipline.

Non-claim boundary:
- Implementation-planning artifact only.
- No theorem promotion or adjudication change by itself.

## 1) Slice B objective

Primary objective:
- Deepen one additional GR-QM seam theorem bottleneck while preserving the anti-widening contract used in Slice A.

One-line target:
- Increase semantic density in the blocker-discharge bridge path without opening any new governance surfaces.

## 2) Named theorem bottleneck (Slice B)

Bottleneck theorem to deepen in Slice B:
- `gr_qm_cycle03_transport_and_regime_closure_blocker_discharge_package`
- Surface: `formal/toe_formal/ToeFormal/Bridges/GR_QM_SeamPromotion.lean`

Why this theorem next:
- It is the immediate downstream consumer of Slice A's strengthened transport theorem.
- It controls the seam blocker-discharge packaging semantics and is the highest-leverage continuation point within the same cycle03 chain.
- It can be deepened without widening to state/roadmap/inventory/registry if the envelope is respected.

## 3) Exact files allowed to change

Strict allowed-change envelope for Slice B:

Required edit surfaces:
1. `formal/toe_formal/ToeFormal/Bridges/GR_QM_SeamPromotion.lean`
2. `formal/docs/paper/DERIVATION_TARGET_GR_QM_CLASS_B_SEAM_PROMOTION_CLASS_FLIP_CYCLE03_v0.md`

Conditionally allowed only if test updates are strictly required by theorem-surface delta:
3. `formal/python/tests/test_gr_qm_seam_promotion_cycle03_class_flip_gate.py`

Disallowed by default in Slice B:
- `State_of_the_Theory.md`
- `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
- `formal/docs/paper/TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md`
- `formal/docs/paper/TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md`
- `formal/docs/release/REPO_REMEDIATION_MASTER_TRACKER_v0.md`
- Any non-GR-QM pillar surface
- Any new governance-family file creation

## 4) Minimal validation ladder (unchanged)

Run only this GR-QM ladder:

1. `./py.ps1 -m pytest -q formal/python/tests/test_gr_qm_seam_promotion_cycle03_class_flip_gate.py`
2. `./py.ps1 -m pytest -q formal/python/tests/test_gr_qm_seam_promotion_cycle02_discharge_gate.py`
3. `./py.ps1 -m pytest -q formal/python/tests/test_gr_qm_seam_promotion_cycle01_theorem_gate.py`

Execution note:
- Keep the same order and same bounded scope as Slice A.
- No broad governance run and no full-suite run in-scope.

## 5) Explicit stop conditions (anti-widening)

Stop immediately and re-scope if any occur:

1. More than 3 files are required to make Slice B green.
2. Any required edit spills into state/roadmap/inventory/registry/tracker surfaces.
3. Any change introduces a new gate family, new cycle file, or new governance token campaign.
4. The Lean edit requires broad refactoring outside cycle03 seam semantics.
5. Gate remediation requires non-GR-QM surfaces.

Escalation outcome on stop:
- Freeze the slice and issue a narrowed `SLICE_B.1` brief before further implementation.

## 6) Acceptance criteria

Slice B is complete when all are true:

1. `gr_qm_cycle03_transport_and_regime_closure_blocker_discharge_package` has a deeper semantics-bearing formulation.
2. `DERIVATION_TARGET_GR_QM_CLASS_B_SEAM_PROMOTION_CLASS_FLIP_CYCLE03_v0.md` mirrors only the theorem-semantic delta.
3. The 3-test GR-QM ladder is green.
4. No disallowed surfaces were touched.
5. No governance-family widening occurred.

## 7) Bounded implementation approach

Edit order:
1. Lean theorem surface first.
2. Cycle03 target doc second.
3. Gate file only if strictly required.
4. Run minimal ladder and stop.

Change-shape rule:
- Theorem content first; doc parity second; no proactive control-surface expansion.

## 8) Post-slice decision gate

If Slice B completes cleanly:
- Decide between one additional GR-QM seam depth increment or a controlled handoff to the next scientific core lane.

If Slice B hits stop conditions:
- Publish blocker note and re-scope narrowly before any further theorem work.
