# WS-10 Implementation Tranche 44 Declaration (2026-04-18)

## Tranche name
WS_10_IMPLEMENTATION_TRANCHE_44_QM_STAT_DIRECT_CYCLE_HELPER_CONSOLIDATION

## Objective
Execute the first real maintenance-reduction slice after T43 by collapsing the QM-STAT direct-cycle gate family onto a shared helper while preserving wrapper filenames, truth semantics, and the bespoke bootstrap/candidate boundary at cycles 01 and 12.

## Allowed files
- formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_44_DECLARATION_20260418_v0.md (new)
- formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md (edit)
- formal/output/ws10_t44_qm_stat_direct_cycle_consolidation_checkpoint_20260418_v0.json (new, generated)
- formal/python/tools/ws10_t44_qm_stat_direct_cycle_consolidation_report.py (new)
- formal/python/tests/qm_stat_class_b_cycle_gate_family_helper.py (new)
- formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle02_gate.py (edit)
- formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle03_gate.py (edit)
- formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle04_gate.py (edit)
- formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle05_gate.py (edit)
- formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle06_gate.py (edit)
- formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle07_gate.py (edit)
- formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle08_gate.py (edit)
- formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle09_gate.py (edit)
- formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle10_gate.py (edit)
- formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle11_gate.py (edit)
- formal/python/tests/test_ws10_t44_qm_stat_direct_cycle_consolidation_gate.py (new)
- State_of_the_Theory.md (edit)
- formal/docs/paper/PHYSICS_ROADMAP_v0.md (edit)

## Out of scope
- synthesis gate consolidation
- cycle01 bootstrap gate changes
- cycle12 candidate contract changes
- theorem-body edits
- seam status class flips or physics-complete status changes
- release-gate truth policy changes
- operator truth-pack generation

## Acceptance
1. The helperized QM-STAT direct-cycle gate family remains green.
2. formal/python/tests/test_ws10_t44_qm_stat_direct_cycle_consolidation_gate.py is green.
3. The generated checkpoint matches current repository state.
4. The reduction is measured against the T43-selected family without changing live truth semantics.

## Rollback anchor
HEAD_AT_T44_START

## Hard stop rule
If any file outside the Allowed files list changes before acceptance, stop immediately, restore the boundary, and treat the tranche as failed until scope is re-established.

## Boundary freshness note
This tranche helperizes only the direct-cycle family members selected in T43. It preserves cycle01 bootstrap behavior, cycle12 candidate status, and all synthesis gates for a later bounded slice.