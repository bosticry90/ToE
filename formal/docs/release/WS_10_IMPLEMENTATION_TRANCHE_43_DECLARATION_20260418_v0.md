# WS-10 Implementation Tranche 43 Declaration (2026-04-18)

## Tranche name
WS_10_IMPLEMENTATION_TRANCHE_43_MAINTENANCE_SELECTION_AND_RELEASE_REGISTRY

## Objective
Execute a bounded remediation tranche that selects one repeated pytest gate family for consolidation, indexes one high-volume release-note family into a generated registry surface, and records both selections against the T42 baseline.

## Allowed files
- formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_43_DECLARATION_20260418_v0.md (new)
- formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md (edit)
- formal/output/ws10_t43_maintenance_selection_checkpoint_20260418_v0.json (new, generated)
- formal/output/reports/qft_gr_sliceb_increment_family_registry_20260418_v0.json (new, generated)
- formal/python/tools/ws10_t43_maintenance_selection_report.py (new)
- formal/python/tests/test_ws10_t43_maintenance_selection_gate.py (new)
- State_of_the_Theory.md (edit)
- formal/docs/paper/PHYSICS_ROADMAP_v0.md (edit)

## Out of scope
- theorem-body edits
- seam status class flips or physics-complete status changes
- release-gate truth policy changes
- new packet-family introduction
- authority-source cutover
- live seam execution changes

## Acceptance
1. formal/python/tests/test_ws10_t43_maintenance_selection_gate.py is green.
2. Focused state and roadmap parity bundle is green.
3. The generated checkpoint and release-family registry match current repository state.
4. No live truth semantics are changed by the indexing work.

## Rollback anchor
HEAD_AT_T43_START

## Hard stop rule
If any file outside the Allowed files list changes before acceptance, stop immediately, restore the boundary, and treat the tranche as failed until scope is re-established.

## Boundary freshness note
This tranche is selection-and-indexing only. It does not yet perform authority cutover, direct gate-family replacement, or theorem/seam execution changes.