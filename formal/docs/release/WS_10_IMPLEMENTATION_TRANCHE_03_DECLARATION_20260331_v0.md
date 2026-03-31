# WS-10 Implementation Tranche 03 Declaration (2026-03-31)

## Tranche name
WS_10_IMPLEMENTATION_TRANCHE_03_QFT_GR_SEAM_REACTIVATION_INCREMENT66

## Objective
Create one small science-facing, non-claim QFT/GR seam reactivation Slice-B increment that captures exactly one new bounded semantic/physics delta and its immediately adjacent synthesis checkpoint, without widening scope beyond the declared lane.

## Allowed files
- formal/docs/paper/DERIVATION_TARGET_QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT66_v0.md (new)
- formal/docs/paper/DERIVATION_TARGET_QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT65_TO_66_SYNTHESIS_v0.md (new)
- formal/python/tests/test_qft_gr_seam_reactivation_sliceb_increment66_gate.py (new)
- formal/python/tests/test_qft_gr_seam_reactivation_sliceb_increment65_to_66_synthesis_gate.py (new)

## Out of scope
- all authority/parity surfaces, including State_of_the_Theory.md and PHYSICS_ROADMAP_v0.md
- checkpoint_ladder.ps1 and governance protocol docs
- empirical comparator recovery
- any new lane creation
- edits to existing increment01-65 science content except where explicitly referenced by the new tranche files
- broad template normalization or unrelated governance refactors

## Acceptance
1. New tranche-local gate files are green.
2. Full formal/python/tests suite is green.
3. ./checkpoint_ladder.ps1 is green end-to-end.
4. Generated outputs are restored as needed and the working tree is clean afterward.

## Rollback anchor
1c239c4

## Hard stop rule
If any file outside the Allowed files list changes during this tranche, stop immediately, revert the drift, and treat the tranche as failed until the boundary is restored.
