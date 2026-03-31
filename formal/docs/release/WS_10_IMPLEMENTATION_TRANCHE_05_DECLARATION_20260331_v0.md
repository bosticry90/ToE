# WS-10 Implementation Tranche 05 Declaration (2026-03-31)

## Tranche name
WS_10_IMPLEMENTATION_TRANCHE_05_QFT_GR_SEAM_REACTIVATION_INCREMENT66_REOPEN

## Objective
Reopen the deferred QFT/GR Slice-B science tranche and implement exactly one bounded, non-claim Increment66 semantic/physics delta plus its immediately adjacent synthesis checkpoint, without widening scope beyond the declared four-file boundary.

## Allowed files
- formal/docs/paper/DERIVATION_TARGET_QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT66_v0.md (new)
- formal/docs/paper/DERIVATION_TARGET_QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT65_TO_66_SYNTHESIS_v0.md (new)
- formal/python/tests/test_qft_gr_seam_reactivation_sliceb_increment66_gate.py (new)
- formal/python/tests/test_qft_gr_seam_reactivation_sliceb_increment65_to_66_synthesis_gate.py (new)

## Out of scope
- all authority/parity surfaces, including State_of_the_Theory.md and PHYSICS_ROADMAP_v0.md
- checkpoint_ladder.ps1 and governance protocol docs
- empirical comparator recovery
- any schema or growth-lock edits
- any new lane creation
- edits to existing increment01-65 content except where cited by the new tranche files
- broad template normalization or unrelated governance refactors

## Acceptance
1. New tranche-local gate files are green.
2. Full formal/python/tests suite is green.
3. ./checkpoint_ladder.ps1 is green end-to-end.
4. Generated outputs are restored as needed and the working tree is clean afterward.

## Rollback anchor
b06e026

## Hard stop rule
If any file outside the Allowed files list changes before acceptance, stop immediately, revert the drift, and treat the tranche as failed until the boundary is restored.