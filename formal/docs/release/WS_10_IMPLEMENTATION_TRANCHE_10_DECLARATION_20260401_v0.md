# WS-10 Implementation Tranche 10 Declaration (2026-04-01)

## Tranche name
WS_10_IMPLEMENTATION_TRANCHE_10_QFT_GR_SEAM_REACTIVATION_INCREMENT67_RESTART

## Objective
Open a fresh declaration-first science tranche and implement exactly one bounded, non-claim QFT/GR Slice-B Increment67 semantic/physics delta plus its immediately adjacent synthesis checkpoint from the clean synced anchor, preserving the four-file boundary and clean-tree acceptance protocol.

## Allowed files
- `formal/docs/paper/DERIVATION_TARGET_QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT67_v0.md` (new)
- `formal/docs/paper/DERIVATION_TARGET_QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT66_TO_67_SYNTHESIS_v0.md` (new)
- `formal/python/tests/test_qft_gr_seam_reactivation_sliceb_increment67_gate.py` (new)
- `formal/python/tests/test_qft_gr_seam_reactivation_sliceb_increment66_to_67_synthesis_gate.py` (new)

## Out of scope
- all authority/parity surfaces, including `State_of_the_Theory.md` and `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
- `checkpoint_ladder.ps1`, governance protocol docs, and growth-lock artifacts
- empirical comparator recovery
- any schema or lock-file edits
- any new lane creation
- edits to existing increment01-66 content except where cited by the new tranche files
- broad template normalization or unrelated governance refactors

## Acceptance
1. The two new tranche-local gate files are green.
2. Full `formal/python/tests` suite is green.
3. `./checkpoint_ladder.ps1` is green end-to-end.
4. Generated outputs are restored as needed and the working tree is clean afterward.

## Rollback anchor
bbe6aac

## Hard stop rule
If any file outside the Allowed files list changes before acceptance, stop immediately, revert the drift, and treat the tranche as failed until the boundary is restored.

## Boundary freshness note
This declaration supersedes reuse of the prior failed science declaration boundary and rebinds the deferred science tranche to clean synced anchor `bbe6aac`.