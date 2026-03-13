# ToE Seam Status Semantics Standard v0

Spec ID:
- `TOE_SEAM_STATUS_SEMANTICS_STANDARD_v0`

Classification:
- `P-POLICY`

Purpose:
- Separate governance completion from physics completion for cross-pillar seams.
- Prevent class-promotion status from being misread as physics-complete unification.
- Freeze one explicit interpretation layer for seam inventory and seam registry surfaces.

Non-claim boundary:
- semantics-only control surface.
- no seam promotion by itself.
- no theorem promotion by itself.
- no canonical action promotion by itself.

Canonical anchors:
- `formal/docs/paper/TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md`
- `formal/docs/paper/TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md`
- `formal/docs/release/TOE_CLOSURE_SEMANTICS_STANDARD_v0.md`
- `State_of_the_Theory.md`
- `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
- `formal/python/tests/test_toe_seam_status_split_gate.py`

Definitions:
- `governance complete`:
  - required seam registry/inventory rows, promotion package pointers, and gate parity surfaces are pinned for the named seam under current policy scope.
- `physics complete`:
  - theorem-linked shared dynamics, transport, residual compatibility, and regime-limit closure are discharged for the named seam.

Interpretation rule:
- class `A` or `CLASS_A_PROMOTED_*` may imply governance completion for a seam package.
- class `A` does not imply physics completion.
- class `B` may still be governance-tracked, but is not governance-complete unless an explicit completion rule says otherwise.

Required tokens:
- `TOE_SEAM_STATUS_SEMANTICS_STATUS_v0: CANONICAL_PINNED`
- `SEAM_STATUS_CLASS_A_NOT_PHYSICS_COMPLETE_v0: TRUE`
- `SEAM_STATUS_GOVERNANCE_COMPLETE_REQUIRES_CROSS_SURFACE_PARITY_v0: TRUE`