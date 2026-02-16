# Derivation Target: GR01 Symmetry Promotion v0

Spec ID:
- `DERIVATION_TARGET_GR01_SYMMETRY_PROMOTION_v0`

Classification:
- `P-POLICY`

Purpose:
- Freeze one blocker-focused work-order for projection-map/symmetry promotion in GR01.
- Define promotion criteria for `ASM-GR01-SYM-01`.
- Keep all work inside the existing GR01 lane with no comparator-lane expansion.

Non-claim boundary:
- This artifact is planning-only.
- This artifact is a non-claim and does not by itself promote theorem status.
- This artifact does not authorize new comparator lanes.
- This artifact does not claim full GR field-equation recovery.

Symmetry/projection assumption under promotion:
- Assumption ID: `ASM-GR01-SYM-01`.
- Current status: `T-CONDITIONAL`.
- Promotion checkpoint statement: projection-map well-formedness is theorem-conditional via explicit carrier/regime predicate.
- Target ID: `TARGET-GR01-SYM-PROMO-PLAN`.

Canonical pointers:
- `formal/docs/paper/ASSUMPTION_REGISTRY_v1.md`
- `formal/docs/paper/TOE_GR01_ANALYTIC_DISCHARGE_v0.md`
- `formal/toe_formal/ToeFormal/Variational/GR01SymmetryPromotion.lean`
- `formal/toe_formal/ToeFormal/Variational/GR01BridgePromotion.lean`
- `formal/toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean`

Symmetry-promotion theorem tokens (Lean):
- `ProjectionMapWellFormedPredicate`
- `gr01_projection_map_well_formed_under_regime_predicate`
- `gr01_projection_map_well_formed`
- `potential_carrier_defined`
- `source_carrier_defined`
- `weak_field_regime_exists`

Strengthened assumption IDs used by this target:
- `ASM-GR01-REG-01`
- `ASM-GR01-REG-02`

## Acceptable Assumption Strengthening (allowed in this target)

- Explicit carrier-witness assumptions for potential/source projection objects.
- Explicit weak-field regime predicate assumptions needed to keep projection semantics bounded.
- Explicit finite/discrete index-domain assumptions where needed for closure.
- All strengthening must be linked to IDs in `ASSUMPTION_REGISTRY_v1.md`.

Forbidden shortcut:
- No new comparator lane can be introduced as a replacement for theorem-surface projection/symmetry discharge.

## Closure Definition

- Promotion checkpoint (`P-POLICY -> T-CONDITIONAL`) for `ASM-GR01-SYM-01` requires:
  - theorem token `gr01_projection_map_well_formed` in
    `GR01SymmetryPromotion.lean`,
  - `ProjectionMapWellFormed` obligations are witness-carrying and not discharged by
    `⟨trivial, trivial⟩` shortcuts,
  - assumption-row status update in `ASSUMPTION_REGISTRY_v1.md`,
  - synchronized claim/map/paper/state/results wording,
  - unchanged freeze policy: no new comparator lanes authorized.

- Current closure status:
  - checkpoint satisfied for `ASM-GR01-SYM-01` (`T-CONDITIONAL`),
  - weak-field policy blocker list is empty at the assumption-registry level.

## Freeze Policy

- No new comparator lanes are authorized by this target.
- Existing GR01 freeze policy remains in force until derivation-grade analytic discharge checklist criteria are discharged.
