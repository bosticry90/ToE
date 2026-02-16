# Derivation Target: GR01 Regime Promotion v0

Spec ID:
- `DERIVATION_TARGET_GR01_REGIME_PROMOTION_v0`

Classification:
- `P-POLICY`

Purpose:
- Freeze one blocker-focused work-order for weak-field regime promotion in GR01.
- Define promotion criteria for `ASM-GR01-REG-01`.
- Keep all work inside the existing GR01 lane with no comparator-lane expansion.

Non-claim boundary:
- This artifact is planning-only.
- This artifact is a non-claim and does not by itself promote theorem status.
- This artifact does not authorize new comparator lanes.
- This artifact does not claim full GR field-equation recovery.

Regime assumption under promotion:
- Assumption ID: `ASM-GR01-REG-01`.
- Current status: `T-CONDITIONAL`.
- Promotion checkpoint statement: weak-field regime is theorem-conditional via explicit bound predicate.
- Target ID: `TARGET-GR01-REG-PROMO-PLAN`.

Canonical pointers:
- `formal/docs/paper/ASSUMPTION_REGISTRY_v1.md`
- `formal/docs/paper/TOE_GR01_ANALYTIC_DISCHARGE_v0.md`
- `formal/toe_formal/ToeFormal/Variational/GR01BridgePromotion.lean`
- `formal/toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean`

Regime-promotion theorem tokens (Lean):
- `WeakFieldRegimePredicate`
- `gr01_regime_predicate_under_uniform_bound`

Strengthened assumption IDs used by this target:
- `ASM-GR01-REG-02`

## Acceptable Assumption Strengthening (allowed in this target)

- Explicit uniform bound parameters for potential/source in weak-field scope.
- Explicit regime-bound relation assumptions (`phiBound ≤ regimeBound`, `rhoBound ≤ regimeBound`).
- Explicit finite/discrete index-domain assumptions where needed for closure.
- All strengthening must be linked to IDs in `ASSUMPTION_REGISTRY_v1.md`.

Forbidden shortcut:
- No new comparator lane can be introduced as a replacement for theorem-surface regime discharge.

## Closure Definition

- Promotion checkpoint (`P-POLICY -> T-CONDITIONAL`) for `ASM-GR01-REG-01` requires:
  - theorem token `gr01_regime_predicate_under_uniform_bound` in
    `GR01BridgePromotion.lean`,
  - assumption-row status update in `ASSUMPTION_REGISTRY_v1.md`,
  - synchronized claim/map/paper/state/results wording,
  - unchanged freeze policy: no new comparator lanes authorized.

- Current closure status:
  - checkpoint satisfied for `ASM-GR01-REG-01` (`T-CONDITIONAL`),
  - remaining GR01 blockers are tracked in `TOE_GR01_ANALYTIC_DISCHARGE_v0.md`.

## Freeze Policy

- No new comparator lanes are authorized by this target.
- Existing GR01 freeze policy remains in force until remaining weak-field blockers are promoted or discharged.
