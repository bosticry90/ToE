# Derivation Target: GR01 Scaling Promotion v0

Spec ID:
- `DERIVATION_TARGET_GR01_SCALING_PROMOTION_v0`

Classification:
- `P-POLICY`

Purpose:
- Freeze one blocker-focused work-order for first-order scaling promotion in GR01.
- Define promotion criteria for `ASM-GR01-APP-01`.
- Keep all work inside the existing GR01 lane with no comparator-lane expansion.

Non-claim boundary:
- This artifact is planning-only.
- This artifact is a non-claim and does not by itself promote theorem status.
- This artifact does not authorize new comparator lanes.
- This artifact does not claim full GR field-equation recovery.

Scaling assumption under promotion:
- Assumption ID: `ASM-GR01-APP-01`.
- Current status: `T-CONDITIONAL`.
- Promotion checkpoint statement: first-order scaling/truncation is theorem-conditional under explicit scaling and remainder assumptions.
- Target ID: `TARGET-GR01-SCALING-PROMO-PLAN`.

Canonical pointers:
- `formal/docs/paper/ASSUMPTION_REGISTRY_v1.md`
- `formal/docs/paper/TOE_GR01_ANALYTIC_DISCHARGE_v0.md`
- `formal/toe_formal/ToeFormal/Variational/GR01ScalingPromotion.lean`
- `formal/toe_formal/ToeFormal/Variational/GR01BridgePromotion.lean`
- `formal/toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean`

Scaling-promotion theorem tokens (Lean):
- `WeakFieldScalingHierarchy`
- `HigherOrderTermsNegligible`
- `gr01_scaling_hierarchy_under_regime_predicate`
- `gr01_first_order_truncation_sound`

Strengthened assumption IDs used by this target:
- `ASM-GR01-REG-01`
- `ASM-GR01-REG-02`
- `ASM-GR01-APP-03`

## Acceptable Assumption Strengthening (allowed in this target)

- Explicit scaling coefficients and dominance bounds for retained first-order sectors.
- Explicit higher-order remainder bound assumptions and zero-scale closure assumptions.
- Explicit finite/discrete index-domain assumptions where needed for closure.
- All strengthening must be linked to IDs in `ASSUMPTION_REGISTRY_v1.md`.

Forbidden shortcut:
- No new comparator lane can be introduced as a replacement for theorem-surface scaling discharge.

## Closure Definition

- Promotion checkpoint (`P-POLICY -> T-CONDITIONAL`) for `ASM-GR01-APP-01` requires:
  - theorem token `gr01_first_order_truncation_sound` in
    `GR01ScalingPromotion.lean`,
  - assumption-row status update in `ASSUMPTION_REGISTRY_v1.md`,
  - synchronized claim/map/paper/state/results wording,
  - unchanged freeze policy: no new comparator lanes authorized.

- Current closure status:
  - checkpoint satisfied for `ASM-GR01-APP-01` (`T-CONDITIONAL`),
  - remaining GR01 blocker is tracked in `TOE_GR01_ANALYTIC_DISCHARGE_v0.md`.

## Freeze Policy

- No new comparator lanes are authorized by this target.
- Existing GR01 freeze policy remains in force until remaining weak-field blockers are promoted or discharged.
