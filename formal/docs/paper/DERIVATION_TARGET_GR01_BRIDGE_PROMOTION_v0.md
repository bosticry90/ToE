# Derivation Target: GR01 Bridge Promotion v0

Spec ID:
- `DERIVATION_TARGET_GR01_BRIDGE_PROMOTION_v0`

Classification:
- `P-POLICY`

Purpose:
- Freeze one blocker-focused work-order for the GR01 emergence bridge.
- Define promotion criteria for `ASM-GR01-APP-02` (`ELImpliesDiscretePoissonResidual`).
- Keep bridge-promotion work inside the existing GR01 lane with no expansion to new comparator lanes.

Non-claim boundary:
- This artifact is planning-only.
- This artifact is a non-claim and does not by itself promote theorem status.
- This artifact does not authorize new comparator lanes.
- This artifact does not claim Einstein-field-equation recovery or full GR emergence.

Bridge under promotion:
- Assumption ID: `ASM-GR01-APP-02`.
- Current status: `T-CONDITIONAL`.
- Promotion checkpoint statement: modeling bridge is theorem-conditional via `gr01_discrete_residual_from_bridge_promotion_chain`.
- Target ID: `TARGET-GR01-BRIDGE-PROMO-PLAN`.

Canonical pointers:
- `formal/docs/paper/ASSUMPTION_REGISTRY_v1.md`
- `formal/docs/paper/TOE_GR01_PROJECTION_BRIDGE_SPEC_v0.md`
- `formal/docs/paper/TOE_GR01_ANALYTIC_DISCHARGE_v0.md`
- `formal/toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean`
- `formal/toe_formal/ToeFormal/Variational/GR01BridgePromotion.lean`

Bridge-promotion theorem tokens (Lean):
- `WeakFieldUniformBound`
- `FirstOrderRemainderSuppressed`
- `ELImpliesOperatorResidualUnderBound`
- `gr01_operator_residual_from_bound_bridge_assumptions`
- `gr01_discrete_residual_from_bridge_promotion_chain`

Strengthened assumption IDs used by this target:
- `ASM-GR01-REG-02`
- `ASM-GR01-APP-03`
- `ASM-GR01-APP-04`

## Promotion Strategy Options

1. Preferred route: discharged lemma chain
- Prove a theorem-level bridge chain that implies `ELImpliesDiscretePoissonResidual`.
- Keep assumptions explicit and theorem-signature visible.
- Preserve `OperatorToDiscreteResidual` as transport-only bookkeeping.

2. Fallback route: sharply delimited postulate freeze
- Keep bridge postulate explicit but narrow its scope (domain/regime/boundary) in theorem-adjacent docs.
- This route may close blocker documentation quality but does not count as theorem discharge.
- No claim-label upgrade is allowed from this route alone.

## Acceptable Assumption Strengthening (allowed in this target)

- Strengthen weak-field truncation assumptions with explicit order bounds.
- Strengthen projection-map regularity/consistency assumptions with explicit boundary compatibility.
- Strengthen source/potential identification assumptions with explicit normalization conventions.
- Add explicit finite-support/discrete-domain restrictions if required for proof closure.
- Keep all strengthened assumptions linked to IDs in `ASSUMPTION_REGISTRY_v1.md`.

Forbidden shortcut:
- Introducing a new comparator lane as a substitute for theorem/analytic bridge work is disallowed.

## Theorem-Surface Contract (bridge-focused)

Minimum contract objective:
- Produce a theorem-level statement that has the shape:
  - from explicit bridge assumptions and EL/core conditions,
  - conclude `DiscretePoissonResidual1D ... = 0`.

Contract requirements:
- non-vacuous theorem signature,
- explicit assumptions (no hidden assumptions),
- no legacy `ELImpliesProjectedResidual` dependency,
- consistent with `WeakFieldProjectionFromCore` discrete-only output,
- theorem-level chain exports are token-pinned in gates.

## Closure Definition

- Promotion checkpoint (`P-POLICY -> T-CONDITIONAL`) for `ASM-GR01-APP-02` requires:
  - a theorem-level bridge lemma chain (Lean) in `GR01BridgePromotion.lean`,
  - bridge theorem token `gr01_discrete_residual_from_bridge_promotion_chain`,
  - assumption IDs updated in `ASSUMPTION_REGISTRY_v1.md`,
  - synchronized updates across claim/map/paper/state/results surfaces,
  - unchanged freeze policy: no new comparator lanes authorized.

- Current closure status:
  - checkpoint satisfied (`ASM-GR01-APP-02` is `T-CONDITIONAL`),
  - remaining GR01 blockers are tracked outside this target in `TOE_GR01_ANALYTIC_DISCHARGE_v0.md`.

## Freeze Policy

- No new comparator lanes are authorized by this target.
- Existing GR01 freeze policy remains in force until blocker promotion is completed.
