# Derivation Target: GR Conservation Object v0

Spec ID:
- `DERIVATION_TARGET_GR_CONSERVATION_OBJECT_v0`

Classification:
- `P-POLICY`

Purpose:
- Freeze a planning-only target for the GR conservation-object structural layer.
- Convert `TARGET-GR-CONS-PLAN` into an auditable work-order artifact.
- Define minimal closure criteria without authorizing new comparator lanes.

Non-claim boundary:
- This artifact is planning-only.
- This artifact is a non-claim and does not promote theorem/evidence status.
- This artifact does not substitute for derivations or theorem discharge.
- This artifact does not authorize new comparator lanes.
- This artifact does not claim Einstein-equation recovery.
- This artifact does not claim Noether theorem derivation.

Target scope:
- Pillar: `PILLAR-GR`.
- Structural object: conservation object (flow/divergence/conserved-quantity scaffolding).
- Map linkage: `TARGET-GR-CONS-PLAN` in `STRUCTURAL_CLOSENESS_MAP_v0`.
- Minimal GR01 compatibility blocker surface:
  - `formal/docs/paper/TOE_GR01_CONSERVATION_COMPATIBILITY_v0.md`
  - result-row token: `TOE-GR-CONS-01`

Canonical Lean target (contract-only):
- Module: `formal/toe_formal/ToeFormal/GR/ConservationContract.lean`
- Theorem surface: `gr_conservation_under_contract_assumptions`
- Additional v0 compatibility theorem token:
  - `gr01_conservation_compatibility_from_poisson_residual_v0`
  - `gr01_conservation_compatibility_from_bridge_promotion_chain_v0`
- Lean header posture tokens: `Contract-only theorem surface.` and
  `No GR field-equation claim and no external truth claim.`

## Minimum Structural Objects Required

1. Flow context object
- Typed flow carrier used by conservation contracts.

2. Divergence operator object
- Typed divergence placeholder over scalar-density carriers.

3. Conserved quantity object
- Typed density carrier for conservation predicates.

4. Conservation contract surface
- Explicit theorem-shaped contract for conservation-law form under declared assumptions.

## Theorem-Surface Contract (Future `T-CONDITIONAL` Target)

- Current contract surface in Lean:
  - typed objects: `FlowContext`, `DivergenceOperator`, `ConservedQuantity`
  - proposition: `ConservationLawUnderFlow`
  - theorem: `gr_conservation_under_contract_assumptions`
  - compatibility theorem: `gr01_conservation_compatibility_from_poisson_residual_v0`
- The theorem contract:
  - consumes explicit assumptions,
  - avoids hidden assumptions and vacuous outputs,
  - remains non-claim and contract-only in v0.

## Closure Definition

- `ABSENT -> P-POLICY` (planning closure):
  - this spec exists,
  - map pointer is wired,
  - claim/paper/state surfaces reference it as planning-only,
  - gate checks enforce non-claim/no-promotion wording.

- `P-POLICY -> T-CONDITIONAL` (theorem-surface closure):
  - Lean theorem surface in `formal/toe_formal/ToeFormal/GR/ConservationContract.lean` exists with explicit assumptions and non-vacuity checks,
  - theorem token `gr_conservation_under_contract_assumptions` is test-pinned,
  - theorem tokens `gr01_conservation_compatibility_from_poisson_residual_v0` and
    `gr01_conservation_compatibility_from_bridge_promotion_chain_v0` are
    test-pinned for `TOE-GR-CONS-01` promotion,
  - assumptions are classified in paper/state artifacts,
  - no hidden assumptions remain in theorem signature text.

## Freeze Policy

- No new comparator lanes are authorized by this target.
- Existing GR01 freeze policy remains in force unless explicitly reset in governance.
