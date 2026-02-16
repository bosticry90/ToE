# Derivation Target: GR Geometry Object v0

Spec ID:
- `DERIVATION_TARGET_GR_GEOMETRY_OBJECT_v0`

Classification:
- `P-POLICY`

Purpose:
- Freeze a planning-only target for the GR geometry-object structural layer.
- Convert `TARGET-GR-GEOM-PLAN` into an auditable work-order artifact.
- Define minimal closure criteria without authorizing new comparator lanes.

Non-claim boundary:
- This artifact is planning-only.
- This artifact is a non-claim and does not promote theorem/evidence status.
- This artifact does not substitute for derivations or theorem discharge.
- This artifact does not authorize new comparator lanes.
- This artifact does not claim GR field-equation recovery.

Target scope:
- Pillar: `PILLAR-GR`.
- Structural object: geometry object (metric + diffeomorphism action scaffolding).
- Map linkage: `TARGET-GR-GEOM-PLAN` in `STRUCTURAL_CLOSENESS_MAP_v0`.

Canonical Lean target (contract-only):
- Module: `formal/toe_formal/ToeFormal/GR/GeometryContract.lean`
- Theorem surface: `gr_metric_invariance_under_contract_assumptions`
- Lean header posture tokens: `Contract-only theorem surface.` and
  `No GR field-equation claim and no external truth claim.`

## Minimum Structural Objects Required

1. Spacetime chart object
- Typed chart carrier and domain surface.

2. Diffeomorphism action object
- Typed action of point maps on points.

3. Metric object
- Typed metric carrier with explicit symmetry contract.

4. Invariance contract surface
- Explicit theorem-shaped contract for metric invariance under the declared action.

## Theorem-Surface Contract (Future `T-CONDITIONAL` Target)

- Current contract surface in Lean:
  - typed objects: `SpacetimeChart`, `DiffeomorphismAction`, `GeometryContext`, `MetricField`
  - proposition: `MetricInvarianceUnderAction`
  - theorem: `gr_metric_invariance_under_contract_assumptions`
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
  - Lean theorem surface in `formal/toe_formal/ToeFormal/GR/GeometryContract.lean` exists with explicit assumptions and non-vacuity checks,
  - theorem token `gr_metric_invariance_under_contract_assumptions` is test-pinned,
  - assumptions are classified in paper/state artifacts,
  - no hidden assumptions remain in theorem signature text.

## Freeze Policy

- No new comparator lanes are authorized by this target.
- Existing GR01 freeze policy remains in force unless explicitly reset in governance.
