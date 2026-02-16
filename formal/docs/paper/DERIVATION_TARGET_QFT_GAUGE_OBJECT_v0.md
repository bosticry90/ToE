# Derivation Target: QFT Gauge Object v0

Spec ID:
- `DERIVATION_TARGET_QFT_GAUGE_OBJECT_v0`

Classification:
- `P-POLICY`

Purpose:
- Freeze a planning-only target for the QFT gauge-object structural layer.
- Convert `TARGET-QFT-GAUGE-PLAN` into an auditable work-order artifact.
- Define minimal closure criteria without authorizing new comparator lanes.

Non-claim boundary:
- This artifact is planning-only.
- This artifact is a non-claim and does not promote theorem/evidence status.
- This artifact does not substitute for derivations or theorem discharge.
- This artifact does not authorize new comparator lanes.
- This artifact does not claim Standard Model recovery.

Target scope:
- Pillar: `PILLAR-QFT`.
- Structural object: local gauge object (group/action/context scaffolding).
- Map linkage: `TARGET-QFT-GAUGE-PLAN` in `STRUCTURAL_CLOSENESS_MAP_v0`.

Canonical Lean target (contract-only):
- Module: `formal/toe_formal/ToeFormal/QFT/GaugeContract.lean`
- Theorem surface: `qft_gauge_invariance_under_contract_assumptions`
- Lean header posture tokens: `Contract-only theorem surface.` and
  `No Standard Model claim and no external truth claim.`

## Minimum Structural Objects Required

1. Gauge group object
- Typed group-carrier object used by the contract context.

2. Gauge action object
- Typed action from gauge elements to field configurations.

3. Gauge context object
- Typed context bundling gauge group and action surfaces.

4. Gauge field object
- Typed carrier for field values under the declared context.

5. Invariance contract surface
- Explicit theorem-shaped contract for invariance under gauge action.

## Theorem-Surface Contract (Future `T-CONDITIONAL` Target)

- Current contract surface in Lean:
  - typed objects: `GaugeGroup`, `GaugeAction`, `GaugeContext`, `GaugeField`
  - proposition: `FieldFixedUnderGaugeAction`
  - theorem: `qft_gauge_invariance_under_contract_assumptions`
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
  - Lean theorem surface in `formal/toe_formal/ToeFormal/QFT/GaugeContract.lean` exists with explicit assumptions and non-vacuity checks,
  - theorem token `qft_gauge_invariance_under_contract_assumptions` is test-pinned,
  - assumptions are classified in paper/state artifacts,
  - no hidden assumptions remain in theorem signature text.

## Freeze Policy

- No new comparator lanes are authorized by this target.
- Existing GR01 freeze policy remains in force unless explicitly reset in governance.
