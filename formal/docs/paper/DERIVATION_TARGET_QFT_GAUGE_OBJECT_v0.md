# Derivation Target: QFT Gauge Object v0

Spec ID:
- `DERIVATION_TARGET_QFT_GAUGE_OBJECT_v0`

Classification:
- `P-POLICY`

Purpose:
- Freeze a planning-only target for the QFT gauge-object structural layer.
- Convert `TARGET-QFT-GAUGE-PLAN` into an auditable work-order artifact.
- Define minimal closure criteria without authorizing new comparator lanes.

Kickoff token contract:
- `DERIVATION_TARGET_QFT_GAUGE_OBJECT_v0`
- `TARGET-QFT-GAUGE-PLAN`
- `QFT_GAUGE_ADJUDICATION: NOT_YET_DISCHARGED`
- `QFT_GAUGE_SCOPE_BOUNDARY_v0: CONTRACT_OBJECT_SCAFFOLD_ONLY_NONCLAIM`
- `QFT_PREREQS_v0: TARGET-EM-U1-PLAN;TARGET-SR-COV-PLAN`
- `TARGET-QFT-GAUGE-MICRO-01-GROUP-ACTION-SURFACE-v0`
- `formal/docs/paper/DERIVATION_TARGET_QFT_GAUGE_MICRO_01_GROUP_ACTION_SURFACE_v0.md`
- `formal/python/tests/test_qft_gauge_micro01_group_action_surface_gate.py`

Non-claim boundary:
- This artifact is planning-only.
- This artifact is a non-claim and does not promote theorem/evidence status.
- This artifact does not substitute for derivations or theorem discharge.
- This artifact does not authorize new comparator lanes.
- This artifact does not claim Standard Model recovery.
- This artifact does not claim quantization closure.
- This artifact does not claim dynamics derivation closure.

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

## Kickoff Scaffold Deliverables (Contract/Object Only)

- `QFT_GAUGE_DELIVERABLE_GROUP_SURFACE_v0: U1_AND_NONABELIAN_PLACEHOLDER_DECLARED`
  - Group object surface includes explicit U(1) lane and nonabelian placeholder lane.
- `QFT_GAUGE_DELIVERABLE_CONNECTION_SURFACE_v0: A_OBJECT_SURFACE_DECLARED`
  - Connection/potential object surface `A` is declared as a typed scaffold surface only.
- `QFT_GAUGE_DELIVERABLE_CURVATURE_SURFACE_v0: F_EQ_DA_PLUS_A_WEDGE_A_PLACEHOLDER_DECLARED`
  - Curvature object surface includes `F = dA` with explicit `A∧A` placeholder posture.
- `QFT_GAUGE_DELIVERABLE_TRANSFORM_SURFACE_v0: GAUGE_TRANSFORM_AND_INVARIANCE_STATEMENT_ONLY`
  - Gauge-transform and invariance surfaces are statement-only (no closure promotion).
- `QFT_GAUGE_DELIVERABLE_COUPLING_SURFACE_v0: CURRENT_SOURCE_INTERFACE_STATEMENT_ONLY`
  - Coupling interface is source/current statement surface only (no dynamics claim).

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
