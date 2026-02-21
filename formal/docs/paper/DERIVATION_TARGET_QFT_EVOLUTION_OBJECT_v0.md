# Derivation Target: QFT Evolution Object v0

Spec ID:
- `DERIVATION_TARGET_QFT_EVOLUTION_OBJECT_v0`

Classification:
- `P-POLICY`

Purpose:
- Freeze a planning-only target for the QFT evolution-object structural layer.
- Convert `TARGET-QFT-EVOL-PLAN` into an auditable work-order artifact.
- Define minimal closure criteria without authorizing new comparator lanes.

Kickoff token contract:
- `DERIVATION_TARGET_QFT_EVOLUTION_OBJECT_v0`
- `TARGET-QFT-EVOL-PLAN`
- `QFT_EVOL_ADJUDICATION: NOT_YET_DISCHARGED`
- `QFT_EVOL_SCOPE_BOUNDARY_v0: CONTRACT_OBJECT_SCAFFOLD_ONLY_NONCLAIM`
- `QFT_EVOL_PREREQS_v0: TARGET-QFT-GAUGE-PLAN;TARGET-SR-COV-PLAN;TARGET-EM-U1-PLAN`
- `QFT_EVOL_DELIVERABLE_FIELD_OBJECT_v0: FIELD_CARRIER_TYPED_SCAFFOLD_ONLY`
- `QFT_EVOL_DELIVERABLE_LAGRANGIAN_PLACEHOLDER_v0: ACTION_DENSITY_PLACEHOLDER_NONCLAIM`
- `QFT_EVOL_DELIVERABLE_EOM_PLACEHOLDER_v0: EULER_LAGRANGE_STATEMENT_ONLY`
- `QFT_EVOL_DELIVERABLE_CANONICAL_MOMENTUM_PLACEHOLDER_v0: STATEMENT_ONLY`
- `QFT_EVOL_DELIVERABLE_UNITARITY_PLACEHOLDER_v0: STATEMENT_ONLY_NONPROOF`
- `formal/toe_formal/ToeFormal/QFT/Evolution/ObjectScaffold.lean`
- `TARGET-QFT-EVOL-MICRO-01-TIME-STATE-OPERATOR-SURFACE-v0`
- `formal/docs/paper/DERIVATION_TARGET_QFT_EVOL_MICRO_01_TIME_STATE_OPERATOR_SURFACE_v0.md`
- `formal/python/tests/test_qft_evol_micro01_time_state_operator_surface_gate.py`
- `TARGET-QFT-EVOL-MICRO-02-EVOLUTION-CONTEXT-SURFACE-v0`
- `formal/docs/paper/DERIVATION_TARGET_QFT_EVOL_MICRO_02_EVOLUTION_CONTEXT_SURFACE_v0.md`
- `formal/python/tests/test_qft_evol_micro02_evolution_context_surface_gate.py`
- `TARGET-QFT-EVOL-MICRO-03-ACTION-DENSITY-SURFACE-v0`
- `formal/docs/paper/DERIVATION_TARGET_QFT_EVOL_MICRO_03_ACTION_DENSITY_SURFACE_v0.md`
- `formal/python/tests/test_qft_evol_micro03_action_density_surface_gate.py`

Non-claim boundary:
- This artifact is planning-only.
- This artifact is a non-claim and does not promote theorem/evidence status.
- This artifact does not substitute for derivations or theorem discharge.
- This artifact does not authorize new comparator lanes.
- This artifact does not claim quantization closure.
- This artifact does not claim dynamics derivation closure.
- This artifact does not claim Standard Model recovery.
- This artifact does not claim external truth.

Target scope:
- Pillar: `PILLAR-QFT`.
- Structural object: evolution object (time/state/evolution-operator scaffolding).
- Map linkage: `TARGET-QFT-EVOL-PLAN` in `STRUCTURAL_CLOSENESS_MAP_v0`.

Canonical Lean targets:
- Contract module: `formal/toe_formal/ToeFormal/QFT/EvolutionContract.lean`
  - theorem surface: `qft_evolution_under_contract_assumptions`
  - Lean header posture tokens: `Contract-only theorem surface.` and
    `No Standard Model claim and no external truth claim.`
- Object scaffold module: `formal/toe_formal/ToeFormal/QFT/Evolution/ObjectScaffold.lean`
  - scope: typed carriers and statement-only seams.

## Minimum Structural Objects Required

1. Time parameter object
- Typed time carrier for evolution contracts.

2. Field-state object
- Typed state carrier for evolution contracts.

3. Evolution operator object
- Typed evolution operator from time + state to state.

4. Evolution context object
- Typed context bundling time parameter and evolution operator surfaces.

5. Evolution contract surface
- Explicit theorem-shaped contract for state evolution under declared assumptions.

## Kickoff Scaffold Deliverables (Contract/Object Only)

- `QFT_EVOL_DELIVERABLE_FIELD_OBJECT_v0: FIELD_CARRIER_TYPED_SCAFFOLD_ONLY`
  - Field carrier object is typed and scaffold-only.
- `QFT_EVOL_DELIVERABLE_LAGRANGIAN_PLACEHOLDER_v0: ACTION_DENSITY_PLACEHOLDER_NONCLAIM`
  - Action density surface is placeholder-only and non-claim.
- `QFT_EVOL_DELIVERABLE_EOM_PLACEHOLDER_v0: EULER_LAGRANGE_STATEMENT_ONLY`
  - Euler-Lagrange surface is statement-only and non-proof.
- `QFT_EVOL_DELIVERABLE_CANONICAL_MOMENTUM_PLACEHOLDER_v0: STATEMENT_ONLY`
  - Canonical momentum surface is statement-only and placeholder-only.
- `QFT_EVOL_DELIVERABLE_UNITARITY_PLACEHOLDER_v0: STATEMENT_ONLY_NONPROOF`
  - Unitarity surface is statement-only and non-proof.

## Theorem-Surface Contract (Future `T-CONDITIONAL` Target)

- Current contract surface in Lean:
  - typed objects: `TimeParameter`, `FieldState`, `EvolutionOperator`, `EvolutionContext`
  - proposition: `EvolvesUnderContract`
  - theorem: `qft_evolution_under_contract_assumptions`
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
  - Lean theorem surface in `formal/toe_formal/ToeFormal/QFT/EvolutionContract.lean` exists with explicit assumptions and non-vacuity checks,
  - theorem token `qft_evolution_under_contract_assumptions` is test-pinned,
  - assumptions are classified in paper/state artifacts,
  - no hidden assumptions remain in theorem signature text.

## Freeze Policy

- No new comparator lanes are authorized by this target.
- Existing GR01 freeze policy remains in force unless explicitly reset in governance.
