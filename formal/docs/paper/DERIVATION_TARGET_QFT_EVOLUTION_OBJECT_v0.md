# Derivation Target: QFT Evolution Object v0

Spec ID:
- `DERIVATION_TARGET_QFT_EVOLUTION_OBJECT_v0`

Classification:
- `P-POLICY`

Purpose:
- Freeze a planning-only target for the QFT evolution-object structural layer.
- Convert `TARGET-QFT-EVOL-PLAN` into an auditable work-order artifact.
- Define minimal closure criteria without authorizing new comparator lanes.

Non-claim boundary:
- This artifact is planning-only.
- This artifact is a non-claim and does not promote theorem/evidence status.
- This artifact does not substitute for derivations or theorem discharge.
- This artifact does not authorize new comparator lanes.
- This artifact does not claim Schrodinger/Dirac/Klein-Gordon derivation.
- This artifact does not claim Standard Model dynamics recovery.

Target scope:
- Pillar: `PILLAR-QFT`.
- Structural object: evolution object (time/state/evolution-operator scaffolding).
- Map linkage: `TARGET-QFT-EVOL-PLAN` in `STRUCTURAL_CLOSENESS_MAP_v0`.

Canonical Lean target (contract-only):
- Module: `formal/toe_formal/ToeFormal/QFT/EvolutionContract.lean`
- Theorem surface: `qft_evolution_under_contract_assumptions`
- Lean header posture tokens: `Contract-only theorem surface.` and
  `No Standard Model claim and no external truth claim.`

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
