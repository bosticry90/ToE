# Derivation Target: QM Evolution Object v0

Spec ID:
- `DERIVATION_TARGET_QM_EVOLUTION_OBJECT_v0`

Classification:
- `P-POLICY`

Purpose:
- Freeze a planning-only target for the QM evolution-object structural layer.
- Convert `TARGET-QM-EVOL-PLAN` into an auditable work-order artifact.
- Define minimal closure criteria without authorizing new comparator lanes.

Non-claim boundary:
- This artifact is planning-only.
- This artifact is a non-claim and does not promote theorem/evidence status.
- This artifact does not substitute for derivations or theorem discharge.
- This artifact does not authorize new comparator lanes.
- This artifact does not claim Schrodinger-equation derivation.
- This artifact does not claim unitary dynamics recovery.

Promotion checkpoint (theorem surface):
- `TOE-QM-THM-01` tracks the promoted conditional theorem contract in
  `formal/docs/paper/RESULTS_TABLE_v0.md`.
- This target remains the frozen planning work-order artifact for residual
  non-derivational assumptions and scope boundaries.

Target scope:
- Pillar: `PILLAR-QM`.
- Structural object: evolution object (time/state/evolution-operator scaffolding).
- Map linkage: `TARGET-QM-EVOL-PLAN` in `STRUCTURAL_CLOSENESS_MAP_v0`.

Canonical Lean target (contract-only):
- Module: `formal/toe_formal/ToeFormal/QM/EvolutionContract.lean`
- Theorem surface: `qm_evolution_under_contract_assumptions`
- Lean header posture tokens: `Contract-only theorem surface.` and
  `No Schrodinger derivation claim and no external truth claim.`

## Minimum Structural Objects Required

1. Time parameter object
- Typed time carrier for evolution contracts.

2. QM-state object
- Typed state carrier for evolution contracts.

3. Evolution operator object
- Typed evolution operator from time + state to state.

4. Evolution context object
- Typed context bundling time parameter and evolution operator surfaces.

5. Evolution contract surface
- Explicit theorem-shaped contract for QM-state evolution under declared assumptions.

## Theorem-Surface Contract (`T-CONDITIONAL` Checkpoint)

- Current contract surface in Lean:
  - typed objects: `TimeParameter`, `QMState`, `EvolutionOperator`, `EvolutionContext`
  - proposition: `QMStateEvolvesUnderContract`
  - theorem: `qm_evolution_under_contract_assumptions`
- The theorem contract:
  - consumes explicit assumptions,
  - avoids hidden assumptions and vacuous outputs,
  - remains non-claim and contract-only in v0.

## Assumption Classification (Promotion Draft)

Registry pointer:
- `formal/docs/paper/ASSUMPTION_REGISTRY_v1.md`

Theorem-linked assumption IDs:
- `ASM-QM-EVOL-STR-01` (structural context typing).
- `ASM-QM-EVOL-STR-02` (explicit time/state binders).
- `ASM-QM-EVOL-APP-01` (non-derivational boundary: no Schrodinger/unitary recovery claim).

## Closure Definition

- `ABSENT -> P-POLICY` (planning closure):
  - this spec exists,
  - map pointer is wired,
  - claim/paper/state surfaces reference it as planning-only,
  - gate checks enforce non-claim/no-promotion wording.

- `P-POLICY -> T-CONDITIONAL` (theorem-surface closure):
  - Lean theorem surface in `formal/toe_formal/ToeFormal/QM/EvolutionContract.lean` exists with explicit assumptions and non-vacuity checks,
  - theorem token `qm_evolution_under_contract_assumptions` is test-pinned,
  - assumptions are classified in paper/state artifacts,
  - no hidden assumptions remain in theorem signature text.

## Freeze Policy

- No new comparator lanes are authorized by this target.
- Existing GR01 freeze policy remains in force unless explicitly reset in governance.
