# Derivation Target: QM Symmetry Object v0

Spec ID:
- `DERIVATION_TARGET_QM_SYMMETRY_OBJECT_v0`

Classification:
- `P-POLICY`

Purpose:
- Freeze a planning-only target for the QM symmetry-object structural layer.
- Convert `TARGET-QM-SYMM-PLAN` into an auditable work-order artifact.
- Define minimal closure criteria without authorizing new comparator lanes.

Non-claim boundary:
- This artifact is planning-only.
- This artifact is a non-claim and does not promote theorem/evidence status.
- This artifact does not substitute for derivations or theorem discharge.
- This artifact does not authorize new comparator lanes.
- This artifact does not claim Schrodinger-equation recovery.

Target scope:
- Pillar: `PILLAR-QM`.
- Structural object: symmetry object (group/action/context scaffolding).
- Map linkage: `TARGET-QM-SYMM-PLAN` in `STRUCTURAL_CLOSENESS_MAP_v0`.

Canonical Lean target (contract-only):
- Module: `formal/toe_formal/ToeFormal/QM/SymmetryContract.lean`
- Theorem surface: `qm_state_fixed_under_symmetry_contract_assumptions`
- Lean header posture tokens: `Contract-only theorem surface.` and
  `No QM interpretation claim and no external truth claim.`

## Minimum Structural Objects Required

1. Symmetry group object
- Typed group-carrier object used by the contract context.

2. Symmetry action object
- Typed action from symmetry elements to QM-state carriers.

3. Symmetry context object
- Typed context bundling symmetry group and action surfaces.

4. QM-state object
- Typed state carrier under the declared symmetry context.

5. Invariance contract surface
- Explicit theorem-shaped contract for state-fixed behavior under declared symmetry action.

## Theorem-Surface Contract (Future `T-CONDITIONAL` Target)

- Current contract surface in Lean:
  - typed objects: `SymmetryGroup`, `SymmetryAction`, `SymmetryContext`, `QMState`
  - proposition: `StateFixedUnderSymmetryAction`
  - theorem: `qm_state_fixed_under_symmetry_contract_assumptions`
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
  - Lean theorem surface in `formal/toe_formal/ToeFormal/QM/SymmetryContract.lean` exists with explicit assumptions and non-vacuity checks,
  - theorem token `qm_state_fixed_under_symmetry_contract_assumptions` is test-pinned,
  - assumptions are classified in paper/state artifacts,
  - no hidden assumptions remain in theorem signature text.

## Freeze Policy

- No new comparator lanes are authorized by this target.
- Existing GR01 freeze policy remains in force unless explicitly reset in governance.
