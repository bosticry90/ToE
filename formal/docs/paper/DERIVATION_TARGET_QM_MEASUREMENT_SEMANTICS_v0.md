# Derivation Target: QM Measurement Semantics v0

Spec ID:
- `DERIVATION_TARGET_QM_MEASUREMENT_SEMANTICS_v0`

Classification:
- `P-POLICY`

Purpose:
- Freeze a planning-only target for the QM measurement/probability structural object.
- Convert the `TARGET-QM-MEAS-PLAN` map entry into an auditable work-order artifact.
- Define minimal closure criteria without authorizing new comparator lanes.

Non-claim boundary:
- This artifact is planning-only.
- This artifact is a non-claim and does not promote any theorem/evidence status.
- This artifact does not substitute for derivations or theorem discharge.
- This artifact does not authorize new comparator lanes.
- This artifact does not claim a Born-rule derivation.

Target scope:
- Pillar: `PILLAR-QM`.
- Structural object: measurement/data anchoring semantics.
- Map linkage: `TARGET-QM-MEAS-PLAN` in `STRUCTURAL_CLOSENESS_MAP_v0`.

Canonical Lean target (contract-only):
- Module: `formal/toe_formal/ToeFormal/QM/MeasurementSemantics.lean`
- Theorem surface: `qm_measurement_weights_normalized_under_assumptions`
- Scope note: normalization contract only; not a Born-rule claim.
- Lean header posture tokens: `Contract-only theorem surface.` and
  `No Born-rule claim and no external truth claim.`
- Assumption transparency note: `h_context_consistency` is retained as an auditable boundary-condition assumption and is used by the zero-extension boundary lemmas.
- Nonnegativity posture: `ProbabilityMap` is context-indexed and support-scoped (`nonneg_support`) in v0.

## Minimum Structural Objects Required

1. Probability map object
- Define a typed map from admissible state objects to normalized outcome weights.
- Include explicit normalization and domain assumptions.

2. Measurement semantics object
- Define typed measurement contexts/observables and outcome spaces.
- Define how a measurement context consumes a state and returns outcome semantics.

3. Classification bridge surface
- Declare which parts are `P-POLICY` vs `T-CONDITIONAL` candidates.
- Keep postulate/theorem boundaries explicit and test-auditable.

## Theorem-Surface Contract (Future `T-CONDITIONAL` Target)

- Current contract surface in Lean:
  - typed objects: `OutcomeSpace`, `MeasurementContext`, `ProbabilityMap`
  - predicates/aggregates: `NormalizedWeights`, `Expectation`, `ExpectedObservable`
  - theorem: `qm_measurement_weights_normalized_under_assumptions`
  - boundary contracts: `weights_eq_zero_extension_of_context_consistency`, `expectation_eq_of_context_consistency_with_zero_extension`
  - expectation contracts: `expectation_add`, `expectation_smul`, `expectation_nonneg_of_nonneg_weights_and_observable`, `expected_observable_nonneg_of_support_nonneg`
- The theorem contract:
  - consumes explicit assumptions,
  - references typed probability and measurement semantics objects,
  - avoids hidden assumptions and vacuous outputs.
- No theorem-level promotion is claimed in this v0 planning artifact.

## Closure Definition

- `ABSENT -> P-POLICY` (planning closure):
  - this spec exists,
  - map pointer is wired,
  - claim/paper surfaces reference it as planning-only,
  - gate checks enforce non-claim/no-promotion wording.

- `P-POLICY -> T-CONDITIONAL` (theorem-surface closure):
  - Lean theorem surface in `formal/toe_formal/ToeFormal/QM/MeasurementSemantics.lean` exists with explicit assumptions and non-vacuity checks,
  - theorem token `qm_measurement_weights_normalized_under_assumptions` is test-pinned,
  - assumptions are classified in paper/state artifacts,
  - no hidden assumptions remain in theorem signature text.

## Freeze Policy

- No new comparator lanes are authorized by this target.
- Existing GR01 freeze policy remains in force unless explicitly reset in governance.
