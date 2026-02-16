# Derivation Target: QM Evolution Hardening v0

Spec ID:
- `DERIVATION_TARGET_QM_EVOLUTION_HARDENING_v0`

Classification:
- `T-PROVED`

Purpose:
- Harden the existing QM evolution theorem surface (`TOE-QM-THM-01`) into a
  minimized and robustness-auditable artifact while preserving current non-claim
  boundaries.

Adjudication token:
- `QM_EVOLUTION_HARDENING_ADJUDICATION: DISCHARGED_v0_CONTRACT_HARDENED`

Scope boundary:
- contract-only QM evolution scope (`EvolutionContract.lean`)
- no Schrodinger-equation derivation claim
- no unitary-dynamics recovery claim
- no comparator-lane expansion

## Hardening done criteria

1. Assumption inventory is explicit and classed as `MATH|DEF|POLICY|SCOPE`.
2. Robustness perturbations are recorded with deterministic artifacts.
3. Negative controls fail informatively with pinned failure tokens.
4. Resolution-trend sanity (optional) is documented without over-claim.
5. Package freeze and reopen triggers are explicit.

## Phase plan

### Phase I — Canonicalization & Hygiene

- Keep canonical theorem token pinned: `qm_evolution_under_contract_assumptions`.
- Keep contract-only posture tokens pinned in module header and target docs.

### Phase II — Assumption minimization

- Ledger token: `QM_EVOLUTION_ASSUMPTION_LEDGER_v0`.
- Canonical bundle token: `QMEvolutionAssumptions_v0`.
- Phase-II minimization token:
  - `QM_EVOLUTION_RECLASSIFICATION_v0_MIN1: hStepTotalPolicy_POLICY_TO_MATH_via_qm_step_total_of_definition`
- Class labels required: `MATH`, `DEF`, `POLICY`, `SCOPE`.

### Phase III — Robustness stress tests

- Record token: `QM_EVOLUTION_ROBUSTNESS_RECORD_v0`.
- Required families (template-level v0):
  - time-parameter perturbation
  - state-carrying perturbation
  - operator-step perturbation

### Phase IIIb — Negative controls

- Record token: `QM_EVOLUTION_NEGATIVE_CONTROL_RECORD_v0`.
- Required controls (template-level v0):
  - invalid evolution context shape
  - broken step-function contract
  - incompatible state carrier

### Phase IV — Optional trend checks

- Record token: `QM_EVOLUTION_RESOLUTION_TREND_RECORD_v0`.
- Trend fields: `residual_norm`, `convergence_trend`, `limit_break_annotation`.

### Phase V — Package freeze

- Package token: `QM_EVOLUTION_PILLAR_PACKAGE_v0`.
- Freeze token: `QM_EVOLUTION_PILLAR_PACKAGE_STATUS_v0: FROZEN_CONTENTS_PINNED`.
- Reopen policy token:
  - `QM_EVOLUTION_REOPEN_POLICY_v0: FROZEN_WATCH_REOPEN_ON_REGRESSION`

## Canonical artifact pointers

- `formal/toe_formal/ToeFormal/QM/EvolutionContract.lean`
- `formal/toe_formal/ToeFormal/QM/QMEvolutionAssumptionLedger.lean`
- `formal/docs/paper/TOE_QM_EVOLUTION_PILLAR_SUMMARY_v0.md`
- `formal/docs/paper/TOE_QM_EVOLUTION_CANONICAL_CHAIN_MAP_v0.md`
- `formal/markdown/locks/policy/QM_EVOLUTION_ASSUMPTION_LEDGER_v0.md`
- `formal/markdown/locks/policy/QM_EVOLUTION_ROBUSTNESS_RECORD_v0.md`
- `formal/markdown/locks/policy/QM_EVOLUTION_NEGATIVE_CONTROL_RECORD_v0.md`
- `formal/markdown/locks/policy/QM_EVOLUTION_RESOLUTION_TREND_RECORD_v0.md`
- `formal/markdown/locks/policy/QM_EVOLUTION_PILLAR_PACKAGE_v0.md`

## Enforcement contract

Hardening adjudication may flip to `DISCHARGED_v0_CONTRACT_HARDENED` only when:

1. phase artifacts exist and required tokens are pinned,
2. state token and target token are synchronized,
3. package freeze + reopen triggers are pinned.
