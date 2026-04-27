# Scalar QFT Phase0 Baseline Acceptance Contract v0

Document ID:
- `SCALAR_QFT_PHASE0_BASELINE_ACCEPTANCE_CONTRACT_v0`

Purpose:
- Freeze a pre-tranche baseline for the strict scalar/QFT lane.
- Define objective pass/fail acceptance criteria for blocker-moving work.
- Prevent Phase 1 theorem edits unless this Phase 0 gate is GREEN.

Non-claim boundary:
- no parser claim
- no master-action promotion claim
- no seam closure claim
- no empirical claim
- no global ToE completion claim

## Scope

In scope:
- baseline freeze and acceptance criteria only
- machine-check gate for contract completeness
- report JSON surface for GREEN/RED status

Out of scope:
- Lean theorem or proof edits
- Phase 1 structured-source implementation
- continuum-obligation discharge work
- neutralization-lemma family work

## Baseline Snapshot

Snapshot date:
- `2026-04-25`

Pinned baseline (authoritative read):
- theorem_gap_count_baseline: `7`
- seam_integration_gap_count_baseline: `3`
- scalar_lane_retained_assumption_rows_baseline: `6`

Baseline source pointers:
- `State_of_the_Theory.md`
- `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md`

## Success Criteria

Tranche success requires all of the following:
1. At least one named theorem movement or blocker delta in the strict scalar/QFT lane.
2. Evidence pointers are complete and resolvable.
3. Non-claim boundary is preserved.
4. Phase 0 gate status is `GREEN`.

## Fail-Closed Conditions

Fail conditions:
- no net movement => tranche fails
- missing evidence pointers => tranche fails
- unqualified completion language drift => tranche fails
- Phase 0 gate not GREEN => tranche fails

## Verification Command Set

Run focused Lean witness build:
- `Set-Location "c:\Users\psboy\Documents\ToE\formal\toe_formal"; $env:CI='1'; .\lake.ps1 build ToeFormal.QFT.ToeCandidateFreeScalarWitness`

Run diagnostics on touched files:
- `get_errors` for:
  - `formal/docs/lanes/SCALAR_QFT_PHASE0_BASELINE_ACCEPTANCE_CONTRACT_v0.md`
  - `formal/python/tests/test_scalar_qft_phase0_baseline_acceptance_contract_gate.py`
  - `formal/output/reports/scalar_qft_phase0_baseline_acceptance_contract_v0.json`

Run Phase 0 gate:
- `./py.ps1 -m pytest formal/python/tests/test_scalar_qft_phase0_baseline_acceptance_contract_gate.py -q`

## Evidence Pointer Requirements

Required surfaces:
- `formal/docs/lanes/SCALAR_QFT_PHASE0_BASELINE_ACCEPTANCE_CONTRACT_v0.md`
- `formal/python/tests/test_scalar_qft_phase0_baseline_acceptance_contract_gate.py`
- `formal/output/reports/scalar_qft_phase0_baseline_acceptance_contract_v0.json`
- `State_of_the_Theory.md`
- `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md`

## Phase Lock Rule

Phase 1 blocked until Phase 0 gate is GREEN.
No Lean theorem files modified in this tranche.
