# WS_09_T04A_FAILING_GOVERNANCE_TRANCHE_TRIAGE_NOTE_v0

## Purpose
Bound the WS-09-T04 blocker into an explicit remediation program for the failing governance pytest tranche.

## Failure Inventory (exact)
Source:
- `scratch/ce05_governance_suite_run.log`
- extracted list: `scratch/ce05_failed_tests_exact.txt`

Failing tests (14):
1. `formal/python/tests/test_state_doc_comp_fn_rep_policy.py::test_comp_fn_rep_policy_is_wired_and_evidenced`
2. `formal/python/tests/test_state_doc_comp_fn_rep32_64_equiv.py::test_comp_fn_rep32_64_equiv_gap_is_wired_and_evidenced`
3. `formal/python/tests/test_state_doc_comp_fn_rep32_link_discharge.py::test_comp_fn_rep32_link_is_marked_implemented_and_build_guarded`
4. `formal/python/tests/test_state_doc_comp_fn_rep_nonalias_equivalence01.py::test_comp_fn_rep_nonalias_equiv01_gap_is_wired`
5. `formal/python/tests/test_state_doc_comp03_comp05_transition.py::test_comp03_is_implemented_and_comp05_is_lifted`
6. `formal/python/tests/test_state_doc_comp03_comp05_transition.py::test_comp_pred_fals_mentions_cv03_ucff_lane`
7. `formal/python/tests/test_state_doc_comp_evol_link_discharge.py::test_comp_evol_link_is_marked_discharged_and_build_verified`
8. `formal/python/tests/test_state_doc_cv_lane_wiring.py::test_state_doc_has_cv_and_domain_blocks_with_evidence`
9. `formal/python/tests/test_state_doc_cv_lane_wiring.py::test_comp_pred_fals_evidence_mentions_cv_bridge_and_domain02_lanes`
10. `formal/python/tests/test_state_doc_mainline_does_not_depend_on_variantA.py::test_pol01_mainline_dependencies_do_not_include_variantA_or_ov01x`
11. `formal/python/tests/test_pillar_status_matrix_consistency_gate.py::test_pillar_status_matrix_qft_entry_matches_state_tokens`
12. `formal/python/tests/test_pillar_phase_advancement_gate.py::test_registry_drives_pillar_phase_advancement_semantics`
13. `formal/python/tests/test_gr_continuum_discharge_criteria_cycle10_gate.py::test_gr_continuum_cycle10_criteria_pointer_parity_in_state_and_roadmap`
14. `formal/python/tests/test_conftest_signature_stability_gate.py::test_conftest_signature_matches_protocol_pin`

## Grouped Failure Types

### 1) Authority/state parity (11)
- Tests: 1-10 and 13.
- Shared signal:
  - missing or drifted state surface tokens/pointers in `State_of_the_Theory.md`.
  - parity assertions between state and roadmap/protocol references are failing.

### 2) Pillar/status consistency (2)
- Tests: 11-12.
- Shared signal:
  - pillar/status and phase-advancement token parity drift between state text and matrix/registry expectations.

### 3) Conftest/signature stability (1)
- Test: 14.
- Shared signal:
  - `conftest.py` hash differs from pinned protocol hash.

## Smallest Shared Root Cause First
Primary first fix family:
- Authority/state parity drift in `State_of_the_Theory.md` token and pointer block.
Why first:
- Covers the largest failing cluster (11/14) and likely unlocks part of pillar/status parity.

## Remediation Order
1. Family A: authority/state parity token+pointer reconciliation in `State_of_the_Theory.md` (and any required paired roadmap pointer parity lines).
2. Family B: pillar/status consistency reconciliation against matrix/registry expected tokens.
3. Family C: conftest signature stability reconciliation (`conftest.py` vs protocol pin update policy).
4. Re-run failing subset.
5. Re-run `governance_suite.ps1` unchanged.

## Expected Verification Commands
Failing subset (exact 14 tests):
- `./py.ps1 -m pytest -q formal/python/tests/test_state_doc_comp_fn_rep_policy.py formal/python/tests/test_state_doc_comp_fn_rep32_64_equiv.py formal/python/tests/test_state_doc_comp_fn_rep32_link_discharge.py formal/python/tests/test_state_doc_comp_fn_rep_nonalias_equivalence01.py formal/python/tests/test_state_doc_comp03_comp05_transition.py formal/python/tests/test_state_doc_comp_evol_link_discharge.py formal/python/tests/test_state_doc_cv_lane_wiring.py formal/python/tests/test_state_doc_mainline_does_not_depend_on_variantA.py formal/python/tests/test_pillar_status_matrix_consistency_gate.py formal/python/tests/test_pillar_phase_advancement_gate.py formal/python/tests/test_gr_continuum_discharge_criteria_cycle10_gate.py formal/python/tests/test_conftest_signature_stability_gate.py`

Canonical governance suite:
- `pwsh -NoProfile -ExecutionPolicy Bypass -File ./governance_suite.ps1`

## Non-Closure Rule
- This triage note is remediation-planning evidence only.
- CE-05 remains open until failing subset and canonical governance suite both pass.
