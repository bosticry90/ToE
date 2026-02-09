# Bragg lane: DR-01 → BR-01 (eliminative summary)

Last updated: 2026-02-04

## Goal

Provide a single, reproducible lane that can say (without inference inflation):

- Given a **pinned external evidence source** and **locked digitization + selection rules**, which BR-01 candidate constructors are:
  - `true` (survives declared structural constraints)
  - `false` (eliminated by declared structural constraints)
  - `unknown` (no declared prediction; unknown is not fail)

This lane is **summary-only / eliminative-only**.

## External anchor (pinned)

- Source PDF and render provenance live in the OV-BR-03N lock:
  - `formal/markdown/locks/observables/OV-BR-03_bragg_dispersion_k_omega_digitized.md`
  - External evidence file (repo-relative): `formal/external_evidence/bec_bragg_shammass_2012/source.pdf`

## Canonical lock outputs

- Audit / anchoring record (must pass self-checks):
  - `formal/markdown/locks/observables/OV-SEL-BR-01_bragg_lowk_slope_audit.md`

- Candidate declaration surface (structural; no numeric constraints):
  - `formal/markdown/locks/observables/OV-DR-BR-00_br01_prediction_declarations.md`

- Candidate pruning table (the lane deliverable):
  - `formal/markdown/locks/observables/OV-DR-BR-01_candidate_pruning_table.md`
    - Includes an explicit `summary.counts` and `summary.candidates` rollup.

## Notes on gates/blocked status

The Bragg lane records are allowed to remain **blocked-by-default** under the admissibility manifest.

- Even when blocked, the lane remains valuable as a deterministic, non-inferential bookkeeping surface:
  - selection rules remain pinned
  - candidate IDs remain structural
  - pruning can proceed on declared structure

## Closeout checklist (2026-02-04)

Required preflight
- Clear override env for canonical run: `TOE_ADMISSIBILITY_MANIFEST` must be unset.
- Required command: `.\py.ps1 -m formal.python.tools.regen_canonical_locks --bragg-only --report`

Required canonical locks (must exist)
- `formal/markdown/locks/observables/OV-BR-03_bragg_dispersion_k_omega_digitized.md`
- `formal/markdown/locks/observables/OV-BR-05_bragg_lowk_slope_summary.md`
- `formal/markdown/locks/observables/OV-DR-BR-00_br01_prediction_declarations.md`
- `formal/markdown/locks/observables/OV-DR-BR-01_candidate_pruning_table.md`
- `formal/markdown/locks/observables/OV-SEL-BR-01_bragg_lowk_slope_audit.md`

Non-negotiable tests (must pass)
- `formal/python/tests/test_ov_br03n_bragg_dispersion_digitized_lock.py`
- `formal/python/tests/test_ov_br04a_results_primary_contract.py`
- `formal/python/tests/test_ov_br05_bragg_lowk_slope_summary_lock.py`
- `formal/python/tests/test_ov_dr_br00_br01_prediction_declarations_lock.py`
- `formal/python/tests/test_ov_dr_br01_candidate_pruning_table_lock.py`
- `formal/python/tests/test_ov_sel_br01_bragg_lowk_slope_audit_lock.py`
- `formal/python/tests/test_br01_candidate_table.py`
- `formal/python/tests/test_br01_front_door_enforced.py`
- `formal/python/tests/test_regen_canonical_locks_bragg_only.py`
- `formal/python/tests/test_state_theory_dag.py`

Expected pruning outcome (canonical manifest)
- `schema == OV-DR-BR-01_candidate_pruning_table/v1`
- `observable_id == OV-DR-BR-01`
- `summary.counts == {"true": 2, "false": 1, "unknown": 1}`
- `true = [BR01_metric_from_DR01_fit_constant_density, BR01_metric_from_DR01_fit_unit_density]`
- `false = [BR01_metric_from_DR01_fit_unit_density_structural_fail]`
- `unknown = [BR01_metric_from_DR01_fit_rest_frame_u0]`
- `status.blocked == true` (blocked-by-default posture under canonical manifest)

## Evidence

- Record generators:
  - `formal/python/toe/observables/ovsel_br01_bragg_lowk_slope_audit_record.py`
  - `formal/python/toe/observables/ovdrbr00_br01_prediction_declarations_record.py`
  - `formal/python/toe/observables/ovdrbr01_candidate_pruning_table_record.py`

- Tests:
  - `formal/python/tests/test_ov_sel_br01_bragg_lowk_slope_audit_lock.py`
  - `formal/python/tests/test_ov_dr_br01_candidate_pruning_table_lock.py`
