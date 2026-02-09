$ErrorActionPreference = 'Stop'

Write-Host "Running governance suite via ./py.ps1" -ForegroundColor Cyan

./py.ps1 -m pytest `
  formal/python/tests/test_state_theory_dag.py `
  formal/python/tests/test_state_doc_no_duplicate_gapids.py `
  formal/python/tests/test_toe_target_spec_doc.py `
  formal/python/tests/test_relativistic_limit_dispersion_lane_doc.py `
  formal/python/tests/test_nonrelativistic_limit_nlse_lane_doc.py `
  formal/python/tests/test_weak_field_poisson_lane_doc.py `
  formal/python/tests/test_rl02_nonrelativistic_nlse_v0_front_door.py `
  formal/python/tests/test_rl02_nonrelativistic_nlse_v0_surface_contract_freeze.py `
  formal/python/tests/test_rl02_nonrelativistic_nlse_v0_pinned_artifacts.py `
  formal/python/tests/test_rl02_nonrelativistic_nlse_v0_lock.py `
  formal/python/tests/test_rl01_relativistic_dispersion_v0_front_door.py `
  formal/python/tests/test_rl01_relativistic_dispersion_v0_surface_contract_freeze.py `
  formal/python/tests/test_rl01_relativistic_dispersion_v0_pinned_artifacts.py `
  formal/python/tests/test_rl01_relativistic_dispersion_v0_lock.py `
  formal/python/tests/test_state_doc_comp_fn_rep_policy.py `
  formal/python/tests/test_state_doc_comp_fn_rep32_64_equiv.py `
  formal/python/tests/test_state_doc_comp_fn_rep32_link_discharge.py `
  formal/python/tests/test_state_doc_comp_fn_rep_nonalias_equivalence01.py `
  formal/python/tests/test_state_doc_comp03_comp05_transition.py `
  formal/python/tests/test_state_doc_comp_evol_link_discharge.py `
  formal/python/tests/test_state_doc_cv_lane_wiring.py `
  formal/python/tests/test_state_doc_mainline_does_not_depend_on_variantA.py `
  formal/python/tests/test_state_doc_mainline_cannot_claim_beta_nonzero.py `
  -q

Write-Host "OK" -ForegroundColor Green
