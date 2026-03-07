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
  formal/python/tests/test_pillar_status_matrix_consistency_gate.py `
  formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py `
  formal/python/tests/test_pillar_phase_advancement_gate.py `
  formal/python/tests/test_locked_queue_phase_adherence_standard_gate.py `
  formal/python/tests/test_cosmo_background_kickoff_gate.py `
  formal/python/tests/test_cosmo_bg_micro01_object_surface_gate.py `
  formal/python/tests/test_cosmo_bg_micro02_expansion_law_surface_gate.py `
  formal/python/tests/test_cosmo_bg_micro03_source_coupling_surface_gate.py `
  formal/python/tests/test_cosmo_bg_micro04_regime_falsifiability_surface_gate.py `
  formal/python/tests/test_cosmo_bg_micro05_package_freeze_reopen_policy_gate.py `
  formal/python/tests/test_cosmo_bg_micro06_state_checkpoint_boundary_gate.py `
  formal/python/tests/test_cosmo_bg_micro07_matrix_lane_drift_alarm_gate.py `
  formal/python/tests/test_cosmo_bg_micro08_locked_queue_unlock_transition_packet_gate.py `
  formal/python/tests/test_cosmo_bg_micro09_authorized_unlock_conditions_checklist_packet_gate.py `
  formal/python/tests/test_cosmo_bg_micro10_lock_transition_dryrun_attestation_packet_gate.py `
  formal/python/tests/test_cosmo_bg_micro11_dryrun_reconciliation_packet_gate.py `
  formal/python/tests/test_cosmo_bg_micro12_dryrun_closure_packet_gate.py `
  formal/python/tests/test_cosmo_bg_micro13_dryrun_custody_packet_gate.py `
  formal/python/tests/test_cosmo_bg_micro14_dryrun_custody_confirmation_packet_gate.py `
  formal/python/tests/test_cosmo_bg_micro15_dryrun_custody_confirmation_attestation_packet_gate.py `
  formal/python/tests/test_cosmo_bg_micro16_dryrun_custody_confirmation_attestation_confirmation_packet_gate.py `
  formal/python/tests/test_cosmo_bg_micro17_dryrun_custody_confirmation_attestation_confirmation_attestation_packet_gate.py `
  formal/python/tests/test_cosmo_bg_micro18_dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_packet_gate.py `
  formal/python/tests/test_cosmo_bg_micro19_dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_packet_gate.py `
  formal/python/tests/test_cosmo_bg_micro20_dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_gate.py `
  formal/python/tests/test_cosmo_phase_adherence_snapshot_gate.py `
  formal/python/tests/test_cosmo_background_pillar_package_rollup_gate.py `
  formal/python/tests/test_cosmo_state_rollup_checkpoint_gate.py `
  formal/python/tests/test_cosmo_matrix_rollup_crosspin_gate.py `
  formal/python/tests/test_orchestration_report_contract_gate.py `
  formal/python/tests/test_dev_stack_preflight.py `
  formal/python/tests/test_ci_tranche3_gates.py `
  formal/python/tests/test_sql_integrity_snapshot_tool.py `
  -q

Write-Host "OK" -ForegroundColor Green
