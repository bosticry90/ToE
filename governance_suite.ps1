$ErrorActionPreference = 'Stop'

Write-Host "Running governance suite via ./py.ps1" -ForegroundColor Cyan

Write-Host "Running local stack preflight" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.dev_stack_preflight
if ($LASTEXITCODE -ne 0) {
  throw "Dev stack preflight failed."
}

Write-Host "Running tooling validation checks (no writes)" -ForegroundColor Cyan
pwsh -NoProfile -ExecutionPolicy Bypass -File ./tooling_validate.ps1
if ($LASTEXITCODE -ne 0) {
  throw "Tooling validate checks failed."
}

Write-Host "Running local divergence guardrail" -ForegroundColor Cyan
git show-ref --verify --quiet refs/remotes/origin/main
if ($LASTEXITCODE -eq 0) {
  $aheadLimit = 20
  $aheadCountRaw = git rev-list --count origin/main..HEAD
  if ($LASTEXITCODE -ne 0) {
    throw "Unable to compute local ahead count against origin/main."
  }
  $aheadCount = [int]($aheadCountRaw.Trim())
  Write-Host "divergence_guardrail.ahead_count=$aheadCount limit=$aheadLimit"
  if ($aheadCount -gt $aheadLimit) {
    throw "Divergence guardrail failed: local branch is ahead by $aheadCount commits (limit $aheadLimit)."
  }
}

./py.ps1 -m pytest `
  formal/python/tests/test_active_dependency_baseline_lock_gate.py `
  formal/python/tests/test_dependency_security_scan_schedule_gate.py `
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
  formal/python/tests/test_ct01_no_superluminal_propagation_v0_front_door.py `
  formal/python/tests/test_ct01_no_superluminal_propagation_v0_surface_contract_freeze.py `
  formal/python/tests/test_ct01_no_superluminal_propagation_v0_pinned_artifacts.py `
  formal/python/tests/test_ct01_no_superluminal_propagation_v0_lock.py `
  formal/python/tests/test_state_doc_comp_fn_rep_policy.py `
  formal/python/tests/test_state_doc_comp_fn_rep32_64_equiv.py `
  formal/python/tests/test_state_doc_comp_fn_rep32_link_discharge.py `
  formal/python/tests/test_state_doc_comp_fn_rep_nonalias_equivalence01.py `
  formal/python/tests/test_state_doc_comp03_comp05_transition.py `
  formal/python/tests/test_state_doc_comp_evol_link_discharge.py `
  formal/python/tests/test_state_doc_cv_lane_wiring.py `
  formal/python/tests/test_repo_status_audit_20260315_gate.py `
  formal/python/tests/test_state_doc_mainline_does_not_depend_on_variantA.py `
  formal/python/tests/test_state_doc_mainline_cannot_claim_beta_nonzero.py `
  formal/python/tests/test_pillar_status_matrix_consistency_gate.py `
  formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py `
  formal/python/tests/test_toe_closure_and_action_promotion_standards_gate.py `
  formal/python/tests/test_toe_closure_status_language_ambiguity_guard_gate.py `
  formal/python/tests/test_toe_seam_status_split_gate.py `
  formal/python/tests/test_toe_language_enforcement_policy_gate.py `
  formal/python/tests/test_toe_status_language_lock_guard_gate.py `
  formal/python/tests/test_scored_audit_matrix_schema_and_language_gate.py `
  formal/python/tests/test_pillar_phase_advancement_gate.py `
  formal/python/tests/test_foundational_derivation_chain_coverage_gate.py `
  formal/python/tests/test_toe_master_action_seam_registry_gate.py `
  formal/python/tests/test_toe_master_action_assumption_classification_gate.py `
  formal/python/tests/test_toe_master_action_shadow_numerics_cycle01_gate.py `
  formal/python/tests/test_foundational_prediction_scaffold_coverage_gate.py `
  formal/python/tests/test_toe_empirical_comparison_packet_01_gate.py `
  formal/python/tests/test_toe_empirical_packet_01_evidence_promotion_gate.py `
  formal/python/tests/test_qm_empirical_comparison_packet_01_gate.py `
  formal/python/tests/test_qm_empirical_comparison_packet_02_gate.py `
  formal/python/tests/test_qm_empirical_packet_02_decision_record_gate.py `
  formal/python/tests/test_gr_empirical_packet_02_decision_record_gate.py `
  formal/python/tests/test_stat_empirical_packet_02_decision_record_gate.py `
  formal/python/tests/test_cosmo_empirical_packet_02_decision_record_gate.py `
  formal/python/tests/test_em_empirical_packet_02_decision_record_gate.py `
  formal/python/tests/test_qft_empirical_packet_02_decision_record_gate.py `
  formal/python/tests/test_sr_empirical_packet_02_decision_record_gate.py `
  formal/python/tests/test_empirical_packet02_decision_ledger_parity_gate.py `
  formal/python/tests/test_packet02_m4_seam_coupling_gate.py `
  formal/python/tests/test_qm_empirical_comparison_packet_03_gate.py `
  formal/python/tests/test_gr_empirical_comparison_packet_03_gate.py `
  formal/python/tests/test_stat_empirical_comparison_packet_03_gate.py `
  formal/python/tests/test_cosmo_empirical_comparison_packet_03_gate.py `
  formal/python/tests/test_em_empirical_comparison_packet_03_gate.py `
  formal/python/tests/test_qft_empirical_comparison_packet_03_gate.py `
  formal/python/tests/test_sr_empirical_comparison_packet_03_gate.py `
    formal/python/tests/test_gr_qm_seam_promotion_cycle01_theorem_gate.py `
    formal/python/tests/test_gr_qm_seam_promotion_cycle02_discharge_gate.py `
    formal/python/tests/test_gr_qm_seam_promotion_cycle03_class_flip_gate.py `
    formal/python/tests/test_proof_debt_marker_stability_gate.py `
    formal/python/tests/test_proof_debt_burndown_cycle05_gate.py `
    formal/python/tests/test_qm_m2_assumption_minimization_depth_exemplar_cycle02_gate.py `
    formal/python/tests/test_gr_m2_assumption_minimization_depth_exemplar_cycle02_gate.py `
    formal/python/tests/test_stat_m2_assumption_minimization_depth_exemplar_cycle02_gate.py `
  formal/python/tests/test_qm_empirical_comparison_packet_04_gate.py `
  formal/python/tests/test_gr_empirical_comparison_packet_04_gate.py `
  formal/python/tests/test_gr_empirical_comparison_packet_05_gate.py `
  formal/python/tests/test_gr_empirical_packet_05_artifact_schema_gate.py `
  formal/python/tests/test_sr_empirical_comparison_packet_05_gate.py `
  formal/python/tests/test_sr_empirical_packet_05_artifact_schema_gate.py `
  formal/python/tests/test_empirical_packet05_decision_ledger_parity_gate.py `
  formal/python/tests/test_empirical_packet05_falsification_surface_gate.py `
  formal/python/tests/test_foundational_empirical_packet05_override_policy_gate.py `
  formal/python/tests/test_stat_empirical_comparison_packet_04_gate.py `
  formal/python/tests/test_cosmo_empirical_comparison_packet_04_gate.py `
  formal/python/tests/test_em_empirical_comparison_packet_04_gate.py `
  formal/python/tests/test_qft_empirical_comparison_packet_04_gate.py `
  formal/python/tests/test_sr_empirical_comparison_packet_04_gate.py `
  formal/python/tests/test_foundational_empirical_packet05_matrix_consistency_gate.py `
  formal/python/tests/test_foundational_empirical_packet05_progression_policy_gate.py `
  formal/python/tests/test_toe_master_action_shadow_numerics_cycle02_gate.py `
  formal/python/tests/test_toe_master_action_shadow_numerics_cycle03_gate.py `
  formal/python/tests/test_toe_master_action_shadow_numerics_cycle04_gate.py `
  formal/python/tests/test_toe_master_action_shadow_numerics_cycle05_gate.py `
  formal/python/tests/test_toe_master_action_shadow_numerics_cycle06_gate.py `
  formal/python/tests/test_toe_master_action_shadow_numerics_cycle07_gate.py `
  formal/python/tests/test_toe_master_action_shadow_numerics_cycle08_gate.py `
  formal/python/tests/test_toe_master_action_shadow_numerics_cycle09_gate.py `
  formal/python/tests/test_toe_master_action_shadow_numerics_cycle10_gate.py `
  formal/python/tests/test_toe_master_action_shadow_numerics_cycle11_gate.py `
  formal/python/tests/test_toe_master_action_shadow_numerics_cycle12_gate.py `
  formal/python/tests/test_toe_master_action_shadow_numerics_cycle13_gate.py `
  formal/python/tests/test_toe_master_action_shadow_numerics_cycle14_gate.py `
  formal/python/tests/test_toe_master_action_shadow_numerics_cycle15_gate.py `
  formal/python/tests/test_qm_empirical_packet_01_evidence_promotion_gate.py `
  formal/python/tests/test_gr_empirical_comparison_packet_01_gate.py `
  formal/python/tests/test_gr_empirical_packet_01_evidence_promotion_gate.py `
  formal/python/tests/test_stat_empirical_comparison_packet_01_gate.py `
  formal/python/tests/test_stat_empirical_packet_01_evidence_promotion_gate.py `
  formal/python/tests/test_cosmo_empirical_comparison_packet_01_gate.py `
  formal/python/tests/test_cosmo_empirical_packet_01_evidence_promotion_gate.py `
  formal/python/tests/test_em_empirical_comparison_packet_01_gate.py `
  formal/python/tests/test_em_empirical_packet_01_evidence_promotion_gate.py `
  formal/python/tests/test_qft_empirical_comparison_packet_01_gate.py `
  formal/python/tests/test_qft_empirical_packet_01_evidence_promotion_gate.py `
  formal/python/tests/test_sr_empirical_comparison_packet_01_gate.py `
  formal/python/tests/test_sr_empirical_packet_01_evidence_promotion_gate.py `
  formal/python/tests/test_foundational_empirical_packet_matrix_consistency_gate.py `
  formal/python/tests/test_foundational_empirical_packet02_matrix_consistency_gate.py `
  formal/python/tests/test_foundational_empirical_packet02_decision_balance_gate.py `
  formal/python/tests/test_foundational_empirical_packet03_matrix_consistency_gate.py `
  formal/python/tests/test_foundational_empirical_packet03_decision_policy_gate.py `
  formal/python/tests/test_foundational_empirical_packet04_matrix_consistency_gate.py `
  formal/python/tests/test_foundational_empirical_packet04_decision_policy_gate.py `
  formal/python/tests/test_foundational_empirical_packet_progression_policy_gate.py `
  formal/python/tests/test_foundational_derivation_chain_matrix_consistency_gate.py `
  formal/python/tests/test_pillar_deep_maturity_program_gate.py `
  formal/python/tests/test_phase3_m3_consolidation_promotion_cycle01_gate.py `
  formal/python/tests/test_qm_m3_completion_promotion_cycle01_gate.py `
  formal/python/tests/test_gr_m3_completion_promotion_cycle01_gate.py `
  formal/python/tests/test_stat_m3_completion_promotion_cycle01_gate.py `
  formal/python/tests/test_cosmo_m3_completion_promotion_cycle01_gate.py `
  formal/python/tests/test_em_m3_completion_promotion_cycle01_gate.py `
  formal/python/tests/test_qft_m3_completion_promotion_cycle01_gate.py `
  formal/python/tests/test_sr_m3_completion_promotion_cycle01_gate.py `
  formal/python/tests/test_qm_m4_seam_closure_promotion_cycle01_gate.py `
  formal/python/tests/test_gr_m4_seam_closure_promotion_cycle01_gate.py `
  formal/python/tests/test_stat_m4_seam_closure_promotion_cycle01_gate.py `
  formal/python/tests/test_cosmo_m4_seam_closure_promotion_cycle01_gate.py `
  formal/python/tests/test_em_m4_seam_closure_promotion_cycle01_gate.py `
  formal/python/tests/test_qft_m4_seam_closure_promotion_cycle01_gate.py `
  formal/python/tests/test_sr_m4_seam_closure_promotion_cycle01_gate.py `
  formal/python/tests/test_sr_m5_theory_parity_link_cycle56_gate.py `
  formal/python/tests/test_sr_m5_phase5_cycle_advancement_contract_gate.py `
  formal/python/tests/test_sr_m5_cycle_archive_discipline_gate.py `
  formal/python/tests/test_pillar_deep_maturity_next_target_semantics_gate.py `
  formal/python/tests/test_phase5_m5_completion_closeout_gate.py `
  formal/python/tests/test_sr_m5_archive_retention_policy_gate.py `
  formal/python/tests/test_sr_m5_periodic_quality_checkpoint_gate.py `
  formal/python/tests/test_master_action_variant_cycle18_sensitivity_gate.py `
  formal/python/tests/test_gr01_publication_grade_discharge_package_gate.py `
  formal/python/tests/test_gr01_publication_theorem_claim_advancement_gate.py `
  formal/python/tests/test_gr_continuum_discharge_criteria_cycle10_gate.py `
  formal/python/tests/test_gr01_function_space_discrete_regularity_evidence_gate.py `
  formal/python/tests/test_gr01_function_space_continuum_regularity_route_gate.py `
  formal/python/tests/test_gr01_function_space_nonclaim_boundary_evidence_gate.py `
  formal/python/tests/test_gr01_function_space_completion_criteria_gate.py `
  formal/python/tests/test_toe_qft_scalar_propagator_gate.py `
  formal/python/tests/test_toe_qft_scalar_route_review_readiness_gate.py `
  formal/python/tests/test_toe_qft_scalar_route_submission_candidate_gate.py `
  formal/python/tests/test_toe_qft_scalar_route_submission_readiness_gate.py `
  formal/python/tests/test_toe_qft_scalar_route_submission_package_gate.py `
  formal/python/tests/test_toe_qft_scalar_route_submission_support_package_gate.py `
  formal/python/tests/test_qft_gr_seam_reactivation_sliceb_increment15_authority_mirror_gate.py `
  formal/python/tests/test_qft_gr_seam_reactivation_sliceb_science_first_enforcement_gate.py `
  formal/python/tests/test_qft_gr_seam_reactivation_sliceb_derivation_completeness_enforcement_gate.py `
  formal/python/tests/test_toe_qft_gr_seam_packet41_successor_discriminator_package_gate.py `
  formal/python/tests/test_pillar_deep_maturity_m2_completion_gate.py `
  formal/python/tests/test_qm_m2_analytic_completeness_scaffold_cycle01_gate.py `
  formal/python/tests/test_qm_m2_canonical_equivalence_scaffold_cycle01_gate.py `
  formal/python/tests/test_qm_m2_assumption_minimization_scaffold_cycle01_gate.py `
  formal/python/tests/test_qm_m2_literature_alignment_scaffold_cycle01_gate.py `
  formal/python/tests/test_qm_m2_completion_promotion_cycle01_gate.py `
  formal/python/tests/test_gr_m2_analytic_completeness_scaffold_cycle01_gate.py `
  formal/python/tests/test_gr_m2_canonical_equivalence_scaffold_cycle01_gate.py `
  formal/python/tests/test_gr_m2_assumption_minimization_scaffold_cycle01_gate.py `
  formal/python/tests/test_gr_m2_literature_alignment_scaffold_cycle01_gate.py `
  formal/python/tests/test_gr_m2_completion_promotion_cycle01_gate.py `
  formal/python/tests/test_stat_m2_analytic_completeness_scaffold_cycle01_gate.py `
  formal/python/tests/test_stat_m2_canonical_equivalence_scaffold_cycle01_gate.py `
  formal/python/tests/test_stat_m2_assumption_minimization_scaffold_cycle01_gate.py `
  formal/python/tests/test_stat_m2_literature_alignment_scaffold_cycle01_gate.py `
  formal/python/tests/test_stat_m2_completion_promotion_cycle01_gate.py `
  formal/python/tests/test_cosmo_m2_analytic_completeness_scaffold_cycle01_gate.py `
  formal/python/tests/test_cosmo_m2_canonical_equivalence_scaffold_cycle01_gate.py `
  formal/python/tests/test_cosmo_m2_assumption_minimization_scaffold_cycle01_gate.py `
  formal/python/tests/test_cosmo_m2_literature_alignment_scaffold_cycle01_gate.py `
  formal/python/tests/test_cosmo_m2_completion_promotion_cycle01_gate.py `
  formal/python/tests/test_em_m2_analytic_completeness_scaffold_cycle01_gate.py `
  formal/python/tests/test_em_m2_canonical_equivalence_scaffold_cycle01_gate.py `
  formal/python/tests/test_em_m2_assumption_minimization_scaffold_cycle01_gate.py `
  formal/python/tests/test_em_m2_literature_alignment_scaffold_cycle01_gate.py `
  formal/python/tests/test_em_m2_completion_promotion_cycle01_gate.py `
  formal/python/tests/test_qft_m2_analytic_completeness_scaffold_cycle01_gate.py `
  formal/python/tests/test_qft_m2_canonical_equivalence_scaffold_cycle01_gate.py `
  formal/python/tests/test_qft_m2_assumption_minimization_scaffold_cycle01_gate.py `
  formal/python/tests/test_qft_m2_literature_alignment_scaffold_cycle01_gate.py `
  formal/python/tests/test_qft_m2_completion_promotion_cycle01_gate.py `
  formal/python/tests/test_sr_m2_analytic_completeness_scaffold_cycle01_gate.py `
  formal/python/tests/test_sr_m2_canonical_equivalence_scaffold_cycle01_gate.py `
  formal/python/tests/test_sr_m2_assumption_minimization_scaffold_cycle01_gate.py `
  formal/python/tests/test_sr_m2_literature_alignment_scaffold_cycle01_gate.py `
  formal/python/tests/test_sr_m2_completion_promotion_cycle01_gate.py `
  formal/python/tests/test_qm_empirical_discriminator_emp_qm_01_scaffold_gate.py `
  formal/python/tests/test_gr_empirical_discriminator_emp_gr_01_scaffold_gate.py `
  formal/python/tests/test_stat_empirical_discriminator_emp_stat_01_scaffold_gate.py `
  formal/python/tests/test_cosmo_empirical_discriminator_emp_cosmo_01_scaffold_gate.py `
  formal/python/tests/test_em_empirical_discriminator_emp_em_01_scaffold_gate.py `
  formal/python/tests/test_qft_empirical_discriminator_emp_qft_01_scaffold_gate.py `
  formal/python/tests/test_sr_empirical_discriminator_emp_sr_01_scaffold_gate.py `
  formal/python/tests/test_pillar_full_completion_action_plan_gate.py `
  formal/python/tests/test_phase4_global_unification_and_residual_debt_gate.py `
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
  formal/python/tests/test_cosmo_rollup_pointer_completeness_gate.py `
  formal/python/tests/test_cosmo_matrix_rollup_crosspin_gate.py `
  formal/python/tests/test_cosmo_external_implications_reference_surface_policy_gate.py `
  formal/python/tests/test_cosmo_external_implications_cross_surface_parity_gate.py `
  formal/python/tests/test_cosmo_derivation_completeness_gate_readiness_packet_cycle01_gate.py `
  formal/python/tests/test_cosmo_der01_theorem_surface_scaffold_cycle01_gate.py `
  formal/python/tests/test_cosmo_der02_governance_coupling_scaffold_cycle01_gate.py `
  formal/python/tests/test_cosmo_der01_closure_package_cycle01_gate.py `
  formal/python/tests/test_cosmo_der02_closure_package_cycle01_gate.py `
  formal/python/tests/test_stat_der01_theorem_surface_scaffold_coupling_cycle01_gate.py `
  formal/python/tests/test_stat_der01_theorem_body_scope_boundary_cycle01_gate.py `
  formal/python/tests/test_stat_der01_theorem_body_scaffold_coupling_cycle01_gate.py `
  formal/python/tests/test_stat_der01_discharge_scaffold_coupling_cycle01_gate.py `
  formal/python/tests/test_stat_der01_object_surface_scaffold_coupling_cycle01_gate.py `
  formal/python/tests/test_stat_der02_regime_closure_coupling_scaffold_coupling_cycle01_gate.py `
  formal/python/tests/test_stat_der02_theorem_body_scope_boundary_cycle01_gate.py `
  formal/python/tests/test_stat_der02_theorem_body_scaffold_coupling_cycle01_gate.py `
  formal/python/tests/test_stat_der02_discharge_scaffold_coupling_cycle01_gate.py `
  formal/python/tests/test_stat_der02_object_surface_scaffold_coupling_cycle01_gate.py `
  formal/python/tests/test_orchestration_report_contract_gate.py `
  formal/python/tests/test_conftest_signature_stability_gate.py `
  formal/python/tests/test_repository_retention_policy_contract_gate.py `
  formal/python/tests/test_local_execution_posture_gate.py `
  formal/python/tests/test_dev_stack_preflight.py `
  formal/python/tests/test_ci_tranche3_gates.py `
  formal/python/tests/test_sql_integrity_snapshot_tool.py `
  -q

if ($LASTEXITCODE -ne 0) {
  throw "Governance pytest tranche failed."
}

Write-Host "Running local orchestration manifest" -ForegroundColor Cyan
./py.ps1 -m formal.python.orchestration.runner --manifest formal/docs/release/TOE_ASYNC_ORCHESTRATION_MANIFEST_v0.json --output formal/output/reports/toe_orchestration_report_v0.json --max-concurrency 2 --fail-on-check-failure
if ($LASTEXITCODE -ne 0) {
  throw "Orchestration runner failed."
}

Write-Host "Running SQL integrity snapshot mirror" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.sql_integrity_snapshot --db formal/output/reports/toe_integrity_snapshot_v0.sqlite3 --report formal/output/reports/toe_integrity_snapshot_report_v0.json --fail-on-issues
if ($LASTEXITCODE -ne 0) {
  throw "SQL integrity snapshot reported issues."
}

# Local Rust trust-core execution is policy-enforced when cargo is available.
# Set TOE_REQUIRE_RUST_LOCAL=1 to fail hard when cargo is missing.
$cargo = Get-Command cargo -ErrorAction SilentlyContinue
if ($null -ne $cargo) {
  Write-Host "Running Rust trust-core pilot" -ForegroundColor Cyan
  cargo run --manifest-path formal/rust/toe_trust_core/Cargo.toml
  if ($LASTEXITCODE -ne 0) {
    throw "Rust trust-core pilot failed."
  }
} elseif ($env:TOE_REQUIRE_RUST_LOCAL -eq '1') {
  throw "Rust is required locally (TOE_REQUIRE_RUST_LOCAL=1) but cargo was not found."
} else {
  Write-Host "WARN: cargo not found; skipping local Rust trust-core run." -ForegroundColor Yellow
}

Write-Host "OK" -ForegroundColor Green



