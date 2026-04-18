param(
  [switch]$AllowDivergenceOverride,
  [switch]$UseInvalidationSelection,
  [string]$InvalidationBaseRef = 'HEAD~1',
  [switch]$IncludeInvalidationWorkingTree,
  [switch]$EnableReadOnlyParallel,
  [string]$ReadOnlyParallelWorkers = 'auto',
  [string]$ParallelCapabilityReportPath = 'formal/output/reports/governance_parallel_capability_v0.json'
)

function Invoke-GovernanceGate {
  param(
    [Parameter(Mandatory = $true)][string]$TargetRow,
    [Parameter(Mandatory = $true)][string]$BlockerClass,
    [Parameter(Mandatory = $true)][string]$Declaration
  )

  $matrixPath = "formal/docs/release/TOE_GLOBAL_COMPLETION_MATRIX_v0.md"

  if (-not (Test-Path $Declaration)) {
    throw "Governance gate failed: declaration not found at '$Declaration'."
  }
  if (-not (Test-Path $matrixPath)) {
    throw "Governance gate failed: completion matrix not found at '$matrixPath'."
  }

  $declarationText = Get-Content -Path $Declaration -Raw
  if ($declarationText -notmatch [Regex]::Escape("Target row: $TargetRow")) {
    throw "Governance gate failed: declaration '$Declaration' does not pin target row '$TargetRow'."
  }
  if ($declarationText -notmatch [Regex]::Escape("Blocker class: $BlockerClass")) {
    throw "Governance gate failed: declaration '$Declaration' does not pin blocker class '$BlockerClass'."
  }

  $matrixText = Get-Content -Path $matrixPath -Raw
  $rowPattern = "(?m)^\|\s*" + [Regex]::Escape($TargetRow) + "\s*\|.*$"
  $rowMatch = [Regex]::Match($matrixText, $rowPattern)
  if (-not $rowMatch.Success) {
    throw "Governance gate failed: target row '$TargetRow' not found in '$matrixPath'."
  }

  $cells = $rowMatch.Value.Trim('|').Split('|') | ForEach-Object { $_.Trim() }
  if ($cells.Count -lt 8) {
    throw "Governance gate failed: matrix row '$TargetRow' has unexpected column count."
  }

  $rowBlockerClass = $cells[4]
  $primaryTarget = $cells[5]
  $primaryArtifact = $cells[6]
  $primaryGate = $cells[7]

  if ($rowBlockerClass -ne $BlockerClass) {
    throw "Governance gate failed: matrix blocker class '$rowBlockerClass' does not match expected '$BlockerClass' for row '$TargetRow'."
  }

  foreach ($requiredPath in @($primaryTarget, $primaryArtifact, $primaryGate)) {
    if (-not (Test-Path $requiredPath)) {
      throw "Governance gate failed: matrix-pinned path '$requiredPath' is missing for row '$TargetRow'."
    }
  }

  Write-Host "governance_gate.ok row=$TargetRow blocker=$BlockerClass declaration=$Declaration" -ForegroundColor Green
}

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

Write-Host "Running authority-surface parity precheck" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.authority_surface_parity_check
if ($LASTEXITCODE -ne 0) {
  throw "Authority-surface parity precheck failed."
}

Write-Host "Running local divergence guardrail" -ForegroundColor Cyan
git show-ref --verify --quiet refs/remotes/origin/main
if ($LASTEXITCODE -eq 0) {
  $warnLimit = 10
  $hardLimit = 20
  $overrideLimit = 30
  $aheadCountRaw = git rev-list --count origin/main..HEAD
  if ($LASTEXITCODE -ne 0) {
    throw "Unable to compute local ahead count against origin/main."
  }
  $aheadCount = [int]($aheadCountRaw.Trim())
  Write-Host "divergence_guardrail.ahead_count=$aheadCount warn_limit=$warnLimit hard_limit=$hardLimit override_limit=$overrideLimit"

  if ($aheadCount -le $warnLimit) {
    # Normal operating range.
  } elseif ($aheadCount -le $hardLimit) {
    Write-Host "WARN: divergence guardrail warning band: local branch is ahead by $aheadCount commits (warn threshold $warnLimit)." -ForegroundColor Yellow
  } elseif ($aheadCount -le $overrideLimit) {
    if (-not $AllowDivergenceOverride -and $env:TOE_ALLOW_DIVERGENCE_OVERRIDE -ne '1') {
      throw "Divergence guardrail failed: local branch is ahead by $aheadCount commits (hard limit $hardLimit). Re-run with -AllowDivergenceOverride or set TOE_ALLOW_DIVERGENCE_OVERRIDE=1 for temporary override up to $overrideLimit."
    }
    Write-Host "WARN: divergence guardrail override band active: local branch is ahead by $aheadCount commits (override limit $overrideLimit)." -ForegroundColor Yellow
  } else {
    throw "Divergence guardrail failed: local branch is ahead by $aheadCount commits (override limit $overrideLimit)."
  }
}

$governanceManifestPath = "formal/docs/release/GOVERNANCE_TEST_MANIFEST_v1.json"
$governanceManifestGroup = "governance_pytests"

# Governance pytest execution is manifest-authoritative only; no secondary text-pinned registry is maintained.
# Canonical gate reference retained for cross-surface contract parity:
# formal/python/tests/test_pillar_phase_advancement_gate.py
# BEGIN GOVERNANCE MANIFEST TEST REFERENCES
# Canonical manifest-backed gate references retained for text-parity contract tests.
# formal/python/tests/test_active_dependency_baseline_lock_gate.py
# formal/python/tests/test_dependency_security_scan_schedule_gate.py
# formal/python/tests/test_state_theory_dag.py
# formal/python/tests/test_state_core_generation_integrity_gate.py
# formal/python/tests/test_state_core_generated_block_manual_edit_prohibition_gate.py
# formal/python/tests/test_cosmo_sr_state_core_generation_integrity_gate.py
# formal/python/tests/test_ws10_branch_boundary_status_family_gate.py
# formal/python/tests/test_ws10_task_status_table_family_gate.py
# formal/python/tests/test_ws10_evidence_log_family_gate.py
# formal/python/tests/test_ws10_scientific_artifact_lineage_family_gate.py
# formal/python/tests/test_ws10_scientific_artifact_gate_metadata_family_gate.py
# formal/python/tests/test_ws10_additive_candidate_declaration_metadata_family_gate.py
# formal/python/tests/test_state_core_compression_yield_gate.py
# formal/python/tests/test_state_doc_no_duplicate_gapids.py
# formal/python/tests/test_toe_target_spec_doc.py
# formal/python/tests/test_relativistic_limit_dispersion_lane_doc.py
# formal/python/tests/test_nonrelativistic_limit_nlse_lane_doc.py
# formal/python/tests/test_weak_field_poisson_lane_doc.py
# formal/python/tests/test_rl02_nonrelativistic_nlse_v0_front_door.py
# formal/python/tests/test_rl02_nonrelativistic_nlse_v0_surface_contract_freeze.py
# formal/python/tests/test_rl02_nonrelativistic_nlse_v0_pinned_artifacts.py
# formal/python/tests/test_rl02_nonrelativistic_nlse_v0_lock.py
# formal/python/tests/test_rl01_relativistic_dispersion_v0_front_door.py
# formal/python/tests/test_rl01_relativistic_dispersion_v0_surface_contract_freeze.py
# formal/python/tests/test_rl01_relativistic_dispersion_v0_pinned_artifacts.py
# formal/python/tests/test_rl01_relativistic_dispersion_v0_lock.py
# formal/python/tests/test_ct01_no_superluminal_propagation_v0_front_door.py
# formal/python/tests/test_ct01_no_superluminal_propagation_v0_surface_contract_freeze.py
# formal/python/tests/test_ct01_no_superluminal_propagation_v0_pinned_artifacts.py
# formal/python/tests/test_ct01_no_superluminal_propagation_v0_lock.py
# formal/python/tests/test_state_doc_comp_fn_rep_policy.py
# formal/python/tests/test_state_doc_comp_fn_rep32_64_equiv.py
# formal/python/tests/test_state_doc_comp_fn_rep32_link_discharge.py
# formal/python/tests/test_state_doc_comp_fn_rep_nonalias_equivalence01.py
# formal/python/tests/test_state_doc_comp03_comp05_transition.py
# formal/python/tests/test_state_doc_comp_evol_link_discharge.py
# formal/python/tests/test_state_doc_cv_lane_wiring.py
# formal/python/tests/test_repo_status_audit_20260315_gate.py
# formal/python/tests/test_state_doc_mainline_does_not_depend_on_variantA.py
# formal/python/tests/test_state_doc_mainline_cannot_claim_beta_nonzero.py
# formal/python/tests/test_pillar_status_matrix_consistency_gate.py
# formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py
# formal/python/tests/test_toe_closure_and_action_promotion_standards_gate.py
# formal/python/tests/test_toe_closure_status_language_ambiguity_guard_gate.py
# formal/python/tests/test_toe_seam_status_split_gate.py
# formal/python/tests/test_toe_language_enforcement_policy_gate.py
# formal/python/tests/test_toe_status_language_lock_guard_gate.py
# formal/python/tests/test_scored_audit_matrix_schema_and_language_gate.py
# formal/python/tests/test_pillar_phase_advancement_gate.py
# formal/python/tests/test_foundational_derivation_chain_coverage_gate.py
# formal/python/tests/test_toe_master_action_seam_registry_gate.py
# formal/python/tests/test_discovery_priority_queue_report.py
# formal/python/tests/test_qm_stat_discovery_tranche_terminal_outcome_gate.py
# formal/python/tests/test_qm_stat_discovery_discriminator_tranche_report.py
# formal/python/tests/test_qm_stat_discovery_ruling_report.py
# formal/python/tests/test_qm_stat_discovery_interpretation_report.py
# formal/python/tests/test_qm_stat_discovery_numerical_probe_report.py
# formal/python/tests/test_qm_stat_discovery_numerical_probe_execution_report.py
# formal/python/tests/test_qm_stat_discovery_derivation_probe_ruling_report.py
# formal/python/tests/test_qm_stat_discovery_post_derivation_probe_decision_report.py
# formal/python/tests/test_qm_stat_discovery_next_route_decision_report.py
# formal/python/tests/test_qft_gr_discovery_discriminator_tranche_report.py
# formal/python/tests/test_qft_gr_discovery_ruling_report.py
# formal/python/tests/test_qft_gr_discovery_tranche_terminal_outcome_gate.py
# formal/python/tests/test_qft_gr_discovery_interpretation_report.py
# formal/python/tests/test_qft_gr_discovery_post_cycle_decision_report.py
# formal/python/tests/test_discovery_queue_transition_decision_report.py
# formal/python/tests/test_discovery_queue_review_pass_report.py
# formal/python/tests/test_discovery_queue_rescoring_pass_report.py
# formal/python/tests/test_gr_discovery_tranche_terminal_outcome_gate.py
# formal/python/tests/test_gr_discovery_discriminator_tranche_report.py
# formal/python/tests/test_gr_discovery_ruling_report.py
# formal/python/tests/test_toe_master_action_assumption_classification_gate.py
# formal/python/tests/test_toe_master_action_shadow_numerics_cycle01_gate.py
# formal/python/tests/test_foundational_prediction_scaffold_coverage_gate.py
# formal/python/tests/test_toe_empirical_comparison_packet_01_gate.py
# formal/python/tests/test_toe_empirical_packet_01_evidence_promotion_gate.py
# formal/python/tests/test_qm_empirical_comparison_packet_01_gate.py
# formal/python/tests/test_qm_empirical_comparison_packet_02_gate.py
# formal/python/tests/test_qm_empirical_packet_02_decision_record_gate.py
# formal/python/tests/test_gr_empirical_packet_02_decision_record_gate.py
# formal/python/tests/test_stat_empirical_packet_02_decision_record_gate.py
# formal/python/tests/test_cosmo_empirical_packet_02_decision_record_gate.py
# formal/python/tests/test_em_empirical_packet_02_decision_record_gate.py
# formal/python/tests/test_qft_empirical_packet_02_decision_record_gate.py
# formal/python/tests/test_sr_empirical_packet_02_decision_record_gate.py
# formal/python/tests/test_empirical_packet02_decision_ledger_parity_gate.py
# formal/python/tests/test_packet02_m4_seam_coupling_gate.py
# formal/python/tests/test_qm_empirical_comparison_packet_03_gate.py
# formal/python/tests/test_gr_empirical_comparison_packet_03_gate.py
# formal/python/tests/test_stat_empirical_comparison_packet_03_gate.py
# formal/python/tests/test_cosmo_empirical_comparison_packet_03_gate.py
# formal/python/tests/test_em_empirical_comparison_packet_03_gate.py
# formal/python/tests/test_qft_empirical_comparison_packet_03_gate.py
# formal/python/tests/test_sr_empirical_comparison_packet_03_gate.py
# formal/python/tests/test_gr_qm_seam_promotion_cycle01_theorem_gate.py
# formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle01_gate.py
# formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle02_gate.py
# formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle03_gate.py
# formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle04_gate.py
# formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle05_gate.py
# formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle06_gate.py
# formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle01_to_02_synthesis_gate.py
# formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle02_to_03_synthesis_gate.py
# formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle03_to_04_synthesis_gate.py
# formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle04_to_05_synthesis_gate.py
# formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle05_to_06_synthesis_gate.py
# formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle01_gate.py
# formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle02_gate.py
# formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle03_gate.py
# formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle04_gate.py
# formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle05_gate.py
# formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle06_gate.py
# formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle01_synthesis_gate.py
# formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle01_to_02_synthesis_gate.py
# formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle02_to_03_synthesis_gate.py
# formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle03_to_04_synthesis_gate.py
# formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle04_to_05_synthesis_gate.py
# formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle05_to_06_synthesis_gate.py
# formal/python/tests/test_gr_qm_seam_promotion_cycle02_discharge_gate.py
# formal/python/tests/test_gr_qm_seam_promotion_cycle03_class_flip_gate.py
# formal/python/tests/test_proof_debt_marker_stability_gate.py
# formal/python/tests/test_proof_debt_burndown_cycle05_gate.py
# formal/python/tests/test_qm_m2_assumption_minimization_depth_exemplar_cycle02_gate.py
# formal/python/tests/test_gr_m2_assumption_minimization_depth_exemplar_cycle02_gate.py
# formal/python/tests/test_stat_m2_assumption_minimization_depth_exemplar_cycle02_gate.py
# formal/python/tests/test_qm_empirical_comparison_packet_04_gate.py
# formal/python/tests/test_gr_empirical_comparison_packet_04_gate.py
# formal/python/tests/test_gr_empirical_comparison_packet_05_gate.py
# formal/python/tests/test_gr_empirical_packet_05_artifact_schema_gate.py
# formal/python/tests/test_sr_empirical_comparison_packet_05_gate.py
# formal/python/tests/test_sr_empirical_packet_05_artifact_schema_gate.py
# formal/python/tests/test_empirical_packet05_decision_ledger_parity_gate.py
# formal/python/tests/test_empirical_packet05_falsification_surface_gate.py
# formal/python/tests/test_foundational_empirical_packet05_override_policy_gate.py
# formal/python/tests/test_stat_empirical_comparison_packet_04_gate.py
# formal/python/tests/test_cosmo_empirical_comparison_packet_04_gate.py
# formal/python/tests/test_em_empirical_comparison_packet_04_gate.py
# formal/python/tests/test_qft_empirical_comparison_packet_04_gate.py
# formal/python/tests/test_sr_empirical_comparison_packet_04_gate.py
# formal/python/tests/test_foundational_empirical_packet05_matrix_consistency_gate.py
# formal/python/tests/test_foundational_empirical_packet05_progression_policy_gate.py
# formal/python/tests/test_toe_master_action_shadow_numerics_cycle02_gate.py
# formal/python/tests/test_toe_master_action_shadow_numerics_cycle03_gate.py
# formal/python/tests/test_toe_master_action_shadow_numerics_cycle04_gate.py
# formal/python/tests/test_toe_master_action_shadow_numerics_cycle05_gate.py
# formal/python/tests/test_toe_master_action_shadow_numerics_cycle06_gate.py
# formal/python/tests/test_toe_master_action_shadow_numerics_cycle07_gate.py
# formal/python/tests/test_toe_master_action_shadow_numerics_cycle08_gate.py
# formal/python/tests/test_toe_master_action_shadow_numerics_cycle09_gate.py
# formal/python/tests/test_toe_master_action_shadow_numerics_cycle10_gate.py
# formal/python/tests/test_toe_master_action_shadow_numerics_cycle11_gate.py
# formal/python/tests/test_toe_master_action_shadow_numerics_cycle12_gate.py
# formal/python/tests/test_toe_master_action_shadow_numerics_cycle13_gate.py
# formal/python/tests/test_toe_master_action_shadow_numerics_cycle14_gate.py
# formal/python/tests/test_toe_master_action_shadow_numerics_cycle15_gate.py
# formal/python/tests/test_qm_empirical_packet_01_evidence_promotion_gate.py
# formal/python/tests/test_gr_empirical_comparison_packet_01_gate.py
# formal/python/tests/test_gr_empirical_packet_01_evidence_promotion_gate.py
# formal/python/tests/test_stat_empirical_comparison_packet_01_gate.py
# formal/python/tests/test_stat_empirical_packet_01_evidence_promotion_gate.py
# formal/python/tests/test_cosmo_empirical_comparison_packet_01_gate.py
# formal/python/tests/test_cosmo_empirical_packet_01_evidence_promotion_gate.py
# formal/python/tests/test_em_empirical_comparison_packet_01_gate.py
# formal/python/tests/test_em_empirical_packet_01_evidence_promotion_gate.py
# formal/python/tests/test_qft_empirical_comparison_packet_01_gate.py
# formal/python/tests/test_qft_empirical_packet_01_evidence_promotion_gate.py
# formal/python/tests/test_sr_empirical_comparison_packet_01_gate.py
# formal/python/tests/test_sr_empirical_packet_01_evidence_promotion_gate.py
# formal/python/tests/test_foundational_empirical_packet_matrix_consistency_gate.py
# formal/python/tests/test_foundational_empirical_packet02_matrix_consistency_gate.py
# formal/python/tests/test_foundational_empirical_packet02_decision_balance_gate.py
# formal/python/tests/test_foundational_empirical_packet03_matrix_consistency_gate.py
# formal/python/tests/test_foundational_empirical_packet03_decision_policy_gate.py
# formal/python/tests/test_foundational_empirical_packet04_matrix_consistency_gate.py
# formal/python/tests/test_foundational_empirical_packet04_decision_policy_gate.py
# formal/python/tests/test_foundational_empirical_packet_progression_policy_gate.py
# formal/python/tests/test_foundational_derivation_chain_matrix_consistency_gate.py
# formal/python/tests/test_pillar_deep_maturity_program_gate.py
# formal/python/tests/test_phase3_m3_consolidation_promotion_cycle01_gate.py
# formal/python/tests/test_qm_m3_completion_promotion_cycle01_gate.py
# formal/python/tests/test_gr_m3_completion_promotion_cycle01_gate.py
# formal/python/tests/test_stat_m3_completion_promotion_cycle01_gate.py
# formal/python/tests/test_cosmo_m3_completion_promotion_cycle01_gate.py
# formal/python/tests/test_em_m3_completion_promotion_cycle01_gate.py
# formal/python/tests/test_qft_m3_completion_promotion_cycle01_gate.py
# formal/python/tests/test_sr_m3_completion_promotion_cycle01_gate.py
# formal/python/tests/test_qm_m4_seam_closure_promotion_cycle01_gate.py
# formal/python/tests/test_gr_m4_seam_closure_promotion_cycle01_gate.py
# formal/python/tests/test_stat_m4_seam_closure_promotion_cycle01_gate.py
# formal/python/tests/test_cosmo_m4_seam_closure_promotion_cycle01_gate.py
# formal/python/tests/test_em_m4_seam_closure_promotion_cycle01_gate.py
# formal/python/tests/test_qft_m4_seam_closure_promotion_cycle01_gate.py
# formal/python/tests/test_sr_m4_seam_closure_promotion_cycle01_gate.py
# formal/python/tests/test_sr_m5_theory_parity_link_cycle56_gate.py
# formal/python/tests/test_sr_m5_phase5_cycle_advancement_contract_gate.py
# formal/python/tests/test_sr_m5_cycle_archive_discipline_gate.py
# formal/python/tests/test_pillar_deep_maturity_next_target_semantics_gate.py
# formal/python/tests/test_phase5_m5_completion_closeout_gate.py
# formal/python/tests/test_sr_m5_archive_retention_policy_gate.py
# formal/python/tests/test_sr_m5_periodic_quality_checkpoint_gate.py
# formal/python/tests/test_master_action_variant_cycle18_sensitivity_gate.py
# formal/python/tests/test_gr01_publication_grade_discharge_package_gate.py
# formal/python/tests/test_gr01_publication_theorem_claim_advancement_gate.py
# formal/python/tests/test_gr_continuum_discharge_criteria_cycle10_gate.py
# formal/python/tests/test_gr_w2_continuum_regularity_increment_gate.py
# formal/python/tests/test_w1_w2_science_increment_gate.py
# formal/python/tests/test_em_distributional_science_increment_gate.py
# formal/python/tests/test_em_distributional_weak_form_derivation_surface_gate.py
# formal/python/tests/test_gr01_function_space_discrete_regularity_evidence_gate.py
# formal/python/tests/test_gr01_function_space_continuum_regularity_route_gate.py
# formal/python/tests/test_gr01_function_space_nonclaim_boundary_evidence_gate.py
# formal/python/tests/test_gr01_function_space_completion_criteria_gate.py
# formal/python/tests/test_toe_qft_scalar_propagator_gate.py
# formal/python/tests/test_toe_qft_scalar_route_review_readiness_gate.py
# formal/python/tests/test_toe_qft_scalar_route_submission_candidate_gate.py
# formal/python/tests/test_toe_qft_scalar_route_submission_readiness_gate.py
# formal/python/tests/test_toe_qft_scalar_route_submission_package_gate.py
# formal/python/tests/test_toe_qft_scalar_route_submission_support_package_gate.py
# formal/python/tests/test_qft_gr_seam_reactivation_sliceb_increment15_authority_mirror_gate.py
# formal/python/tests/test_qft_gr_seam_reactivation_sliceb_science_first_enforcement_gate.py
# formal/python/tests/test_qft_gr_seam_reactivation_sliceb_derivation_completeness_enforcement_gate.py
# formal/python/tests/test_toe_qft_gr_seam_packet41_successor_discriminator_package_gate.py
# formal/python/tests/test_pillar_deep_maturity_m2_completion_gate.py
# formal/python/tests/test_qm_m2_analytic_completeness_scaffold_cycle01_gate.py
# formal/python/tests/test_qm_m2_canonical_equivalence_scaffold_cycle01_gate.py
# formal/python/tests/test_qm_m2_assumption_minimization_scaffold_cycle01_gate.py
# formal/python/tests/test_qm_m2_literature_alignment_scaffold_cycle01_gate.py
# formal/python/tests/test_qm_m2_completion_promotion_cycle01_gate.py
# formal/python/tests/test_gr_m2_analytic_completeness_scaffold_cycle01_gate.py
# formal/python/tests/test_gr_m2_canonical_equivalence_scaffold_cycle01_gate.py
# formal/python/tests/test_gr_m2_assumption_minimization_scaffold_cycle01_gate.py
# formal/python/tests/test_gr_m2_literature_alignment_scaffold_cycle01_gate.py
# formal/python/tests/test_gr_m2_completion_promotion_cycle01_gate.py
# formal/python/tests/test_stat_m2_analytic_completeness_scaffold_cycle01_gate.py
# formal/python/tests/test_stat_m2_canonical_equivalence_scaffold_cycle01_gate.py
# formal/python/tests/test_stat_m2_assumption_minimization_scaffold_cycle01_gate.py
# formal/python/tests/test_stat_m2_literature_alignment_scaffold_cycle01_gate.py
# formal/python/tests/test_stat_m2_completion_promotion_cycle01_gate.py
# formal/python/tests/test_cosmo_m2_analytic_completeness_scaffold_cycle01_gate.py
# formal/python/tests/test_cosmo_m2_canonical_equivalence_scaffold_cycle01_gate.py
# formal/python/tests/test_cosmo_m2_assumption_minimization_scaffold_cycle01_gate.py
# formal/python/tests/test_cosmo_m2_literature_alignment_scaffold_cycle01_gate.py
# formal/python/tests/test_cosmo_m2_completion_promotion_cycle01_gate.py
# formal/python/tests/test_em_m2_analytic_completeness_scaffold_cycle01_gate.py
# formal/python/tests/test_em_m2_canonical_equivalence_scaffold_cycle01_gate.py
# formal/python/tests/test_em_m2_assumption_minimization_scaffold_cycle01_gate.py
# formal/python/tests/test_em_m2_literature_alignment_scaffold_cycle01_gate.py
# formal/python/tests/test_em_m2_completion_promotion_cycle01_gate.py
# formal/python/tests/test_qft_m2_analytic_completeness_scaffold_cycle01_gate.py
# formal/python/tests/test_qft_m2_canonical_equivalence_scaffold_cycle01_gate.py
# formal/python/tests/test_qft_m2_assumption_minimization_scaffold_cycle01_gate.py
# formal/python/tests/test_qft_m2_literature_alignment_scaffold_cycle01_gate.py
# formal/python/tests/test_qft_m2_completion_promotion_cycle01_gate.py
# formal/python/tests/test_sr_m2_analytic_completeness_scaffold_cycle01_gate.py
# formal/python/tests/test_sr_m2_canonical_equivalence_scaffold_cycle01_gate.py
# formal/python/tests/test_sr_m2_assumption_minimization_scaffold_cycle01_gate.py
# formal/python/tests/test_sr_m2_literature_alignment_scaffold_cycle01_gate.py
# formal/python/tests/test_sr_m2_completion_promotion_cycle01_gate.py
# formal/python/tests/test_qm_empirical_discriminator_emp_qm_01_scaffold_gate.py
# formal/python/tests/test_gr_empirical_discriminator_emp_gr_01_scaffold_gate.py
# formal/python/tests/test_stat_empirical_discriminator_emp_stat_01_scaffold_gate.py
# formal/python/tests/test_cosmo_empirical_discriminator_emp_cosmo_01_scaffold_gate.py
# formal/python/tests/test_em_empirical_discriminator_emp_em_01_scaffold_gate.py
# formal/python/tests/test_qft_empirical_discriminator_emp_qft_01_scaffold_gate.py
# formal/python/tests/test_sr_empirical_discriminator_emp_sr_01_scaffold_gate.py
# formal/python/tests/test_pillar_full_completion_action_plan_gate.py
# formal/python/tests/test_phase4_global_unification_and_residual_debt_gate.py
# formal/python/tests/test_locked_queue_phase_adherence_standard_gate.py
# formal/python/tests/test_cosmo_background_kickoff_gate.py
# formal/python/tests/test_cosmo_bg_micro01_object_surface_gate.py
# formal/python/tests/test_cosmo_bg_micro02_expansion_law_surface_gate.py
# formal/python/tests/test_cosmo_bg_micro03_source_coupling_surface_gate.py
# formal/python/tests/test_cosmo_bg_micro04_regime_falsifiability_surface_gate.py
# formal/python/tests/test_cosmo_bg_micro05_package_freeze_reopen_policy_gate.py
# formal/python/tests/test_cosmo_bg_micro06_state_checkpoint_boundary_gate.py
# formal/python/tests/test_cosmo_bg_micro07_matrix_lane_drift_alarm_gate.py
# formal/python/tests/test_cosmo_bg_micro08_locked_queue_unlock_transition_packet_gate.py
# formal/python/tests/test_cosmo_bg_micro09_authorized_unlock_conditions_checklist_packet_gate.py
# formal/python/tests/test_cosmo_bg_micro10_lock_transition_dryrun_attestation_packet_gate.py
# formal/python/tests/test_cosmo_bg_micro11_dryrun_reconciliation_packet_gate.py
# formal/python/tests/test_cosmo_bg_micro12_dryrun_closure_packet_gate.py
# formal/python/tests/test_cosmo_bg_micro13_dryrun_custody_packet_gate.py
# formal/python/tests/test_cosmo_bg_micro14_dryrun_custody_confirmation_packet_gate.py
# formal/python/tests/test_cosmo_bg_micro15_dryrun_custody_confirmation_attestation_packet_gate.py
# formal/python/tests/test_cosmo_bg_micro16_dryrun_custody_confirmation_attestation_confirmation_packet_gate.py
# formal/python/tests/test_cosmo_bg_micro17_dryrun_custody_confirmation_attestation_confirmation_attestation_packet_gate.py
# formal/python/tests/test_cosmo_bg_micro18_dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_packet_gate.py
# formal/python/tests/test_cosmo_bg_micro19_dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_packet_gate.py
# formal/python/tests/test_cosmo_bg_micro20_dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_gate.py
# formal/python/tests/test_cosmo_phase_adherence_snapshot_gate.py
# formal/python/tests/test_cosmo_background_pillar_package_rollup_gate.py
# formal/python/tests/test_cosmo_state_rollup_checkpoint_gate.py
# formal/python/tests/test_cosmo_rollup_pointer_completeness_gate.py
# formal/python/tests/test_cosmo_matrix_rollup_crosspin_gate.py
# formal/python/tests/test_cosmo_external_implications_reference_surface_policy_gate.py
# formal/python/tests/test_cosmo_external_implications_cross_surface_parity_gate.py
# formal/python/tests/test_cosmo_derivation_completeness_gate_readiness_packet_cycle01_gate.py
# formal/python/tests/test_cosmo_der01_theorem_surface_scaffold_cycle01_gate.py
# formal/python/tests/test_cosmo_der02_governance_coupling_scaffold_cycle01_gate.py
# formal/python/tests/test_cosmo_der01_closure_package_cycle01_gate.py
# formal/python/tests/test_cosmo_der02_closure_package_cycle01_gate.py
# formal/python/tests/test_stat_der01_theorem_surface_scaffold_coupling_cycle01_gate.py
# formal/python/tests/test_stat_der01_theorem_body_scope_boundary_cycle01_gate.py
# formal/python/tests/test_stat_der01_theorem_body_scaffold_coupling_cycle01_gate.py
# formal/python/tests/test_stat_der01_discharge_scaffold_coupling_cycle01_gate.py
# formal/python/tests/test_stat_der01_object_surface_scaffold_coupling_cycle01_gate.py
# formal/python/tests/test_stat_der02_regime_closure_coupling_scaffold_coupling_cycle01_gate.py
# formal/python/tests/test_stat_der02_theorem_body_scope_boundary_cycle01_gate.py
# formal/python/tests/test_stat_der02_theorem_body_scaffold_coupling_cycle01_gate.py
# formal/python/tests/test_stat_der02_discharge_scaffold_coupling_cycle01_gate.py
# formal/python/tests/test_stat_der02_object_surface_scaffold_coupling_cycle01_gate.py
# formal/python/tests/test_orchestration_report_contract_gate.py
# formal/python/tests/test_conftest_signature_stability_gate.py
# formal/python/tests/test_repository_retention_policy_contract_gate.py
# formal/python/tests/test_local_execution_posture_gate.py
# formal/python/tests/test_dev_stack_preflight.py
# formal/python/tests/test_ci_tranche3_gates.py
# formal/python/tests/test_convergence_baseline_pack_gate.py
# formal/python/tests/test_convergence_promotion_significance_gate.py
# formal/python/tests/test_convergence_promotion_authorization_block_gate.py
# formal/python/tests/test_redundancy_control_registry_family_index_gate.py
# formal/python/tests/test_redundancy_control_seam_family_index_gate.py
# formal/python/tests/test_redundancy_control_admission_semantics_gate.py
# formal/python/tests/test_redundancy_control_registry_full_family_index_gate.py
# formal/python/tests/test_redundancy_control_seam_full_family_index_gate.py
# formal/python/tests/test_redundancy_control_dedup_wave_progress_gate.py
# formal/python/tests/test_redundancy_control_seam_qm_stat_owner_dedup_wave4_gate.py
# formal/python/tests/test_redundancy_control_seam_history_archive_dedup_wave5_gate.py
# formal/python/tests/test_redundancy_control_packet_history_archive_dedup_wave6_gate.py
# formal/python/tests/test_redundancy_control_changelog_archive_dedup_wave7_gate.py
# formal/python/tests/test_redundancy_control_repo_disposition_checklist_dedup_wave8_gate.py
# formal/python/tests/test_redundancy_control_ws10_audit_exec_program_dedup_wave9_gate.py
# formal/python/tests/test_redundancy_control_repo_comprehensive_audit_dedup_wave10_gate.py
# formal/python/tests/test_governance_audit_packet_gate.py
# formal/python/tests/test_physics_progress_ledger_tgc93_consistency_gate.py
# formal/python/tests/test_dual_track_cutover_measured_mode_policy_gate.py
# formal/python/tests/test_governance_invalidation_select_telemetry_gate.py
# formal/python/tests/test_dual_track_hardening_closeout_gate.py
# formal/python/tests/test_governance_parallel_capability_probe_gate.py
# formal/python/tests/test_sql_integrity_snapshot_tool.py
# END GOVERNANCE MANIFEST TEST REFERENCES
Write-Host "Resolving governance pytest manifest selection" -ForegroundColor Cyan
function Resolve-GovernanceManifestGroup {
  param(
    [Parameter(Mandatory = $true)][string]$Group,
    [switch]$EnforceExpected
  )

  $cmd = @(
    "-m",
    "formal.python.tools.governance_manifest_select",
    "--manifest",
    $governanceManifestPath,
    "--group",
    $Group
  )
  if ($EnforceExpected) {
    $cmd += "--enforce-expected"
  }

  $selection = @(./py.ps1 @cmd)
  if ($LASTEXITCODE -ne 0) {
    throw "Governance manifest selection failed for group '$Group'."
  }
  if ($selection.Count -eq 0) {
    throw "Governance manifest selection produced zero tests for group '$Group'."
  }
  return $selection
}

function Invoke-GovernancePytestLane {
  param(
    [Parameter(Mandatory = $true)][string]$LaneName,
    [Parameter(Mandatory = $true)][array]$Tests,
    [switch]$Parallelizable
  )

  Write-Host ("Running governance pytest lane {0} (count={1})" -f $LaneName, $Tests.Count) -ForegroundColor Cyan
  $cmd = @("-m", "pytest")
  if ($Parallelizable -and $EnableReadOnlyParallel) {
    $cmd += "-n"
    $cmd += $ReadOnlyParallelWorkers
    Write-Host ("Parallel mode enabled for lane {0}: workers={1}" -f $LaneName, $ReadOnlyParallelWorkers) -ForegroundColor Yellow
  }
  $cmd += $Tests
  $cmd += "-q"

  ./py.ps1 @cmd
  if ($LASTEXITCODE -ne 0) {
    throw ("Governance pytest lane failed: {0}" -f $LaneName)
  }
}

function Test-ReadOnlyParallelCapability {
  $helpText = ./py.ps1 -m pytest --help
  if ($LASTEXITCODE -ne 0 -or $null -eq $helpText) {
    return $false
  }

  $joined = [string]::Join("`n", @($helpText))
  if (-not ($joined -match '(?m)^\s*-n\b')) {
    return $false
  }

  # Guarded probe: ensure -n is not only advertised, but executable in current environment.
  ./py.ps1 -m pytest -n 1 --collect-only formal/python/tests/test_state_theory_dag.py -q *> $null
  return ($LASTEXITCODE -eq 0)
}

function Write-ParallelCapabilityReport {
  param(
    [Parameter(Mandatory = $true)][bool]$ParallelRequested,
    [Parameter(Mandatory = $true)][bool]$CapabilityAvailable,
    [Parameter(Mandatory = $true)][bool]$ParallelActivated,
    [Parameter(Mandatory = $true)][string]$Workers,
    [string]$ReportPath = 'formal/output/reports/governance_parallel_capability_v0.json'
  )

  $payload = @{
    schema_id = 'GOVERNANCE_PARALLEL_CAPABILITY_v0'
    status = 'ACTIVE_NONLIVE_NONCLAIM'
    captured_at_utc = (Get-Date).ToUniversalTime().ToString('yyyy-MM-ddTHH:mm:ssZ')
    parallel_requested = $ParallelRequested
    capability_available = $CapabilityAvailable
    parallel_activated = $ParallelActivated
    workers = $Workers
    rule = 'ENABLE_PARALLEL_ONLY_WHEN_CAPABILITY_PROBE_PASSES_ELSE_FALLBACK_TO_SERIAL'
    non_claim_boundary = 'This report is a repository-local execution capability artifact and does not assert scientific adequacy.'
  }

  if ([string]::IsNullOrWhiteSpace($ReportPath)) {
    $ReportPath = 'formal/output/reports/governance_parallel_capability_v0.json'
  }

  $reportBase = if (-not [string]::IsNullOrWhiteSpace($PSScriptRoot)) { $PSScriptRoot } else { (Get-Location).Path }
  $reportTarget = if ([System.IO.Path]::IsPathRooted($ReportPath)) { $ReportPath } else { Join-Path $reportBase $ReportPath }
  $dir = Split-Path -Parent $reportTarget
  if (-not (Test-Path $dir)) {
    New-Item -ItemType Directory -Path $dir -Force | Out-Null
  }
  $payload | ConvertTo-Json -Depth 8 | Set-Content -Path $reportTarget -Encoding utf8
}

function Resolve-InvalidationSubsetSelection {
  $cmd = @(
    "-m",
    "formal.python.tools.governance_invalidation_select",
    "--base-ref",
    $InvalidationBaseRef
  )

  if ($IncludeInvalidationWorkingTree) {
    $cmd += "--include-working-tree"
  }

  $raw = ./py.ps1 @cmd
  if ($LASTEXITCODE -ne 0) {
    throw "Governance invalidation selector failed."
  }

  if ($null -eq $raw) {
    throw "Governance invalidation selector returned empty output."
  }

  $jsonText = [string]::Join("`n", @($raw))
  return $jsonText | ConvertFrom-Json
}

$governanceTests = @(Resolve-GovernanceManifestGroup -Group $governanceManifestGroup -EnforceExpected)
$criticalTests = @(Resolve-GovernanceManifestGroup -Group "critical_gates")
$integrityTests = @(Resolve-GovernanceManifestGroup -Group "integrity_gates")

$parallelLaneCEnabled = $false
$parallelCapabilityAvailable = $false
if ($EnableReadOnlyParallel) {
  if (Test-ReadOnlyParallelCapability) {
    $parallelCapabilityAvailable = $true
    $parallelLaneCEnabled = $true
  } else {
    Write-Host "WARN: read-only parallel requested but pytest parallel option '-n' is unavailable; falling back to serial lane C." -ForegroundColor Yellow
  }
}

Write-ParallelCapabilityReport `
  -ParallelRequested ([bool]$EnableReadOnlyParallel) `
  -CapabilityAvailable $parallelCapabilityAvailable `
  -ParallelActivated $parallelLaneCEnabled `
  -Workers $ReadOnlyParallelWorkers `
  -ReportPath $ParallelCapabilityReportPath

$laneCovered = New-Object 'System.Collections.Generic.HashSet[string]' ([System.StringComparer]::Ordinal)
foreach ($testPath in $criticalTests + $integrityTests) {
  [void]$laneCovered.Add([string]$testPath)
}

$standardTests = @()
foreach ($testPath in $governanceTests) {
  if (-not $laneCovered.Contains([string]$testPath)) {
    $standardTests += $testPath
  }
}

if ($UseInvalidationSelection) {
  $selection = Resolve-InvalidationSubsetSelection
  $selectionMode = [string]$selection.mode
  $selectionReasons = @($selection.reasons)
  if ($selectionReasons.Count -gt 0) {
    Write-Host ("Governance invalidation selection reasons: {0}" -f (($selectionReasons | ForEach-Object { [string]$_ }) -join ", ")) -ForegroundColor Yellow
  }

  if ($selectionMode -eq "SUBSET") {
    $subset = New-Object 'System.Collections.Generic.HashSet[string]' ([System.StringComparer]::Ordinal)
    foreach ($path in @($selection.subset_tests)) {
      [void]$subset.Add([string]$path)
    }

    $selectedStandard = @()
    foreach ($testPath in $standardTests) {
      if ($subset.Contains([string]$testPath)) {
        $selectedStandard += $testPath
      }
    }
    $standardTests = $selectedStandard
    Write-Host ("Governance invalidation subset active: selected_standard_count={0}" -f $standardTests.Count) -ForegroundColor Yellow
  } else {
    Write-Host "Governance invalidation selection fell back to FULL mode." -ForegroundColor Yellow
  }
}

Invoke-GovernancePytestLane -LaneName "A:critical" -Tests $criticalTests
Invoke-GovernancePytestLane -LaneName "B:integrity" -Tests $integrityTests
if ($standardTests.Count -gt 0) {
  if ($parallelLaneCEnabled) {
    Invoke-GovernancePytestLane -LaneName "C:standard" -Tests $standardTests -Parallelizable
  } else {
    Invoke-GovernancePytestLane -LaneName "C:standard" -Tests $standardTests
  }
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

# Governance gate for TGC-77
Invoke-GovernanceGate -TargetRow "ROW-PILLAR-QM-001" -BlockerClass "THEOREM_GAP" -Declaration "formal/docs/release/TGC_77_DECLARATION.md"

# Governance gate for TGC-78
Invoke-GovernanceGate -TargetRow "ROW-PILLAR-COSMO-001" -BlockerClass "THEOREM_GAP" -Declaration "formal/docs/release/TGC_78_DECLARATION.md"

# Governance gate for TGC-83
Invoke-GovernanceGate -TargetRow "ROW-PILLAR-QFT-001" -BlockerClass "THEOREM_GAP" -Declaration "formal/docs/release/TGC_83_DECLARATION.md"

# Governance gate for TGC-85
Invoke-GovernanceGate -TargetRow "ROW-PILLAR-SR-001" -BlockerClass "THEOREM_GAP" -Declaration "formal/docs/release/TGC_85_DECLARATION.md"


Write-Host "Enforcing TGC-93 branch decision routing" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.tgc93_branch_decision_router
if ($LASTEXITCODE -ne 0) {
  throw "TGC-93 branch decision routing enforcement failed."
}

Write-Host "Enforcing tranche progress semantics policy" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.tranche_progress_semantics_check
if ($LASTEXITCODE -ne 0) {
  throw "Tranche progress semantics enforcement failed."
}

Write-Host "Generating physics progress ledger" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.physics_progress_ledger_generate
if ($LASTEXITCODE -ne 0) {
  throw "Physics progress ledger generation failed."
}

Write-Host "Generating discovery priority queue report (shadow mode)" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.discovery_priority_queue_report
if ($LASTEXITCODE -ne 0) {
  Write-Host "WARN: discovery priority queue shadow generation failed; continuing because discovery lane is non-authoritative in shadow mode." -ForegroundColor Yellow
}

Write-Host "Generating QM-STAT discovery discriminator tranche report (shadow mode)" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.qm_stat_discovery_discriminator_tranche_report
if ($LASTEXITCODE -ne 0) {
  Write-Host "WARN: QM-STAT discovery discriminator tranche shadow generation failed; continuing because discovery lane is non-authoritative in shadow mode." -ForegroundColor Yellow
}

Write-Host "Generating QM-STAT discovery ruling report (shadow mode)" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.qm_stat_discovery_ruling_report
if ($LASTEXITCODE -ne 0) {
  Write-Host "WARN: QM-STAT discovery ruling shadow generation failed; continuing because discovery lane is non-authoritative in shadow mode." -ForegroundColor Yellow
}

Write-Host "Generating QM-STAT discovery interpretation report (shadow mode)" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.qm_stat_discovery_interpretation_report
if ($LASTEXITCODE -ne 0) {
  Write-Host "WARN: QM-STAT discovery interpretation shadow generation failed; continuing because discovery lane is non-authoritative in shadow mode." -ForegroundColor Yellow
}

Write-Host "Generating QM-STAT discovery numerical probe report (shadow mode)" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.qm_stat_discovery_numerical_probe_report
if ($LASTEXITCODE -ne 0) {
  Write-Host "WARN: QM-STAT discovery numerical probe shadow generation failed; continuing because discovery lane is non-authoritative in shadow mode." -ForegroundColor Yellow
}

Write-Host "Generating QM-STAT discovery numerical probe execution report (shadow mode)" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.qm_stat_discovery_numerical_probe_execution_report
if ($LASTEXITCODE -ne 0) {
  Write-Host "WARN: QM-STAT discovery numerical probe execution shadow generation failed; continuing because discovery lane is non-authoritative in shadow mode." -ForegroundColor Yellow
}

Write-Host "Generating QM-STAT derivation/probe paired ruling report (shadow mode)" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.qm_stat_discovery_derivation_probe_ruling_report
if ($LASTEXITCODE -ne 0) {
  Write-Host "WARN: QM-STAT derivation/probe paired ruling shadow generation failed; continuing because discovery lane is non-authoritative in shadow mode." -ForegroundColor Yellow
}

Write-Host "Generating QM-STAT post-derivation/probe decision report (shadow mode)" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.qm_stat_discovery_post_derivation_probe_decision_report
if ($LASTEXITCODE -ne 0) {
  Write-Host "WARN: QM-STAT post-derivation/probe decision shadow generation failed; continuing because discovery lane is non-authoritative in shadow mode." -ForegroundColor Yellow
}

Write-Host "Generating QM-STAT next-route decision report (shadow mode)" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.qm_stat_discovery_next_route_decision_report
if ($LASTEXITCODE -ne 0) {
  Write-Host "WARN: QM-STAT next-route decision shadow generation failed; continuing because discovery lane is non-authoritative in shadow mode." -ForegroundColor Yellow
}

Write-Host "Generating QFT-GR discovery discriminator tranche report (shadow mode)" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.qft_gr_discovery_discriminator_tranche_report
if ($LASTEXITCODE -ne 0) {
  Write-Host "WARN: QFT-GR discovery discriminator tranche shadow generation failed; continuing because discovery lane is non-authoritative in shadow mode." -ForegroundColor Yellow
}

Write-Host "Generating QFT-GR discovery ruling report (shadow mode)" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.qft_gr_discovery_ruling_report
if ($LASTEXITCODE -ne 0) {
  Write-Host "WARN: QFT-GR discovery ruling shadow generation failed; continuing because discovery lane is non-authoritative in shadow mode." -ForegroundColor Yellow
}

Write-Host "Generating QFT-GR discovery interpretation report (shadow mode)" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.qft_gr_discovery_interpretation_report
if ($LASTEXITCODE -ne 0) {
  Write-Host "WARN: QFT-GR discovery interpretation shadow generation failed; continuing because discovery lane is non-authoritative in shadow mode." -ForegroundColor Yellow
}

Write-Host "Generating QFT-GR post-cycle decision report (shadow mode)" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.qft_gr_discovery_post_cycle_decision_report
if ($LASTEXITCODE -ne 0) {
  Write-Host "WARN: QFT-GR post-cycle decision shadow generation failed; continuing because discovery lane is non-authoritative in shadow mode." -ForegroundColor Yellow
}

Write-Host "Generating discovery queue transition decision report (shadow mode)" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.discovery_queue_transition_decision_report
if ($LASTEXITCODE -ne 0) {
  Write-Host "WARN: discovery queue transition decision shadow generation failed; continuing because discovery lane is non-authoritative in shadow mode." -ForegroundColor Yellow
}

Write-Host "Generating discovery queue review pass report (shadow mode)" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.discovery_queue_review_pass_report
if ($LASTEXITCODE -ne 0) {
  Write-Host "WARN: discovery queue review pass shadow generation failed; continuing because discovery lane is non-authoritative in shadow mode." -ForegroundColor Yellow
}

Write-Host "Generating discovery queue rescoring pass report (shadow mode)" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.discovery_queue_rescoring_pass_report
if ($LASTEXITCODE -ne 0) {
  Write-Host "WARN: discovery queue rescoring pass shadow generation failed; continuing because discovery lane is non-authoritative in shadow mode." -ForegroundColor Yellow
}

Write-Host "Generating GR discovery discriminator tranche report (shadow mode)" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.gr_discovery_discriminator_tranche_report
if ($LASTEXITCODE -ne 0) {
  Write-Host "WARN: GR discovery discriminator tranche shadow generation failed; continuing because discovery lane is non-authoritative in shadow mode." -ForegroundColor Yellow
}

Write-Host "Generating GR discovery ruling report (shadow mode)" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.gr_discovery_ruling_report
if ($LASTEXITCODE -ne 0) {
  Write-Host "WARN: GR discovery ruling shadow generation failed; continuing because discovery lane is non-authoritative in shadow mode." -ForegroundColor Yellow
}

Write-Host "Generating runtime measurement integrity report" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.runtime_measurement_integrity_report
if ($LASTEXITCODE -ne 0) {
  throw "Runtime measurement integrity report generation failed."
}

Write-Host "Generating Packet41 successor decision enforcement report" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.packet41_successor_decision_enforcement
if ($LASTEXITCODE -ne 0) {
  throw "Packet41 successor decision enforcement report generation failed."
}

Write-Host "Generating governance single-source consolidation report" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.governance_single_source_consolidation_report
if ($LASTEXITCODE -ne 0) {
  throw "Governance single-source consolidation report generation failed."
}

Write-Host "Generating governance scale observability report" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.governance_scale_observability_report
if ($LASTEXITCODE -ne 0) {
  throw "Governance scale observability report generation failed."
}

Write-Host "Generating governance cross-platform parity report" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.governance_cross_platform_parity_report
if ($LASTEXITCODE -ne 0) {
  throw "Governance cross-platform parity report generation failed."
}

Write-Host "Generating enforced execution closeout report" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.toe_enforced_execution_closeout
if ($LASTEXITCODE -ne 0) {
  throw "Enforced execution closeout report generation failed."
}

Write-Host "Generating science/global completion baseline report" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.science_global_completion_baseline_report
if ($LASTEXITCODE -ne 0) {
  throw "Science/global completion baseline report generation failed."
}

Write-Host "Generating theorem-gap reduction wave report" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.theorem_gap_reduction_wave_report
if ($LASTEXITCODE -ne 0) {
  throw "Theorem-gap reduction wave report generation failed."
}

Write-Host "Generating theorem-gap execution linkage report" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.theorem_gap_execution_linkage_report
if ($LASTEXITCODE -ne 0) {
  throw "Theorem-gap execution linkage report generation failed."
}

Write-Host "Generating theorem-gap row outcome trend report" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.theorem_gap_row_outcome_trend_report
if ($LASTEXITCODE -ne 0) {
  throw "Theorem-gap row outcome trend report generation failed."
}

Write-Host "Generating theorem-gap single-row execution report" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.theorem_gap_single_row_execution_report
if ($LASTEXITCODE -ne 0) {
  throw "Theorem-gap single-row execution report generation failed."
}

Write-Host "Generating theorem-gap QM rework tranche report" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.theorem_gap_qm_rework_tranche_report
if ($LASTEXITCODE -ne 0) {
  throw "Theorem-gap QM rework tranche report generation failed."
}

Write-Host "Generating theorem-gap QM sub-target tranche report" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.theorem_gap_qm_subtarget_tranche_report
if ($LASTEXITCODE -ne 0) {
  throw "Theorem-gap QM sub-target tranche report generation failed."
}
Write-Host "Generating R0-R6 objective quality closeout report" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.r0_r6_objective_quality_closeout_report
if ($LASTEXITCODE -ne 0) { throw "R0-R6 objective quality closeout report generation failed." }


Write-Host "Writing governance green cache stamp" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.governance_cache_key --status GREEN
if ($LASTEXITCODE -ne 0) {
  throw "Failed to write governance green cache stamp."
}






