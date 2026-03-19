$files = @(
  'formal/python/toe/observables/snddig01_minimal_density_digitization_record.py',
  'formal/python/toe/observables/ovcvbr01_cv01_v1_pruning_bridge_record.py',
  'formal/python/toe/observables/ovdq02_dq01_v2_threshold_update_record.py',
  'formal/python/toe/observables/ovucff06_temporal_spectral_entropy_trends_audit.py',
  'formal/python/toe/observables/ovsel_snd03_sound_speed_derived_audit_record.py',
  'formal/python/toe/observables/ovbr05_bragg_lowk_slope_summary_record.py',
  'formal/python/toe/observables/ovbrfn01_fn01_metric_residual_pruning_table_record.py',
  'formal/python/toe/observables/ovsel_snd02_sound_anchor_interaction_stress_test_record.py',
  'formal/python/toe/observables/ovucff05_temporal_band_modulation_audit.py',
  'formal/python/toe/observables/ovbrfn00_fn01_metric_residual_prediction_declarations_record.py',
  'formal/python/toe/observables/ovsel_snd01_sound_anchor_ingestion_audit_record.py',
  'formal/python/toe/observables/ovsel_snd05_multi_density_constancy_audit_record.py',
  'formal/python/toe/observables/ovpt01_phase_transition_window_audit.py',
  'formal/python/toe/observables/ovsel_br01_bragg_lowk_slope_audit_record.py',
  'formal/python/toe/observables/ovsel_snd04_density_dependence_audit_record.py',
  'formal/python/toe/observables/ovfg01_graph_fourier_mode_audit.py',
  'formal/python/toe/observables/ovucff04_spectral_evolution_audit.py',
  'formal/python/toe/observables/ovsw01_shallow_water_lowk_slope_record.py',
  'formal/python/toe/observables/ovobs01_observability_metadata_invariance.py',
  'formal/python/toe/observables/ovmb01_orthogonality_catastrophe_audit.py',
  'formal/python/toe/observables/ovselct10_independent_anchor_selection_verdict_record.py',
  'formal/python/toe/observables/ovucff02_framewise_variation_audit.py',
  'formal/python/toe/observables/ovucff01_jitter_structure_audit.py',
  'formal/python/toe/observables/ovucff03b_band_energy_tolerance_audit.py',
  'formal/python/toe/observables/ovqc01_berry_curvature_audit.py',
  'formal/python/toe/observables/ovucff03_band_energy_distribution_audit.py'
)

$oldHelper = @'
def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")

'@

$updated = @()
foreach ($f in $files) {
  if (-not (Test-Path $f)) { continue }
  $old = Get-Content -Raw -Path $f
  $new = $old

  if ($new -notmatch 'from formal\.python\.meta\.repo_environment import find_repo_root') {
    $new = $new.Replace("from pathlib import Path`r`n", "from pathlib import Path`r`nfrom formal.python.meta.repo_environment import find_repo_root`r`n")
  }

  $new = $new.Replace($oldHelper, '')
  $new = $new.Replace('_find_repo_root(', 'find_repo_root(')

  if ($new -ne $old) {
    [System.IO.File]::WriteAllText($f, $new, [System.Text.UTF8Encoding]::new($false))
    $updated += $f
  }
}
Write-Output ("UPDATED_FILES=" + $updated.Count)
$updated
