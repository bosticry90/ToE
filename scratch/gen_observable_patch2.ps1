$files = @(
  'formal/python/toe/observables/bmdig01_minimal_numeric_benchmark_digitization_record.py',
  'formal/python/toe/observables/ov04x_fit_family_robustness_record.py',
  'formal/python/toe/observables/ov03x_fit_family_robustness_record.py',
  'formal/python/toe/observables/ovbm01_mean_field_line_shift_scaling_benchmark.py',
  'formal/python/toe/observables/ovbm01_mean_field_line_shift_scaling_digitized.py',
  'formal/python/toe/observables/ovbm02_linewidth_quadrature_composition_benchmark.py',
  'formal/python/toe/observables/ovbm02_linewidth_quadrature_composition_digitized.py',
  'formal/python/toe/observables/ovbr01_regime_bridge_record.py',
  'formal/python/toe/observables/ovbr02_regime_bridge_record.py',
  'formal/python/toe/observables/ovbr03n_bragg_dispersion_k_omega_digitized.py',
  'formal/python/toe/observables/ovbr04a_bragg_lowk_slope_conditionA_record.py',
  'formal/python/toe/observables/ovbr04b_bragg_lowk_slope_conditionB_record.py'
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

$patch = New-Object System.Text.StringBuilder
[void]$patch.AppendLine('*** Begin Patch')

foreach ($file in $files) {
  $old = Get-Content -Raw -Path $file
  $new = $old

  if ($new -notmatch 'from formal\.python\.meta\.repo_environment import find_repo_root') {
    $new = $new.Replace("from pathlib import Path`r`n", "from pathlib import Path`r`nfrom formal.python.meta.repo_environment import find_repo_root`r`n")
  }

  $new = $new.Replace($oldHelper, '')
  $new = $new.Replace('_find_repo_root(', 'find_repo_root(')

  if ($new -eq $old) {
    continue
  }

  [void]$patch.AppendLine("*** Update File: c:\Users\psboy\Documents\ToE\$($file -replace '/', '\\')")
  [void]$patch.AppendLine('@@')

  foreach ($line in ($old -split "`r?`n")) {
    [void]$patch.AppendLine('-' + $line)
  }

  foreach ($line in ($new -split "`r?`n")) {
    [void]$patch.AppendLine('+' + $line)
  }
}

[void]$patch.AppendLine('*** End Patch')
[System.IO.File]::WriteAllText('scratch/observable_tranche_patch.txt', $patch.ToString(), [System.Text.UTF8Encoding]::new($false))
Write-Output 'PATCH_READY'
