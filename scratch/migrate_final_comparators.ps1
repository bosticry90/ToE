$files = @(
  'formal/python/toe/comparators/ct06_external_anchor_dispersion_v0.py',
  'formal/python/toe/comparators/cv03_ucff_dispersion_v1.py',
  'formal/python/toe/comparators/ct05_rep_invariant_admissibility_class_v0.py',
  'formal/python/toe/comparators/cv02_bec_bragg_b1_v0.py',
  'formal/python/toe/comparators/ct02_energy_causality_update_bounds_v0.py',
  'formal/python/toe/comparators/ct03_energy_causality_rep_variant_v0.py',
  'formal/python/toe/comparators/ct04_minimality_no_go_v0.py',
  'formal/python/toe/comparators/cv01_bec_bragg_v1.py',
  'formal/python/toe/comparators/ct08_external_anchor_dispersion_highk_slice_v0.py',
  'formal/python/toe/comparators/ct09_independent_external_anchor_sound_speed_v0.py',
  'formal/python/toe/comparators/ct07_external_anchor_dispersion_lowk_slice_v0.py',
  'formal/python/toe/comparators/cv01_bec_bragg_v0.py'
)
$updated = @()
$defPattern = '(?ms)^def _find_repo_root\(start: Path\) -> Path:\r?\n(?:    .*\r?\n)+?    raise RuntimeError\("Could not locate repo root \(expected a ''formal'' directory\)."\)\r?\n\r?\n'
foreach ($f in $files) {
  if (-not (Test-Path $f)) { continue }
  $content = Get-Content -Raw -Path $f
  $orig = $content
  if ($content -notmatch 'from formal\.python\.meta\.repo_environment import find_repo_root') {
    $content = [regex]::Replace($content, 'from pathlib import Path\r?\n', "from pathlib import Path`r`nfrom formal.python.meta.repo_environment import find_repo_root`r`n", 1)
  }
  $content = [regex]::Replace($content, $defPattern, '')
  $content = [regex]::Replace($content, '\b_find_repo_root\(', 'find_repo_root(')
  if ($content -ne $orig) {
    [System.IO.File]::WriteAllText($f, $content, [System.Text.UTF8Encoding]::new($false))
    $updated += $f
  }
}
"UPDATED_FILES=$($updated.Count)"
$updated
