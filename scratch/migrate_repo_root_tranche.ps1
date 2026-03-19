$targets = @()
$targets += Get-ChildItem 'formal/python/toe/comparators' -Filter '*.py' -File
$targets += Get-ChildItem 'formal/python/tests' -Filter '*.py' -File
$updated = @()
$defPattern = '(?ms)^def _find_repo_root\(start: Path\) -> Path:\r?\n(?:^[ \t].*\r?\n)+\r?\n'
foreach ($f in $targets) {
  $content = Get-Content -Raw -Path $f.FullName
  if ($content -notmatch 'def _find_repo_root\(') { continue }
  $orig = $content

  if ($content -notmatch 'from formal\.python\.meta\.repo_environment import find_repo_root') {
    $importRx = [regex]::new('from pathlib import Path\r?\n')
    $content = $importRx.Replace($content, "from pathlib import Path`r`nfrom formal.python.meta.repo_environment import find_repo_root`r`n", 1)
  }

  $content = [regex]::Replace($content, $defPattern, '')
  $content = [regex]::Replace($content, '\b_find_repo_root\(', 'find_repo_root(')

  if ($content -ne $orig) {
    [System.IO.File]::WriteAllText($f.FullName, $content, [System.Text.UTF8Encoding]::new($false))
    $updated += $f.FullName
  }
}
"UPDATED_FILES=$($updated.Count)"
$updated
