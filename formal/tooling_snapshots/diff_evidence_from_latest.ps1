Param(
  [string]$Profile = "clean",
  [switch]$IgnoreQuarantine,
  [int]$MaxList = 200,
  [switch]$Fast
)

$ErrorActionPreference = "Stop"

$repoRoot = Resolve-Path (Join-Path $PSScriptRoot "..\..")
$py = Join-Path $repoRoot ".venv\Scripts\python.exe"
if (!(Test-Path $py)) { throw "Python venv not found: $py" }

# Hard-fail if we accidentally invoke anything except the repo venv python.
$pyResolved = (Resolve-Path $py).Path
$pyExpectedResolved = (Resolve-Path (Join-Path $repoRoot ".venv\Scripts\python.exe")).Path
if ($pyResolved -ne $pyExpectedResolved) {
  throw "Refusing to run: python is not repo venv ($pyResolved). Use .\py.ps1 or ensure .venv exists."
}

$ptr = Join-Path $repoRoot "formal\tooling_snapshots\LATEST_BASELINE_EVIDENCE.txt"
if (!(Test-Path $ptr)) { throw "Missing pointer file: $ptr" }

$baselineRel = (Get-Content $ptr -Raw).Trim()
if ([string]::IsNullOrWhiteSpace($baselineRel)) { throw "Empty baseline pointer: $ptr" }

$baseline = Join-Path $repoRoot $baselineRel
if (!(Test-Path $baseline)) { throw "Baseline snapshot not found: $baseline (from $baselineRel)" }

$stamp = Get-Date -Format "yyyyMMdd_HHmmss"
$workingRel = "formal/tooling_snapshots/repo_snapshot_${stamp}_WORKING_evidence_external_evidence.jsonl"
$working = Join-Path $repoRoot $workingRel

# Evidence stream is rooted at external_evidence only (matches how the baseline was created).
$snapArgs = @("snapshot", "--root", "formal/external_evidence", "--out", $working, "--progress-every", "5000")
if ($Fast) {
  Write-Warning "FAST mode: quick drift hint only (non-authoritative). May miss content-only changes; re-run without -Fast for fail-closed verification."
  $snapArgs += "--fast"
}

& $py -m formal.python.tools.repo_hygiene_snapshot @snapArgs | Out-Host

$diffRel = "formal/tooling_snapshots/diff_LATEST_BASELINE_EVIDENCE_to_WORKING_${stamp}.txt"
$diff = Join-Path $repoRoot $diffRel

$diffArgs = @("diff", $baseline, $working, "--profile", $Profile, "--out", $diff, "--max-list", "$MaxList")
if ($IgnoreQuarantine) { $diffArgs += "--ignore-quarantine" }

& $py -m formal.python.tools.repo_hygiene_snapshot @diffArgs | Out-Host

Write-Output "BASELINE=$baselineRel"
Write-Output "WORKING=$workingRel"
Write-Output "DIFF=$diffRel"
if ($Fast) { Write-Output "MODE=FAST_METADATA_ONLY" } else { Write-Output "MODE=FULL_HASH" }
Get-Content $diff -Tail 3
