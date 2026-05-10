[CmdletBinding(PositionalBinding = $false)]
param(
  [int]$TimeoutSeconds = 1200,
  [switch]$LastFailed,
  [int]$MaxFail = 0,
  [switch]$Parallel,
  [string]$ParallelWorkers = 'auto',
  [string]$ParallelDist = 'loadfile',
  [switch]$DryRun,
  [Parameter(ValueFromRemainingArguments = $true)]
  [string[]]$PytestArgs
)

$ErrorActionPreference = 'Stop'

$repoRoot = Split-Path -Parent $MyInvocation.MyCommand.Path
. (Join-Path $repoRoot 'validation_timeout_guard.ps1')

$powerShellPath = (Get-Process -Id $PID).Path
if (-not $powerShellPath) {
  $powerShellPath = 'pwsh'
}

$effectiveArgs = @()
if ($PytestArgs.Count -gt 0) {
  $effectiveArgs += $PytestArgs
} else {
  $effectiveArgs += 'formal/python/tests'
}
if ($LastFailed) {
  $effectiveArgs += '--lf'
}
if ($MaxFail -gt 0) {
  $effectiveArgs += "--maxfail=$MaxFail"
}
if ($Parallel) {
  $effectiveArgs += '-n'
  $effectiveArgs += $ParallelWorkers
  $effectiveArgs += '--dist'
  $effectiveArgs += $ParallelDist
}
$effectiveArgs += '-q'

$pythonRunner = Join-Path $repoRoot 'py.ps1'
$argumentList = @('-NoProfile', '-ExecutionPolicy', 'Bypass', '-File', $pythonRunner, '-m', 'pytest') + $effectiveArgs

$exitCode = Invoke-ValidationCommand `
  -Label 'pytest' `
  -FilePath $powerShellPath `
  -ArgumentList $argumentList `
  -WorkingDirectory $repoRoot `
  -TimeoutSeconds $TimeoutSeconds `
  -DryRun:$DryRun

exit $exitCode
