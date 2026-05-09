param(
  [string]$Target = 'ToeFormal',
  [int]$TimeoutSeconds = 1800,
  [switch]$DryRun
)

$ErrorActionPreference = 'Stop'

$repoRoot = Split-Path -Parent $MyInvocation.MyCommand.Path
. (Join-Path $repoRoot 'validation_timeout_guard.ps1')

$leanRoot = Join-Path $repoRoot 'formal\toe_formal'
$exitCode = Invoke-ValidationCommand `
  -Label 'lean' `
  -FilePath 'lake' `
  -ArgumentList @('build', $Target) `
  -WorkingDirectory $leanRoot `
  -TimeoutSeconds $TimeoutSeconds `
  -KillProcessNames @('lake', 'lean', 'elan') `
  -DryRun:$DryRun

exit $exitCode
