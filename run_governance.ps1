[CmdletBinding(PositionalBinding = $false)]
param(
  [int]$TimeoutSeconds = 1200,
  [switch]$DryRun,
  [Parameter(ValueFromRemainingArguments = $true)]
  [string[]]$GovernanceArgs
)

$ErrorActionPreference = 'Stop'

$repoRoot = Split-Path -Parent $MyInvocation.MyCommand.Path
. (Join-Path $repoRoot 'validation_timeout_guard.ps1')

$powerShellPath = (Get-Process -Id $PID).Path
if (-not $powerShellPath) {
  $powerShellPath = 'pwsh'
}

$governanceRunner = Join-Path $repoRoot 'governance_suite.ps1'
$argumentList = @('-NoProfile', '-ExecutionPolicy', 'Bypass', '-File', $governanceRunner) + $GovernanceArgs

$exitCode = Invoke-ValidationCommand `
  -Label 'governance' `
  -FilePath $powerShellPath `
  -ArgumentList $argumentList `
  -WorkingDirectory $repoRoot `
  -TimeoutSeconds $TimeoutSeconds `
  -DryRun:$DryRun

exit $exitCode
