param(
  [Parameter(ValueFromRemainingArguments = $true)]
  [string[]]$Args
)

$ErrorActionPreference = 'Stop'

$repoRoot = Split-Path -Parent $MyInvocation.MyCommand.Path
$venvPy = Join-Path $repoRoot ".venv\Scripts\python.exe"

if (-not (Test-Path $venvPy)) {
  throw "Expected venv python at '$venvPy'. Create it (e.g., python -m venv .venv) or run with an explicit interpreter." 
}

& $venvPy @Args
