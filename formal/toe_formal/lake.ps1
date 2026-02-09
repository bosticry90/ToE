# lake.ps1 - hard-bound Lake wrapper (runs from this project root)
[CmdletBinding(PositionalBinding=$false)]
param(
  [Parameter(ValueFromRemainingArguments=$true)]
  [string[]] $Args
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

$LakeExe = Join-Path $env:LOCALAPPDATA "Microsoft\WinGet\Links\lake.exe"
if ($env:TOE_LAKE_EXE) { $LakeExe = $env:TOE_LAKE_EXE }

if (-not (Test-Path -LiteralPath $LakeExe)) {
  throw "Lake executable not found: $LakeExe`nSet TOE_LAKE_EXE or reinstall Lean/Lake."
}

$ScriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
Push-Location $ScriptDir
try {
  & $LakeExe @Args
}
finally {
  Pop-Location
}
