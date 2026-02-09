# lean.ps1 - hard-bound Lean wrapper
[CmdletBinding(PositionalBinding=$false)]
param(
  [Parameter(ValueFromRemainingArguments=$true)]
  [string[]] $Args
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

$LeanExe = Join-Path $env:USERPROFILE ".elan\toolchains\leanprover--lean4---v4.27.0-rc1\bin\lean.exe"
if ($env:TOE_LEAN_EXE) { $LeanExe = $env:TOE_LEAN_EXE }

if (-not (Test-Path -LiteralPath $LeanExe)) {
  throw "Lean executable not found: $LeanExe`nSet TOE_LEAN_EXE or reinstall toolchain."
}

& $LeanExe @Args
