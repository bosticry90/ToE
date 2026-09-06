# build.ps1
# Hard-binds Lake + Lean and auto-finds the lake project root.
# Usage:
#   .\build.ps1
#   .\build.ps1 ToeFormal.Derivation.Parents.P1_NLS_EFT
#   .\build.ps1 --clean ToeFormal.Derivation.Parents.P1_NLS_EFT
#   .\build.ps1 --all
#   .\build.ps1 --where
#   .\build.ps1 --toolchain

[CmdletBinding(PositionalBinding = $true)]
param(
  [Parameter(ValueFromRemainingArguments = $true)]
  [string[]] $Args
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

function Write-Info([string]$msg) { Write-Host "[build] $msg" }

# -----------------------
# Hard-bound executables
# -----------------------
function Resolve-Tool(
  [string]$override,
  [string]$commandName,
  [string[]]$fallbacks
) {
  if (-not [string]::IsNullOrWhiteSpace($override)) {
    return $override
  }
  $command = Get-Command $commandName -CommandType Application -ErrorAction SilentlyContinue |
    Select-Object -First 1
  if ($command) {
    return $command.Source
  }
  foreach ($fallback in $fallbacks) {
    if (
      -not [string]::IsNullOrWhiteSpace($fallback) -and
      (Test-Path -LiteralPath $fallback)
    ) {
      return $fallback
    }
  }
  throw "$commandName not found on PATH and no platform fallback exists."
}

$lakeFallbacks = @()
if (-not [string]::IsNullOrWhiteSpace($env:LOCALAPPDATA)) {
  $lakeFallbacks += Join-Path $env:LOCALAPPDATA "Microsoft\WinGet\Links\lake.exe"
}
$leanFallbacks = @()
if (-not [string]::IsNullOrWhiteSpace($env:USERPROFILE)) {
  $leanFallbacks += Join-Path $env:USERPROFILE ".elan\toolchains\leanprover--lean4---v4.27.0-rc1\bin\lean.exe"
}

# Explicit overrides remain highest priority.  Otherwise prefer the active
# elan/toolchain shims on PATH, with the prior Windows paths as fallbacks.
$LakeExe = Resolve-Tool $env:TOE_LAKE_EXE "lake" $lakeFallbacks
$LeanExe = Resolve-Tool $env:TOE_LEAN_EXE "lean" $leanFallbacks

function Assert-Exists([string]$path, [string]$label) {
  if (-not (Test-Path -LiteralPath $path)) {
    throw "$label not found: $path`nSet TOE_LAKE_EXE / TOE_LEAN_EXE or reinstall."
  }
}

Assert-Exists $LakeExe "Lake exe"
Assert-Exists $LeanExe "Lean exe"

# -----------------------
# Parse flags + targets
# -----------------------
$doClean = $false
$doAll = $false
$doWhere = $false
$showToolchain = $false
$targets = @()

foreach ($a in $Args) {
  switch -Regex ($a) {
    '^--clean$'     { $doClean = $true; continue }
    '^--all$'       { $doAll = $true; continue }
    '^--where$'     { $doWhere = $true; continue }
    '^--toolchain$' { $showToolchain = $true; continue }
    default         { $targets += $a; continue }
  }
}

# -----------------------
# Find project root
# -----------------------
function Has-Lakefile([string]$dir) {
  return (Test-Path -LiteralPath (Join-Path $dir "lakefile.lean")) -or
         (Test-Path -LiteralPath (Join-Path $dir "lakefile.toml"))
}

function Find-LakeRoot([string]$startDir) {
  $d = (Resolve-Path -LiteralPath $startDir).Path
  while ($true) {
    if (Has-Lakefile $d) { return $d }
    $parent = Split-Path -Parent $d
    if ($parent -eq $d -or [string]::IsNullOrWhiteSpace($parent)) { break }
    $d = $parent
  }
  return $null
}

$pwdPath = (Get-Location).Path
$root = Find-LakeRoot $pwdPath

if (-not $root) {
  throw "No lakefile.lean or lakefile.toml found from '$pwdPath' upward. cd into your toe_formal root and rerun."
}

# Make sure lake runs from project root even if invoked elsewhere
Push-Location $root
try {
  if ($doWhere) {
    Write-Info "Lake     : $LakeExe"
    Write-Info "Lean     : $LeanExe"
    Write-Info "ProjRoot : $root"
    Write-Info "PWD      : $pwdPath"
    return
  }

  Write-Info "ProjRoot : $root"
  Write-Info "Using Lake: $LakeExe"
  Write-Info "Using Lean: $LeanExe"

  # Help downstream tools that consult LEAN/ELAN
  $env:LEAN = $LeanExe

  if ($showToolchain) {
    Write-Info "Lean version (pinned):"
    & $LeanExe --version
    Write-Info "Lake version:"
    & $LakeExe --version
    Write-Info "Lean version via lake env (project):"
    & $LakeExe env lean --version
  }

  if ($doClean) {
    Write-Info "lake clean"
    & $LakeExe clean
  }

  if ($doAll -or $targets.Count -eq 0) {
    Write-Info "lake build"
    & $LakeExe build
  } else {
    foreach ($t in $targets) {
      Write-Info "lake build $t"
      & $LakeExe build $t
    }
  }

  Write-Info "Done."
}
finally {
  Pop-Location
}
