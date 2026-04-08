$ErrorActionPreference = 'Stop'

$lockPath = "requirements.active.lock"
$reportPath = "formal/output/reports/dependency_security_scan_report_v0.json"

if (-not (Test-Path $lockPath)) {
  throw "Missing dependency lockfile: $lockPath"
}

$lockContent = Get-Content -Path $lockPath -Raw
if ($lockContent.Trim().StartsWith("{") -or $lockContent.Trim().StartsWith("[")) {
  throw "Invalid lockfile format for pip-audit: expected pip-freeze lines in $lockPath"
}

Write-Host "Running dependency security scan against $lockPath" -ForegroundColor Cyan
./py.ps1 -m pip_audit -r $lockPath --format json --output $reportPath
if ($LASTEXITCODE -ne 0) {
  throw "Dependency security scan failed. See $reportPath"
}

if (-not (Test-Path $reportPath)) {
  throw "Dependency security scan did not produce report: $reportPath"
}

$report = Get-Content -Path $reportPath -Raw | ConvertFrom-Json
if ($null -eq $report.dependencies) {
  throw "Dependency security scan report missing dependencies field: $reportPath"
}

$dependencyCount = @($report.dependencies).Count
Write-Host "dependency_security_scan: ok report_path=$reportPath dependencies=$dependencyCount" -ForegroundColor Green
