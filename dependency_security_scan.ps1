$ErrorActionPreference = 'Stop'

$reportPath = "formal/output/reports/dependency_security_scan_report_v0.json"

Write-Host "Running dependency security scan against requirements.active.lock" -ForegroundColor Cyan
./py.ps1 -m pip_audit -r requirements.active.lock --format json --output $reportPath
if ($LASTEXITCODE -ne 0) {
  throw "Dependency security scan failed. See $reportPath"
}

Write-Host "dependency_security_scan: ok report_path=$reportPath" -ForegroundColor Green
