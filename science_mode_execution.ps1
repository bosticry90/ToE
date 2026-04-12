param(
  [switch]$SkipExternalPacket,
  [string]$ExternalPacketMode = "numeric_only",
  [switch]$Packet41Only,
  [string]$Packet41ComponentTarget = "packet41_eligibility_review_pass"
)

$ErrorActionPreference = "Stop"

Write-Host "Science mode active: governance expansion frozen for this run." -ForegroundColor Yellow

Write-Host "[1/5] Packet41 seam strike report" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.packet41_successor_decision_enforcement
if ($LASTEXITCODE -ne 0) { throw "packet41_successor_decision_enforcement failed" }

Write-Host "[2/5] Packet41 narrow numeric-clearance rework tranche" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.packet41_numeric_clearance_rework_tranche_report
if ($LASTEXITCODE -ne 0) { throw "packet41_numeric_clearance_rework_tranche_report failed" }

Write-Host "[2b/5] Packet41 review-layer clearance decomposition" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.packet41_review_layer_clearance_decomposition_report
if ($LASTEXITCODE -ne 0) { throw "packet41_review_layer_clearance_decomposition_report failed" }

Write-Host "[2c/5] Packet41 single-component lift tranche ($Packet41ComponentTarget)" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.packet41_component_lift_tranche_report --component $Packet41ComponentTarget
if ($LASTEXITCODE -ne 0) { throw "packet41_component_lift_tranche_report failed" }

if ($Packet41ComponentTarget -eq "packet41_eligibility_review_pass") {
  Write-Host "[2d/5] Packet41 eligibility evidence-injection tranche" -ForegroundColor Cyan
  ./py.ps1 -m formal.python.tools.packet41_eligibility_evidence_injection_tranche_report
  if ($LASTEXITCODE -ne 0) { throw "packet41_eligibility_evidence_injection_tranche_report failed" }

  Write-Host "[2e/5] Re-run component lift after evidence injection" -ForegroundColor Cyan
  ./py.ps1 -m formal.python.tools.packet41_component_lift_tranche_report --component $Packet41ComponentTarget
  if ($LASTEXITCODE -ne 0) { throw "packet41_component_lift_tranche_report rerun failed" }
}

if ($Packet41ComponentTarget -eq "packet41_targeted_justification_review_pass") {
  Write-Host "[2d/5] Packet41 targeted-justification evidence-injection tranche" -ForegroundColor Cyan
  ./py.ps1 -m formal.python.tools.packet41_targeted_justification_evidence_injection_tranche_report
  if ($LASTEXITCODE -ne 0) { throw "packet41_targeted_justification_evidence_injection_tranche_report failed" }

  Write-Host "[2e/5] Re-run component lift after targeted-justification evidence injection" -ForegroundColor Cyan
  ./py.ps1 -m formal.python.tools.packet41_component_lift_tranche_report --component $Packet41ComponentTarget
  if ($LASTEXITCODE -ne 0) { throw "packet41_component_lift_tranche_report rerun failed" }
}

if ($Packet41ComponentTarget -eq "packet41_hold_fork_release_condition_pass") {
  Write-Host "[2d/5] Packet41 hold-fork evidence-injection tranche" -ForegroundColor Cyan
  ./py.ps1 -m formal.python.tools.packet41_hold_fork_evidence_injection_tranche_report
  if ($LASTEXITCODE -ne 0) { throw "packet41_hold_fork_evidence_injection_tranche_report failed" }

  Write-Host "[2e/5] Re-run component lift after hold-fork evidence injection" -ForegroundColor Cyan
  ./py.ps1 -m formal.python.tools.packet41_component_lift_tranche_report --component $Packet41ComponentTarget
  if ($LASTEXITCODE -ne 0) { throw "packet41_component_lift_tranche_report rerun failed" }

  $componentLiftPath = "formal/output/reports/packet41_component_lift_tranche_20260411_v0.json"
  $componentLift = Get-Content $componentLiftPath -Raw | ConvertFrom-Json
  $stopRuleTriggered = [bool]$componentLift.summary.stop_rule.triggered
  if ($stopRuleTriggered) {
    Write-Host "[2f/5] Stop-rule triggered: run retrospective single-component lift tranche" -ForegroundColor Yellow
    $retrospectiveOutPath = "formal/output/reports/packet41_component_lift_retrospective_tranche_20260411_v0.json"
    ./py.ps1 -m formal.python.tools.packet41_component_lift_tranche_report --component retrospective_cumulative_delta_audit_release_condition_pass --out $retrospectiveOutPath
    if ($LASTEXITCODE -ne 0) { throw "packet41_component_lift_tranche_report retrospective tranche failed" }

    Write-Host "[2g/5] Emit Packet41 branch decision tranche" -ForegroundColor Yellow
    ./py.ps1 -m formal.python.tools.packet41_branch_decision_tranche_report --hold-fork-component-lift-path $componentLiftPath --retrospective-component-lift-path $retrospectiveOutPath
    if ($LASTEXITCODE -ne 0) { throw "packet41_branch_decision_tranche_report failed" }
  }
}

$externalReportPath = ""
if (-not $SkipExternalPacket) {
  Write-Host "[3/5] External discriminative science packet" -ForegroundColor Cyan
  $externalReportPath = ./py.ps1 -m formal.python.tools.cross_anchor_bragg_vs_sound_report --mode $ExternalPacketMode
  if ($LASTEXITCODE -ne 0) { throw "cross_anchor_bragg_vs_sound_report failed" }
  if ($null -eq $externalReportPath) { throw "cross_anchor_bragg_vs_sound_report returned empty output path" }
  $externalReportPath = [string]$externalReportPath
  $externalReportPath = $externalReportPath.Trim()
}

Write-Host "[4/5] Recompute blocker state" -ForegroundColor Cyan
./py.ps1 -m formal.python.tools.physics_progress_ledger_generate
if ($LASTEXITCODE -ne 0) { throw "physics_progress_ledger_generate failed" }
./py.ps1 -m formal.python.tools.science_global_completion_baseline_report
if ($LASTEXITCODE -ne 0) { throw "science_global_completion_baseline_report failed" }

$packet41ReworkPath = "formal/output/reports/packet41_numeric_clearance_rework_tranche_20260411_v0.json"
$packet41Rework = Get-Content $packet41ReworkPath -Raw | ConvertFrom-Json
$packet41Moved = [bool]$packet41Rework.summary.packet41_hold_state_changed

if (-not $Packet41Only -and -not $packet41Moved) {
  Write-Host "Packet41 remained flat; switching to QM micro-subtarget refinement." -ForegroundColor Yellow
  ./py.ps1 -m formal.python.tools.theorem_gap_qm_subtarget_tranche_report
  if ($LASTEXITCODE -ne 0) { throw "theorem_gap_qm_subtarget_tranche_report failed" }
} elseif ($Packet41Only -and -not $packet41Moved) {
  Write-Host "Packet41-only mode active; QM fallback intentionally skipped." -ForegroundColor Yellow
} else {
  Write-Host "Packet41 moved; QM fallback skipped for this run." -ForegroundColor Green
}

Write-Host "[5/5] Build science strike summary" -ForegroundColor Cyan
$summaryArgs = @("-m", "formal.python.tools.science_mode_strike_summary")
if (-not [string]::IsNullOrWhiteSpace($externalReportPath)) {
  $summaryArgs += "--external-report-path"
  $summaryArgs += $externalReportPath
  $summaryArgs += "--external-packet-mode"
  $summaryArgs += $ExternalPacketMode
}
if (-not $Packet41Only -and -not $packet41Moved) {
  $summaryArgs += "--qm-fallback-executed"
}
if ($Packet41Only) {
  $summaryArgs += "--packet41-only"
}
$summaryArgs += "--packet41-component-target"
$summaryArgs += $Packet41ComponentTarget
./py.ps1 @summaryArgs
if ($LASTEXITCODE -ne 0) { throw "science_mode_strike_summary failed" }

Write-Host "Science-mode execution complete." -ForegroundColor Green