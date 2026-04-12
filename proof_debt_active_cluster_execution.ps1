# Active proof-debt runner (blocker-facing lane)
# Purpose:
# - Execute only the active proof-debt cluster packet/discharge chain.
# - Refresh next-cluster selection and consolidated strike summary.
# - Intentionally skip historical branch-ruling regeneration.
#
# Scope contract:
# - Use for active blocker-facing proof-debt runs.
# - Historical branch-ruling artifacts are regenerated only during explicit ruling workflows.
#
# Example:
#   ./proof_debt_active_cluster_execution.ps1
#   ./proof_debt_active_cluster_execution.ps1 -SkipSummary

param(
  [string]$ActiveClusterId = "",
  [switch]$SkipSummary
)

$ErrorActionPreference = "Stop"
$TotalSteps = if ($SkipSummary) { 9 } else { 10 }

if ([string]::IsNullOrWhiteSpace($ActiveClusterId)) {
  $NextClusterReportPath = "formal/output/reports/proof_debt_next_cluster_selection_report_20260411_v0.json"
  if (-not (Test-Path $NextClusterReportPath)) {
    throw "No ActiveClusterId supplied and next-cluster selection report is missing at $NextClusterReportPath."
  }
  $ActiveClusterId = (Get-Content $NextClusterReportPath | ConvertFrom-Json).summary.selected_next_cluster_id
}

switch ($ActiveClusterId) {
  "PDC-MATH-PROOF-DEBT-BURNDOWN-01" {
    $PacketDeclaration = "formal/docs/release/PROOF_DEBT_FIRST_FORMAL_CAMPAIGN_PACKET_20260411_v0.json"
    $DischargeDeclaration = "formal/docs/release/PROOF_DEBT_FIRST_FORMAL_CAMPAIGN_DISCHARGE_TRANCHE_20260411_v0.json"
    $FocusDeclaration = "formal/docs/release/PROOF_DEBT_ACTIVE_CLUSTER_NEXT_TRANCHE_FOCUS_20260411_v0.json"
    $ClusterFocusOut = "formal/output/reports/proof_debt_active_cluster_next_tranche_focus_math_pd_burndown_20260411_v0.json"
  }
  "PDC-EMU1-DISTRIBUTIONAL-AUTH-01" {
    $PacketDeclaration = "formal/docs/release/PROOF_DEBT_FIRST_FORMAL_CAMPAIGN_PACKET_EMU1_DISTRIBUTIONAL_AUTH_20260411_v0.json"
    $DischargeDeclaration = "formal/docs/release/PROOF_DEBT_FIRST_FORMAL_CAMPAIGN_DISCHARGE_TRANCHE_EMU1_DISTRIBUTIONAL_AUTH_20260411_v0.json"
    $FocusDeclaration = "formal/docs/release/PROOF_DEBT_ACTIVE_CLUSTER_NEXT_TRANCHE_FOCUS_EMU1_DISTRIBUTIONAL_AUTH_20260411_v0.json"
    $ClusterFocusOut = "formal/output/reports/proof_debt_active_cluster_next_tranche_focus_emu1_distributional_auth_20260411_v0.json"
  }
  default {
    throw "No proof-debt declaration mapping found for active cluster '$ActiveClusterId'."
  }
}

Write-Host "Proof-debt active-cluster execution mode" -ForegroundColor Cyan
Write-Host "Active cluster: $ActiveClusterId" -ForegroundColor Cyan
Write-Host "Historical branch ruling regeneration is intentionally skipped." -ForegroundColor Yellow

Write-Host "[1/$TotalSteps] Packet readiness report" -ForegroundColor Green
./py.ps1 -m formal.python.tools.proof_debt_first_formal_campaign_packet_report --declaration $PacketDeclaration
if ($LASTEXITCODE -ne 0) { throw "proof_debt_first_formal_campaign_packet_report failed" }

Write-Host "[2/$TotalSteps] Packet decision report" -ForegroundColor Green
./py.ps1 -m formal.python.tools.proof_debt_first_formal_campaign_decision_report
if ($LASTEXITCODE -ne 0) { throw "proof_debt_first_formal_campaign_decision_report failed" }

Write-Host "[3/$TotalSteps] Bounded discharge tranche report" -ForegroundColor Green
./py.ps1 -m formal.python.tools.proof_debt_first_formal_campaign_discharge_tranche_report --declaration $DischargeDeclaration
if ($LASTEXITCODE -ne 0) { throw "proof_debt_first_formal_campaign_discharge_tranche_report failed" }

Write-Host "[4/$TotalSteps] Discharge decision report" -ForegroundColor Green
./py.ps1 -m formal.python.tools.proof_debt_first_formal_campaign_discharge_decision_report
if ($LASTEXITCODE -ne 0) { throw "proof_debt_first_formal_campaign_discharge_decision_report failed" }

Write-Host "[5/$TotalSteps] Active-cluster next-tranche focus report" -ForegroundColor Green
./py.ps1 -m formal.python.tools.proof_debt_active_cluster_next_tranche_focus_report --declaration $FocusDeclaration
if ($LASTEXITCODE -ne 0) { throw "proof_debt_active_cluster_next_tranche_focus_report failed" }

$FocusReportPath = "formal/output/reports/proof_debt_active_cluster_next_tranche_focus_report_20260411_v0.json"
Copy-Item -LiteralPath $FocusReportPath -Destination $ClusterFocusOut -Force
$SelectedSurfaceId = (Get-Content $FocusReportPath | ConvertFrom-Json).summary.selected_surface_id

if ([string]::IsNullOrWhiteSpace($SelectedSurfaceId)) {
  Write-Host "[6/$TotalSteps] No eligible active-cluster surface remains; skipping bounded surface tranche report" -ForegroundColor Yellow
  Write-Host "[7/$TotalSteps] No eligible active-cluster surface remains; skipping surface ruling report" -ForegroundColor Yellow
  Write-Host "[8/$TotalSteps] No eligible active-cluster surface remains; skipping focus refresh" -ForegroundColor Yellow
}
else {
  switch ($SelectedSurfaceId) {
    "MATH-PD-C05-BURNDOWN-GATE" {
      $SurfaceTrancheDeclaration = "formal/docs/release/PROOF_DEBT_ACTIVE_CLUSTER_SURFACE_TRANCHE_MATH_PD_C05_BURNDOWN_20260411_v0.json"
      $SurfaceRulingDeclaration = "formal/docs/release/PROOF_DEBT_ACTIVE_CLUSTER_SURFACE_RULING_MATH_PD_C05_BURNDOWN_GATE_20260411_v0.json"
      $SurfaceRulingOut = "formal/output/reports/proof_debt_active_cluster_surface_ruling_math_pd_c05_burndown_gate_20260411_v0.json"
    }
    "MATH-PD-C05-MARKER-STABILITY-GATE" {
      $SurfaceTrancheDeclaration = "formal/docs/release/PROOF_DEBT_ACTIVE_CLUSTER_SURFACE_TRANCHE_MATH_PD_C05_MARKER_STABILITY_20260411_v0.json"
      $SurfaceRulingDeclaration = "formal/docs/release/PROOF_DEBT_ACTIVE_CLUSTER_SURFACE_RULING_MATH_PD_C05_MARKER_STABILITY_GATE_20260411_v0.json"
      $SurfaceRulingOut = "formal/output/reports/proof_debt_active_cluster_surface_ruling_math_pd_c05_marker_stability_gate_20260411_v0.json"
    }
    "EMU1-MICRO21-AUTHORIZATION-GATE" {
      $SurfaceTrancheDeclaration = "formal/docs/release/PROOF_DEBT_ACTIVE_CLUSTER_SURFACE_TRANCHE_EMU1_MICRO21_AUTHORIZATION_20260411_v0.json"
      $SurfaceRulingDeclaration = "formal/docs/release/PROOF_DEBT_ACTIVE_CLUSTER_SURFACE_RULING_EMU1_MICRO21_AUTHORIZATION_GATE_20260411_v0.json"
      $SurfaceRulingOut = "formal/output/reports/proof_debt_active_cluster_surface_ruling_emu1_micro21_authorization_gate_20260411_v0.json"
    }
    "EMU1-MICRO22-SEMANTICS-MAPPING-GATE" {
      $SurfaceTrancheDeclaration = "formal/docs/release/PROOF_DEBT_ACTIVE_CLUSTER_SURFACE_TRANCHE_EMU1_MICRO22_SEMANTICS_MAPPING_20260411_v0.json"
      $SurfaceRulingDeclaration = "formal/docs/release/PROOF_DEBT_ACTIVE_CLUSTER_SURFACE_RULING_EMU1_MICRO22_SEMANTICS_MAPPING_GATE_20260411_v0.json"
      $SurfaceRulingOut = "formal/output/reports/proof_debt_active_cluster_surface_ruling_emu1_micro22_semantics_mapping_gate_20260411_v0.json"
    }
    "EMU1-MICRO23-REFERENCE-SURFACE-GATE" {
      $SurfaceTrancheDeclaration = "formal/docs/release/PROOF_DEBT_ACTIVE_CLUSTER_SURFACE_TRANCHE_EMU1_MICRO23_REFERENCE_SURFACE_20260411_v0.json"
      $SurfaceRulingDeclaration = "formal/docs/release/PROOF_DEBT_ACTIVE_CLUSTER_SURFACE_RULING_EMU1_MICRO23_REFERENCE_SURFACE_GATE_20260411_v0.json"
      $SurfaceRulingOut = "formal/output/reports/proof_debt_active_cluster_surface_ruling_emu1_micro23_reference_surface_gate_20260411_v0.json"
    }
    default {
      throw "No active-cluster surface declaration mapping found for selected surface '$SelectedSurfaceId'."
    }
  }

  Write-Host "[6/$TotalSteps] Bounded active-cluster surface tranche report" -ForegroundColor Green
  ./py.ps1 -m formal.python.tools.proof_debt_active_cluster_surface_tranche_report --declaration $SurfaceTrancheDeclaration
  if ($LASTEXITCODE -ne 0) { throw "proof_debt_active_cluster_surface_tranche_report failed" }

  Write-Host "[7/$TotalSteps] Active-cluster surface ruling report" -ForegroundColor Green
  ./py.ps1 -m formal.python.tools.proof_debt_active_cluster_surface_ruling_report --declaration $SurfaceRulingDeclaration --out $SurfaceRulingOut
  if ($LASTEXITCODE -ne 0) { throw "proof_debt_active_cluster_surface_ruling_report failed" }

  Write-Host "[8/$TotalSteps] Active-cluster next-tranche focus report refresh" -ForegroundColor Green
  ./py.ps1 -m formal.python.tools.proof_debt_active_cluster_next_tranche_focus_report --declaration $FocusDeclaration
  if ($LASTEXITCODE -ne 0) { throw "proof_debt_active_cluster_next_tranche_focus_report refresh failed" }
  Copy-Item -LiteralPath $FocusReportPath -Destination $ClusterFocusOut -Force
}

Write-Host "[9/$TotalSteps] Next-cluster selection report refresh" -ForegroundColor Green
./py.ps1 -m formal.python.tools.proof_debt_next_cluster_selection_report
if ($LASTEXITCODE -ne 0) { throw "proof_debt_next_cluster_selection_report failed" }

if (-not $SkipSummary) {
  Write-Host "[10/$TotalSteps] Consolidated strike summary refresh" -ForegroundColor Green
  ./py.ps1 -m formal.python.tools.science_mode_strike_summary --out formal/output/reports/science_mode_strike_summary.json
  if ($LASTEXITCODE -ne 0) { throw "science_mode_strike_summary failed" }
}

Write-Host "Completed active-cluster proof-debt execution without branch-ruling regeneration." -ForegroundColor Green
