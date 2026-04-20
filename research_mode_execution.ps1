param(
  [string[]]$FocusedTests = @(
    "formal/python/tests/test_research_mode_lane_policy_gate.py",
    "formal/python/tests/test_research_mode_metadata_schema_gate.py",
    "formal/python/tests/test_research_mode_pilot_pack_report.py",
    "formal/python/tests/test_research_mode_step14_acceptance_review_report.py",
    "formal/python/tests/test_research_mode_sandbox_candidacy_review_report.py",
    "formal/python/tests/test_research_mode_harder_qm_stat_target_report.py",
    "formal/python/tests/test_research_mode_qm_stat_sandbox_payload_record_report.py",
    "formal/python/tests/test_research_mode_qm_stat_sandbox_candidate_comparison_report.py",
    "formal/python/tests/test_research_mode_qm_stat_governed_review_wrapper_report.py",
    "formal/python/tests/test_research_mode_qm_stat_sandbox_governed_intake_execution_report.py",
    "formal/python/tests/test_research_mode_qm_stat_sandbox_review_execution_packet_report.py",
    "formal/python/tests/test_research_mode_qm_stat_sandbox_review_execution_report.py",
    "formal/python/tests/test_research_mode_qm_stat_post_review_adjudication_report.py",
    "formal/python/tests/test_research_mode_qm_stat_live_authority_evidence_report.py",
    "formal/python/tests/test_research_mode_qm_stat_reentry_support_artifact_report.py",
    "formal/python/tests/test_research_mode_qm_stat_reentry_eligibility_review_report.py",
    "formal/python/tests/test_research_mode_qm_stat_reentry_review_cycle_queue_report.py"
  ),
  [switch]$SkipGate,
  [string]$ResearchPath = "formal/python/research"
)

$ErrorActionPreference = "Stop"

Write-Host "Research mode active: equation-first discovery with lightweight guardrails." -ForegroundColor Yellow
Write-Host "Canonical mutation remains disabled until sandbox and promotion governance pass." -ForegroundColor Yellow

if (-not $SkipGate) {
  Write-Host "[1/3] Research mode boundary gates" -ForegroundColor Cyan
  ./py.ps1 -m pytest formal/python/tests/test_research_mode_lane_policy_gate.py formal/python/tests/test_research_mode_metadata_schema_gate.py -q
  if ($LASTEXITCODE -ne 0) { throw "Research mode boundary gates failed" }
}

if ((Test-Path $ResearchPath) -and $FocusedTests.Count -gt 0) {
  Write-Host "[2/3] Focused research tests" -ForegroundColor Cyan
  ./py.ps1 -m pytest @FocusedTests -q
  if ($LASTEXITCODE -ne 0) { throw "Focused research tests failed" }
}

if (Test-Path $ResearchPath) {
  Write-Host "[3/17] Materialize retained pilot artifacts" -ForegroundColor Cyan
  ./py.ps1 -m formal.python.research.pilot_pack --write
  if ($LASTEXITCODE -ne 0) { throw "Research pilot materialization failed" }

  Write-Host "[4/17] Materialize Step 14 acceptance review" -ForegroundColor Cyan
  ./py.ps1 -m formal.python.research.acceptance_review --write
  if ($LASTEXITCODE -ne 0) { throw "Research Step 14 acceptance review materialization failed" }

  Write-Host "[5/17] Materialize sandbox candidacy bridge" -ForegroundColor Cyan
  ./py.ps1 -m formal.python.research.sandbox_candidacy_review --write
  if ($LASTEXITCODE -ne 0) { throw "Research sandbox candidacy bridge materialization failed" }

  Write-Host "[6/17] Materialize harder live QM-STAT target" -ForegroundColor Cyan
  ./py.ps1 -m formal.python.research.harder_qm_stat_target --write
  if ($LASTEXITCODE -ne 0) { throw "Research harder QM-STAT target materialization failed" }

  Write-Host "[7/17] Materialize QM-STAT sandbox payload record" -ForegroundColor Cyan
  ./py.ps1 -m formal.python.research.qm_stat_sandbox_payload_record --write
  if ($LASTEXITCODE -ne 0) { throw "Research QM-STAT sandbox payload record materialization failed" }

  Write-Host "[8/17] Materialize QM-STAT payload versus harder-target comparison" -ForegroundColor Cyan
  ./py.ps1 -m formal.python.research.qm_stat_sandbox_candidate_comparison --write
  if ($LASTEXITCODE -ne 0) { throw "Research QM-STAT sandbox candidate comparison materialization failed" }

  Write-Host "[9/17] Materialize QM-STAT governed review wrapper" -ForegroundColor Cyan
  ./py.ps1 -m formal.python.tools.research_mode_qm_stat_governed_review_wrapper_report
  if ($LASTEXITCODE -ne 0) { throw "Research QM-STAT governed review wrapper materialization failed" }

  Write-Host "[10/17] Materialize QM-STAT sandbox governed intake execution" -ForegroundColor Cyan
  ./py.ps1 -m formal.python.tools.research_mode_qm_stat_sandbox_governed_intake_execution_report
  if ($LASTEXITCODE -ne 0) { throw "Research QM-STAT sandbox governed intake execution materialization failed" }

  Write-Host "[11/17] Materialize QM-STAT sandbox review execution packet" -ForegroundColor Cyan
  ./py.ps1 -m formal.python.tools.research_mode_qm_stat_sandbox_review_execution_packet_report
  if ($LASTEXITCODE -ne 0) { throw "Research QM-STAT sandbox review execution packet materialization failed" }

  Write-Host "[12/17] Materialize QM-STAT sandbox review execution" -ForegroundColor Cyan
  ./py.ps1 -m formal.python.tools.research_mode_qm_stat_sandbox_review_execution_report
  if ($LASTEXITCODE -ne 0) { throw "Research QM-STAT sandbox review execution materialization failed" }

  Write-Host "[13/17] Materialize QM-STAT post-review adjudication" -ForegroundColor Cyan
  ./py.ps1 -m formal.python.tools.research_mode_qm_stat_post_review_adjudication_report
  if ($LASTEXITCODE -ne 0) { throw "Research QM-STAT post-review adjudication materialization failed" }

  Write-Host "[14/17] Materialize QM-STAT stronger live-target or authority evidence" -ForegroundColor Cyan
  ./py.ps1 -m formal.python.tools.research_mode_qm_stat_live_authority_evidence_report
  if ($LASTEXITCODE -ne 0) { throw "Research QM-STAT stronger live-target or authority evidence materialization failed" }

  Write-Host "[15/17] Materialize QM-STAT re-entry support artifact" -ForegroundColor Cyan
  ./py.ps1 -m formal.python.tools.research_mode_qm_stat_reentry_support_artifact_report
  if ($LASTEXITCODE -ne 0) { throw "Research QM-STAT re-entry support artifact materialization failed" }

  Write-Host "[16/17] Materialize QM-STAT re-entry eligibility review" -ForegroundColor Cyan
  ./py.ps1 -m formal.python.tools.research_mode_qm_stat_reentry_eligibility_review_report
  if ($LASTEXITCODE -ne 0) { throw "Research QM-STAT re-entry eligibility review materialization failed" }

  Write-Host "[17/17] Materialize QM-STAT re-entry review-cycle queue" -ForegroundColor Cyan
  ./py.ps1 -m formal.python.tools.research_mode_qm_stat_reentry_review_cycle_queue_report
  if ($LASTEXITCODE -ne 0) { throw "Research QM-STAT re-entry review-cycle queue materialization failed" }
}

Write-Host "Research-mode execution complete." -ForegroundColor Green