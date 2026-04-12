param(
    [Parameter(Mandatory = $true)]
    [ValidateSet('baseline', 'draft', 'preclosure', 'final', 'integration')]
    [string]$Stage,

    [string[]]$FocusedTests = @(),

    [switch]$UseInvalidationSelection,
    [string]$InvalidationBaseRef = 'HEAD~1',
    [switch]$IncludeInvalidationWorkingTree,
    [switch]$EnableReadOnlyParallel,
    [string]$ReadOnlyParallelWorkers = 'auto',

    [double]$GovernanceSuiteSeconds,
    [double]$BranchHealthFullPytestSeconds,
    [double]$CheckpointLadderSeconds,
    [double]$GovernanceRequiredImprovementPercent = 10.0,
    [double]$CheckpointRequiredImprovementPercent = 10.0,
    [switch]$UseMeasuredRuntimeCapture,
    [switch]$AllowManualIntegrationCutover,

    [switch]$AllowDivergenceOverride,
    [switch]$Resume
)

$ErrorActionPreference = 'Stop'

function Invoke-TimedCommand {
    param(
        [Parameter(Mandatory = $true)]
        [string]$Label,

        [Parameter(Mandatory = $true)]
        [scriptblock]$Command
    )

    Write-Host "Measuring runtime for $Label..." -ForegroundColor DarkCyan
    $sw = [System.Diagnostics.Stopwatch]::StartNew()
    & $Command
    $exitCode = $LASTEXITCODE
    $sw.Stop()

    if ($exitCode -ne 0) {
        throw "Measured command for '$Label' failed with exit code $exitCode."
    }

    return [Math]::Round($sw.Elapsed.TotalSeconds, 3)
}

$repoRoot = Split-Path -Parent $MyInvocation.MyCommand.Path
Push-Location $repoRoot

try {
    switch ($Stage) {
        'baseline' {
            $baselineMeasurementMode = 'MANUAL'
            $baselineGovernanceCommand = 'pwsh -NoProfile -ExecutionPolicy Bypass -File ./governance_suite.ps1'
            $baselineBranchHealthCommand = './py.ps1 -m pytest formal/python/tests -q'
            $baselineCheckpointCommand = 'pwsh -NoProfile -ExecutionPolicy Bypass -File ./checkpoint_ladder.ps1'

            if ($UseMeasuredRuntimeCapture) {
                $baselineMeasurementMode = 'MEASURED'
                $GovernanceSuiteSeconds = Invoke-TimedCommand -Label 'governance_suite' -Command {
                    pwsh -NoProfile -ExecutionPolicy Bypass -File ./governance_suite.ps1
                }
                $BranchHealthFullPytestSeconds = Invoke-TimedCommand -Label 'branch_health_full_pytest' -Command {
                    ./py.ps1 -m pytest formal/python/tests -q
                }
                $CheckpointLadderSeconds = Invoke-TimedCommand -Label 'checkpoint_ladder' -Command {
                    pwsh -NoProfile -ExecutionPolicy Bypass -File ./checkpoint_ladder.ps1
                }
            }

            if ($GovernanceSuiteSeconds -le 0 -or $BranchHealthFullPytestSeconds -le 0 -or $CheckpointLadderSeconds -le 0) {
                throw "Stage 'baseline' requires positive -GovernanceSuiteSeconds, -BranchHealthFullPytestSeconds, and -CheckpointLadderSeconds values, or -UseMeasuredRuntimeCapture."
            }

            Write-Host "Dual-track stage=baseline: recording runtime baseline artifact." -ForegroundColor Cyan
            ./py.ps1 -m formal.python.tools.governance_runtime_baseline_capture `
                --governance-suite-seconds $GovernanceSuiteSeconds `
                --branch-health-full-pytest-seconds $BranchHealthFullPytestSeconds `
                --checkpoint-ladder-seconds $CheckpointLadderSeconds `
                --measurement-mode $baselineMeasurementMode `
                --governance-suite-command $baselineGovernanceCommand `
                --branch-health-full-pytest-command $baselineBranchHealthCommand `
                --checkpoint-ladder-command $baselineCheckpointCommand
            if ($LASTEXITCODE -ne 0) {
                throw 'Dual-track baseline stage failed runtime baseline capture.'
            }

            Write-Host 'Dual-track baseline stage complete.' -ForegroundColor Green
        }

        'draft' {
            if ($FocusedTests.Count -eq 0) {
                throw "Stage 'draft' requires one or more -FocusedTests entries."
            }

            Write-Host "Dual-track stage=draft: running focused tests only." -ForegroundColor Cyan
            ./py.ps1 -m pytest @FocusedTests -q
            if ($LASTEXITCODE -ne 0) {
                throw 'Dual-track draft stage failed focused tests.'
            }

            Write-Host 'Dual-track draft stage complete.' -ForegroundColor Green
        }

        'preclosure' {
            Write-Host "Dual-track stage=preclosure: running governance once." -ForegroundColor Cyan

            $govArgs = @('-NoProfile', '-ExecutionPolicy', 'Bypass', '-File', './governance_suite.ps1')
            if ($AllowDivergenceOverride) {
                $govArgs += '-AllowDivergenceOverride'
            }
            if ($UseInvalidationSelection) {
                $govArgs += '-UseInvalidationSelection'
                $govArgs += '-InvalidationBaseRef'
                $govArgs += $InvalidationBaseRef
                if ($IncludeInvalidationWorkingTree) {
                    $govArgs += '-IncludeInvalidationWorkingTree'
                }
            }
            if ($EnableReadOnlyParallel) {
                $govArgs += '-EnableReadOnlyParallel'
                $govArgs += '-ReadOnlyParallelWorkers'
                $govArgs += $ReadOnlyParallelWorkers
            }

            pwsh @govArgs
            if ($LASTEXITCODE -ne 0) {
                throw 'Dual-track preclosure stage failed governance suite.'
            }

            Write-Host 'Dual-track preclosure stage complete.' -ForegroundColor Green
        }

        'final' {
            Write-Host "Dual-track stage=final: running checkpoint ladder once with governance reuse enabled." -ForegroundColor Cyan

            $ladderArgs = @('-NoProfile', '-ExecutionPolicy', 'Bypass', '-File', './checkpoint_ladder.ps1', '-ReuseGovernanceWhenUnchanged')
            if ($Resume) {
                $ladderArgs += '-Resume'
            }

            pwsh @ladderArgs
            if ($LASTEXITCODE -ne 0) {
                throw 'Dual-track final stage failed checkpoint ladder.'
            }

            Write-Host 'Dual-track final stage complete.' -ForegroundColor Green
        }

        'integration' {
            $integrationMeasurementMode = 'MANUAL'
            $integrationGovernanceCommand = 'pwsh -NoProfile -ExecutionPolicy Bypass -File ./governance_suite.ps1'
            $integrationBranchHealthCommand = './py.ps1 -m pytest formal/python/tests -q'
            $integrationCheckpointCommand = 'pwsh -NoProfile -ExecutionPolicy Bypass -File ./checkpoint_ladder.ps1 -ReuseGovernanceWhenUnchanged'

            if ($UseMeasuredRuntimeCapture) {
                $integrationMeasurementMode = 'MEASURED'

                $integrationGovArgs = @('-NoProfile', '-ExecutionPolicy', 'Bypass', '-File', './governance_suite.ps1')
                if ($AllowDivergenceOverride) {
                    $integrationGovArgs += '-AllowDivergenceOverride'
                }
                if ($UseInvalidationSelection) {
                    $integrationGovArgs += '-UseInvalidationSelection'
                    $integrationGovArgs += '-InvalidationBaseRef'
                    $integrationGovArgs += $InvalidationBaseRef
                    if ($IncludeInvalidationWorkingTree) {
                        $integrationGovArgs += '-IncludeInvalidationWorkingTree'
                    }
                }
                if ($EnableReadOnlyParallel) {
                    $integrationGovArgs += '-EnableReadOnlyParallel'
                    $integrationGovArgs += '-ReadOnlyParallelWorkers'
                    $integrationGovArgs += $ReadOnlyParallelWorkers
                }
                $integrationGovernanceCommand = "pwsh $($integrationGovArgs -join ' ')"

                $integrationLadderArgs = @('-NoProfile', '-ExecutionPolicy', 'Bypass', '-File', './checkpoint_ladder.ps1', '-ReuseGovernanceWhenUnchanged')
                if ($Resume) {
                    $integrationLadderArgs += '-Resume'
                }
                $integrationCheckpointCommand = "pwsh $($integrationLadderArgs -join ' ')"

                $GovernanceSuiteSeconds = Invoke-TimedCommand -Label 'governance_suite' -Command {
                    pwsh @integrationGovArgs
                }
                $BranchHealthFullPytestSeconds = Invoke-TimedCommand -Label 'branch_health_full_pytest' -Command {
                    ./py.ps1 -m pytest formal/python/tests -q
                }
                $CheckpointLadderSeconds = Invoke-TimedCommand -Label 'checkpoint_ladder' -Command {
                    pwsh @integrationLadderArgs
                }
            }

            if ($GovernanceSuiteSeconds -le 0 -or $BranchHealthFullPytestSeconds -le 0 -or $CheckpointLadderSeconds -le 0) {
                throw "Stage 'integration' requires positive -GovernanceSuiteSeconds, -BranchHealthFullPytestSeconds, and -CheckpointLadderSeconds values, or -UseMeasuredRuntimeCapture."
            }

            if ($integrationMeasurementMode -ne 'MEASURED' -and -not $AllowManualIntegrationCutover) {
                throw "Stage 'integration' requires measured runtime evidence by default. Re-run with -UseMeasuredRuntimeCapture (recommended) or explicitly override with -AllowManualIntegrationCutover."
            }

            if ($integrationMeasurementMode -ne 'MEASURED' -and $AllowManualIntegrationCutover) {
                Write-Host "WARN: integration cutover is running in manual mode override; resulting cutover report remains non-authoritative." -ForegroundColor Yellow
            }

            Write-Host "Dual-track stage=integration: capturing current runtime snapshot and cutover report." -ForegroundColor Cyan

            ./py.ps1 -m formal.python.tools.dual_track_runtime_snapshot `
                --governance-suite-seconds $GovernanceSuiteSeconds `
                --branch-health-full-pytest-seconds $BranchHealthFullPytestSeconds `
                --checkpoint-ladder-seconds $CheckpointLadderSeconds `
                --measurement-mode $integrationMeasurementMode `
                --governance-suite-command $integrationGovernanceCommand `
                --branch-health-full-pytest-command $integrationBranchHealthCommand `
                --checkpoint-ladder-command $integrationCheckpointCommand
            if ($LASTEXITCODE -ne 0) {
                throw 'Dual-track integration stage failed runtime snapshot generation.'
            }

            ./py.ps1 -m formal.python.tools.dual_track_cutover_report_generate `
                --governance-required-improvement-percent $GovernanceRequiredImprovementPercent `
                --checkpoint-required-improvement-percent $CheckpointRequiredImprovementPercent
            if ($LASTEXITCODE -ne 0) {
                throw 'Dual-track integration stage failed cutover report generation.'
            }

            Write-Host 'Dual-track integration stage complete.' -ForegroundColor Green
        }
    }
}
finally {
    Pop-Location
}
