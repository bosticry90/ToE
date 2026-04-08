param(
    [switch]$Resume
)

$ErrorActionPreference = 'Stop'

$repoRoot = Split-Path -Parent $MyInvocation.MyCommand.Path
Push-Location $repoRoot

$progressPath = 'formal/output/reports/checkpoint_ladder_progress_v0.json'
$summaryPath = 'formal/output/reports/checkpoint_ladder_acceptance_summary_v0.json'

$generatedOutputsManifestPath = 'formal/docs/release/CHECKPOINT_LADDER_GENERATED_OUTPUTS_MANIFEST_v0.json'

function Get-GitStatusSnapshot {
    $status = @(git status --short)
    if ($LASTEXITCODE -ne 0) {
        throw 'Failed to read git status snapshot.'
    }
    return @($status | Sort-Object)
}

function Get-GeneratedOutputs {
    param(
        [Parameter(Mandatory = $true)] [string]$ManifestPath
    )

    if (-not (Test-Path $ManifestPath)) {
        throw ("Missing generated-output manifest: {0}" -f $ManifestPath)
    }

    $manifest = Get-Content $ManifestPath -Raw | ConvertFrom-Json
    $schemaId = [string]$manifest.schema_id
    if ($schemaId -ne 'CHECKPOINT_LADDER_GENERATED_OUTPUTS_MANIFEST_v0') {
        throw ("Unexpected generated-output manifest schema_id: {0}" -f $schemaId)
    }

    if ($null -eq $manifest.generated_outputs -or $manifest.generated_outputs.Count -eq 0) {
        throw 'Generated-output manifest has no generated_outputs entries.'
    }

    $outputs = @()
    foreach ($entry in $manifest.generated_outputs) {
        $path = [string]$entry.path
        $restore = [bool]$entry.restore
        if ($restore -and -not [string]::IsNullOrWhiteSpace($path)) {
            $outputs += $path
        }
    }

    if ($outputs.Count -eq 0) {
        throw 'Generated-output manifest produced zero restore paths.'
    }

    return $outputs
}

$generatedOutputs = @(Get-GeneratedOutputs -ManifestPath $generatedOutputsManifestPath)
$preRunStatus = @(Get-GitStatusSnapshot)

function Load-ProgressState {
    param(
        [Parameter(Mandatory = $true)] [string]$Path
    )
    if (-not (Test-Path $Path)) {
        return @{}
    }
    $raw = Get-Content $Path -Raw | ConvertFrom-Json
    $state = @{}
    if ($null -ne $raw.completed_steps) {
        foreach ($step in $raw.completed_steps) {
            $state[[string]$step] = $true
        }
    }
    return $state
}

function Save-ProgressState {
    param(
        [Parameter(Mandatory = $true)] [string]$Path,
        [Parameter(Mandatory = $true)] [hashtable]$State
    )
    $completed = @($State.Keys | Sort-Object)
    $payload = [ordered]@{
        schema_id = 'CHECKPOINT_LADDER_PROGRESS_v0'
        updated_at_utc = (Get-Date).ToUniversalTime().ToString('o')
        completed_steps = $completed
    }
    $dir = Split-Path -Parent $Path
    if (-not (Test-Path $dir)) {
        New-Item -ItemType Directory -Path $dir -Force | Out-Null
    }
    $payload | ConvertTo-Json -Depth 5 | Set-Content -Path $Path -Encoding utf8
}

function Write-AcceptanceSummary {
    param(
        [Parameter(Mandatory = $true)] [string]$Path,
        [Parameter(Mandatory = $true)] [array]$StepResults,
        [Parameter(Mandatory = $true)] [bool]$Failed,
        [Parameter(Mandatory = $true)] [bool]$CleanTree,
        [Parameter(Mandatory = $false)] [array]$StatusOutput
    )

    $headRaw = git rev-parse --short HEAD
    $head = ''
    if ($LASTEXITCODE -eq 0) {
        $head = [string]$headRaw
        $head = $head.Trim()
    }

    $payload = [ordered]@{
        schema_id = 'CHECKPOINT_LADDER_ACCEPTANCE_SUMMARY_v0'
        generated_at_utc = (Get-Date).ToUniversalTime().ToString('o')
        head_commit = $head
        resume_mode = [bool]$Resume
        failed = [bool]$Failed
        clean_tree = [bool]$CleanTree
        step_results = $StepResults
        status_output = $StatusOutput
    }
    $dir = Split-Path -Parent $Path
    if (-not (Test-Path $dir)) {
        New-Item -ItemType Directory -Path $dir -Force | Out-Null
    }
    $payload | ConvertTo-Json -Depth 8 | Set-Content -Path $Path -Encoding utf8
}

$progressState = Load-ProgressState -Path $progressPath
$stepResults = @()

function Invoke-Step {
    param(
        [Parameter(Mandatory = $true)] [string]$StepKey,
        [Parameter(Mandatory = $true)] [string]$Name,
        [Parameter(Mandatory = $true)] [scriptblock]$Body
    )

    if ($Resume -and $progressState.ContainsKey($StepKey) -and $progressState[$StepKey]) {
        Write-Host ("`n==> {0} (resume skip)" -f $Name) -ForegroundColor Yellow
        $script:stepResults += [ordered]@{ step = $Name; key = $StepKey; status = 'SKIPPED_RESUME' }
        return
    }

    Write-Host ("`n==> {0}" -f $Name) -ForegroundColor Cyan
    & $Body
    if ($LASTEXITCODE -ne 0) {
        $script:stepResults += [ordered]@{ step = $Name; key = $StepKey; status = 'FAILED' }
        throw ("Step failed: {0}" -f $Name)
    }
    $script:stepResults += [ordered]@{ step = $Name; key = $StepKey; status = 'PASSED' }
    $script:progressState[$StepKey] = $true
    Save-ProgressState -Path $progressPath -State $script:progressState
    Write-Host ("PASS: {0}" -f $Name) -ForegroundColor Green
}

$failed = $false

try {
    Invoke-Step -StepKey 'render_apply_verify' -Name '1) renderer apply/verify' -Body {
        ./py.ps1 -m formal.python.tools.render_state_core_mirrors --apply-mirrors --verify-mirrors
    }

    Invoke-Step -StepKey 'state_core_integrity' -Name '2) state-core integrity gate' -Body {
        ./py.ps1 -m pytest formal/python/tests/test_state_core_generation_integrity_gate.py -q
    }

    Invoke-Step -StepKey 'compression_yield' -Name '3) compression/yield gate' -Body {
        ./py.ps1 -m pytest formal/python/tests/test_state_core_compression_yield_gate.py -q
    }

    Invoke-Step -StepKey 'full_governance_suite' -Name '4) full governance suite' -Body {
        pwsh -NoProfile -ExecutionPolicy Bypass -File ./governance_suite.ps1
    }

    if (Test-Path $progressPath) {
        Remove-Item $progressPath -Force
    }

    Write-Host "`nCheckpoint ladder complete: all four steps are green." -ForegroundColor Green
}
catch {
    $failed = $true
    Write-Host "`nCheckpoint ladder failed." -ForegroundColor Red
    Write-Host $_.Exception.Message -ForegroundColor Red
}
finally {
    # Generated artifacts may change during verification; restore them to keep a clean tree.
    $existing = @()
    foreach ($path in $generatedOutputs) {
        if (Test-Path $path) {
            $existing += $path
        }
    }
    if ($existing.Count -gt 0) {
        git restore -- $existing
    }

    Write-Host "`nPost-run git status:" -ForegroundColor Yellow
    $postRunStatus = @(Get-GitStatusSnapshot)

    $statusOutput = $postRunStatus
    $cleanTree = ($postRunStatus.Count -eq 0)

    if ($postRunStatus.Count -eq 0) {
        Write-Host "(clean)" -ForegroundColor Green
    }
    else {
        $postRunStatus | ForEach-Object { Write-Host $_ }
    }

    $newDrift = @(
        Compare-Object -ReferenceObject $preRunStatus -DifferenceObject $postRunStatus |
        Where-Object { $_.SideIndicator -eq '=>' } |
        Select-Object -ExpandProperty InputObject |
        Sort-Object
    )
    if ($newDrift.Count -gt 0) {
        Write-Host "`nCheckpoint ladder post-run hygiene failed: new working-tree drift detected relative to pre-run baseline." -ForegroundColor Red
        $newDrift | ForEach-Object { Write-Host ("  drift: {0}" -f $_) -ForegroundColor Red }
        $failed = $true
    }
    else {
        Write-Host "`nCheckpoint ladder hygiene check passed: no new drift relative to pre-run baseline." -ForegroundColor Green
    }

    Write-AcceptanceSummary -Path $summaryPath -StepResults $stepResults -Failed $failed -CleanTree $cleanTree -StatusOutput $statusOutput

    Pop-Location
}

if ($failed) {
    exit 1
}

exit 0
