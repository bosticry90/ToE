$ErrorActionPreference = 'Stop'

$repoRoot = Split-Path -Parent $MyInvocation.MyCommand.Path
Push-Location $repoRoot

$generatedOutputs = @(
    'formal/output/state_core_compression_yield_report_v0.json',
    'formal/output/state_core_generated/state_core_tracker_snippet_v0.md',
    'formal/output/state_core_generated/state_core_ws10_snippet_v0.md'
)

function Invoke-Step {
    param(
        [Parameter(Mandatory = $true)] [string]$Name,
        [Parameter(Mandatory = $true)] [scriptblock]$Body
    )

    Write-Host ("`n==> {0}" -f $Name) -ForegroundColor Cyan
    & $Body
    if ($LASTEXITCODE -ne 0) {
        throw ("Step failed: {0}" -f $Name)
    }
    Write-Host ("PASS: {0}" -f $Name) -ForegroundColor Green
}

$failed = $false

try {
    Invoke-Step -Name '1) renderer apply/verify' -Body {
        ./py.ps1 -m formal.python.tools.render_state_core_mirrors --apply-mirrors --verify-mirrors
    }

    Invoke-Step -Name '2) state-core integrity gate' -Body {
        ./py.ps1 -m pytest formal/python/tests/test_state_core_generation_integrity_gate.py -q
    }

    Invoke-Step -Name '3) compression/yield gate' -Body {
        ./py.ps1 -m pytest formal/python/tests/test_state_core_compression_yield_gate.py -q
    }

    Invoke-Step -Name '4) full governance suite' -Body {
        pwsh -NoProfile -ExecutionPolicy Bypass -File ./governance_suite.ps1
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
    $statusOutput = @(git status --short)
    if ($statusOutput.Count -gt 0) {
        $statusOutput | ForEach-Object { Write-Host $_ }
        Write-Host "`nCheckpoint ladder post-run hygiene failed: working tree is not clean after generated-output restore." -ForegroundColor Red
        $failed = $true
    }
    else {
        Write-Host "(clean)" -ForegroundColor Green
    }

    Pop-Location
}

if ($failed) {
    exit 1
}

exit 0
