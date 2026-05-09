$ValidationTimeoutExitCode = 124

function Format-ValidationCommand {
  param(
    [Parameter(Mandatory = $true)][string]$FilePath,
    [string[]]$ArgumentList = @()
  )

  $parts = @($FilePath) + $ArgumentList
  return ($parts | ForEach-Object {
    if ($_ -match '\s') {
      "'" + ($_ -replace "'", "''") + "'"
    } else {
      $_
    }
  }) -join ' '
}

function ConvertTo-ValidationProcessArgument {
  param(
    [Parameter(Mandatory = $true)][AllowEmptyString()][string]$Argument
  )

  if ($Argument.Length -eq 0) {
    return '""'
  }
  if ($Argument -notmatch '[\s"]') {
    return $Argument
  }

  $escaped = $Argument.Replace('"', '\"')
  return '"' + $escaped + '"'
}

function Get-ValidationProcessTree {
  param(
    [Parameter(Mandatory = $true)][int]$RootProcessId
  )

  $allProcesses = @(Get-CimInstance Win32_Process)
  $childrenByParent = @{}

  foreach ($process in $allProcesses) {
    $parentId = [int]$process.ParentProcessId
    if (-not $childrenByParent.ContainsKey($parentId)) {
      $childrenByParent[$parentId] = @()
    }
    $childrenByParent[$parentId] += $process
  }

  $descendants = @()
  $stack = New-Object System.Collections.Stack
  $stack.Push($RootProcessId)

  while ($stack.Count -gt 0) {
    $parentId = [int]$stack.Pop()
    if (-not $childrenByParent.ContainsKey($parentId)) {
      continue
    }

    foreach ($child in $childrenByParent[$parentId]) {
      $descendants += $child
      $stack.Push([int]$child.ProcessId)
    }
  }

  return $descendants
}

function Write-ValidationLogFile {
  param(
    [Parameter(Mandatory = $true)][string]$Path
  )

  if ((Test-Path -LiteralPath $Path) -and ((Get-Item -LiteralPath $Path).Length -gt 0)) {
    Get-Content -LiteralPath $Path -Raw | Write-Host
  }
}

function Stop-ValidationProcessTree {
  param(
    [Parameter(Mandatory = $true)][int]$RootProcessId,
    [string[]]$KillProcessNames = @()
  )

  $descendants = @(Get-ValidationProcessTree -RootProcessId $RootProcessId)
  [array]::Reverse($descendants)

  if ($KillProcessNames.Count -gt 0) {
    Write-Host "validation_runner.kill_labels names=$($KillProcessNames -join ',')" -ForegroundColor Yellow
  }

  foreach ($process in $descendants) {
    Write-Host "validation_runner.kill descendant pid=$($process.ProcessId) name=$($process.Name)" -ForegroundColor Yellow
    Stop-Process -Id $process.ProcessId -Force -ErrorAction SilentlyContinue
  }

  Write-Host "validation_runner.kill root pid=$RootProcessId" -ForegroundColor Yellow
  Stop-Process -Id $RootProcessId -Force -ErrorAction SilentlyContinue
}

function Invoke-ValidationCommand {
  param(
    [Parameter(Mandatory = $true)][string]$Label,
    [Parameter(Mandatory = $true)][string]$FilePath,
    [string[]]$ArgumentList = @(),
    [string]$WorkingDirectory = (Get-Location).Path,
    [Parameter(Mandatory = $true)][int]$TimeoutSeconds,
    [string[]]$KillProcessNames = @(),
    [switch]$DryRun
  )

  if ($TimeoutSeconds -le 0) {
    throw "TimeoutSeconds must be positive."
  }
  if (-not (Test-Path -LiteralPath $WorkingDirectory -PathType Container)) {
    throw "Working directory does not exist: $WorkingDirectory"
  }

  $commandText = Format-ValidationCommand -FilePath $FilePath -ArgumentList $ArgumentList

  if ($DryRun) {
    Write-Host "validation_runner.DRY_RUN label=$Label cwd=$WorkingDirectory timeout_seconds=$TimeoutSeconds"
    Write-Host "validation_runner.command $commandText"
    return 0
  }

  $runId = [Guid]::NewGuid().ToString("N")
  $safeLabel = $Label -replace '[^A-Za-z0-9_.-]', '_'
  $tempRoot = [System.IO.Path]::GetTempPath()
  $stdoutPath = Join-Path $tempRoot "toe_validation_${safeLabel}_${runId}.stdout.log"
  $stderrPath = Join-Path $tempRoot "toe_validation_${safeLabel}_${runId}.stderr.log"
  $startArgumentList = ($ArgumentList | ForEach-Object { ConvertTo-ValidationProcessArgument -Argument $_ }) -join ' '
  $stopwatch = [System.Diagnostics.Stopwatch]::StartNew()

  Write-Host "validation_runner.start label=$Label cwd=$WorkingDirectory timeout_seconds=$TimeoutSeconds"
  Write-Host "validation_runner.command $commandText"

  try {
    $process = Start-Process `
      -FilePath $FilePath `
      -ArgumentList $startArgumentList `
      -WorkingDirectory $WorkingDirectory `
      -RedirectStandardOutput $stdoutPath `
      -RedirectStandardError $stderrPath `
      -NoNewWindow `
      -PassThru

    $timedOut = $false
    try {
      Wait-Process -Id $process.Id -Timeout $TimeoutSeconds -ErrorAction Stop
    } catch {
      $stillRunning = Get-Process -Id $process.Id -ErrorAction SilentlyContinue
      if ($stillRunning) {
        $timedOut = $true
      }
    }

    if ($timedOut) {
      Stop-ValidationProcessTree -RootProcessId $process.Id -KillProcessNames $KillProcessNames
      Start-Sleep -Milliseconds 250
      Write-ValidationLogFile -Path $stdoutPath
      Write-ValidationLogFile -Path $stderrPath
      $elapsedSeconds = [Math]::Round($stopwatch.Elapsed.TotalSeconds, 3)
      Write-Host "validation_runner.timeout label=$Label exit_code=$ValidationTimeoutExitCode elapsed_seconds=$elapsedSeconds" -ForegroundColor Red
      return $ValidationTimeoutExitCode
    }

    $process.Refresh()
    Write-ValidationLogFile -Path $stdoutPath
    Write-ValidationLogFile -Path $stderrPath
    $elapsedSeconds = [Math]::Round($stopwatch.Elapsed.TotalSeconds, 3)
    Write-Host "validation_runner.finished label=$Label exit_code=$($process.ExitCode) elapsed_seconds=$elapsedSeconds"
    return [int]$process.ExitCode
  } finally {
    $stopwatch.Stop()
    Remove-Item -LiteralPath $stdoutPath, $stderrPath -Force -ErrorAction SilentlyContinue
  }
}
