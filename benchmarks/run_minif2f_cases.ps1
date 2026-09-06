[CmdletBinding()]
param(
    [Parameter(Mandatory = $true)]
    [string] $Source,

    [Parameter(Mandatory = $true)]
    [string] $Output,

    [int] $From = 1,
    [int] $To = [int]::MaxValue,
    [int] $BudgetSec = 15,
    [int] $HardTimeoutSec = 75,
    [switch] $Resume
)

$ErrorActionPreference = 'Stop'

if ($From -lt 1) {
    throw '-From is one-based and must be at least 1.'
}
if ($To -lt $From) {
    throw '-To must be greater than or equal to -From.'
}
if ($BudgetSec -lt 1 -or $HardTimeoutSec -le $BudgetSec) {
    throw '-HardTimeoutSec must be greater than -BudgetSec, and both must be positive.'
}

$integrationRoot = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..\integration\mathlib'))
$sourcePath = [IO.Path]::GetFullPath($Source)
$outputPath = [IO.Path]::GetFullPath($Output)
if ([string]::IsNullOrWhiteSpace($env:LEAN_PATH)) {
    throw 'Run this script through `lake env powershell -File ...` so each case can invoke lean.exe directly.'
}
$leanPath = @(Get-Command lean -CommandType Application)[0].Source
if (-not [IO.File]::Exists($sourcePath)) {
    throw "Dataset source does not exist: $sourcePath"
}

$sourceText = [IO.File]::ReadAllText($sourcePath, [Text.Encoding]::UTF8)
$marker = '#vialean_dataset_eval'
$firstMarker = $sourceText.IndexOf($marker, [StringComparison]::Ordinal)
if ($firstMarker -lt 0) {
    throw "No $marker commands found in $sourcePath"
}

$header = $sourceText.Substring(0, $firstMarker)
$casePattern = '(?ms)^#vialean_dataset_eval\b.*?(?=^#vialean_dataset_eval\b|\z)'
$matches = [Text.RegularExpressions.Regex]::Matches($sourceText, $casePattern)
if ($matches.Count -eq 0) {
    throw "No complete $marker commands found in $sourcePath"
}

$upper = [Math]::Min($To, $matches.Count)
$workRoot = Join-Path $integrationRoot '.lake\vialean-case-runner'
[IO.Directory]::CreateDirectory($workRoot) | Out-Null
[IO.Directory]::CreateDirectory([IO.Path]::GetDirectoryName($outputPath)) | Out-Null

$completed = [Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
if ($Resume -and [IO.File]::Exists($outputPath)) {
    foreach ($line in [IO.File]::ReadLines($outputPath, [Text.Encoding]::UTF8)) {
        try {
            $record = $line | ConvertFrom-Json
            if ($null -ne $record.case) {
                [void] $completed.Add([string] $record.case)
            }
        } catch {
            # Keep valid earlier records even if a manually interrupted run left noise.
        }
    }
} elseif ([IO.File]::Exists($outputPath)) {
    [IO.File]::WriteAllText($outputPath, '', [Text.UTF8Encoding]::new($false))
}

function Add-ResultLine([string] $Line) {
    [IO.File]::AppendAllText($outputPath, $Line.Trim() + [Environment]::NewLine,
        [Text.UTF8Encoding]::new($false))
}

for ($index = $From; $index -le $upper; $index++) {
    $command = $matches[$index - 1].Value.TrimEnd() + [Environment]::NewLine
    $nameMatch = [Text.RegularExpressions.Regex]::Match(
        $command,
        '^#vialean_dataset_eval\s+"[^"]+"\s+"[^"]+"\s+"([^"]+)"')
    if (-not $nameMatch.Success) {
        throw "Could not parse case name at index $index"
    }
    $caseName = $nameMatch.Groups[1].Value
    if ($completed.Contains($caseName)) {
        Write-Host ("[{0}/{1}] skip {2}" -f $index, $matches.Count, $caseName)
        continue
    }

    $caseFile = Join-Path $workRoot ("Case{0:D3}.lean" -f $index)
    $stdoutFile = Join-Path $workRoot ("Case{0:D3}.stdout" -f $index)
    $stderrFile = Join-Path $workRoot ("Case{0:D3}.stderr" -f $index)
    $caseText = $header + $command.Replace('(timeoutSec := 15)', "(timeoutSec := $BudgetSec)")
    [IO.File]::WriteAllText($caseFile, $caseText, [Text.UTF8Encoding]::new($false))

    $start = [Diagnostics.ProcessStartInfo]::new()
    $start.FileName = $leanPath
    $start.WorkingDirectory = $integrationRoot
    $start.UseShellExecute = $false
    $start.CreateNoWindow = $true
    $start.RedirectStandardOutput = $true
    $start.RedirectStandardError = $true
    $escapedCaseFile = $caseFile.Replace('"', '\"')
    $start.Arguments = "-s 65536 `"$escapedCaseFile`""

    Write-Host ("[{0}/{1}] run  {2}" -f $index, $matches.Count, $caseName)
    $stopwatch = [Diagnostics.Stopwatch]::StartNew()
    $process = [Diagnostics.Process]::new()
    $process.StartInfo = $start
    [void] $process.Start()
    $stdoutTask = $process.StandardOutput.ReadToEndAsync()
    $stderrTask = $process.StandardError.ReadToEndAsync()
    $finished = $process.WaitForExit($HardTimeoutSec * 1000)
    if (-not $finished) {
        try { $process.Kill() } catch { }
    }
    $process.WaitForExit()
    $stdout = $stdoutTask.GetAwaiter().GetResult()
    $stderr = $stderrTask.GetAwaiter().GetResult()
    $stopwatch.Stop()
    [IO.File]::WriteAllText($stdoutFile, $stdout, [Text.UTF8Encoding]::new($false))
    [IO.File]::WriteAllText($stderrFile, $stderr, [Text.UTF8Encoding]::new($false))

    $jsonLine = $stdout -split '\r?\n' |
        Where-Object { $_.TrimStart().StartsWith('{') } |
        Select-Object -Last 1
    if ($finished -and $null -ne $jsonLine) {
        Add-ResultLine $jsonLine
        $parsed = $jsonLine | ConvertFrom-Json
        Write-Host ("[{0}/{1}] {2,-6} {3} ({4} ms)" -f
            $index, $matches.Count, $(if ($parsed.solved) { 'solved' } else { 'failed' }),
            $caseName, $parsed.elapsed_ms)
        continue
    }

    $failure = [ordered]@{
        schema = 'vialean.dataset.v1'
        dataset = 'miniF2F'
        split = 'test'
        case = $caseName
        solved = $false
        elapsed_ms = [int64] $stopwatch.ElapsedMilliseconds
        direct_attempts = 0
        proposal_attempts = 0
        model_calls = 0
        replan_count = 0
        atlas_nodes = 0
        atlas_transitions = 0
        atlas_meta_ops = 0
        search_exceptions = 1
        internal_error = $true
        attempts = 1
        profile = $(if ($finished) { 'process-error' } else { 'process-timeout' })
        budget_sec = $BudgetSec
    } | ConvertTo-Json -Compress
    Add-ResultLine $failure
    Write-Host ("[{0}/{1}] {2,-7} {3} ({4} ms)" -f
        $index, $matches.Count, $(if ($finished) { 'error' } else { 'timeout' }),
        $caseName, $stopwatch.ElapsedMilliseconds)
}

$records = @([IO.File]::ReadLines($outputPath, [Text.Encoding]::UTF8) |
    ForEach-Object { $_ | ConvertFrom-Json })
$solved = @($records | Where-Object solved).Count
$timeouts = @($records | Where-Object { $_.profile -eq 'process-timeout' }).Count
$errors = @($records | Where-Object internal_error).Count
$rate = if ($records.Count -eq 0) { 0.0 } else { 100.0 * $solved / $records.Count }
Write-Host ("summary: {0}/{1} solved ({2:N1}%), hard timeouts={3}, internal errors={4}" -f
    $solved, $records.Count, $rate, $timeouts, $errors)
