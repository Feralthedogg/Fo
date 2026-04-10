param(
    [string]$Version = $env:FO_VERSION,
    [string]$Repo = $(if ($env:FO_REPO) { $env:FO_REPO } else { "Feralthedogg/Fo" })
)

$ErrorActionPreference = "Stop"

if (-not $Version) {
    $latest = Invoke-RestMethod -Uri "https://api.github.com/repos/$Repo/releases/latest"
    $Version = $latest.tag_name
}

$asset = "fo-$Version-windows-amd64.msi"
$url = "https://github.com/$Repo/releases/download/$Version/$asset"
$tmp = Join-Path $env:TEMP $asset

Invoke-WebRequest -Uri $url -OutFile $tmp
$process = Start-Process msiexec.exe -ArgumentList @("/i", $tmp, "/passive", "/norestart") -Wait -PassThru
if ($process.ExitCode -ne 0) {
    throw "msiexec failed with exit code $($process.ExitCode)"
}

Write-Host "Installed Fo from $asset"
Write-Host "Open a new terminal session to pick up PATH changes."
