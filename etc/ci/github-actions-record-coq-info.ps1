# Get the short version of rocq
$COQC_VERSION_SHORT = & opam exec -- rocq --print-version 2>$null | Select-Object -First 1

# Get the full version of rocq, replace new lines with commas, and remove trailing comma
$COQC_VERSION = & opam exec -- rocq --version 2>$null | ForEach-Object { $_ -join ',' } | ForEach-Object { $_ -replace ',$', '' }

# Run rocq top and capture both stdout and stderr
$COQTOP_VERSION = "" | & opam exec -- rocq top 2>$null

# Check if GITHUB_STEP_SUMMARY and COQC_VERSION are not empty
if (![string]::IsNullOrEmpty($env:GITHUB_STEP_SUMMARY) -and ![string]::IsNullOrEmpty($COQC_VERSION)) {
    # Append details to GITHUB_STEP_SUMMARY
    "<details><summary>$COQC_VERSION</summary>" | Out-File -FilePath $env:GITHUB_STEP_SUMMARY -Append
    "``````" | Out-File -FilePath $env:GITHUB_STEP_SUMMARY -Append
    $COQTOP_VERSION | Out-File -FilePath $env:GITHUB_STEP_SUMMARY -Append
    "``````" | Out-File -FilePath $env:GITHUB_STEP_SUMMARY -Append
    "</details>" | Out-File -FilePath $env:GITHUB_STEP_SUMMARY -Append
}