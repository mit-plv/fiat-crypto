# Get the short version of coqc
$COQC_VERSION_SHORT = & opam exec -- coqc --print-version 2>$null | Select-Object -First 1

# Get the full version of coqc, replace new lines with commas, and remove trailing comma
$COQC_VERSION = & opam exec -- coqc --version 2>$null | ForEach-Object { $_ -join ',' } | ForEach-Object { $_ -replace ',$', '' }

# Run coqtop and capture both stdout and stderr
$COQTOP_VERSION = "" | & opam exec -- coqtop 2>$null

# Check if GITHUB_STEP_SUMMARY and COQC_VERSION are not empty
if (![string]::IsNullOrEmpty($env:GITHUB_STEP_SUMMARY) -and ![string]::IsNullOrEmpty($COQC_VERSION)) {
    # Append details to GITHUB_STEP_SUMMARY
    "<details><summary>$COQC_VERSION</summary>" | Out-File -FilePath $env:GITHUB_STEP_SUMMARY -Append
    "``````" | Out-File -FilePath $env:GITHUB_STEP_SUMMARY -Append
    $COQTOP_VERSION | Out-File -FilePath $env:GITHUB_STEP_SUMMARY -Append
    "``````" | Out-File -FilePath $env:GITHUB_STEP_SUMMARY -Append
    "</details>" | Out-File -FilePath $env:GITHUB_STEP_SUMMARY -Append
}