#!/bin/sh

# summarize coqc version to make it easier to read
COQC_VERSION_SHORT="$(coqc --print-version 2>/dev/null | cut -d " " -f 1)"
COQC_VERSION="$(coqc --version 2>/dev/null | tr '\n' ',' | sed 's/,$//g')"
COQTOP_VERSION="$(true | coqtop 2>&1)"
if [ ! -z "$GITHUB_STEP_SUMMARY" ] && [ ! -z "$COQC_VERSION" ]; then
    printf '%s\n\n' "<details><summary>${COQC_VERSION}</summary>" >> "$GITHUB_STEP_SUMMARY"
    printf '%s\n' '```' >> "$GITHUB_STEP_SUMMARY"
    printf '%s\n' "${COQTOP_VERSION} >> "$GITHUB_STEP_SUMMARY"
    printf '%s\n%s\n' '```' '</details>' >> "$GITHUB_STEP_SUMMARY"
fi