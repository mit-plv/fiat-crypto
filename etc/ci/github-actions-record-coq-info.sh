#!/bin/sh

outfile="${1:-$GITHUB_STEP_SUMMARY}"

# summarize rocq version to make it easier to read
COQC_VERSION_SHORT="$(rocq --print-version 2>/dev/null | cut -d " " -f 1)"
COQC_VERSION="$(rocq --version 2>/dev/null | tr '\n' ',' | sed 's/,$//g')"
COQTOP_VERSION="$(rocq top </dev/null 2>&1)"
if [ ! -z "$outfile" ]; then
    if [ ! -z "$COQC_VERSION" ]; then
        echo "Writing $COQC_VERSION to $outfile..."
        printf '%s\n\n' "<details><summary>${COQC_VERSION}</summary>" >> "$outfile"
        printf '%s\n' '```' >> "$outfile"
        printf '%s\n' "${COQTOP_VERSION}" >> "$outfile"
        printf '%s\n%s\n' '```' '</details>' >> "$outfile"
    else
        echo "Not writing missing rocq version to $outfile"
    fi
else
    echo "GITHUB_STEP_SUMMARY is unset"
fi
