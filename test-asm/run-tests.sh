#!/bin/sh
# Run equivalence check tests from the manifest.
# Usage: ./test-asm/run-tests.sh [-v] [-c CATEGORY] [-n NAME] [-m MANIFEST]

set -e

# Defaults
VERBOSE=0
QUIET=0
CATEGORY=""
NAME=""
MANIFEST="test-asm/test-manifest.tsv"

while [ $# -gt 0 ]; do
    case "$1" in
        -v) VERBOSE=1; shift ;;
        -q) QUIET=1; shift ;;
        -c) CATEGORY="$2"; shift 2 ;;
        -n) NAME="$2"; shift 2 ;;
        -m) MANIFEST="$2"; shift 2 ;;
        -h|--help)
            echo "Usage: $0 [-v] [-q] [-c CATEGORY] [-n NAME] [-m MANIFEST]"
            echo "  -v  Verbose: show checker output on failure"
            echo "  -q  Quiet: only show summary"
            echo "  -c  Filter by category"
            echo "  -n  Run only this named test"
            echo "  -m  Alternate manifest file"
            exit 0 ;;
        *) echo "Unknown option: $1" >&2; exit 2 ;;
    esac
done

# Must run from repo root
if [ ! -d src/ExtractionOCaml ]; then
    echo "ERROR: run from fiat-crypto repo root" >&2
    exit 2
fi

if [ ! -f "$MANIFEST" ]; then
    echo "ERROR: manifest not found: $MANIFEST" >&2
    exit 2
fi

# Counters
total=0
passed=0
failed=0
skipped=0

while IFS='	' read -r name category binary curve_name bitwidth limbs prime operation asm_file extra_flags; do
    # Skip comments and blank lines
    case "$name" in
        '#'*|'') continue ;;
    esac

    # Apply filters
    if [ -n "$CATEGORY" ] && [ "$category" != "$CATEGORY" ]; then
        continue
    fi
    if [ -n "$NAME" ] && [ "$name" != "$NAME" ]; then
        continue
    fi

    total=$((total + 1))

    # Check binary exists
    if [ ! -x "$binary" ]; then
        skipped=$((skipped + 1))
        [ "$QUIET" -eq 0 ] && printf "SKIP   %s (binary not built: %s)\n" "$name" "$binary"
        continue
    fi

    # Check asm file exists
    if [ ! -f "$asm_file" ]; then
        skipped=$((skipped + 1))
        [ "$QUIET" -eq 0 ] && printf "SKIP   %s (file missing: %s)\n" "$name" "$asm_file"
        continue
    fi

    # Build and run command
    output=$("$binary" --inline --static --use-value-barrier \
        "$curve_name" "$bitwidth" "$limbs" "$prime" "$operation" \
        $extra_flags \
        --hints-file "$asm_file" \
        -o /dev/null --output-asm /dev/null 2>&1) && rc=0 || rc=$?

    if [ $rc -eq 0 ]; then
        passed=$((passed + 1))
        [ "$QUIET" -eq 0 ] && printf "PASS   %s\n" "$name"
    else
        failed=$((failed + 1))
        [ "$QUIET" -eq 0 ] && printf "FAIL   %s\n" "$name"
        if [ "$VERBOSE" -eq 1 ]; then
            echo "--- output (last 80 lines) ---"
            echo "$output" | tail -80
            echo "--- end ---"
            echo "$output" > /tmp/test_output_${name}.txt
            echo "(full output saved to /tmp/test_output_${name}.txt)"
        fi
    fi
done < "$MANIFEST"

# Summary
echo "================================"
printf "Total: %d  Passed: %d  Failed: %d  Skipped: %d\n" "$total" "$passed" "$failed" "$skipped"
echo "================================"

if [ "$failed" -gt 0 ]; then
    exit 1
fi
exit 0
