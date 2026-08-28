#!/bin/sh
# Benchmark the equivalence checker on all test-avx programs.
# Outputs a TSV with: name, category, instructions, time(s), result
#
# Usage: ./test-avx/bench-equiv-check.sh [RUNS]
#   RUNS: number of iterations per test for averaging (default: 3)

set -e

RUNS="${1:-3}"
MANIFEST="test-avx/test-manifest.tsv"
BINARY="src/ExtractionOCaml/unsaturated_solinas"

if [ ! -x "$BINARY" ]; then
    echo "ERROR: binary not built: $BINARY" >&2
    exit 1
fi

# Header
printf "name\tcategory\tinstructions\ttime_s\tresult\n"

while IFS='	' read -r name category binary curve_name bitwidth limbs prime operation asm_file extra_flags; do
    case "$name" in '#'*|'') continue ;; esac
    [ ! -f "$asm_file" ] && continue

    # Count instructions (non-blank, non-comment, non-directive lines starting with letter/whitespace+letter)
    instr_count=$(grep -cE '^\s*[a-z]' "$asm_file" 2>/dev/null | grep -v ':' || grep -cE '^\s+[a-z]' "$asm_file" 2>/dev/null || echo 0)

    # Time the check (average over RUNS)
    total_time=0
    result="PASS"
    for i in $(seq 1 "$RUNS"); do
        t0=$(python3 -c 'import time; print(time.time())')
        "$binary" --inline --static --use-value-barrier \
            "$curve_name" "$bitwidth" "$limbs" "$prime" "$operation" \
            $extra_flags \
            --hints-file "$asm_file" \
            -o /dev/null --output-asm /dev/null >/dev/null 2>&1 && rc=0 || rc=$?
        t1=$(python3 -c 'import time; print(time.time())')
        elapsed=$(python3 -c "print(${t1} - ${t0})")
        total_time=$(python3 -c "print(${total_time} + ${elapsed})")
        if [ $rc -ne 0 ]; then
            result="FAIL"
        fi
    done
    avg_time=$(python3 -c "print(round(${total_time} / ${RUNS}, 3))")

    printf "%s\t%s\t%s\t%s\t%s\n" "$name" "$category" "$instr_count" "$avg_time" "$result"
done < "$MANIFEST"
