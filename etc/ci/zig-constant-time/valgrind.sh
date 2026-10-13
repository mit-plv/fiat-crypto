#!/usr/bin/env bash
# Run every public function of each fiat-zig/src/*.zig file on secret inputs
# under Valgrind (see valgrind.zig), for the CPU features and optimization
# modes below.  With --self-test, check bad.zig instead and require that its
# selectArray and collatzSteps functions are reported.
#
# Usage: valgrind.sh [--self-test]
# Environment: ZIG (default zig), VALGRIND (default valgrind), CPUS.

set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(cd "${here}/../../.." && pwd)"
zig="${ZIG:-zig}"
valgrind="${VALGRIND:-valgrind}"
case "$(uname -m)" in
    x86_64) default_cpus="baseline x86_64_v3" ;;
    *) default_cpus="baseline" ;;
esac
read -r -a cpus <<< "${CPUS:-${default_cpus}}"
modes=(ReleaseFast ReleaseSmall)

self_test=0
if [ "${1:-}" = "--self-test" ]; then
    self_test=1
    files=("${here}/bad.zig")
else
    files=()
    for f in "${repo}"/fiat-zig/src/*.zig; do
        [ "$(basename "$f")" = main.zig ] || files+=("$f")
    done
fi

# Left in place for inspection.
work="$(mktemp -d)"
echo "building in ${work}"

failures=0
for f in "${files[@]}"; do
    for cpu in "${cpus[@]}"; do
        for mode in "${modes[@]}"; do
            name="$(basename "$f" .zig)-${cpu}-${mode}"
            "$zig" build-exe -O "$mode" -mcpu="$cpu" -fvalgrind -fno-strip \
                --dep fiat -Mroot="${here}/valgrind.zig" -Mfiat="$f" \
                -femit-bin="${work}/${name}" --cache-dir "${work}/cache" \
                --global-cache-dir "${work}/cache"
            status=0
            "$valgrind" -q --error-exitcode=1 "${work}/${name}" > "${work}/${name}.log" 2>&1 || status=$?
            where="${f#"${repo}"/} (${cpu}, ${mode})"
            if [ "$self_test" = 1 ]; then
                for fn in selectArray collatzSteps; do
                    if ! grep -q "bad\.${fn} " "${work}/${name}.log"; then
                        echo "error: ${where}: bad.${fn} not reported"
                        failures=$((failures + 1))
                    fi
                done
            elif [ "$status" != 0 ]; then
                echo "error: ${where}:"
                cat "${work}/${name}.log"
                failures=$((failures + 1))
            fi
        done
    done
done
echo "${#files[@]} files checked, ${failures} failures"
[ "$failures" = 0 ]
