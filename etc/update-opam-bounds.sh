#!/usr/bin/env bash

set -euo pipefail

QUIET=0
for arg in "$@"; do
    case "$arg" in
        -q|--quiet) QUIET=1 ;;
    esac
done

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$DIR/.."

# Fetch tags for all submodules so git describe can find them
git submodule foreach --recursive --quiet 'git fetch --tags 2>/dev/null || true'

# Special-case mappings for submodules without .opam files
declare -A SPECIAL_MAPPINGS=(
    ["rupicola"]="coq-rupicola"
    ["bedrock2"]="coq-bedrock2-compiler"
)

declare -A PACKAGE_VERSIONS

while IFS=$'\t' read -r displaypath tag; do
    version="${tag#v}"
    if [ "$QUIET" -eq 0 ]; then
        echo "Submodule $displaypath: tag=$tag, version=$version"
    fi

    found_opam=0
    for opam_file in "$displaypath"/*.opam; do
        if [ -f "$opam_file" ]; then
            name="$(basename "$opam_file" .opam)"
            PACKAGE_VERSIONS["$name"]="$version"
            found_opam=1
        fi
    done

    # Check special mappings if no opam file found
    if [ "$found_opam" -eq 0 ]; then
        submodule_name="$(basename "$displaypath")"
        if [ -n "${SPECIAL_MAPPINGS[$submodule_name]+x}" ]; then
            PACKAGE_VERSIONS["${SPECIAL_MAPPINGS[$submodule_name]}"]="$version"
        fi
    fi
done < <(git submodule foreach --recursive --quiet 'tag=$(git describe --tags --abbrev=0 2>/dev/null || true); if [ -n "$tag" ]; then printf "%s\t%s\n" "$displaypath" "$tag"; fi')

if [ "$QUIET" -eq 0 ]; then
    echo ""
    echo "Package version mapping:"
    for name in "${!PACKAGE_VERSIONS[@]}"; do
        echo "  $name -> ${PACKAGE_VERSIONS[$name]}"
    done
    echo ""
fi

# Update top-level .opam files
for name in "${!PACKAGE_VERSIONS[@]}"; do
    ver="${PACKAGE_VERSIONS[$name]}"

    for opam_file in *.opam; do
        [ -f "$opam_file" ] || continue

        # Skip files that don't reference this package
        if ! grep -q "\"$name\"" "$opam_file"; then
            continue
        fi

        perl -i -pe '
            BEGIN { $pkg = shift @ARGV; $ver = shift @ARGV; }
            # Pattern 1: "$pkg" {= "VER" | = "dev"}
            s/("\Q$pkg\E" \s* \{ \s* = \s* ") [^"]* (" \s* \| \s* = \s* "dev" \s* \})/$1$ver$2/x;
            # Pattern 2: "$pkg" {( >= "LOW" & <= "VER" ) | = "dev"}
            s/("\Q$pkg\E" \s* \{ \s* \( \s* >= \s* "[^"]*" \s* & \s* <= \s* ") [^"]* (" \s* \) \s* \| \s* = \s* "dev" \s* \})/$1$ver$2/x;
        ' -- "$name" "$ver" "$opam_file"
    done
done
