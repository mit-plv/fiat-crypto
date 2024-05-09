#!/usr/bin/env bash

usage() {
    >&2 printf "%s FILENAME [DEFAULT_ARCH]\n" "$0"
}

fname="$1"
default="$2"
if [ -z "$fname" ] || [ "$fname" = "-h" ] || [ "$fname" = "--help" ]; then
    usage
fi
if [ -z "$fname" ]; then
    exit 1
fi

if [ ! -z "${SHELL}" ]; then
    run() {
        "${SHELL}" -c "$*" || true
    }
else
    run() {
        /bin/sh -c "$*" || true
    }
fi

if [ ! -z "$CI" ]; then
    group() {
        echo "::group::$*"
        run "$@"
        echo "::endgroup::"
    }
else
    group() { run "$@"; }
fi

default_arch() {
    if [ -z "$default" ]; then
        printf "%s\n" "$1" | awk '{print $NF}'
    else
        printf "%s\n" "$default"
    fi
    >&2 echo "::warning::Unknown architecture ${file_info} (using ${arch})"
}


>&2 group file "$fname"
>&2 group otool -L "$fname" || true
>&2 group lipo -info "$fname" || true
file_info="$(file "$fname" 2>&1)"

case "${file_info}" in
    *"Mach-O universal"*)
        arches=($(printf '%s' "${file_info}" | grep -o 'Mach-O universal.*' | grep -o '\[[^]:]*' | sed 's/^\[//g'))
        if [ "${#arches[@]}" -eq 1 ]; then
            arch="${arches[0]}"
        elif [ "${#arches[@]}" -gt 1 ]; then
            arch="universal"
            if [[ " ${arches[*]} " =~ " arm64 " ]] && [[ " ${arches[*]} " =~ " x86_64 " ]]; then
                :
            else
                for cur_arch in "${arches[@]}"; do
                    arch="${arch}_${cur_arch}"
                done
            fi
        else
            arch="$(default_arch "${file_info}")"
        fi
        ;;
    *x86_64*|*x86-64*)
        arch=x86_64
        ;;
    *arm64*)
        arch=arm64
        ;;
    *)
        arch="$(default_arch "${file_info}")"
        ;;
esac

printf "%s\n" "$arch"
