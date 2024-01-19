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

>&2 group file "$fname"
>&2 group otool -L "$fname" || true
>&2 group lipo -info "$fname" || true
file_info="$(file "$fname" 2>&1)"
case "${file_info}" in
    *x86_64*|*x86-64*)
        arch=x86_64
        ;;
    *)
        if [ -z "$default" ]; then
            arch="$(printf "%s\n" "${file_info}" | awk '{print $NF}')"
        else
            arch="$default"
        fi
        >&2 echo "::warning::Unknown architecture ${file_info} (using ${arch})"
        ;;
esac

printf "%s\n" "$arch"
