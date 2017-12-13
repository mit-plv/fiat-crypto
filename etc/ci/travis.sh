#!/usr/bin/env bash

set -x

CACHE_DIR="$HOME/.cache/vos"
PREV_ARCHIVE="${CACHE_DIR}/vos-${COQ_VERSION}-${PREV}.tar.gz"
CUR_ARCHIVE="${CACHE_DIR}/vos-${COQ_VERSION}-${CUR}.tar.gz"

tar -xzf "${PREV_ARCHIVE}" || true
mkdir -p "${CACHE_DIR}"
shift

make "$@" -j2 TIMED=1 2>&1 | tee -a time-of-build.log
python "./etc/coq-scripts/timing/make-one-time-file.py" "time-of-build.log" "time-of-build-pretty.log" || exit $?
rm -f "${CUR_ARCHIVE}"
tar -czf "${CUR_ARCHIVE}" time-of-build.log src Bedrock coqprime

cat time-of-build-pretty.log
make "$@" -j2 TIMED=1 || exit $?
