#!/usr/bin/env bash

set -x

if [ ! -z "${TOUCH}" ]; then
    make -j2 -t ${TOUCH} || exit $?
fi

OUTPUT_SYNC=""
if make -h 2>/dev/null | grep -q output-sync; then
    OUTPUT_SYNC="--output-sync"
else
    echo "WARNING: make does not support --output-sync"
fi

reportify=" --errors"

if [ "$1" == "--warnings" ]; then
    reportify+=" $1"
    shift
fi
if [ ! -z "${reportify}" ]; then
    reportify="COQC='$(pwd)/etc/coq-scripts/github/reportify-coq.sh'${reportify} ${COQBIN}coqc"
fi

rm -f finished.ok
(make "$@" ${OUTPUT_SYNC} TIMED=1 TIMING=1 "${reportify}" 2>&1 && touch finished.ok) | tee -a time-of-build.log
python "./etc/coq-scripts/timing/make-one-time-file.py" "time-of-build.log" "time-of-build-pretty.log" || exit $?

git status
git diff

cat time-of-build-pretty.log
if [ ! -f finished.ok ]; then
    make "$@" ${OUTPUT_SYNC} TIMED=1 TIMING=1 VERBOSE=1 || exit $?
fi

unameOut="$(uname -s)"
if [[ "${unameOut}" == CYGWIN* ]]; then
    # generated build outputs have a different path, so we fix up the paths
    git grep --name-only 'D:\\a\\fiat-crypto\\fiat-crypto.src.ExtractionOCaml.' | xargs sed s',D:\\a\\fiat-crypto\\fiat-crypto.src.ExtractionOCaml.\(.*\).exe,src/ExtractionOCaml/\1,g' -i
fi

if [ ! -z "$(git diff)" ]; then
    git submodule foreach --recursive git diff
    git submodule foreach --recursive git status
    git diff
    if [ "${ALLOW_DIFF}" != "1" ]; then
        exit 1
    fi
fi
