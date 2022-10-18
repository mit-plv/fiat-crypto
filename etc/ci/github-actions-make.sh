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

make_one_time_file_real=""
unameOut="$(uname -s)"
if [[ "${unameOut}" == CYGWIN* ]]; then
    # time on cygwin doesn't report accurate user times, so we use real times
    make_one_time_file_real="--real"
fi

echo "::add-matcher::.github/make.json"

rm -f finished.ok
(make "$@" ${OUTPUT_SYNC} TIMED=1 TIMING=1 "${reportify}" 2>&1 && touch finished.ok) | tee -a time-of-build.log
python "./etc/coq-scripts/timing/make-one-time-file.py" ${make_one_time_file_real} "time-of-build.log" "time-of-build-pretty.log" || exit $?

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
    diff_msg="$(git diff 2>&1; git submodule foreach --recursive git diff 2>&1; git submodule foreach --recursive git status 2>&1)"
    diff_msg="$(printf "Non-empty-diff:\n%s\n" "${diff_msg}" | sed -z 's/\n/%0A/g')"
    if [ "${ALLOW_DIFF}" != "1" ]; then
        printf "::error::%s" "${diff_msg}"
        exit 1
    else
        printf "::warning::%s" "${diff_msg}"
    fi
fi
