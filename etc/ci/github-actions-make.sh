#!/usr/bin/env bash

set -x

if [ ! -z "${TOUCH}" ]; then
    make -j2 -t ${TOUCH} || exit $?
fi

rm -f finished.ok
(make "$@" TIMED=1 2>&1 && touch finished.ok) | tee -a time-of-build.log
python "./etc/coq-scripts/timing/make-one-time-file.py" "time-of-build.log" "time-of-build-pretty.log" || exit $?

git update-index --assume-unchanged _CoqProject
git status
git diff

cat time-of-build-pretty.log
make "$@" TIMED=1 || exit $?

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
