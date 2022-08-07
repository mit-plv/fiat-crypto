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

if [ ! -z "$(git diff)" ]; then
    git submodule foreach --recursive git diff
    git submodule foreach --recursive git status
    git diff
    if [ -z "${ALLOW_DIFF}" ] || [ "${ALLOW_DIFF}" == "0" ]; then
        exit 1
    fi
fi
