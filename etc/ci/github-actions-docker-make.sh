#!/usr/bin/env bash

set -x

cd -- "$( dirname -- "${BASH_SOURCE[0]}" )"
cd ../..

if [ -z "${EXTRA_PACKAGES+x}" ]; then
    EXTRA_PACKAGES=""
fi

sudo chmod -R a+rw .
echo '::group::install general dependencies'
sudo apt-get update -y
sudo apt-get install -y python python3 ${EXTRA_PACKAGES}
eval $(opam env)
echo '::endgroup::'
echo '::remove-matcher owner=coq-problem-matcher::'
etc/ci/describe-system-config.sh
ulimit -S -s 32768
etc/ci/github-actions-make.sh "$@"
