#!/usr/bin/env bash

set -x

cd -- "$( dirname -- "${BASH_SOURCE[0]}" )"
cd ../..

if [ -z "${EXTRA_PACKAGES+x}" ]; then
    EXTRA_PACKAGES=""
fi

sudo chmod -R a=u .
echo '::group::install general dependencies'
sudo apt-get update -y
sudo apt-get install -y python python3 bsdmainutils ${EXTRA_PACKAGES}
eval $(opam env)
echo '::endgroup::'
echo '::remove-matcher owner=coq-problem-matcher::'
etc/ci/describe-system-config.sh
etc/ci/github-actions-make.sh "$@"
