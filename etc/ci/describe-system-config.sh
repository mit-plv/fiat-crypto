#!/usr/bin/env bash

cd -- "$( dirname -- "${BASH_SOURCE[0]}" )"
cd ../..

function run() {
    "${SHELL}" -c "$@" || true
}

if [ ! -z "$CI" ]; then
    function group() {
        echo "::group::$@"
        run "$@"
        echo "::endgroup::"
    }
else
    function group() { run "$@"; }
fi

group lscpu
group uname -a
group lsb_release -a
group ghc --version
group gcc -v
group ocamlc -config
group coqc --config
group coqc --version
group "true | coqtop"
group etc/machine.sh
