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

group sysctl -n machdep.cpu.brand_string
group "sysctl -a | grep machdep.cpu"
group uname -a
group sw_vers -productVersion
group system_profiler SPSoftwareDataType
group opam list
group ocamlc -config
group coqc --config
group coqc --version
group "true | coqtop"
group etc/machine.sh
