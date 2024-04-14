#!/bin/sh

cd -- "$( dirname -- "$0" )"
cd ../..

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
        2>&1 run "$@"
        echo "::endgroup::"
    }
else
    group() { run "$@"; }
fi

group sysctl -n machdep.cpu.brand_string
group "sysctl -a | grep machdep.cpu"
group uname -a
group sw_vers -productVersion
group system_profiler SPSoftwareDataType
group opam switch
group opam list
group ocamlc -config
group coqc --config
group coqc --version
group "true | coqtop"
group etc/machine.sh
etc/ci/github-actions-record-coq-info.sh
