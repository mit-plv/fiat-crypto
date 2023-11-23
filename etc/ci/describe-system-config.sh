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

group lscpu
group uname -a
group lsb_release -a
group ulimit -aH
group ulimit -aS
group cat /etc/os-release
group cat /proc/cpuinfo
group cat /proc/meminfo
group apk info
group dpkg -l
group ghc --version
group ghc -v
group gcc --version
group gcc -v
group opam switch
group opam list
group ocamlc -config
group coqc --config
group coqc --version
group "true | coqtop"
group etc/machine.sh
group "echo PATH=$PATH"
group "echo SHELL=$SHELL"
