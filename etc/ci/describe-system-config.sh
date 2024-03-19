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
group cat /etc/alpine-release
group apk info
group apk info coq
group apk --print-arch
group dpkg -l
group pacman -Qs
group ghc --version
group ghc -v
group gcc --version
group gcc -v
group opam switch
group opam list
group ocamlc -config
group ocamlc -where
group ocamlfind printconf destdir
group ocamlfind list
group ocamlfind query findlib
group ocamlfind query zarith
group ocamlfind query coq
group ocamlfind query coq-core
group ocamlfind query coq-core.plugins
group ocamlfind query coq-core.plugins.ltac
group "ocamlfind query coq | xargs find"
group js_of_ocaml --version
group wasm_of_ocaml --version
group coqc --config
group coqc --version
group "true | coqtop"
group etc/machine.sh
group "echo PATH=$PATH"
group "echo SHELL=$SHELL"
