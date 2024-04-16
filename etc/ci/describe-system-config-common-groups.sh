#!/bin/sh

group uname -a
group ulimit -aH
group ulimit -aS
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
group coqtop </dev/null
group etc/machine.sh
group "echo PATH=$PATH"
group "echo SHELL=$SHELL"
group etc/ci/github-actions-record-coq-info.sh "$GITHUB_STEP_SUMMARY"
