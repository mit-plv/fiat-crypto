#!/bin/bash

set -o pipefail
set -ex

cd "$( dirname "${BASH_SOURCE[0]}" )"

python3 generate_parameters.py primes.txt
./src/Specific/CurveParameters/remake_curves.sh -f | tee remake_curves.log
grep 'git add ' remake_curves.log | sed s'/git add //g' | tr '"' '\n' | grep -v '^\s*$' | xargs git add
make update-_CoqProject
