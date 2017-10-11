#!/usr/bin/bash

set -ex

cd "$WORKSPACE"
export PATH="/opt/coq-$coq_version/bin${PATH:+:}$PATH"
. /opt/bashrc/bashrc
export TARGETS="coq display bench test"
rm -f BUILD.ok
((/opt/timeout/default-timeout make -j$(nproc) TIMED=1 PROFILE=1 $TARGETS || make STDTIME='/opt/timeout/time-default-timeout-coq -f "$* (real: %e, user: %U, sys: %S, mem: %M ko)"' TIMED=1 PROFILE=1 $TARGETS) && touch BUILD.ok) 2>&1 | tee time-of-build.log
python ./etc/coq-scripts/timing/make-one-time-file.py time-of-build.log time-of-build-pretty.log
cat time-of-build-pretty.log
rm BUILD.ok
