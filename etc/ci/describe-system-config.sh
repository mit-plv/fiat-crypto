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
group lsb_release -a
group cat /etc/os-release
group cat /proc/cpuinfo
group cat /proc/meminfo
group cat /etc/alpine-release
group apk info
group apk info coq
group apk --print-arch
group dpkg -l | cat
group pacman -Qs
. etc/ci/describe-system-config-common-groups.sh
