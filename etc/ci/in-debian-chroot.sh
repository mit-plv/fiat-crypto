#!/bin/sh
set -e -u -x

# This script is intended to be called from github hosted runners only.

exec sudo chroot /chroot setpriv --reuid "$(id -u)" --regid "$(id -g)" --init-groups \
  /bin/sh -e -u -x -c 'cd "$1"; shift; exec sh -e -u -x "$@"' -- "$(pwd)" "$@"
