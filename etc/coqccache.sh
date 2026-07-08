#!/bin/sh
# EXAMPLE: COQCCACHE=/tmp/mycache coqccache.sh .coqdep.mk coqc a.v"
# CLEANUP: find /tmp/mycache -mindepth 3 -maxdepth 3 -type d -name "outputs" -atime +7 -exec sh -c 'rm -rf "$(dirname "$1")"' _ {} \;

set -euo pipefail

COQCCACHE="${COQCCACHE:-$HOME/.cache/coqccache}"
depfile="$1"; shift

target_v=""
for arg; do case "$arg" in *.v) target_v="$arg" ;; esac; done
[ -z "$target_v" ] && exec "$@" # for -version, etc

rule=$(sed -n "\%^\([^:]*[[:space:]]\)\?\(\./\)\?${target_v%.v}\.vo\?[[:space:]:]%{p;q;}" "$depfile")
targets=$(echo "${rule%%:*}" | sed 's/\(^\|[[:space:]]\)\.\//\1/g')
deps=$(echo "$(command -v "$1") ${rule#*:}" | sed -e 's/\$(DYNLIB)/.cmxs/g' -e 's/\(^\|[[:space:]]\)\.\//\1/g')
cmd_str=$(printf '%q ' "$@")
cmd_hash=$(printf '%s\n' "$cmd_str" | sha512sum | cut -d' ' -f1)
manifest=$({ echo "$cmd_hash  cmd.sh"; sha512sum $deps; } | sort -k2)
cachekey=$(printf '%s\n' "$manifest" | sha512sum | cut -d' ' -f1)
cachedpath="$COQCCACHE/$(echo "$cachekey" | sed 's/^\(..\)/\1\//')"

[ -f "$cachedpath/deps.sha512" ] && exec cp -R "$cachedpath/outputs/." .

"$@"
mkdir -p "$cachedpath/outputs/$(dirname "$target_v")"
for t in $targets; do [ -f "$t" ] && cp -p "$t" "$cachedpath/outputs/$(dirname "$target_v")/"; done
ln -s "$PWD" "$cachedpath/builddir"
printf '%s\n' "$cmd_str" > "$cachedpath/cmd.sh"
printf '%s\n' "$manifest" > "$cachedpath/deps.sha512"
