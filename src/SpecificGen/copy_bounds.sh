#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

cd "$DIR"

FILENAME="$1"
V_FILE_STEM="${FILENAME%.*}"

for ORIG in $(git ls-files "../Specific/**GF25519*.v" | grep -v "../Specific/GF25519.v"); do
    NEW="$(echo "$ORIG" | sed s'|^../Specific|.|g' | sed s"|25519|${V_FILE_STEM}|g")"
    echo "$NEW"
    NEW_DIR="$(dirname "$NEW")"
    mkdir -p "$NEW_DIR" || exit $?
    cat "$ORIG" | sed s'/Specific/SpecificGen/g' | sed s"/25519/${V_FILE_STEM}/g" > "$NEW" || exit $?
done
