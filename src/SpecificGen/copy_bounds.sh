#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

cd "$DIR"

FILENAME="$1"
V_FILE_STEM="${FILENAME%.*}"
BIT_WIDTH=64
case "$V_FILE_STEM" in
    *_64) BIT_WIDTH=128;;
esac

if [ -z "$V_FILE_STEM" ]; then
    echo "USAGE: $0 JSON_FILE"
    exit 1
fi

for ORIG in $(git ls-files "../Specific/**GF25519*.v" | grep -v "../Specific/GF25519.v"); do
    NEW="$(echo "$ORIG" | sed s'|^../Specific|.|g' | sed s"|25519|${V_FILE_STEM}|g")"
    echo "$NEW"
    NEW_DIR="$(dirname "$NEW")"
    mkdir -p "$NEW_DIR" || exit $?
    cat "$ORIG" | sed s"/64/${BIT_WIDTH}/g" | sed s'/Specific/SpecificGen/g' | sed s"/25519/${V_FILE_STEM}/g" > "$NEW" || exit $?
    if [ -z "$(git ls-files "$NEW")" ]; then
        echo "git add '$NEW'"
        git add "$NEW" || exit $?
    fi
done
