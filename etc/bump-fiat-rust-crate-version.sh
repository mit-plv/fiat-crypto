#!/usr/bin/env bash

set -e

CARGO_TOML_PATH="fiat-rust/Cargo.toml"

VERSION_LINE="$(grep 'version\s*=\s*' "${CARGO_TOML_PATH}")"
VERSION_NUMBER="$(echo "${VERSION_LINE}" | sed 's/version\s*=\s*//g; s/"//g; s/\s//g')"
# https://stackoverflow.com/a/4486087/377022
NEW_VERSION_NUMBER="$(awk -F. '/[0-9]+\./{$NF++;print}' OFS=. <<< "${VERSION_NUMBER}")"
NEW_VERSION_LINE="$(echo "${VERSION_LINE}" | sed "s/${VERSION_NUMBER}/${NEW_VERSION_NUMBER}/g")"
echo "Updating ${CARGO_TOML_PATH} from version ${VERSION_NUMBER} to ${NEW_VERSION_NUMBER}"
sed "s/${VERSION_LINE}/${NEW_VERSION_LINE}/g" -i "${CARGO_TOML_PATH}"

# sanity check
AGAIN_VERSION_LINE="$(grep 'version\s*=\s*' "${CARGO_TOML_PATH}")"
AGAIN_VERSION_NUMBER="$(echo "${AGAIN_VERSION_LINE}" | sed 's/version\s*=\s*//g; s/"//g; s/\s//g')"
if [ "${NEW_VERSION_NUMBER}" != "${AGAIN_VERSION_NUMBER}" ]; then
    echo "ERROR: Tried to change '${VERSION_NUMBER}' to '${NEW_VERSION_NUMBER}' in ${CARGO_TOML_PATH},"
    echo "  but somehow ended up with '${AGAIN_VERSION_NUMBER}'."
    exit 1
fi
