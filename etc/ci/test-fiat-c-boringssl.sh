#!/usr/bin/env bash
# USAGE: $0 SUBCOMPONENT (e.g., fiat-c/src)

################################################################################
# Tests for BoringSSL
################################################################################
echo "::group::Cloning BoringSSL"
({
    set -ex
    rm -rf boringssl
    git clone https://boringssl.googlesource.com/boringssl || exit $?
    git -C boringssl log -1
}) || exit $?
echo "::endgroup::"

SUBCOMPONENT="$1"
if [ -z "$SUBCOMPONENT" ]; then
    echo "ERROR: Missing argument"
    echo "USAGE: $0 SUBCOMPONENT"
    echo "Example SUBCOMPONENTS include fiat-c/src, fiat-bedrock2/src"
    exit 1
fi
SUBCOMPONENT_PATH="$(cd "$SUBCOMPONENT" && pwd)"

pushd boringssl >/dev/null

echo "::group::Patching BoringSSL"
({
    set -ex
    ( cd third_party/fiat &&
      for i in "curve25519_32.h" "curve25519_64.h" "p256_32.h" "p256_64.h"; do
        cp "${SUBCOMPONENT_PATH}/${i/.h/.c}" "$i" || exit $?
      done ) || exit $?
    ( cd third_party/fiat && git --no-pager diff )
}) || exit $?
echo "::endgroup::"

echo "::group::Building BoringSSL"
({
    set -ex
    mkdir build
    cd build
    cmake -GNinja .. -DCMAKE_CXX_FLAGS="-Wno-error=unused-function ${EXTRA_CFLAGS}" -DCMAKE_C_FLAGS="-Wno-error=unused-function ${EXTRA_CFLAGS}" || exit $?
    ninja || exit $?
}) || exit $?
echo "::endgroup::"

echo "::group::Testing BoringSSL"
({
    set -ex
    ninja -C build run_tests || exit $?
}) || exit $?
echo "::endgroup::"

popd >/dev/null
