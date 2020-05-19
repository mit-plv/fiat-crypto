#!/usr/bin/env bash

set -ex

################################################################################
# Tests for crate-crypto/Ed448-Goldilocks
################################################################################
git clone https://github.com/crate-crypto/Ed448-Goldilocks.git --branch=master Ed448-Goldilocks || exit $?

pushd Ed448-Goldilocks >/dev/null || exit $?

cat >> Cargo.toml <<EOF

[patch.crates-io]
fiat-crypto = { path = "../fiat-rust" }
EOF

cargo test --features="fiat_u64_backend" --no-default-features || exit $?

popd >/dev/null
