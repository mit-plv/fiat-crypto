#!/usr/bin/env bash

set -ex

################################################################################
# Tests for calibra/curve25519-dalek
################################################################################
git clone https://github.com/calibra/curve25519-dalek.git --branch=fiat2 curve25519-dalek || exit $?

pushd curve25519-dalek >/dev/null || exit $?

cat >> Cargo.toml <<EOF
[patch.crates-io]
fiat-crypto = { path = "../fiat-rust" }
EOF

cargo test --features="std fiat_u64_backend" --no-default-features || exit $?

popd >/dev/null
