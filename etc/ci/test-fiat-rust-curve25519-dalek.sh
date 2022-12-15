#!/usr/bin/env bash

set -ex

################################################################################
# Tests for calibra/curve25519-dalek
################################################################################
git clone https://github.com/dalek-cryptography/curve25519-dalek curve25519-dalek || exit $?

pushd curve25519-dalek >/dev/null || exit $?

cat >> Cargo.toml <<EOF
[patch.crates-io]
fiat-crypto = { path = "../fiat-rust" }
EOF

RUSTFLAGS='--cfg curve25519_dalek_backend="fiat" --cfg curve25519_dalek_bits="64"' cargo test || exit $?
RUSTFLAGS='--cfg curve25519_dalek_backend="fiat" --cfg curve25519_dalek_bits="32"' cargo test || exit $?

popd >/dev/null
