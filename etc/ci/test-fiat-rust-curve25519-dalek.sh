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

RUSTFLAGS='--cfg curve25519_dalek_backend="fiat"' cargo test --target x86_64-unknown-linux-gnu || exit $?
RUSTFLAGS='--cfg curve25519_dalek_backend="fiat"' cargo test --target i686-unknown-linux-gnu || exit $?

popd >/dev/null
