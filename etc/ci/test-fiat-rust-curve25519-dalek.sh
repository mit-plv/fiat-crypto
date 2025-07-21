#!/usr/bin/env bash

set -ex

################################################################################
# Tests for calibra/curve25519-dalek
################################################################################
git clone https://github.com/dalek-cryptography/curve25519-dalek curve25519-dalek || exit $?

pushd curve25519-dalek >/dev/null || exit $?

if grep -q "^\[patch\.crates-io\]" Cargo.toml; then
    # Add to existing [patch.crates-io] section
    sed -i '/^\[patch\.crates-io\]/a fiat-crypto = { path = "../fiat-rust" }' Cargo.toml
else
    # Create new [patch.crates-io] section
    cat >> Cargo.toml <<EOF

[patch.crates-io]
fiat-crypto = { path = "../fiat-rust" }
EOF
fi

RUSTFLAGS='--cfg curve25519_dalek_backend="fiat" --cfg curve25519_dalek_bits="64"' cargo test || exit $?
RUSTFLAGS='--cfg curve25519_dalek_backend="fiat" --cfg curve25519_dalek_bits="32"' cargo test || exit $?

popd >/dev/null
