#!/usr/bin/env bash

set -ex

################################################################################
# Tests for crate-crypto/Ed448-Goldilocks
################################################################################
git clone https://github.com/crate-crypto/Ed448-Goldilocks.git --branch=master Ed448-Goldilocks || exit $?

pushd Ed448-Goldilocks >/dev/null || exit $?

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

cargo test --features="fiat_u64_backend" --no-default-features || exit $?

popd >/dev/null
