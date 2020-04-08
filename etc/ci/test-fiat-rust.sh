#!/usr/bin/env bash

set -ex

git clone https://github.com/calibra/curve25519-dalek.git --branch=fiat2 curve25519-dalek || exit $?

cd curve25519-dalek || exit $?

cat >> Cargo.toml <<EOF
[patch.crates-io]
fiat-crypto = { path = "../fiat-rust" }
EOF

cargo test --features="std fiat_u64_backend" --no-default-features || exit $?
