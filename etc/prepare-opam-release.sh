#!/usr/bin/env bash

# Prepares coq-fiat-crypto.opam for release by:
# 1. Removing the version: line
# 2. Replacing the git URL with a tarball URL and sha512 checksum

set -e

cd "$(git rev-parse --show-toplevel)"

# Get version from CLI or default to most recent tag
version="${1:-$(git tag --sort=-v:refname | head -1)}"

if [ -z "$version" ]; then
    echo "Error: No version provided and no git tags found" >&2
    exit 1
fi

# Strip leading 'v' if present for the version number
version_num="${version#v}"
# Ensure version starts with 'v' for the tag
version_tag="v${version_num}"

opam_file="coq-fiat-crypto.opam"

if [ ! -f "$opam_file" ]; then
    echo "Error: $opam_file not found" >&2
    exit 1
fi

echo "Preparing $opam_file for release ${version_tag}..."

# Download the tarball and compute sha512
tarball_url="https://github.com/mit-plv/fiat-crypto/archive/refs/tags/${version_tag}.tar.gz"
echo "Downloading ${tarball_url}..."

tmpfile=$(mktemp)
trap "rm -f '$tmpfile'" EXIT

if ! wget -q "$tarball_url" -O "$tmpfile"; then
    echo "Error: Failed to download tarball from $tarball_url" >&2
    exit 1
fi

# Compute sha512 (works on both Linux and macOS)
if command -v sha512sum >/dev/null 2>&1; then
    sha512=$(sha512sum "$tmpfile" | cut -d' ' -f1)
elif command -v shasum >/dev/null 2>&1; then
    sha512=$(shasum -a 512 "$tmpfile" | cut -d' ' -f1)
else
    echo "Error: Neither sha512sum nor shasum found" >&2
    exit 1
fi

echo "SHA512: $sha512"

# Remove the version: line
sed -i.bak '/^version:/d' "$opam_file"

# Replace the url block
# First, remove the existing url block (handles multiline)
awk '
/^url \{/ { in_url=1; next }
in_url && /^\}/ { in_url=0; next }
!in_url { print }
' "$opam_file" > "${opam_file}.tmp"

# Append the new url block
cat >> "${opam_file}.tmp" << EOF
url {
  src: "${tarball_url}"
  checksum: "sha512=${sha512}"
}
EOF

mv "${opam_file}.tmp" "$opam_file"
rm -f "${opam_file}.bak"

echo "Done. Updated $opam_file:"
echo "---"
cat "$opam_file"
