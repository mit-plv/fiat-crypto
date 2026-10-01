# Vendored copy of `wasm-feature-detect`

This directory contains an unmodified copy of the UMD build of
[`wasm-feature-detect`](https://github.com/GoogleChromeLabs/wasm-feature-detect)
(Google Chrome Labs, Apache-2.0; see `LICENSE`), used by
`fiat-html/disable-wasm-option.js` to decide whether the browser supports the
WebAssembly features (tail calls, GC, exceptions) that the wasm_of_ocaml build
of fiat-crypto needs.

The file is vendored, rather than loaded from a CDN at page load time, so that
the published page at <https://mit-plv.github.io/fiat-crypto/> only ever runs
script that is checked into this repository (scrutineer finding #2520).

| File | Upstream source |
|---|---|
| `wasm-feature-detect-1.9.0.umd.js` | `dist/umd/index.js` from the npm package `wasm-feature-detect@1.9.0` |
| `LICENSE` | `LICENSE` from the same package |

Provenance of version 1.9.0 (published 2026-08-11):

- npm tarball: <https://registry.npmjs.org/wasm-feature-detect/-/wasm-feature-detect-1.9.0.tgz>
  (registry `integrity`: `sha512-zonE+xlIIYtxPy++L24ow0hAD8CICb4+FgPyROd3buyXIqsJvUEDkBgfCCoXOd1Hu3DUr0GOfnPIdcGV+YpNaA==`)
- same bytes as <https://unpkg.com/wasm-feature-detect@1.9.0/dist/umd/index.js>
- `wasm-feature-detect-1.9.0.umd.js` SHA-384 (SRI form):
  `sha384-Vrjn7GSeLwDNwl7PQMXuvOQjwK7YPWWT0CCmgjbSDzk76LQW/l1qpFZCk4cz/tqR`

## Updating

1. Download the new tarball from the npm registry and check its `integrity`
   hash against `https://registry.npmjs.org/wasm-feature-detect`.
2. Copy `package/dist/umd/index.js` to `wasm-feature-detect-<version>.umd.js`
   here (do not edit it), remove the old file, and refresh `LICENSE` if it
   changed upstream.
3. Update the `<script src="vendor/wasm-feature-detect/...">` tag in
   `fiat-html/fiat-crypto.html` and the version/hashes in this file.
4. Check that the functions used by `fiat-html/disable-wasm-option.js`
   (`tailCall`, `gc`, `exceptions`) still exist.
