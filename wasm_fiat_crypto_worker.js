self.importScripts("wasm/fiat_crypto.js");
// The wasm_of_ocaml launcher fetches and instantiates the .wasm
// asynchronously and only then runs the OCaml entry point that does
// `Js.export "synthesize" ...`, so `self.synthesize` is not defined
// when importScripts returns. Queue messages and poll until ready.
// Newer wasm_of_ocaml (https://github.com/ocaml-wasm/wasm_of_ocaml/pull/143)
// dispatches `wasmoocaml:loaded` / `wasmoocaml:error` on globalThis; we hook
// those when available and keep the polling fallback for older releases.
let pending = [];
let ready = false;
self.onmessage = function (e) { pending.push(e); };

function installHandler() {
    if (ready) return;
    ready = true;
    self.onmessage = function (e) {
        try {
            const result = self.synthesize(e.data);
            postMessage({ result: result });
        } catch (err) {
            postMessage({ error: err });
        }
    };
    pending.forEach(e => { self.onmessage(e); });
    pending = [];
}

function reportLoadError(err, src) {
    if (ready) return;
    ready = true;
    const message = "wasm_fiat_crypto_worker: wasm load failed" + (src ? " (src=" + src + ")" : "");
    console.error(message, err);
    self.onmessage = function () {
        postMessage({ error: { name: "WasmLoadError", message: message, cause: err } });
    };
    pending.forEach(e => { self.onmessage(e); });
    pending = [];
}

self.addEventListener("wasmoocaml:loaded", function (e) {
    console.log(
        "wasm_fiat_crypto_worker: received wasmoocaml:loaded; the installed " +
        "wasm_of_ocaml is new enough that the polling fallback in this file " +
        "can be removed (see https://github.com/ocaml-wasm/wasm_of_ocaml/pull/143).",
        e && e.detail
    );
    installHandler();
});
self.addEventListener("wasmoocaml:error", function (e) {
    reportLoadError(e && e.detail && e.detail.error, e && e.detail && e.detail.src);
});

(function waitForReady() {
    if (ready) return;
    if (typeof self.synthesize === 'function') {
        installHandler();
    } else {
        console.warn("wasm_fiat_crypto_worker: self.synthesize not yet defined, retrying in 50ms");
        setTimeout(waitForReady, 50);
    }
})();
