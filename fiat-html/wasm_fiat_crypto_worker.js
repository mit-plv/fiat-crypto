self.importScripts("wasm/fiat_crypto.js");
let pending = [];
self.onmessage = function (e) { pending.push(e); };
setTimeout(function () {
    self.onmessage = function(e) {
        try {
            const result = synthesize(e.data);
            postMessage({result: result});
        } catch (err) {
            postMessage({error: err});
        }
    };
    pending.forEach(e => { self.onmessage(e); });
    pending = [];
}, 1000);
