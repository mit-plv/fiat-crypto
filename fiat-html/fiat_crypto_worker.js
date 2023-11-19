self.importScripts("fiat_crypto.js");
self.onmessage = function(e) {
    const result = synthesize(e.data);
    postMessage(result);
};
