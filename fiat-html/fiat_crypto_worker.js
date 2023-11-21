self.importScripts("fiat_crypto.js");
self.onmessage = function(e) {
    try {
        const result = synthesize(e.data);
        postMessage({result: result});
    } catch (err) {
        postMessage({error: err});
    }
};
