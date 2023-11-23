document.addEventListener('DOMContentLoaded', async function() {
    const wasmCheckbox = document.getElementById('wasm');
    const extraWasmLabel = document.getElementById('extraWasmLabel');
    wasmCheckbox.disabled = true;  // Initially disable the checkbox

    try {
        if (await wasmFeatureDetect.tailCall()) {
            wasmCheckbox.disabled = false;  // Re-enable the checkbox if tail calls are supported
        } else {
            wasmCheckbox.checked = false;

            if (navigator.userAgent.includes('Firefox')) {
                extraWasmLabel.innerHTML = '(enable <code>javascript.options.wasm_tail_calls</code> in <code>about:config</code>)';
            } else {
                extraWasmLabel.innerHTML = '(wasm tail calls not supported)';
            }
        }
    } catch (error) {
        console.error('Error checking wasm tail call support:', error);
    }
});
