document.addEventListener('DOMContentLoaded', async function() {
    const wasmCheckbox = document.getElementById('wasm');
    const extraWasmLabel = document.getElementById('extraWasmLabel');
    wasmCheckbox.disabled = true; // Initially disable the checkbox

    try {
        const features = {
            tailCall: await wasmFeatureDetect.tailCall(),
            gc: await wasmFeatureDetect.gc(),
            exceptions: await wasmFeatureDetect.exceptions()
        };

        const unsupportedFeatures = Object.entries(features)
              .filter(([feature, supported]) => !supported)
              .map(([feature]) => feature);

        if (unsupportedFeatures.length === 0) {
            wasmCheckbox.disabled = false; // Re-enable the checkbox if all features are supported
        } else {
            wasmCheckbox.checked = false;

            let featureText = unsupportedFeatures.join(', ');
            let firefoxText = unsupportedFeatures.map(feature => {
                if (feature === 'tailCall') return 'javascript.options.wasm_tail_calls';
                if (feature === 'gc') return 'javascript.options.wasm_gc';
                if (feature === 'exceptions') return 'javascript.options.wasm_exceptions';
                return feature;
            }).join(', ');

            if (navigator.userAgent.includes('Firefox')) {
                extraWasmLabel.innerHTML = `(enable <code>${firefoxText}</code> in <code>about:config</code>)`;
            } else {
                extraWasmLabel.innerHTML = `(missing wasm support for: ${featureText})`;
            }
        }
    } catch (error) {
        console.error('Error checking wasm feature support:', error);
    }
});
