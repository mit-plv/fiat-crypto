// Written with help from https://chat.openai.com/share/74d5901c-9005-4560-8307-582ff54e403e
const SYNTHESIS_CACHE_VERSION = 2;
document.addEventListener('DOMContentLoaded', function () {
    const errorDiv = document.getElementById('error');
    const outputDiv = document.getElementById('output');
    const stdoutDiv = document.getElementById('stdoutContainer');
    const stderrDiv = document.getElementById('stderrContainer');
    const stdoutBox = document.getElementById('stdout');
    const stderrBox = document.getElementById('stderr');
    const outputFilesContainer = document.getElementById('outputFilesContainer');
    const versionBox = document.getElementById('version');
    const wasmCheckbox = document.getElementById('wasm');
    const inputForm = document.getElementById('inputForm');
    const inputArgs = document.getElementById('inputArgs');
    const synthesizeButton = document.getElementById('synthesizeButton');
    const cancelButton = document.getElementById('cancelButton');
    const clearCacheButton = document.getElementById('clearCacheButton');
    const permalink = document.getElementById('permalink');
    const statusSpan = document.getElementById('status');
    const isSafari = /^((?!chrome|android).)*safari/i.test(navigator.userAgent);
    const isMacOrIOS = /Macintosh|MacIntel|MacPPC|Mac68K|iPhone|iPad|iPod/.test(navigator.platform);

    function splitUnescapedSpaces(input) {
        return input
            .replace(/\\\\/g, '\u0000')  // Temporarily replace \\ with a placeholder
            .replace(/\\ /g, '\u0001')  // Temporarily replace escaped spaces with a placeholder
            .split(/ +/)               // Split by spaces
            .filter(s => s)
            .map(s => s
                .replace(/\u0000/g, '\\')  // Restore backslashes
                .replace(/\u0001/g, ' ')   // Restore spaces
            );
    }

    function joinWithEscaping(inputArray) {
        return inputArray
            .map(s => s
                .replace(/\\/g, '\\\\')  // Escape backslashes
                .replace(/ /g, '\\ ')   // Escape spaces
            )
            .join(' ');
    }

    function parseToStringArray(str, name) {
        let args = JSON.parse(str);
        if (!Array.isArray(args) || !args.every(arg => typeof arg === 'string')) {
            throw new Error(`Invalid: ${name} is not an array of strings`);
        }
        return args;
    }

    function parseToStringArrayArray(str, name) {
        let args = JSON.parse(str);
        if (!Array.isArray(args) || !args.every(arg => Array.isArray(arg) && arg.every(arg2 => typeof arg2 === 'string'))) {
            throw new Error(`Invalid: ${name} is not an array of arrays of strings`);
        }
        return args;
    }

    function parseToStringMapStringArray(str, name) {
        let args = JSON.parse(str);
        if (typeof args !== 'object') {
            throw new Error(`Invalid: ${name} is not an object`);
        }
        if (args === null) {
            throw new Error(`Invalid: ${name} is null`);
        }
        if (Array.isArray(args)) {
            throw new Error(`Invalid: ${name} is an array, not a mapping from strings to arrays of strings`);
        }
        Object.entries(args).forEach(([key, value]) => {
            if (typeof key !== 'string') {
                throw new Error(`Invalid: ${name} has non-string key ${key}`);
            }
            if (!Array.isArray(value) || !value.every(value2 => typeof value2 === 'string')) {
                throw new Error(`Invalid: ${name} has non-array value ${value} for key ${key}`);
            }
        });
        return args;
    }

    function isValidJsonStringArray(str) {
        try {
            parseToStringArray(str);
            return true;
        } catch (e) {
            return false;
        }
    }

    function validateInput() {
        const isJson = document.querySelector('input[name="inputType"][value="json"]').checked;
        const isValid = !isJson || isValidJsonStringArray(inputArgs.value);
        synthesizeButton.disabled = !isValid;
        document.querySelector('input[name="inputType"]:not([value="json"])').disabled = !isValid;
    }

    function enableForm() {
        inputArgs.disabled = false;
        synthesizeButton.disabled = false;
        cancelButton.disabled = true;
    }

    function setOutputFiles(files) {
        // Clear the output files container
        outputFilesContainer.innerHTML = '';

        // Create a container for each output file
        const fileEntries = Object.entries(files);
        
        // Add or remove 'hidden' class based on whether there are files
        if (fileEntries.length > 0) {
            // Create HTML for each file
            fileEntries.forEach(([filename, contents]) => {
                // Create file container with HTML template literal
                const fileHtml = `
                    <div class="code-container">
                        <pre class="output-filename">${escapeHtml(filename)}:</pre>
                        <code id="output-file-${escapeHtml(filename)}" class="code"></code>
                        <button class="copy-button" data-target="output-file-${escapeHtml(filename)}">Copy</button>
                    </div>
                `;

                // Parse the HTML and add to container
                const template = document.createElement('template');
                template.innerHTML = fileHtml.trim();
                const entry = template.content.firstElementChild.cloneNode(true);
                entry.querySelector('.code').textContent = contents;
                outputFilesContainer.appendChild(entry);
            });
            outputFilesContainer.classList.remove('hidden');
        } else {
            outputFilesContainer.classList.add('hidden');
        }
    }

    function clearOutput() {
        errorDiv.textContent = '';
        stdoutBox.textContent = '';
        stderrBox.textContent = '';
        setOutputFiles({});
        errorDiv.classList.add('hidden');
        outputDiv.classList.add('hidden');
        stderrDiv.classList.add('hidden');
        stdoutDiv.classList.add('hidden');
    }

    function escapeHtml(html) {
        var text = document.createTextNode(html);
        var p = document.createElement('p');
        p.appendChild(text);
        return p.innerHTML;
    }


    function displayError(message, isHtml = false) {
        if (isHtml) {
            errorDiv.innerHTML = message;
        } else {
            errorDiv.textContent = message;
        }
        if (message) {
            errorDiv.classList.remove('hidden');
            const consoleMessage = message.replace(/<br\s*\/?>/gi, '\n');
            console.error(consoleMessage);
        } else {
            errorDiv.classList.add('hidden');
        }
        enableForm();
    }

    function displayOutput(stdout, stderr, outputFiles) {
        stdoutBox.textContent = stdout;
        stderrBox.textContent = stderr;
        setOutputFiles(outputFiles);
        outputDiv.classList.remove('hidden');
        if (stdout) {
            stdoutDiv.classList.remove('hidden');
        } else {
            stdoutDiv.classList.add('hidden');
        }
        if (stderr) {
            console.error(stderr);
            stderrDiv.classList.remove('hidden');
        } else {
            stderrDiv.classList.add('hidden');
        }
        enableForm();
    }

    function updatePermalink(args) {
        const wasmString = wasmCheckbox.checked ? '&wasm' : '';
        const stdin = getStdinFromFormBoxRaw();
        const files = getFilesFromFormBoxRaw();
        const stdinString = stdin ? `&stdin=${encodeURIComponent(stdin)}` : '';
        const filesString = files ? `&files=${encodeURIComponent(files)}` : '';
        const inputType = document.querySelector('input[name="inputType"]:checked').value === 'json' ? `&inputType=json` : '';
        const inputTypeString = inputType !== 'string' ? `&inputType=${inputType}` : '';
        const queryString = `?argv=${encodeURIComponent(JSON.stringify(args.slice(1)))}${stdinString}${filesString}${inputTypeString}&interactive${wasmString}`;
        // Handle both file and http(s) URLs
        let baseUrl = window.location.href.split('?')[0]; // Get base URL without query string
        permalink.href = baseUrl + queryString;
        permalink.classList.remove('hidden');
    }

    function updateStatus(message) {
        statusSpan.textContent = message;
        if (message) {
            statusSpan.classList.remove('hidden');
        } else {
            statusSpan.classList.add('hidden');
        }
    }

    function handleSynthesisResultData(result) {
        const success = result[0];
        const exceptionText = result[1];
        const stdout = result[2];
        const stderr = result[3];
        const files = result[4];

        if (!success) {
            displayError(exceptionText.join('\n'));
        }
        const filesMap = {};
        for (const [key, value] of files) {
            filesMap[key] = value.join('');
        }
        displayOutput(stdout.join(''), stderr.join(''), filesMap);
    }

    function handleException(err) {
        const errHtml = err === undefined ? 'undefined error message (try opening the developer console)' : escapeHtml(`${err.name}: ${err.message}`);
        let errorMessage = `Synthesis failed: ${errHtml}`;

        if (err === undefined || /stack size exceeded|too much recursion/i.test(err.message)) {
            if (!isSafari) {
                errorMessage += "<br>Unfortunately Chrome, Firefox, and the ECMAScript Standard don't support proper tail-call elimination for unfortunate <a href=\"https://stackoverflow.com/a/54721813/377022\">historical</a> <a href=\"https://medium.com/indigoag-eng/tail-call-optimization-in-the-wild-26a10e450c73\">reasons</a>.";

                if (!isMacOrIOS) {
                    errorMessage += "<br>Consider using WASM or opening this page in <a href=\"https://www.apple.com/safari/\">Safari</a> on a Mac or iOS device instead.";
                } else {
                    errorMessage += "<br>Consider using WASM or opening this page in <a href=\"https://www.apple.com/safari/\">Safari</a> instead.";
                }
            }
        }

        clearOutput();
        displayError(errorMessage, true);
        updateStatus(""); // Clear status
    }

    function handleSynthesisResult(result, cached) {
        console.log({ 'handleSynthesisResult result': result });
        const extraCachedString = [
            result.fiat_crypto_version == fiat_crypto_version ? '' : ` in ${result.fiat_crypto_version}`,
            result.method === undefined ? '' : ` via ${result.method}`,
        ].join('');
        const cachedString = cached ? ` (cached on ${result.timestamp}${extraCachedString})` : '';
        if (result.success) {
            clearOutput();
            updateStatus(`Synthesis completed in ${result.time} seconds${cachedString}`);
            handleSynthesisResultData(result.result);
        } else {
            handleException(result.result);
            updateStatus(`Synthesis failed in ${result.time} seconds${cachedString}`);
        }
    }

    let fiatCryptoWorker;
    let wasmFiatCryptoWorker;

    function setupWorkers() {
        fiatCryptoWorker = new Worker("fiat_crypto_worker.js");
        wasmFiatCryptoWorker = new Worker("wasm_fiat_crypto_worker.js");

        // Common setup for both workers
        [fiatCryptoWorker, wasmFiatCryptoWorker].forEach(worker => {
            worker.onmessage = function (e) {
                console.log(`Early synthesis result: ${e.data}`);
            };

            worker.onerror = function (err) {
                handleException(err);
            };
        });
    }

    function cancelWorkers() {
        [fiatCryptoWorker, wasmFiatCryptoWorker].forEach(worker => worker.terminate());
        console.log("Synthesis workers terminated.");

        // Re-setup workers
        setupWorkers();
    }

    // https://betterprogramming.pub/serializing-error-in-javascript-27c3a048dc3b
    function errorJSONReplacer(key, value) {
        // JSON.stringify does not deal with errors
        if (value instanceof Error) {
            return {
                name: value.name,
                message: value.message,
                stack: value.stack,
                cause: value.cause,
            };
        }
        return value;
    }

    function handleSynthesis(args, stdin, files) {
        const startTime = performance.now();
        const cacheKey = 'synthesize_' + JSON.stringify([args, stdin, files]);
        const cached = localStorage.getItem(cacheKey);
        console.log({ 'synthesize args': [args, stdin, files] });
        updateStatus("Synthesizing...");
        updatePermalink(args);

        if (cached) {
            const cachedData = JSON.parse(cached);
            if (cachedData.version === SYNTHESIS_CACHE_VERSION) {
                handleSynthesisResult(cachedData, true);
                return;
            } else {
                console.log(`cache miss: version ${cachedData.version} (${cachedData.fiat_crypto_version}), expected ${SYNTHESIS_CACHE_VERSION}`)
            }
        }

        const useWasm = wasmCheckbox.checked;

        const recieveMessage = function (success) {
            return function (e) {
                const endTime = performance.now();
                const timeTaken = (endTime - startTime) / 1000;
                const now = new Date();
                const resultData = {
                    result: success ? (e.data.error !== undefined ? e.data.error : e.data.result) : e.data,
                    time: timeTaken,
                    success: success && e.data !== undefined && e.data.error === undefined,
                    timestamp: now.toISOString(),
                    version: SYNTHESIS_CACHE_VERSION,
                    fiat_crypto_version: fiat_crypto_version,
                    method: useWasm ? 'wasm_of_ocaml' : 'js_of_ocaml',
                };
                try {
                    localStorage.setItem(cacheKey, JSON.stringify(resultData, errorJSONReplacer));
                } catch (e) {
                    console.error(`Failed: localStorage.setItem(${JSON.stringify(cacheKey)}, ${JSON.stringify(JSON.stringify(resultData))})`);
                }
                handleSynthesisResult(resultData, false);
            };
        };

        const currentWorker = useWasm ? wasmFiatCryptoWorker : fiatCryptoWorker;
        const filesList = Object.entries(files).map(([name, contents]) => [name, ...contents]);
        currentWorker.postMessage([[args], stdin, filesList]);
        currentWorker.onmessage = recieveMessage(true);
        currentWorker.onerror = recieveMessage(false);
    }

    function parseAndRun(argv, stdinv, filesv) {
        try {
            let args = parseToStringArray(decodeURIComponent(argv), 'argv');
            args.unshift('fiat_crypto.js');
            let stdin = parseToStringArrayArray(decodeURIComponent(stdinv), 'stdin');
            let files = parseToStringMapStringArray(decodeURIComponent(filesv), 'files');
            handleSynthesis(args, stdin, files);
        } catch (e) {
            displayError(`Error: ${e.message}: ${argv}, ${stdinv}, ${filesv}`);
        }
    }

    function nonFalseQueryParam(value) {
        return value !== null && value != 'false' && value != '0';
    }

    function updateInputType(inputType) {
        if (inputType === 'string') {
            if (isValidJsonStringArray(inputArgs.value)) {
                inputArgs.value = joinWithEscaping(JSON.parse(inputArgs.value));
            }
        } else if (inputType === 'json') {
            inputArgs.value = JSON.stringify(splitUnescapedSpaces(inputArgs.value));
        }
        validateInput();
    }

    function parseQueryParams() {
        const queryParams = new URLSearchParams(window.location.search);
        const argv = queryParams.get('argv');
        const interactive = queryParams.get('interactive');
        const wasm = queryParams.get('wasm')
        const inputType = queryParams.get('inputType') || 'string';
        const stdin = queryParams.get('stdin') || '[]';
        const files = queryParams.get('files') || '{}';

        if (nonFalseQueryParam(wasm)) {
            wasmCheckbox.checked = true;
        }

        setupWorkers();

        if (argv) {
            if (nonFalseQueryParam(interactive)) {
                inputArgs.value = decodeURIComponent(argv);
                populateStdinEntries(JSON.parse(decodeURIComponent(stdin)));
                populateFileEntries(JSON.parse(decodeURIComponent(files)));
                document.querySelector(`input[value="${inputType}"]`).checked = true;
                updateInputType(inputType);
                inputForm.classList.remove('hidden');
            }
            parseAndRun(argv, stdin, files);
        } else {
            inputForm.classList.remove('hidden');
        }
    }

    parseQueryParams();

    inputArgs.addEventListener('input', validateInput);

    document.querySelectorAll('input[name="inputType"]').forEach(radio => {
        radio.addEventListener('change', function () {
            updateInputType(this.value);
        });
    });

    synthesizeButton.addEventListener('click', function () {
        // Disable form elements
        inputArgs.disabled = true;
        synthesizeButton.disabled = true;
        cancelButton.disabled = false;
        // Parse arguments and handle synthesis
        const argsType = document.querySelector('input[name="inputType"]:checked').value;
        const args = argsType === 'json' ? JSON.parse(inputArgs.value) : splitUnescapedSpaces(inputArgs.value);
        args.unshift('fiat_crypto.js');
        const stdin = getStdinFromFormBox();
        const files = getFilesFromFormBox();
        handleSynthesis(args, stdin, files);
    });

    inputForm.addEventListener('submit', function (event) {
        event.preventDefault(); // Prevent the default form submission
        synthesizeButton.click(); // Programmatically click the synthesize button
    });

    cancelButton.addEventListener('click', function () {
        // Cancel synthesis if possible and re-enable form elements
        inputArgs.disabled = false;
        synthesizeButton.disabled = false;
        cancelButton.disabled = true;
        updateStatus("");
        cancelWorkers();
    });

    clearCacheButton.addEventListener('click', function () {
        localStorage.clear();
    });

    versionBox.textContent = `${fiat_crypto_version}`;
});
