// Written with help from https://chat.openai.com/share/74d5901c-9005-4560-8307-582ff54e403e
const SYNTHESIS_CACHE_VERSION = 1;
document.addEventListener('DOMContentLoaded', function() {
    const errorDiv = document.getElementById('error');
    const outputDiv = document.getElementById('output');
    const stdoutDiv = document.getElementById('stdoutContainer');
    const stderrDiv = document.getElementById('stderrContainer');
    const stdoutBox = document.getElementById('stdout');
    const stderrBox = document.getElementById('stderr');
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

    function parseToStringArray(str) {
        let args = JSON.parse(str);
        if (!Array.isArray(args) || !args.every(arg => typeof arg === 'string')) {
            throw new Error('Invalid: Not an array of strings');
        }
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

    function clearOutput() {
        errorDiv.textContent = '';
        stdoutBox.textContent = '';
        stderrBox.textContent = '';
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

    function displayOutput(stdout, stderr) {
        stdoutBox.textContent = stdout;
        stderrBox.textContent = stderr;
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
        const queryString = `?argv=${encodeURIComponent(JSON.stringify(args.slice(1)))}&interactive`;
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
        displayOutput(stdout.join(''), stderr.join(''));
    }

    function handleException(err) {
        let errorMessage = `Synthesis failed: ${escapeHtml(err.toString())}`;

        if (/stack size exceeded|[Tt]oo much recursion/.test(err.message)) {
            if (!isSafari) {
                errorMessage += "<br>Unfortunately Chrome, Firefox, and the ECMAScript Standard don't support proper tail-call elimination for unfortunate <a href=\"https://stackoverflow.com/a/54721813/377022\">historical</a> <a href=\"https://medium.com/indigoag-eng/tail-call-optimization-in-the-wild-26a10e450c73\">reasons</a>.";

                if (!isMacOrIOS) {
                    errorMessage += "<br>Consider opening this page in <a href=\"https://www.apple.com/safari/\">Safari</a> on a Mac or iOS device instead.";
                } else {
                    errorMessage += "<br>Consider opening this page in <a href=\"https://www.apple.com/safari/\">Safari</a> instead.";
                }
            }
        }

        clearOutput();
        displayError(errorMessage, true);
        updateStatus(""); // Clear status
    }

    function handleSynthesisResult(result, cached) {
        const cachedString = cached ? ` (cached on ${result.timestamp})` : '';
        if (result.success) {
            clearOutput();
            updateStatus(`Synthesis${cachedString} completed in ${result.time} seconds`);
            handleSynthesisResultData(result.result);
        } else {
            handleException(result.result);
            updateStatus(`Synthesis${cachedString} failed in ${result.time} seconds`);
        }
    }

    let synthesisWorker;

    function setupSynthesisWorker() {
        synthesisWorker = new Worker("fiat_crypto_worker.js");

        synthesisWorker.onmessage = function(e) {
            console.log(`Early synthesis result: ${e.data}`);
        };

        synthesisWorker.onerror = function(err) {
            handleException(err);
        };
    }

    function cancelSynthesisWorker() {
        if (synthesisWorker) {
            synthesisWorker.terminate();
            console.log("Synthesis worker terminated.");
        }
        setupSynthesisWorker(); // Re-setup the worker for future use
    }

    function handleSynthesis(args) {
        const startTime = performance.now();
        const cacheKey = 'synthesize_' + JSON.stringify(args);
        const cached = localStorage.getItem(cacheKey);
        console.log({'synthesize args': args});
        updateStatus("Synthesizing...");
        updatePermalink(args);

        if (cached) {
            const cachedData = JSON.parse(cached);
            if (cachedData.version === SYNTHESIS_CACHE_VERSION) {
                handleSynthesisResult(cachedData, true);
                return;
            } else {
                console.log(`cache miss: version ${cachedData.version}, expected ${SYNTHESIS_CACHE_VERSION}`)
            }
        }

        const recieveMessage = function (success) {
            return function(e) {
                const endTime = performance.now();
                const timeTaken = (endTime - startTime) / 1000;
                const now = new Date();
                const resultData = {
                    result: e.data,
                    time: timeTaken,
                    success: success,
                    timestamp: now.toISOString(),
                    version: SYNTHESIS_CACHE_VERSION
                };
                try {
                    localStorage.setItem(cacheKey, JSON.stringify(resultData));
                } catch (e) {
                    console.error(`Failed: localStorage.setItem(${JSON.stringify(cacheKey)}, ${JSON.stringify(JSON.stringify(resultData))})`);
                }
                handleSynthesisResult(resultData, false);
            };
        };

        synthesisWorker.postMessage(args);
        synthesisWorker.onmessage = recieveMessage(true);
        synthesisWorker.onerror = recieveMessage(false);
    }

    function parseAndRun(argv) {
        try {
            let args = parseToStringArray(decodeURIComponent(argv));
            args.unshift('fiat_crypto.js');
            handleSynthesis(args);
        } catch (e) {
            displayError(`Error: ${e.message}: ${argv}`);
        }
    }

    setupSynthesisWorker();

    const queryParams = new URLSearchParams(window.location.search);
    const argv = queryParams.get('argv');
    const interactive = queryParams.get('interactive');

    if (argv) {
        if (interactive !== null && interactive != 'false' && interactive != '0') {
            inputArgs.value = decodeURIComponent(argv);
            document.querySelector('input[value="json"]').checked = true;
            inputForm.classList.remove('hidden');
        }
        parseAndRun(argv);
    } else {
        inputForm.classList.remove('hidden');
    }

    inputArgs.addEventListener('input', validateInput);

    document.querySelectorAll('input[name="inputType"]').forEach(radio => {
        radio.addEventListener('change', function() {
            if (this.value === 'string') {
                if (isValidJsonStringArray(inputArgs.value)) {
                    inputArgs.value = joinWithEscaping(JSON.parse(inputArgs.value));
                }
            } else if (this.value === 'json') {
                inputArgs.value = JSON.stringify(splitUnescapedSpaces(inputArgs.value));
            }
            validateInput();
        });
    });

    synthesizeButton.addEventListener('click', function() {
        // Disable form elements
        inputArgs.disabled = true;
        synthesizeButton.disabled = true;
        cancelButton.disabled = false;
        // Parse arguments and handle synthesis
        const argsType = document.querySelector('input[name="inputType"]:checked').value;
        const args = argsType === 'json' ? JSON.parse(inputArgs.value) : splitUnescapedSpaces(inputArgs.value);
        args.unshift('fiat_crypto.js');
        handleSynthesis(args);
    });

    inputForm.addEventListener('submit', function(event) {
        event.preventDefault(); // Prevent the default form submission
        synthesizeButton.click(); // Programmatically click the synthesize button
    });

    cancelButton.addEventListener('click', function() {
        // Cancel synthesis if possible and re-enable form elements
        inputArgs.disabled = false;
        synthesizeButton.disabled = false;
        cancelButton.disabled = true;
        updateStatus("");
        cancelSynthesisWorker();
    });

    clearCacheButton.addEventListener('click', function() {
        localStorage.clear();
    });
});
