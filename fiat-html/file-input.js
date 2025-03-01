(function () {

    // Function to create a new file entry
    function createFileEntry(filename, content) {
        filename = filename || '';
        content = content || '';
        const fileEntryHTML = `
            <div class="file-entry">
                <input type="text" class="file-name" placeholder="Filename">
                <textarea class="file-content" placeholder="File content"></textarea>
                <button type="button" class="remove-btn">-</button>
            </div>
        `;

        const template = document.createElement('template');
        template.innerHTML = fileEntryHTML.trim();
        const entry = template.content.firstElementChild.cloneNode(true);

        const nameInput = entry.querySelector('.file-name');
        const contentTextarea = entry.querySelector('.file-content');
        const removeButton = entry.querySelector('.remove-btn');

        nameInput.value = filename;
        contentTextarea.value = content;
        // Update placeholder based on filename
        const updatePlaceholder = () => {
            const filename = nameInput.value.trim();
            contentTextarea.placeholder = filename ? `${filename} contents` : 'File content';
        };

        // Set initial placeholder
        updatePlaceholder();

        // Add event listener to update placeholder when filename changes
        nameInput.addEventListener('input', updatePlaceholder);

        removeButton.addEventListener('click', function () {
            entry.remove();
            updateFilesValue();
        });

        nameInput.addEventListener('input', updateFilesValue);
        contentTextarea.addEventListener('input', updateFilesValue);

        return entry;
    }

    function createStdinEntry(line) {
        line = line || '';
        const stdinEntryHTML = `
            <div class="stdin-entry">
                <textarea class="stdin-textarea" placeholder="Enter stdin"></textarea>
                <button type="button" class="remove-btn">-</button>
            </div>
        `;

        const template = document.createElement('template');
        template.innerHTML = stdinEntryHTML.trim();
        const entry = template.content.firstElementChild.cloneNode(true);

        entry.querySelector('.stdin-textarea').value = line;

        const removeButton = entry.querySelector('.remove-btn');
        removeButton.addEventListener('click', function () {
            entry.remove();
            updateStdinValue();
        });

        return entry;
    }


    function getStdinFromFormBoxRaw() {
        const stdinBox = document.getElementById('stdinTextArea');
        return stdinBox.value;
    }

    function getFilesFromFormBoxRaw() {
        const filesBox = document.getElementById('filesTextArea');
        return filesBox.value;
    }


    function getStdinFromFormBox() {
        return JSON.parse(getStdinFromFormBoxRaw() || '[]');
    }

    function getFilesFromFormBox() {
        return JSON.parse(getFilesFromFormBoxRaw() || '{}');
    }

    function populateStdinEntries(stdin) {
        const stdinEntries = document.getElementById('stdinEntries');

        if (stdin === undefined) {
            stdin = getStdinFromFormBox();
        }
        const entries = stdinEntries.querySelectorAll('.stdin-entry');
        entries.forEach(entry => {
            entry.remove();
        });
        stdin.forEach(line => {
            const entry = createStdinEntry(line);
            stdinEntries.appendChild(entry);
        });
    }

    function populateFileEntries(files) {
        const fileEntries = document.getElementById('fileEntries');

        if (files === undefined) {
            files = getFilesFromFormBox();
        }
        const entries = fileEntries.querySelectorAll('.file-entry');
        entries.forEach(entry => {
            entry.remove();
        });
        Object.entries(files).forEach(([filename, content]) => {
            const entry = createFileEntry(filename, content);
            fileEntries.appendChild(entry);
        });
    }

    // Function to update the hidden stdin input value
    function updateStdinValue() {
        const stdinEntries = document.getElementById('stdinEntries');
        const stdinBox = document.getElementById('stdinTextArea');
        const entries = stdinEntries.querySelectorAll('.stdin-entry');
        const stdinArray = Array.from(entries).map(entry => {
            const textarea = entry.querySelector('.stdin-textarea');
            return textarea.value.split('\n').map(line => line + '\n');
        });
        stdinBox.value = JSON.stringify(stdinArray);
    }

    // Function to update the hidden files input value
    function updateFilesValue() {
        const fileEntries = document.getElementById('fileEntries');
        const filesBox = document.getElementById('filesTextArea');
        const entries = fileEntries.querySelectorAll('.file-entry');
        const filesObj = {};

        Array.from(entries).forEach(entry => {
            const nameInput = entry.querySelector('.file-name');
            const contentTextarea = entry.querySelector('.file-content');

            if (nameInput.value.trim()) {
                filesObj[nameInput.value] = contentTextarea.value.split('\n').map(line => line + '\n');
            }
        });

        filesBox.value = JSON.stringify(filesObj);
    }

    window.getStdinFromFormBox = getStdinFromFormBox;
    window.getFilesFromFormBox = getFilesFromFormBox;
    window.getStdinFromFormBoxRaw = getStdinFromFormBoxRaw;
    window.getFilesFromFormBoxRaw = getFilesFromFormBoxRaw;
    window.populateStdinEntries = populateStdinEntries;
    window.populateFileEntries = populateFileEntries;

    document.addEventListener('DOMContentLoaded', function () {
        const addStdinButton = document.getElementById('addStdinButton');
        const addFileButton = document.getElementById('addFileButton');

        // Add event listeners for adding new entries
        addStdinButton.addEventListener('click', function () {
            stdinEntries.appendChild(createStdinEntry());
        });

        addFileButton.addEventListener('click', function () {
            fileEntries.appendChild(createFileEntry());
        });

        populateStdinEntries();
        populateFileEntries();
    });
})();
