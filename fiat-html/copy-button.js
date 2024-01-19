// JavaScript for copy functionality
document.addEventListener('click', function(e) {
    if (e.target.matches('.copy-button')) {
        const button = e.target;
        const targetId = button.getAttribute('data-target');
        const codeText = document.getElementById(targetId).textContent;

        navigator.clipboard.writeText(codeText).then(() => {
            button.textContent = "Copied!";
            button.disabled = true;

            setTimeout(() => {
                button.textContent = "Copy";
                button.disabled = false;
            }, 3000); // Revert after 3 seconds
        });
    }
});
