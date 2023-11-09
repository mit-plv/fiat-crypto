#!/bin/sh

# Written mostly by GPT-4 https://web.archive.org/web/20231111233735/https://chat.openai.com/share/8098af96-4a10-4083-bf47-7f9e8cc333ed

# Check if $RANDOM is available
if [ -z "$RANDOM" ]; then
    random="$$"
else
    random="$RANDOM"
fi

# Try to use mktemp if available
if command -v mktemp > /dev/null; then
    # MacOS and some BSDs require a template for mktemp
    if [ "$(uname)" = "Darwin" ] || [ "$(uname)" = "FreeBSD" ]; then
        temp_dir="$(mktemp -d "${TMPDIR:-/tmp}/tmp.XXXXXX")"
    else
        temp_dir="$(mktemp -d 2>/dev/null || mktemp -d -t 'tmp')"
    fi
else
    # Fallback: Create a directory with a random name in TMPDIR or /tmp
    dir="${TMPDIR:-/tmp}/tmp.$random"
    mkdir -p "$dir"
    temp_dir="$dir"
fi

# Output the path of the created directory
printf "%s\n" "$temp_dir"
