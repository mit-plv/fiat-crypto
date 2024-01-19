#!/bin/sh

for i in $(find . -name "*.v.timing" | sort); do
    echo "::group::$i"
    cat "$i"
    echo "::endgroup::"
done
