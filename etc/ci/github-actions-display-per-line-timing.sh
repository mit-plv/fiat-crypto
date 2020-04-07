#!/usr/bin/env bash

for i in $(find -name "*.v.timing" | sort); do
    echo "::group::$i"
    cat "$i"
    echo "::endgroup::"
done
