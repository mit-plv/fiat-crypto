#!/usr/bin/env bash
set -eu
cd -- "$(dirname -- "$0")"
cd ..

red=$'\033[0;31m'
# No Color
nc=$'\033[0m'
green=$'\033[0;32m'
bold="$(tput bold)"
normal="$(tput sgr0)"
passed_start="${green}${bold}PASSED:${normal}${nc} "
passed_end=""
failed_start="${red}${bold}FAILED:${normal} ${red}"
failed_end="${nc}"

failed_count=0
total_count=0

while IFS= read -r line; do
    total_count=$((total_count + 1))
    eval $line 2>/dev/null >/dev/null && echo "${passed_start}${line}${passed_end}" || {
            echo "${failed_start}${line}${failed_end}";
            failed_count=$((failed_count + 1))
        };
done < <(fiat-amd64/gentest.py fiat-amd64/*.asm)

if [[ ${failed_count} == 0 ]]; then
    echo "${green}${bold}ALL ${total_count} TESTS PASSED${normal}${nc}"
else
    echo "${green}${bold}PASSED:${normal}${green} $((total_count - failed_count))${nc} / ${total_count}"
    echo "${red}${bold}FAILED:${normal}${red} ${failed_count}${nc} / ${total_count}"
    exit 1
fi
