#!/usr/bin/env bash

cd "$( dirname "${BASH_SOURCE[0]}" )"

cat <<EOF
(** * Generic Tactics *)
Require Export Crypto.Util.FixCoqMistakes.
EOF
FILES="$(cd Tactics; git ls-files '*.v' | env LC_COLLATE=C sort)"
for i in $FILES; do
    echo "Require Export Crypto.Util.Tactics.${i%.v}."
done
