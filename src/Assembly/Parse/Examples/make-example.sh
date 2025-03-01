#!/bin/sh

cat << EOF
From Coq Require Import String List.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Example example : list string := [
EOF

while read -r line; do
  echo "\"$line\";"
done

echo '""].'
