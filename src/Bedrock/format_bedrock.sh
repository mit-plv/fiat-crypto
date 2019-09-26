#! /bin/bash

sed 's/expr\.[a-z]* //g' | sed 's/constr:(\(["a-z0-9]*\))/\1/g' | sed 's/constr://g' | sed 's/bedrock_expr://g' | sed 's/bopname\.//g' | sed 's/"//g' | clang-format
