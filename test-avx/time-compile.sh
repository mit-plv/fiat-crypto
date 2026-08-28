#!/bin/bash
# Timed compile of SymbolicProofs.v — shows where it gets stuck or slow.
# Usage: ./test-avx/time-compile.sh
# Hit Ctrl-C when it hangs, then check /tmp/symproofs-timing.log

FILE=src/Assembly/WithBedrock/SymbolicProofs.v
LOG=/tmp/symproofs-timing.log

rocq compile -time -q \
  -w '+implicit-core-hint-db,+implicits-in-term,+non-reversible-notation,+deprecated-intros-until-0,+deprecated-focus,+unused-intro-pattern,+variable-collision,+unexpected-implicit-declaration,+omega-is-deprecated,+deprecated-instantiate-syntax,+non-recursive,+undeclared-scope,+deprecated-hint-rewrite-without-locality,+deprecated-hint-without-locality,+deprecated-instance-without-locality,+deprecated-typeclasses-transparency-without-locality,+fragile-hint-constr,-deprecated-since-9.0,-deprecated-since-8.20,-deprecated-from-Coq' \
  -w -notation-overridden,-native-compiler-disabled,-ambiguous-paths,-masking-absolute-name \
  -w -deprecated-native-compiler-option \
  -native-compiler ondemand \
  -I rewriter/src/Rewriter/Util/plugins \
  -Q coqprime/src/Coqprime Coqprime \
  -Q rupicola/bedrock2/deps/coqutil/src/coqutil coqutil \
  -Q rupicola/src/Rupicola Rupicola \
  -Q rupicola/bedrock2/bedrock2/src/bedrock2 bedrock2 \
  -Q rupicola/bedrock2/bedrock2/src/bedrock2Examples bedrock2Examples \
  -Q rupicola/bedrock2/compiler/src/compiler compiler \
  -Q rupicola/bedrock2/deps/riscv-coq/src/riscv riscv \
  -Q rewriter/src/Rewriter Rewriter \
  -R src Crypto \
  "$FILE" 2>&1 | tee "$LOG"

echo ""
echo "=== SLOW SENTENCES (>1s) ==="
grep -E '^\s*Chars.*[0-9]{2,}\. secs' "$LOG" | while read line; do
  offset=$(echo "$line" | grep -oE 'Chars [0-9]+' | grep -oE '[0-9]+')
  echo "$line"
  echo "  -> $(head -c $((offset + 80)) "$FILE" | tail -c 80)"
  echo ""
done

echo "=== LAST SENTENCE PROCESSED ==="
tail -1 "$LOG" | while read line; do
  offset=$(echo "$line" | grep -oE 'Chars [0-9]+ - [0-9]+' | grep -oE '[0-9]+' | tail -1)
  echo "$line"
  echo "  -> source around char $offset:"
  echo "  -> $(head -c $((offset + 120)) "$FILE" | tail -c 120)"
done
