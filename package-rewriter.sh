#!/usr/bin/env bash

FILES="$(make --dry-run --always-make src/RewriterExamples.vo | grep -o 'src/.*\.v' | grep -v Coqprime | uniq | sort)"
rm -rf rewriting
mkdir rewriting
cat > rewriting/_CoqProject <<EOF
-R src Rewriting
EOF

for i in $FILES; do
    mkdir -p rewriting/$(dirname $i)
    sed s'/Crypto\./Rewriting./g' $i > rewriting/$i
    echo $i >> rewriting/_CoqProject
done

cat > rewriting/Makefile <<'EOF'

.DEFAULT_GOAL := all

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f $< -o $@

%: Makefile.coq
	$(MAKE) --no-print-directory -f Makefile.coq $(MAKECMDGOALS)
EOF

rm -rf rewriting.tar.gz
tar -czvf rewriting.tar.gz rewriting/
