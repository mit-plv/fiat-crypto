# © 2012–2015 the Massachusetts Institute of Technology
# @author bbaren + rsloan

COQC = coqc
COQDEP = coqdep

COMPILE.v = $(COQC) -q $(COQLIBS)

.PHONY: check_fiat check_bedrock

check_fiat:
	@perl -e \
		'if(! -d "./fiat") { print("you need to link fiat to ./fiat\n"); exit(1) }'

check_bedrock:
	@perl -e \
		'if(! -d "./bedrock") { print("you need to link bedrock to ./bedrock\n"); exit(1) }'

%.vo %.glob: %.v.d
	$(COMPILE.v) $*

%.v.d: %.v
	@$(COQDEP) -I . $(COQLIBS) "$<" >"$@" \
	  || (RV=$$?; rm -f "$@"; exit $${RV})

define coq-generated
$1.vo $1.v.d $1.glob
endef
