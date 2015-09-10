# © 2012–2015 the Massachusetts Institute of Technology
# @author bbaren + rsloan

COQC = coqc
COQDEP = coqdep

COMPILE.v = $(COQC) -q $(COQLIBS)

.PHONY: check_fiat

check_fiat:
	@perl -e \
		'if(! -d "./fiat") { print("you need to link fiat to ./fiat\n"); exit(1) }'

%.vo %.glob: check_fiat %.v
	$(COMPILE.v) $*

%.v.d: check_fiat %.v
	@$(COQDEP) -I . $(COQLIBS) "$<" >"$@" \
	  || (RV=$$?; rm -f "$@"; exit $${RV})

define coq-generated
$1.vo $1.v.d $1.glob
endef
