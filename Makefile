MOD_NAME := Crypto
SRC_DIR  := src

.PHONY: coq clean install coqprime-8.4 coqprime-8.5 coqprime update-_CoqProject
.DEFAULT_GOAL := coq

VERBOSE = 0

SILENCE_COQC_0 = @echo "COQC $<"; #
SILENCE_COQC_1 =
SILENCE_COQC = $(SILENCE_COQC_$(VERBOSE))

SILENCE_COQDEP_0 = @echo "COQDEP $<"; #
SILENCE_COQDEP_1 =
SILENCE_COQDEP = $(SILENCE_COQDEP_$(VERBOSE))

SORT_COQPROJECT = sed 's,[^/]*/,~&,g' | env LC_COLLATE=C sort | sed 's,~,,g'

update-_CoqProject::
	$(Q)(echo '-R $(SRC_DIR) $(MOD_NAME)'; echo '-R Bedrock Bedrock'; (git ls-files 'src/*.v' 'Bedrock/*.v' | $(SORT_COQPROJECT))) > _CoqProject

coq: coqprime Makefile.coq
	$(MAKE) -f Makefile.coq

COQ_VERSION_PREFIX = The Coq Proof Assistant, version
COQ_VERSION := $(firstword $(subst $(COQ_VERSION_PREFIX),,$(shell $(COQBIN)coqc --version 2>/dev/null)))

ifneq ($(filter 8.5%,$(COQ_VERSION)),) # 8.5
coqprime: coqprime-8.5
else
coqprime: coqprime-8.4
endif

coqprime-8.4:
	$(MAKE) -C coqprime-8.4

coqprime-8.5:
	$(MAKE) -C coqprime

Makefile.coq: Makefile _CoqProject
	$(Q)$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

install: coq Makefile.coq
	$(MAKE) -f Makefile.coq install
	$(MAKE) -C coqprime install
