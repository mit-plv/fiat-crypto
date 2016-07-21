MOD_NAME := Crypto
SRC_DIR  := src

.PHONY: coq clean update-_CoqProject cleanall install \
	install-coqprime clean-coqprime coqprime
.DEFAULT_GOAL := coq

SORT_COQPROJECT = sed 's,[^/]*/,~&,g' | env LC_COLLATE=C sort | sed 's,~,,g'

update-_CoqProject::
	$(Q)(echo '-R $(SRC_DIR) $(MOD_NAME)'; echo '-R Bedrock Bedrock'; (git ls-files 'src/*.v' 'Bedrock/*.v' | $(SORT_COQPROJECT))) > _CoqProject

coq: coqprime Makefile.coq
	$(MAKE) -f Makefile.coq

COQ_VERSION_PREFIX = The Coq Proof Assistant, version
COQ_VERSION := $(firstword $(subst $(COQ_VERSION_PREFIX),,$(shell $(COQBIN)coqc --version 2>/dev/null)))

ifneq ($(filter 8.4%,$(COQ_VERSION)),) # 8.4
COQPRIME_FOLDER := coqprime-8.4
else
COQPRIME_FOLDER := coqprime
endif

coqprime:
	$(MAKE) -C $(COQPRIME_FOLDER)

clean-coqprime:
	$(MAKE) -C $(COQPRIME_FOLDER) clean

install-coqprime:
	$(MAKE) -C $(COQPRIME_FOLDER) install

Makefile.coq: Makefile _CoqProject
	$(Q)$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

cleanall: clean clean-coqprime
	rm -f .dir-locals.el

install: coq Makefile.coq
	$(MAKE) install-coqprime
	$(MAKE) -f Makefile.coq install

.dir-locals.el::
	sed 's:@COQPRIME@:$(COQPRIME_FOLDER):g' .dir-locals.el.in > $@
