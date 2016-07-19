MOD_NAME := Crypto
SRC_DIR  := src
STDTIME?=/usr/bin/time -f "$* (real: %e, user: %U, sys: %S, mem: %M ko)"

.PHONY: coq clean update-_CoqProject cleanall install \
	install-coqprime clean-coqprime coqprime \
	specific non-specific
.DEFAULT_GOAL := coq

-include Makefile.submodule

STRICT_COQDEP ?= 1

-include etc/coq-scripts/Makefile.coq.common

update-_CoqProject::
	$(SHOW)'ECHO > _CoqProject'
	$(HIDE)(echo '-R $(SRC_DIR) $(MOD_NAME)'; echo '-R Bedrock Bedrock'; (git ls-files 'src/*.v' 'Bedrock/*.v' | $(SORT_COQPROJECT))) > _CoqProject

clean::
	rm -f submodule-update

$(VOFILES): | coqprime

# add files to this list to prevent them from being built by default
UNMADE_VOFILES :=

COQ_VOFILES := $(filter-out $(UNMADE_VOFILES),$(VOFILES))
SPECIFIC_VO := $(filter src/Specific/%,$(VOFILES))
NON_SPECIFIC_VO := $(filter-out $(SPECIFIC_VO),$(VO_FILES))

specific: $(SPECIFIC_VO) coqprime
non-specific: $(NON_SPECIFIC_VO) coqprime
coq: $(COQ_VOFILES) coqprime

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

cleanall:: clean clean-coqprime
	rm -f .dir-locals.el

install: coq install-coqprime

.dir-locals.el::
	sed 's:@COQPRIME@:$(COQPRIME_FOLDER):g' .dir-locals.el.in > $@
