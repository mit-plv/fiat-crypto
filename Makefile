MOD_NAME := Crypto
SRC_DIR  := src
TIMED?=
TIMECMD?=
STDTIME?=/usr/bin/time -f "$* (real: %e, user: %U, sys: %S, mem: %M ko)"
TIMER=$(if $(TIMED), $(STDTIME), $(TIMECMD))

VERBOSE?=
SHOW := $(if $(VERBOSE),@true "",@echo "")
HIDE := $(if $(VERBOSE),,@)

.PHONY: coq clean update-_CoqProject cleanall install \
	install-coqprime clean-coqprime coqprime \
	specific non-specific

SORT_COQPROJECT = sed 's,[^/]*/,~&,g' | env LC_COLLATE=C sort | sed 's,~,,g'

FAST_TARGETS += archclean clean cleanall printenv clean-old update-_CoqProject Makefile.coq
SUPER_FAST_TARGETS += update-_CoqProject Makefile.coq

COQ_VERSION_PREFIX = The Coq Proof Assistant, version
COQ_VERSION := $(firstword $(subst $(COQ_VERSION_PREFIX),,$(shell "$(COQBIN)coqc" --version 2>/dev/null)))

ifneq ($(filter 8.4%,$(COQ_VERSION)),) # 8.4
# Give us TIMED=1 in Coq 8.4
COQC?=$(TIMER) "$(COQBIN)coqc"
endif

ifneq ($(filter-out $(SUPER_FAST_TARGETS),$(MAKECMDGOALS)),)
-include Makefile.coq
else
ifeq ($(MAKECMDGOALS),)
-include Makefile.coq
endif
endif

.DEFAULT_GOAL := coq

update-_CoqProject::
	$(SHOW)'ECHO > _CoqProject'
	$(HIDE)(echo '-R $(SRC_DIR) $(MOD_NAME)'; echo '-R Bedrock Bedrock'; (git ls-files 'src/*.v' 'Bedrock/*.v' | $(SORT_COQPROJECT))) > _CoqProject

$(VOFILES): | coqprime

# add files to this list to prevent them from being built by default
UNMADE_VOFILES :=

COQ_VOFILES := $(filter-out $(UNMADE_VOFILES),$(VOFILES))
SPECIFIC_VO := $(filter src/Specific/%,$(VOFILES))
NON_SPECIFIC_VO := $(filter-out $(SPECIFIC_VO),$(VO_FILES))

specific: $(SPECIFIC_VO) coqprime
non-specific: $(NON_SPECIFIC_VO) coqprime
coq: $(COQ_VOFILES) coqprime

ifneq ($(filter 8.4%,$(COQ_VERSION)),) # 8.4
COQPRIME_FOLDER := coqprime-8.4
else
COQPRIME_FOLDER := coqprime
ifneq ($(filter 8.5%,$(COQ_VERSION)),) # 8.5
else
OTHERFLAGS ?= -w "-deprecated-appcontext -notation-overridden"
endif
endif

COQPATH?=$(shell pwd)/$(COQPRIME_FOLDER)
export COQPATH

coqprime:
	$(MAKE) -C $(COQPRIME_FOLDER)

clean-coqprime:
	$(MAKE) -C $(COQPRIME_FOLDER) clean

install-coqprime:
	$(MAKE) -C $(COQPRIME_FOLDER) install

Makefile.coq: Makefile _CoqProject
	$(SHOW)'COQ_MAKEFILE -f _CoqProject > $@'
	$(HIDE)$(COQBIN)coq_makefile -f _CoqProject | sed s'|^\(-include.*\)$$|ifneq ($$(filter-out $(FAST_TARGETS),$$(MAKECMDGOALS)),)~\1~else~ifeq ($$(MAKECMDGOALS),)~\1~endif~endif|g' | tr '~' '\n' | sed s'/^clean:$$/clean::/g' | sed s'/^Makefile: /Makefile-old: /g' | sed s'/^printenv:$$/printenv::/g' > $@

clean::
	rm -f Makefile.coq

cleanall:: clean clean-coqprime
	rm -f .dir-locals.el

install: coq install-coqprime

printenv::
	@echo "COQPATH =        $$COQPATH"

.dir-locals.el::
	sed 's:@COQPRIME@:$(COQPRIME_FOLDER):g' .dir-locals.el.in > $@
