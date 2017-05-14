MOD_NAME := Crypto
SRC_DIR  := src
TIMED?=
TIMECMD?=
STDTIME?=/usr/bin/time -f "$* (real: %e, user: %U, sys: %S, mem: %M ko)"
TIMER=$(if $(TIMED), $(STDTIME), $(TIMECMD))

PROFILE?=
VERBOSE?=
SHOW := $(if $(VERBOSE),@true "",@echo "")
HIDE := $(if $(VERBOSE),,@)

.PHONY: coq clean update-_CoqProject cleanall install \
	install-coqprime clean-coqprime coqprime \
	specific-display display \
	specific non-specific

SORT_COQPROJECT = sed 's,[^/]*/,~&,g' | env LC_COLLATE=C sort | sed 's,~,,g' | uniq

FAST_TARGETS += archclean clean cleanall clean-coqprime printenv clean-old update-_CoqProject Makefile.coq
SUPER_FAST_TARGETS += update-_CoqProject Makefile.coq

SLOW :=
ifneq ($(filter-out $(SUPER_FAST_TARGETS),$(MAKECMDGOALS)),)
SLOW := 1
else
ifeq ($(MAKECMDGOALS),)
SLOW := 1
endif
endif

ifneq ($(SLOW),)
COQ_VERSION_PREFIX = The Coq Proof Assistant, version
COQ_VERSION := $(firstword $(subst $(COQ_VERSION_PREFIX),,$(shell "$(COQBIN)coqc" --version 2>/dev/null)))

-include Makefile.coq
endif

-include etc/coq-scripts/Makefile.vo_closure

.DEFAULT_GOAL := coq

update-_CoqProject::
	$(SHOW)'ECHO > _CoqProject'
	$(HIDE)(echo '-R $(SRC_DIR) $(MOD_NAME)'; echo '-R Bedrock Bedrock'; (git ls-files 'src/*.v' 'Bedrock/*.v' | $(SORT_COQPROJECT))) > _CoqProject

$(VOFILES): | coqprime

# add files to this list to prevent them from being built by default
UNMADE_VOFILES := src/SpecificGen/% src/Specific/%Display.vo
# add files to this list to prevent them from being built as final
# targets by the "lite" target
HEAVY_VOFILES := src/Curves/Weierstrass/AffineProofs.vo

COQ_VOFILES := $(filter-out $(UNMADE_VOFILES),$(VOFILES))
SPECIFIC_VO := $(filter src/Specific/%,$(VOFILES))
NON_SPECIFIC_VO := $(filter-out $(SPECIFIC_VO),$(VO_FILES))
SPECIFIC_DISPLAY_VO := $(filter src/Specific/%Display.vo,$(VOFILES))
DISPLAY_VO := $(SPECIFIC_DISPLAY_VO)
DISPLAY_JAVA_VO := $(filter %JavaDisplay.vo,$(DISPLAY_VO))
DISPLAY_NON_JAVA_VO := $(filter-out $(DISPLAY_JAVA_VO),$(DISPLAY_VO))
# computing the reverse_vo_closure is slow, so we only do it if we're
# asked to make the lite target
ifneq ($(filter lite,$(MAKECMDGOALS)),)
LITE_VOFILES := $(filter-out $(call reverse_vo_closure,$(VO_FILES),$(HEAVY_VOFILES)),$(COQ_VOFILES))
endif

specific: $(SPECIFIC_VO) coqprime
non-specific: $(NON_SPECIFIC_VO) coqprime
coq: $(COQ_VOFILES) coqprime
lite: $(LITE_VOFILES) coqprime
specific-display: $(SPECIFIC_DISPLAY_VO:.vo=.log) coqprime
display: $(DISPLAY_VO:.vo=.log) coqprime

COQPRIME_FOLDER := coqprime
ifneq ($(filter 8.5%,$(COQ_VERSION)),) # 8.5
else
ifneq ($(PROFILE),)
OTHERFLAGS ?= -profile-ltac -w "-notation-overridden"
else
OTHERFLAGS ?= -w "-notation-overridden"
endif
endif

COQPATH?=${CURDIR}/$(COQPRIME_FOLDER)
export COQPATH

coqprime:
	$(MAKE) -C $(COQPRIME_FOLDER)

clean-coqprime:
	$(MAKE) -C $(COQPRIME_FOLDER) clean

install-coqprime:
	$(MAKE) -C $(COQPRIME_FOLDER) install

Makefile.coq: Makefile _CoqProject
	$(SHOW)'COQ_MAKEFILE -f _CoqProject > $@'
	$(HIDE)$(COQBIN)coq_makefile -f _CoqProject | sed s'/^clean:$$/clean::/g' | sed s'/^Makefile: /Makefile-old: /g' | sed s'/^printenv:$$/printenv::/g' > $@

$(DISPLAY_NON_JAVA_VO:.vo=.log) : %Display.log : %.vo %Display.v src/Compilers/Z/CNotations.vo src/Specific/IntegrationTestDisplayCommon.vo
	$(SHOW)"COQC $*Display > $@"
	$(HIDE)$(COQC) $(COQDEBUG) $(COQFLAGS) $*Display.v > $@.tmp && mv -f $@.tmp $@

$(DISPLAY_JAVA_VO:.vo=.log) : %JavaDisplay.log : %.vo %JavaDisplay.v src/Compilers/Z/JavaNotations.vo src/Specific/IntegrationTestDisplayCommon.vo
	$(SHOW)"COQC $*JavaDisplay > $@"
	$(HIDE)$(COQC) $(COQDEBUG) $(COQFLAGS) $*JavaDisplay.v > $@.tmp && mv -f $@.tmp $@

src/Specific/x25519_c64.c: src/Specific/x25519_c64.c.sh src/Specific/IntegrationTestLadderstepDisplay.log src/Specific/IntegrationTestMulDisplay.log src/Specific/IntegrationTestSquareDisplay.log
	bash src/Specific/x25519_c64.c.sh > src/Specific/x25519_c64.c

clean::
	rm -f Makefile.coq

cleanall:: clean clean-coqprime

install: coq install-coqprime

printenv::
	@echo "COQPATH =        $$COQPATH"

printdeps::
	$(HIDE)$(foreach vo,$(filter %.vo,$(MAKECMDGOALS)),echo '$(vo): $(call vo_closure,$(vo))'; )

printreversedeps::
	$(HIDE)$(foreach vo,$(filter %.vo,$(MAKECMDGOALS)),echo '$(vo): $(call vo_reverse_closure,$(VOFILES),$(vo))'; )
