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
	specific non-specific

SORT_COQPROJECT = sed 's,[^/]*/,~&,g' | env LC_COLLATE=C sort | sed 's,~,,g'

FAST_TARGETS += archclean clean cleanall clean-coqprime printenv clean-old update-_CoqProject Makefile.coq
SUPER_FAST_TARGETS += update-_CoqProject Makefile.coq

COQ_VERSION_PREFIX = The Coq Proof Assistant, version
COQ_VERSION := $(firstword $(subst $(COQ_VERSION_PREFIX),,$(shell "$(COQBIN)coqc" --version 2>/dev/null)))

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
UNMADE_VOFILES := src/SpecificGen/% src/Specific/%Display.vo
# add files to this list to prevent them from being built by the "lite" target
HEAVY_VOFILES := src/WeierstrassCurve/WeierstrassCurveTheorems.vo

COQ_VOFILES := $(filter-out $(UNMADE_VOFILES),$(VOFILES))
LITE_VOFILES := $(filter-out $(HEAVY_VOFILES),$(COQ_VOFILES))
SPECIFIC_VO := $(filter src/Specific/%,$(VOFILES))
NON_SPECIFIC_VO := $(filter-out $(SPECIFIC_VO),$(VO_FILES))

specific: $(SPECIFIC_VO) coqprime
non-specific: $(NON_SPECIFIC_VO) coqprime
coq: $(COQ_VOFILES) coqprime
lite: $(LITE_VOFILES) coqprime

COQPRIME_FOLDER := coqprime
ifneq ($(filter 8.5%,$(COQ_VERSION)),) # 8.5
else
ifneq ($(PROFILE),)
OTHERFLAGS ?= -profile-ltac -w "-deprecated-appcontext -notation-overridden"
else
OTHERFLAGS ?= -w "-deprecated-appcontext -notation-overridden"
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
	$(HIDE)$(COQBIN)coq_makefile -f _CoqProject | sed s'|^\(-include.*\)$$|ifneq ($$(filter-out $(FAST_TARGETS),$$(MAKECMDGOALS)),)~\1~else~ifeq ($$(MAKECMDGOALS),)~\1~endif~endif|g' | tr '~' '\n' | sed s'/^clean:$$/clean::/g' | sed s'/^Makefile: /Makefile-old: /g' | sed s'/^printenv:$$/printenv::/g' > $@

#$(DISPLAY_NON_JAVA_VO:.vo=.log) : %Display.log : %.vo %Display.v src/Reflection/Z/CNotations.vo
#	$(SHOW)"COQC $*Display > $@"
#	$(HIDE)$(COQC) $(COQDEBUG) $(COQFLAGS) $*Display.v > $@.tmp && mv -f $@.tmp $@
#
#$(DISPLAY_JAVA_VO:.vo=.log) : %JavaDisplay.log : %.vo %JavaDisplay.v src/Reflection/Z/JavaNotations.vo
#	$(SHOW)"COQC $*JavaDisplay > $@"
#	$(HIDE)$(COQC) $(COQDEBUG) $(COQFLAGS) $*JavaDisplay.v > $@.tmp && mv -f $@.tmp $@

clean::
	rm -f Makefile.coq

cleanall:: clean clean-coqprime
	rm -f .dir-locals.el

install: coq install-coqprime

printenv::
	@echo "COQPATH =        $$COQPATH"

.dir-locals.el::
	sed 's:@COQPRIME@:$(COQPRIME_FOLDER):g' .dir-locals.el.in > $@

-include etc/coq-scripts/Makefile.vo_closure
printdeps::
	$(HIDE)$(foreach vo,$(filter %.vo,$(MAKECMDGOALS)),echo '$(vo): $(call vo_closure,$(vo))'; )
