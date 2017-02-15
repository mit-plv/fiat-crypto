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
	display \
	specific non-specific \
	small-specific-gen medium-specific-gen specific-gen \
	extraction ghc

SORT_COQPROJECT = sed 's,[^/]*/,~&,g' | env LC_COLLATE=C sort | sed 's,~,,g'

FAST_TARGETS += archclean clean cleanall clean-coqprime printenv clean-old update-_CoqProject Makefile.coq
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
UNMADE_VOFILES := src/SpecificGen/%

COQ_VOFILES := $(filter-out $(UNMADE_VOFILES),$(VOFILES))
SPECIFIC_VO := $(filter src/Specific/%,$(VOFILES))
SPECIFIC_GEN_VO := $(filter src/SpecificGen/%,$(VOFILES))
MEDIUM_SPECIFIC_GEN_VO := $(filter-out src/SpecificGen/GF5211_32%,$(SPECIFIC_GEN_VO))
SMALL_SPECIFIC_GEN_VO := $(filter-out src/SpecificGen/GF41417_32%,$(MEDIUM_SPECIFIC_GEN_VO))
NON_SPECIFIC_VO := $(filter-out $(SPECIFIC_VO),$(VO_FILES))
DISPLAY_VO := $(filter src/Specific/%Display.vo src/SpecificGen/%Display.vo,$(VOFILES))
DISPLAY_JAVA_VO := $(filter src/Specific/%JavaDisplay.vo src/SpecificGen/%JavaDisplay.vo,$(DISPLAY_VO))
DISPLAY_NON_JAVA_VO := $(filter-out $(DISPLAY_JAVA_VO),$(DISPLAY_VO))

specific: $(SPECIFIC_VO) coqprime
specific-gen: $(SPECIFIC_GEN_VO) coqprime
medium-specific-gen: $(MEDIUM_SPECIFIC_GEN_VO) coqprime
small-specific-gen: $(SMALL_SPECIFIC_GEN_VO) coqprime
non-specific: $(NON_SPECIFIC_VO) coqprime
display: $(DISPLAY_VO:.vo=.log) coqprime
coq: $(COQ_VOFILES) coqprime

ifneq ($(filter 8.4%,$(COQ_VERSION)),) # 8.4
COQPRIME_FOLDER := coqprime-8.4
else
COQPRIME_FOLDER := coqprime
ifneq ($(filter 8.5%,$(COQ_VERSION)),) # 8.5
else
ifneq ($(PROFILE),)
OTHERFLAGS ?= -profile-ltac -w "-deprecated-appcontext -notation-overridden"
else
OTHERFLAGS ?= -w "-deprecated-appcontext -notation-overridden"
endif
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

$(DISPLAY_NON_JAVA_VO:.vo=.log) : %Display.log : %.vo %Display.v src/Reflection/Z/CNotations.vo
	$(SHOW)"COQC $*Display > $@"
	$(HIDE)$(COQC) $(COQDEBUG) $(COQFLAGS) $*Display.v > $@.tmp && mv -f $@.tmp $@

$(DISPLAY_JAVA_VO:.vo=.log) : %JavaDisplay.log : %.vo %JavaDisplay.v src/Reflection/Z/CNotations.vo
	$(SHOW)"COQC $*JavaDisplay > $@"
	$(HIDE)$(COQC) $(COQDEBUG) $(COQFLAGS) $*JavaDisplay.v > $@.tmp && mv -f $@.tmp $@

src/Experiments/Ed25519_noimports.hs: src/Experiments/Ed25519Extraction.vo src/Experiments/Ed25519Extraction.v

src/Experiments/Ed25519.hs: src/Experiments/Ed25519_noimports.hs src/Experiments/Ed25519_imports.hs
	( cd src/Experiments && \
		( < Ed25519_noimports.hs \
		sed "/import qualified Prelude/r Ed25519_imports.hs" | \
	  sed 's/ Ed25519_noimports / Ed25519 /g' \
		&& echo -e '{-# INLINE mul1 #-} \n{-# INLINE add2 #-} \n{-# INLINE sub3 #-}' ) \
		> Ed25519.hs )

src/Experiments/X25519.hs: src/Experiments/X25519_noimports.hs src/Experiments/Ed25519_imports.hs
	( cd src/Experiments && \
		( < X25519_noimports.hs \
		sed "/import qualified Prelude/r Ed25519_imports.hs" | \
	  sed 's/ X25519_noimports / X25519 /g' \
		&& echo -e '{-# INLINE mul #-} \n{-# INLINE sub0 #-} \n{-# INLINE add #-}' ) \
		> X25519.hs )

src/Experiments/Ed25519.o: src/Experiments/Ed25519.hs
	( cd src/Experiments && ghc -XStrict -O3 Ed25519.hs )

src/Experiments/X25519.o: src/Experiments/X25519.hs
	( cd src/Experiments && ghc -XStrict -O3 X25519.hs )

extraction: src/Experiments/Ed25519.hs src/Experiments/X25519.hs
ghc: src/Experiments/Ed25519.o src/Experiments/X25519.o

clean::
	rm -f Makefile.coq

cleanall:: clean clean-coqprime
	rm -f .dir-locals.el

install: coq install-coqprime

printenv::
	@echo "COQPATH =        $$COQPATH"

.dir-locals.el::
	sed 's:@COQPRIME@:$(COQPRIME_FOLDER):g' .dir-locals.el.in > $@
