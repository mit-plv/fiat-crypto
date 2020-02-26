.SUFFIXES:

MOD_NAME := Crypto
SRC_DIR  := src
TIMED?=
TIMECMD?=
STDTIME?=/usr/bin/time -f "$@ (real: %e, user: %U, sys: %S, mem: %M ko)"
TIMER=$(if $(TIMED), $(STDTIME), $(TIMECMD))
TIMECMD_FULL?=
STDTIME_FULL?=/usr/bin/time -f "$@ (real: %e, user: %U, sys: %S, mem: %M ko)"
TIMER_FULL=$(if $(TIMED), $(STDTIME_FULL), $(TIMECMD_FULL))

GHC?=ghc
GHCFLAGS?= # -XStrict

PROFILE?=
VERBOSE?=
SHOW := $(if $(VERBOSE),@true "",@echo "")
HIDE := $(if $(VERBOSE),,@)
INSTALLDEFAULTROOT := Crypto

# Set this is ADX is not present
SKIP_ICC?=

.PHONY: coq clean update-_CoqProject cleanall install \
	install-coqprime clean-coqprime coqprime coqprime-all \
	old-pipeline-nobigmem print-old-pipeline-nobigmem \
	old-pipeline-lite print-old-pipeline-lite \
	coq-without-new-pipeline \
	nobigmem print-nobigmem \
	util some-early \
	specific-c specific-display display \
	specific non-specific lite only-heavy printlite lite-display print-lite-display lite-display-test \
	new-pipeline pre-standalone \
	curves-proofs no-curves-proofs no-curves-proofs-non-specific \
	selected-specific selected-specific-display selected-specific-display-test nonautogenerated-specific nonautogenerated-specific-display nonautogenerated-c build-selected-test selected-test build-selected-bench selected-bench selected-c \
	build-test test build-bench bench c \
	standalone standalone-haskell standalone-ocaml \
	print-nonautogenerated-specific print-nonautogenerated-specific-display nonautogenerated-specific-display-test \
	print-old-pipeline-lite-hardcoded old-pipeline-lite-hardcoded lite-display-hardcoded lite-display-test-hardcoded \
	print-old-pipeline-nobigmem-hardcoded old-pipeline-nobigmem-hardcoded \
	regenerate-curves

SORT_COQPROJECT = sed 's,[^/]*/,~&,g' | env LC_COLLATE=C sort | sed 's,~,,g' | uniq

FAST_TARGETS += archclean clean cleanall clean-coqprime printenv clean-old update-_CoqProject regenerate-curves Makefile.coq
SUPER_FAST_TARGETS += update-_CoqProject Makefile.coq regenerate-curves only-test-c-files

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

ifeq ($(filter curves-proofs no-curves-proofs no-curves-proofs-non-specific selected-specific selected-specific-display lite only-heavy printdeps printreversedeps printlite print-lite-display lite-display lite-display-test nobigmem print-nobigmem new-pipeline pre-standalone old-pipeline-nobigmem print-old-pipeline-nobigmem old-pipeline-lite print-old-pipeline-lite util,$(MAKECMDGOALS)),)
-include etc/coq-scripts/Makefile.vo_closure
else
include etc/coq-scripts/Makefile.vo_closure
endif

.DEFAULT_GOAL := coq

update-_CoqProject::
	$(SHOW)'ECHO > _CoqProject'
	$(HIDE)(echo '-R $(SRC_DIR) $(MOD_NAME)'; echo '-R bbv/src/bbv bbv'; ((git ls-files 'src/*.v'; (git submodule foreach 'git ls-files "*.v" 2>/dev/null | sed "s|^|$$path/|"' | grep 'bbv/')) | $(SORT_COQPROJECT))) > _CoqProject

# add files to this list to prevent them from being built by default
UNMADE_VOFILES :=
UNMADE_C_FILES := \
	src/Specific/X25519/C64/fesub.c src/Specific/X25519/C64/feadd.c src/Specific/X25519/C64/fecarry.c \
	src/Specific/X25519/C64/fesub.h src/Specific/X25519/C64/feadd.h src/Specific/X25519/C64/fecarry.h \
	src/Specific/X25519/C32/fesub.c src/Specific/X25519/C32/feadd.c src/Specific/X25519/C32/fecarry.c \
	src/Specific/X25519/C32/fesub.h src/Specific/X25519/C32/feadd.h src/Specific/X25519/C32/fecarry.h
# files that are treated specially
SPECIAL_VOFILES := \
	src/Specific/%Display.vo \
	src/Experiments/NewPipeline/ExtractionOCaml/%.vo \
	src/Experiments/NewPipeline/ExtractionHaskell/%.vo
SPECIFIC_GENERATED_VOFILES := src/Specific/solinas%.vo src/Specific/montgomery%.vo
# add files to this list to prevent them from being built as final
# targets by the "lite" target
NEW_PIPELINE_FILTER := src/Experiments/NewPipeline/%
LITE_UNMADE_VOFILES := src/Curves/Weierstrass/AffineProofs.vo \
	src/Curves/Weierstrass/Jacobian.vo \
	src/Curves/Weierstrass/Projective.vo \
	src/Specific/X2448/Karatsuba/C64/fe%.vo \
	src/Specific/NISTP256/AMD64/fe%.vo \
	src/Specific/NISTP256/AMD128/fe%.vo \
	src/Specific/X25519/C64/ladderstep.vo \
	src/Specific/X25519/C32/fe%.vo \
	src/Experiments/NewPipeline/RewriterWf1.vo \
	src/Experiments/NewPipeline/RewriterWf2.vo \
	src/Experiments/NewPipeline/RewriterRulesGood.vo \
	src/Experiments/NewPipeline/RewriterProofs.vo \
	src/Experiments/NewPipeline/Toplevel2.vo \
	src/Experiments/NewPipeline/SlowPrimeSynthesisExamples.vo \
	src/Experiments/SimplyTypedArithmetic.vo \
	$(SPECIFIC_GENERATED_VOFILES)
NOBIGMEM_UNMADE_VOFILES := \
	src/Curves/Weierstrass/AffineProofs.vo \
	src/Curves/Weierstrass/Jacobian.vo \
	src/Curves/Weierstrass/Projective.vo \
	$(SPECIFIC_GENERATED_VOFILES)
OLD_PIPELINE_LITE_UNMADE_VOFILES := $(LITE_UNMADE_VOFILES) $(NEW_PIPELINE_FILTER)
OLD_PIPELINE_NOBIGMEM_UNMADE_VOFILES := $(NOBIGMEM_UNMADE_VOFILES) $(NEW_PIPELINE_FILTER)
REGULAR_VOFILES := $(filter-out $(SPECIAL_VOFILES) $(UNMADE_VOFILES),$(VOFILES))
CURVES_PROOFS_PRE_VOFILES := $(filter src/Curves/Weierstrass/Jacobian.vo src/Curves/%Proofs.vo,$(REGULAR_VOFILES))
NO_CURVES_PROOFS_UNMADE_VOFILES := src/Curves/Weierstrass/AffineProofs.vo \
	src/Curves/Weierstrass/Jacobian.vo
NO_CURVES_PROOFS_NON_SPECIFIC_UNMADE_VOFILES := $(filter $(NO_CURVES_PROOFS_UNMADE_VOFILES) src/Specific/%.vo,$(VOFILES))
REAL_SPECIFIC_GENERATED_VOFILES := $(filter $(SPECIFIC_GENERATED_VOFILES),$(VOFILES))
NEW_PIPELINE_PRE_VOFILES := $(filter $(NEW_PIPELINE_FILTER),$(REGULAR_VOFILES))
PRE_STANDALONE_PRE_VOFILES := $(filter src/Experiments/NewPipeline/Standalone%.vo,$(REGULAR_VOFILES))
UTIL_PRE_VOFILES := $(filter bbv/%.vo src/Algebra/%.vo src/Tactics/%.vo src/Util/%.vo,$(REGULAR_VOFILES))
COQ_WITHOUT_NEW_PIPELINE_VOFILES := $(filter-out $(NEW_PIPELINE_FILTER),$(REGULAR_VOFILES))
SOME_EARLY_VOFILES := \
	src/Experiments/NewPipeline/Arithmetic.vo \
	src/Experiments/NewPipeline/Rewriter.vo \
	src/Experiments/SimplyTypedArithmetic.vo

SELECTED_PATTERN := \
	src/Specific/X25519/C64/% \
	src/Specific/X25519/C32/Synthesis.vo \
	src/Specific/NISTP256/AMD64/% \
	src/Specific/NISTP256/AMD128/Synthesis.vo \
	src/Specific/NISTP256/FancyMachine256/% \
	third_party/%
SELECTED_SPECIFIC_PRE_VOFILES := $(filter $(SELECTED_PATTERN),$(REGULAR_VOFILES))

COQ_VOFILES := $(filter-out $(SPECIFIC_GENERATED_VOFILES),$(REGULAR_VOFILES))
FILESTOINSTALL := $(filter-out $(SPECIFIC_GENERATED_VOFILES),$(FILESTOINSTALL))
SPECIFIC_VO := $(filter src/Specific/%,$(REGULAR_VOFILES))
NONAUTOGENERATED_SPECIFIC_VO := $(filter-out $(SPECIFIC_GENERATED_VOFILES),$(SPECIFIC_VO))
NON_SPECIFIC_VO := $(filter-out $(SPECIFIC_VO),$(REGULAR_VOFILES))
SPECIFIC_DISPLAY_VO := $(filter src/Specific/%Display.vo,$(filter-out $(UNMADE_VOFILES),$(VOFILES)))
NONAUTOGENERATED_SPECIFIC_DISPLAY_VO := $(filter-out $(SPECIFIC_GENERATED_VOFILES),$(SPECIFIC_DISPLAY_VO))
DISPLAY_VO := $(SPECIFIC_DISPLAY_VO)
DISPLAY_JAVA_VO := $(filter %JavaDisplay.vo,$(DISPLAY_VO))
DISPLAY_NON_JAVA_VO := $(filter-out $(DISPLAY_JAVA_VO),$(DISPLAY_VO))
SELECTED_SPECIFIC_DISPLAY_VO := $(filter $(SELECTED_PATTERN),$(DISPLAY_VO))
# computing the vo_reverse_closure is slow, so we only do it if we're
# asked to make the lite target
ifneq ($(filter printlite lite lite-display print-lite-display lite-display-test,$(MAKECMDGOALS)),)
LITE_ALL_UNMADE_VOFILES := $(foreach vo,$(LITE_UNMADE_VOFILES),$(call vo_reverse_closure,$(VOFILES),$(vo)))
LITE_VOFILES := $(filter-out $(LITE_ALL_UNMADE_VOFILES),$(COQ_VOFILES))
LITE_DISPLAY_VOFILES := $(filter-out $(LITE_ALL_UNMADE_VOFILES),$(DISPLAY_VO))
else
include Makefile.lite-hardcoded
endif
ifneq ($(filter print-old-pipeline-lite old-pipeline-lite,$(MAKECMDGOALS)),)
OLD_PIPELINE_LITE_ALL_UNMADE_VOFILES := $(foreach vo,$(OLD_PIPELINE_LITE_UNMADE_VOFILES),$(call vo_reverse_closure,$(VOFILES),$(vo)))
OLD_PIPELINE_LITE_VOFILES := $(filter-out $(OLD_PIPELINE_LITE_ALL_UNMADE_VOFILES),$(COQ_VOFILES))
else
include Makefile.old-pipeline-lite-hardcoded
endif
ifneq ($(filter nobigmem print-nobigmem,$(MAKECMDGOALS)),)
NOBIGMEM_ALL_UNMADE_VOFILES := $(foreach vo,$(NOBIGMEM_UNMADE_VOFILES),$(call vo_reverse_closure,$(VOFILES),$(vo)))
NOBIGMEM_VOFILES := $(filter-out $(NOBIGMEM_ALL_UNMADE_VOFILES),$(COQ_VOFILES))
endif
ifneq ($(filter old-pipeline-nobigmem print-old-pipeline-nobigmem,$(MAKECMDGOALS)),)
OLD_PIPELINE_NOBIGMEM_ALL_UNMADE_VOFILES := $(foreach vo,$(OLD_PIPELINE_NOBIGMEM_UNMADE_VOFILES),$(call vo_reverse_closure,$(VOFILES),$(vo)))
OLD_PIPELINE_NOBIGMEM_VOFILES := $(filter-out $(OLD_PIPELINE_NOBIGMEM_ALL_UNMADE_VOFILES),$(COQ_VOFILES))
else
include Makefile.old-pipeline-nobigmem-hardcoded
endif
ifneq ($(filter only-heavy,$(MAKECMDGOALS)),)
HEAVY_VOFILES := $(call vo_closure,$(LITE_UNMADE_VOFILES))
endif
ifneq ($(filter util,$(MAKECMDGOALS)),)
UTIL_VOFILES := $(call vo_closure,$(UTIL_PRE_VOFILES))
endif
ifneq ($(filter no-curves-proofs,$(MAKECMDGOALS)),)
NO_CURVES_PROOFS_ALL_UNMADE_VOFILES := $(foreach vo,$(NO_CURVES_PROOFS_UNMADE_VOFILES),$(call vo_reverse_closure,$(VOFILES),$(vo)))
NO_CURVES_PROOFS_VOFILES := $(filter-out $(NO_CURVES_PROOFS_ALL_UNMADE_VOFILES),$(COQ_VOFILES))
endif
ifneq ($(filter no-curves-proofs-non-specific,$(MAKECMDGOALS)),)
NO_CURVES_PROOFS_NON_SPECIFIC_ALL_UNMADE_VOFILES := $(foreach vo,$(NO_CURVES_PROOFS_NON_SPECIFIC_UNMADE_VOFILES),$(call vo_reverse_closure,$(VOFILES),$(vo)))
NO_CURVES_PROOFS_NON_SPECIFIC_VOFILES := $(filter-out $(NO_CURVES_PROOFS_NON_SPECIFIC_ALL_UNMADE_VOFILES),$(COQ_VOFILES))
endif
ifneq ($(filter curves-proofs,$(MAKECMDGOALS)),)
CURVES_PROOFS_VOFILES := $(call vo_closure,$(CURVES_PROOFS_PRE_VOFILES))
endif
ifneq ($(filter selected-specific,$(MAKECMDGOALS)),)
SELECTED_SPECIFIC_VOFILES := $(call vo_closure,$(SELECTED_SPECIFIC_PRE_VOFILES))
endif
ifneq ($(filter new-pipeline,$(MAKECMDGOALS)),)
NEW_PIPELINE_VOFILES := $(call vo_closure,$(NEW_PIPELINE_PRE_VOFILES))
endif
ifneq ($(filter pre-standalone,$(MAKECMDGOALS)),)
PRE_STANDALONE_VOFILES := $(call vo_closure,$(PRE_STANDALONE_PRE_VOFILES))
endif


specific: $(SPECIFIC_VO)
non-specific: $(NON_SPECIFIC_VO)
coq: $(COQ_VOFILES)
lite: $(LITE_VOFILES)
old-pipeline-lite old-pipeline-lite-hardcoded: $(OLD_PIPELINE_LITE_VOFILES)
lite-display lite-display-hardcoded: $(LITE_DISPLAY_VOFILES:.vo=.log)
lite-display-test lite-display-test-hardcoded: $(LITE_DISPLAY_VOFILES:.vo=.log.diff)
coq-without-new-pipeline: $(COQ_WITHOUT_NEW_PIPELINE_VOFILES)
nobigmem: $(NOBIGMEM_VOFILES)
old-pipeline-nobigmem old-pipeline-nobigmem-hardcoded: $(OLD_PIPELINE_NOBIGMEM_VOFILES)
only-heavy: $(HEAVY_VOFILES)
util: $(UTIL_VOFILES)
curves-proofs: $(CURVES_PROOFS_VOFILES)
no-curves-proofs: $(NO_CURVES_PROOFS_VOFILES)
no-curves-proofs-non-specific: $(NO_CURVES_PROOFS_NON_SPECIFIC_VOFILES)
new-pipeline: $(NEW_PIPELINE_VOFILES)
pre-standalone: $(PRE_STANDALONE_VOFILES)
specific-display: $(SPECIFIC_DISPLAY_VO:.vo=.log)
specific-c: $(filter-out $(UNMADE_C_FILES),$(SPECIFIC_DISPLAY_VO:Display.vo=.c) $(SPECIFIC_DISPLAY_VO:Display.vo=.h))
selected-specific: $(SELECTED_SPECIFIC_VOFILES)
selected-specific-display: $(SELECTED_SPECIFIC_DISPLAY_VO:.vo=.log)
selected-specific-display-test: $(SELECTED_SPECIFIC_DISPLAY_VO:.vo=.log.diff)
selected-c: $(filter-out $(UNMADE_C_FILES),$(SELECTED_SPECIFIC_DISPLAY_VO:Display.vo=.c) $(SELECTED_SPECIFIC_DISPLAY_VO:Display.vo=.h))
some-early: $(SOME_EARLY_VOFILES)
nonautogenerated-specific: $(NONAUTOGENERATED_SPECIFIC_VO)
nonautogenerated-specific-display: $(NONAUTOGENERATED_SPECIFIC_DISPLAY_VO:.vo=.log)
nonautogenerated-specific-display-test: $(NONAUTOGENERATED_SPECIFIC_DISPLAY_VO:.vo=.log.diff)
nonautogenerated-c: $(filter-out $(UNMADE_C_FILES),$(NONAUTOGENERATED_SPECIFIC_DISPLAY_VO:Display.vo=.c) $(NONAUTOGENERATED_SPECIFIC_DISPLAY_VO:Display.vo=.h))
display: $(DISPLAY_VO:.vo=.log)

regenerate-curves::
	./regenerate-curves.sh

# extra target for faster coqdep
.PHONY: src/Specific/.autgenerated-deps
src/Specific/.autgenerated-deps:
	$(SHOW)'COQDEP $@'
	$(HIDE)$(COQDEP) $(COQLIBS) -dyndep var -c $(REAL_SPECIFIC_GENERATED_VOFILES:.vo=.v) $(redir_if_ok)

.PHONY: fast-autogenerated-deps
fast-autogenerated-deps: src/Specific/.autgenerated-deps
	$(SHOW)'CP .v.d'
	$(HIDE)for i in $(REAL_SPECIFIC_GENERATED_VOFILES:.vo=.v.d); do rm -f $$i; ln -s "$(shell cd src/Specific && pwd)/.autgenerated-deps" $$i; done

.PHONY: fake-autogenerated-deps
fake-autogenerated-deps:
	$(SHOW)'FAKE COQDEP SPECIFIC.v.d'
	$(HIDE)touch $(REAL_SPECIFIC_GENERATED_VOFILES:.vo=.v.d)

ifneq ($(filter fast-autogenerated-deps,$(MAKECMDGOALS)),)
$(REAL_SPECIFIC_GENERATED_VOFILES:.vo=.v.d): fast-autogenerated-deps
	@ true
endif

ifneq ($(filter fake-autogenerated-deps,$(MAKECMDGOALS)),)
$(REAL_SPECIFIC_GENERATED_VOFILES:.vo=.v.d): fake-autogenerated-deps
	@ true
endif


printlite::
	@echo 'Files Made:'
	@for i in $(sort $(LITE_VOFILES)); do echo $$i; done
	@echo
	@echo
	@echo 'Files Not Made:'
	@for i in $(sort $(LITE_ALL_UNMADE_VOFILES)); do echo $$i; done

print-old-pipeline-lite print-old-pipeline-lite-hardcoded::
	@echo 'Files Made:'
	@for i in $(sort $(OLD_PIPELINE_LITE_VOFILES)); do echo $$i; done
	@echo
	@echo
	@echo 'Files Not Made:'
	@for i in $(sort $(OLD_PIPELINE_LITE_ALL_UNMADE_VOFILES)); do echo $$i; done

print-lite-display print-lite-display-hardcoded::
	@echo 'Files Made:'
	@for i in $(sort $(LITE_DISPLAY_VOFILES)); do echo $$i; done
	@echo
	@echo
	@echo 'Files Not Made:'
	@for i in $(sort $(LITE_ALL_UNMADE_VOFILES)); do echo $$i; done

print-nobigmem::
	@echo 'Files Made:'
	@for i in $(sort $(NOBIGMEM_VOFILES)); do echo $$i; done
	@echo
	@echo
	@echo 'Files Not Made:'
	@for i in $(sort $(NOBIGMEM_ALL_UNMADE_VOFILES)); do echo $$i; done

print-old-pipeline-nobigmem print-old-pipeline-nobigmem-hardcoded::
	@echo 'Files Made:'
	@for i in $(sort $(OLD_PIPELINE_NOBIGMEM_VOFILES)); do echo $$i; done
	@echo
	@echo
	@echo 'Files Not Made:'
	@for i in $(sort $(OLD_PIPELINE_NOBIGMEM_ALL_UNMADE_VOFILES)); do echo $$i; done

print-nonautogenerated-specific::
	@echo 'Files Made:'
	@for i in $(sort $(NONAUTOGENERATED_SPECIFIC_VO)); do echo $$i; done

print-nonautogenerated-specific-display::
	@echo 'Files Made:'
	@for i in $(sort $(NONAUTOGENERATED_SPECIFIC_DISPLAY_VO:.vo=.log)); do echo $$i; done

ifneq ($(filter 8.5%,$(COQ_VERSION)),) # 8.5
else
ifneq ($(PROFILE),)
OTHERFLAGS += -profile-ltac
endif
OTHERFLAGS += -w "-notation-overridden"
endif

ifneq ($(filter /cygdrive/%,$(CURDIR)),)
CURDIR_SAFE := $(shell cygpath -m "$(CURDIR)")
else
CURDIR_SAFE := $(CURDIR)
endif

EXTERNAL_DEPENDENCIES?=

ifneq ($(EXTERNAL_DEPENDENCIES),1)

COQPRIME_FOLDER := coqprime
COQPATH?=${CURDIR_SAFE}/$(COQPRIME_FOLDER)/src
export COQPATH

$(VOFILES): | coqprime

coqprime:
	$(MAKE) --no-print-directory -C $(COQPRIME_FOLDER) src/Coqprime/PrimalityTest/Zp.vo

coqprime-all: coqprime
	$(MAKE) --no-print-directory -C $(COQPRIME_FOLDER)

clean-coqprime:
	$(MAKE) --no-print-directory -C $(COQPRIME_FOLDER) clean

install-coqprime:
	$(MAKE) --no-print-directory -C $(COQPRIME_FOLDER) install

cleanall:: clean-coqprime

install: install-coqprime

endif

etc/tscfreq: etc/tscfreq.c
	gcc etc/tscfreq.c -s -Os -o etc/tscfreq

Makefile.coq: Makefile _CoqProject
	$(SHOW)'COQ_MAKEFILE -f _CoqProject > $@'
	$(HIDE)$(COQBIN)coq_makefile -f _CoqProject INSTALLDEFAULTROOT = $(INSTALLDEFAULTROOT) -o Makefile-old && cat Makefile-old | sed s'/^printenv:/printenv::/g' | sed s'/^printenv:::/printenv::/g' | sed s'/\$$(TIMER) \$$(COQC)/$$(SET_LIMITS) $$(TIMER) $$(TIMEOUT_CMD) $$(COQC)/g' | sed s'/\$$(SHOW)COQC/$$(SHOW)$$(TIMEOUT_SHOW)COQC/g' > $@ && rm -f Makefile-old

NO_LIMIT_PERF?=
MAX_KB?=10000000 # 10 GB
MAX_SEC?=
TIMEOUT_CMD?=
TIMEOUT_SHOW?=
SET_LIMITS?=

ifeq (,$(NO_LIMIT_PERF))
ifneq (,$(MAX_SEC))
TIMEOUT_CMD:=timeout $(MAX_SEC)
PERF_T_ARG:=-t $(MAX_SEC) # trailing space important
else
PERF_T_ARG:=
endif

# apparently ulimit -m doesn't work anymore https://superuser.com/a/1497437/59575 / https://thirld.com/blog/2012/02/09/things-to-remember-when-using-ulimit/
SET_LIMITS = ulimit -S -m $(MAX_KB); ulimit -S -v $(MAX_KB);
TIMEOUT_SHOW:=TIMEOUT -m $(strip $(MAX_KB)) $(PERF_T_ARG)
endif

$(DISPLAY_NON_JAVA_VO:.vo=.log) : %Display.log : %.vo src/Compilers/Z/CNotations.vo src/Specific/Framework/IntegrationTestDisplayCommon.vo
$(DISPLAY_JAVA_VO:.vo=.log) : %JavaDisplay.log : %.vo src/Compilers/Z/JavaNotations.vo src/Specific/Framework/IntegrationTestDisplayCommon.vo

$(DISPLAY_JAVA_VO:.vo=.log) $(DISPLAY_NON_JAVA_VO:.vo=.log) : %.log : %.v
	$(SHOW)'$(TIMEOUT_SHOW)COQC $< > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(SET_LIMITS) $(TIMER) $(TIMEOUT_CMD) $(COQC) $(COQDEBUG) $(COQFLAGS) $(COQLIBS) $< && touch $@.ok) > $@.tmp
	$(HIDE)rm $@.ok
	$(HIDE)sed s'/\r\n/\n/g' $@.tmp > $@ && rm -f $@.tmp

DISPLAY_X25519_C64_VO := $(filter src/Specific/X25519/C64/%,$(DISPLAY_NON_JAVA_VO))
DISPLAY_X25519_C32_VO := $(filter src/Specific/X25519/C32/%,$(DISPLAY_NON_JAVA_VO))
DISPLAY_NON_JAVA_C32_VO := $(DISPLAY_X25519_C32_VO)
DISPLAY_NON_JAVA_C64_VO := $(filter-out $(DISPLAY_NON_JAVA_C32_VO) $(SPECIFIC_GENERATED_VOFILES),$(DISPLAY_NON_JAVA_VO))
DISPLAY_GENERATED_VO := $(filter $(SPECIFIC_GENERATED_VOFILES),$(DISPLAY_NON_JAVA_VO))
DISPLAY_NON_GENERATED_VO := $(filter-out $(DISPLAY_GENERATED_VO),$(DISPLAY_NON_JAVA_VO))

.PHONY: $(DISPLAY_VO:.vo=.log.diff)
$(DISPLAY_VO:.vo=.log.diff) : %.log.diff : %.log %.log.expected
	diff $*.log.expected $*.log

c: $(filter-out $(UNMADE_C_FILES),$(DISPLAY_NON_JAVA_VO:Display.vo=.c) $(DISPLAY_NON_GENERATED_VO:Display.vo=.h))

$(DISPLAY_NON_JAVA_C64_VO:Display.vo=.c) : %.c : %Display.log extract-function.sh
	BITWIDTH=64 FIAT_CRYPTO_EXTRACT_FUNCTION_IS_ASM="" ./extract-function.sh $(patsubst %Display.log,%,$(notdir $<)) < $< > $@

$(DISPLAY_NON_JAVA_C32_VO:Display.vo=.c) : %.c : %Display.log extract-function.sh
	BITWIDTH=32 FIAT_CRYPTO_EXTRACT_FUNCTION_IS_ASM="" ./extract-function.sh $(patsubst %Display.log,%,$(notdir $<)) < $< > $@

$(DISPLAY_NON_JAVA_C64_VO:Display.vo=.h) : %.h : %Display.log extract-function-header.sh
	BITWIDTH=64 ./extract-function-header.sh $(patsubst %Display.log,%,$(notdir $<)) < $< > $@

$(DISPLAY_NON_JAVA_C32_VO:Display.vo=.h) : %.h : %Display.log extract-function-header.sh
	BITWIDTH=32 ./extract-function-header.sh $(patsubst %Display.log,%,$(notdir $<)) < $< > $@

$(DISPLAY_GENERATED_VO:Display.vo=.c) : %.c : %Display.log src/Specific/Framework/bench/prettyprint.py
	./src/Specific/Framework/bench/prettyprint.py $(patsubst %Display.log,%,$(notdir $<)) < $< > $@

TEST_BINARIES := \
	src/Specific/X25519/C64/test \
	src/Specific/NISTP256/AMD64/test/feadd_test \
	src/Specific/NISTP256/AMD64/test/femul_test \
	src/Specific/NISTP256/AMD64/test/p256_test
MEASUREMENTS := \
	src/Specific/X25519/C64/measurements.txt \
	third_party/openssl-curve25519/measurements.txt \
	third_party/curve25519-donna-c64/measurements.txt \
	third_party/openssl-nistz256-amd64/measurements.txt \
	third_party/openssl-nistz256-adx/measurements.txt \
	third_party/openssl-nistp256c64/measurements.txt \
	src/Specific/NISTP256/AMD64/measurements.txt
ifeq ($(SKIP_ICC),)
TEST_BINARIES += src/Specific/NISTP256/AMD64/icc/p256_test
MEASUREMENTS += src/Specific/NISTP256/AMD64/icc/measurements.txt
endif
RUN_TEST_BINARIES := $(addsuffix -run,$(TEST_BINARIES))
MEASURE_BINARIES := $(addsuffix measure,$(dir $(MEASUREMENTS)))

SELECTED_TEST_BINARIES := $(filter $(SELECTED_PATTERN),$(TEST_BINARIES))
RUN_SELECTED_TEST_BINARIES := $(filter $(SELECTED_PATTERN),$(RUN_TEST_BINARIES))
SELECTED_MEASURE_BINARIES := $(filter $(SELECTED_PATTERN),$(MEASURE_BINARIES))
SELECTED_MEASUREMENTS := $(filter $(SELECTED_PATTERN),$(MEASUREMENTS))

src/Specific/X25519/C64/test src/Specific/X25519/C64/measure: $(filter-out $(UNMADE_C_FILES),$(DISPLAY_X25519_C64_VO:Display.vo=.c) $(DISPLAY_X25519_C64_VO:Display.vo=.h)) src/Specific/X25519/C64/scalarmult.c
src/Specific/X25519/C64/test: src/Specific/X25519/C64/compiler.sh src/Specific/X25519/x25519_test.c
src/Specific/X25519/C64/test: INCLUDE_FOLDER=src/Specific/X25519/C64
src/Specific/X25519/C64/measure: UUT=crypto_scalarmult_bench
src/Specific/X25519/C64/measurements.txt: COUNT=2047

third_party/openssl-curve25519/measure: third_party/openssl-curve25519/crypto_scalarmult_bench.c third_party/openssl-curve25519/ec_curve25519.c third_party/openssl-curve25519/ec_curve25519.h
third_party/openssl-curve25519/measure: UUT=crypto_scalarmult_bench
third_party/openssl-curve25519/measurements.txt: COUNT=2047

third_party/curve25519-donna-c64/measure: third_party/curve25519-donna-c64/crypto_scalarmult_bench.c third_party/curve25519-donna-c64/curve25519-donna-c64.c
third_party/curve25519-donna-c64/measure: UUT=crypto_scalarmult_bench
third_party/curve25519-donna-c64/measurements.txt: COUNT=2047

third_party/openssl-nistz256-amd64/measure: third_party/openssl-nistz256-amd64/bench_madd.c third_party/openssl-nistz256-amd64/cpu_intel.c third_party/openssl-nistz256-amd64/ecp_nistz256-x86_64.s third_party/openssl-nistz256-amd64/nistz256.h
third_party/openssl-nistz256-amd64/measure: UUT=bench_madd
third_party/openssl-nistz256-amd64/measurements.txt: COUNT=65535

third_party/openssl-nistz256-adx/measure: third_party/openssl-nistz256-adx/bench_madd.c third_party/openssl-nistz256-adx/cpu_intel.c third_party/openssl-nistz256-adx/ecp_nistz256-x86_64.s third_party/openssl-nistz256-adx/nistz256.h
third_party/openssl-nistz256-adx/measure: UUT=bench_madd
third_party/openssl-nistz256-adx/measurements.txt: COUNT=65535

third_party/openssl-nistp256c64/measure: third_party/openssl-nistp256c64/bench_madd.c third_party/openssl-nistp256c64/ecp_nistp256.c third_party/openssl-nistp256c64/ecp_nistp256.h
third_party/openssl-nistp256c64/measure: UUT=bench_madd
third_party/openssl-nistp256c64/measurements.txt: COUNT=65535

src/Specific/NISTP256/AMD64/measure: src/Specific/NISTP256/AMD64/bench_madd.c src/Specific/NISTP256/AMD64/feadd.h src/Specific/NISTP256/AMD64/feadd.c src/Specific/NISTP256/AMD64/femul.h src/Specific/NISTP256/AMD64/femul.c src/Specific/NISTP256/AMD64/fenz.h src/Specific/NISTP256/AMD64/fenz.c src/Specific/NISTP256/AMD64/feopp.h src/Specific/NISTP256/AMD64/feopp.c src/Specific/NISTP256/AMD64/fesub.h src/Specific/NISTP256/AMD64/fesub.c src/Specific/NISTP256/AMD64/p256_jacobian_add_affine.c liblow/cmovznz.c
src/Specific/NISTP256/AMD64/measure: UUT=bench_madd
src/Specific/NISTP256/AMD64/measurements.txt: COUNT=65535

src/Specific/NISTP256/AMD64/icc/measure: src/Specific/NISTP256/AMD64/p256.h src/Specific/NISTP256/AMD64/icc/icc17_p256_jacobian_add_affine.s src/Specific/NISTP256/AMD64/bench_madd.c liblow/cmovznz.c
src/Specific/NISTP256/AMD64/icc/measure: UUT=bench_madd
src/Specific/NISTP256/AMD64/icc/measurements.txt: COUNT=65535


src/Specific/NISTP256/AMD64/test/feadd_test src/Specific/NISTP256/AMD64/test/femul_test src/Specific/NISTP256/AMD64/test/p256_test: src/Specific/NISTP256/AMD64/compiler.sh liblow/cmovznz.c
src/Specific/NISTP256/AMD64/test/feadd_test src/Specific/NISTP256/AMD64/test/femul_test src/Specific/NISTP256/AMD64/test/p256_test: INCLUDE_FOLDER=src/Specific/NISTP256/AMD64/

src/Specific/NISTP256/AMD64/test/feadd_test: src/Specific/NISTP256/AMD64/feadd.h src/Specific/NISTP256/AMD64/feadd.c src/Specific/NISTP256/AMD64/test/feadd_test.c

src/Specific/NISTP256/AMD64/test/femul_test: src/Specific/NISTP256/AMD64/femul.h src/Specific/NISTP256/AMD64/femul.c src/Specific/NISTP256/AMD64/test/femul_test.c

src/Specific/NISTP256/AMD64/test/p256_test: src/Specific/NISTP256/AMD64/test/p256_test.c src/Specific/NISTP256/AMD64/feadd.c src/Specific/NISTP256/AMD64/feadd.h src/Specific/NISTP256/AMD64/femul.c src/Specific/NISTP256/AMD64/femul.h src/Specific/NISTP256/AMD64/fenz.c src/Specific/NISTP256/AMD64/fenz.h src/Specific/NISTP256/AMD64/fesub.c src/Specific/NISTP256/AMD64/fesub.h src/Specific/NISTP256/AMD64/p256_jacobian_add_affine.c src/Specific/NISTP256/AMD64/p256.h

src/Specific/NISTP256/AMD64/icc/p256_test: src/Specific/NISTP256/AMD64/icc/compiler.sh src/Specific/NISTP256/AMD64/test/p256_test.c src/Specific/NISTP256/AMD64/icc/icc17_p256_jacobian_add_affine.s src/Specific/NISTP256/AMD64/p256.h
src/Specific/NISTP256/AMD64/icc/p256_test: INCLUDE_FOLDER=src/Specific/NISTP256/AMD64/

$(TEST_BINARIES):
	$(filter %/compiler.sh,$^) -o $@ -I liblow -I $(INCLUDE_FOLDER) $(filter %.c %.s,$^)

$(MEASURE_BINARIES) : %/measure : %/compiler.sh measure.c
	$*/compiler.sh -o $@ -I liblow -I $* $(filter %.c %.s,$^) -D UUT=$(UUT)

$(MEASUREMENTS) : %/measurements.txt : %/measure capture.sh etc/machine.sh etc/cpufreq etc/tscfreq
	./capture.sh $* $(COUNT)

src/Specific/NISTP256/AMD64/icc/combined.c: liblow/cmovznz.c src/Specific/NISTP256/AMD64/feadd.c src/Specific/NISTP256/AMD64/femul.c src/Specific/NISTP256/AMD64/fenz.c src/Specific/NISTP256/AMD64/fesub.c src/Specific/NISTP256/AMD64/p256_jacobian_add_affine.c extract-function.sh
	(cd src/Specific/NISTP256/AMD64 && ( BITWIDTH=64 FIAT_CRYPTO_EXTRACT_FUNCTION_IS_ASM="" ../../../../extract-function.sh "stdint" < /dev/null | grep -v stdint && sed 's:^uint64_t:static inline &:' ../../../../liblow/cmovznz.c && echo fenz.c feadd.c fesub.c femul.c p256_jacobian_add_affine.c | xargs -n1 grep -A99999 void -- ) | sed 's:^void force_inline:static inline void force_inline:' | grep -v liblow > icc/combined.c )

GENERATED_FOLDERS := $(sort $(dir $(filter $(SPECIFIC_GENERATED_VOFILES),$(REGULAR_VOFILES))))
GENERATED_PY_MEASUREMENTS := $(addsuffix montladder.log,$(GENERATED_FOLDERS))
GENERATED_GMPXX := $(addsuffix gmpxx,$(GENERATED_FOLDERS))
GENERATED_GMPXX_MEASUREMENTS := $(addsuffix .log,$(GENERATED_GMPXX))
GENERATED_GMPVAR := $(addsuffix gmpvar,$(GENERATED_FOLDERS))
GENERATED_GMPVAR_MEASUREMENTS := $(addsuffix .log,$(GENERATED_GMPVAR))
GENERATED_GMPSEC := $(addsuffix gmpsec,$(GENERATED_FOLDERS))
GENERATED_GMPSEC_MEASUREMENTS := $(addsuffix .log,$(GENERATED_GMPSEC))
GENERATED_FIBE := $(addsuffix fibe,$(GENERATED_FOLDERS))
GENERATED_FIBE_MEASUREMENTS := $(addsuffix .log,$(GENERATED_FIBE))

generated-benchmarks: $(GENERATED_FIBE) $(GENERATED_GMPSEC) $(GENERATED_GMPVAR) $(GENERATED_GMPXX)

$(GENERATED_PY_MEASUREMENTS) : %/montladder.log : %/py_interpreter.sh src/Specific/Framework/bench/montladder.py
	sh $*/py_interpreter.sh src/Specific/Framework/bench/montladder.py > $@

$(GENERATED_GMPXX) : %/gmpxx : %/compilerxx.sh src/Specific/Framework/bench/gmpxx.cpp
	sh $*/compilerxx.sh src/Specific/Framework/bench/gmpxx.cpp -lgmp -lgmpxx -o $@

$(GENERATED_GMPXX_MEASUREMENTS) : %/gmpxx.log : %/gmpxx
	$(STDTIME) $< 2>&1 | tee $@

$(GENERATED_GMPVAR) : %/gmpvar : %/compiler.sh src/Specific/Framework/bench/gmpvar.c
	sh $*/compiler.sh src/Specific/Framework/bench/gmpvar.c -lgmp -o $@

$(GENERATED_GMPVAR_MEASUREMENTS) : %/gmpvar.log : %/gmpvar
	$(STDTIME) $< 2>&1 | tee $@

$(GENERATED_GMPSEC) : %/gmpsec : %/compiler.sh src/Specific/Framework/bench/gmpsec.c
	sh $*/compiler.sh src/Specific/Framework/bench/gmpsec.c -lgmp -o $@

$(GENERATED_GMPSEC_MEASUREMENTS) : %/gmpsec.log : %/gmpsec
	$(STDTIME) $< 2>&1 | tee $@

$(GENERATED_FIBE) : %/fibe : %/compiler.sh src/Specific/Framework/bench/fibe.c %/feadd.c %/femul.c %/fesquare.c %/fesub.c liblow/liblow.h liblow/cmovznz.c
	sh $*/compiler.sh -I liblow/ liblow/cmovznz.c src/Specific/Framework/bench/fibe.c -I $*/ -o $@

$(GENERATED_FIBE_MEASUREMENTS) : %/fibe.log : %/fibe
	$(STDTIME) $< 2>&1 | tee $@

.PHONY: generated-py-bench
generated-py-bench: $(GENERATED_PY_MEASUREMENTS)
	head -999999 $?

.PHONY: generated-gmpxx-bench
generated-gmpxx-bench: $(GENERATED_GMPXX_MEASUREMENTS)
	head -999999 $?

.PHONY: generated-gmpvar-bench
generated-gmpvar-bench: $(GENERATED_GMPVAR_MEASUREMENTS)
	head -999999 $?

.PHONY: generated-gmpsec-bench
generated-gmpsec-bench: $(GENERATED_GMPSEC_MEASUREMENTS)
	head -999999 $?

.PHONY: generated-fibe-bench
generated-fibe-bench: $(GENERATED_FIBE_MEASUREMENTS)
	head -999999 $?

bench: $(MEASUREMENTS)
	head -999999 $?

selected-bench: $(SELECTED_MEASUREMENTS)
	head -999999 $?


.PHONY: $(RUN_TEST_BINARIES)
$(RUN_TEST_BINARIES) : %-run : %
	$<

test: $(RUN_TEST_BINARIES)

build-test: $(TEST_BINARIES)

selected-test: $(RUN_SELECTED_TEST_BINARIES)

build-selected-test: $(SELECTED_TEST_BINARIES)

build-bench: $(MEASURE_BINARIES)

build-selected-bench: $(SELECTED_MEASURE_BINARIES)

STANDALONE := \
	unsaturated_solinas \
	saturated_solinas \
	word_by_word_montgomery

$(STANDALONE:%=src/Experiments/NewPipeline/ExtractionOCaml/%.ml) : %.ml : %.v src/Experiments/NewPipeline/StandaloneOCamlMain.vo
	$(SHOW)'COQC $< > $@'
	$(HIDE)$(TIMER_FULL) $(COQC) $(COQDEBUG) $(COQFLAGS) $(COQLIBS) $< > $@.tmp
	$(HIDE)sed 's/\r\n/\n/g; s/\r//g' $@.tmp > $@ && rm -f $@.tmp

$(STANDALONE:%=src/Experiments/NewPipeline/ExtractionHaskell/%.hs) : %.hs : %.v src/Experiments/NewPipeline/StandaloneHaskellMain.vo src/Experiments/NewPipeline/haskell.sed
	$(SHOW)'COQC $< > $@'
	$(HIDE)$(TIMER_FULL) $(COQC) $(COQDEBUG) $(COQFLAGS) $(COQLIBS) $< > $@.tmp
	$(HIDE)sed 's/\r\n/\n/g; s/\r//g' $@.tmp | sed -f src/Experiments/NewPipeline/haskell.sed > $@ && rm -f $@.tmp

# pass -w -20 to disable the unused argument warning
$(STANDALONE:%=src/Experiments/NewPipeline/ExtractionOCaml/%) : % : %.ml
	$(TIMER_FULL) ocamlopt -w -20 -o $@ $<

$(STANDALONE:%=src/Experiments/NewPipeline/ExtractionHaskell/%) : % : %.hs
	$(TIMER_FULL) $(GHC) $(GHCFLAGS) -o $@ $<

standalone: standalone-haskell standalone-ocaml

standalone-haskell: $(STANDALONE:%=src/Experiments/NewPipeline/ExtractionHaskell/%)
standalone-ocaml: $(STANDALONE:%=src/Experiments/NewPipeline/ExtractionOCaml/%)

UNSATURATED_SOLINAS_C_FILES := curve25519_64.c curve25519_32.c p521_64.c p521_32.c # p224_solinas_64.c
WORD_BY_WORD_MONTGOMERY_C_FILES := p256_64.c p256_32.c p384_64.c p384_32.c secp256k1_64.c secp256k1_32.c p224_64.c p224_32.c
FUNCTIONS_FOR_25519 := carry_mul carry_square carry_scmul121666 carry add sub opp selectznz to_bytes from_bytes
UNSATURATED_SOLINAS := src/Experiments/NewPipeline/ExtractionOCaml/unsaturated_solinas
WORD_BY_WORD_MONTGOMERY := src/Experiments/NewPipeline/ExtractionOCaml/word_by_word_montgomery
ALL_C_FILES := $(UNSATURATED_SOLINAS_C_FILES) $(WORD_BY_WORD_MONTGOMERY_C_FILES)
.PHONY: c-files
c-files: $(ALL_C_FILES)

$(UNSATURATED_SOLINAS_C_FILES): $(UNSATURATED_SOLINAS) # Makefile

$(WORD_BY_WORD_MONTGOMERY_C_FILES): $(WORD_BY_WORD_MONTGOMERY) # Makefile

# 2^255 - 19
curve25519_64.c:
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)$(TIMER_FULL) $(UNSATURATED_SOLINAS) '25519' '5' '2^255' '1,19' '64' $(FUNCTIONS_FOR_25519) > $@

# 2^255 - 19
curve25519_32.c:
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)$(TIMER_FULL) $(UNSATURATED_SOLINAS) '25519' '10' '2^255' '1,19' '32' $(FUNCTIONS_FOR_25519) > $@

# 2^521 - 1
p521_64.c:
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)$(TIMER_FULL) $(UNSATURATED_SOLINAS) 'p521' '9' '2^521' '1,1' '64' > $@

# 2^521 - 1
p521_32.c:
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)$(TIMER_FULL) $(UNSATURATED_SOLINAS) 'p521' '17' '2^521' '1,1' '32' > $@

## 2^224 - 2^96 + 1 ## does not bounds check
#p224_solinas_64.c:
#	$(SHOW)'SYNTHESIZE > $@'
#	$(HIDE)$(TIMER_FULL) $(UNSATURATED_SOLINAS) 'p224' '4' '2^224' '2^96,1;1,-1' '64' > $@

# 2^256 - 2^224 + 2^192 + 2^96 - 1
p256_64.c p256_32.c : p256_%.c :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)$(TIMER_FULL) $(WORD_BY_WORD_MONTGOMERY) 'p256' '2^256' '2^224,1;2^192,-1;2^96,-1;1,1' '$*' > $@

# 2^256 - 2^32 - 977
secp256k1_64.c secp256k1_32.c : secp256k1_%.c :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)$(TIMER_FULL) $(WORD_BY_WORD_MONTGOMERY) 'secp256k1' '2^256' '2^32,1;1,977' '$*' > $@

# 2^384 - 2^128 - 2^96 + 2^32 - 1
p384_64.c p384_32.c : p384_%.c :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)$(TIMER_FULL) $(WORD_BY_WORD_MONTGOMERY) 'p384' '2^384' '2^128,1;2^96,1;2^32,-1;1,1' '$*' > $@

# 2^224 - 2^96 + 1
p224_64.c p224_32.c : p224_%.c :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)$(TIMER_FULL) $(WORD_BY_WORD_MONTGOMERY) 'p224' '2^224' '2^96,1;1,-1' '$*' > $@

CFLAGS?=
.PHONY: only-test-c-files test-c-files
only-test-c-files test-c-files:
	$(CC) -Wall -Wno-unused-function -Werror $(CFLAGS) -c $(ALL_C_FILES)

test-c-files: $(ALL_C_FILES)

clean::
	rm -f Makefile.coq remake_curves.log src/Specific/.autgenerated-deps

cleanall:: clean

ifneq ($(filter install,$(MAKECMDGOALS)),)
FILESTOINSTALL := $(wildcard $(FILESTOINSTALL))
endif

install: coq

printenv::
	@echo "COQPATH =        $$COQPATH"

printdeps::
	$(HIDE)$(foreach vo,$(filter %.vo,$(MAKECMDGOALS)),echo '$(vo): $(call vo_closure,$(vo))'; )

printreversedeps::
	$(HIDE)$(foreach vo,$(filter %.vo,$(MAKECMDGOALS)),echo '$(vo): $(call vo_reverse_closure,$(VOFILES),$(vo))'; )
