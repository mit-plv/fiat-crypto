.SUFFIXES:

.PHONY: coq clean cleanall install \
	coq-without-bedrock2 install-without-bedrock2 \
	install-rewriter clean-rewriter rewriter \
	install-coqprime clean-coqprime coqprime coqprime-all \
	bedrock2 clean-bedrock2 install-bedrock2 coqutil clean-coqutil install-coqutil \
	bedrock2-compiler clean-bedrock2-compiler install-bedrock2-compiler \
	rupicola clean-rupicola install-rupicola \
	util all-except-generated all all-except-generated-and-js-of-ocaml all-except-js-of-ocaml \
	bedrock2-backend \
	deps \
	nobigmem print-nobigmem \
	lite only-heavy printlite \
	all-except-compiled \
	some-early pre-standalone pre-standalone-extracted \
	check-output accept-output

include Makefile.config

SKIP_INCLUDE?=
SKIP_COQSCRIPTS_INCLUDE?=
ifneq ($(SKIP_INCLUDE),1)
# this include must be before all: and validate: which are overriden below
-include Makefile.coq
ifneq ($(SKIP_COQSCRIPTS_INCLUDE),1)
include etc/coq-scripts/Makefile.vo_closure
endif

ifeq (,$(COQ_VERSION))
# Makefile.coq didn't get included, so we need to make a best-effort to get the Coq version so we can make _CoqProject
ifneq (,$(COQBIN))
# add an ending /
COQBIN:=$(COQBIN)/
endif

COQC     ?= "$(COQBIN)coqc"
COQ_VERSION:=$(shell $(COQC) --print-version | cut -d " " -f 1)

endif
endif


PERF_TESTS?=
ifneq ($(PERF_TESTS),1)
PERF_RECORDER?=
else
PERF_RECORDER?=$(PERF_RECORD)
endif

.DEFAULT_GOAL := all

# coq .vo files that are not compiled using coq_makefile
SPECIAL_VOFILES := \
	src/ExtractionOCaml/%.vo \
	src/ExtractionJsOfOCaml/%.vo \
	src/ExtractionHaskell/%.vo \
	src/Rewriter/PerfTesting/Specific/generated/%.vo
GREP_EXCLUDE_SPECIAL := grep -v '^\(src/Extraction\(OCaml\|Haskell\)/\|src/Rewriter/PerfTesting/Specific/generated/\)'
GREP_EXCLUDE_GENERATED := grep -v '^\(src\|src/Bedrock\)/Everything\.v'

# .vo files that depend on Everything.vo (should be just testing files, not defining anything)
AFTER_EVERYTHING_VOFILES := \
	src/PerfTesting/PerfTestSearch.vo \
	src/PerfTesting/PerfTestSearchPattern.vo \
	src/PerfTesting/PerfTestPrint.vo \
	#

PERFTESTING_VO := \
	src/Rewriter/PerfTesting/Core.vo \
	src/Rewriter/PerfTesting/StandaloneOCamlMain.vo
BEDROCK2_FILES_PATTERN := \
	src/ExtractionJsOfOCaml/bedrock2_% \
	src/ExtractionOCaml/bedrock2_% \
	src/ExtractionHaskell/bedrock2_% \
	src/ExtractionJsOfOCaml/with_bedrock2_% \
	src/ExtractionOCaml/with_bedrock2_% \
	src/ExtractionHaskell/with_bedrock2_% \
	src/Assembly/WithBedrock/% \
	src/Bedrock/% # it's important to catch not just the .vo files, but also the .glob files, etc, because this is used to filter FILESTOINSTALL
EXCLUDE_PATTERN :=

ifeq ($(SKIP_BEDROCK2),1)
EXCLUDE_PATTERN += $(BEDROCK2_FILES_PATTERN)
$(warning Skipping bedrock2)
endif
EXCLUDED_VOFILES := $(filter $(EXCLUDE_PATTERN),$(VOFILES))
# add files to this list to prevent them from being built as final
# targets by the "lite" target
LITE_UNMADE_VOFILES := src/Curves/Weierstrass/AffineProofs.vo \
	src/Curves/Weierstrass/Jacobian/Jacobian.vo \
	src/Curves/Weierstrass/Jacobian/CoZ.vo \
	src/Curves/Weierstrass/Jacobian/ScalarMult.vo \
	src/Curves/Weierstrass/Projective.vo \
	src/Rewriter/RulesGood.vo \
	src/Rewriter/All.vo \
	$(PERFTESTING_VO) \
	$(EXCLUDED_VO)
NOBIGMEM_UNMADE_VOFILES := \
	src/Curves/Weierstrass/AffineProofs.vo \
	src/Curves/Weierstrass/Jacobian/Jacobian.vo \
	src/Curves/Weierstrass/Jacobian/CoZ.vo \
	src/Curves/Weierstrass/Jacobian/ScalarMult.vo \
	src/Curves/Weierstrass/Projective.vo \
	$(PERFTESTING_VO) \
	$(EXCLUDED_VO)
REGULAR_WITH_BEDROCK2_VOFILES := $(filter-out $(SPECIAL_VOFILES),$(VOFILES))
REGULAR_VOFILES := $(filter-out $(EXCLUDE_PATTERN),$(REGULAR_WITH_BEDROCK2_VOFILES))
REGULAR_EXCEPT_BEDROCK2_VOFILES := $(filter-out $(BEDROCK2_FILES_PATTERN),$(REGULAR_VOFILES))
BEDROCK2_VOFILES := $(filter $(BEDROCK2_FILES_PATTERN),$(REGULAR_VOFILES))
PRE_STANDALONE_PRE_VOFILES := $(filter src/Standalone%.vo src/Bedrock/Standalone%.vo,$(REGULAR_VOFILES))
UTIL_PRE_VOFILES := $(filter src/Algebra/%.vo src/Tactics/%.vo src/Util/%.vo,$(REGULAR_VOFILES))
SOME_EARLY_VOFILES := \
  src/Arithmetic/Core.vo \
  src/Rewriter/AllTacticsExtra.vo

# computing the vo_reverse_closure is slow, so we only do it if we're
# asked to make the lite target
ifneq ($(filter printlite lite,$(MAKECMDGOALS)),)
LITE_ALL_UNMADE_VOFILES := $(foreach vo,$(LITE_UNMADE_VOFILES),$(call vo_reverse_closure,$(VOFILES),$(vo)))
LITE_VOFILES := $(filter-out $(LITE_ALL_UNMADE_VOFILES),$(REGULAR_VOFILES))
endif
ifneq ($(filter nobigmem print-nobigmem,$(MAKECMDGOALS)),)
NOBIGMEM_ALL_UNMADE_VOFILES := $(foreach vo,$(NOBIGMEM_UNMADE_VOFILES),$(call vo_reverse_closure,$(VOFILES),$(vo)))
NOBIGMEM_VOFILES := $(filter-out $(NOBIGMEM_ALL_UNMADE_VOFILES),$(REGULAR_VOFILES))
endif
ifneq ($(filter only-heavy,$(MAKECMDGOALS)),)
HEAVY_VOFILES := $(call vo_closure,$(LITE_UNMADE_VOFILES))
endif
ifneq ($(filter util,$(MAKECMDGOALS)),)
UTIL_VOFILES := $(call vo_closure,$(UTIL_PRE_VOFILES))
endif
ifneq ($(filter pre-standalone,$(MAKECMDGOALS)),)
PRE_STANDALONE_VOFILES := $(call vo_closure,$(PRE_STANDALONE_PRE_VOFILES))
endif

OUTPUT_VOS := \
	src/Fancy/Montgomery256.vo \
	src/Fancy/Barrett256.vo \
	src/UnsaturatedSolinasHeuristics/Tests.vo

OUTPUT_PREOUTS := \
	Crypto.Fancy.Montgomery256.Prod.MontRed256 \
	Crypto.Fancy.Montgomery256.prod_montred256_correct \
	Crypto.Fancy.Montgomery256.prod_montred256_correct.Assumptions \
	Crypto.Fancy.Montgomery256.montred256 \
	Crypto.Fancy.Barrett256.Prod.MulMod \
	Crypto.Fancy.Barrett256.prod_barrett_red256_correct \
	Crypto.Fancy.Barrett256.prod_barrett_red256_correct.Assumptions \
	Crypto.Fancy.Barrett256.barrett_red256 \
	Crypto.UnsaturatedSolinasHeuristics.Tests.get_possible_limbs \
	Crypto.UnsaturatedSolinasHeuristics.Tests.get_balances

CHECK_OUTPUTS := $(addprefix check-,$(OUTPUT_PREOUTS))
ACCEPT_OUTPUTS := $(addprefix accept-,$(OUTPUT_PREOUTS) fiat-amd64.test)

all-except-compiled: coq pre-standalone-extracted check-output
all-except-generated-and-js-of-ocaml: standalone-ocaml perf-standalone all-except-compiled
all-except-generated: all-except-generated-and-js-of-ocaml standalone-js-of-ocaml
all-except-js-of-ocaml: all-except-generated-and-js-of-ocaml generated-files
all: all-except-generated-and-js-of-ocaml standalone-js-of-ocaml generated-files copy-to-fiat-rust copy-to-fiat-go
	@true
coq: $(REGULAR_VOFILES)
coq-without-bedrock2: $(REGULAR_EXCEPT_BEDROCK2_VOFILES)
bedrock2-backend: $(BEDROCK2_VOFILES)

lite: $(LITE_VOFILES)
nobigmem: $(NOBIGMEM_VOFILES)
only-heavy: $(HEAVY_VOFILES)
util: $(UTIL_VOFILES)
pre-standalone: $(PRE_STANDALONE_VOFILES)
some-early: $(SOME_EARLY_VOFILES)

# backwards-compat for coq ci:
new-pipeline: coq


printlite::
	@echo 'Files Made:'
	@for i in $(sort $(LITE_VOFILES)); do echo $$i; done
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

# this is needed on Windows to get make to see .vo files in -Q dependencies
ifneq ($(filter /cygdrive/%,$(CURDIR)),)
CURDIR_SAFE := $(shell cygpath -m "$(CURDIR)")
else
CURDIR_SAFE := $(CURDIR)
endif

EXTERNAL_DEPENDENCIES?=
EXTERNAL_BEDROCK2?=
EXTERNAL_COQUTIL?=
EXTERNAL_REWRITER?=
EXTERNAL_COQPRIME?=

ifneq ($(EXTERNAL_DEPENDENCIES),1)

REWRITER_FOLDER := rewriter
REWRITER_SRC := $(REWRITER_FOLDER)/src
REWRITER_NAME := Rewriter
COQPRIME_FOLDER := coqprime
COQPRIME_SRC := $(COQPRIME_FOLDER)/src
COQPRIME_NAME := Coqprime
BEDROCK2_ROOT_FOLDER := rupicola/bedrock2
BEDROCK2_FOLDER := $(BEDROCK2_ROOT_FOLDER)/bedrock2
BEDROCK2_SRC := $(BEDROCK2_FOLDER)/src
BEDROCK2_NAME := bedrock2
BEDROCK2_EXAMPLES_FOLDER := $(BEDROCK2_ROOT_FOLDER)/bedrock2
BEDROCK2_EXAMPLES_SRC := $(BEDROCK2_EXAMPLES_FOLDER)/src
BEDROCK2_EXAMPLES_NAME := bedrock2Examples
BEDROCK2_COMPILER_FOLDER := $(BEDROCK2_ROOT_FOLDER)/compiler
BEDROCK2_COMPILER_SRC := $(BEDROCK2_COMPILER_FOLDER)/src
BEDROCK2_COMPILER_NAME := compiler
COQUTIL_FOLDER := $(BEDROCK2_ROOT_FOLDER)/deps/coqutil
COQUTIL_SRC := $(COQUTIL_FOLDER)/src
COQUTIL_NAME := coqutil
RISCV_FOLDER := $(BEDROCK2_ROOT_FOLDER)/deps/riscv-coq
RISCV_SRC := $(RISCV_FOLDER)/src
RISCV_NAME := riscv
RUPICOLA_FOLDER := rupicola
RUPICOLA_SRC := $(RUPICOLA_FOLDER)/src
RUPICOLA_NAME := Rupicola
# dependency flags (-Q ...) separated by \n (Note: \n is not interpreted by make)
DEPFLAGS_NL :=

ifneq ($(EXTERNAL_REWRITER),1)
DEPFLAGS_NL:=-Q ${CURDIR_SAFE}/$(REWRITER_SRC)/$(REWRITER_NAME) $(REWRITER_NAME)\n-I ${CURDIR_SAFE}/$(REWRITER_SRC)/$(REWRITER_NAME)/Util/plugins\n$(DEPFLAGS_NL)
deps: rewriter
$(VOFILES): | rewriter
$(ALLDFILES): | rewriter
cleanall:: clean-rewriter
install: install-rewriter
endif

ifneq ($(SKIP_BEDROCK2),1)
ifneq ($(EXTERNAL_BEDROCK2),1)
DEPFLAGS_NL:=-Q ${CURDIR_SAFE}/$(RUPICOLA_SRC)/$(RUPICOLA_NAME) $(RUPICOLA_NAME) \n-Q ${CURDIR_SAFE}/$(BEDROCK2_SRC)/$(BEDROCK2_NAME) $(BEDROCK2_NAME)\n-Q ${CURDIR_SAFE}/$(BEDROCK2_EXAMPLES_SRC)/$(BEDROCK2_EXAMPLES_NAME) $(BEDROCK2_EXAMPLES_NAME)\n-Q ${CURDIR_SAFE}/$(BEDROCK2_COMPILER_SRC)/$(BEDROCK2_COMPILER_NAME) $(BEDROCK2_COMPILER_NAME)\n-Q ${CURDIR_SAFE}/$(RISCV_SRC)/$(RISCV_NAME) $(RISCV_NAME)\n$(DEPFLAGS_NL)
deps: bedrock2 bedrock2-compiler rupicola
$(VOFILES): | bedrock2 bedrock2-compiler rupicola
$(ALLDFILES): | bedrock2 bedrock2-compiler rupicola
cleanall:: clean-bedrock2 clean-bedrock2-compiler clean-rupicola
install: install-bedrock2 install-bedrock2-compiler install-rupicola
endif
endif

ifneq ($(EXTERNAL_COQUTIL),1)
DEPFLAGS_NL:=-Q ${CURDIR_SAFE}/$(COQUTIL_SRC)/$(COQUTIL_NAME) $(COQUTIL_NAME)\n$(DEPFLAGS_NL)
deps: coqutil
$(VOFILES): | coqutil
$(ALLDFILES): | coqutil
cleanall:: clean-coqutil
install: install-coqutil
endif

ifneq ($(EXTERNAL_COQPRIME),1)
DEPFLAGS_NL:=-Q ${CURDIR_SAFE}/$(COQPRIME_SRC)/$(COQPRIME_NAME) $(COQPRIME_NAME)\n$(DEPFLAGS_NL)
deps: coqprime
$(VOFILES): | coqprime
$(ALLDFILES): | coqprime
cleanall:: clean-coqprime
install: install-coqprime
endif

DEPFLAGS:=$(subst \n, ,$(DEPFLAGS_NL))

coqprime:
	$(MAKE) --no-print-directory -C $(COQPRIME_FOLDER) src/Coqprime/PrimalityTest/Zp.vo src/Coqprime/PrimalityTest/PocklingtonCertificat.vo

coqprime-all: coqprime
	$(MAKE) --no-print-directory -C $(COQPRIME_FOLDER)

clean-coqprime:
	$(MAKE) --no-print-directory -C $(COQPRIME_FOLDER) clean

install-coqprime:
	$(MAKE) --no-print-directory -C $(COQPRIME_FOLDER) install

rewriter:
	$(MAKE) --no-print-directory -C $(REWRITER_FOLDER)

clean-rewriter:
	$(MAKE) --no-print-directory -C $(REWRITER_FOLDER) clean

install-rewriter:
	$(MAKE) --no-print-directory -C $(REWRITER_FOLDER) install

coqutil:
	$(MAKE) --no-print-directory -C $(COQUTIL_FOLDER)

clean-coqutil:
	$(MAKE) --no-print-directory -C $(COQUTIL_FOLDER) clean

install-coqutil:
	$(MAKE) --no-print-directory -C $(COQUTIL_FOLDER) install

bedrock2: coqutil
	$(MAKE) --no-print-directory -C $(BEDROCK2_ROOT_FOLDER) bedrock2_ex

clean-bedrock2:
	$(MAKE) --no-print-directory -C $(BEDROCK2_ROOT_FOLDER) clean_bedrock2

install-bedrock2:
	$(MAKE) --no-print-directory -C $(BEDROCK2_ROOT_FOLDER) install_bedrock2

bedrock2-compiler: bedrock2
	$(MAKE) --no-print-directory -C $(BEDROCK2_ROOT_FOLDER) compiler_noex

clean-bedrock2-compiler:
	$(MAKE) --no-print-directory -C $(BEDROCK2_ROOT_FOLDER) clean_deps
	$(MAKE) --no-print-directory -C $(BEDROCK2_ROOT_FOLDER) clean_compiler

install-bedrock2-compiler:
	$(MAKE) --no-print-directory -C $(BEDROCK2_ROOT_FOLDER) install_compiler

rupicola: bedrock2 | bedrock2-compiler
	$(MAKE) --no-print-directory -C $(RUPICOLA_FOLDER) all

clean-rupicola:
	$(MAKE) --no-print-directory -C $(RUPICOLA_FOLDER) clean

install-rupicola:
	$(MAKE) --no-print-directory -C $(RUPICOLA_FOLDER) install_lib
endif

Makefile.coq: Makefile _CoqProject
	$(SHOW)'COQ_MAKEFILE -f _CoqProject > $@'
	$(HIDE)$(COQBIN)coq_makefile -f _CoqProject INSTALLDEFAULTROOT = $(INSTALLDEFAULTROOT) -o $@

include Makefile.examples
include Makefile.standalone
include Makefile.js-html

$(STANDALONE:%=src/ExtractionOCaml/%.ml): src/StandaloneOCamlMain.vo
$(BEDROCK2_STANDALONE:%=src/ExtractionOCaml/%.ml): src/Bedrock/Standalone/StandaloneOCamlMain.vo
$(PERF_STANDALONE:%=src/ExtractionOCaml/%.ml): src/Rewriter/PerfTesting/StandaloneOCamlMain.vo
$(STANDALONE:%=src/ExtractionHaskell/%.hs): src/StandaloneHaskellMain.vo
$(BEDROCK2_STANDALONE:%=src/ExtractionHaskell/%.hs): src/Bedrock/Standalone/StandaloneHaskellMain.vo
$(STANDALONE_JS_OF_OCAML:%=src/ExtractionJsOfOCaml/%.ml): src/StandaloneJsOfOCamlMain.vo
$(BEDROCK2_STANDALONE_JS_OF_OCAML:%=src/ExtractionJsOfOCaml/%.ml): src/Bedrock/Standalone/StandaloneJsOfOCamlMain.vo
# $(PERF_STANDALONE:%=src/ExtractionHaskell/%.hs): src/Rewriter/PerfTesting/StandaloneHaskellMain.vo

pre-standalone-extracted: $(STANDALONE_OCAML:%=src/ExtractionOCaml/%.ml) $(STANDALONE_JS_OF_OCAML:%=src/ExtractionJsOfOCaml/%.ml) $(STANDALONE_HASKELL:%=src/ExtractionHaskell/%.hs)

$(STANDALONE_OCAML:%=src/ExtractionOCaml/%.ml) : %.ml : %.v
	$(SHOW)'COQC $<'
	$(HIDE)$(TIMER) $(COQC) $(COQDEBUG) $(COQFLAGS) $(COQLIBS) $<
	$(HIDE)cat $*.tmp.ml | tr -d '\r' > $@ && rm $*.tmp.ml
	$(HIDE)cat $*.tmp.mli | tr -d '\r' > $*.mli && rm $*.tmp.mli

$(STANDALONE_JS_OF_OCAML:%=src/ExtractionJsOfOCaml/%.ml) : %.ml : %.v
	$(SHOW)'COQC $<'
	$(HIDE)$(TIMER) $(COQC) $(COQDEBUG) $(COQFLAGS) $(COQLIBS) $<
	$(HIDE)cat $*.tmp.ml | tr -d '\r' > $@ && rm $*.tmp.ml
	$(HIDE)cat $*.tmp.mli | tr -d '\r' > $*.mli && rm $*.tmp.mli

$(STANDALONE_HASKELL:%=src/ExtractionHaskell/%.hs) : %.hs : %.v src/haskell.sed src/StandaloneHaskellMain.vo
	$(SHOW)'COQC $< > $@'
	$(HIDE)$(TIMER) $(COQC) $(COQDEBUG) $(COQFLAGS) $(COQLIBS) $< > $@.tmp
	$(HIDE)cat $@.tmp | tr -d '\r' | sed -f src/haskell.sed > $@ && rm $@.tmp

.SECONDEXPANSION:

# Perf testing
PERF_MAKEFILE = src/Rewriter/PerfTesting/Specific/generated/primes.mk
ifneq ($(SKIP_INCLUDE),1)
include $(PERF_MAKEFILE)
endif

$(PERF_MAKEFILE): Makefile src/Rewriter/PerfTesting/Specific/make.py primes.txt
	./src/Rewriter/PerfTesting/Specific/make.py primes.txt
PERF_MAX_TIME?=600 # 10 minutes
PERF_MAX_MEM?=10000000 # 10 GB in kbytes
PERF_MAX_STACK?=1000000
PERF_TIMEOUT?=timeout $(PERF_MAX_TIME) # etc/timeout/timeout -m $(PERF_MAX_MEM) # limit to 10 GB # https://raw.githubusercontent.com/pshved/timeout/master/timeout
# PERF_TIMEOUT?=timeout $(PERF_MAX_TIME)
# apparently ulimit -m doesn't work anymore https://superuser.com/a/1497437/59575 / https://thirld.com/blog/2012/02/09/things-to-remember-when-using-ulimit/
PERF_SET_LIMITS = ulimit -S -s $(PERF_MAX_STACK); ulimit -S -m $(PERF_MAX_MEM); ulimit -S -v $(PERF_MAX_MEM);

.PHONY: perf perf-vos perf-extraction
PERF_VOLOGS := $(PERF_PRIME_VOS:.vo=.log)
PERF_SHLOGS := $(PERF_PRIME_SHS:.sh=.log)
PERF_LOGS := $(PERF_VOLOGS) $(PERF_SHLOGS)
ALL_PERF_LOGS := $(PERF_LOGS) $(PERF_LOGS:.log=.log.tmp)

perf-vos: $(PERF_VOLOGS) \
	$(PERF_MAKEFILE) \
	src/Rewriter/PerfTesting/Core.vo \

FILTER_OUT = $(foreach v,$(2),$(if $(findstring $(1),$(v)),,$(v)))
FILTER = $(foreach v,$(2),$(if $(findstring $(1),$(v)),$(v),))
.PHONY: perf-except-computed-vos
perf-except-computed-vos: $(call FILTER_OUT,ComputedOf,$(PERF_VOLOGS)) \
	$(PERF_MAKEFILE) \
	src/Rewriter/PerfTesting/Core.vo \

.PHONY: perf-only-computed-vos
perf-only-computed-vos: $(call FILTER,ComputedOf,$(PERF_VOLOGS)) \
	$(PERF_MAKEFILE) \
	src/Rewriter/PerfTesting/Core.vo \

perf-extraction: $(PERF_SHLOGS) \
	$(PERF_MAKEFILE) \
	perf-standalone

.PHONY: perf perf-except-computed perf-only-computed
perf: perf-extraction perf-vos
perf-except-computed: perf-extraction perf-except-computed-vos
perf-only-computed: perf-extraction perf-only-computed-vos

PERF_PRE_TXTS := perf-old-vm-times perf-new-vm-times perf-new-extraction-times perf-old-cbv-times \
	perf-new-extraction-over-old-vm perf-new-vm-over-old-vm perf-old-vm-over-old-vm \
	perf-new-extraction-over-new-extraction perf-new-vm-over-new-extraction perf-old-vm-over-new-extraction
PERF_TXTS := $(addsuffix .txt,$(PERF_PRE_TXTS) \
	$(foreach kind,UnsaturatedSolinas WordByWordMontgomery, \
	$(foreach bitwidth,32 64, \
	$(addsuffix --only-$(kind)-x$(bitwidth),$(PERF_PRE_TXTS)))))

.PHONY: perf-csv
perf-csv: perf.csv perf-graph.csv $(PERF_TXTS)

.PHONY: perf.csv
perf.csv:
	$(SHOW)'PYTHON > $@'
	$(HIDE)$(file >$@.list.tmp,)
	$(HIDE)$(foreach i,$(wildcard $(ALL_PERF_LOGS)),$(file >>$@.list.tmp,$(i)))
	$(HIDE)./src/Rewriter/PerfTesting/Specific/to_csv.py --file-list $@.list.tmp > $@.tmp
	$(HIDE)cat $@.tmp | sed 's/\s*$$//g' > $@ && rm -f $@.list.tmp $@.tmp

.PHONY: perf-graph.csv
perf-graph.csv:
	$(SHOW)'PYTHON > $@'
	$(HIDE)$(file >$@.list.tmp,)
	$(HIDE)$(foreach i,$(wildcard $(ALL_PERF_LOGS)),$(file >>$@.list.tmp,$(i)))
	$(HIDE)./src/Rewriter/PerfTesting/Specific/to_csv.py --for-graph --file-list $@.list.tmp > $@.tmp
	$(HIDE)cat $@.tmp | sed 's/\s*$$//g' > $@ && rm -f $@.list.tmp $@.tmp

.PHONY: $(PERF_TXTS)
$(PERF_TXTS) : %.txt :
	$(SHOW)'PYTHON > $@'
	$(HIDE)$(file >$@.list.tmp,)
	$(HIDE)$(foreach i,$(wildcard $(ALL_PERF_LOGS)),$(file >>$@.list.tmp,$(i)))
	$(HIDE)./src/Rewriter/PerfTesting/Specific/to_csv.py --$* --txt --file-list $@.list.tmp > $@.tmp
	$(HIDE)cat $@.tmp | sed 's/\s*$$//g' > $@ && rm -f $@.list.tmp $@.tmp

# work around COQBUG(https://github.com/coq/coq/issues/10495)
.PHONY: clean-tmp-native-work-around-bug-10495
clean-tmp-native-work-around-bug-10495::
	rm -f /tmp/Coq_native*.{cmi,cmx,cmxs,o,native}

$(PERF_PRIME_VOS:.vo=.log) : %.log : %.v src/Rewriter/PerfTesting/Core.vo
	$(SHOW)'PERF COQC $< > $@'
	$(HIDE)($(PERF_SET_LIMITS) $(TIMER) $(PERF_TIMEOUT) $(COQC) $(COQDEBUG) $(COQFLAGS) $(COQLIBS) $< && touch $@.ok) > $@.tmp
	$(HIDE)rm $@.ok
	$(HIDE)cat $@.tmp | tr -d '\r' | sed 's/\s*$$//g' > $@ && rm -f $@.tmp

$(PERF_PRIME_SHS:.sh=.log) : %.log : %.sh $(PERF_STANDALONE:%=src/ExtractionOCaml/%)
	$(SHOW)'PERF SH $< > $@'
	$(HIDE)($(PERF_SET_LIMITS) $(TIMER) $(PERF_TIMEOUT) bash $< && touch $@.ok) > $@.tmp
	$(HIDE)rm $@.ok
	$(HIDE)cat $@.tmp | tr -d '\r' | sed 's/\s*$$//g' > $@ && rm -f $@.tmp


curves: $(filter src/Spec/%Curve%.vo,$(REGULAR_VOFILES)) $(filter src/Curves/%.vo,$(REGULAR_VOFILES))

.PHONY: $(CHECK_OUTPUTS) $(ACCEPT_OUTPUTS)
check-output: $(CHECK_OUTPUTS)
accept-output: $(ACCEPT_OUTPUTS)
$(CHECK_OUTPUTS) : check-% : $(OUTPUT_VOS)
	$(SHOW)'DIFF $*'
	$(HIDE)cat output-tests/$*.expected | grep -v '^Arguments ' | tr '\n' ' ' > output-tests/$*.expected.processed
	$(HIDE)cat $*.out | grep -v '^Arguments ' | tr '\n' ' ' > $*.out.processed
	$(HIDE)diff --ignore-space-change output-tests/$*.expected.processed $*.out.processed || (RV=$$?; diff --ignore-space-change output-tests/$*.expected $*.out; echo "To accept the new output, run make accept-$*"; exit $$RV)

$(ACCEPT_OUTPUTS) : accept-% :
	$(SHOW)'ACCEPT $*.out'
	$(HIDE)cp -f $*.out output-tests/$*.expected

clean::
	rm -f Makefile.coq

cleanall:: clean
	rm -rf src/Rewriter/PerfTesting/Specific/generated

install: coq $(filter %.vo,$(FILESTOINSTALL))
install-without-bedrock2: coq-without-bedrock2 $(filter %.vo,$(filter-out $(BEDROCK2_FILES_PATTERN),$(FILESTOINSTALL)))

install-without-bedrock2:
	$(HIDE)$(MAKE) -f Makefile.coq install FILESTOINSTALL="$(filter-out $(BEDROCK2_FILES_PATTERN),$(FILESTOINSTALL))"

install-standalone-ocaml: standalone-ocaml
install-standalone-haskell: standalone-haskell

.PHONY: validate
validate: Makefile.coq
	$(MAKE) -f Makefile.coq validate VOFILES="$(REGULAR_VOFILES)"

.PHONY: print_DEPFLAGS
print_DEPFLAGS:
	@echo "DEPFLAGS_NL ="
	@printf -- '$(DEPFLAGS_NL)'

# This target is used to update the _CoqProject file.
SORT_COQPROJECT = sed 's,[^/]*/,~&,g' | env LC_COLLATE=C sort | sed 's,~,,g'
EXISTING_COQPROJECT_CONTENTS_SORTED:=$(shell cat _CoqProject 2>&1 | $(SORT_COQPROJECT))
WARNINGS_PLUS := +implicit-core-hint-db,+implicits-in-term,+non-reversible-notation,+deprecated-intros-until-0,+deprecated-focus,+unused-intro-pattern,+variable-collision,+unexpected-implicit-declaration,+omega-is-deprecated,+deprecated-instantiate-syntax,+non-recursive,+undeclared-scope,+deprecated-hint-rewrite-without-locality,+deprecated-hint-without-locality,+deprecated-instance-without-locality,+deprecated-typeclasses-transparency-without-locality
# Remove unsupported-attributes once we stop supporting < 8.14
WARNINGS := $(WARNINGS_PLUS),unsupported-attributes
COQPROJECT_CMD:=(echo '-R $(SRC_DIR) $(MOD_NAME)'; printf -- '$(DEPFLAGS_NL)'; echo '-arg -w -arg $(WARNINGS)'; echo '-arg -native-compiler -arg ondemand'; echo 'src/Everything.v'; echo 'src/Bedrock/Everything.v'; find src -type f -name '*.v' | $(GREP_EXCLUDE_SPECIAL) | $(GREP_EXCLUDE_GENERATED) | $(SORT_COQPROJECT))
NEW_COQPROJECT_CONTENTS_SORTED:=$(shell $(COQPROJECT_CMD) | $(SORT_COQPROJECT))

ifneq ($(EXISTING_COQPROJECT_CONTENTS_SORTED),$(NEW_COQPROJECT_CONTENTS_SORTED))
.PHONY: _CoqProject
_CoqProject:
	$(SHOW)'ECHO > $@'
	$(HIDE)$(COQPROJECT_CMD) > $@
endif

printdeps::
	$(HIDE)$(foreach vo,$(filter %.vo,$(MAKECMDGOALS)),echo '$(vo): $(call vo_closure,$(vo))'; )

printreversedeps::
	$(HIDE)$(foreach vo,$(filter %.vo,$(MAKECMDGOALS)),echo '$(vo): $(call vo_reverse_closure,$(VOFILES),$(vo))'; )

REGULAR_WITH_BEDROCK2_LIBS := $(sort $(subst /,.,$(patsubst src/%.vo,Crypto/%,$(filter-out src/Bedrock/Everything.vo src/Everything.vo $(AFTER_EVERYTHING_VOFILES),$(REGULAR_WITH_BEDROCK2_VOFILES)))))
REGULAR_EXCEPT_BEDROCK2_LIBS := $(sort $(subst /,.,$(patsubst src/%.vo,Crypto/%,$(filter-out src/Bedrock/Everything.vo src/Everything.vo $(AFTER_EVERYTHING_VOFILES),$(REGULAR_EXCEPT_BEDROCK2_VOFILES)))))
make_Everything_v_cmd_gen = { printf 'Require Import\n'; printf '%s\n' $(1); printf '.\n'; }
make_Everything_v_cmd := $(call make_Everything_v_cmd_gen,$(REGULAR_EXCEPT_BEDROCK2_LIBS))
make_Bedrock_Everything_v_cmd := $(call make_Everything_v_cmd_gen,$(REGULAR_WITH_BEDROCK2_LIBS))
EXISTING_EVERYTHING_V_CONTENTS:=$(shell cat src/Everything.v 2>&1)
EXISTING_BEDROCK_EVERYTHING_V_CONTENTS:=$(shell cat src/Bedrock/Everything.v 2>&1)
NEW_EVERYTHING_V_CONTENTS:=$(shell $(make_Everything_v_cmd))
NEW_BEDROCK_EVERYTHING_V_CONTENTS:=$(shell $(make_Bedrock_Everything_v_cmd))
ifneq ($(EXISTING_EVERYTHING_V_CONTENTS),$(NEW_EVERYTHING_V_CONTENTS))
.PHONY: src/Everything.v
src/Everything.v:
	$(SHOW)'ECHO > $@'
	$(HIDE)$(make_Everything_v_cmd) > $@
endif

ifneq ($(EXISTING_BEDROCK_EVERYTHING_V_CONTENTS),$(NEW_BEDROCK_EVERYTHING_V_CONTENTS))
.PHONY: src/Bedrock/Everything.v
src/Bedrock/Everything.v:
	$(SHOW)'ECHO > $@'
	$(HIDE)$(make_Bedrock_Everything_v_cmd) > $@
endif
