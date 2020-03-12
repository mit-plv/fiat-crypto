.SUFFIXES:

MOD_NAME := Crypto
SRC_DIR  := src

BINDIR?=/usr/local/bin
# or $(shell opam config var bin) ?

GHC?=ghc
GHCFLAGS?= # -XStrict

CFLAGS?=

CARGO_BUILD := cargo build

SKIP_BEDROCK2?=

PROFILE?=
VERBOSE?=
SHOW := $(if $(VERBOSE),@true "",@echo "")
HIDE := $(if $(VERBOSE),,@)
INSTALLDEFAULTROOT := Crypto

.PHONY: coq clean update-_CoqProject cleanall install \
	coq-without-bedrock2 install-without-bedrock2 \
	install-rewriter clean-rewriter rewriter \
	install-coqprime clean-coqprime coqprime coqprime-all \
	bedrock2 clean-bedrock2 install-bedrock2 coqutil clean-coqutil install-coqutil \
	install-standalone install-standalone-ocaml install-standalone-haskell \
	uninstall-standalone uninstall-standalone-ocaml uninstall-standalone-haskell \
	util c-files rust-files go-files java-files \
	bedrock2-backend \
	deps \
	nobigmem print-nobigmem \
	lite only-heavy printlite \
	some-early pre-standalone standalone standalone-haskell standalone-ocaml \
	test-c-files test-rust-files test-go-files test-java-files \
	only-test-c-files only-test-rust-files only-test-go-files only-test-java-files \
	javadoc only-javadoc \
	check-output accept-output

TIMEFMT?="$@ (real: %e, user: %U, sys: %S, mem: %M ko)"
-include Makefile.coq
include etc/coq-scripts/Makefile.vo_closure

.DEFAULT_GOAL := all

SORT_COQPROJECT = sed 's,[^/]*/,~&,g' | env LC_COLLATE=C sort | sed 's,~,,g' | uniq
WARNINGS := +implicit-core-hint-db,+implicits-in-term,+non-reversible-notation,+deprecated-intros-until-0,+deprecated-focus,+unused-intro-pattern,+variable-collision,-deprecated-hint-constr
update-_CoqProject::
	$(SHOW)'ECHO > _CoqProject'
	$(HIDE)(echo '-R $(SRC_DIR) $(MOD_NAME)'; echo '-arg -w -arg $(WARNINGS)'; (git ls-files 'src/*.v' | $(GREP_EXCLUDE_SPECIAL_VOFILES) | $(SORT_COQPROJECT))) > _CoqProject

# coq .vo files that are not compiled using coq_makefile
SPECIAL_VOFILES := \
	src/ExtractionOCaml/%.vo \
	src/ExtractionHaskell/%.vo
GREP_EXCLUDE_SPECIAL_VOFILES := grep -v '^src/Extraction\(OCaml\|Haskell\)/'
PERFTESTING_VO := \
	src/Rewriter/PerfTesting/Core.vo \
	src/Rewriter/PerfTesting/StandaloneOCamlMain.vo
BEDROCK2_FILES_PATTERN := \
	src/ExtractionOCaml/bedrock2_% \
	src/ExtractionHaskell/bedrock2_% \
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
	src/Curves/Weierstrass/Jacobian.vo \
	src/Curves/Weierstrass/Projective.vo \
	src/Rewriter/RulesGood.vo \
	src/Rewriter/All.vo \
	$(PERFTESTING_VO) \
	$(EXCLUDED_VO)
NOBIGMEM_UNMADE_VOFILES := \
	src/Curves/Weierstrass/AffineProofs.vo \
	src/Curves/Weierstrass/Jacobian.vo \
	src/Curves/Weierstrass/Projective.vo \
	$(PERFTESTING_VO) \
	$(EXCLUDED_VO)
REGULAR_VOFILES := $(filter-out $(EXCLUDE_PATTERN) $(SPECIAL_VOFILES),$(VOFILES))
REGULAR_EXCEPT_BEDROCK2_VOFILES := $(filter-out $(BEDROCK2_FILES_PATTERN),$(REGULAR_VOFILES))
BEDROCK2_VOFILES := $(filter $(BEDROCK2_FILES_PATTERN),$(REGULAR_VOFILES))
PRE_STANDALONE_PRE_VOFILES := $(filter src/Standalone%.vo,$(REGULAR_VOFILES))
UTIL_PRE_VOFILES := $(filter src/Algebra/%.vo src/Tactics/%.vo src/Util/%.vo,$(REGULAR_VOFILES))
SOME_EARLY_VOFILES := \
  src/Arithmetic/Core.vo \
  src/Rewriter/AllTacticsExtra.vo
COPY_TO_FIAT_RUST := \
	AUTHORS \
	CONTRIBUTORS \
	LICENSE

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

C_DIR := fiat-c/src/
RS_DIR := fiat-rust/src/
GO_DIR := fiat-go/src/
JAVA_DIR := fiat-java/src/
JAVADOC_DIR := fiat-java/doc/

UNSATURATED_SOLINAS_BASE_FILES := curve25519_64 curve25519_32 p521_64 p448_solinas_64 # p224_solinas_64
WORD_BY_WORD_MONTGOMERY_BASE_FILES := p256_64 p256_32 p384_64 p384_32 secp256k1_64 secp256k1_32 p224_64 p224_32 p434_64 # p434_32
ALL_BASE_FILES := $(UNSATURATED_SOLINAS_BASE_FILES) $(WORD_BY_WORD_MONTGOMERY_BASE_FILES)

UNSATURATED_SOLINAS_C_FILES := $(patsubst %,$(C_DIR)%.c,$(UNSATURATED_SOLINAS_BASE_FILES))
WORD_BY_WORD_MONTGOMERY_C_FILES := $(patsubst %,$(C_DIR)%.c,$(WORD_BY_WORD_MONTGOMERY_BASE_FILES))
ALL_C_FILES := $(patsubst %,$(C_DIR)%.c,$(ALL_BASE_FILES))

UNSATURATED_SOLINAS_RUST_FILES := $(patsubst %,$(RS_DIR)%.rs,$(UNSATURATED_SOLINAS_BASE_FILES))
WORD_BY_WORD_MONTGOMERY_RUST_FILES := $(patsubst %,$(RS_DIR)%.rs,$(WORD_BY_WORD_MONTGOMERY_BASE_FILES))
ALL_RUST_FILES := $(patsubst %,$(RS_DIR)%.rs,$(ALL_BASE_FILES))

UNSATURATED_SOLINAS_GO_FILES := $(patsubst %,$(GO_DIR)%.go,$(UNSATURATED_SOLINAS_BASE_FILES))
WORD_BY_WORD_MONTGOMERY_GO_FILES := $(patsubst %,$(GO_DIR)%.go,$(WORD_BY_WORD_MONTGOMERY_BASE_FILES))
ALL_GO_FILES := $(patsubst %,$(GO_DIR)%.go,$(ALL_BASE_FILES))

# Java only really supports 32-bit builds, because we have neither 64x64->64x64 multiplication, nor uint128
# Java also requires that class names match file names
# from https://stackoverflow.com/q/42925485/377022
to_title_case = $(shell echo '$(1)' | sed 's/.*/\L&/; s/[a-z]*/\u&/g')
JAVA_RENAME = $(foreach i,$(patsubst %_32,%,$(filter %_32,$(1))),Fiat$(call to_title_case,$(subst _, ,$(i))))
UNSATURATED_SOLINAS_JAVA_FILES := $(patsubst %,$(JAVA_DIR)%.java,$(call JAVA_RENAME,$(UNSATURATED_SOLINAS_BASE_FILES)))
WORD_BY_WORD_MONTGOMERY_JAVA_FILES := $(patsubst %,$(JAVA_DIR)%.java,$(call JAVA_RENAME,$(WORD_BY_WORD_MONTGOMERY_BASE_FILES)))
ALL_JAVA_FILES := $(UNSATURATED_SOLINAS_JAVA_FILES) $(WORD_BY_WORD_MONTGOMERY_JAVA_FILES)

UNSATURATED_SOLINAS_FUNCTIONS := carry_mul carry_square carry add sub opp selectznz to_bytes from_bytes
FUNCTIONS_FOR_25519 := $(UNSATURATED_SOLINAS_FUNCTIONS) carry_scmul121666
WORD_BY_WORD_MONTGOMERY_FUNCTIONS := mul square add sub opp from_montgomery nonzero selectznz to_bytes from_bytes
UNSATURATED_SOLINAS := src/ExtractionOCaml/unsaturated_solinas
WORD_BY_WORD_MONTGOMERY := src/ExtractionOCaml/word_by_word_montgomery

GO_EXTRA_ARGS_ALL := --cmovznz-by-mul --widen-carry --widen-bytes
GO_EXTRA_ARGS_64  := --no-wide-int $(GO_EXTRA_ARGS_ALL)
GO_EXTRA_ARGS_32  := $(GO_EXTRA_ARGS_ALL)

JAVA_EXTRA_ARGS_ALL := --cmovznz-by-mul --widen-carry --widen-bytes --internal-static --only-signed
JAVA_EXTRA_ARGS_64  := --no-wide-int $(JAVA_EXTRA_ARGS_ALL)
JAVA_EXTRA_ARGS_32  := $(JAVA_EXTRA_ARGS_ALL)

OUTPUT_VOS := \
	src/Fancy/Montgomery256.vo \
	src/Fancy/Barrett256.vo

OUTPUT_PREOUTS := \
	Crypto.Fancy.Montgomery256.Prod.MontRed256 \
	Crypto.Fancy.Montgomery256.prod_montred256_correct \
	Crypto.Fancy.Montgomery256.prod_montred256_correct.Assumptions \
	Crypto.Fancy.Montgomery256.montred256 \
	Crypto.Fancy.Barrett256.Prod.MulMod \
	Crypto.Fancy.Barrett256.prod_barrett_red256_correct \
	Crypto.Fancy.Barrett256.prod_barrett_red256_correct.Assumptions \
	Crypto.Fancy.Barrett256.barrett_red256

CHECK_OUTPUTS := $(addprefix check-,$(OUTPUT_PREOUTS))
ACCEPT_OUTPUTS := $(addprefix accept-,$(OUTPUT_PREOUTS))

all: coq standalone-ocaml perf-standalone c-files rust-files go-files java-files check-output
coq: $(REGULAR_VOFILES)
coq-without-bedrock2: $(REGULAR_EXCEPT_BEDROCK2_VOFILES)
bedrock2-backend: $(BEDROCK2_VOFILES)
c-files: $(ALL_C_FILES)
rust-files: $(ALL_RUST_FILES)
go-files: $(ALL_GO_FILES)
java-files: $(ALL_JAVA_FILES)

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

# Remove -undeclared-scope once we stop supporting 8.9
OTHERFLAGS += -w -notation-overridden,-undeclared-scope
ifneq ($(PROFILE),)
OTHERFLAGS += -profile-ltac
endif

export OTHERFLAGS

ifneq ($(filter /cygdrive/%,$(CURDIR)),)
CURDIR_SAFE := $(shell cygpath -m "$(CURDIR)")
else
CURDIR_SAFE := $(CURDIR)
endif

EXTERNAL_DEPENDENCIES?=
EXTERNAL_BEDROCK2?=
EXTERNAL_REWRITER?=
EXTERNAL_COQPRIME?=

ifneq ($(EXTERNAL_DEPENDENCIES),1)

REWRITER_FOLDER := rewriter
REWRITER_SRC := $(REWRITER_FOLDER)/src
COQPRIME_FOLDER := coqprime
COQPRIME_SRC := $(COQPRIME_FOLDER)/src
BEDROCK2_FOLDER := bedrock2/bedrock2
BEDROCK2_SRC := $(BEDROCK2_FOLDER)/src
BEDROCK2_NAME := bedrock2
COQUTIL_FOLDER := bedrock2/deps/coqutil
COQUTIL_SRC := $(COQUTIL_FOLDER)/src
COQUTIL_NAME := coqutil
# Work around COQBUG(https://github.com/coq/coq/issues/11834)
SYS_OS_TYPE := $(shell "$(OCAMLFIND)" ocamlc etc/sys_os_type.ml -o etc/sys_os_type.exe && etc/sys_os_type.exe)
COQPATH_TEMP:=
ifeq ($(SYS_OS_TYPE),Win32)
COQPATH_SEP:=;
else
COQPATH_SEP:=:
endif

ifneq ($(EXTERNAL_REWRITER),1)
COQPATH_TEMP:=${CURDIR_SAFE}/$(REWRITER_SRC)$(COQPATH_SEP)$(COQPATH_TEMP)
deps: rewriter
$(VOFILES): | rewriter
$(ALLDFILES): | rewriter
cleanall:: clean-rewriter
install: install-rewriter
endif

ifneq ($(SKIP_BEDROCK2),1)
ifneq ($(EXTERNAL_BEDROCK2),1)
COQPATH_TEMP:=${CURDIR_SAFE}/$(BEDROCK2_SRC)$(COQPATH_SEP)${CURDIR_SAFE}/$(COQUTIL_SRC)$(COQPATH_SEP)$(COQPATH_TEMP)
deps: coqutil bedrock2
$(VOFILES): | coqutil bedrock2
$(ALLDFILES): | coqutil bedrock2
cleanall:: clean-bedrock2 clean-coqutil
install: install-bedrock2 install-coqutil
endif
endif

ifneq ($(EXTERNAL_COQPRIME),1)
COQPATH_TEMP:=${CURDIR_SAFE}/$(COQPRIME_SRC)$(COQPATH_SEP)$(COQPATH_TEMP)
deps: coqprime
$(VOFILES): | coqprime
$(ALLDFILES): | coqprime
cleanall:: clean-coqprime
install: install-coqprime
endif

COQPATH?=$(patsubst %$(COQPATH_SEP),%,$(COQPATH_TEMP))
export COQPATH

coqprime:
	$(MAKE) --no-print-directory -C $(COQPRIME_FOLDER) src/Coqprime/PrimalityTest/Zp.vo

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
	$(MAKE) --no-print-directory -C $(BEDROCK2_FOLDER) noex

clean-bedrock2:
	$(MAKE) --no-print-directory -C $(BEDROCK2_FOLDER) clean

install-bedrock2:
	$(MAKE) --no-print-directory -C $(BEDROCK2_FOLDER) install
endif

# Note that the bit about OTHERFLAGS is to work around COQBUG(https://github.com/coq/coq/issues/10905)
Makefile.coq: Makefile _CoqProject
	$(SHOW)'COQ_MAKEFILE -f _CoqProject > $@'
	$(HIDE)$(COQBIN)coq_makefile -f _CoqProject INSTALLDEFAULTROOT = $(INSTALLDEFAULTROOT) -o Makefile-old && cat Makefile-old | sed s'/^printenv:/printenv::/g' | sed s'/^printenv:::/printenv::/g' | sed s'/^all:/all-old:/g' | sed s'/OTHERFLAGS        :=/OTHERFLAGS        ?=/g' > $@ && rm -f Makefile-old


STANDALONE := unsaturated_solinas saturated_solinas word_by_word_montgomery base_conversion
BEDROCK2_STANDALONE := $(addprefix bedrock2_,$(STANDALONE))
ifneq ($(SKIP_BEDROCK2),1)
STANDALONE += $(BEDROCK2_STANDALONE)
endif
PERF_STANDALONE := perf_unsaturated_solinas perf_word_by_word_montgomery

STANDALONE_OCAML := $(STANDALONE) $(PERF_STANDALONE)
STANDALONE_HASKELL := $(STANDALONE)

OCAML_BINARIES := $(STANDALONE:%=src/ExtractionOCaml/%)
HASKELL_BINARIES := $(STANDALONE:%=src/ExtractionHaskell/%)

$(STANDALONE:%=src/ExtractionOCaml/%.ml): src/StandaloneOCamlMain.vo
$(BEDROCK2_STANDALONE:%=src/ExtractionOCaml/%.ml): src/Bedrock/StandaloneOCamlMain.vo
$(PERF_STANDALONE:%=src/ExtractionOCaml/%.ml): src/Rewriter/PerfTesting/StandaloneOCamlMain.vo
$(STANDALONE:%=src/ExtractionHaskell/%.hs): src/StandaloneHaskellMain.vo
$(BEDROCK2_STANDALONE:%=src/ExtractionHaskell/%.hs): src/Bedrock/StandaloneHaskellMain.vo
# $(PERF_STANDALONE:%=src/ExtractionHaskell/%.hs): src/Rewriter/PerfTesting/StandaloneHaskellMain.vo

$(STANDALONE_OCAML:%=src/ExtractionOCaml/%.ml) : %.ml : %.v
	$(SHOW)'COQC $< > $@'
	$(HIDE)$(TIMER) $(COQC) $(COQDEBUG) $(COQFLAGS) $(COQLIBS) $< > $@.tmp
	$(HIDE)cat $@.tmp | tr -d '\r' > $@ && rm -f $@.tmp

$(STANDALONE_HASKELL:%=src/ExtractionHaskell/%.hs) : %.hs : %.v src/haskell.sed
	$(SHOW)'COQC $< > $@'
	$(HIDE)$(TIMER) $(COQC) $(COQDEBUG) $(COQFLAGS) $(COQLIBS) $< > $@.tmp
	$(HIDE)cat $@.tmp | tr -d '\r' | sed -f src/haskell.sed > $@ && rm -f $@.tmp

# pass -w -20 to disable the unused argument warning
# unix package needed for Unix.gettimeofday for the perf_* binaries
$(STANDALONE_OCAML:%=src/ExtractionOCaml/%) : % : %.ml
	$(SHOW)'OCAMLOPT $< -o $@'
	$(HIDE)$(TIMER) ocamlfind ocamlopt -package unix -linkpkg -w -20 -o $@ $<

$(STANDALONE_HASKELL:%=src/ExtractionHaskell/%) : % : %.hs
	$(SHOW)'GHC $< -o $@'
	$(HIDE)$(TIMER) $(GHC) $(GHCFLAGS) -o $@ $<

standalone: standalone-haskell standalone-ocaml
standalone-haskell: $(STANDALONE_HASKELL:%=src/ExtractionHaskell/%)
standalone-ocaml: $(STANDALONE_OCAML:%=src/ExtractionOCaml/%)

$(UNSATURATED_SOLINAS_C_FILES): $(UNSATURATED_SOLINAS) # Makefile

$(WORD_BY_WORD_MONTGOMERY_C_FILES): $(WORD_BY_WORD_MONTGOMERY) # Makefile

# 2^255 - 19
$(C_DIR)curve25519_64.c : $(C_DIR)curve25519_%.c :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(UNSATURATED_SOLINAS) --static '25519' '5' '2^255 - 19' '$*' $(FUNCTIONS_FOR_25519) && touch $@.ok) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

# 2^255 - 19
$(C_DIR)curve25519_32.c : $(C_DIR)curve25519_%.c :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(UNSATURATED_SOLINAS) --static '25519' '10' '2^255 - 19' '$*' $(FUNCTIONS_FOR_25519) && touch $@.ok) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

# 2^521 - 1
$(C_DIR)p521_64.c : $(C_DIR)p521_%.c :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(UNSATURATED_SOLINAS) --static 'p521' '9' '2^521 - 1' '$*' $(UNSATURATED_SOLINAS_FUNCTIONS) && touch $@.ok) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

## 2^224 - 2^96 + 1 ## does not bounds check
#$(C_DIR)p224_solinas_64.c : $(C_DIR)p224_solinas_%.c :
#	$(SHOW)'SYNTHESIZE > $@'
#	$(HIDE)rm -f $@.ok
#	$(HIDE)($(TIMER) $(UNSATURATED_SOLINAS) --static 'p224' '4' '2^224 - 2^96 + 1' '$*' $(UNSATURATED_SOLINAS_FUNCTIONS) && touch $@.ok) > $@.tmp
#	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

# 2^448 - 2^224 - 1
$(C_DIR)p448_solinas_64.c : $(C_DIR)p448_solinas_%.c :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(UNSATURATED_SOLINAS) --static 'p448' '8' '2^448 - 2^224 - 1' '$*' $(UNSATURATED_SOLINAS_FUNCTIONS) && touch $@.ok) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

# 2^256 - 2^224 + 2^192 + 2^96 - 1
$(C_DIR)p256_64.c $(C_DIR)p256_32.c : $(C_DIR)p256_%.c :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(WORD_BY_WORD_MONTGOMERY) --static 'p256' '2^256 - 2^224 + 2^192 + 2^96 - 1' '$*' $(WORD_BY_WORD_MONTGOMERY_FUNCTIONS) && touch $@.ok) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

# 2^256 - 2^32 - 977
$(C_DIR)secp256k1_64.c $(C_DIR)secp256k1_32.c : $(C_DIR)secp256k1_%.c :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(WORD_BY_WORD_MONTGOMERY) --static 'secp256k1' '2^256 - 2^32 - 977' '$*' $(WORD_BY_WORD_MONTGOMERY_FUNCTIONS) && touch $@.ok) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

# 2^384 - 2^128 - 2^96 + 2^32 - 1
$(C_DIR)p384_64.c $(C_DIR)p384_32.c : $(C_DIR)p384_%.c :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(WORD_BY_WORD_MONTGOMERY) --static 'p384' '2^384 - 2^128 - 2^96 + 2^32 - 1' '$*' $(WORD_BY_WORD_MONTGOMERY_FUNCTIONS) && touch $@.ok) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

# 2^224 - 2^96 + 1
$(C_DIR)p224_64.c $(C_DIR)p224_32.c : $(C_DIR)p224_%.c :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(WORD_BY_WORD_MONTGOMERY) --static 'p224' '2^224 - 2^96 + 1' '$*' $(WORD_BY_WORD_MONTGOMERY_FUNCTIONS) && touch $@.ok) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

# 2^216 * 3^137 - 1
$(C_DIR)p434_64.c $(C_DIR)p434_32.c : $(C_DIR)p434_%.c :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(WORD_BY_WORD_MONTGOMERY) --static 'p434' '2^216 * 3^137 - 1' '$*' $(WORD_BY_WORD_MONTGOMERY_FUNCTIONS) && touch $@.ok) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

test-c-files: $(ALL_C_FILES)

test-c-files only-test-c-files:
	$(CC) -Wall -Wno-unused-function -Werror $(CFLAGS) -c $(ALL_C_FILES)

$(UNSATURATED_SOLINAS_RUST_FILES): $(UNSATURATED_SOLINAS) # Makefile

$(WORD_BY_WORD_MONTGOMERY_RUST_FILES): $(WORD_BY_WORD_MONTGOMERY) # Makefile

# 2^255 - 19
$(RS_DIR)curve25519_64.rs : $(RS_DIR)curve25519_%.rs :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(UNSATURATED_SOLINAS) --lang=Rust '25519' '5' '2^255 - 19' '$*' $(FUNCTIONS_FOR_25519) && touch $@.ok) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

# 2^255 - 19
$(RS_DIR)curve25519_32.rs : $(RS_DIR)curve25519_%.rs :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(UNSATURATED_SOLINAS) --lang=Rust '25519' '10' '2^255 - 19' '$*' $(FUNCTIONS_FOR_25519) && touch $@.ok) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

# 2^521 - 1
$(RS_DIR)p521_64.rs : $(RS_DIR)p521_%.rs :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(UNSATURATED_SOLINAS) --lang=Rust 'p521' '9' '2^521 - 1' '$*' $(UNSATURATED_SOLINAS_FUNCTIONS) && touch $@.ok) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

## 2^224 - 2^96 + 1 ## does not bounds check
#$(RS_DIR)p224_solinas_64.rs : $(RS_DIR)p224_solinas_%.rs :
#	$(SHOW)'SYNTHESIZE > $@'
#	$(HIDE)rm -f $@.ok
#	$(HIDE)($(TIMER) $(UNSATURATED_SOLINAS) --lang=Rust 'p224' '4' '2^224 - 2^96 + 1' '$*' $(UNSATURATED_SOLINAS_FUNCTIONS) && touch $@.ok) > $@.tmp
#	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

# 2^448 - 2^224 - 1
$(RS_DIR)p448_solinas_64.rs : $(RS_DIR)p448_solinas_%.rs :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(UNSATURATED_SOLINAS) --lang=Rust 'p448' '8' '2^448 - 2^224 - 1' '$*' $(UNSATURATED_SOLINAS_FUNCTIONS) && touch $@.ok) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

# 2^256 - 2^224 + 2^192 + 2^96 - 1
$(RS_DIR)p256_64.rs $(RS_DIR)p256_32.rs : $(RS_DIR)p256_%.rs :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(WORD_BY_WORD_MONTGOMERY) --lang=Rust 'p256' '2^256 - 2^224 + 2^192 + 2^96 - 1' '$*' $(WORD_BY_WORD_MONTGOMERY_FUNCTIONS) && touch $@.ok) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

# 2^256 - 2^32 - 977
$(RS_DIR)secp256k1_64.rs $(RS_DIR)secp256k1_32.rs : $(RS_DIR)secp256k1_%.rs :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(WORD_BY_WORD_MONTGOMERY) --lang=Rust 'secp256k1' '2^256 - 2^32 - 977' '$*' $(WORD_BY_WORD_MONTGOMERY_FUNCTIONS) && touch $@.ok) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

# 2^384 - 2^128 - 2^96 + 2^32 - 1
$(RS_DIR)p384_64.rs $(RS_DIR)p384_32.rs : $(RS_DIR)p384_%.rs :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(WORD_BY_WORD_MONTGOMERY) --lang=Rust 'p384' '2^384 - 2^128 - 2^96 + 2^32 - 1' '$*' $(WORD_BY_WORD_MONTGOMERY_FUNCTIONS) && touch $@.ok) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

# 2^224 - 2^96 + 1
$(RS_DIR)p224_64.rs $(RS_DIR)p224_32.rs : $(RS_DIR)p224_%.rs :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(WORD_BY_WORD_MONTGOMERY) --lang=Rust 'p224' '2^224 - 2^96 + 1' '$*' $(WORD_BY_WORD_MONTGOMERY_FUNCTIONS) && touch $@.ok) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

# 2^216 * 3^137 - 1
$(RS_DIR)p434_64.rs $(RS_DIR)p434_32.rs : $(RS_DIR)p434_%.rs :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(WORD_BY_WORD_MONTGOMERY) --lang=Rust 'p434' '2^216 * 3^137 - 1' '$*' $(WORD_BY_WORD_MONTGOMERY_FUNCTIONS) && touch $@.ok) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

test-rust-files: $(ALL_RUST_FILES)

test-rust-files only-test-rust-files:
	cd fiat-rust; $(CARGO_BUILD)

all: $(addprefix fiat-rust/,$(COPY_TO_FIAT_RUST))

# make these .PHONY, so that we copy by contents, not by modification date
# this ensures that these files are always in sync as long as we run make
.PHONY: $(addprefix fiat-rust/,$(COPY_TO_FIAT_RUST))
$(addprefix fiat-rust/,$(COPY_TO_FIAT_RUST)) : fiat-rust/% : %
	cp -f $< $@

$(UNSATURATED_SOLINAS_GO_FILES): $(UNSATURATED_SOLINAS) # Makefile

$(WORD_BY_WORD_MONTGOMERY_GO_FILES): $(WORD_BY_WORD_MONTGOMERY) # Makefile

# 2^255 - 19
$(GO_DIR)curve25519_64.go : $(GO_DIR)curve25519_%.go :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(UNSATURATED_SOLINAS) --lang=Go $(GO_EXTRA_ARGS_$*) '25519' '5' '2^255 - 19' '$*' $(FUNCTIONS_FOR_25519) && touch $@.ok) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

# 2^255 - 19
$(GO_DIR)curve25519_32.go : $(GO_DIR)curve25519_%.go :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(UNSATURATED_SOLINAS) --lang=Go $(GO_EXTRA_ARGS_$*) '25519' '10' '2^255 - 19' '$*' $(FUNCTIONS_FOR_25519) && touch $@.ok) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

# 2^521 - 1
$(GO_DIR)p521_64.go : $(GO_DIR)p521_%.go :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(UNSATURATED_SOLINAS) --lang=Go $(GO_EXTRA_ARGS_$*) 'p521' '9' '2^521 - 1' '$*' $(UNSATURATED_SOLINAS_FUNCTIONS) && touch $@.ok) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

## 2^224 - 2^96 + 1 ## does not bounds check
#$(GO_DIR)p224_solinas_64.go : $(GO_DIR)p224_%.go :
#	$(SHOW)'SYNTHESIZE > $@'
#	$(HIDE)rm -f $@.ok
#	$(HIDE)($(TIMER) $(UNSATURATED_SOLINAS) --lang=Go $(GO_EXTRA_ARGS_$*) 'p224' '4' '2^224 - 2^96 + 1' '$*' $(UNSATURATED_SOLINAS_FUNCTIONS) && touch $@.ok) > $@.tmp
#	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

# 2^448 - 2^224 - 1
$(GO_DIR)p448_solinas_64.go : $(GO_DIR)p448_solinas_%.go :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(UNSATURATED_SOLINAS) --lang=Go $(GO_EXTRA_ARGS_$*) 'p448' '8' '2^448 - 2^224 - 1' '$*' $(UNSATURATED_SOLINAS_FUNCTIONS) && touch $@.ok) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

# 2^256 - 2^224 + 2^192 + 2^96 - 1
$(GO_DIR)p256_64.go $(GO_DIR)p256_32.go : $(GO_DIR)p256_%.go :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(WORD_BY_WORD_MONTGOMERY) --lang=Go $(GO_EXTRA_ARGS_$*) 'p256' '2^256 - 2^224 + 2^192 + 2^96 - 1' '$*' $(WORD_BY_WORD_MONTGOMERY_FUNCTIONS) && touch $@.ok) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

# 2^256 - 2^32 - 977
$(GO_DIR)secp256k1_64.go $(GO_DIR)secp256k1_32.go : $(GO_DIR)secp256k1_%.go :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(WORD_BY_WORD_MONTGOMERY) --lang=Go $(GO_EXTRA_ARGS_$*) 'secp256k1' '2^256 - 2^32 - 977' '$*' $(WORD_BY_WORD_MONTGOMERY_FUNCTIONS) && touch $@.ok) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

# 2^384 - 2^128 - 2^96 + 2^32 - 1
$(GO_DIR)p384_64.go $(GO_DIR)p384_32.go : $(GO_DIR)p384_%.go :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(WORD_BY_WORD_MONTGOMERY) --lang=Go $(GO_EXTRA_ARGS_$*) 'p384' '2^384 - 2^128 - 2^96 + 2^32 - 1' '$*' $(WORD_BY_WORD_MONTGOMERY_FUNCTIONS) && touch $@.ok) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

# 2^224 - 2^96 + 1
$(GO_DIR)p224_64.go $(GO_DIR)p224_32.go : $(GO_DIR)p224_%.go :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(WORD_BY_WORD_MONTGOMERY) --lang=Go $(GO_EXTRA_ARGS_$*) 'p224' '2^224 - 2^96 + 1' '$*' $(WORD_BY_WORD_MONTGOMERY_FUNCTIONS) && touch $@.ok) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

# 2^216 * 3^137 - 1
$(GO_DIR)p434_64.go $(GO_DIR)p434_32.go : $(GO_DIR)p434_%.go :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(WORD_BY_WORD_MONTGOMERY) --lang=Go $(GO_EXTRA_ARGS_$*) 'p434' '2^216 * 3^137 - 1' '$*' $(WORD_BY_WORD_MONTGOMERY_FUNCTIONS) && touch $@.ok) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

.PHONY: $(addprefix test-,$(ALL_GO_FILES))
.PHONY: $(addprefix only-test-,$(ALL_GO_FILES))

$(addprefix test-,$(ALL_GO_FILES)) : test-% : %
	go build $*

$(addprefix only-test-,$(ALL_GO_FILES)) : only-test-% :
	go build $*

test-go-files: $(addprefix test-,$(ALL_GO_FILES))
only-test-go-files: $(addprefix only-test-,$(ALL_GO_FILES))

$(UNSATURATED_SOLINAS_JAVA_FILES): $(UNSATURATED_SOLINAS) # Makefile

$(WORD_BY_WORD_MONTGOMERY_JAVA_FILES): $(WORD_BY_WORD_MONTGOMERY) # Makefile

# 2^255 - 19
$(JAVA_DIR)FiatCurve25519.java : $(JAVA_DIR)Fiat%.java :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(UNSATURATED_SOLINAS) --lang=Java $(JAVA_EXTRA_ARGS_32) '$*' '10' '2^255 - 19' '32' $(FUNCTIONS_FOR_25519) && touch $@.ok) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

# 2^256 - 2^224 + 2^192 + 2^96 - 1
$(JAVA_DIR)FiatP256.java : $(JAVA_DIR)Fiat%.java :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(WORD_BY_WORD_MONTGOMERY) --lang=Java $(JAVA_EXTRA_ARGS_32) '$*' '2^256 - 2^224 + 2^192 + 2^96 - 1' '32' && touch $@.ok) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

# 2^256 - 2^32 - 977
$(JAVA_DIR)FiatSecp256K1.java : $(JAVA_DIR)Fiat%.java :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(WORD_BY_WORD_MONTGOMERY) --lang=Java $(JAVA_EXTRA_ARGS_32) '$*' '2^256 - 2^32 - 977' '32' && touch $@.ok) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

# 2^384 - 2^128 - 2^96 + 2^32 - 1
$(JAVA_DIR)FiatP384.java: $(JAVA_DIR)Fiat%.java :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(WORD_BY_WORD_MONTGOMERY) --lang=Java $(JAVA_EXTRA_ARGS_32) '$*' '2^384 - 2^128 - 2^96 + 2^32 - 1' '32' && touch $@.ok) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

# 2^224 - 2^96 + 1
$(JAVA_DIR)FiatP224.java : $(JAVA_DIR)Fiat%.java :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(WORD_BY_WORD_MONTGOMERY) --lang=Java $(JAVA_EXTRA_ARGS_32) '$*' '2^224 - 2^96 + 1' '32' && touch $@.ok) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

# 2^216 * 3^137 - 1
$(JAVA_DIR)FiatP434.java : $(JAVA_DIR)Fiat%.java :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(WORD_BY_WORD_MONTGOMERY) --lang=Java $(JAVA_EXTRA_ARGS_32) '$*' '2^216 * 3^137 - 1' '32' && touch $@.ok) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

.PHONY: $(addprefix test-,$(ALL_JAVA_FILES))
.PHONY: $(addprefix only-test-,$(ALL_JAVA_FILES))

$(addprefix test-,$(ALL_JAVA_FILES)) : test-% : %
	javac $*

$(addprefix only-test-,$(ALL_JAVA_FILES)) : only-test-% :
	javac $*

test-java-files: $(addprefix test-,$(ALL_JAVA_FILES))
only-test-java-files: $(addprefix only-test-,$(ALL_JAVA_FILES))

javadoc: $(ALL_JAVA_FILES)

javadoc only-javadoc:
	mkdir -p $(JAVADOC_DIR)
	(cd $(JAVADOC_DIR); javadoc $(addprefix $(realpath .)/,$(ALL_JAVA_FILES)))

# Perf testing
PERF_MAKEFILE = src/Rewriter/PerfTesting/Specific/generated/primes.mk
include $(PERF_MAKEFILE)

$(PERF_MAKEFILE): Makefile src/Rewriter/PerfTesting/Specific/make.py primes.txt
	./src/Rewriter/PerfTesting/Specific/make.py primes.txt
PERF_MAX_TIME?=600 # 10 minutes
PERF_MAX_MEM?=10000000 # 10 GB in kbytes
PERF_MAX_STACK?=1000000
PERF_TIMEOUT?=timeout $(PERF_MAX_TIME) # etc/timeout/timeout -m $(PERF_MAX_MEM) # limit to 10 GB # https://raw.githubusercontent.com/pshved/timeout/master/timeout
# PERF_TIMEOUT?=timeout $(PERF_MAX_TIME)
# apparently ulimit -m doesn't work anymore https://superuser.com/a/1497437/59575 / https://thirld.com/blog/2012/02/09/things-to-remember-when-using-ulimit/
PERF_SET_LIMITS = ulimit -S -s $(PERF_MAX_STACK); ulimit -S -m $(PERF_MAX_MEM); ulimit -S -v $(PERF_MAX_MEM);

.PHONY: perf perf-vos perf-extraction perf-standalone
PERF_VOLOGS := $(PERF_PRIME_VOS:.vo=.log)
PERF_SHLOGS := $(PERF_PRIME_SHS:.sh=.log)
PERF_LOGS := $(PERF_VOLOGS) $(PERF_SHLOGS)
ALL_PERF_LOGS := $(PERF_LOGS) $(PERF_LOGS:.log=.log.tmp)

perf-standalone: $(PERF_STANDALONE:%=src/ExtractionOCaml/%)

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
	$(HIDE)./src/Rewriter/PerfTesting/Specific/to_csv.py $(wildcard $(ALL_PERF_LOGS)) > $@.tmp
	$(HIDE)cat $@.tmp | tr -d '\r' | sed 's/\s*$$//g' > $@ && rm -f $@.tmp

.PHONY: perf-graph.csv
perf-graph.csv:
	$(SHOW)'PYTHON > $@'
	$(HIDE)./src/Rewriter/PerfTesting/Specific/to_csv.py --for-graph $(wildcard $(ALL_PERF_LOGS)) > $@.tmp
	$(HIDE)cat $@.tmp | tr -d '\r' | sed 's/\s*$$//g' > $@ && rm -f $@.tmp

.PHONY: $(PERF_TXTS)
$(PERF_TXTS) : %.txt :
	$(SHOW)'PYTHON > $@'
	$(HIDE)./src/Rewriter/PerfTesting/Specific/to_csv.py --$* --txt $(wildcard $(ALL_PERF_LOGS)) > $@.tmp
	$(HIDE)cat $@.tmp | tr -d '\r' | sed 's/\s*$$//g' > $@ && rm -f $@.tmp

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
	$(HIDE)diff output-tests/$*.expected $*.out || (RV=$$?; echo "To accept the new output, run make accept-$*"; exit $$RV)

$(ACCEPT_OUTPUTS) : accept-% :
	$(SHOW)'ACCEPT $*.out'
	$(HIDE)cp -f $*.out output-tests/$*.expected

clean::
	rm -f Makefile.coq

cleanall:: clean
	rm -rf src/Rewriter/PerfTesting/Specific/generated

install: coq
install-without-bedrock2: coq-without-bedrock2

install-without-bedrock2:
	$(HIDE)$(MAKE) -f Makefile.coq install FILESTOINSTALL="$(filter-out $(BEDROCK2_FILES_PATTERN),$(FILESTOINSTALL))"

install-standalone-ocaml: standalone-ocaml
install-standalone-haskell: standalone-haskell

install-standalone-ocaml: FILESTOINSTALL=$(OCAML_BINARIES)
install-standalone-haskell: FILESTOINSTALL=$(HASKELL_BINARIES)

uninstall-standalone-ocaml: FILESTOINSTALL=$(OCAML_BINARIES)
uninstall-standalone-haskell: FILESTOINSTALL=$(HASKELL_BINARIES)

install-standalone-ocaml install-standalone-haskell:
	$(HIDE)code=0; for f in $(FILESTOINSTALL); do\
	 if ! [ -f "$$f" ]; then >&2 echo $$f does not exist; code=1; fi \
	done; exit $$code
	$(HIDE)for f in $(FILESTOINSTALL); do\
	   install -d "$(BINDIR)/" &&\
	   install -m 0755 "$$f" "$(BINDIR)/" &&\
	   echo INSTALL "$$f" "$(BINDIR)/";\
	done

uninstall-standalone-ocaml uninstall-standalone-haskell:
	$(HIDE)for f in $(FILESTOINSTALL); do \
	 instf="$(BINDIR)/`basename $$f`" &&\
	 rm -f "$$instf" &&\
	 echo RM "$$instf"; \
	done

install-standalone: install-standalone-ocaml # install-standalone-haskell
uninstall-standalone: uninstall-standalone-ocaml # uninstall-standalone-haskell

printenv::
	@echo "COQPATH =        $$COQPATH"

printdeps::
	$(HIDE)$(foreach vo,$(filter %.vo,$(MAKECMDGOALS)),echo '$(vo): $(call vo_closure,$(vo))'; )

printreversedeps::
	$(HIDE)$(foreach vo,$(filter %.vo,$(MAKECMDGOALS)),echo '$(vo): $(call vo_reverse_closure,$(VOFILES),$(vo))'; )

etc/tscfreq: etc/tscfreq.c
	$(CC) etc/tscfreq.c -s -Os -o etc/tscfreq
