.SUFFIXES:

MOD_NAME := Crypto
SRC_DIR  := src

BINDIR?=/usr/local/bin
# or $(shell opam config var bin) ?

GHC?=ghc
GHCFLAGS?= # -XStrict

CFLAGS?=

CARGO_BUILD := cargo build
ZIG_BUILD := zig build

SKIP_BEDROCK2?=

VERBOSE?=
SHOW := $(if $(VERBOSE),@true "",@echo "")
HIDE := $(if $(VERBOSE),,@)
INSTALLDEFAULTROOT := Crypto

PERF_RECORD?=perf record -g -o "$@.perf.data" --

RED:=\033[0;31m
# No Color
NC:=\033[0m
GREEN:=\033[0;32m
BOLD:=$(shell tput bold)
NORMAL:=$(shell tput sgr0)

WITH_PERF?=

.PHONY: coq clean update-_CoqProject cleanall install \
	coq-without-bedrock2 install-without-bedrock2 \
	install-rewriter clean-rewriter rewriter \
	install-coqprime clean-coqprime coqprime coqprime-all \
	bedrock2 clean-bedrock2 install-bedrock2 coqutil clean-coqutil install-coqutil \
	bedrock2-compiler clean-bedrock2-compiler install-bedrock2-compiler \
	rupicola clean-rupicola install-rupicola \
	install-standalone install-standalone-ocaml install-standalone-haskell \
	uninstall-standalone uninstall-standalone-ocaml uninstall-standalone-haskell \
	util all-except-generated \
	c-files bedrock2-files rust-files go-files json-files java-files zig-files generated-files \
	lite-c-files lite-bedrock2-files lite-rust-files lite-go-files lite-json-files lite-java-files lite-zig-files lite-generated-files \
	bedrock2-backend \
	update-go-pkg-cache \
	deps \
	nobigmem print-nobigmem \
	lite only-heavy printlite \
	all-except-compiled \
	some-early pre-standalone pre-standalone-extracted standalone standalone-haskell standalone-ocaml \
	test-c-files test-bedrock2-files test-rust-files test-go-files test-json-files test-java-files test-zig-files test-amd64-files \
	only-test-c-files only-test-bedrock2-files only-test-rust-files only-test-go-files only-test-json-files only-test-java-files only-test-zig-files only-test-amd64-files \
	test-go-module only-test-go-module \
	javadoc only-javadoc \
	check-output accept-output

TIMEFMT?="$@ (real: %e, user: %U, sys: %S, mem: %M ko)"
SKIP_INCLUDE?=
SKIP_COQSCRIPTS_INCLUDE?=
ifneq ($(SKIP_INCLUDE),1)
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

# This include is meant to be safe
include Makefile.local.common

# in case we didn't include Makefile.coq
OCAMLFIND?=ocamlfind
OCAMLOPT?="$(OCAMLFIND)" ocamlopt
OCAMLOPTP?="$(OCAMLFIND)" ocamloptp
ifneq ($(WITH_PERF),1)
CAMLOPT_PERF ?= $(OCAMLOPT)
CAMLOPT_PERF_SHOW:=OCAMLOPT
else
CAMLOPT_PERF ?= $(OCAMLOPTP)
CAMLOPT_PERF_SHOW:=OCAMLOPTP
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
	src/ExtractionHaskell/%.vo
GREP_EXCLUDE_SPECIAL_VOFILES := grep -v '^src/Extraction\(OCaml\|Haskell\)/'

PERFTESTING_VO := \
	src/Rewriter/PerfTesting/Core.vo \
	src/Rewriter/PerfTesting/StandaloneOCamlMain.vo
BEDROCK2_FILES_PATTERN := \
	src/ExtractionOCaml/bedrock2_% \
	src/ExtractionHaskell/bedrock2_% \
	src/ExtractionOCaml/with_bedrock2_% \
	src/ExtractionHaskell/with_bedrock2_% \
	src/Assembly/WithBedrock/% \
	src/Bedrock/% # it's important to catch not just the .vo files, but also the .glob files, etc, because this is used to filter FILESTOINSTALL
EXCLUDE_PATTERN :=

FORCE_BEDROCK2?=
ifneq (,$(filter 8.11% 8.12% 8.13%,$(COQ_VERSION)))
ifneq ($(SKIP_BEDROCK2),1)
$(warning Coq version $(COQ_VERSION) is older than the minimum bedrock2 Coq version of 8.14)
ifeq ($(FORCE_BEDROCK2),1)
$(warning Building bedrock2 code anyway because FORCE_BEDROCK2=$(FORCE_BEDROCK2))
else
ifeq ($(SKIP_BEDROCK2),)
SKIP_BEDROCK2=1
else
$(error Cannot build bedrock2! Pass FORCE_BEDROCK2=1 to override this error and build anyway, or pass SKIP_BEDROCK2=1 (instead of SKIP_BEDROCK2=$(SKIP_BEDROCK2)) to skip bedrock2)
endif
endif
endif
endif

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
REGULAR_WITH_BEDROCK2_VOFILES := $(filter-out $(SPECIAL_VOFILES),$(VOFILES))
REGULAR_VOFILES := $(filter-out $(EXCLUDE_PATTERN),$(REGULAR_WITH_BEDROCK2_VOFILES))
REGULAR_EXCEPT_BEDROCK2_VOFILES := $(filter-out $(BEDROCK2_FILES_PATTERN),$(REGULAR_VOFILES))
BEDROCK2_VOFILES := $(filter $(BEDROCK2_FILES_PATTERN),$(REGULAR_VOFILES))
PRE_STANDALONE_PRE_VOFILES := $(filter src/Standalone%.vo src/Bedrock/Standalone%.vo,$(REGULAR_VOFILES))
UTIL_PRE_VOFILES := $(filter src/Algebra/%.vo src/Tactics/%.vo src/Util/%.vo,$(REGULAR_VOFILES))
SOME_EARLY_VOFILES := \
  src/Arithmetic/Core.vo \
  src/Rewriter/AllTacticsExtra.vo
COPY_TO_FIAT_RUST_AND_FIAT_GO := \
	AUTHORS \
	CONTRIBUTORS \
	COPYRIGHT \
	LICENSE-MIT \
	LICENSE-APACHE \
	LICENSE-BSD-1
COPY_TO_FIAT_RUST := \
	$(COPY_TO_FIAT_RUST_AND_FIAT_GO)
COPY_TO_FIAT_GO := \
	$(COPY_TO_FIAT_RUST_AND_FIAT_GO)

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
BEDROCK2_DIR := fiat-bedrock2/src/
RUST_DIR := fiat-rust/src/
GO_DIR := fiat-go/
JSON_DIR := fiat-json/src/
JAVA_DIR := fiat-java/src/
JAVADOC_DIR := fiat-java/doc/
ZIG_DIR := fiat-zig/src/

# Java only really supports 32-bit builds, because we have neither 64x64->64x64 multiplication, nor uint128
# Java also requires that class names match file names
# import string; print(''.join(f'$(patsubst {i}%,{i.upper()}%,' for i in string.ascii_lowercase) + '$(1)' + ')' * len(string.ascii_lowercase))
capitalize_first_letter = $(patsubst a%,A%,$(patsubst b%,B%,$(patsubst c%,C%,$(patsubst d%,D%,$(patsubst e%,E%,$(patsubst f%,F%,$(patsubst g%,G%,$(patsubst h%,H%,$(patsubst i%,I%,$(patsubst j%,J%,$(patsubst k%,K%,$(patsubst l%,L%,$(patsubst m%,M%,$(patsubst n%,N%,$(patsubst o%,O%,$(patsubst p%,P%,$(patsubst q%,Q%,$(patsubst r%,R%,$(patsubst s%,S%,$(patsubst t%,T%,$(patsubst u%,U%,$(patsubst v%,V%,$(patsubst w%,W%,$(patsubst x%,X%,$(patsubst y%,Y%,$(patsubst z%,Z%,$(1)))))))))))))))))))))))))))
split_after_non_alpha = $(shell echo '$(1)' | sed 's/\([^a-zA-Z ]\)/\1 /g')
to_title_case = $(foreach i,$(1),$(subst $(space),,$(call capitalize_first_letter,$(call split_after_non_alpha,$(i)))))
empty=
space=$(empty) $(empty)
JAVA_RENAME = $(foreach i,$(patsubst %_32,%,$(filter %_32,$(1))),Fiat$(subst $(space),,$(call to_title_case,$(subst _, ,$(i)))))

# Go places each file in a separate directory, and separates these directories by machine bitwidth
GO_RENAME_TO_KEY  = $(strip $(foreach bw,32 64,$(foreach i,$(subst _,,$(patsubst %_$(bw),%,$(filter %_$(bw),$(1)))),$(bw)__SLASH__$(i)__SLASH__$(i))))
GO_KEY_TO_FILE    = $(subst __SLASH__,/,$(1))
GO_FILE_TO_KEY    = $(subst /,__SLASH__,$(1))
GO_RENAME_TO_FILE = $(call GO_KEY_TO_FILE,$(call GO_RENAME_TO_KEY,$(1)))

# Keys for looking up curve parameters
define add_curve_keys
# add_curve_keys curve_base BINARY_NAME description bitwidth non_bitwidth_args FUNCTIONS
$(2)_BASE_FILES += $(1)
ALL_BASE_FILES += $(1)

$(1)_BINARY_NAME:=$(2)
$(1)_DESCRIPTION:=$(3)
$(1)_BITWIDTH:=$(4)
$(1)_ARGS:=$(4) $(5)
$(1)_FUNCTIONS:=$(6)

GO_$(call GO_RENAME_TO_KEY,$(1))_BINARY_NAME:=$(2)
GO_$(call GO_RENAME_TO_KEY,$(1))_PACKAGE:=$(subst _,,$(patsubst %_32,%,$(patsubst %_64,%,$(1))))
GO_$(call GO_RENAME_TO_KEY,$(1))_BITWIDTH:=$(4)
GO_$(call GO_RENAME_TO_KEY,$(1))_ARGS:=$(4) $(5)
GO_$(call GO_RENAME_TO_KEY,$(1))_FUNCTIONS:=$(6) $(GO_EXTRA_$(7)_FUNCTIONS)

JAVA_$(call JAVA_RENAME,$(1))_BINARY_NAME:=$(2)
JAVA_$(call JAVA_RENAME,$(1))_DESCRIPTION:=$(patsubst Fiat%,%,$(call JAVA_RENAME,$(1)))
JAVA_$(call JAVA_RENAME,$(1))_BITWIDTH:=$(4)
JAVA_$(call JAVA_RENAME,$(1))_ARGS:=$(4) $(5)
JAVA_$(call JAVA_RENAME,$(1))_FUNCTIONS:=$(6)

endef

UNSATURATED_SOLINAS_FUNCTIONS := carry_mul carry_square carry add sub opp selectznz to_bytes from_bytes relax
FUNCTIONS_FOR_25519 := $(UNSATURATED_SOLINAS_FUNCTIONS) carry_scmul121666
WORD_BY_WORD_MONTGOMERY_FUNCTIONS := mul square add sub opp from_montgomery to_montgomery nonzero selectznz to_bytes from_bytes one msat divstep divstep_precomp
UNSATURATED_SOLINAS := src/ExtractionOCaml/unsaturated_solinas
WORD_BY_WORD_MONTGOMERY := src/ExtractionOCaml/word_by_word_montgomery

UNSATURATED_SOLINAS_BASE_FILES := # p224_solinas_64
WORD_BY_WORD_MONTGOMERY_BASE_FILES := # p434_32
ALL_BASE_FILES := $(UNSATURATED_SOLINAS_BASE_FILES) $(WORD_BY_WORD_MONTGOMERY_BASE_FILES)

BASE_FILES_NEEDING_INT128 := p448_solinas_32

GO_EXTRA_UNSATURATED_SOLINAS_FUNCTIONS := carry_add carry_sub carry_opp
GO_EXTRA_WORD_BY_WORD_MONTGOMERY_FUNCTIONS :=

$(foreach bw,64 32,$(eval $(call add_curve_keys,curve25519_$(bw),UNSATURATED_SOLINAS,'25519',$(bw),'(auto)' '2^255 - 19',$(FUNCTIONS_FOR_25519),UNSATURATED_SOLINAS)))
$(eval $(call add_curve_keys,poly1305_64,UNSATURATED_SOLINAS,'poly1305',64,'3' '2^130 - 5',$(UNSATURATED_SOLINAS_FUNCTIONS),UNSATURATED_SOLINAS))
$(eval $(call add_curve_keys,poly1305_32,UNSATURATED_SOLINAS,'poly1305',32,'(auto)' '2^130 - 5',$(UNSATURATED_SOLINAS_FUNCTIONS),UNSATURATED_SOLINAS))
$(eval $(call add_curve_keys,p521_64,UNSATURATED_SOLINAS,'p521',64,'9' '2^521 - 1',$(UNSATURATED_SOLINAS_FUNCTIONS),UNSATURATED_SOLINAS))
## 2^224 - 2^96 + 1 ## does not bounds check
#$(eval $(call add_curve_keys,p224_solinas_64,UNSATURATED_SOLINAS,'p224',64,'4' '2^224 - 2^96 + 1',$(UNSATURATED_SOLINAS_FUNCTIONS),UNSATURATED_SOLINAS))
$(eval $(call add_curve_keys,p448_solinas_64,UNSATURATED_SOLINAS,'p448',64,'8' '2^448 - 2^224 - 1',$(UNSATURATED_SOLINAS_FUNCTIONS),UNSATURATED_SOLINAS))
$(eval $(call add_curve_keys,p448_solinas_32,UNSATURATED_SOLINAS,'p448',32,'16' '2^448 - 2^224 - 1',$(UNSATURATED_SOLINAS_FUNCTIONS),UNSATURATED_SOLINAS))
$(foreach bw,64 32,$(eval $(call add_curve_keys,p256_$(bw),WORD_BY_WORD_MONTGOMERY,'p256',$(bw),'2^256 - 2^224 + 2^192 + 2^96 - 1',$(WORD_BY_WORD_MONTGOMERY_FUNCTIONS),WORD_BY_WORD_MONTGOMERY)))
$(foreach bw,64 32,$(eval $(call add_curve_keys,secp256k1_$(bw),WORD_BY_WORD_MONTGOMERY,'secp256k1',$(bw),'2^256 - 2^32 - 977',$(WORD_BY_WORD_MONTGOMERY_FUNCTIONS),WORD_BY_WORD_MONTGOMERY)))
$(foreach bw,64 32,$(eval $(call add_curve_keys,p384_$(bw),WORD_BY_WORD_MONTGOMERY,'p384',$(bw),'2^384 - 2^128 - 2^96 + 2^32 - 1',$(WORD_BY_WORD_MONTGOMERY_FUNCTIONS),WORD_BY_WORD_MONTGOMERY)))
$(foreach bw,64 32,$(eval $(call add_curve_keys,p224_$(bw),WORD_BY_WORD_MONTGOMERY,'p224',$(bw),'2^224 - 2^96 + 1',$(WORD_BY_WORD_MONTGOMERY_FUNCTIONS),WORD_BY_WORD_MONTGOMERY)))
$(foreach bw,64,$(eval $(call add_curve_keys,p434_$(bw),WORD_BY_WORD_MONTGOMERY,'p434',$(bw),'2^216 * 3^137 - 1',$(WORD_BY_WORD_MONTGOMERY_FUNCTIONS),WORD_BY_WORD_MONTGOMERY))) # 32 is a bit too heavy

$(foreach bw,64 32,$(eval $(call add_curve_keys,curve25519_scalar_$(bw),WORD_BY_WORD_MONTGOMERY,'25519_scalar',$(bw),'2^252 + 27742317777372353535851937790883648493',$(WORD_BY_WORD_MONTGOMERY_FUNCTIONS),WORD_BY_WORD_MONTGOMERY)))
$(foreach bw,64 32,$(eval $(call add_curve_keys,p256_scalar_$(bw),WORD_BY_WORD_MONTGOMERY,'p256_scalar',$(bw),'2^256 - 2^224 + 2^192 - 89188191075325690597107910205041859247',$(WORD_BY_WORD_MONTGOMERY_FUNCTIONS),WORD_BY_WORD_MONTGOMERY)))
$(foreach bw,64 32,$(eval $(call add_curve_keys,p384_scalar_$(bw),WORD_BY_WORD_MONTGOMERY,'p384_scalar',$(bw),'2^384 - 1388124618062372383947042015309946732620727252194336364173',$(WORD_BY_WORD_MONTGOMERY_FUNCTIONS),WORD_BY_WORD_MONTGOMERY)))
$(foreach bw,64 32,$(eval $(call add_curve_keys,secp256k1_scalar_$(bw),WORD_BY_WORD_MONTGOMERY,'secp256k1_scalar',$(bw),'2^256 - 432420386565659656852420866394968145599',$(WORD_BY_WORD_MONTGOMERY_FUNCTIONS),WORD_BY_WORD_MONTGOMERY)))

# Files taking 30s or less
LITE_BASE_FILES := curve25519_64 poly1305_64 poly1305_32 p256_64 secp256k1_64 p384_64 p224_32 p434_64 p448_solinas_64 secp256k1_32 p256_32 p448_solinas_32 \
	curve25519_scalar_64 p256_scalar_64 secp256k1_scalar_64 p384_scalar_64 secp256k1_scalar_32 p256_scalar_32

EXTRA_C_FILES := inversion/c/*_test.c

ALL_C_FILES := $(patsubst %,$(C_DIR)%.c,$(ALL_BASE_FILES))
ALL_BEDROCK2_FILES := $(patsubst %,$(BEDROCK2_DIR)%.c,$(filter-out $(BASE_FILES_NEEDING_INT128),$(ALL_BASE_FILES)))
ALL_RUST_FILES := $(patsubst %,$(RUST_DIR)%.rs,$(ALL_BASE_FILES))
ALL_RUST_MODS := $(ALL_BASE_FILES)
ALL_GO_FILES := $(patsubst %,$(GO_DIR)%.go,$(call GO_RENAME_TO_FILE,$(filter-out $(BASE_FILES_NEEDING_INT128),$(ALL_BASE_FILES))))
ALL_JSON_FILES := $(patsubst %,$(JSON_DIR)%.json,$(ALL_BASE_FILES))
ALL_JAVA_FILES := $(patsubst %,$(JAVA_DIR)%.java,$(call JAVA_RENAME,$(filter-out $(BASE_FILES_NEEDING_INT128),$(ALL_BASE_FILES))))
ALL_ZIG_FILES := $(patsubst %,$(ZIG_DIR)%.zig,$(ALL_BASE_FILES))

LITE_C_FILES := $(patsubst %,$(C_DIR)%.c,$(LITE_BASE_FILES))
LITE_BEDROCK2_FILES := $(patsubst %,$(BEDROCK2_DIR)%.c,$(filter-out $(BASE_FILES_NEEDING_INT128),$(LITE_BASE_FILES)))
LITE_RUST_FILES := $(patsubst %,$(RUST_DIR)%.rs,$(LITE_BASE_FILES))
LITE_GO_FILES := $(patsubst %,$(GO_DIR)%.go,$(call GO_RENAME_TO_FILE,$(filter-out $(BASE_FILES_NEEDING_INT128),$(LITE_BASE_FILES))))
LITE_JSON_FILES := $(patsubst %,$(JSON_DIR)%.json,$(LITE_BASE_FILES))
LITE_JAVA_FILES := $(patsubst %,$(JAVA_DIR)%.java,$(call JAVA_RENAME,$(filter-out $(BASE_FILES_NEEDING_INT128),$(LITE_BASE_FILES))))
LITE_ZIG_FILES := $(patsubst %,$(ZIG_DIR)%.zig,$(LITE_BASE_FILES))

BEDROCK2_UNSATURATED_SOLINAS := src/ExtractionOCaml/bedrock2_unsaturated_solinas
BEDROCK2_WORD_BY_WORD_MONTGOMERY := src/ExtractionOCaml/bedrock2_word_by_word_montgomery

C_EXTRA_ARGS := --inline --static --use-value-barrier

JSON_EXTRA_ARGS := --emit-all-casts

BEDROCK2_ARGS := --no-wide-int --widen-carry --widen-bytes --split-multiret --no-select --no-field-element-typedefs
BEDROCK2_EXTRA_CFLAGS := -Wno-error=unused-but-set-variable

RUST_EXTRA_ARGS := --inline

GO_EXTRA_ARGS_ALL := --relax-primitive-carry-to-bitwidth 32,64 --cmovznz-by-mul --internal-static --package-case flatcase --public-function-case UpperCamelCase --private-function-case camelCase --public-type-case UpperCamelCase --private-type-case camelCase --no-prefix-fiat --doc-newline-in-typedef-bounds --doc-prepend-header 'Code generated by Fiat Cryptography. DO NOT EDIT.' --doc-text-before-function-name '' --doc-text-before-type-name ''
GO_EXTRA_ARGS_64  := --no-wide-int $(GO_EXTRA_ARGS_ALL)
GO_EXTRA_ARGS_32  := $(GO_EXTRA_ARGS_ALL)

JAVA_EXTRA_ARGS_ALL := --cmovznz-by-mul --widen-carry --widen-bytes --internal-static --package-name fiat_crypto --class-case UpperCamelCase --no-field-element-typedefs
JAVA_EXTRA_ARGS_64  := --no-wide-int $(JAVA_EXTRA_ARGS_ALL)
JAVA_EXTRA_ARGS_32  := $(JAVA_EXTRA_ARGS_ALL)

ZIG_EXTRA_ARGS := --internal-static --public-function-case camelCase --private-function-case camelCase --public-type-case UpperCamelCase --private-type-case UpperCamelCase --no-prefix-fiat

.PHONY: bedrock2-extra-cflags
bedrock2-extra-cflags:
	@echo "$(BEDROCK2_EXTRA_CFLAGS)"

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

ifneq ($(SKIP_BEDROCK2),1)
OUTPUT_VOS += \
	src/Bedrock/Group/ScalarMult/LadderStep.vo \
	src/Bedrock/Group/ScalarMult/MontgomeryLadder.vo
OUTPUT_PREOUTS += \
	Crypto.Bedrock.Group.ScalarMult.LadderStep.ladderstep_body \
	Crypto.Bedrock.Group.ScalarMult.MontgomeryLadder.montladder_body
endif

CHECK_OUTPUTS := $(addprefix check-,$(OUTPUT_PREOUTS))
ACCEPT_OUTPUTS := $(addprefix accept-,$(OUTPUT_PREOUTS) fiat-amd64.test)

generated-files: c-files rust-files go-files json-files java-files zig-files
lite-generated-files: lite-c-files lite-rust-files lite-go-files lite-json-files lite-java-files lite-zig-files
all-except-compiled: coq pre-standalone-extracted check-output
all-except-generated: standalone-ocaml perf-standalone all-except-compiled
all: all-except-generated generated-files
ifneq ($(SKIP_BEDROCK2),1)
generated-files: bedrock2-files
lite-generated-files: lite-bedrock2-files
endif
coq: $(REGULAR_VOFILES)
coq-without-bedrock2: $(REGULAR_EXCEPT_BEDROCK2_VOFILES)
bedrock2-backend: $(BEDROCK2_VOFILES)
c-files: $(ALL_C_FILES)
bedrock2-files: $(ALL_BEDROCK2_FILES)
rust-files: $(ALL_RUST_FILES)
go-files: $(ALL_GO_FILES)
json-files: $(ALL_JSON_FILES)
java-files: $(ALL_JAVA_FILES)
zig-files: $(ALL_ZIG_FILES)

lite-c-files: $(LITE_C_FILES)
lite-bedrock2-files: $(LITE_BEDROCK2_FILES)
lite-rust-files: $(LITE_RUST_FILES)
lite-go-files: $(LITE_GO_FILES)
lite-json-files: $(LITE_JSON_FILES)
lite-java-files: $(LITE_JAVA_FILES)
lite-zig-files: $(LITE_ZIG_FILES)

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
DEPFLAGS_NL:=-Q $(REWRITER_SRC)/$(REWRITER_NAME) $(REWRITER_NAME)\n-I $(REWRITER_SRC)/$(REWRITER_NAME)/Util/plugins\n$(DEPFLAGS_NL)
deps: rewriter
$(VOFILES): | rewriter
$(ALLDFILES): | rewriter
cleanall:: clean-rewriter
install: install-rewriter
endif

ifneq ($(SKIP_BEDROCK2),1)
ifneq ($(EXTERNAL_BEDROCK2),1)
DEPFLAGS_NL:=-Q $(RUPICOLA_SRC)/$(RUPICOLA_NAME) $(RUPICOLA_NAME)\n-Q $(BEDROCK2_SRC)/$(BEDROCK2_NAME) $(BEDROCK2_NAME)\n-Q $(BEDROCK2_EXAMPLES_SRC)/$(BEDROCK2_EXAMPLES_NAME) $(BEDROCK2_EXAMPLES_NAME)\n-Q $(BEDROCK2_COMPILER_SRC)/$(BEDROCK2_COMPILER_NAME) $(BEDROCK2_COMPILER_NAME)\n-Q $(RISCV_SRC)/$(RISCV_NAME) $(RISCV_NAME)\n$(DEPFLAGS_NL)
deps: bedrock2 bedrock2-compiler rupicola
$(VOFILES): | bedrock2 bedrock2-compiler rupicola
$(ALLDFILES): | bedrock2 bedrock2-compiler rupicola
cleanall:: clean-bedrock2 clean-bedrock2-compiler clean-rupicola
install: install-bedrock2 install-bedrock2-compiler install-rupicola
endif
endif

ifneq ($(EXTERNAL_COQUTIL),1)
DEPFLAGS_NL:=-Q $(COQUTIL_SRC)/$(COQUTIL_NAME) $(COQUTIL_NAME)\n$(DEPFLAGS_NL)
deps: coqutil
$(VOFILES): | coqutil
$(ALLDFILES): | coqutil
cleanall:: clean-coqutil
install: install-coqutil
endif

ifneq ($(EXTERNAL_COQPRIME),1)
DEPFLAGS_NL:=-Q $(COQPRIME_SRC)/$(COQPRIME_NAME) $(COQPRIME_NAME)\n$(DEPFLAGS_NL)
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
	$(HIDE)$(COQBIN)coq_makefile -f _CoqProject $(DEPFLAGS) INSTALLDEFAULTROOT = $(INSTALLDEFAULTROOT) -o Makefile-coq && cat Makefile-coq | sed 's/^printenv:/printenv::/g; s/^printenv:::/printenv::/g; s/^all:/all-old:/g; s/^validate:/validate-vo:/g; s/^.PHONY: validate/.PHONY: validate-vo/g' > $@ && rm -f Makefile-coq


BASE_STANDALONE := unsaturated_solinas saturated_solinas word_by_word_montgomery base_conversion
BEDROCK2_STANDALONE := $(addprefix bedrock2_,$(BASE_STANDALONE)) $(addprefix with_bedrock2_,$(BASE_STANDALONE))
STANDALONE := $(BASE_STANDALONE)
ifneq ($(SKIP_BEDROCK2),1)
STANDALONE += $(BEDROCK2_STANDALONE) $(WITH_BEDROCK2_STANDALONE)
endif
PERF_STANDALONE := perf_unsaturated_solinas perf_word_by_word_montgomery

STANDALONE_OCAML := $(STANDALONE) $(PERF_STANDALONE)
STANDALONE_HASKELL := $(STANDALONE)

OCAML_BINARIES := $(BASE_STANDALONE:%=src/ExtractionOCaml/%)
HASKELL_BINARIES := $(BASE_STANDALONE:%=src/ExtractionHaskell/%)

WITH_BEDROCK2_OCAML_BINARIES := $(BASE_STANDALONE:%=src/ExtractionOCaml/with_bedrock2_%)
WITH_BEDROCK2_HASKELL_BINARIES := $(BASE_STANDALONE:%=src/ExtractionHaskell/with_bedrock2_%)


$(STANDALONE:%=src/ExtractionOCaml/%.ml): src/StandaloneOCamlMain.vo
$(BEDROCK2_STANDALONE:%=src/ExtractionOCaml/%.ml): src/Bedrock/Standalone/StandaloneOCamlMain.vo
$(PERF_STANDALONE:%=src/ExtractionOCaml/%.ml): src/Rewriter/PerfTesting/StandaloneOCamlMain.vo
$(STANDALONE:%=src/ExtractionHaskell/%.hs): src/StandaloneHaskellMain.vo
$(BEDROCK2_STANDALONE:%=src/ExtractionHaskell/%.hs): src/Bedrock/Standalone/StandaloneHaskellMain.vo
# $(PERF_STANDALONE:%=src/ExtractionHaskell/%.hs): src/Rewriter/PerfTesting/StandaloneHaskellMain.vo

pre-standalone-extracted: $(STANDALONE_OCAML:%=src/ExtractionOCaml/%.ml) $(STANDALONE_HASKELL:%=src/ExtractionHaskell/%.hs)

$(STANDALONE_OCAML:%=src/ExtractionOCaml/%.ml) : %.ml : %.v
	$(SHOW)'COQC $<'
	$(HIDE)$(TIMER) $(COQC) $(COQDEBUG) $(COQFLAGS) $(COQLIBS) $<
	$(HIDE)cat $*.tmp.ml | tr -d '\r' > $@ && rm $*.tmp.ml
	$(HIDE)cat $*.tmp.mli | tr -d '\r' > $*.mli && rm $*.tmp.mli

$(STANDALONE_HASKELL:%=src/ExtractionHaskell/%.hs) : %.hs : %.v src/haskell.sed
	$(SHOW)'COQC $< > $@'
	$(HIDE)$(TIMER) $(COQC) $(COQDEBUG) $(COQFLAGS) $(COQLIBS) $< > $@.tmp
	$(HIDE)cat $@.tmp | tr -d '\r' | sed -f src/haskell.sed > $@ && rm $@.tmp

# pass -w -20 to disable the unused argument warning
# unix package needed for Unix.gettimeofday for the perf_* binaries
$(STANDALONE_OCAML:%=src/ExtractionOCaml/%.cmi) : %.cmi : %.ml
	$(SHOW)'$(CAMLOPT_PERF_SHOW) $*.mli'
	$(HIDE)$(TIMER) $(CAMLOPT_PERF) -package unix -w -20 -g $*.mli

$(STANDALONE_OCAML:%=src/ExtractionOCaml/%) : % : %.ml %.cmi
	$(SHOW)'$(CAMLOPT_PERF_SHOW) $< -o $@'
	$(HIDE)$(TIMER) $(CAMLOPT_PERF) -package unix -linkpkg -w -20 -g -I src/ExtractionOCaml/ -o $@ $<

$(STANDALONE_HASKELL:%=src/ExtractionHaskell/%) : % : %.hs
	$(SHOW)'GHC $< -o $@'
	$(HIDE)$(TIMER) $(GHC) $(GHCFLAGS) -o $@ $<

standalone: standalone-haskell standalone-ocaml
standalone-haskell: $(STANDALONE_HASKELL:%=src/ExtractionHaskell/%)
standalone-ocaml: $(STANDALONE_OCAML:%=src/ExtractionOCaml/%)

.SECONDEXPANSION:

$(ALL_C_FILES) : $(C_DIR)%.c : $$($$($$*_BINARY_NAME))
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $($($*_BINARY_NAME)) $(C_EXTRA_ARGS) $($*_DESCRIPTION) $($*_ARGS) $($*_FUNCTIONS) && touch $@.ok || true) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

test-c-files: $(ALL_C_FILES) $(EXTRA_C_FILES)

test-c-files only-test-c-files:
	$(CC) -Wall -Wno-unused-function -Wpedantic -Werror $(CFLAGS) -c $(ALL_C_FILES) $(EXTRA_C_FILES)

$(ALL_BEDROCK2_FILES) : $(BEDROCK2_DIR)%.c : $$(BEDROCK2_$$($$*_BINARY_NAME))
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)($(TIMER) $(BEDROCK2_$($*_BINARY_NAME)) --lang bedrock2 --static $(BEDROCK2_ARGS) $($*_DESCRIPTION) $($*_ARGS) $($*_FUNCTIONS) && touch $@.ok || true) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

test-bedrock2-files: $(ALL_BEDROCK2_FILES)

test-bedrock2-files only-test-bedrock2-files:
	$(CC) -Wall -Wno-unused-function -Werror $(BEDROCK2_EXTRA_CFLAGS) $(CFLAGS) -c $(ALL_BEDROCK2_FILES)

$(ALL_RUST_FILES) : $(RUST_DIR)%.rs : $$($$($$*_BINARY_NAME))
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $($($*_BINARY_NAME)) --lang Rust $(RUST_EXTRA_ARGS) $($*_DESCRIPTION) $($*_ARGS) $($*_FUNCTIONS) && touch $@.ok || true) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

test-rust-files: $(ALL_RUST_FILES)

test-rust-files only-test-rust-files:
	cd fiat-rust; $(CARGO_BUILD)

rust-files lite-rust-files: fiat-rust/src/lib.rs

fiat-rust/src/lib.rs: Makefile
	$(SHOW)'PRINTF > $@'
	$(HIDE)(echo '// AUTOGENERATED FILE: DO NOT EDIT'; echo '#![cfg_attr(not(feature = "std"), no_std)]'; printf 'pub mod %s;\n' $(sort $(ALL_RUST_MODS))) > $@

$(ALL_ZIG_FILES) : $(ZIG_DIR)%.zig : $$($$($$*_BINARY_NAME))
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $($($*_BINARY_NAME)) --lang Zig $(ZIG_EXTRA_ARGS) --package-name $($*_DESCRIPTION) "" $($*_ARGS) $($*_FUNCTIONS) && touch $@.ok || true) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

test-zig-files: $(ALL_ZIG_FILES)

test-zig-files only-test-zig-files:
	cd fiat-zig; $(ZIG_BUILD)

all: $(addprefix fiat-rust/,$(COPY_TO_FIAT_RUST))
all: $(addprefix fiat-go/,$(COPY_TO_FIAT_GO))

# make these .PHONY, so that we copy by contents, not by modification date
# this ensures that these files are always in sync as long as we run make
.PHONY: $(addprefix fiat-rust/,$(COPY_TO_FIAT_RUST))
$(addprefix fiat-rust/,$(COPY_TO_FIAT_RUST)) : fiat-rust/% : %
	cp -f $< $@

.PHONY: $(addprefix fiat-go/,$(COPY_TO_FIAT_GO))
$(addprefix fiat-go/,$(COPY_TO_FIAT_GO)) : fiat-go/% : %
	cp -f $< $@

$(ALL_GO_FILES) : $(GO_DIR)%.go : $$($$(GO_$$(call GO_FILE_TO_KEY,$$*)_BINARY_NAME))
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)mkdir -p $(dir $@)
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(PERF_RECORDER) $($(GO_$(call GO_FILE_TO_KEY,$*)_BINARY_NAME)) --lang Go $(GO_EXTRA_ARGS_$(GO_$(call GO_FILE_TO_KEY,$*)_BITWIDTH)) --package-name $(GO_$(call GO_FILE_TO_KEY,$*)_PACKAGE) "" $(GO_$(call GO_FILE_TO_KEY,$*)_ARGS) $(GO_$(call GO_FILE_TO_KEY,$*)_FUNCTIONS) && touch $@.ok || true) > $@.tmp
	$(HIDE)(rm $@.ok && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

.PHONY: $(addprefix test-,$(ALL_GO_FILES))
.PHONY: $(addprefix only-test-,$(ALL_GO_FILES))

$(addprefix test-,$(ALL_GO_FILES)) : test-% : %
	go build $*

$(addprefix only-test-,$(ALL_GO_FILES)) : only-test-% :
	go build $*

test-go-module only-test-go-module:
	( cd fiat-go && go build -a -v ./... )

test-go-module: $(ALL_GO_FILES)

test-go-files: $(addprefix test-,$(ALL_GO_FILES))
only-test-go-files: $(addprefix only-test-,$(ALL_GO_FILES))


$(ALL_JSON_FILES) : $(JSON_DIR)%.json : $$($$($$*_BINARY_NAME))
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok1 $@.ok2
	$(HIDE)(($(TIMER) $(PERF_RECORDER) $($($*_BINARY_NAME)) --lang JSON $(JSON_EXTRA_ARGS) $($*_DESCRIPTION) $($*_ARGS) $($*_FUNCTIONS) && touch $@.ok1 || true) | jq -s . && touch $@.ok2 || true) > $@.tmp
	$(HIDE)(rm $@.ok1 $@.ok2 && mv $@.tmp $@) || ( RV=$$?; cat $@.tmp; exit $$RV )

.PHONY: $(addprefix test-,$(ALL_JSON_FILES))
.PHONY: $(addprefix only-test-,$(ALL_JSON_FILES))

$(addprefix test-,$(ALL_JSON_FILES)) : test-% : %
	jq . >/dev/null <$*

$(addprefix only-test-,$(ALL_JSON_FILES)) : only-test-% :
	jq . >/dev/null <$*

test-json-files: $(addprefix test-,$(ALL_JSON_FILES))
only-test-json-files: $(addprefix only-test-,$(ALL_JSON_FILES))

$(ALL_JAVA_FILES) : $(JAVA_DIR)%.java : $$($$(JAVA_$$*_BINARY_NAME))
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER) $(PERF_RECORDER) $($(JAVA_$*_BINARY_NAME)) --lang Java $(JAVA_EXTRA_ARGS_$(JAVA_$*_BITWIDTH)) $(JAVA_$*_DESCRIPTION) $(JAVA_$*_ARGS) $(JAVA_$*_FUNCTIONS) && touch $@.ok) > $@.tmp
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

ifneq (,$(wildcard .git/))
AMD64_ASM_FILES := $(sort $(shell git ls-files "fiat-amd64/*.asm"))
else
AMD64_ASM_FILES := $(sort $(wildcard fiat-amd64/*.asm))
endif

Makefile.test-amd64-files.mk: fiat-amd64/gentest.py $(AMD64_ASM_FILES)
	$(SHOW)'GENTEST --makefile fiat-amd64/*.asm > $@'
	$(HIDE)fiat-amd64/gentest.py --makefile $(AMD64_ASM_FILES) > $@

include Makefile.test-amd64-files.mk

.PHONY: test-amd64-files-print-report only-test-amd64-files-print-report

test-amd64-files-print-report::
	@ export passed=$$(cat $(AMD64_ASM_STATUS_FILES) 2>/dev/null | grep -c '^0$$'); \
	  export total=$(words $(AMD64_ASM_STATUS_FILES)); \
	  export failed=$$(expr $${total} - $${passed}); \
	  if [ $${passed} -eq $${total} ]; then \
	      echo "$(GREEN)$(BOLD)ALL $${total} AMD64 ASM TESTS PASSED$(NC)"; \
	  else \
	      echo "$(GREEN)$(BOLD)PASSED:$(NORMAL) $(GREEN)$${passed}$(NC) / $${total}"; \
	      echo "$(RED)$(BOLD)FAILED:$(NORMAL) $(RED)$${failed}$(NC) / $${total}"; \
	  fi

only-test-amd64-files-print-report::
	@ export passed=$$(cat $(AMD64_ASM_ONLY_STATUS_FILES) 2>/dev/null | grep -c '^0$$'); \
	  export total=$(words $(AMD64_ASM_ONLY_STATUS_FILES)); \
	  export failed=$$(expr $${total} - $${passed}); \
	  if [ $${passed} -eq $${total} ]; then \
	      echo "$(GREEN)$(BOLD)ALL $${total} AMD64 ASM TESTS PASSED$(NC)"; \
	  else \
	      echo "$(GREEN)$(BOLD)PASSED:$(NORMAL) $(GREEN)$${passed}$(NC) / $${total}"; \
	      echo "$(RED)$(BOLD)FAILED:$(NORMAL) $(RED)$${failed}$(NC) / $${total}"; \
	  fi

test-amd64-files-status: $(AMD64_ASM_STATUS_FILES)
	$(HIDE)! grep -q -v '^0$$' $^

only-test-amd64-files-status: $(AMD64_ASM_ONLY_STATUS_FILES)
	$(HIDE)! grep -q -v '^0$$' $^

.PHONY: test-amd64-files-status only-test-amd64-files-status

test-amd64-files: $(UNSATURATED_SOLINAS) $(WORD_BY_WORD_MONTGOMERY)

test-amd64-files: test-amd64-files-print-report test-amd64-files-status

only-test-amd64-files: only-test-amd64-files-print-report only-test-amd64-files-status

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

install: coq
install-without-bedrock2: coq-without-bedrock2

install-without-bedrock2:
	$(HIDE)$(MAKE) -f Makefile.coq install FILESTOINSTALL="$(filter-out $(BEDROCK2_FILES_PATTERN),$(FILESTOINSTALL))"

install-standalone-ocaml: standalone-ocaml
install-standalone-haskell: standalone-haskell

uninstall-standalone-ocaml: FILESTOINSTALL=$(OCAML_BINARIES)
uninstall-standalone-haskell: FILESTOINSTALL=$(HASKELL_BINARIES)

ifeq ($(SKIP_BEDROCK2),1)
install-standalone-ocaml: FILESTOINSTALL=$(OCAML_BINARIES)
install-standalone-haskell: FILESTOINSTALL=$(HASKELL_BINARIES)

install-standalone-ocaml install-standalone-haskell:
	$(HIDE)code=0; for f in $(FILESTOINSTALL); do\
	 if ! [ -f "$$f" ]; then >&2 echo $$f does not exist; code=1; fi \
	done; exit $$code
	$(HIDE)for f in $(FILESTOINSTALL); do\
	   install -d "$(BINDIR)/" &&\
	   install -m 0755 "$$f" "$(BINDIR)/" &&\
	   echo INSTALL "$$f" "$(BINDIR)/";\
	done
else
install-standalone-ocaml: FILESTOINSTALL=$(WITH_BEDROCK2_OCAML_BINARIES)
install-standalone-haskell: FILESTOINSTALL=$(WITH_BEDROCK2_HASKELL_BINARIES)

install-standalone-ocaml install-standalone-haskell:
	$(HIDE)code=0; for f in $(FILESTOINSTALL); do\
	 if ! [ -f "$$f" ]; then >&2 echo $$f does not exist; code=1; fi \
	done; exit $$code
	$(HIDE)for f in $(FILESTOINSTALL); do\
	   fdir="$$(dirname "$$f")" &&\
	   fname="$$(basename "$$f")" &&\
	   df="$${fname#with_bedrock2_}" &&\
	   install -d "$(BINDIR)/" &&\
	   install -m 0755 "$$f" "$(BINDIR)/$$df" &&\
	   echo INSTALL "$$f" "$(BINDIR)/$$df";\
	done
endif

uninstall-standalone-ocaml uninstall-standalone-haskell:
	$(HIDE)for f in $(FILESTOINSTALL); do \
	 instf="$(BINDIR)/`basename $$f`" &&\
	 rm -f "$$instf" &&\
	 echo RM "$$instf"; \
	done

install-standalone: install-standalone-ocaml # install-standalone-haskell
uninstall-standalone: uninstall-standalone-ocaml # uninstall-standalone-haskell

.PHONY: validate
validate: Makefile.coq
	$(MAKE) -f Makefile.coq validate-vo VOFILES="$(REGULAR_VOFILES)"

.PHONY: print_DEPFLAGS
print_DEPFLAGS:
	@echo "DEPFLAGS_NL ="
	@printf -- '$(DEPFLAGS_NL)'

# This target is used to update the _CoqProject file.
# But it only works if we have git
ifneq (,$(wildcard .git/))
SORT_COQPROJECT = sed 's,[^/]*/,~&,g' | env LC_COLLATE=C sort | sed 's,~,,g'
EXISTING_COQPROJECT_CONTENTS_SORTED:=$(shell cat _CoqProject 2>&1 | $(SORT_COQPROJECT))
WARNINGS_PLUS := +implicit-core-hint-db,+implicits-in-term,+non-reversible-notation,+deprecated-intros-until-0,+deprecated-focus,+unused-intro-pattern,+variable-collision,+unexpected-implicit-declaration,+omega-is-deprecated,+deprecated-instantiate-syntax,+non-recursive,+undeclared-scope,+deprecated-hint-rewrite-without-locality,+deprecated-hint-without-locality,+deprecated-instance-without-locality,+deprecated-typeclasses-transparency-without-locality
# Remove unsupported-attributes once we stop supporting < 8.14
WARNINGS := $(WARNINGS_PLUS),unsupported-attributes
COQPROJECT_CMD:=(echo '-R $(SRC_DIR) $(MOD_NAME)'; printf -- '$(DEPFLAGS_NL)'; echo '-arg -w -arg $(WARNINGS)'; echo '-arg -native-compiler -arg ondemand'; ((echo "$(sort $(VERSION_DEPENDENT_FILES) $(SPECIAL_VERSION_DEPENDENT_FILES))" | tr ' ' '\n'; git ls-files 'src/*.v' | $(GREP_EXCLUDE_SPECIAL_VOFILES)) | $(SORT_COQPROJECT)))
NEW_COQPROJECT_CONTENTS_SORTED:=$(shell $(COQPROJECT_CMD) | $(SORT_COQPROJECT))

ifneq ($(EXISTING_COQPROJECT_CONTENTS_SORTED),$(NEW_COQPROJECT_CONTENTS_SORTED))
.PHONY: _CoqProject
_CoqProject:
	$(SHOW)'ECHO > $@'
	$(HIDE)$(COQPROJECT_CMD) > $@
endif
endif

printdeps::
	$(HIDE)$(foreach vo,$(filter %.vo,$(MAKECMDGOALS)),echo '$(vo): $(call vo_closure,$(vo))'; )

printreversedeps::
	$(HIDE)$(foreach vo,$(filter %.vo,$(MAKECMDGOALS)),echo '$(vo): $(call vo_reverse_closure,$(VOFILES),$(vo))'; )

etc/tscfreq: etc/tscfreq.c
	$(CC) etc/tscfreq.c -s -Os -o etc/tscfreq

REGULAR_WITH_BEDROCK2_LIBS := $(sort $(subst /,.,$(patsubst src/%.vo,Crypto/%,$(filter-out src/Bedrock/Everything.vo src/Everything.vo,$(REGULAR_WITH_BEDROCK2_VOFILES)))))
REGULAR_EXCEPT_BEDROCK2_LIBS := $(sort $(subst /,.,$(patsubst src/%.vo,Crypto/%,$(filter-out src/Bedrock/Everything.vo src/Everything.vo,$(REGULAR_EXCEPT_BEDROCK2_VOFILES)))))
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

GOPROXY?=https://proxy.golang.org
GO111MODULE?=on
export GOPROXY
export GO111MODULE
update-go-pkg-cache:
	go get "github.com/mit-plv/fiat-crypto/fiat-go@master"
	go get "github.com/mit-plv/fiat-crypto/fiat-go@v0.0.0-$(shell TZ=UTC git show --quiet --date='format-local:%Y%m%d%H%M%S' --format="%cd" HEAD)-$(shell git rev-parse HEAD | cut -c 1-12)"
	curl "https://pkg.go.dev/github.com/mit-plv/fiat-crypto/fiat-go@v0.0.0-$(shell TZ=UTC git show --quiet --date='format-local:%Y%m%d%H%M%S' --format="%cd" HEAD)-$(shell git rev-parse HEAD | cut -c 1-12)" >/dev/null
