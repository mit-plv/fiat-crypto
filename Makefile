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

CFLAGS?=

PROFILE?=
VERBOSE?=
SHOW := $(if $(VERBOSE),@true "",@echo "")
HIDE := $(if $(VERBOSE),,@)
INSTALLDEFAULTROOT := Crypto

.PHONY: coq clean update-_CoqProject cleanall install \
	install-coqprime clean-coqprime coqprime coqprime-all \
	util c-files \
	nobigmem print-nobigmem \
	lite only-heavy printlite \
	some-early pre-standalone standalone standalone-haskell standalone-ocaml \
	test-c-files

-include Makefile.coq
include etc/coq-scripts/Makefile.vo_closure

.DEFAULT_GOAL := all

SORT_COQPROJECT = sed 's,[^/]*/,~&,g' | env LC_COLLATE=C sort | sed 's,~,,g' | uniq
update-_CoqProject::
	$(SHOW)'ECHO > _CoqProject'
	$(HIDE)(echo '-R $(SRC_DIR) $(MOD_NAME)'; echo '-R bbv/theories bbv'; ((git ls-files 'src/*.v'; (git submodule foreach 'git ls-files "*.v" 2>/dev/null | sed "s|^|$$path/|"' | grep 'bbv/')) | $(SORT_COQPROJECT))) > _CoqProject

# coq .vo files that are not compiled using coq_makefile
SPECIAL_VOFILES := \
	src/ExtractionOCaml/%.vo \
	src/ExtractionHaskell/%.vo
# add files to this list to prevent them from being built as final
# targets by the "lite" target
LITE_UNMADE_VOFILES := src/Curves/Weierstrass/AffineProofs.vo \
	src/Curves/Weierstrass/Jacobian.vo \
	src/Curves/Weierstrass/Projective.vo \
	src/RewriterWf1.vo \
	src/RewriterWf2.vo \
	src/RewriterRulesGood.vo \
	src/RewriterProofs.vo \
	src/Toplevel2.vo
NOBIGMEM_UNMADE_VOFILES := \
	src/Curves/Weierstrass/AffineProofs.vo \
	src/Curves/Weierstrass/Jacobian.vo \
	src/Curves/Weierstrass/Projective.vo
REGULAR_VOFILES := $(filter-out $(SPECIAL_VOFILES),$(VOFILES))
CURVES_PROOFS_PRE_VOFILES := $(filter src/Curves/Weierstrass/Jacobian.vo src/Curves/%Proofs.vo,$(REGULAR_VOFILES))
NO_CURVES_PROOFS_UNMADE_VOFILES := \
	src/Curves/Weierstrass/AffineProofs.vo \
	src/Curves/Weierstrass/Jacobian.vo
PRE_STANDALONE_PRE_VOFILES := $(filter src/Standalone%.vo,$(REGULAR_VOFILES))
UTIL_PRE_VOFILES := $(filter bbv/%.vo src/Algebra/%.vo src/Tactics/%.vo src/Util/%.vo,$(REGULAR_VOFILES))
SOME_EARLY_VOFILES := \
  src/Arithmetic.vo \
  src/Rewriter.vo

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


all: coq c-files
coq: $(REGULAR_VOFILES)
c-files: $(ALL_C_FILES)

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

OTHERFLAGS += -w "-notation-overridden"
ifneq ($(PROFILE),)
OTHERFLAGS += -profile-ltac
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
	(cd $(COQPRIME_FOLDER) && $(COQBIN)coq_makefile -f _CoqProject -o Makefile)
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

Makefile.coq: Makefile _CoqProject
	$(SHOW)'COQ_MAKEFILE -f _CoqProject > $@'
	$(HIDE)$(COQBIN)coq_makefile -f _CoqProject INSTALLDEFAULTROOT = $(INSTALLDEFAULTROOT) -o Makefile-old && cat Makefile-old | sed s'/^printenv:/printenv::/g' | sed s'/^printenv:::/printenv::/g' > $@ && rm -f Makefile-old


STANDALONE := unsaturated_solinas saturated_solinas word_by_word_montgomery

$(STANDALONE:%=src/ExtractionOCaml/%.ml) : %.ml : %.v src/StandaloneOCamlMain.vo
	$(SHOW)'COQC $< > $@'
	$(HIDE)$(TIMER_FULL) $(COQC) $(COQDEBUG) $(COQFLAGS) $(COQLIBS) $< > $@.tmp
	$(HIDE)sed 's/\r\n/\n/g; s/\r//g' $@.tmp > $@ && rm -f $@.tmp

$(STANDALONE:%=src/ExtractionHaskell/%.hs) : %.hs : %.v src/StandaloneHaskellMain.vo src/haskell.sed
	$(SHOW)'COQC $< > $@'
	$(HIDE)$(TIMER_FULL) $(COQC) $(COQDEBUG) $(COQFLAGS) $(COQLIBS) $< > $@.tmp
	$(HIDE)sed 's/\r\n/\n/g; s/\r//g' $@.tmp | sed -f src/haskell.sed > $@ && rm -f $@.tmp

# pass -w -20 to disable the unused argument warning
$(STANDALONE:%=src/ExtractionOCaml/%) : % : %.ml
	$(TIMER_FULL) ocamlopt -w -20 -o $@ $<

$(STANDALONE:%=src/ExtractionHaskell/%) : % : %.hs
	$(TIMER_FULL) $(GHC) $(GHCFLAGS) -o $@ $<

standalone: standalone-haskell standalone-ocaml
standalone-haskell: $(STANDALONE:%=src/ExtractionHaskell/%)
standalone-ocaml: $(STANDALONE:%=src/ExtractionOCaml/%)

UNSATURATED_SOLINAS_C_FILES := curve25519_64.c curve25519_32.c p521_64.c p521_32.c # p224_solinas_64.c
WORD_BY_WORD_MONTGOMERY_C_FILES := p256_64.c p256_32.c p384_64.c p384_32.c secp256k1_64.c secp256k1_32.c p224_64.c p224_32.c
ALL_C_FILES := $(UNSATURATED_SOLINAS_C_FILES) $(WORD_BY_WORD_MONTGOMERY_C_FILES)
FUNCTIONS_FOR_25519 := carry_mul carry_square carry_scmul121666 carry add sub opp selectznz to_bytes from_bytes
UNSATURATED_SOLINAS := src/ExtractionOCaml/unsaturated_solinas
WORD_BY_WORD_MONTGOMERY := src/ExtractionOCaml/word_by_word_montgomery

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

test-c-files: $(ALL_C_FILES)
	$(CC) -Wall -Wno-unused-function -Werror $(CFLAGS) -c $(ALL_C_FILES)

clean::
	rm -f Makefile.coq

cleanall:: clean

install: coq

printenv::
	@echo "COQPATH =        $$COQPATH"

printdeps::
	$(HIDE)$(foreach vo,$(filter %.vo,$(MAKECMDGOALS)),echo '$(vo): $(call vo_closure,$(vo))'; )

printreversedeps::
	$(HIDE)$(foreach vo,$(filter %.vo,$(MAKECMDGOALS)),echo '$(vo): $(call vo_reverse_closure,$(VOFILES),$(vo))'; )
