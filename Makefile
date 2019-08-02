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

CARGO_BUILD := cargo build

PROFILE?=
VERBOSE?=
SHOW := $(if $(VERBOSE),@true "",@echo "")
HIDE := $(if $(VERBOSE),,@)
INSTALLDEFAULTROOT := Crypto

.PHONY: coq clean update-_CoqProject cleanall install \
	install-coqprime clean-coqprime coqprime coqprime-all \
	util c-files rust-files \
	nobigmem print-nobigmem \
	lite only-heavy printlite \
	some-early pre-standalone standalone standalone-haskell standalone-ocaml \
	test-c-files test-rust-files

-include Makefile.coq
include etc/coq-scripts/Makefile.vo_closure

.DEFAULT_GOAL := all

SORT_COQPROJECT = sed 's,[^/]*/,~&,g' | env LC_COLLATE=C sort | sed 's,~,,g' | uniq
update-_CoqProject::
	$(SHOW)'ECHO > _CoqProject'
	$(HIDE)(echo '-R $(SRC_DIR) $(MOD_NAME)'; (git ls-files 'src/*.v' | $(GREP_EXCLUDE_SPECIAL_VOFILES) | $(SORT_COQPROJECT))) > _CoqProject

# coq .vo files that are not compiled using coq_makefile
SPECIAL_VOFILES := \
	src/ExtractionOCaml/%.vo \
	src/ExtractionHaskell/%.vo
GREP_EXCLUDE_SPECIAL_VOFILES := grep -v '^src/Extraction\(OCaml\|Haskell\)/'
PERFTESTING_VO := \
	src/Rewriter/PerfTesting/Core.vo \
	src/Rewriter/PerfTesting/StandaloneOCamlMain.vo
# add files to this list to prevent them from being built as final
# targets by the "lite" target
LITE_UNMADE_VOFILES := src/Curves/Weierstrass/AffineProofs.vo \
	src/Curves/Weierstrass/Jacobian.vo \
	src/Curves/Weierstrass/Projective.vo \
	src/RewriterWf1.vo \
	src/RewriterWf2.vo \
	src/RewriterRulesGood.vo \
	src/RewriterAll.vo \
	$(PERFTESTING_VO)
NOBIGMEM_UNMADE_VOFILES := \
	src/Curves/Weierstrass/AffineProofs.vo \
	src/Curves/Weierstrass/Jacobian.vo \
	src/Curves/Weierstrass/Projective.vo \
	$(PERFTESTING_VO)
REGULAR_VOFILES := $(filter-out $(SPECIAL_VOFILES),$(VOFILES))
PRE_STANDALONE_PRE_VOFILES := $(filter src/Standalone%.vo,$(REGULAR_VOFILES))
UTIL_PRE_VOFILES := $(filter src/Algebra/%.vo src/Tactics/%.vo src/Util/%.vo,$(REGULAR_VOFILES))
SOME_EARLY_VOFILES := \
  src/Arithmetic/Core.vo \
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

UNSATURATED_SOLINAS_C_FILES := curve25519_64.c curve25519_32.c p521_64.c p521_32.c p448_solinas_64.c # p224_solinas_64.c
WORD_BY_WORD_MONTGOMERY_C_FILES := p256_64.c p256_32.c p384_64.c p384_32.c secp256k1_64.c secp256k1_32.c p224_64.c p224_32.c p434_64.c # p434_32.c
ALL_C_FILES := $(UNSATURATED_SOLINAS_C_FILES) $(WORD_BY_WORD_MONTGOMERY_C_FILES)
UNSATURATED_SOLINAS_RUST_FILES := curve25519_64.rs curve25519_32.rs p521_64.rs p521_32.rs p448_solinas_64.rs # p224_solinas_64.rs
WORD_BY_WORD_MONTGOMERY_RUST_FILES := p256_64.rs p256_32.rs p384_64.rs p384_32.rs secp256k1_64.rs secp256k1_32.rs p224_64.rs p224_32.rs p434_64.rs # p434_32.rs
ALL_RUST_FILES := $(UNSATURATED_SOLINAS_RUST_FILES) $(WORD_BY_WORD_MONTGOMERY_RUST_FILES)
FUNCTIONS_FOR_25519 := carry_mul carry_square carry_scmul121666 carry add sub opp selectznz to_bytes from_bytes
UNSATURATED_SOLINAS := src/ExtractionOCaml/unsaturated_solinas
WORD_BY_WORD_MONTGOMERY := src/ExtractionOCaml/word_by_word_montgomery


all: coq c-files rust-files
coq: $(REGULAR_VOFILES)
c-files: $(ALL_C_FILES)
rust-files: $(ALL_RUST_FILES)

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
PERF_STANDALONE := perf_unsaturated_solinas perf_word_by_word_montgomery

STANDALONE_OCAML := $(STANDALONE) $(PERF_STANDALONE)
STANDALONE_HASKELL := $(STANDALONE)

$(STANDALONE:%=src/ExtractionOCaml/%.ml): src/StandaloneOCamlMain.vo
$(PERF_STANDALONE:%=src/ExtractionOCaml/%.ml): src/Rewriter/PerfTesting/StandaloneOCamlMain.vo
$(STANDALONE:%=src/ExtractionHaskell/%.hs): src/StandaloneHaskellMain.vo
# $(PERF_STANDALONE:%=src/ExtractionHaskell/%.hs): src/Rewriter/PerfTesting/StandaloneHaskellMain.vo

$(STANDALONE_OCAML:%=src/ExtractionOCaml/%.ml) : %.ml : %.v
	$(SHOW)'COQC $< > $@'
	$(HIDE)$(TIMER_FULL) $(COQC) $(COQDEBUG) $(COQFLAGS) $(COQLIBS) $< > $@.tmp
	$(HIDE)sed 's/\r\n/\n/g; s/\r//g' $@.tmp > $@ && rm -f $@.tmp

$(STANDALONE_HASKELL:%=src/ExtractionHaskell/%.hs) : %.hs : %.v src/haskell.sed
	$(SHOW)'COQC $< > $@'
	$(HIDE)$(TIMER_FULL) $(COQC) $(COQDEBUG) $(COQFLAGS) $(COQLIBS) $< > $@.tmp
	$(HIDE)sed 's/\r\n/\n/g; s/\r//g' $@.tmp | sed -f src/haskell.sed > $@ && rm -f $@.tmp

# pass -w -20 to disable the unused argument warning
# unix package needed for Unix.gettimeofday for the perf_* binaries
$(STANDALONE_OCAML:%=src/ExtractionOCaml/%) : % : %.ml
	$(TIMER_FULL) ocamlfind ocamlopt -package unix -linkpkg -w -20 -o $@ $<

$(STANDALONE_HASKELL:%=src/ExtractionHaskell/%) : % : %.hs
	$(TIMER_FULL) $(GHC) $(GHCFLAGS) -o $@ $<

standalone: standalone-haskell standalone-ocaml
standalone-haskell: $(STANDALONE_HASKELL:%=src/ExtractionHaskell/%)
standalone-ocaml: $(STANDALONE_OCAML:%=src/ExtractionOCaml/%)

$(UNSATURATED_SOLINAS_C_FILES): $(UNSATURATED_SOLINAS) # Makefile

$(WORD_BY_WORD_MONTGOMERY_C_FILES): $(WORD_BY_WORD_MONTGOMERY) # Makefile

# 2^255 - 19
curve25519_64.c:
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER_FULL) $(UNSATURATED_SOLINAS) --static '25519' '5' '2^255 - 19' '64' $(FUNCTIONS_FOR_25519) && touch $@.ok) > $@.tmp
	$(HIDE)rm $@.ok && mv $@.tmp $@

# 2^255 - 19
curve25519_32.c:
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER_FULL) $(UNSATURATED_SOLINAS) --static '25519' '10' '2^255 - 19' '32' $(FUNCTIONS_FOR_25519) && touch $@.ok) > $@.tmp
	$(HIDE)rm $@.ok && mv $@.tmp $@

# 2^521 - 1
p521_64.c:
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER_FULL) $(UNSATURATED_SOLINAS) --static 'p521' '9' '2^521 - 1' '64' && touch $@.ok) > $@.tmp
	$(HIDE)rm $@.ok && mv $@.tmp $@

# 2^521 - 1
p521_32.c:
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER_FULL) $(UNSATURATED_SOLINAS) --static 'p521' '17' '2^521 - 1' '32' && touch $@.ok) > $@.tmp
	$(HIDE)rm $@.ok && mv $@.tmp $@

## 2^224 - 2^96 + 1 ## does not bounds check
#p224_solinas_64.c:
#	$(SHOW)'SYNTHESIZE > $@'
#	$(HIDE)rm -f $@.ok
#	$(HIDE)($(TIMER_FULL) $(UNSATURATED_SOLINAS) --static 'p224' '4' '2^224 - 2^96 + 1' '64' && touch $@.ok) > $@.tmp
#	$(HIDE)rm $@.ok && mv $@.tmp $@

# 2^448 - 2^224 - 1
p448_solinas_64.c:
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER_FULL) $(UNSATURATED_SOLINAS) --static 'p448' '8' '2^448 - 2^224 - 1' '64' && touch $@.ok) > $@.tmp
	$(HIDE)rm $@.ok && mv $@.tmp $@

# 2^256 - 2^224 + 2^192 + 2^96 - 1
p256_64.c p256_32.c : p256_%.c :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER_FULL) $(WORD_BY_WORD_MONTGOMERY) --static 'p256' '2^256 - 2^224 + 2^192 + 2^96 - 1' '$*' && touch $@.ok) > $@.tmp
	$(HIDE)rm $@.ok && mv $@.tmp $@

# 2^256 - 2^32 - 977
secp256k1_64.c secp256k1_32.c : secp256k1_%.c :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER_FULL) $(WORD_BY_WORD_MONTGOMERY) --static 'secp256k1' '2^256 - 2^32 - 977' '$*' && touch $@.ok) > $@.tmp
	$(HIDE)rm $@.ok && mv $@.tmp $@

# 2^384 - 2^128 - 2^96 + 2^32 - 1
p384_64.c p384_32.c : p384_%.c :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER_FULL) $(WORD_BY_WORD_MONTGOMERY) --static 'p384' '2^384 - 2^128 - 2^96 + 2^32 - 1' '$*' && touch $@.ok) > $@.tmp
	$(HIDE)rm $@.ok && mv $@.tmp $@

# 2^224 - 2^96 + 1
p224_64.c p224_32.c : p224_%.c :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER_FULL) $(WORD_BY_WORD_MONTGOMERY) --static 'p224' '2^224 - 2^96 + 1' '$*' && touch $@.ok) > $@.tmp
	$(HIDE)rm $@.ok && mv $@.tmp $@

# 2^216 * 3^137 - 1
p434_64.c p434_32.c : p434_%.c :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER_FULL) $(WORD_BY_WORD_MONTGOMERY) --static 'p434' '2^216 * 3^137 - 1' '$*' && touch $@.ok) > $@.tmp
	$(HIDE)rm $@.ok && mv $@.tmp $@

test-c-files: $(ALL_C_FILES)
	$(CC) -Wall -Wno-unused-function -Werror $(CFLAGS) -c $(ALL_C_FILES)

$(UNSATURATED_SOLINAS_RUST_FILES): $(UNSATURATED_SOLINAS) # Makefile

$(WORD_BY_WORD_MONTGOMERY_RUST_FILES): $(WORD_BY_WORD_MONTGOMERY) # Makefile

# 2^255 - 19
curve25519_64.rs:
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER_FULL) $(UNSATURATED_SOLINAS) --lang=Rust '25519' '5' '2^255 - 19' '64' $(FUNCTIONS_FOR_25519) && touch $@.ok) > $@.tmp
	$(HIDE)rm $@.ok && mv $@.tmp fiat-rust/src/$@

# 2^255 - 19
curve25519_32.rs:
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER_FULL) $(UNSATURATED_SOLINAS) --lang=Rust '25519' '10' '2^255 - 19' '32' $(FUNCTIONS_FOR_25519) && touch $@.ok) > $@.tmp
	$(HIDE)rm $@.ok && mv $@.tmp fiat-rust/src/$@

# 2^521 - 1
p521_64.rs:
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER_FULL) $(UNSATURATED_SOLINAS) --lang=Rust 'p521' '9' '2^521 - 1' '64' && touch $@.ok) > $@.tmp
	$(HIDE)rm $@.ok && mv $@.tmp fiat-rust/src/$@

# 2^521 - 1
p521_32.rs:
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER_FULL) $(UNSATURATED_SOLINAS) --lang=Rust 'p521' '17' '2^521 - 1' '32' && touch $@.ok) > $@.tmp
	$(HIDE)rm $@.ok && mv $@.tmp fiat-rust/src/$@

## 2^224 - 2^96 + 1 ## does not bounds check
#p224_solinas_64.rs:
#	$(SHOW)'SYNTHESIZE > $@'
#	$(HIDE)rm -f $@.ok
#	$(HIDE)($(TIMER_FULL) $(UNSATURATED_SOLINAS) --lang=Rust 'p224' '4' '2^224 - 2^96 + 1' '64' && touch $@.ok) > $@.tmp
#	$(HIDE)rm $@.ok && mv $@.tmp fiat-rust/src/$@

# 2^448 - 2^224 - 1
p448_solinas_64.rs:
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER_FULL) $(UNSATURATED_SOLINAS) --lang=Rust 'p448' '8' '2^448 - 2^224 - 1' '64' && touch $@.ok) > $@.tmp
	$(HIDE)rm $@.ok && mv $@.tmp fiat-rust/src/$@

# 2^256 - 2^224 + 2^192 + 2^96 - 1
p256_64.rs p256_32.rs : p256_%.rs :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER_FULL) $(WORD_BY_WORD_MONTGOMERY) --lang=Rust 'p256' '2^256 - 2^224 + 2^192 + 2^96 - 1' '$*' && touch $@.ok) > $@.tmp
	$(HIDE)rm $@.ok && mv $@.tmp fiat-rust/src/$@

# 2^256 - 2^32 - 977
secp256k1_64.rs secp256k1_32.rs : secp256k1_%.rs :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER_FULL) $(WORD_BY_WORD_MONTGOMERY) --lang=Rust 'secp256k1' '2^256 - 2^32 - 977' '$*' && touch $@.ok) > $@.tmp
	$(HIDE)rm $@.ok && mv $@.tmp fiat-rust/src/$@

# 2^384 - 2^128 - 2^96 + 2^32 - 1
p384_64.rs p384_32.rs : p384_%.rs :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER_FULL) $(WORD_BY_WORD_MONTGOMERY) --lang=Rust 'p384' '2^384 - 2^128 - 2^96 + 2^32 - 1' '$*' && touch $@.ok) > $@.tmp
	$(HIDE)rm $@.ok && mv $@.tmp fiat-rust/src/$@

# 2^224 - 2^96 + 1
p224_64.rs p224_32.rs : p224_%.rs :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER_FULL) $(WORD_BY_WORD_MONTGOMERY) --lang=Rust 'p224' '2^224 - 2^96 + 1' '$*' && touch $@.ok) > $@.tmp
	$(HIDE)rm $@.ok && mv $@.tmp fiat-rust/src/$@

# 2^216 * 3^137 - 1
p434_64.rs p434_32.rs : p434_%.rs :
	$(SHOW)'SYNTHESIZE > $@'
	$(HIDE)rm -f $@.ok
	$(HIDE)($(TIMER_FULL) $(WORD_BY_WORD_MONTGOMERY) --lang=Rust 'p434' '2^216 * 3^137 - 1' '$*' && touch $@.ok) > $@.tmp
	$(HIDE)rm $@.ok && mv $@.tmp fiat-rust/src/$@

test-rust-files: $(ALL_RUST_FILES)
	cd fiat-rust; $(CARGO_BUILD)

# Perf testing
PERF_MAKEFILE = src/Rewriter/PerfTesting/Specific/generated/primes.mk
include $(PERF_MAKEFILE)

$(PERF_MAKEFILE): Makefile src/Rewriter/PerfTesting/Specific/make.py primes.txt
	./src/Rewriter/PerfTesting/Specific/make.py primes.txt
# PERF_TIMEOUT?=./etc/timeout -t 600 -m 10000 # limit to 10 GB # https://raw.githubusercontent.com/pshved/timeout/master/timeout
PERF_TIMEOUT?=timeout 600

.PHONY: perf perf-vos perf-extraction perf-standalone
PERF_VOLOGS := $(PERF_PRIME_VOS:.vo=.log)
PERF_SHLOGS := $(PERF_PRIME_SHS:.sh=.log)
PERF_LOGS := $(PERF_VOLOGS) $(PERF_SHLOGS)
ALL_PERF_LOGS := $(PERF_LOGS) $(PERF_LOGS:.log=.log.tmp)

perf-standalone: $(PERF_STANDALONE:%=src/ExtractionOCaml/%)

perf-vos: $(PERF_VOLOGS) \
	$(PERF_MAKEFILE) \
	src/Rewriter/PerfTesting/Core.vo \

perf-extraction: $(PERF_SHLOGS) \
	$(PERF_MAKEFILE) \
	perf-standalone

perf: perf-extraction perf-vos

.PHONE: perf-csv
PERF_TXTS := perf-old-vm-times.txt perf-new-vm-times.txt perf-new-extraction-times.txt perf-old-cbv-times.txt \
	perf-new-extraction-over-old-vm.txt perf-new-vm-over-old-vm.txt perf-old-vm-over-old-vm.txt \
	perf-new-extraction-over-new-extraction.txt perf-new-vm-over-new-extraction.txt perf-old-vm-over-new-extraction.txt
perf-csv: perf.csv perf-graph.csv $(PERF_TXTS)

perf.csv::
	$(SHOW)'PYTHON > $@'
	$(HIDE)./src/Rewriter/PerfTesting/Specific/to_csv.py $(wildcard $(ALL_PERF_LOGS)) > $@.tmp
	$(HIDE)sed 's/\r\n/\n/g; s/\r//g; s/\s*$$//g' $@.tmp > $@ && rm -f $@.tmp

perf-graph.csv::
	$(SHOW)'PYTHON > $@'
	$(HIDE)./src/Rewriter/PerfTesting/Specific/to_csv.py --for-graph $(wildcard $(ALL_PERF_LOGS)) > $@.tmp
	$(HIDE)sed 's/\r\n/\n/g; s/\r//g; s/\s*$$//g' $@.tmp > $@ && rm -f $@.tmp

$(PERF_TXTS) :: %.txt :
	$(SHOW)'PYTHON > $@'
	$(HIDE)./src/Rewriter/PerfTesting/Specific/to_csv.py --$* --txt $(wildcard $(ALL_PERF_LOGS)) > $@.tmp
	$(HIDE)sed 's/\r\n/\n/g; s/\r//g; s/\s*$$//g' $@.tmp > $@ && rm -f $@.tmp

$(PERF_PRIME_VOS:.vo=.log) : %.log : %.v src/Rewriter/PerfTesting/Core.vo
	$(SHOW)'PERF COQC $< > $@'
	$(HIDE)$(TIMER_FULL) $(PERF_TIMEOUT) $(COQC) $(COQDEBUG) $(COQFLAGS) $(COQLIBS) $< > $@.tmp
	$(HIDE)sed 's/\r\n/\n/g; s/\r//g; s/\s*$$//g' $@.tmp > $@ && rm -f $@.tmp

$(PERF_PRIME_SHS:.sh=.log) : %.log : %.sh $(PERF_STANDALONE:%=src/ExtractionOCaml/%)
	$(SHOW)'PERF SH $< > $@'
	$(HIDE)$(TIMER_FULL) $(PERF_TIMEOUT) bash $< > $@.tmp
	$(HIDE)sed 's/\r\n/\n/g; s/\r//g; s/\s*$$//g' $@.tmp > $@ && rm -f $@.tmp

clean::
	rm -f Makefile.coq

cleanall:: clean
	rm -rf src/Rewriter/PerfTesting/Specific/generated

install: coq

printenv::
	@echo "COQPATH =        $$COQPATH"

printdeps::
	$(HIDE)$(foreach vo,$(filter %.vo,$(MAKECMDGOALS)),echo '$(vo): $(call vo_closure,$(vo))'; )

printreversedeps::
	$(HIDE)$(foreach vo,$(filter %.vo,$(MAKECMDGOALS)),echo '$(vo): $(call vo_reverse_closure,$(VOFILES),$(vo))'; )
