FIATCRYPTO_EVERYTHING_VFILES := $(filter-out $(FIATCRYPTO_DIR)/Everything.v $(FIATCRYPTO_DIR)/Bedrock/Everything.v $(FIATCRYPTO_DIR)/Extraction% $(FIATCRYPTO_DIR)/PerfTesting/% $(FIATCRYPTO_DIR)/Rewriter/PerfTesting/%,$(FIATCRYPTO_VFILES))
#
# PerfTesting targets depend on Everything.vo
FIATCRYPTO_COQDEPFLAGS += -R $(O)/$(FIATCRYPTO_DIR) Crypto

empty :=
space := $(empty) $(empty)
define newline


endef

eq = $(and $(findstring $(1),$(2)),$(findstring $(2),$(1)))


FIATCRYPTO_EVERYTHING_CONTENTS := Require Import$(newline)$(subst $(space),$(newline),$(sort $(subst /,.,$(patsubst $(FIATCRYPTO_DIR)/%.v,Crypto/%,$(FIATCRYPTO_EVERYTHING_VFILES)))))$(newline).

$(O)/$(FIATCRYPTO_DIR):
	@mkdir -p $@

$(O)/$(FIATCRYPTO_DIR)/Everything.v: $(FIATCRYPTO_EVERYTHING_VFILES) | $(O)/$(FIATCRYPTO_DIR)
	$(if $(call eq,$(file <$@),$(FIATCRYPTO_EVERYTHING_CONTENTS)),,\
		$(file >$@,$(FIATCRYPTO_EVERYTHING_CONTENTS)$(newline)))

$(O)/.coqdep.mk: | $(O)/$(FIATCRYPTO_DIR)/Everything.v
