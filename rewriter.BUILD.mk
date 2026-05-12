REWRITER_DIR := $(patsubst %/,%,$(dir $(lastword $(MAKEFILE_LIST))))/rewriter/src/Rewriter
OCAMLPATH ?=
export OCAMLPATH := $(REWRITER_DIR)/Util/plugins$(if $(OCAMLPATH),:$(OCAMLPATH))

include rewriter/Makefile.local.common
REWRITER_COMPAT_VFILES := $(addprefix rewriter/,$(filter %.v,$(COMPATIBILITY_FILES)))
REWRITER_VFILES := $(sort $(call rwildcard,$(REWRITER_DIR),*.v) $(REWRITER_COMPAT_VFILES))
REWRITER_COQDEPFLAGS := -I $(REWRITER_DIR)/Util/plugins -Q $(REWRITER_DIR) $(notdir $(REWRITER_DIR))
REWRITER_REQUIREFLAGS := -I $(REWRITER_DIR)/Util/plugins -Q $(O)/$(REWRITER_DIR) $(notdir $(REWRITER_DIR))

$(REWRITER_COMPAT_VFILES): | recursive-make-rewriter-plugin
$(O)/.coqdep.mk: | recursive-make-rewriter-plugin

.PHONY: recursive-make-rewriter-optfiles
recursive-make-rewriter-plugin: private MAKEFLAGS := --silent
recursive-make-rewriter-plugin: | recursive-make-rewriter-plugin
	$(MAKE) -C $(REWRITER_DIR)/../.. optfiles

REWRITER_COQFLAGS := $(REWRITER_REQUIREFLAGS)
$(O)/$(REWRITER_DIR)/%.vo: private COQFLAGS += $(REWRITER_COQFLAGS)
$(O)/$(REWRITER_DIR)/%.vos: private COQFLAGS += $(REWRITER_COQFLAGS)
$(O)/$(REWRITER_DIR)/%.vok: private COQFLAGS += $(REWRITER_COQFLAGS)
