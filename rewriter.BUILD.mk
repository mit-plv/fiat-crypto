REWRITER_DIR := $(patsubst %/,%,$(dir $(lastword $(MAKEFILE_LIST))))/rewriter/src/Rewriter
REWRITER_VFILES := $(call rwildcard,$(REWRITER_DIR),*.v)
REWRITER_COQDEPFLAGS := -I $(REWRITER_DIR)/Util/plugins -Q $(REWRITER_DIR) $(notdir $(REWRITER_DIR))
REWRITER_REQUIREFLAGS := -I $(REWRITER_DIR)/Util/plugins -Q $(O)/$(REWRITER_DIR) $(notdir $(REWRITER_DIR))

REWRITER_COQFLAGS := $(REWRITER_REQUIREFLAGS)
$(O)/$(REWRITER_DIR)/%.vo: private COQFLAGS += $(REWRITER_COQFLAGS)
$(O)/$(REWRITER_DIR)/%.vos: private COQFLAGS += $(REWRITER_COQFLAGS)
$(O)/$(REWRITER_DIR)/%.vok: private COQFLAGS += $(REWRITER_COQFLAGS)
$(O)/$(REWRITER_DIR)/Util/plugins/%.vo: rewriterplugin
$(O)/$(REWRITER_DIR)/Util/plugins/%.vos: rewriterplugin
$(O)/$(REWRITER_DIR)/Util/plugins/%.vok: rewriterplugin
# .PHONY: rewriterplugin
# rewriterplugin: private MAKEFLAGS := --silent
# rewriterplugin:
# 	$(MAKE) -C $(REWRITER_DIR)/../.. optfiles
# $(O)/.coqdep.mk: | rewriterplugin
