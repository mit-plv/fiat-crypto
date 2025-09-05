COQPRIME_DIR := $(patsubst %/,%,$(dir $(lastword $(MAKEFILE_LIST))))/coqprime/src/Coqprime
COQPRIME_VFILES := $(filter-out $(COQPRIME_DIR)/examples/% $(COQPRIME_DIR)/num/%,$(call rwildcard,$(COQPRIME_DIR),*.v))
COQPRIME_COQDEPFLAGS := -Q $(COQPRIME_DIR) $(notdir $(COQPRIME_DIR))
COQPRIME_REQUIREFLAGS := -Q $(O)/$(COQPRIME_DIR) $(notdir $(COQPRIME_DIR))

COQPRIME_COQFLAGS := $(COQPRIME_REQUIREFLAGS)
$(O)/$(COQPRIME_DIR)/%.vo: private COQFLAGS += $(COQPRIME_COQFLAGS)
$(O)/$(COQPRIME_DIR)/%.vos: private COQFLAGS += $(COQPRIME_COQFLAGS)
$(O)/$(COQPRIME_DIR)/%.vok: private COQFLAGS += $(COQPRIME_COQFLAGS)
# $(COQPRIME_DIR)/_CoqProject: private COQFLAGS += $(COQPRIME_COQFLAGS)
