# © 2015 the Massachusetts Institute of Technology
# @author bbaren

SOURCES := $(shell grep -v '^-' _CoqProject | tr '\n' ' ')
COQLIBS := $(shell grep '^-' _CoqProject | tr '\n' ' ')

include .make/cc.mk
include .make/coq.mk

FAST_TARGETS += check_fiat clean

.DEFAULT_GOAL = all
.PHONY: all clean coquille

all: $(SOURCES)
	@echo "done!"

coquille:
	vim -c "execute coquille#Launch($(COQLIBS))" -N

clean:
	$(RM) $(foreach f,$(SOURCES),$(call coq-generated,$(basename $f)))

