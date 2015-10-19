# © 2015 the Massachusetts Institute of Technology
# @author bbaren + rsloan

SOURCES := $(shell grep -v '^-' _CoqProject | tr '\n' ' ')
COQLIBS := $(shell grep '^-' _CoqProject | tr '\n' ' ')

include .make/cc.mk
include .make/coq.mk

FAST_TARGETS += check_fiat check_bedrock clean

.DEFAULT_GOAL = all
.PHONY: all deps objects clean coquille

all: objects

deps: $(SOURCES:%=%.d) 

objects: deps $(SOURCES:%=%o)

clean:
	$(RM) $(foreach f,$(SOURCES),$(call coq-generated,$(basename $f)))

