COQ_ARGS := -R bedrock/Bedrock Bedrock
MOD_NAME := Crypto
SRC_DIR  := src
MODULES  := Curves Galois Rep Specific Tactics Util

VS       := $(MODULES:%=src/%/*.v)

.PHONY: coq clean install
.DEFAULT_GOAL: coq

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile -R $(SRC_DIR) $(MOD_NAME) $(COQ_ARGS) $(VS) -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

install: coq
	ln -sfL $(shell pwd)/src $(shell coqtop -where)/user-contrib/Crypto
	ln -sfL $(shell pwd)/bedrock/Bedrock $(shell coqtop -where)/user-contrib/Bedrock

