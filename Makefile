
MOD_NAME := Crypto
SRC_DIR  := src
FLAGS := -R Coqprime/Coqprime Coqprime

.PHONY: coq clean install coqprime update-_CoqProject
.DEFAULT_GOAL := coq

update-_CoqProject::
	@(echo "-R $(SRC_DIR) $(MOD_NAME)"; echo "$(FLAGS)"; git ls-files src/*.v) > _CoqProject

coq: coqprime Makefile.coq
	@$(MAKE) -f Makefile.coq

coqprime:
	@$(MAKE) -C coqprime

Makefile.coq: Makefile _CoqProject
	@coq_makefile -f _CoqProject -o Makefile.coq 2> /dev/null

clean: Makefile.coq
	@$(MAKE) -f Makefile.coq clean
	@rm -f Makefile.coq

install: coq Makefile.coq
	@$(MAKE) -f Makefile.coq install
	@$(MAKE) -C coqprime install
