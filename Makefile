MOD_NAME := Crypto
SRC_DIR  := src

.PHONY: coq clean install coqprime update-_CoqProject
.DEFAULT_GOAL := coq

SORT_COQPROJECT = sed 's,[^/]*/,~&,g' | env LC_COLLATE=C sort | sed 's,~,,g'

update-_CoqProject::
	(echo '-R $(SRC_DIR) $(MOD_NAME)'; (git ls-files "src/*.v" | $(SORT_COQPROJECT))) > _CoqProject

coq: coqprime Makefile.coq
	$(MAKE) -f Makefile.coq

coqprime:
	$(MAKE) -C coqprime

Makefile.coq: Makefile _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

install: coq Makefile.coq
	$(MAKE) -f Makefile.coq install
	$(MAKE) -C coqprime install
