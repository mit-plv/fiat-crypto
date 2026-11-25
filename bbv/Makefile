VS:=$(shell find . -type f -name '*.v')

.PHONY: coq clean force

coq: Makefile.coq.all $(VS)
	$(MAKE) -f Makefile.coq.all

Makefile.coq.all: force
	$(COQBIN)coq_makefile -f _CoqProject $(VS) -o Makefile.coq.all

force:

clean:: Makefile.coq.all
	$(MAKE) -f Makefile.coq.all clean
	rm -rf *.v.d *.glob *.vo *~ *.hi *.o
	rm -f Makefile.coq.all Makefile.coq.all.conf

install: Makefile.coq.all
	$(MAKE) -f Makefile.coq.all install

uninstall: Makefile.coq.all
	$(MAKE) -f Makefile.coq.all uninstall
