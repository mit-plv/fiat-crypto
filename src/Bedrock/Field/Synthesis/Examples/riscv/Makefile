FIAT_CRYPTO_ROOT:=$(PWD)/../../../../../..
COQPATH_SEP:=:
COQPATH=$(FIAT_CRYPTO_ROOT)/coqprime/src$(COQPATH_SEP)$(FIAT_CRYPTO_ROOT)/rewriter/src$(COQPATH_SEP)$(FIAT_CRYPTO_ROOT)/rupicola/src$(COQPATH_SEP)$(FIAT_CRYPTO_ROOT)/rupicola/bedrock2/bedrock2/src$(COQPATH_SEP)$(FIAT_CRYPTO_ROOT)/rupicola/bedrock2/compiler/src$(COQPATH_SEP)$(FIAT_CRYPTO_ROOT)/rupicola/bedrock2/deps/riscv-coq/src$(COQPATH_SEP)$(FIAT_CRYPTO_ROOT)/rupicola/bedrock2/deps/coqutil/src
export COQPATH
COQC?=coqc

# fun fact: fiat-crypto forces all its dependencies to be in a physical folder named the same as their logical name, so that they can be put on COQPATH, but fiat-crypto itself violates this rule ("src" has to be mapped to "Crypto")
COQC_OPTIONS=-Q $(FIAT_CRYPTO_ROOT)/src Crypto

.PRECIOUS: %.vo

%.vo : %.v
	$(COQC) $(COQC_OPTIONS) $<

%.hex : %.v SyscallNumbers.vo
	$(COQC) $(COQC_OPTIONS) $< > $@

%.bin : %.hex
	xxd -r -p < $< > $@

%_wrapper.s : %.bin wrapper_template.s
	sed wrapper_template.s -e 's/FILENAME/'$<'/g' > $@

%.o : %_wrapper.s
	riscv32-unknown-linux-gnu-as $< -o $@

%.exe : %.o
	riscv32-unknown-linux-gnu-ld $< -o $@
