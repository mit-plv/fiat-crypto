FIAT_CRYPTO_ROOT:=$(PWD)/../../../../../..
COQPATH_SEP:=:
COQPATH=$(FIAT_CRYPTO_ROOT)/coqprime/src$(COQPATH_SEP)$(FIAT_CRYPTO_ROOT)/rewriter/src$(COQPATH_SEP)$(FIAT_CRYPTO_ROOT)/rupicola/src$(COQPATH_SEP)$(FIAT_CRYPTO_ROOT)/rupicola/bedrock2/bedrock2/src$(COQPATH_SEP)$(FIAT_CRYPTO_ROOT)/rupicola/bedrock2/compiler/src$(COQPATH_SEP)$(FIAT_CRYPTO_ROOT)/rupicola/bedrock2/deps/riscv-coq/src$(COQPATH_SEP)$(FIAT_CRYPTO_ROOT)/rupicola/bedrock2/deps/coqutil/src
export COQPATH
COQC?=coqc

# fun fact: fiat-crypto forces all its dependencies to be in a physical folder named the same as their logical name, so that they can be put on COQPATH, but fiat-crypto itself violates this rule ("src" has to be mapped to "Crypto")
COQC_OPTIONS=-Q $(FIAT_CRYPTO_ROOT)/src Crypto

CROSS_COMPILE?=riscv32-unknown-linux-gnu-
RISCV_OBJCOPY?=$(CROSS_COMPILE)objcopy
RISCV_AS?=$(CROSS_COMPILE)as
RISCV_LD?=$(CROSS_COMPILE)ld
RISCV_GCC?=$(CROSS_COMPILE)gcc
RISCV_GDB?=$(CROSS_COMPILE)gdb

.PRECIOUS: %.vo %.o %.hex %.s %.bin

%.vo : %.v
	$(COQC) $(COQC_OPTIONS) $<

%.hex : %_compile.v
	$(COQC) $(COQC_OPTIONS) $< > $@

%.s : %_wrap.v asm_wrappers.vo %.hex
	$(COQC) $(COQC_OPTIONS) $< > $@

%.bin : %.hex
	xxd -r -p < $< > $@

%.o : %.s %.bin
	$(RISCV_AS) -march=rv32ima -mabi=ilp32 $< -o $@

%.exe : %_main.c %.o
	$(RISCV_GCC) -g -march=rv32ima -mabi=ilp32 $^ -o $@

SYSROOT:=$(dir $(shell which $(RISCV_GCC)))/../sysroot/

CURRENTLY_TESTING?=signer

run: $(CURRENTLY_TESTING).exe
	qemu-riscv32 -L $(SYSROOT) $<

debug: $(CURRENTLY_TESTING).exe
	qemu-riscv32 -L $(SYSROOT) -g 1234 $<

gdb:
	$(RISCV_GDB) -ex "target remote :1234" -ex "file $(CURRENTLY_TESTING).exe"

# %_main.o : %_main.c
#	$(RISCV_GCC) -c $< -o $@
#
# %.exe : %.o %_main.o
#	$(RISCV_LD) $^ -o $@
