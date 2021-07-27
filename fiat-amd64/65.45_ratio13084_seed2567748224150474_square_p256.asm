SECTION .text
	GLOBAL square_p256
square_p256:
sub rsp, 0x88 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x58 ], rbx; saving to stack
mov [ rsp + 0x60 ], rbp; saving to stack
mov [ rsp + 0x68 ], r12; saving to stack
mov [ rsp + 0x70 ], r13; saving to stack
mov [ rsp + 0x78 ], r14; saving to stack
mov [ rsp + 0x80 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x4 to register64
mov r10, [ rsi + 0x18 ]; load m64 x3 to register64
mov rdx, r10; x3 to rdx
mulx r10, r11, [ rsi + 0x8 ]; x134, x133<- x3 * arg1[1]
mulx rbx, rbp, [ rsi + 0x0 ]; x136, x135<- x3 * arg1[0]
xor r12, r12
adox r11, rbx
mulx r13, r14, [ rsi + 0x18 ]; x130, x129<- x3 * arg1[3]
mulx rdx, r15, [ rsi + 0x10 ]; x132, x131<- x3 * arg1[2]
adox r15, r10
adox r14, rdx
adox r13, r12
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rcx, r8, rax; x10, x9<- x4 * arg1[1]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r9, r10, rax; x8, x7<- x4 * arg1[2]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rbx, r12, rax; x12, x11<- x4 * arg1[0]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov [ rsp + 0x8 ], r13; spilling x143 to mem
mulx rdi, r13, r12; x25, x24<- x11 * 0xffffffffffffffff
mov rdx, 0xffffffff ; moving imm to reg
mov [ rsp + 0x10 ], r14; spilling x141 to mem
mov [ rsp + 0x18 ], r15; spilling x139 to mem
mulx r14, r15, r12; x23, x22<- x11 * 0xffffffff
mov rdx, [ rsi + 0x8 ]; load m64 x1 to register64
adcx r15, rdi
adc r14, 0x0
xor rdi, rdi
adox r8, rbx
mulx rbx, rdi, [ rsi + 0x8 ]; x44, x43<- x1 * arg1[1]
adcx r13, r12
mov [ rsp + 0x20 ], r11; spilling x137 to mem
mulx r13, r11, [ rsi + 0x0 ]; x46, x45<- x1 * arg1[0]
adox r10, rcx
adcx r15, r8
adcx r14, r10
setc cl; spill CF x34 to reg (rcx)
clc;
adcx rdi, r13
setc r8b; spill CF x48 to reg (r8)
clc;
adcx r11, r15
mov r13, rdx; preserving value of x1 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx rax, r10, rax; x6, x5<- x4 * arg1[3]
adcx rdi, r14
adox r10, r9
mov rdx, 0xffffffffffffffff ; moving imm to reg
mulx r9, r15, r11; x69, x68<- x54 * 0xffffffffffffffff
seto r14b; spill OF x18 to reg (r14)
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, r11
mov r15, 0xffffffff ; moving imm to reg
mov rdx, r11; x54 to rdx
mov [ rsp + 0x28 ], rbp; spilling x135 to mem
mulx r11, rbp, r15; x67, x66<- x54 * 0xffffffff
setc r15b; spill CF x57 to reg (r15)
clc;
adcx rbp, r9
mov r9, 0x0 ; moving imm to reg
adcx r11, r9
movzx r9, r14b; x19, copying x18 here, cause x18 is needed in a reg for other than x19, namely all: , x19, size: 1
lea r9, [ r9 + rax ]
mov rax, 0xffffffff00000001 ; moving imm to reg
xchg rdx, rax; 0xffffffff00000001, swapping with x54, which is currently in rdx
mulx r12, r14, r12; x21, x20<- x11 * 0xffffffff00000001
clc;
mov rdx, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, rdx; loading flag
adcx r10, r14
adcx r12, r9
adox rbp, rdi
mov rdx, r13; x1 to rdx
mulx r13, rcx, [ rsi + 0x18 ]; x40, x39<- x1 * arg1[3]
mulx rdx, rdi, [ rsi + 0x10 ]; x42, x41<- x1 * arg1[2]
setc r9b; spill CF x38 to reg (r9)
clc;
mov r14, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, r14; loading flag
adcx rbx, rdi
adcx rcx, rdx
mov r8, 0x0 ; moving imm to reg
adcx r13, r8
clc;
movzx r15, r15b
adcx r15, r14; loading flag
adcx r10, rbx
mov r15, [ rsi + 0x10 ]; load m64 x2 to register64
adcx rcx, r12
movzx r12, r9b; x62, copying x38 here, cause x38 is needed in a reg for other than x62, namely all: , x62--x63, size: 1
adcx r12, r13
adox r11, r10
mov r9, 0xffffffff00000001 ; moving imm to reg
mov rdx, r9; 0xffffffff00000001 to rdx
mulx rax, r9, rax; x65, x64<- x54 * 0xffffffff00000001
adox r9, rcx
adox rax, r12
seto dil; spill OF x83 to reg (rdi)
adc dil, 0x0
movzx rdi, dil
mov rbx, rdx; preserving value of 0xffffffff00000001 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r13, r10, r15; x91, x90<- x2 * arg1[0]
adox r10, rbp
mov rdx, 0xffffffff ; moving imm to reg
mulx rbp, rcx, r10; x112, x111<- x99 * 0xffffffff
mov r12, rdx; preserving value of 0xffffffff into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r8, r14, r15; x89, x88<- x2 * arg1[1]
adcx r14, r13
mov rdx, 0xffffffffffffffff ; moving imm to reg
mulx r13, rbx, r10; x114, x113<- x99 * 0xffffffffffffffff
adox r14, r11
setc r11b; spill CF x93 to reg (r11)
clc;
adcx rcx, r13
seto r13b; spill OF x102 to reg (r13)
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, r10
adox rcx, r14
seto bl; spill OF x121 to reg (rbx)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rcx, [ rsp + 0x28 ]
adcx rbp, r12
mulx r14, r12, rcx; x159, x158<- x144 * 0xffffffffffffffff
mov rdx, 0xffffffff ; moving imm to reg
mov byte [ rsp + 0x30 ], dil; spilling byte x83 to mem
mov [ rsp + 0x38 ], rbp; spilling x117 to mem
mulx rdi, rbp, rcx; x157, x156<- x144 * 0xffffffff
mov byte [ rsp + 0x40 ], bl; spilling byte x121 to mem
mov rbx, rdx; preserving value of 0xffffffff into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x48 ], rax; spilling x81 to mem
mov [ rsp + 0x50 ], r9; spilling x79 to mem
mulx rax, r9, r15; x87, x86<- x2 * arg1[2]
clc;
adcx r12, rcx
seto r12b; spill OF x145 to reg (r12)
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r11, r11b
adox r11, rdx; loading flag
adox r8, r9
setc r11b; spill CF x164 to reg (r11)
clc;
adcx rbp, r14
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r15, r14, r15; x85, x84<- x2 * arg1[3]
mov rdx, 0xffffffff00000001 ; moving imm to reg
mulx r10, r9, r10; x110, x109<- x99 * 0xffffffff00000001
adox r14, rax
mov rax, 0x0 ; moving imm to reg
adcx rdi, rax
adox r15, rax
add r13b, 0x7F; load flag from rm/8 into OF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
seto r13b; since that has deps, resore it whereever it was
adox r8, [ rsp + 0x50 ]
mov r13, [ rsp + 0x48 ]; x105, copying x81 here, cause x81 is needed in a reg for other than x105, namely all: , x105--x106, size: 1
adox r13, r14
movzx r14, byte [ rsp + 0x40 ]; load byte memx121 to register64
mov rax, -0x1 ; moving imm to reg
adcx r14, rax; loading flag
adcx r8, [ rsp + 0x38 ]
movzx r14, byte [ rsp + 0x30 ]; x107, copying x83 here, cause x83 is needed in a reg for other than x107, namely all: , x107--x108, size: 1
adox r14, r15
mulx rcx, r15, rcx; x155, x154<- x144 * 0xffffffff00000001
adcx r9, r13
adcx r10, r14
seto r13b; spill OF x128 to reg (r13)
adc r13b, 0x0
movzx r13, r13b
add r12b, 0xFF; load flag from rm/8 into CF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
setc r12b; since that has deps, resore it whereever it was
adcx r8, [ rsp + 0x20 ]
movzx r11, r11b
adox r11, rax; loading flag
adox r8, rbp
mov r12, [ rsp + 0x18 ]; x148, copying x139 here, cause x139 is needed in a reg for other than x148, namely all: , x148--x149, size: 1
adcx r12, r9
mov r11, [ rsp + 0x10 ]; x150, copying x141 here, cause x141 is needed in a reg for other than x150, namely all: , x150--x151, size: 1
adcx r11, r10
adox rdi, r12
movzx r13, r13b
mov rbp, [ rsp + 0x8 ]; x152, copying x143 here, cause x143 is needed in a reg for other than x152, namely all: , x152--x153, size: 1
adcx rbp, r13
adox r15, r11
adox rcx, rbp
setc r14b; spill CF x153 to reg (r14)
seto r9b; spill OF x172 to reg (r9)
mov r10, r8; x174, copying x165 here, cause x165 is needed in a reg for other than x174, namely all: , x184, x174--x175, size: 2
mov r13, 0xffffffffffffffff ; moving imm to reg
sub r10, r13
mov r12, rdi; x176, copying x167 here, cause x167 is needed in a reg for other than x176, namely all: , x185, x176--x177, size: 2
sbb r12, rbx
movzx r11, r9b; x173, copying x172 here, cause x172 is needed in a reg for other than x173, namely all: , x173, size: 1
movzx r14, r14b
lea r11, [ r11 + r14 ]
mov r14, r15; x178, copying x169 here, cause x169 is needed in a reg for other than x178, namely all: , x186, x178--x179, size: 2
sbb r14, 0x00000000
mov rbp, rcx; x180, copying x171 here, cause x171 is needed in a reg for other than x180, namely all: , x187, x180--x181, size: 2
sbb rbp, rdx
sbb r11, 0x00000000
cmovc r10, r8; if CF, x184<- x165 (nzVar)
cmovc rbp, rcx; if CF, x187<- x171 (nzVar)
cmovc r14, r15; if CF, x186<- x169 (nzVar)
cmovc r12, rdi; if CF, x185<- x167 (nzVar)
mov r11, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r11 + 0x0 ], r10; out1[0] = x184
mov [ r11 + 0x10 ], r14; out1[2] = x186
mov [ r11 + 0x8 ], r12; out1[1] = x185
mov [ r11 + 0x18 ], rbp; out1[3] = x187
mov rbx, [ rsp + 0x58 ]; restoring from stack
mov rbp, [ rsp + 0x60 ]; restoring from stack
mov r12, [ rsp + 0x68 ]; restoring from stack
mov r13, [ rsp + 0x70 ]; restoring from stack
mov r14, [ rsp + 0x78 ]; restoring from stack
mov r15, [ rsp + 0x80 ]; restoring from stack
add rsp, 0x88 
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; clocked at 4778 MHz
; first cyclecount 84.04, best 62.52136752136752, lastGood 65.44642857142857
; seed 2567748224150474 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 665906 ms / 60000 runs=> 11.098433333333332ms/run
; Time spent for assembling and measureing (initial batch_size=112, initial num_batches=101): 128818 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.19344772385291617
; number reverted permutation/ tried permutation: 22697 / 30183 =75.198%
; number reverted decision/ tried decision: 22132 / 29818 =74.224%