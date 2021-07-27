SECTION .text
	GLOBAL mul_p224
mul_p224:
sub rsp, 0xb8 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x88 ], rbx; saving to stack
mov [ rsp + 0x90 ], rbp; saving to stack
mov [ rsp + 0x98 ], r12; saving to stack
mov [ rsp + 0xa0 ], r13; saving to stack
mov [ rsp + 0xa8 ], r14; saving to stack
mov [ rsp + 0xb0 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x4 to register64
mov r10, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x0 ]; saving arg2[0] in rdx.
mulx r11, rbx, rax; x12, x11<- x4 * arg2[0]
mov rbp, 0xffffffffffffffff ; moving imm to reg
mov rdx, rbp; 0xffffffffffffffff to rdx
mulx rbp, r12, rbx; _, x20<- x11 * 0xffffffffffffffff
mov rbp, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mulx r13, r14, rax; x10, x9<- x4 * arg2[1]
mov r15, 0xffffffff00000000 ; moving imm to reg
mov rdx, r12; x20 to rdx
mulx r12, rcx, r15; x27, x26<- x20 * 0xffffffff00000000
mov r8, rdx; _, copying x20 here, cause x20 is needed in a reg for other than _, namely all: , x22--x23, x24--x25, _--x34, size: 3
add r8, rbx; could be done better, if r0 has been u8 as well
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, r11
adcx rcx, r14
mov r9, [ rsi + 0x8 ]; load m64 x1 to register64
mov r11, rdx; preserving value of x20 into a new reg
mov rdx, [ r10 + 0x0 ]; saving arg2[0] in rdx.
mulx rbx, r14, r9; x50, x49<- x1 * arg2[0]
setc r8b; spill CF x36 to reg (r8)
clc;
adcx r14, rcx
mov rdx, rbp; 0xffffffffffffffff to rdx
mulx rbp, rcx, r14; _, x68<- x58 * 0xffffffffffffffff
mulx rbp, r15, rcx; x73, x72<- x68 * 0xffffffffffffffff
mov rdx, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov [ rsp + 0x8 ], rbx; spilling x50 to mem
mulx rdi, rbx, rcx; x75, x74<- x68 * 0xffffffff00000000
mov rdx, 0xffffffff ; moving imm to reg
mov [ rsp + 0x10 ], rbx; spilling x74 to mem
mov byte [ rsp + 0x18 ], r8b; spilling byte x36 to mem
mulx rbx, r8, rcx; x71, x70<- x68 * 0xffffffff
setc dl; spill CF x59 to reg (rdx)
clc;
adcx r15, rdi
adcx r8, rbp
mov rbp, 0x0 ; moving imm to reg
adcx rbx, rbp
mov dil, dl; preserving value of x59 into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mov [ rsp + 0x20 ], rbx; spilling x80 to mem
mulx rbp, rbx, r9; x48, x47<- x1 * arg2[1]
clc;
adcx rcx, r14
mov rdx, [ r10 + 0x10 ]; arg2[2] to rdx
mulx rcx, r14, rax; x8, x7<- x4 * arg2[2]
mov [ rsp + 0x28 ], r8; spilling x78 to mem
mov r8, 0xffffffffffffffff ; moving imm to reg
mov rdx, r11; x20 to rdx
mov [ rsp + 0x30 ], r15; spilling x76 to mem
mulx r11, r15, r8; x25, x24<- x20 * 0xffffffffffffffff
setc r8b; spill CF x82 to reg (r8)
clc;
adcx r15, r12
adox r14, r13
setc r13b; spill CF x29 to reg (r13)
movzx r12, byte [ rsp + 0x18 ]; load byte memx36 to register64
clc;
mov [ rsp + 0x38 ], rbp; spilling x48 to mem
mov rbp, -0x1 ; moving imm to reg
adcx r12, rbp; loading flag
adcx r14, r15
setc r12b; spill CF x38 to reg (r12)
clc;
adcx rbx, [ rsp + 0x8 ]
setc r15b; spill CF x52 to reg (r15)
clc;
movzx rdi, dil
adcx rdi, rbp; loading flag
adcx r14, rbx
mov rdi, 0xffffffff ; moving imm to reg
mulx rdx, rbx, rdi; x23, x22<- x20 * 0xffffffff
setc bpl; spill CF x61 to reg (rbp)
clc;
mov rdi, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, rdi; loading flag
adcx r14, [ rsp + 0x10 ]
setc r8b; spill CF x84 to reg (r8)
clc;
movzx r13, r13b
adcx r13, rdi; loading flag
adcx r11, rbx
mov r13, rdx; preserving value of x23 into a new reg
mov rdx, [ r10 + 0x18 ]; saving arg2[3] in rdx.
mulx rax, rbx, rax; x6, x5<- x4 * arg2[3]
mov rdx, r9; x1 to rdx
mulx r9, rdi, [ r10 + 0x18 ]; x44, x43<- x1 * arg2[3]
mov [ rsp + 0x40 ], r14; spilling x83 to mem
mov r14, [ rsi + 0x18 ]; load m64 x3 to register64
adox rbx, rcx
mulx rdx, rcx, [ r10 + 0x10 ]; x46, x45<- x1 * arg2[2]
mov byte [ rsp + 0x48 ], r8b; spilling byte x84 to mem
mov r8, 0x0 ; moving imm to reg
adcx r13, r8
adox rax, r8
add r15b, 0xFF; load flag from rm/8 into CF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
setc r15b; since that has deps, resore it whereever it was
adcx rcx, [ rsp + 0x38 ]
adcx rdi, rdx
mov rdx, [ r10 + 0x0 ]; arg2[0] to rdx
mulx r15, r8, r14; x148, x147<- x3 * arg2[0]
adc r9, 0x0
add r12b, 0xFF; load flag from rm/8 into CF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
setc r12b; since that has deps, resore it whereever it was
adcx rbx, r11
mov r12, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, r12; loading flag
adox rbx, rcx
adcx r13, rax
adox rdi, r13
mov rbp, [ rsi + 0x10 ]; load m64 x2 to register64
seto r11b; spill OF x65 to reg (r11)
movzx rax, byte [ rsp + 0x48 ]; load byte memx84 to register64
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rcx, -0x1 ; moving imm to reg
adox rax, rcx; loading flag
adox rbx, [ rsp + 0x30 ]
mov rax, [ rsp + 0x28 ]; x87, copying x78 here, cause x78 is needed in a reg for other than x87, namely all: , x87--x88, size: 1
adox rax, rdi
movzx r13, r11b; x66, copying x65 here, cause x65 is needed in a reg for other than x66, namely all: , x66--x67, size: 1
adcx r13, r9
mov r9, [ rsp + 0x20 ]; x89, copying x80 here, cause x80 is needed in a reg for other than x89, namely all: , x89--x90, size: 1
adox r9, r13
seto r11b; spill OF x91 to reg (r11)
adc r11b, 0x0
movzx r11, r11b
mov rdx, [ r10 + 0x0 ]; arg2[0] to rdx
mulx rdi, r13, rbp; x99, x98<- x2 * arg2[0]
adox r13, [ rsp + 0x40 ]
mov rdx, [ r10 + 0x8 ]; arg2[1] to rdx
mulx r12, rcx, r14; x146, x145<- x3 * arg2[1]
adcx rcx, r15
mov rdx, [ r10 + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x50 ], rcx; spilling x149 to mem
mulx r15, rcx, r14; x144, x143<- x3 * arg2[2]
adcx rcx, r12
mov rdx, [ r10 + 0x18 ]; arg2[3] to rdx
mulx r14, r12, r14; x142, x141<- x3 * arg2[3]
adcx r12, r15
mov r15, 0xffffffffffffffff ; moving imm to reg
mov rdx, r15; 0xffffffffffffffff to rdx
mov [ rsp + 0x58 ], r12; spilling x153 to mem
mulx r15, r12, r13; _, x117<- x107 * 0xffffffffffffffff
mov [ rsp + 0x60 ], rcx; spilling x151 to mem
mulx r15, rcx, r12; x122, x121<- x117 * 0xffffffffffffffff
mov rdx, 0xffffffff ; moving imm to reg
mov [ rsp + 0x68 ], r8; spilling x147 to mem
mov byte [ rsp + 0x70 ], r11b; spilling byte x91 to mem
mulx r8, r11, r12; x120, x119<- x117 * 0xffffffff
mov rdx, 0x0 ; moving imm to reg
adcx r14, rdx
mov rdx, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x78 ], r14; spilling x155 to mem
mov [ rsp + 0x80 ], r9; spilling x89 to mem
mulx r14, r9, r12; x124, x123<- x117 * 0xffffffff00000000
clc;
adcx rcx, r14
adcx r11, r15
mov r15, 0x0 ; moving imm to reg
adcx r8, r15
xchg rdx, rbp; x2, swapping with 0xffffffff00000000, which is currently in rdx
mulx r14, r15, [ r10 + 0x8 ]; x97, x96<- x2 * arg2[1]
clc;
adcx r12, r13
setc r12b; spill CF x131 to reg (r12)
clc;
adcx r15, rdi
adox r15, rbx
mulx rbx, rdi, [ r10 + 0x10 ]; x95, x94<- x2 * arg2[2]
adcx rdi, r14
mulx rdx, r13, [ r10 + 0x18 ]; x93, x92<- x2 * arg2[3]
adox rdi, rax
adcx r13, rbx
mov rax, 0x0 ; moving imm to reg
adcx rdx, rax
clc;
mov r14, -0x1 ; moving imm to reg
movzx r12, r12b
adcx r12, r14; loading flag
adcx r15, r9
adcx rcx, rdi
mov r9, [ rsp + 0x80 ]; x113, copying x89 here, cause x89 is needed in a reg for other than x113, namely all: , x113--x114, size: 1
adox r9, r13
adcx r11, r9
movzx r12, byte [ rsp + 0x70 ]; x115, copying x91 here, cause x91 is needed in a reg for other than x115, namely all: , x115--x116, size: 1
adox r12, rdx
adcx r8, r12
setc bl; spill CF x139 to reg (rbx)
clc;
adcx r15, [ rsp + 0x68 ]
mov rdi, 0xffffffffffffffff ; moving imm to reg
mov rdx, r15; x156 to rdx
mulx r15, r13, rdi; _, x166<- x156 * 0xffffffffffffffff
xchg rdx, r13; x166, swapping with x156, which is currently in rdx
mulx r15, r9, rdi; x171, x170<- x166 * 0xffffffffffffffff
movzx r12, bl; x140, copying x139 here, cause x139 is needed in a reg for other than x140, namely all: , x140, size: 1
adox r12, rax
mov rbx, rdx; _, copying x166 here, cause x166 is needed in a reg for other than _, namely all: , x172--x173, x168--x169, _--x180, size: 3
mov r14, -0x3 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbx, r13
mov rbx, [ rsp + 0x50 ]; x158, copying x149 here, cause x149 is needed in a reg for other than x158, namely all: , x158--x159, size: 1
adcx rbx, rcx
mov rcx, [ rsp + 0x60 ]; x160, copying x151 here, cause x151 is needed in a reg for other than x160, namely all: , x160--x161, size: 1
adcx rcx, r11
mulx r11, r13, rbp; x173, x172<- x166 * 0xffffffff00000000
setc r14b; spill CF x161 to reg (r14)
clc;
adcx r9, r11
adox r13, rbx
mov rbx, 0xffffffff ; moving imm to reg
mulx rdx, r11, rbx; x169, x168<- x166 * 0xffffffff
adox r9, rcx
adcx r11, r15
adcx rdx, rax
seto r15b; spill OF x184 to reg (r15)
mov rcx, r13; x190, copying x181 here, cause x181 is needed in a reg for other than x190, namely all: , x200, x190--x191, size: 2
sub rcx, 0x00000001
mov rax, r9; x192, copying x183 here, cause x183 is needed in a reg for other than x192, namely all: , x192--x193, x201, size: 2
sbb rax, rbp
mov rbp, 0x0 ; moving imm to reg
dec rbp; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r14, r14b
adox r14, rbp; loading flag
adox r8, [ rsp + 0x58 ]
mov r14, [ rsp + 0x78 ]; x164, copying x155 here, cause x155 is needed in a reg for other than x164, namely all: , x164--x165, size: 1
adox r14, r12
seto r12b; spill OF x165 to reg (r12)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, rbp; loading flag
adox r8, r11
adox rdx, r14
movzx r15, r12b; x189, copying x165 here, cause x165 is needed in a reg for other than x189, namely all: , x189, size: 1
mov r11, 0x0 ; moving imm to reg
adox r15, r11
mov r12, r8; x194, copying x185 here, cause x185 is needed in a reg for other than x194, namely all: , x202, x194--x195, size: 2
sbb r12, rdi
mov r14, rdx; x196, copying x187 here, cause x187 is needed in a reg for other than x196, namely all: , x196--x197, x203, size: 2
sbb r14, rbx
sbb r15, 0x00000000
cmovc r12, r8; if CF, x202<- x185 (nzVar)
cmovc r14, rdx; if CF, x203<- x187 (nzVar)
mov r15, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r15 + 0x18 ], r14; out1[3] = x203
cmovc rcx, r13; if CF, x200<- x181 (nzVar)
cmovc rax, r9; if CF, x201<- x183 (nzVar)
mov [ r15 + 0x0 ], rcx; out1[0] = x200
mov [ r15 + 0x10 ], r12; out1[2] = x202
mov [ r15 + 0x8 ], rax; out1[1] = x201
mov rbx, [ rsp + 0x88 ]; restoring from stack
mov rbp, [ rsp + 0x90 ]; restoring from stack
mov r12, [ rsp + 0x98 ]; restoring from stack
mov r13, [ rsp + 0xa0 ]; restoring from stack
mov r14, [ rsp + 0xa8 ]; restoring from stack
mov r15, [ rsp + 0xb0 ]; restoring from stack
add rsp, 0xb8 
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; clocked at 4769 MHz
; first cyclecount 91.085, best 72.13592233009709, lastGood 73.94059405940594
; seed 704989933151320 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 749020 ms / 60000 runs=> 12.483666666666666ms/run
; Time spent for assembling and measureing (initial batch_size=101, initial num_batches=101): 105000 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.14018317267896718
; number reverted permutation/ tried permutation: 23128 / 29977 =77.152%
; number reverted decision/ tried decision: 22668 / 30024 =75.500%