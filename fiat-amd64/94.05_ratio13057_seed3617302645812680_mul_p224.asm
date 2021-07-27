SECTION .text
	GLOBAL mul_p224
mul_p224:
sub rsp, 0xc0 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x90 ], rbx; saving to stack
mov [ rsp + 0x98 ], rbp; saving to stack
mov [ rsp + 0xa0 ], r12; saving to stack
mov [ rsp + 0xa8 ], r13; saving to stack
mov [ rsp + 0xb0 ], r14; saving to stack
mov [ rsp + 0xb8 ], r15; saving to stack
mov rax, [ rsi + 0x10 ]; load m64 x2 to register64
mov r10, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x8 ]; saving arg2[1] in rdx.
mulx r11, rbx, rax; x97, x96<- x2 * arg2[1]
mov rbp, [ rsi + 0x8 ]; load m64 x1 to register64
mov rdx, rax; x2 to rdx
mulx rax, r12, [ r10 + 0x0 ]; x99, x98<- x2 * arg2[0]
mulx r13, r14, [ r10 + 0x18 ]; x93, x92<- x2 * arg2[3]
add rbx, rax; could be done better, if r0 has been u8 as well
xchg rdx, rbp; x1, swapping with x2, which is currently in rdx
mulx r15, rcx, [ r10 + 0x10 ]; x46, x45<- x1 * arg2[2]
mov r8, rdx; preserving value of x1 into a new reg
mov rdx, [ r10 + 0x10 ]; saving arg2[2] in rdx.
mulx rbp, r9, rbp; x95, x94<- x2 * arg2[2]
mov rdx, r8; x1 to rdx
mulx r8, rax, [ r10 + 0x8 ]; x48, x47<- x1 * arg2[1]
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov [ rsp + 0x8 ], rbx; spilling x100 to mem
mulx rdi, rbx, [ r10 + 0x0 ]; x50, x49<- x1 * arg2[0]
mov [ rsp + 0x10 ], r12; spilling x98 to mem
mov r12, [ rsi + 0x0 ]; load m64 x4 to register64
adcx r9, r11
adcx r14, rbp
adc r13, 0x0
mulx rdx, r11, [ r10 + 0x18 ]; x44, x43<- x1 * arg2[3]
xor rbp, rbp
adox rax, rdi
xchg rdx, r12; x4, swapping with x44, which is currently in rdx
mulx rdi, rbp, [ r10 + 0x10 ]; x8, x7<- x4 * arg2[2]
adox rcx, r8
mov [ rsp + 0x18 ], r13; spilling x106 to mem
mulx r8, r13, [ r10 + 0x8 ]; x10, x9<- x4 * arg2[1]
adox r11, r15
mov [ rsp + 0x20 ], r14; spilling x104 to mem
mulx r15, r14, [ r10 + 0x0 ]; x12, x11<- x4 * arg2[0]
mov [ rsp + 0x28 ], r9; spilling x102 to mem
mulx rdx, r9, [ r10 + 0x18 ]; x6, x5<- x4 * arg2[3]
adcx r13, r15
mov r15, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r15; 0xffffffffffffffff, swapping with x6, which is currently in rdx
mov [ rsp + 0x30 ], r11; spilling x55 to mem
mov [ rsp + 0x38 ], rcx; spilling x53 to mem
mulx r11, rcx, r14; _, x20<- x11 * 0xffffffffffffffff
adcx rbp, r8
mov r11, 0xffffffff00000000 ; moving imm to reg
xchg rdx, r11; 0xffffffff00000000, swapping with 0xffffffffffffffff, which is currently in rdx
mulx r8, r11, rcx; x27, x26<- x20 * 0xffffffff00000000
mov rdx, rcx; _, copying x20 here, cause x20 is needed in a reg for other than _, namely all: , x22--x23, x24--x25, _--x34, size: 3
mov [ rsp + 0x40 ], rax; spilling x51 to mem
seto al; spill OF x56 to reg (rax)
mov [ rsp + 0x48 ], rbx; spilling x49 to mem
mov rbx, -0x2 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rdx, r14
adcx r9, rdi
mov rdi, 0xffffffffffffffff ; moving imm to reg
mov rdx, rcx; x20 to rdx
mulx rcx, r14, rdi; x25, x24<- x20 * 0xffffffffffffffff
setc bl; spill CF x18 to reg (rbx)
clc;
adcx r14, r8
adox r11, r13
adox r14, rbp
movzx r13, bl; x19, copying x18 here, cause x18 is needed in a reg for other than x19, namely all: , x19, size: 1
lea r13, [ r13 + r15 ]
movzx r15, al; x57, copying x56 here, cause x56 is needed in a reg for other than x57, namely all: , x57, size: 1
lea r15, [ r15 + r12 ]
setc r12b; spill CF x29 to reg (r12)
clc;
adcx r11, [ rsp + 0x48 ]
xchg rdx, rdi; 0xffffffffffffffff, swapping with x20, which is currently in rdx
mulx rax, rbp, r11; _, x68<- x58 * 0xffffffffffffffff
mov rax, [ rsp + 0x40 ]; x60, copying x51 here, cause x51 is needed in a reg for other than x60, namely all: , x60--x61, size: 1
adcx rax, r14
mov r8, 0xffffffff00000000 ; moving imm to reg
xchg rdx, rbp; x68, swapping with 0xffffffffffffffff, which is currently in rdx
mulx rbx, r14, r8; x75, x74<- x68 * 0xffffffff00000000
mov r8, rdx; _, copying x68 here, cause x68 is needed in a reg for other than _, namely all: , x72--x73, _--x82, x70--x71, size: 3
seto bpl; spill OF x38 to reg (rbp)
mov [ rsp + 0x50 ], rsi; spilling arg1 to mem
mov rsi, -0x2 ; moving imm to reg
inc rsi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, r11
adox r14, rax
setc r8b; spill CF x61 to reg (r8)
clc;
adcx r14, [ rsp + 0x10 ]
mov r11, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r14; x107, swapping with x68, which is currently in rdx
mulx rax, rsi, r11; _, x117<- x107 * 0xffffffffffffffff
mov rax, 0xffffffff ; moving imm to reg
xchg rdx, rdi; x20, swapping with x107, which is currently in rdx
mulx rdx, r11, rax; x23, x22<- x20 * 0xffffffff
xchg rdx, rax; 0xffffffff, swapping with x23, which is currently in rdx
mov [ rsp + 0x58 ], r15; spilling x57 to mem
mov [ rsp + 0x60 ], r13; spilling x19 to mem
mulx r15, r13, rsi; x120, x119<- x117 * 0xffffffff
mov rdx, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x68 ], rbx; spilling x75 to mem
mov byte [ rsp + 0x70 ], r8b; spilling byte x61 to mem
mulx rbx, r8, rsi; x124, x123<- x117 * 0xffffffff00000000
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x78 ], r8; spilling x123 to mem
mov [ rsp + 0x80 ], r9; spilling x17 to mem
mulx r8, r9, rsi; x122, x121<- x117 * 0xffffffffffffffff
setc dl; spill CF x108 to reg (rdx)
clc;
adcx r9, rbx
adcx r13, r8
setc bl; spill CF x128 to reg (rbx)
clc;
adcx rsi, rdi
movzx rdi, bl; x129, copying x128 here, cause x128 is needed in a reg for other than x129, namely all: , x129, size: 1
lea rdi, [ rdi + r15 ]
setc r15b; spill CF x131 to reg (r15)
clc;
mov r8, -0x1 ; moving imm to reg
movzx r12, r12b
adcx r12, r8; loading flag
adcx rcx, r11
mov r12, 0x0 ; moving imm to reg
adcx rax, r12
mov r11, 0xffffffff ; moving imm to reg
xchg rdx, r14; x68, swapping with x108, which is currently in rdx
mulx rbx, r12, r11; x71, x70<- x68 * 0xffffffff
clc;
movzx rbp, bpl
adcx rbp, r8; loading flag
adcx rcx, [ rsp + 0x80 ]
setc bpl; spill CF x40 to reg (rbp)
movzx r8, byte [ rsp + 0x70 ]; load byte memx61 to register64
clc;
mov r11, -0x1 ; moving imm to reg
adcx r8, r11; loading flag
adcx rcx, [ rsp + 0x38 ]
mov r8, 0xffffffffffffffff ; moving imm to reg
mulx rdx, r11, r8; x73, x72<- x68 * 0xffffffffffffffff
setc r8b; spill CF x63 to reg (r8)
clc;
adcx r11, [ rsp + 0x68 ]
adcx r12, rdx
adox r11, rcx
seto cl; spill OF x86 to reg (rcx)
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r14, r14b
adox r14, rdx; loading flag
adox r11, [ rsp + 0x8 ]
mov r14, 0x0 ; moving imm to reg
adcx rbx, r14
clc;
movzx rbp, bpl
adcx rbp, rdx; loading flag
adcx rax, [ rsp + 0x60 ]
seto bpl; spill OF x110 to reg (rbp)
dec r14; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx r8, r8b
adox r8, r14; loading flag
adox rax, [ rsp + 0x30 ]
setc r8b; spill CF x42 to reg (r8)
clc;
movzx rcx, cl
adcx rcx, r14; loading flag
adcx rax, r12
movzx r8, r8b
mov r12, [ rsp + 0x58 ]; x66, copying x57 here, cause x57 is needed in a reg for other than x66, namely all: , x66--x67, size: 1
adox r12, r8
adcx rbx, r12
mov rcx, [ rsp + 0x50 ]; load m64 arg1 to register64
mov r8, [ rcx + 0x18 ]; load m64 x3 to register64
seto r12b; spill OF x67 to reg (r12)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, r14; loading flag
adox rax, [ rsp + 0x28 ]
setc bpl; spill CF x90 to reg (rbp)
clc;
movzx r15, r15b
adcx r15, r14; loading flag
adcx r11, [ rsp + 0x78 ]
adcx r9, rax
movzx r15, bpl; x91, copying x90 here, cause x90 is needed in a reg for other than x91, namely all: , x91, size: 1
movzx r12, r12b
lea r15, [ r15 + r12 ]
mov r12, [ rsp + 0x20 ]; x113, copying x104 here, cause x104 is needed in a reg for other than x113, namely all: , x113--x114, size: 1
adox r12, rbx
mov rdx, [ r10 + 0x0 ]; arg2[0] to rdx
mulx rbp, rbx, r8; x148, x147<- x3 * arg2[0]
mov rdx, [ r10 + 0x8 ]; arg2[1] to rdx
mulx rax, r14, r8; x146, x145<- x3 * arg2[1]
mov [ rsp + 0x88 ], r9; spilling x134 to mem
mov r9, [ rsp + 0x18 ]; x115, copying x106 here, cause x106 is needed in a reg for other than x115, namely all: , x115--x116, size: 1
adox r9, r15
adcx r13, r12
seto r15b; spill OF x116 to reg (r15)
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, rbp
mov rdx, [ r10 + 0x18 ]; arg2[3] to rdx
mulx rbp, r12, r8; x142, x141<- x3 * arg2[3]
adcx rdi, r9
mov rdx, r8; x3 to rdx
mulx rdx, r8, [ r10 + 0x10 ]; x144, x143<- x3 * arg2[2]
adox r8, rax
movzx rax, r15b; x140, copying x116 here, cause x116 is needed in a reg for other than x140, namely all: , x140, size: 1
mov r9, 0x0 ; moving imm to reg
adcx rax, r9
clc;
adcx rbx, r11
mov r11, [ rsp + 0x88 ]; x158, copying x134 here, cause x134 is needed in a reg for other than x158, namely all: , x158--x159, size: 1
adcx r11, r14
adox r12, rdx
mov r15, 0xffffffffffffffff ; moving imm to reg
mov rdx, r15; 0xffffffffffffffff to rdx
mulx r15, r14, rbx; _, x166<- x156 * 0xffffffffffffffff
mulx r15, r9, r14; x171, x170<- x166 * 0xffffffffffffffff
mov rdx, 0x0 ; moving imm to reg
adox rbp, rdx
adcx r8, r13
adcx r12, rdi
mov r13, r14; _, copying x166 here, cause x166 is needed in a reg for other than _, namely all: , x172--x173, x168--x169, _--x180, size: 3
mov rdi, -0x3 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r13, rbx
mov r13, 0xffffffff ; moving imm to reg
xchg rdx, r14; x166, swapping with 0x0, which is currently in rdx
mulx rbx, r14, r13; x169, x168<- x166 * 0xffffffff
mov rdi, 0xffffffff00000000 ; moving imm to reg
mulx rdx, r13, rdi; x173, x172<- x166 * 0xffffffff00000000
adox r13, r11
adcx rbp, rax
setc al; spill CF x165 to reg (rax)
clc;
adcx r9, rdx
adcx r14, r15
mov r11, 0x0 ; moving imm to reg
adcx rbx, r11
adox r9, r8
adox r14, r12
seto r15b; spill OF x186 to reg (r15)
mov r8, r13; x190, copying x181 here, cause x181 is needed in a reg for other than x190, namely all: , x190--x191, x200, size: 2
sub r8, 0x00000001
dec r11; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r15, r15b
adox r15, r11; loading flag
adox rbp, rbx
movzx r12, al; x189, copying x165 here, cause x165 is needed in a reg for other than x189, namely all: , x189, size: 1
mov rdx, 0x0 ; moving imm to reg
adox r12, rdx
mov rax, r9; x192, copying x183 here, cause x183 is needed in a reg for other than x192, namely all: , x201, x192--x193, size: 2
sbb rax, rdi
mov rbx, r14; x194, copying x185 here, cause x185 is needed in a reg for other than x194, namely all: , x202, x194--x195, size: 2
mov r15, 0xffffffffffffffff ; moving imm to reg
sbb rbx, r15
mov rdx, rbp; x196, copying x187 here, cause x187 is needed in a reg for other than x196, namely all: , x196--x197, x203, size: 2
mov r11, 0xffffffff ; moving imm to reg
sbb rdx, r11
sbb r12, 0x00000000
cmovc rbx, r14; if CF, x202<- x185 (nzVar)
cmovc rax, r9; if CF, x201<- x183 (nzVar)
cmovc r8, r13; if CF, x200<- x181 (nzVar)
cmovc rdx, rbp; if CF, x203<- x187 (nzVar)
mov r12, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r12 + 0x0 ], r8; out1[0] = x200
mov [ r12 + 0x18 ], rdx; out1[3] = x203
mov [ r12 + 0x8 ], rax; out1[1] = x201
mov [ r12 + 0x10 ], rbx; out1[2] = x202
mov rbx, [ rsp + 0x90 ]; restoring from stack
mov rbp, [ rsp + 0x98 ]; restoring from stack
mov r12, [ rsp + 0xa0 ]; restoring from stack
mov r13, [ rsp + 0xa8 ]; restoring from stack
mov r14, [ rsp + 0xb0 ]; restoring from stack
mov r15, [ rsp + 0xb8 ]; restoring from stack
add rsp, 0xc0 
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; clocked at 2200 MHz
; first cyclecount 103.36, best 89.46835443037975, lastGood 94.05
; seed 3617302645812680 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1010654 ms / 60000 runs=> 16.84423333333333ms/run
; Time spent for assembling and measureing (initial batch_size=80, initial num_batches=101): 145407 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.1438741646498208
; number reverted permutation/ tried permutation: 26206 / 29953 =87.490%
; number reverted decision/ tried decision: 23282 / 30048 =77.483%