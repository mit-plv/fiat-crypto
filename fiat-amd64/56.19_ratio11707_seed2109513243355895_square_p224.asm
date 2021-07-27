SECTION .text
	GLOBAL square_p224
square_p224:
sub rsp, 0xc8 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x98 ], rbx; saving to stack
mov [ rsp + 0xa0 ], rbp; saving to stack
mov [ rsp + 0xa8 ], r12; saving to stack
mov [ rsp + 0xb0 ], r13; saving to stack
mov [ rsp + 0xb8 ], r14; saving to stack
mov [ rsp + 0xc0 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x4 to register64
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r10, r11, rax; x12, x11<- x4 * arg1[0]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbx, rbp, rax; x10, x9<- x4 * arg1[1]
mov r12, [ rsi + 0x8 ]; load m64 x1 to register64
mov r13, 0xffffffffffffffff ; moving imm to reg
mov rdx, r11; x11 to rdx
mulx r11, r14, r13; _, x20<- x11 * 0xffffffffffffffff
mov r11, r14; _, copying x20 here, cause x20 is needed in a reg for other than _, namely all: , x24--x25, x26--x27, _--x34, x22--x23, size: 4
add r11, rdx; could be done better, if r0 has been u8 as well
mov r11, 0xffffffff00000000 ; moving imm to reg
mov rdx, r11; 0xffffffff00000000 to rdx
mulx r11, r15, r14; x27, x26<- x20 * 0xffffffff00000000
mov rcx, rdx; preserving value of 0xffffffff00000000 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r8, r9, r12; x50, x49<- x1 * arg1[0]
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, r10
adcx r15, rbp
setc r10b; spill CF x36 to reg (r10)
clc;
adcx r9, r15
mov rdx, r13; 0xffffffffffffffff to rdx
mulx r13, rbp, r9; _, x68<- x58 * 0xffffffffffffffff
mulx r13, r15, rbp; x73, x72<- x68 * 0xffffffffffffffff
xchg rdx, rcx; 0xffffffff00000000, swapping with 0xffffffffffffffff, which is currently in rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx rcx, rdi, rbp; x75, x74<- x68 * 0xffffffff00000000
mov rdx, 0xffffffff ; moving imm to reg
mov [ rsp + 0x8 ], rdi; spilling x74 to mem
mov byte [ rsp + 0x10 ], r10b; spilling byte x36 to mem
mulx rdi, r10, rbp; x71, x70<- x68 * 0xffffffff
mov rdx, [ rsi + 0x10 ]; load m64 x2 to register64
mov [ rsp + 0x18 ], r8; spilling x50 to mem
setc r8b; spill CF x59 to reg (r8)
clc;
adcx r15, rcx
adcx r10, r13
mov r13, 0x0 ; moving imm to reg
adcx rdi, r13
mulx rcx, r13, [ rsi + 0x18 ]; x93, x92<- x2 * arg1[3]
mov [ rsp + 0x20 ], rdi; spilling x80 to mem
mov [ rsp + 0x28 ], r10; spilling x78 to mem
mulx rdi, r10, [ rsi + 0x8 ]; x97, x96<- x2 * arg1[1]
mov [ rsp + 0x30 ], r15; spilling x76 to mem
mov byte [ rsp + 0x38 ], r8b; spilling byte x59 to mem
mulx r15, r8, [ rsi + 0x0 ]; x99, x98<- x2 * arg1[0]
clc;
adcx r10, r15
mulx rdx, r15, [ rsi + 0x10 ]; x95, x94<- x2 * arg1[2]
adcx r15, rdi
adcx r13, rdx
mov rdi, 0x0 ; moving imm to reg
adcx rcx, rdi
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x40 ], rcx; spilling x106 to mem
mulx rdi, rcx, rax; x8, x7<- x4 * arg1[2]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x48 ], r13; spilling x104 to mem
mov [ rsp + 0x50 ], r15; spilling x102 to mem
mulx r13, r15, r14; x25, x24<- x20 * 0xffffffffffffffff
clc;
adcx r15, r11
adox rcx, rbx
setc bl; spill CF x29 to reg (rbx)
clc;
adcx rbp, r9
mov rbp, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r11, r9, r12; x48, x47<- x1 * arg1[1]
setc dl; spill CF x82 to reg (rdx)
clc;
adcx r9, [ rsp + 0x18 ]
setc bpl; spill CF x52 to reg (rbp)
mov [ rsp + 0x58 ], r10; spilling x100 to mem
movzx r10, byte [ rsp + 0x10 ]; load byte memx36 to register64
clc;
mov [ rsp + 0x60 ], r11; spilling x48 to mem
mov r11, -0x1 ; moving imm to reg
adcx r10, r11; loading flag
adcx rcx, r15
setc r10b; spill CF x38 to reg (r10)
movzx r15, byte [ rsp + 0x38 ]; load byte memx59 to register64
clc;
adcx r15, r11; loading flag
adcx rcx, r9
setc r15b; spill CF x61 to reg (r15)
clc;
movzx rdx, dl
adcx rdx, r11; loading flag
adcx rcx, [ rsp + 0x8 ]
setc dl; spill CF x84 to reg (rdx)
clc;
adcx r8, rcx
mov r9b, dl; preserving value of x84 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx rax, rcx, rax; x6, x5<- x4 * arg1[3]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov byte [ rsp + 0x68 ], r9b; spilling byte x84 to mem
mulx r11, r9, r8; _, x117<- x107 * 0xffffffffffffffff
mov r11, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov byte [ rsp + 0x70 ], r15b; spilling byte x61 to mem
mov [ rsp + 0x78 ], rax; spilling x6 to mem
mulx r15, rax, r12; x46, x45<- x1 * arg1[2]
mov rdx, 0xffffffff ; moving imm to reg
mulx r14, r11, r14; x23, x22<- x20 * 0xffffffff
adox rcx, rdi
setc dil; spill CF x108 to reg (rdi)
clc;
mov rdx, -0x1 ; moving imm to reg
movzx rbx, bl
adcx rbx, rdx; loading flag
adcx r13, r11
seto bl; spill OF x18 to reg (rbx)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r11, -0x1 ; moving imm to reg
movzx r10, r10b
adox r10, r11; loading flag
adox rcx, r13
mov r10, r9; _, copying x117 here, cause x117 is needed in a reg for other than _, namely all: , x119--x120, _--x131, x121--x122, x123--x124, size: 4
setc r13b; spill CF x31 to reg (r13)
clc;
adcx r10, r8
setc r10b; spill CF x131 to reg (r10)
clc;
movzx rbp, bpl
adcx rbp, r11; loading flag
adcx rax, [ rsp + 0x60 ]
movzx rbp, bl; x19, copying x18 here, cause x18 is needed in a reg for other than x19, namely all: , x19, size: 1
mov r8, [ rsp + 0x78 ]; load m64 x6 to register64
lea rbp, [ rbp + r8 ]; r8/64 + m8
setc r8b; spill CF x54 to reg (r8)
movzx rbx, byte [ rsp + 0x70 ]; load byte memx61 to register64
clc;
adcx rbx, r11; loading flag
adcx rcx, rax
seto bl; spill OF x40 to reg (rbx)
movzx rax, byte [ rsp + 0x68 ]; load byte memx84 to register64
dec rdx; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
adox rax, rdx; loading flag
adox rcx, [ rsp + 0x30 ]
movzx r11, r13b; x32, copying x31 here, cause x31 is needed in a reg for other than x32, namely all: , x32, size: 1
lea r11, [ r11 + r14 ]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r12, rax, r12; x44, x43<- x1 * arg1[3]
seto dl; spill OF x86 to reg (rdx)
mov r14, -0x1 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r13, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, r13; loading flag
adox r15, rax
mov r8, 0xffffffff00000000 ; moving imm to reg
xchg rdx, r8; 0xffffffff00000000, swapping with x86, which is currently in rdx
mulx rax, r14, r9; x124, x123<- x117 * 0xffffffff00000000
seto r13b; spill OF x56 to reg (r13)
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rdi, dil
adox rdi, rdx; loading flag
adox rcx, [ rsp + 0x58 ]
movzx rdi, r13b; x57, copying x56 here, cause x56 is needed in a reg for other than x57, namely all: , x57, size: 1
lea rdi, [ rdi + r12 ]
seto r12b; spill OF x110 to reg (r12)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
movzx r10, r10b
adox r10, r13; loading flag
adox rcx, r14
setc r10b; spill CF x63 to reg (r10)
clc;
movzx rbx, bl
adcx rbx, r13; loading flag
adcx rbp, r11
setc bl; spill CF x42 to reg (rbx)
clc;
movzx r10, r10b
adcx r10, r13; loading flag
adcx rbp, r15
movzx r10, bl; x66, copying x42 here, cause x42 is needed in a reg for other than x66, namely all: , x66--x67, size: 1
adcx r10, rdi
setc r11b; spill CF x67 to reg (r11)
clc;
movzx r8, r8b
adcx r8, r13; loading flag
adcx rbp, [ rsp + 0x28 ]
mov r8, 0xffffffff ; moving imm to reg
xchg rdx, r9; x117, swapping with 0x0, which is currently in rdx
mulx r15, r14, r8; x120, x119<- x117 * 0xffffffff
mov rdi, 0xffffffffffffffff ; moving imm to reg
mulx rdx, rbx, rdi; x122, x121<- x117 * 0xffffffffffffffff
mov r9, [ rsp + 0x20 ]; x89, copying x80 here, cause x80 is needed in a reg for other than x89, namely all: , x89--x90, size: 1
adcx r9, r10
movzx r10, r11b; x91, copying x67 here, cause x67 is needed in a reg for other than x91, namely all: , x91, size: 1
mov r13, 0x0 ; moving imm to reg
adcx r10, r13
clc;
adcx rbx, rax
mov rax, [ rsi + 0x18 ]; load m64 x3 to register64
mov r11, rdx; preserving value of x122 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r13, r8, rax; x146, x145<- x3 * arg1[1]
adcx r14, r11
setc dl; spill CF x128 to reg (rdx)
clc;
mov r11, -0x1 ; moving imm to reg
movzx r12, r12b
adcx r12, r11; loading flag
adcx rbp, [ rsp + 0x50 ]
mov r12, [ rsp + 0x48 ]; x113, copying x104 here, cause x104 is needed in a reg for other than x113, namely all: , x113--x114, size: 1
adcx r12, r9
adox rbx, rbp
mov r9, [ rsp + 0x40 ]; x115, copying x106 here, cause x106 is needed in a reg for other than x115, namely all: , x115--x116, size: 1
adcx r9, r10
movzx r10, dl; x129, copying x128 here, cause x128 is needed in a reg for other than x129, namely all: , x129, size: 1
lea r10, [ r10 + r15 ]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r15, rbp, rax; x142, x141<- x3 * arg1[3]
adox r14, r12
mov rdx, rax; x3 to rdx
mulx rax, r12, [ rsi + 0x0 ]; x148, x147<- x3 * arg1[0]
adox r10, r9
seto r9b; spill OF x139 to reg (r9)
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r12, rcx
movzx rcx, r9b; x140, copying x139 here, cause x139 is needed in a reg for other than x140, namely all: , x140, size: 1
adcx rcx, r11
mulx rdx, r9, [ rsi + 0x10 ]; x144, x143<- x3 * arg1[2]
clc;
adcx r8, rax
adcx r9, r13
adcx rbp, rdx
mov rdx, rdi; 0xffffffffffffffff to rdx
mulx r13, rax, r12; _, x166<- x156 * 0xffffffffffffffff
adox r8, rbx
mulx r13, rbx, rax; x171, x170<- x166 * 0xffffffffffffffff
adcx r15, r11
mov r11, 0xffffffff ; moving imm to reg
xchg rdx, r11; 0xffffffff, swapping with 0xffffffffffffffff, which is currently in rdx
mov [ rsp + 0x80 ], r15; spilling x155 to mem
mulx r11, r15, rax; x169, x168<- x166 * 0xffffffff
mov rdx, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x88 ], rcx; spilling x140 to mem
mov [ rsp + 0x90 ], r8; spilling x158 to mem
mulx rcx, r8, rax; x173, x172<- x166 * 0xffffffff00000000
clc;
adcx rbx, rcx
adcx r15, r13
adox r9, r14
mov r14, 0x0 ; moving imm to reg
adcx r11, r14
clc;
adcx rax, r12
adox rbp, r10
mov rax, [ rsp + 0x90 ]; x181, copying x158 here, cause x158 is needed in a reg for other than x181, namely all: , x181--x182, size: 1
adcx rax, r8
mov r10, [ rsp + 0x80 ]; load m64 x155 to register64
mov r12, [ rsp + 0x88 ]; x164, copying x140 here, cause x140 is needed in a reg for other than x164, namely all: , x164--x165, size: 1
adox r12, r10
adcx rbx, r9
setc r13b; spill CF x184 to reg (r13)
seto r10b; spill OF x165 to reg (r10)
mov rcx, rax; x190, copying x181 here, cause x181 is needed in a reg for other than x190, namely all: , x190--x191, x200, size: 2
sub rcx, 0x00000001
mov r8, rbx; x192, copying x183 here, cause x183 is needed in a reg for other than x192, namely all: , x192--x193, x201, size: 2
sbb r8, rdx
dec r14; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r13, r13b
adox r13, r14; loading flag
adox rbp, r15
adox r11, r12
movzx r15, r10b; x189, copying x165 here, cause x165 is needed in a reg for other than x189, namely all: , x189, size: 1
mov r9, 0x0 ; moving imm to reg
adox r15, r9
mov r10, rbp; x194, copying x185 here, cause x185 is needed in a reg for other than x194, namely all: , x202, x194--x195, size: 2
mov r12, 0xffffffffffffffff ; moving imm to reg
sbb r10, r12
mov r13, r11; x196, copying x187 here, cause x187 is needed in a reg for other than x196, namely all: , x203, x196--x197, size: 2
mov r9, 0xffffffff ; moving imm to reg
sbb r13, r9
sbb r15, 0x00000000
cmovc r13, r11; if CF, x203<- x187 (nzVar)
cmovc r8, rbx; if CF, x201<- x183 (nzVar)
mov r15, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r15 + 0x8 ], r8; out1[1] = x201
cmovc r10, rbp; if CF, x202<- x185 (nzVar)
cmovc rcx, rax; if CF, x200<- x181 (nzVar)
mov [ r15 + 0x10 ], r10; out1[2] = x202
mov [ r15 + 0x18 ], r13; out1[3] = x203
mov [ r15 + 0x0 ], rcx; out1[0] = x200
mov rbx, [ rsp + 0x98 ]; restoring from stack
mov rbp, [ rsp + 0xa0 ]; restoring from stack
mov r12, [ rsp + 0xa8 ]; restoring from stack
mov r13, [ rsp + 0xb0 ]; restoring from stack
mov r14, [ rsp + 0xb8 ]; restoring from stack
mov r15, [ rsp + 0xc0 ]; restoring from stack
add rsp, 0xc8 
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; clocked at 3600 MHz
; first cyclecount 69.82, best 55.437086092715234, lastGood 56.18543046357616
; seed 2109513243355895 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 695363 ms / 60000 runs=> 11.589383333333334ms/run
; Time spent for assembling and measureing (initial batch_size=151, initial num_batches=101): 156908 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.22564904948925957
; number reverted permutation/ tried permutation: 25225 / 30023 =84.019%
; number reverted decision/ tried decision: 23446 / 29978 =78.211%