SECTION .text
	GLOBAL square_p224
square_p224:
sub rsp, 0xa8 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x78 ], rbx; saving to stack
mov [ rsp + 0x80 ], rbp; saving to stack
mov [ rsp + 0x88 ], r12; saving to stack
mov [ rsp + 0x90 ], r13; saving to stack
mov [ rsp + 0x98 ], r14; saving to stack
mov [ rsp + 0xa0 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x4 to register64
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r10, r11, rax; x8, x7<- x4 * arg1[2]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rbx, rbp, rax; x12, x11<- x4 * arg1[0]
mov r12, 0xffffffffffffffff ; moving imm to reg
mov rdx, rbp; x11 to rdx
mulx rbp, r13, r12; _, x20<- x11 * 0xffffffffffffffff
mov rbp, [ rsi + 0x8 ]; load m64 x1 to register64
mov r14, rdx; preserving value of x11 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r15, rcx, rax; x10, x9<- x4 * arg1[1]
mov rdx, r13; _, copying x20 here, cause x20 is needed in a reg for other than _, namely all: , _--x34, x22--x23, x26--x27, x24--x25, size: 4
xor r8, r8
adox rdx, r14
mov rdx, rbp; x1 to rdx
mulx rbp, r9, [ rsi + 0x0 ]; x50, x49<- x1 * arg1[0]
adcx rcx, rbx
mov rbx, 0xffffffff00000000 ; moving imm to reg
xchg rdx, r13; x20, swapping with x1, which is currently in rdx
mulx r14, r8, rbx; x27, x26<- x20 * 0xffffffff00000000
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx rbx, rdi, r12; x25, x24<- x20 * 0xffffffffffffffff
xchg rdx, rax; x4, swapping with x20, which is currently in rdx
mulx rdx, r12, [ rsi + 0x18 ]; x6, x5<- x4 * arg1[3]
mov [ rsp + 0x8 ], rdx; spilling x6 to mem
mov rdx, [ rsi + 0x10 ]; load m64 x2 to register64
adcx r11, r15
adox r8, rcx
setc r15b; spill CF x16 to reg (r15)
clc;
adcx r9, r8
mov rcx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r9; x58, swapping with x2, which is currently in rdx
mov [ rsp + 0x10 ], r9; spilling x2 to mem
mulx r8, r9, rcx; _, x68<- x58 * 0xffffffffffffffff
mov r8, r9; _, copying x68 here, cause x68 is needed in a reg for other than _, namely all: , x72--x73, _--x82, x70--x71, x74--x75, size: 4
setc cl; spill CF x59 to reg (rcx)
clc;
adcx r8, rdx
setc r8b; spill CF x82 to reg (r8)
clc;
adcx rdi, r14
mov r14, 0xffffffff00000000 ; moving imm to reg
mov rdx, r14; 0xffffffff00000000 to rdx
mov byte [ rsp + 0x18 ], r8b; spilling byte x82 to mem
mulx r14, r8, r9; x75, x74<- x68 * 0xffffffff00000000
adox rdi, r11
mov r11, 0xffffffff ; moving imm to reg
xchg rdx, rax; x20, swapping with 0xffffffff00000000, which is currently in rdx
mulx rdx, rax, r11; x23, x22<- x20 * 0xffffffff
adcx rax, rbx
mov rbx, 0x0 ; moving imm to reg
adcx rdx, rbx
mov rbx, rdx; preserving value of x32 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x20 ], r14; spilling x75 to mem
mulx r11, r14, r13; x48, x47<- x1 * arg1[1]
clc;
mov rdx, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, rdx; loading flag
adcx r10, r12
setc r12b; spill CF x18 to reg (r12)
clc;
adcx r14, rbp
seto bpl; spill OF x38 to reg (rbp)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r15; loading flag
adox rdi, r14
mov rcx, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r14, r15, r13; x46, x45<- x1 * arg1[2]
seto dl; spill OF x61 to reg (rdx)
dec rcx; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx rbp, bpl
adox rbp, rcx; loading flag
adox r10, rax
adcx r15, r11
movzx rbp, r12b; x19, copying x18 here, cause x18 is needed in a reg for other than x19, namely all: , x19, size: 1
mov rax, [ rsp + 0x8 ]; load m64 x6 to register64
lea rbp, [ rbp + rax ]; r8/64 + m8
setc al; spill CF x54 to reg (rax)
movzx r11, byte [ rsp + 0x18 ]; load byte memx82 to register64
clc;
adcx r11, rcx; loading flag
adcx rdi, r8
mov r11, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r9; x68, swapping with x61, which is currently in rdx
mulx r8, r12, r11; x73, x72<- x68 * 0xffffffffffffffff
adox rbx, rbp
seto bpl; spill OF x42 to reg (rbp)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rcx, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, rcx; loading flag
adox r10, r15
seto r9b; spill OF x63 to reg (r9)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r12, [ rsp + 0x20 ]
adcx r12, r10
mov r15, 0xffffffff ; moving imm to reg
mulx rdx, r10, r15; x71, x70<- x68 * 0xffffffff
mov rcx, rdx; preserving value of x71 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx r13, r15, r13; x44, x43<- x1 * arg1[3]
adox r10, r8
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r8, r11, [ rsp + 0x10 ]; x93, x92<- x2 * arg1[3]
mov rdx, 0x0 ; moving imm to reg
adox rcx, rdx
dec rdx; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx rax, al
adox rax, rdx; loading flag
adox r14, r15
mov rdx, [ rsp + 0x10 ]; x2 to rdx
mulx rax, r15, [ rsi + 0x8 ]; x97, x96<- x2 * arg1[1]
mov [ rsp + 0x28 ], r8; spilling x93 to mem
mov r8, 0x0 ; moving imm to reg
adox r13, r8
dec r8; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r9, r9b
adox r9, r8; loading flag
adox rbx, r14
mulx r9, r14, [ rsi + 0x0 ]; x99, x98<- x2 * arg1[0]
movzx r8, bpl; x66, copying x42 here, cause x42 is needed in a reg for other than x66, namely all: , x66--x67, size: 1
adox r8, r13
adcx r10, rbx
adcx rcx, r8
mulx rdx, rbp, [ rsi + 0x10 ]; x95, x94<- x2 * arg1[2]
mov r13, [ rsi + 0x18 ]; load m64 x3 to register64
seto bl; spill OF x91 to reg (rbx)
adc bl, 0x0
movzx rbx, bl
adox r15, r9
adox rbp, rax
adcx r14, rdi
xchg rdx, r13; x3, swapping with x95, which is currently in rdx
mulx rdi, rax, [ rsi + 0x8 ]; x146, x145<- x3 * arg1[1]
adcx r15, r12
mov r12, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r14; x107, swapping with x3, which is currently in rdx
mulx r9, r8, r12; _, x117<- x107 * 0xffffffffffffffff
mov r9, 0xffffffff00000000 ; moving imm to reg
xchg rdx, r9; 0xffffffff00000000, swapping with x107, which is currently in rdx
mov [ rsp + 0x30 ], rdi; spilling x146 to mem
mulx r12, rdi, r8; x124, x123<- x117 * 0xffffffff00000000
adox r11, r13
mov r13, [ rsp + 0x28 ]; x106, copying x93 here, cause x93 is needed in a reg for other than x106, namely all: , x106, size: 1
mov rdx, 0x0 ; moving imm to reg
adox r13, rdx
mov [ rsp + 0x38 ], r13; spilling x106 to mem
mov r13, r8; _, copying x117 here, cause x117 is needed in a reg for other than _, namely all: , _--x131, x119--x120, x121--x122, size: 3
mov byte [ rsp + 0x40 ], bl; spilling byte x91 to mem
mov rbx, -0x3 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r13, r9
mov r13, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r8; x117, swapping with 0x0, which is currently in rdx
mulx r9, r8, r13; x122, x121<- x117 * 0xffffffffffffffff
mov rbx, rdx; preserving value of x117 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x48 ], r11; spilling x104 to mem
mulx r13, r11, r14; x148, x147<- x3 * arg1[0]
adox rdi, r15
adcx rbp, r10
mov rdx, 0xffffffff ; moving imm to reg
mulx rbx, r10, rbx; x120, x119<- x117 * 0xffffffff
setc r15b; spill CF x112 to reg (r15)
clc;
adcx r8, r12
setc r12b; spill CF x126 to reg (r12)
clc;
adcx rax, r13
setc r13b; spill CF x150 to reg (r13)
clc;
adcx r11, rdi
mov rdi, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rdi; 0xffffffffffffffff, swapping with 0xffffffff, which is currently in rdx
mov byte [ rsp + 0x50 ], r13b; spilling byte x150 to mem
mulx rdi, r13, r11; _, x166<- x156 * 0xffffffffffffffff
adox r8, rbp
mov rbp, 0xffffffff00000000 ; moving imm to reg
xchg rdx, r13; x166, swapping with 0xffffffffffffffff, which is currently in rdx
mov [ rsp + 0x58 ], rcx; spilling x89 to mem
mulx r13, rcx, rbp; x173, x172<- x166 * 0xffffffff00000000
adcx rax, r8
mov r8, rdx; _, copying x166 here, cause x166 is needed in a reg for other than _, namely all: , x168--x169, x170--x171, _--x180, size: 3
setc bpl; spill CF x159 to reg (rbp)
clc;
adcx r8, r11
adcx rcx, rax
setc r8b; spill CF x182 to reg (r8)
clc;
mov r11, -0x1 ; moving imm to reg
movzx r12, r12b
adcx r12, r11; loading flag
adcx r9, r10
mov r10, 0x0 ; moving imm to reg
adcx rbx, r10
mov r12, [ rsp + 0x48 ]; load m64 x104 to register64
clc;
movzx r15, r15b
adcx r15, r11; loading flag
adcx r12, [ rsp + 0x58 ]
mov r15, 0xffffffffffffffff ; moving imm to reg
mulx rax, r10, r15; x171, x170<- x166 * 0xffffffffffffffff
mov r11, rdx; preserving value of x166 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x60 ], rax; spilling x171 to mem
mulx r15, rax, r14; x142, x141<- x3 * arg1[3]
adox r9, r12
mov rdx, [ rsp + 0x38 ]; load m64 x106 to register64
movzx r12, byte [ rsp + 0x40 ]; x115, copying x91 here, cause x91 is needed in a reg for other than x115, namely all: , x115--x116, size: 1
adcx r12, rdx
setc dl; spill CF x116 to reg (rdx)
clc;
adcx r10, r13
adox rbx, r12
xchg rdx, r14; x3, swapping with x116, which is currently in rdx
mulx rdx, r13, [ rsi + 0x10 ]; x144, x143<- x3 * arg1[2]
setc r12b; spill CF x175 to reg (r12)
mov [ rsp + 0x68 ], rbx; spilling x138 to mem
movzx rbx, byte [ rsp + 0x50 ]; load byte memx150 to register64
clc;
mov [ rsp + 0x70 ], r15; spilling x142 to mem
mov r15, -0x1 ; moving imm to reg
adcx rbx, r15; loading flag
adcx r13, [ rsp + 0x30 ]
movzx rbx, r14b; x140, copying x116 here, cause x116 is needed in a reg for other than x140, namely all: , x140, size: 1
mov r15, 0x0 ; moving imm to reg
adox rbx, r15
adcx rax, rdx
dec r15; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx rbp, bpl
adox rbp, r15; loading flag
adox r9, r13
setc bpl; spill CF x154 to reg (rbp)
seto r14b; spill OF x161 to reg (r14)
mov rdx, rcx; x190, copying x181 here, cause x181 is needed in a reg for other than x190, namely all: , x190--x191, x200, size: 2
sub rdx, 0x00000001
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, r13; loading flag
adox r9, r10
seto r8b; spill OF x184 to reg (r8)
mov r10, r9; x192, copying x183 here, cause x183 is needed in a reg for other than x192, namely all: , x192--x193, x201, size: 2
mov r15, 0xffffffff00000000 ; moving imm to reg
sbb r10, r15
movzx r13, bpl; x155, copying x154 here, cause x154 is needed in a reg for other than x155, namely all: , x155, size: 1
mov r15, [ rsp + 0x70 ]; load m64 x142 to register64
lea r13, [ r13 + r15 ]; r8/64 + m8
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, rbp; loading flag
adox rax, [ rsp + 0x68 ]
adox r13, rbx
mov rbx, 0xffffffff ; moving imm to reg
xchg rdx, rbx; 0xffffffff, swapping with x190, which is currently in rdx
mulx r11, r14, r11; x169, x168<- x166 * 0xffffffff
seto r15b; spill OF x165 to reg (r15)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, rbp; loading flag
adox r14, [ rsp + 0x60 ]
mov r12, 0x0 ; moving imm to reg
adox r11, r12
dec r12; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx r8, r8b
adox r8, r12; loading flag
adox rax, r14
adox r11, r13
movzx rbp, r15b; x189, copying x165 here, cause x165 is needed in a reg for other than x189, namely all: , x189, size: 1
mov r8, 0x0 ; moving imm to reg
adox rbp, r8
mov r15, rax; x194, copying x185 here, cause x185 is needed in a reg for other than x194, namely all: , x202, x194--x195, size: 2
mov r13, 0xffffffffffffffff ; moving imm to reg
sbb r15, r13
mov r14, r11; x196, copying x187 here, cause x187 is needed in a reg for other than x196, namely all: , x196--x197, x203, size: 2
sbb r14, rdx
sbb rbp, 0x00000000
cmovc r14, r11; if CF, x203<- x187 (nzVar)
cmovc rbx, rcx; if CF, x200<- x181 (nzVar)
mov rbp, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rbp + 0x0 ], rbx; out1[0] = x200
mov [ rbp + 0x18 ], r14; out1[3] = x203
cmovc r10, r9; if CF, x201<- x183 (nzVar)
cmovc r15, rax; if CF, x202<- x185 (nzVar)
mov [ rbp + 0x10 ], r15; out1[2] = x202
mov [ rbp + 0x8 ], r10; out1[1] = x201
mov rbx, [ rsp + 0x78 ]; restoring from stack
mov rbp, [ rsp + 0x80 ]; restoring from stack
mov r12, [ rsp + 0x88 ]; restoring from stack
mov r13, [ rsp + 0x90 ]; restoring from stack
mov r14, [ rsp + 0x98 ]; restoring from stack
mov r15, [ rsp + 0xa0 ]; restoring from stack
add rsp, 0xa8 
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; clocked at 2200 MHz
; first cyclecount 124.26, best 92.46666666666667, lastGood 93.73333333333333
; seed 3777690670788846 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1057111 ms / 60000 runs=> 17.618516666666668ms/run
; Time spent for assembling and measureing (initial batch_size=91, initial num_batches=101): 198440 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.18771917045608266
; number reverted permutation/ tried permutation: 25769 / 29825 =86.401%
; number reverted decision/ tried decision: 21683 / 30176 =71.855%