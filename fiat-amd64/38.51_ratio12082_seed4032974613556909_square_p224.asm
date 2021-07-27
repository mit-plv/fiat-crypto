SECTION .text
	GLOBAL square_p224
square_p224:
sub rsp, 0x88 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x58 ], rbx; saving to stack
mov [ rsp + 0x60 ], rbp; saving to stack
mov [ rsp + 0x68 ], r12; saving to stack
mov [ rsp + 0x70 ], r13; saving to stack
mov [ rsp + 0x78 ], r14; saving to stack
mov [ rsp + 0x80 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x4 to register64
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r10, r11, rax; x12, x11<- x4 * arg1[0]
mov rbx, 0xffffffffffffffff ; moving imm to reg
mov rdx, rbx; 0xffffffffffffffff to rdx
mulx rbx, rbp, r11; _, x20<- x11 * 0xffffffffffffffff
mov rbx, 0xffffffff00000000 ; moving imm to reg
xchg rdx, rbp; x20, swapping with 0xffffffffffffffff, which is currently in rdx
mulx r12, r13, rbx; x27, x26<- x20 * 0xffffffff00000000
mov r14, 0xffffffff ; moving imm to reg
mulx r15, rcx, r14; x23, x22<- x20 * 0xffffffff
mulx r8, r9, rbp; x25, x24<- x20 * 0xffffffffffffffff
add r9, r12; could be done better, if r0 has been u8 as well
mov r12, [ rsi + 0x8 ]; load m64 x1 to register64
adcx rcx, r8
adc r15, 0x0
mov r8, rdx; preserving value of x20 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx rbx, rbp, r12; x50, x49<- x1 * arg1[0]
mov rdx, r12; x1 to rdx
mulx r12, r14, [ rsi + 0x18 ]; x44, x43<- x1 * arg1[3]
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov [ rsp + 0x8 ], r15; spilling x32 to mem
mulx rdi, r15, [ rsi + 0x8 ]; x48, x47<- x1 * arg1[1]
mov [ rsp + 0x10 ], rcx; spilling x30 to mem
xor rcx, rcx
adox r15, rbx
adcx r8, r11
mulx rdx, r8, [ rsi + 0x10 ]; x46, x45<- x1 * arg1[2]
adox r8, rdi
adox r14, rdx
adox r12, rcx
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r11, rbx, rax; x10, x9<- x4 * arg1[1]
mov rdx, -0x3 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbx, r10
adcx r13, rbx
setc r10b; spill CF x36 to reg (r10)
clc;
adcx rbp, r13
mov rdi, 0xffffffffffffffff ; moving imm to reg
mov rdx, rbp; x58 to rdx
mulx rbp, rbx, rdi; _, x68<- x58 * 0xffffffffffffffff
mov rbp, rbx; _, copying x68 here, cause x68 is needed in a reg for other than _, namely all: , _--x82, x72--x73, x70--x71, x74--x75, size: 4
setc r13b; spill CF x59 to reg (r13)
clc;
adcx rbp, rdx
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rbp, rcx, rax; x8, x7<- x4 * arg1[2]
adox rcx, r11
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rax, r11, rax; x6, x5<- x4 * arg1[3]
mov rdx, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x18 ], r12; spilling x57 to mem
mulx rdi, r12, rbx; x75, x74<- x68 * 0xffffffff00000000
seto dl; spill OF x16 to reg (rdx)
mov [ rsp + 0x20 ], rdi; spilling x75 to mem
mov rdi, 0x0 ; moving imm to reg
dec rdi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r10, r10b
adox r10, rdi; loading flag
adox rcx, r9
seto r9b; spill OF x38 to reg (r9)
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r10, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, r10; loading flag
adox rcx, r15
adcx r12, rcx
setc r15b; spill CF x84 to reg (r15)
clc;
movzx rdx, dl
adcx rdx, r10; loading flag
adcx rbp, r11
adcx rax, rdi
mov r13, 0xffffffff ; moving imm to reg
mov rdx, rbx; x68 to rdx
mulx rbx, r11, r13; x71, x70<- x68 * 0xffffffff
clc;
movzx r9, r9b
adcx r9, r10; loading flag
adcx rbp, [ rsp + 0x10 ]
mov r9, [ rsp + 0x8 ]; x41, copying x32 here, cause x32 is needed in a reg for other than x41, namely all: , x41--x42, size: 1
adcx r9, rax
mov rcx, 0xffffffffffffffff ; moving imm to reg
mulx rdx, rax, rcx; x73, x72<- x68 * 0xffffffffffffffff
adox r8, rbp
adox r14, r9
mov rbp, [ rsi + 0x10 ]; load m64 x2 to register64
setc r9b; spill CF x42 to reg (r9)
clc;
adcx rax, [ rsp + 0x20 ]
adcx r11, rdx
adcx rbx, rdi
movzx r9, r9b
mov rdx, [ rsp + 0x18 ]; x66, copying x57 here, cause x57 is needed in a reg for other than x66, namely all: , x66--x67, size: 1
adox rdx, r9
clc;
movzx r15, r15b
adcx r15, r10; loading flag
adcx r8, rax
adcx r11, r14
adcx rbx, rdx
seto r15b; spill OF x91 to reg (r15)
adc r15b, 0x0
movzx r15, r15b
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r9, r14, rbp; x99, x98<- x2 * arg1[0]
adox r14, r12
mov rdx, rcx; 0xffffffffffffffff to rdx
mulx rcx, r12, r14; _, x117<- x107 * 0xffffffffffffffff
mov rcx, [ rsi + 0x18 ]; load m64 x3 to register64
mov rax, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx rdi, r10, rcx; x146, x145<- x3 * arg1[1]
mov rdx, 0xffffffff00000000 ; moving imm to reg
mulx r13, rax, r12; x124, x123<- x117 * 0xffffffff00000000
mov rdx, 0xffffffff ; moving imm to reg
mov byte [ rsp + 0x28 ], r15b; spilling byte x91 to mem
mov [ rsp + 0x30 ], rax; spilling x123 to mem
mulx r15, rax, r12; x120, x119<- x117 * 0xffffffff
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x38 ], rbx; spilling x89 to mem
mov [ rsp + 0x40 ], r11; spilling x87 to mem
mulx rbx, r11, r12; x122, x121<- x117 * 0xffffffffffffffff
adcx r11, r13
xchg rdx, rcx; x3, swapping with 0xffffffffffffffff, which is currently in rdx
mulx r13, rcx, [ rsi + 0x0 ]; x148, x147<- x3 * arg1[0]
mov [ rsp + 0x48 ], rcx; spilling x147 to mem
mov [ rsp + 0x50 ], r11; spilling x125 to mem
mulx rcx, r11, [ rsi + 0x18 ]; x142, x141<- x3 * arg1[3]
adcx rax, rbx
mov rbx, 0x0 ; moving imm to reg
adcx r15, rbx
mulx rdx, rbx, [ rsi + 0x10 ]; x144, x143<- x3 * arg1[2]
clc;
adcx r10, r13
adcx rbx, rdi
adcx r11, rdx
mov rdi, 0x0 ; moving imm to reg
adcx rcx, rdi
mov rdx, rbp; x2 to rdx
mulx rbp, r13, [ rsi + 0x8 ]; x97, x96<- x2 * arg1[1]
clc;
adcx r12, r14
setc r12b; spill CF x131 to reg (r12)
clc;
adcx r13, r9
mulx r9, r14, [ rsi + 0x10 ]; x95, x94<- x2 * arg1[2]
adox r13, r8
adcx r14, rbp
mulx rdx, r8, [ rsi + 0x18 ]; x93, x92<- x2 * arg1[3]
adcx r8, r9
mov rbp, [ rsp + 0x40 ]; x111, copying x87 here, cause x87 is needed in a reg for other than x111, namely all: , x111--x112, size: 1
adox rbp, r14
mov r9, [ rsp + 0x38 ]; x113, copying x89 here, cause x89 is needed in a reg for other than x113, namely all: , x113--x114, size: 1
adox r9, r8
adcx rdx, rdi
clc;
mov r14, -0x1 ; moving imm to reg
movzx r12, r12b
adcx r12, r14; loading flag
adcx r13, [ rsp + 0x30 ]
mov r12, [ rsp + 0x50 ]; x134, copying x125 here, cause x125 is needed in a reg for other than x134, namely all: , x134--x135, size: 1
adcx r12, rbp
movzx r8, byte [ rsp + 0x28 ]; x115, copying x91 here, cause x91 is needed in a reg for other than x115, namely all: , x115--x116, size: 1
adox r8, rdx
adcx rax, r9
adcx r15, r8
setc bpl; spill CF x139 to reg (rbp)
clc;
adcx r13, [ rsp + 0x48 ]
movzx r9, bpl; x140, copying x139 here, cause x139 is needed in a reg for other than x140, namely all: , x140, size: 1
adox r9, rdi
mov rdx, 0xffffffffffffffff ; moving imm to reg
mulx r8, rbp, r13; _, x166<- x156 * 0xffffffffffffffff
mulx r8, rdi, rbp; x171, x170<- x166 * 0xffffffffffffffff
adcx r10, r12
mov r12, rbp; _, copying x166 here, cause x166 is needed in a reg for other than _, namely all: , x168--x169, _--x180, x172--x173, size: 3
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r12, r13
mov r12, 0xffffffff00000000 ; moving imm to reg
xchg rdx, rbp; x166, swapping with 0xffffffffffffffff, which is currently in rdx
mulx r13, r14, r12; x173, x172<- x166 * 0xffffffff00000000
adox r14, r10
adcx rbx, rax
adcx r11, r15
setc al; spill CF x163 to reg (rax)
clc;
adcx rdi, r13
adox rdi, rbx
setc r15b; spill CF x175 to reg (r15)
seto r10b; spill OF x184 to reg (r10)
mov r13, r14; x190, copying x181 here, cause x181 is needed in a reg for other than x190, namely all: , x190--x191, x200, size: 2
sub r13, 0x00000001
mov rbx, rdi; x192, copying x183 here, cause x183 is needed in a reg for other than x192, namely all: , x192--x193, x201, size: 2
sbb rbx, r12
mov r12, 0xffffffff ; moving imm to reg
mulx rdx, rbp, r12; x169, x168<- x166 * 0xffffffff
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r15, r15b
adox r15, r12; loading flag
adox r8, rbp
mov r15, 0x0 ; moving imm to reg
adox rdx, r15
dec r15; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx rax, al
adox rax, r15; loading flag
adox r9, rcx
seto r12b; spill OF x165 to reg (r12)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rcx, -0x1 ; moving imm to reg
movzx r10, r10b
adox r10, rcx; loading flag
adox r11, r8
adox rdx, r9
movzx rax, r12b; x189, copying x165 here, cause x165 is needed in a reg for other than x189, namely all: , x189, size: 1
adox rax, r15
mov r10, r11; x194, copying x185 here, cause x185 is needed in a reg for other than x194, namely all: , x202, x194--x195, size: 2
mov rbp, 0xffffffffffffffff ; moving imm to reg
sbb r10, rbp
mov r8, rdx; x196, copying x187 here, cause x187 is needed in a reg for other than x196, namely all: , x203, x196--x197, size: 2
mov r9, 0xffffffff ; moving imm to reg
sbb r8, r9
sbb rax, 0x00000000
cmovc rbx, rdi; if CF, x201<- x183 (nzVar)
cmovc r13, r14; if CF, x200<- x181 (nzVar)
mov rax, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rax + 0x8 ], rbx; out1[1] = x201
cmovc r8, rdx; if CF, x203<- x187 (nzVar)
cmovc r10, r11; if CF, x202<- x185 (nzVar)
mov [ rax + 0x10 ], r10; out1[2] = x202
mov [ rax + 0x0 ], r13; out1[0] = x200
mov [ rax + 0x18 ], r8; out1[3] = x203
mov rbx, [ rsp + 0x58 ]; restoring from stack
mov rbp, [ rsp + 0x60 ]; restoring from stack
mov r12, [ rsp + 0x68 ]; restoring from stack
mov r13, [ rsp + 0x70 ]; restoring from stack
mov r14, [ rsp + 0x78 ]; restoring from stack
mov r15, [ rsp + 0x80 ]; restoring from stack
add rsp, 0x88 
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; clocked at 1600 MHz
; first cyclecount 48.82, best 38.055813953488375, lastGood 38.50697674418605
; seed 4032974613556909 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1142090 ms / 60000 runs=> 19.034833333333335ms/run
; Time spent for assembling and measureing (initial batch_size=215, initial num_batches=101): 406329 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.3557766901032318
; number reverted permutation/ tried permutation: 26715 / 29849 =89.500%
; number reverted decision/ tried decision: 26604 / 30152 =88.233%