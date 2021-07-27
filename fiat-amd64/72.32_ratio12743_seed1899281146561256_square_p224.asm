SECTION .text
	GLOBAL square_p224
square_p224:
sub rsp, 0x98 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x68 ], rbx; saving to stack
mov [ rsp + 0x70 ], rbp; saving to stack
mov [ rsp + 0x78 ], r12; saving to stack
mov [ rsp + 0x80 ], r13; saving to stack
mov [ rsp + 0x88 ], r14; saving to stack
mov [ rsp + 0x90 ], r15; saving to stack
mov rax, [ rsi + 0x8 ]; load m64 x1 to register64
mov r10, [ rsi + 0x0 ]; load m64 x4 to register64
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r11, rbx, r10; x12, x11<- x4 * arg1[0]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rbp, r12, rax; x50, x49<- x1 * arg1[0]
mov r13, 0xffffffffffffffff ; moving imm to reg
mov rdx, r13; 0xffffffffffffffff to rdx
mulx r13, r14, rbx; _, x20<- x11 * 0xffffffffffffffff
mov r13, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r15, rcx, r10; x10, x9<- x4 * arg1[1]
mov rdx, r14; _, copying x20 here, cause x20 is needed in a reg for other than _, namely all: , x24--x25, x22--x23, _--x34, x26--x27, size: 4
xor r8, r8
adox rdx, rbx
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r9, rbx, r10; x8, x7<- x4 * arg1[2]
adcx rcx, r11
mov rdx, r14; x20 to rdx
mulx r14, r11, r13; x25, x24<- x20 * 0xffffffffffffffff
mov r8, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r13, rdi, r8; x27, x26<- x20 * 0xffffffff00000000
adcx rbx, r15
adox rdi, rcx
seto r15b; spill OF x36 to reg (r15)
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, rdi
mov rdi, rdx; preserving value of x20 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx rcx, r8, rax; x48, x47<- x1 * arg1[1]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x8 ], r14; spilling x25 to mem
mov [ rsp + 0x10 ], r9; spilling x8 to mem
mulx r14, r9, r12; _, x68<- x58 * 0xffffffffffffffff
setc r14b; spill CF x16 to reg (r14)
clc;
adcx r11, r13
setc r13b; spill CF x29 to reg (r13)
clc;
mov rdx, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, rdx; loading flag
adcx rbx, r11
setc r15b; spill CF x38 to reg (r15)
clc;
adcx r8, rbp
mov rdx, rax; x1 to rdx
mulx rax, rbp, [ rsi + 0x10 ]; x46, x45<- x1 * arg1[2]
adox r8, rbx
adcx rbp, rcx
mov rcx, rdx; preserving value of x1 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx r10, r11, r10; x6, x5<- x4 * arg1[3]
mov rdx, 0xffffffff ; moving imm to reg
mulx rdi, rbx, rdi; x23, x22<- x20 * 0xffffffff
mov rdx, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x18 ], rbp; spilling x53 to mem
mov [ rsp + 0x20 ], rax; spilling x46 to mem
mulx rbp, rax, r9; x75, x74<- x68 * 0xffffffff00000000
setc dl; spill CF x54 to reg (rdx)
clc;
mov [ rsp + 0x28 ], rbp; spilling x75 to mem
mov rbp, -0x1 ; moving imm to reg
movzx r14, r14b
adcx r14, rbp; loading flag
adcx r11, [ rsp + 0x10 ]
mov r14, r9; _, copying x68 here, cause x68 is needed in a reg for other than _, namely all: , x70--x71, _--x82, x72--x73, size: 3
seto bpl; spill OF x61 to reg (rbp)
mov byte [ rsp + 0x30 ], dl; spilling byte x54 to mem
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, r12
mov r14, 0xffffffffffffffff ; moving imm to reg
mov rdx, r14; 0xffffffffffffffff to rdx
mulx r14, r12, r9; x73, x72<- x68 * 0xffffffffffffffff
mov rdx, 0x0 ; moving imm to reg
adcx r10, rdx
mov rdx, 0xffffffff ; moving imm to reg
mov byte [ rsp + 0x38 ], bpl; spilling byte x61 to mem
mulx r9, rbp, r9; x71, x70<- x68 * 0xffffffff
clc;
mov rdx, -0x1 ; moving imm to reg
movzx r13, r13b
adcx r13, rdx; loading flag
adcx rbx, [ rsp + 0x8 ]
adox rax, r8
mov r13, 0x0 ; moving imm to reg
adcx rdi, r13
clc;
movzx r15, r15b
adcx r15, rdx; loading flag
adcx r11, rbx
adcx rdi, r10
mov r15, [ rsi + 0x18 ]; load m64 x3 to register64
setc r8b; spill CF x42 to reg (r8)
clc;
adcx r12, [ rsp + 0x28 ]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rcx, r10, rcx; x44, x43<- x1 * arg1[3]
adcx rbp, r14
adcx r9, r13
movzx rdx, byte [ rsp + 0x30 ]; load byte memx54 to register64
clc;
mov r14, -0x1 ; moving imm to reg
adcx rdx, r14; loading flag
adcx r10, [ rsp + 0x20 ]
mov rdx, r15; x3 to rdx
mulx r15, rbx, [ rsi + 0x0 ]; x148, x147<- x3 * arg1[0]
adcx rcx, r13
movzx r13, byte [ rsp + 0x38 ]; load byte memx61 to register64
clc;
adcx r13, r14; loading flag
adcx r11, [ rsp + 0x18 ]
adox r12, r11
adcx r10, rdi
adox rbp, r10
mulx r13, rdi, [ rsi + 0x8 ]; x146, x145<- x3 * arg1[1]
mulx r11, r10, [ rsi + 0x18 ]; x142, x141<- x3 * arg1[3]
movzx r14, r8b; x66, copying x42 here, cause x42 is needed in a reg for other than x66, namely all: , x66--x67, size: 1
adcx r14, rcx
adox r9, r14
mulx rdx, r8, [ rsi + 0x10 ]; x144, x143<- x3 * arg1[2]
mov rcx, [ rsi + 0x10 ]; load m64 x2 to register64
setc r14b; spill CF x67 to reg (r14)
clc;
adcx rdi, r15
movzx r15, r14b; x91, copying x67 here, cause x67 is needed in a reg for other than x91, namely all: , x91, size: 1
mov [ rsp + 0x40 ], rdi; spilling x149 to mem
mov rdi, 0x0 ; moving imm to reg
adox r15, rdi
adcx r8, r13
adcx r10, rdx
adc r11, 0x0
mov rdx, rcx; x2 to rdx
mulx rcx, r13, [ rsi + 0x10 ]; x95, x94<- x2 * arg1[2]
mulx r14, rdi, [ rsi + 0x0 ]; x99, x98<- x2 * arg1[0]
add rdi, rax; could be done better, if r0 has been u8 as well
mov [ rsp + 0x48 ], r11; spilling x155 to mem
mulx rax, r11, [ rsi + 0x8 ]; x97, x96<- x2 * arg1[1]
mov [ rsp + 0x50 ], r10; spilling x153 to mem
mov r10, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rdi; x107, swapping with x2, which is currently in rdx
mov [ rsp + 0x58 ], r8; spilling x151 to mem
mov [ rsp + 0x60 ], rbx; spilling x147 to mem
mulx r8, rbx, r10; _, x117<- x107 * 0xffffffffffffffff
mov r8, rbx; _, copying x117 here, cause x117 is needed in a reg for other than _, namely all: , x119--x120, x123--x124, _--x131, x121--x122, size: 4
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, rdx
setc r8b; spill CF x108 to reg (r8)
clc;
adcx r11, r14
adcx r13, rax
seto r14b; spill OF x131 to reg (r14)
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, rdx; loading flag
adox r12, r11
mov r8, 0xffffffff00000000 ; moving imm to reg
mov rdx, rbx; x117 to rdx
mulx rbx, rax, r8; x124, x123<- x117 * 0xffffffff00000000
mov r11, 0xffffffff ; moving imm to reg
mulx r10, r8, r11; x120, x119<- x117 * 0xffffffff
adox r13, rbp
seto bpl; spill OF x112 to reg (rbp)
mov r11, 0x0 ; moving imm to reg
dec r11; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r14, r14b
adox r14, r11; loading flag
adox r12, rax
mov r14, rdx; preserving value of x117 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx rdi, rax, rdi; x93, x92<- x2 * arg1[3]
adcx rax, rcx
mov rdx, 0xffffffffffffffff ; moving imm to reg
mulx r14, rcx, r14; x122, x121<- x117 * 0xffffffffffffffff
mov r11, 0x0 ; moving imm to reg
adcx rdi, r11
clc;
adcx rcx, rbx
adcx r8, r14
adcx r10, r11
clc;
mov rbx, -0x1 ; moving imm to reg
movzx rbp, bpl
adcx rbp, rbx; loading flag
adcx r9, rax
adcx rdi, r15
adox rcx, r13
setc r15b; spill CF x116 to reg (r15)
clc;
adcx r12, [ rsp + 0x60 ]
mov rbp, [ rsp + 0x40 ]; x158, copying x149 here, cause x149 is needed in a reg for other than x158, namely all: , x158--x159, size: 1
adcx rbp, rcx
adox r8, r9
mulx r13, rax, r12; _, x166<- x156 * 0xffffffffffffffff
adox r10, rdi
mov r13, [ rsp + 0x58 ]; x160, copying x151 here, cause x151 is needed in a reg for other than x160, namely all: , x160--x161, size: 1
adcx r13, r8
movzx r14, r15b; x140, copying x116 here, cause x116 is needed in a reg for other than x140, namely all: , x140, size: 1
adox r14, r11
mov r9, 0xffffffff00000000 ; moving imm to reg
xchg rdx, rax; x166, swapping with 0xffffffffffffffff, which is currently in rdx
mulx r15, rdi, r9; x173, x172<- x166 * 0xffffffff00000000
mulx rcx, r8, rax; x171, x170<- x166 * 0xffffffffffffffff
mov r11, [ rsp + 0x50 ]; x162, copying x153 here, cause x153 is needed in a reg for other than x162, namely all: , x162--x163, size: 1
adcx r11, r10
mov r10, rdx; _, copying x166 here, cause x166 is needed in a reg for other than _, namely all: , _--x180, x168--x169, size: 2
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r10, r12
mov r10, [ rsp + 0x48 ]; x164, copying x155 here, cause x155 is needed in a reg for other than x164, namely all: , x164--x165, size: 1
adcx r10, r14
setc r12b; spill CF x165 to reg (r12)
clc;
adcx r8, r15
mov r14, 0xffffffff ; moving imm to reg
mulx rdx, r15, r14; x169, x168<- x166 * 0xffffffff
adox rdi, rbp
adcx r15, rcx
adox r8, r13
adcx rdx, rbx
adox r15, r11
adox rdx, r10
movzx rbp, r12b; x189, copying x165 here, cause x165 is needed in a reg for other than x189, namely all: , x189, size: 1
adox rbp, rbx
mov r13, rdi; x190, copying x181 here, cause x181 is needed in a reg for other than x190, namely all: , x190--x191, x200, size: 2
sub r13, 0x00000001
mov rcx, r8; x192, copying x183 here, cause x183 is needed in a reg for other than x192, namely all: , x201, x192--x193, size: 2
sbb rcx, r9
mov r11, r15; x194, copying x185 here, cause x185 is needed in a reg for other than x194, namely all: , x194--x195, x202, size: 2
sbb r11, rax
mov r12, rdx; x196, copying x187 here, cause x187 is needed in a reg for other than x196, namely all: , x203, x196--x197, size: 2
sbb r12, r14
sbb rbp, 0x00000000
cmovc r11, r15; if CF, x202<- x185 (nzVar)
cmovc rcx, r8; if CF, x201<- x183 (nzVar)
mov rbp, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rbp + 0x8 ], rcx; out1[1] = x201
cmovc r13, rdi; if CF, x200<- x181 (nzVar)
cmovc r12, rdx; if CF, x203<- x187 (nzVar)
mov [ rbp + 0x10 ], r11; out1[2] = x202
mov [ rbp + 0x0 ], r13; out1[0] = x200
mov [ rbp + 0x18 ], r12; out1[3] = x203
mov rbx, [ rsp + 0x68 ]; restoring from stack
mov rbp, [ rsp + 0x70 ]; restoring from stack
mov r12, [ rsp + 0x78 ]; restoring from stack
mov r13, [ rsp + 0x80 ]; restoring from stack
mov r14, [ rsp + 0x88 ]; restoring from stack
mov r15, [ rsp + 0x90 ]; restoring from stack
add rsp, 0x98 
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; clocked at 4739 MHz
; first cyclecount 93.41, best 70.09174311926606, lastGood 72.3177570093458
; seed 1899281146561256 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 726171 ms / 60000 runs=> 12.10285ms/run
; Time spent for assembling and measureing (initial batch_size=107, initial num_batches=101): 110736 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.1524930078452596
; number reverted permutation/ tried permutation: 22797 / 30002 =75.985%
; number reverted decision/ tried decision: 22785 / 29999 =75.953%