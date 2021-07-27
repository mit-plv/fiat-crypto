SECTION .text
	GLOBAL mul_p224
mul_p224:
sub rsp, 0xf0 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0xc0 ], rbx; saving to stack
mov [ rsp + 0xc8 ], rbp; saving to stack
mov [ rsp + 0xd0 ], r12; saving to stack
mov [ rsp + 0xd8 ], r13; saving to stack
mov [ rsp + 0xe0 ], r14; saving to stack
mov [ rsp + 0xe8 ], r15; saving to stack
mov rax, [ rsi + 0x8 ]; load m64 x1 to register64
mov r10, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x10 ]; saving arg2[2] in rdx.
mulx r11, rbx, rax; x46, x45<- x1 * arg2[2]
mov rbp, [ rsi + 0x0 ]; load m64 x4 to register64
mov rdx, rax; x1 to rdx
mulx rax, r12, [ r10 + 0x8 ]; x48, x47<- x1 * arg2[1]
mulx r13, r14, [ r10 + 0x18 ]; x44, x43<- x1 * arg2[3]
mulx rdx, r15, [ r10 + 0x0 ]; x50, x49<- x1 * arg2[0]
add r12, rdx; could be done better, if r0 has been u8 as well
adcx rbx, rax
mov rdx, [ r10 + 0x0 ]; arg2[0] to rdx
mulx rcx, r8, rbp; x12, x11<- x4 * arg2[0]
adcx r14, r11
mov r9, 0xffffffffffffffff ; moving imm to reg
mov rdx, r8; x11 to rdx
mulx r8, r11, r9; _, x20<- x11 * 0xffffffffffffffff
adc r13, 0x0
mov r8, r11; _, copying x20 here, cause x20 is needed in a reg for other than _, namely all: , x26--x27, _--x34, x22--x23, x24--x25, size: 4
xor rax, rax
adox r8, rdx
mov rdx, [ r10 + 0x8 ]; arg2[1] to rdx
mulx r8, rax, rbp; x10, x9<- x4 * arg2[1]
adcx rax, rcx
mov rcx, 0xffffffff00000000 ; moving imm to reg
mov rdx, rcx; 0xffffffff00000000 to rdx
mulx rcx, r9, r11; x27, x26<- x20 * 0xffffffff00000000
adox r9, rax
seto al; spill OF x36 to reg (rax)
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, r9
mov r9, 0xffffffffffffffff ; moving imm to reg
mov rdx, r9; 0xffffffffffffffff to rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r9, rdi, r15; _, x68<- x58 * 0xffffffffffffffff
mov r9, [ rsi + 0x10 ]; load m64 x2 to register64
mov rdx, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x8 ], r13; spilling x57 to mem
mov [ rsp + 0x10 ], r14; spilling x55 to mem
mulx r13, r14, rdi; x75, x74<- x68 * 0xffffffff00000000
mov rdx, rdi; _, copying x68 here, cause x68 is needed in a reg for other than _, namely all: , x72--x73, _--x82, x70--x71, size: 3
mov [ rsp + 0x18 ], rbx; spilling x53 to mem
seto bl; spill OF x59 to reg (rbx)
mov [ rsp + 0x20 ], r13; spilling x75 to mem
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rdx, r15
mov rdx, [ r10 + 0x10 ]; arg2[2] to rdx
mulx r15, r13, rbp; x8, x7<- x4 * arg2[2]
mov [ rsp + 0x28 ], r15; spilling x8 to mem
mov r15, 0xffffffffffffffff ; moving imm to reg
mov rdx, r15; 0xffffffffffffffff to rdx
mov [ rsp + 0x30 ], r9; spilling x2 to mem
mulx r15, r9, r11; x25, x24<- x20 * 0xffffffffffffffff
adcx r13, r8
setc r8b; spill CF x16 to reg (r8)
clc;
adcx r9, rcx
setc cl; spill CF x29 to reg (rcx)
clc;
mov rdx, -0x1 ; moving imm to reg
movzx rax, al
adcx rax, rdx; loading flag
adcx r13, r9
setc al; spill CF x38 to reg (rax)
clc;
movzx rbx, bl
adcx rbx, rdx; loading flag
adcx r13, r12
adox r14, r13
mov rdx, [ r10 + 0x0 ]; arg2[0] to rdx
mulx r12, rbx, [ rsp + 0x30 ]; x99, x98<- x2 * arg2[0]
setc r9b; spill CF x61 to reg (r9)
clc;
adcx rbx, r14
mov r13, 0xffffffffffffffff ; moving imm to reg
mov rdx, r13; 0xffffffffffffffff to rdx
mulx r13, r14, rbx; _, x117<- x107 * 0xffffffffffffffff
mov r13, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ r10 + 0x18 ]; saving arg2[3] in rdx.
mov [ rsp + 0x38 ], r14; spilling x117 to mem
mulx rbp, r14, rbp; x6, x5<- x4 * arg2[3]
mov r13, 0xffffffff ; moving imm to reg
mov rdx, r11; x20 to rdx
mulx rdx, r11, r13; x23, x22<- x20 * 0xffffffff
setc r13b; spill CF x108 to reg (r13)
clc;
mov [ rsp + 0x40 ], rdx; spilling x23 to mem
mov rdx, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, rdx; loading flag
adcx r14, [ rsp + 0x28 ]
setc r8b; spill CF x18 to reg (r8)
clc;
movzx rcx, cl
adcx rcx, rdx; loading flag
adcx r15, r11
mov rcx, 0xffffffffffffffff ; moving imm to reg
mov rdx, rcx; 0xffffffffffffffff to rdx
mulx rcx, r11, rdi; x73, x72<- x68 * 0xffffffffffffffff
setc dl; spill CF x31 to reg (rdx)
clc;
adcx r11, [ rsp + 0x20 ]
mov [ rsp + 0x48 ], rcx; spilling x73 to mem
setc cl; spill CF x77 to reg (rcx)
clc;
mov byte [ rsp + 0x50 ], dl; spilling byte x31 to mem
mov rdx, -0x1 ; moving imm to reg
movzx rax, al
adcx rax, rdx; loading flag
adcx r14, r15
mov rax, [ rsi + 0x18 ]; load m64 x3 to register64
setc r15b; spill CF x40 to reg (r15)
clc;
movzx r9, r9b
adcx r9, rdx; loading flag
adcx r14, [ rsp + 0x18 ]
mov rdx, [ r10 + 0x8 ]; arg2[1] to rdx
mov byte [ rsp + 0x58 ], r15b; spilling byte x40 to mem
mulx r9, r15, [ rsp + 0x30 ]; x97, x96<- x2 * arg2[1]
mov [ rsp + 0x60 ], r9; spilling x97 to mem
setc r9b; spill CF x63 to reg (r9)
clc;
adcx r15, r12
mov r12, 0xffffffff00000000 ; moving imm to reg
mov rdx, r12; 0xffffffff00000000 to rdx
mov byte [ rsp + 0x68 ], r9b; spilling byte x63 to mem
mulx r12, r9, [ rsp + 0x38 ]; x124, x123<- x117 * 0xffffffff00000000
adox r11, r14
setc r14b; spill CF x101 to reg (r14)
clc;
mov rdx, -0x1 ; moving imm to reg
movzx r13, r13b
adcx r13, rdx; loading flag
adcx r11, r15
setc r13b; spill CF x110 to reg (r13)
clc;
adcx rbx, [ rsp + 0x38 ]
mov rdx, [ r10 + 0x0 ]; arg2[0] to rdx
mulx rbx, r15, rax; x148, x147<- x3 * arg2[0]
adcx r9, r11
setc r11b; spill CF x133 to reg (r11)
clc;
adcx r15, r9
mov r9, 0xffffffffffffffff ; moving imm to reg
mov rdx, r15; x156 to rdx
mov [ rsp + 0x70 ], rbx; spilling x148 to mem
mulx r15, rbx, r9; _, x166<- x156 * 0xffffffffffffffff
xchg rdx, rbx; x166, swapping with x156, which is currently in rdx
mov byte [ rsp + 0x78 ], r11b; spilling byte x133 to mem
mulx r15, r11, r9; x171, x170<- x166 * 0xffffffffffffffff
mov r9, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x80 ], r12; spilling x124 to mem
mov byte [ rsp + 0x88 ], r13b; spilling byte x110 to mem
mulx r12, r13, r9; x173, x172<- x166 * 0xffffffff00000000
movzx r9, r8b; x19, copying x18 here, cause x18 is needed in a reg for other than x19, namely all: , x19, size: 1
lea r9, [ r9 + rbp ]
setc bpl; spill CF x157 to reg (rbp)
clc;
adcx r11, r12
mov r8, 0xffffffff ; moving imm to reg
xchg rdx, r8; 0xffffffff, swapping with x166, which is currently in rdx
mulx rdi, r12, rdi; x71, x70<- x68 * 0xffffffff
mov [ rsp + 0x90 ], r11; spilling x174 to mem
mov [ rsp + 0x98 ], r13; spilling x172 to mem
mulx r11, r13, r8; x169, x168<- x166 * 0xffffffff
movzx rdx, byte [ rsp + 0x50 ]; x32, copying x31 here, cause x31 is needed in a reg for other than x32, namely all: , x32, size: 1
mov byte [ rsp + 0xa0 ], bpl; spilling byte x157 to mem
mov rbp, [ rsp + 0x40 ]; load m64 x23 to register64
lea rdx, [ rdx + rbp ]; r8/64 + m8
adcx r13, r15
mov rbp, 0x0 ; moving imm to reg
adcx r11, rbp
clc;
mov r15, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, r15; loading flag
adcx r12, [ rsp + 0x48 ]
adcx rdi, rbp
movzx rcx, byte [ rsp + 0x58 ]; load byte memx40 to register64
clc;
adcx rcx, r15; loading flag
adcx r9, rdx
setc cl; spill CF x42 to reg (rcx)
movzx rdx, byte [ rsp + 0x68 ]; load byte memx63 to register64
clc;
adcx rdx, r15; loading flag
adcx r9, [ rsp + 0x10 ]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mulx rbp, r15, [ rsp + 0x38 ]; x122, x121<- x117 * 0xffffffffffffffff
movzx rcx, cl
mov rdx, [ rsp + 0x8 ]; x66, copying x57 here, cause x57 is needed in a reg for other than x66, namely all: , x66--x67, size: 1
adcx rdx, rcx
adox r12, r9
adox rdi, rdx
mov rdx, [ r10 + 0x10 ]; arg2[2] to rdx
mulx rcx, r9, [ rsp + 0x30 ]; x95, x94<- x2 * arg2[2]
mov [ rsp + 0xa8 ], r11; spilling x178 to mem
seto r11b; spill OF x91 to reg (r11)
adc r11b, 0x0
movzx r11, r11b
mov [ rsp + 0xb0 ], r13; spilling x176 to mem
mov r13, 0xffffffff ; moving imm to reg
mov rdx, r13; 0xffffffff to rdx
mov byte [ rsp + 0xb8 ], r11b; spilling byte x91 to mem
mulx r13, r11, [ rsp + 0x38 ]; x120, x119<- x117 * 0xffffffff
add r14b, 0x7F; load flag from rm/8 into OF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
seto r14b; since that has deps, resore it whereever it was
adox r9, [ rsp + 0x60 ]
movzx r14, byte [ rsp + 0x88 ]; load byte memx110 to register64
mov rdx, -0x1 ; moving imm to reg
adcx r14, rdx; loading flag
adcx r12, r9
setc r14b; spill CF x112 to reg (r14)
clc;
adcx r15, [ rsp + 0x80 ]
adcx r11, rbp
mov rbp, 0x0 ; moving imm to reg
adcx r13, rbp
movzx r9, byte [ rsp + 0x78 ]; load byte memx133 to register64
clc;
adcx r9, rdx; loading flag
adcx r12, r15
mov rdx, [ r10 + 0x18 ]; arg2[3] to rdx
mulx r9, r15, [ rsp + 0x30 ]; x93, x92<- x2 * arg2[3]
adox r15, rcx
adox r9, rbp
dec rbp; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r14, r14b
adox r14, rbp; loading flag
adox rdi, r15
mov rdx, rax; x3 to rdx
mulx rax, rcx, [ r10 + 0x10 ]; x144, x143<- x3 * arg2[2]
mulx r14, r15, [ r10 + 0x8 ]; x146, x145<- x3 * arg2[1]
adcx r11, rdi
movzx rdi, byte [ rsp + 0xb8 ]; x115, copying x91 here, cause x91 is needed in a reg for other than x115, namely all: , x115--x116, size: 1
adox rdi, r9
seto r9b; spill OF x116 to reg (r9)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r15, [ rsp + 0x70 ]
adcx r13, rdi
adox rcx, r14
mulx rdx, r14, [ r10 + 0x18 ]; x142, x141<- x3 * arg2[3]
movzx rdi, r9b; x140, copying x116 here, cause x116 is needed in a reg for other than x140, namely all: , x140, size: 1
adcx rdi, rbp
adox r14, rax
adox rdx, rbp
add r8, rbx; could be done better, if r0 has been u8 as well
movzx r8, byte [ rsp + 0xa0 ]; load byte memx157 to register64
dec rbp; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
adox r8, rbp; loading flag
adox r12, r15
adox rcx, r11
mov rbx, [ rsp + 0x98 ]; x181, copying x172 here, cause x172 is needed in a reg for other than x181, namely all: , x181--x182, size: 1
adcx rbx, r12
mov r8, [ rsp + 0x90 ]; x183, copying x174 here, cause x174 is needed in a reg for other than x183, namely all: , x183--x184, size: 1
adcx r8, rcx
setc al; spill CF x184 to reg (rax)
seto r11b; spill OF x161 to reg (r11)
mov r9, rbx; x190, copying x181 here, cause x181 is needed in a reg for other than x190, namely all: , x190--x191, x200, size: 2
sub r9, 0x00000001
mov r15, r8; x192, copying x183 here, cause x183 is needed in a reg for other than x192, namely all: , x192--x193, x201, size: 2
mov r12, 0xffffffff00000000 ; moving imm to reg
sbb r15, r12
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rcx, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, rcx; loading flag
adox r13, r14
adox rdx, rdi
seto dil; spill OF x165 to reg (rdi)
dec rbp; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx rax, al
adox rax, rbp; loading flag
adox r13, [ rsp + 0xb0 ]
mov rcx, [ rsp + 0xa8 ]; x187, copying x178 here, cause x178 is needed in a reg for other than x187, namely all: , x187--x188, size: 1
adox rcx, rdx
movzx r14, dil; x189, copying x165 here, cause x165 is needed in a reg for other than x189, namely all: , x189, size: 1
mov r11, 0x0 ; moving imm to reg
adox r14, r11
mov rax, r13; x194, copying x185 here, cause x185 is needed in a reg for other than x194, namely all: , x194--x195, x202, size: 2
mov rdi, 0xffffffffffffffff ; moving imm to reg
sbb rax, rdi
mov rdx, rcx; x196, copying x187 here, cause x187 is needed in a reg for other than x196, namely all: , x203, x196--x197, size: 2
mov r11, 0xffffffff ; moving imm to reg
sbb rdx, r11
sbb r14, 0x00000000
cmovc rax, r13; if CF, x202<- x185 (nzVar)
mov r14, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r14 + 0x10 ], rax; out1[2] = x202
cmovc r9, rbx; if CF, x200<- x181 (nzVar)
cmovc rdx, rcx; if CF, x203<- x187 (nzVar)
cmovc r15, r8; if CF, x201<- x183 (nzVar)
mov [ r14 + 0x18 ], rdx; out1[3] = x203
mov [ r14 + 0x0 ], r9; out1[0] = x200
mov [ r14 + 0x8 ], r15; out1[1] = x201
mov rbx, [ rsp + 0xc0 ]; restoring from stack
mov rbp, [ rsp + 0xc8 ]; restoring from stack
mov r12, [ rsp + 0xd0 ]; restoring from stack
mov r13, [ rsp + 0xd8 ]; restoring from stack
mov r14, [ rsp + 0xe0 ]; restoring from stack
mov r15, [ rsp + 0xe8 ]; restoring from stack
add rsp, 0xf0 
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; clocked at 1600 MHz
; first cyclecount 60.5075, best 39.578828828828826, lastGood 40.59907834101382
; seed 2240937234026075 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1363050 ms / 60000 runs=> 22.7175ms/run
; Time spent for assembling and measureing (initial batch_size=217, initial num_batches=101): 393216 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.28848244745240453
; number reverted permutation/ tried permutation: 25952 / 30016 =86.461%
; number reverted decision/ tried decision: 24679 / 29985 =82.304%