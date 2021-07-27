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
mov rax, [ rsi + 0x8 ]; load m64 x1 to register64
mov r10, [ rsi + 0x0 ]; load m64 x4 to register64
mov rdx, rax; x1 to rdx
mulx rax, r11, [ rsi + 0x8 ]; x48, x47<- x1 * arg1[1]
mulx rbx, rbp, [ rsi + 0x18 ]; x44, x43<- x1 * arg1[3]
mulx r12, r13, [ rsi + 0x10 ]; x46, x45<- x1 * arg1[2]
mulx rdx, r14, [ rsi + 0x0 ]; x50, x49<- x1 * arg1[0]
mov r15, rdx; preserving value of x50 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx rcx, r8, r10; x12, x11<- x4 * arg1[0]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r9, rdi, r8; _, x20<- x11 * 0xffffffffffffffff
add r11, r15; could be done better, if r0 has been u8 as well
adcx r13, rax
adcx rbp, r12
adc rbx, 0x0
mov r9, rdi; _, copying x20 here, cause x20 is needed in a reg for other than _, namely all: , x22--x23, _--x34, x24--x25, x26--x27, size: 4
xor rax, rax
adox r9, r8
mov r9, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r12, r15, r10; x10, x9<- x4 * arg1[1]
adcx r15, rcx
mov rdx, 0xffffffff00000000 ; moving imm to reg
mulx rcx, r8, rdi; x27, x26<- x20 * 0xffffffff00000000
adox r8, r15
seto r15b; spill OF x36 to reg (r15)
mov rdx, -0x3 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r14, r8
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r8, rax, r10; x8, x7<- x4 * arg1[2]
mov rdx, r9; 0xffffffffffffffff to rdx
mov [ rsp + 0x8 ], rbx; spilling x57 to mem
mulx r9, rbx, rdi; x25, x24<- x20 * 0xffffffffffffffff
adcx rax, r12
setc r12b; spill CF x16 to reg (r12)
clc;
adcx rbx, rcx
mov [ rsp + 0x10 ], rbp; spilling x55 to mem
mulx rcx, rbp, r14; _, x68<- x58 * 0xffffffffffffffff
setc cl; spill CF x29 to reg (rcx)
clc;
mov rdx, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, rdx; loading flag
adcx rax, rbx
adox r11, rax
mov r15, rbp; _, copying x68 here, cause x68 is needed in a reg for other than _, namely all: , x70--x71, x72--x73, _--x82, x74--x75, size: 4
setc bl; spill CF x38 to reg (rbx)
clc;
adcx r15, r14
mov r15, [ rsi + 0x10 ]; load m64 x2 to register64
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r14, rax, r15; x99, x98<- x2 * arg1[0]
mov rdx, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x18 ], r14; spilling x99 to mem
mov [ rsp + 0x20 ], r13; spilling x53 to mem
mulx r14, r13, rbp; x75, x74<- x68 * 0xffffffff00000000
adcx r13, r11
setc r11b; spill CF x84 to reg (r11)
clc;
adcx rax, r13
mov r13, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r13; 0xffffffffffffffff, swapping with 0xffffffff00000000, which is currently in rdx
mov byte [ rsp + 0x28 ], r11b; spilling byte x84 to mem
mulx r13, r11, rax; _, x117<- x107 * 0xffffffffffffffff
mov byte [ rsp + 0x30 ], bl; spilling byte x38 to mem
mulx r13, rbx, r11; x122, x121<- x117 * 0xffffffffffffffff
mov rdx, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x38 ], r9; spilling x25 to mem
mov byte [ rsp + 0x40 ], cl; spilling byte x29 to mem
mulx r9, rcx, r11; x124, x123<- x117 * 0xffffffff00000000
mov rdx, 0xffffffff ; moving imm to reg
mov [ rsp + 0x48 ], rcx; spilling x123 to mem
mov [ rsp + 0x50 ], r8; spilling x8 to mem
mulx rcx, r8, rbp; x71, x70<- x68 * 0xffffffff
mov [ rsp + 0x58 ], rcx; spilling x71 to mem
mov byte [ rsp + 0x60 ], r12b; spilling byte x16 to mem
mulx rcx, r12, r11; x120, x119<- x117 * 0xffffffff
setc dl; spill CF x108 to reg (rdx)
clc;
adcx rbx, r9
adcx r12, r13
mov r13b, dl; preserving value of x108 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx r10, r9, r10; x6, x5<- x4 * arg1[3]
mov rdx, 0xffffffff ; moving imm to reg
mov [ rsp + 0x68 ], r12; spilling x127 to mem
mulx rdi, r12, rdi; x23, x22<- x20 * 0xffffffff
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x70 ], rbx; spilling x125 to mem
mulx rbp, rbx, rbp; x73, x72<- x68 * 0xffffffffffffffff
mov rdx, 0x0 ; moving imm to reg
adcx rcx, rdx
clc;
adcx rbx, r14
adcx r8, rbp
setc r14b; spill CF x79 to reg (r14)
movzx rbp, byte [ rsp + 0x60 ]; load byte memx16 to register64
clc;
mov rdx, -0x1 ; moving imm to reg
adcx rbp, rdx; loading flag
adcx r9, [ rsp + 0x50 ]
seto bpl; spill OF x61 to reg (rbp)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r11, rax
seto r11b; spill OF x131 to reg (r11)
movzx rax, byte [ rsp + 0x40 ]; load byte memx29 to register64
dec rdx; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
adox rax, rdx; loading flag
adox r12, [ rsp + 0x38 ]
mov rax, 0x0 ; moving imm to reg
adox rdi, rax
adc r10, 0x0
movzx rax, r14b; x80, copying x79 here, cause x79 is needed in a reg for other than x80, namely all: , x80, size: 1
add rax, [ rsp + 0x58 ]
add byte [ rsp + 0x30 ], 0x7F; load flag from rm/8 into OF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
seto [ rsp + 0x30 ]; since that has deps, resore it whereever it was
adox r9, r12
adox rdi, r10
movzx rbp, bpl
adcx rbp, rdx; loading flag
adcx r9, [ rsp + 0x20 ]
mov rdx, r15; x2 to rdx
mulx r15, rbp, [ rsi + 0x8 ]; x97, x96<- x2 * arg1[1]
mov r14, [ rsp + 0x10 ]; x64, copying x55 here, cause x55 is needed in a reg for other than x64, namely all: , x64--x65, size: 1
adcx r14, rdi
seto r12b; spill OF x66 to reg (r12)
movzx r12, r12b; spilling a flag to reg cause it has deps 
adcx r12, [ rsp + 0x8 ]; CF should have been spilled if it had deps, OF should have been spilled into r12 and into another reg, if it has had other deps than this one.
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, [ rsp + 0x18 ]
mov rdi, [ rsi + 0x18 ]; load m64 x3 to register64
setc r10b; spill CF x67 to reg (r10)
mov [ rsp + 0x78 ], rdi; spilling x3 to mem
movzx rdi, byte [ rsp + 0x28 ]; load byte memx84 to register64
clc;
mov [ rsp + 0x80 ], rcx; spilling x129 to mem
mov rcx, -0x1 ; moving imm to reg
adcx rdi, rcx; loading flag
adcx r9, rbx
mulx rdi, rbx, [ rsi + 0x10 ]; x95, x94<- x2 * arg1[2]
adox rbx, r15
adcx r8, r14
mulx rdx, r15, [ rsi + 0x18 ]; x93, x92<- x2 * arg1[3]
adox r15, rdi
adcx rax, r12
mov r14, 0x0 ; moving imm to reg
adox rdx, r14
movzx r12, r10b; x91, copying x67 here, cause x67 is needed in a reg for other than x91, namely all: , x91, size: 1
adc r12, 0x0
add r13b, 0xFF; load flag from rm/8 into CF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
setc r13b; since that has deps, resore it whereever it was
adcx r9, rbp
adcx rbx, r8
adcx r15, rax
movzx r11, r11b
adox r11, rcx; loading flag
adox r9, [ rsp + 0x48 ]
adcx rdx, r12
mov r13, [ rsp + 0x70 ]; x134, copying x125 here, cause x125 is needed in a reg for other than x134, namely all: , x134--x135, size: 1
adox r13, rbx
mov r11, [ rsp + 0x68 ]; x136, copying x127 here, cause x127 is needed in a reg for other than x136, namely all: , x136--x137, size: 1
adox r11, r15
mov r10, [ rsp + 0x80 ]; x138, copying x129 here, cause x129 is needed in a reg for other than x138, namely all: , x138--x139, size: 1
adox r10, rdx
seto bpl; spill OF x140 to reg (rbp)
adc bpl, 0x0
movzx rbp, bpl
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rdi, r8, [ rsp + 0x78 ]; x148, x147<- x3 * arg1[0]
adox r8, r9
mov rdx, 0xffffffffffffffff ; moving imm to reg
mulx rax, r12, r8; _, x166<- x156 * 0xffffffffffffffff
mov rax, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx rbx, r15, [ rsp + 0x78 ]; x146, x145<- x3 * arg1[1]
mov rdx, r12; x166 to rdx
mulx r12, r9, rax; x171, x170<- x166 * 0xffffffffffffffff
mov rcx, rdx; _, copying x166 here, cause x166 is needed in a reg for other than _, namely all: , _--x180, x172--x173, x168--x169, size: 3
adcx rcx, r8
setc cl; spill CF x180 to reg (rcx)
clc;
adcx r15, rdi
adox r15, r13
mov r13, 0xffffffff00000000 ; moving imm to reg
mulx rdi, r8, r13; x173, x172<- x166 * 0xffffffff00000000
mov r14, rdx; preserving value of x166 into a new reg
mov rdx, [ rsp + 0x78 ]; saving x3 in rdx.
mulx r13, rax, [ rsi + 0x10 ]; x144, x143<- x3 * arg1[2]
mov [ rsp + 0x88 ], r12; spilling x171 to mem
seto r12b; spill OF x159 to reg (r12)
mov byte [ rsp + 0x90 ], bpl; spilling byte x140 to mem
mov rbp, 0x0 ; moving imm to reg
dec rbp; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rcx, cl
adox rcx, rbp; loading flag
adox r15, r8
adcx rax, rbx
setc bl; spill CF x152 to reg (rbx)
clc;
adcx r9, rdi
setc cl; spill CF x175 to reg (rcx)
seto dil; spill OF x182 to reg (rdi)
mov r8, r15; x190, copying x181 here, cause x181 is needed in a reg for other than x190, namely all: , x200, x190--x191, size: 2
sub r8, 0x00000001
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, rbp; loading flag
adox r11, rax
mulx rdx, r12, [ rsi + 0x18 ]; x142, x141<- x3 * arg1[3]
setc al; spill CF x191 to reg (rax)
clc;
movzx rdi, dil
adcx rdi, rbp; loading flag
adcx r11, r9
setc dil; spill CF x184 to reg (rdi)
clc;
movzx rbx, bl
adcx rbx, rbp; loading flag
adcx r13, r12
mov rbx, 0x0 ; moving imm to reg
adcx rdx, rbx
adox r13, r10
movzx r10, byte [ rsp + 0x90 ]; x164, copying x140 here, cause x140 is needed in a reg for other than x164, namely all: , x164--x165, size: 1
adox r10, rdx
mov r9, 0xffffffff ; moving imm to reg
mov rdx, r9; 0xffffffff to rdx
mulx r14, r9, r14; x169, x168<- x166 * 0xffffffff
clc;
movzx rcx, cl
adcx rcx, rbp; loading flag
adcx r9, [ rsp + 0x88 ]
adcx r14, rbx
seto cl; spill OF x165 to reg (rcx)
movzx r12, al; x191, copying x191 here, cause x191 is needed in a reg for other than x191, namely all: , x192--x193, size: 1
add r12, -0x1
mov rax, r11; x192, copying x183 here, cause x183 is needed in a reg for other than x192, namely all: , x192--x193, x201, size: 2
mov r12, 0xffffffff00000000 ; moving imm to reg
sbb rax, r12
inc rbp; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov rbx, -0x1 ; moving imm to reg
movzx rdi, dil
adox rdi, rbx; loading flag
adox r13, r9
adox r14, r10
movzx rdi, cl; x189, copying x165 here, cause x165 is needed in a reg for other than x189, namely all: , x189, size: 1
adox rdi, rbp
mov rcx, r13; x194, copying x185 here, cause x185 is needed in a reg for other than x194, namely all: , x194--x195, x202, size: 2
mov r10, 0xffffffffffffffff ; moving imm to reg
sbb rcx, r10
mov r9, r14; x196, copying x187 here, cause x187 is needed in a reg for other than x196, namely all: , x203, x196--x197, size: 2
sbb r9, rdx
sbb rdi, 0x00000000
cmovc rcx, r13; if CF, x202<- x185 (nzVar)
cmovc rax, r11; if CF, x201<- x183 (nzVar)
cmovc r8, r15; if CF, x200<- x181 (nzVar)
cmovc r9, r14; if CF, x203<- x187 (nzVar)
mov r15, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r15 + 0x10 ], rcx; out1[2] = x202
mov [ r15 + 0x8 ], rax; out1[1] = x201
mov [ r15 + 0x18 ], r9; out1[3] = x203
mov [ r15 + 0x0 ], r8; out1[0] = x200
mov rbx, [ rsp + 0x98 ]; restoring from stack
mov rbp, [ rsp + 0xa0 ]; restoring from stack
mov r12, [ rsp + 0xa8 ]; restoring from stack
mov r13, [ rsp + 0xb0 ]; restoring from stack
mov r14, [ rsp + 0xb8 ]; restoring from stack
mov r15, [ rsp + 0xc0 ]; restoring from stack
add rsp, 0xc8 
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; clocked at 2600 MHz
; first cyclecount 96.14, best 71.45736434108527, lastGood 71.875
; seed 1800767550616553 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1132138 ms / 60000 runs=> 18.868966666666665ms/run
; Time spent for assembling and measureing (initial batch_size=128, initial num_batches=101): 231203 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.20421803702375504
; number reverted permutation/ tried permutation: 23563 / 29904 =78.795%
; number reverted decision/ tried decision: 22214 / 30097 =73.808%