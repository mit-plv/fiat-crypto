SECTION .text
	GLOBAL mul_secp256k1
mul_secp256k1:
sub rsp, 0x110 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0xe0 ], rbx; saving to stack
mov [ rsp + 0xe8 ], rbp; saving to stack
mov [ rsp + 0xf0 ], r12; saving to stack
mov [ rsp + 0xf8 ], r13; saving to stack
mov [ rsp + 0x100 ], r14; saving to stack
mov [ rsp + 0x108 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x4 to register64
mov r10, [ rsi + 0x10 ]; load m64 x2 to register64
xchg rdx, rax; x4, swapping with arg2, which is currently in rdx
mulx r11, rbx, [ rax + 0x8 ]; x10, x9<- x4 * arg2[1]
mov rbp, [ rsi + 0x8 ]; load m64 x1 to register64
mulx r12, r13, [ rax + 0x0 ]; x12, x11<- x4 * arg2[0]
mov r14, 0xd838091dd2253531 ; moving imm to reg
xchg rdx, r14; 0xd838091dd2253531, swapping with x4, which is currently in rdx
mulx r15, rcx, r13; _, x20<- x11 * 0xd838091dd2253531
mov r15, 0xfffffffefffffc2f ; moving imm to reg
xchg rdx, rcx; x20, swapping with 0xd838091dd2253531, which is currently in rdx
mulx r8, r9, r15; x29, x28<- x20 * 0xfffffffefffffc2f
mov r15, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx rcx, rdi, r15; x25, x24<- x20 * 0xffffffffffffffff
mov [ rsp + 0x8 ], rsi; spilling arg1 to mem
mov [ rsp + 0x10 ], rcx; spilling x25 to mem
mulx rsi, rcx, r15; x27, x26<- x20 * 0xffffffffffffffff
add rbx, r12; could be done better, if r0 has been u8 as well
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r9, r13
xchg rdx, r14; x4, swapping with x20, which is currently in rdx
mulx r9, r13, [ rax + 0x10 ]; x8, x7<- x4 * arg2[2]
setc r12b; spill CF x14 to reg (r12)
clc;
adcx rcx, r8
adcx rdi, rsi
mov r8, rdx; preserving value of x4 into a new reg
mov rdx, [ rax + 0x0 ]; saving arg2[0] in rdx.
mulx rsi, r15, rbp; x54, x53<- x1 * arg2[0]
mov [ rsp + 0x18 ], r9; spilling x8 to mem
setc r9b; spill CF x33 to reg (r9)
clc;
mov [ rsp + 0x20 ], r10; spilling x2 to mem
mov r10, -0x1 ; moving imm to reg
movzx r12, r12b
adcx r12, r10; loading flag
adcx r11, r13
adox rcx, rbx
setc bl; spill CF x16 to reg (rbx)
clc;
adcx r15, rcx
adox rdi, r11
mov r12, 0xd838091dd2253531 ; moving imm to reg
mov rdx, r15; x62 to rdx
mulx r15, r13, r12; _, x72<- x62 * 0xd838091dd2253531
mov r15, 0xfffffffefffffc2f ; moving imm to reg
xchg rdx, r15; 0xfffffffefffffc2f, swapping with x62, which is currently in rdx
mulx r11, rcx, r13; x81, x80<- x72 * 0xfffffffefffffc2f
mov r10, rdx; preserving value of 0xfffffffefffffc2f into a new reg
mov rdx, [ rax + 0x8 ]; saving arg2[1] in rdx.
mov byte [ rsp + 0x28 ], r9b; spilling byte x33 to mem
mulx r12, r9, rbp; x52, x51<- x1 * arg2[1]
mov r10, 0xffffffffffffffff ; moving imm to reg
mov rdx, r13; x72 to rdx
mov [ rsp + 0x30 ], r14; spilling x20 to mem
mulx r13, r14, r10; x79, x78<- x72 * 0xffffffffffffffff
seto r10b; spill OF x42 to reg (r10)
mov [ rsp + 0x38 ], r13; spilling x79 to mem
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, r11
seto r11b; spill OF x83 to reg (r11)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r9, rsi
adcx r9, rdi
xchg rdx, r8; x4, swapping with x72, which is currently in rdx
mulx rdx, rsi, [ rax + 0x18 ]; x6, x5<- x4 * arg2[3]
setc dil; spill CF x65 to reg (rdi)
clc;
adcx rcx, r15
adcx r14, r9
mov rcx, rdx; preserving value of x6 into a new reg
mov rdx, [ rax + 0x0 ]; saving arg2[0] in rdx.
mulx r15, r9, [ rsp + 0x20 ]; x107, x106<- x2 * arg2[0]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x40 ], rcx; spilling x6 to mem
mulx r13, rcx, [ rsp + 0x20 ]; x105, x104<- x2 * arg2[1]
mov [ rsp + 0x48 ], r13; spilling x105 to mem
setc r13b; spill CF x92 to reg (r13)
clc;
adcx r9, r14
mov r14, 0xd838091dd2253531 ; moving imm to reg
mov rdx, r9; x115 to rdx
mov byte [ rsp + 0x50 ], r13b; spilling byte x92 to mem
mulx r9, r13, r14; _, x125<- x115 * 0xd838091dd2253531
mov r9, 0xfffffffefffffc2f ; moving imm to reg
xchg rdx, r9; 0xfffffffefffffc2f, swapping with x115, which is currently in rdx
mov byte [ rsp + 0x58 ], r11b; spilling byte x83 to mem
mulx r14, r11, r13; x134, x133<- x125 * 0xfffffffefffffc2f
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov byte [ rsp + 0x60 ], dil; spilling byte x65 to mem
mov byte [ rsp + 0x68 ], r10b; spilling byte x42 to mem
mulx rdi, r10, r13; x132, x131<- x125 * 0xffffffffffffffff
mov [ rsp + 0x70 ], rsi; spilling x5 to mem
mov byte [ rsp + 0x78 ], bl; spilling byte x16 to mem
mulx rsi, rbx, r13; x128, x127<- x125 * 0xffffffffffffffff
setc dl; spill CF x116 to reg (rdx)
clc;
adcx r10, r14
xchg rdx, rbp; x1, swapping with x116, which is currently in rdx
mov [ rsp + 0x80 ], r10; spilling x135 to mem
mulx r14, r10, [ rax + 0x10 ]; x50, x49<- x1 * arg2[2]
mov [ rsp + 0x88 ], r14; spilling x50 to mem
mov r14, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r13; x125, swapping with x1, which is currently in rdx
mov byte [ rsp + 0x90 ], bpl; spilling byte x116 to mem
mulx rdx, rbp, r14; x130, x129<- x125 * 0xffffffffffffffff
adox r10, r12
adcx rbp, rdi
xchg rdx, r8; x72, swapping with x130, which is currently in rdx
mulx r12, rdi, r14; x77, x76<- x72 * 0xffffffffffffffff
seto r14b; spill OF x58 to reg (r14)
mov [ rsp + 0x98 ], rbp; spilling x137 to mem
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, r9
seto r11b; spill OF x143 to reg (r11)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rcx, r15
adcx rbx, r8
mov r15, [ rsp + 0x70 ]; load m64 x5 to register64
seto r9b; spill OF x109 to reg (r9)
movzx r8, byte [ rsp + 0x78 ]; load byte memx16 to register64
dec rbp; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
adox r8, rbp; loading flag
adox r15, [ rsp + 0x18 ]
mov r8, 0x0 ; moving imm to reg
adcx rsi, r8
mov r8, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r8; 0xffffffffffffffff, swapping with x72, which is currently in rdx
mov [ rsp + 0xa0 ], rsi; spilling x141 to mem
mulx rbp, rsi, [ rsp + 0x30 ]; x23, x22<- x20 * 0xffffffffffffffff
movzx rdx, byte [ rsp + 0x28 ]; load byte memx33 to register64
clc;
mov [ rsp + 0xa8 ], rbx; spilling x139 to mem
mov rbx, -0x1 ; moving imm to reg
adcx rdx, rbx; loading flag
adcx rsi, [ rsp + 0x10 ]
seto dl; spill OF x18 to reg (rdx)
movzx rbx, byte [ rsp + 0x68 ]; load byte memx42 to register64
mov byte [ rsp + 0xb0 ], r9b; spilling byte x109 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbx, r9; loading flag
adox r15, rsi
mov rbx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r8; x72, swapping with x18, which is currently in rdx
mulx rdx, rsi, rbx; x75, x74<- x72 * 0xffffffffffffffff
mov r9, 0x0 ; moving imm to reg
adcx rbp, r9
movzx r9, byte [ rsp + 0x60 ]; load byte memx65 to register64
clc;
mov rbx, -0x1 ; moving imm to reg
adcx r9, rbx; loading flag
adcx r15, r10
setc r9b; spill CF x67 to reg (r9)
movzx r10, byte [ rsp + 0x58 ]; load byte memx83 to register64
clc;
adcx r10, rbx; loading flag
adcx rdi, [ rsp + 0x38 ]
adcx rsi, r12
movzx r10, r8b; x19, copying x18 here, cause x18 is needed in a reg for other than x19, namely all: , x19, size: 1
mov r12, [ rsp + 0x40 ]; load m64 x6 to register64
lea r10, [ r10 + r12 ]; r8/64 + m8
mov r12, 0x0 ; moving imm to reg
adcx rdx, r12
movzx r8, byte [ rsp + 0x50 ]; load byte memx92 to register64
clc;
adcx r8, rbx; loading flag
adcx r15, rdi
setc r8b; spill CF x94 to reg (r8)
movzx rdi, byte [ rsp + 0x90 ]; load byte memx116 to register64
clc;
adcx rdi, rbx; loading flag
adcx r15, rcx
setc dil; spill CF x118 to reg (rdi)
clc;
movzx r11, r11b
adcx r11, rbx; loading flag
adcx r15, [ rsp + 0x80 ]
adox rbp, r10
mov r11, rdx; preserving value of x88 into a new reg
mov rdx, [ rax + 0x18 ]; saving arg2[3] in rdx.
mulx r13, rcx, r13; x48, x47<- x1 * arg2[3]
seto r10b; spill OF x46 to reg (r10)
dec r12; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx r14, r14b
adox r14, r12; loading flag
adox rcx, [ rsp + 0x88 ]
mov rdx, [ rsp + 0x20 ]; x2 to rdx
mulx rbx, r14, [ rax + 0x10 ]; x103, x102<- x2 * arg2[2]
mov r12, 0x0 ; moving imm to reg
adox r13, r12
dec r12; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r9, r9b
adox r9, r12; loading flag
adox rbp, rcx
movzx r9, r10b; x70, copying x46 here, cause x46 is needed in a reg for other than x70, namely all: , x70--x71, size: 1
adox r9, r13
setc r10b; spill CF x145 to reg (r10)
clc;
movzx r8, r8b
adcx r8, r12; loading flag
adcx rbp, rsi
mulx rdx, rsi, [ rax + 0x18 ]; x101, x100<- x2 * arg2[3]
adcx r11, r9
setc r8b; spill CF x98 to reg (r8)
movzx rcx, byte [ rsp + 0xb0 ]; load byte memx109 to register64
clc;
adcx rcx, r12; loading flag
adcx r14, [ rsp + 0x48 ]
adcx rsi, rbx
mov rcx, 0x0 ; moving imm to reg
adcx rdx, rcx
mov rbx, [ rsp + 0x8 ]; load m64 arg1 to register64
mov r13, [ rbx + 0x18 ]; load m64 x3 to register64
movzx r9, r8b; x99, copying x98 here, cause x98 is needed in a reg for other than x99, namely all: , x99, size: 1
adox r9, rcx
xchg rdx, r13; x3, swapping with x114, which is currently in rdx
mulx r8, rcx, [ rax + 0x0 ]; x160, x159<- x3 * arg2[0]
add dil, 0x7F; load flag from rm/8 into OF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
seto dil; since that has deps, resore it whereever it was
adox rbp, r14
adox rsi, r11
movzx r10, r10b
adcx r10, r12; loading flag
adcx rbp, [ rsp + 0x98 ]
adox r13, r9
seto dil; spill OF x124 to reg (rdi)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rcx, r15
mov r15, [ rsp + 0xa8 ]; x148, copying x139 here, cause x139 is needed in a reg for other than x148, namely all: , x148--x149, size: 1
adcx r15, rsi
mov r10, [ rsp + 0xa0 ]; x150, copying x141 here, cause x141 is needed in a reg for other than x150, namely all: , x150--x151, size: 1
adcx r10, r13
mov r11, 0xd838091dd2253531 ; moving imm to reg
xchg rdx, r11; 0xd838091dd2253531, swapping with x3, which is currently in rdx
mulx r14, r9, rcx; _, x178<- x168 * 0xd838091dd2253531
movzx r14, dil; x152, copying x124 here, cause x124 is needed in a reg for other than x152, namely all: , x152, size: 1
adcx r14, r12
xchg rdx, r11; x3, swapping with 0xd838091dd2253531, which is currently in rdx
mulx rsi, rdi, [ rax + 0x8 ]; x158, x157<- x3 * arg2[1]
clc;
adcx rdi, r8
mov r8, 0xfffffffefffffc2f ; moving imm to reg
xchg rdx, r8; 0xfffffffefffffc2f, swapping with x3, which is currently in rdx
mulx r13, r12, r9; x187, x186<- x178 * 0xfffffffefffffc2f
adox rdi, rbp
setc bpl; spill CF x162 to reg (rbp)
clc;
adcx r12, rcx
mov r12, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r12; 0xffffffffffffffff, swapping with 0xfffffffefffffc2f, which is currently in rdx
mulx rcx, r12, r9; x185, x184<- x178 * 0xffffffffffffffff
seto r11b; spill OF x171 to reg (r11)
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, r13
mov r13, 0xffffffffffffffff ; moving imm to reg
mov rdx, r13; 0xffffffffffffffff to rdx
mov [ rsp + 0xb8 ], r14; spilling x152 to mem
mulx r13, r14, r9; x183, x182<- x178 * 0xffffffffffffffff
adox r14, rcx
xchg rdx, r8; x3, swapping with 0xffffffffffffffff, which is currently in rdx
mulx rcx, r8, [ rax + 0x10 ]; x156, x155<- x3 * arg2[2]
adcx r12, rdi
mulx rdx, rdi, [ rax + 0x18 ]; x154, x153<- x3 * arg2[3]
mov [ rsp + 0xc0 ], r10; spilling x150 to mem
setc r10b; spill CF x198 to reg (r10)
mov [ rsp + 0xc8 ], r14; spilling x190 to mem
seto r14b; spill OF x191 to reg (r14)
mov [ rsp + 0xd0 ], r15; spilling x148 to mem
mov r15, r12; x206, copying x197 here, cause x197 is needed in a reg for other than x206, namely all: , x206--x207, x216, size: 2
mov byte [ rsp + 0xd8 ], r11b; spilling byte x171 to mem
mov r11, 0xfffffffefffffc2f ; moving imm to reg
sub r15, r11
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, r11; loading flag
adox rsi, r8
mov rbp, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbp; 0xffffffffffffffff, swapping with x154, which is currently in rdx
mulx r9, r8, r9; x181, x180<- x178 * 0xffffffffffffffff
adox rdi, rcx
setc cl; spill CF x207 to reg (rcx)
clc;
movzx r14, r14b
adcx r14, r11; loading flag
adcx r13, r8
mov r14, 0x0 ; moving imm to reg
adcx r9, r14
adox rbp, r14
add byte [ rsp + 0xd8 ], 0xFF; load flag from rm/8 into CF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
setc [ rsp + 0xd8 ]; since that has deps, resore it whereever it was
adcx rsi, [ rsp + 0xd0 ]
movzx r10, r10b
adox r10, r11; loading flag
adox rsi, [ rsp + 0xc8 ]
mov r10, [ rsp + 0xc0 ]; x174, copying x150 here, cause x150 is needed in a reg for other than x174, namely all: , x174--x175, size: 1
adcx r10, rdi
adox r13, r10
mov r8, [ rsp + 0xb8 ]; x176, copying x152 here, cause x152 is needed in a reg for other than x176, namely all: , x176--x177, size: 1
adcx r8, rbp
adox r9, r8
setc dil; spill CF x177 to reg (rdi)
seto bpl; spill OF x204 to reg (rbp)
movzx r10, cl; x207, copying x207 here, cause x207 is needed in a reg for other than x207, namely all: , x208--x209, size: 1
add r10, -0x1
mov r10, rsi; x208, copying x199 here, cause x199 is needed in a reg for other than x208, namely all: , x208--x209, x217, size: 2
sbb r10, rdx
mov rcx, r13; x210, copying x201 here, cause x201 is needed in a reg for other than x210, namely all: , x218, x210--x211, size: 2
sbb rcx, rdx
mov r8, r9; x212, copying x203 here, cause x203 is needed in a reg for other than x212, namely all: , x212--x213, x219, size: 2
sbb r8, rdx
movzx r14, bpl; x205, copying x204 here, cause x204 is needed in a reg for other than x205, namely all: , x205, size: 1
movzx rdi, dil
lea r14, [ r14 + rdi ]
sbb r14, 0x00000000
cmovc r10, rsi; if CF, x217<- x199 (nzVar)
cmovc r8, r9; if CF, x219<- x203 (nzVar)
cmovc r15, r12; if CF, x216<- x197 (nzVar)
mov r14, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r14 + 0x0 ], r15; out1[0] = x216
cmovc rcx, r13; if CF, x218<- x201 (nzVar)
mov [ r14 + 0x10 ], rcx; out1[2] = x218
mov [ r14 + 0x8 ], r10; out1[1] = x217
mov [ r14 + 0x18 ], r8; out1[3] = x219
mov rbx, [ rsp + 0xe0 ]; restoring from stack
mov rbp, [ rsp + 0xe8 ]; restoring from stack
mov r12, [ rsp + 0xf0 ]; restoring from stack
mov r13, [ rsp + 0xf8 ]; restoring from stack
mov r14, [ rsp + 0x100 ]; restoring from stack
mov r15, [ rsp + 0x108 ]; restoring from stack
add rsp, 0x110 
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; clocked at 2200 MHz
; first cyclecount 137.56, best 102.5, lastGood 105.5
; seed 1660769872531946 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1303784 ms / 60000 runs=> 21.729733333333332ms/run
; Time spent for assembling and measureing (initial batch_size=76, initial num_batches=101): 180013 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.13806964957385578
; number reverted permutation/ tried permutation: 23441 / 30160 =77.722%
; number reverted decision/ tried decision: 20654 / 29841 =69.213%