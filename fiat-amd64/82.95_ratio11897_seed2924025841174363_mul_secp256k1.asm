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
mov r10, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x8 ]; saving arg2[1] in rdx.
mulx r11, rbx, rax; x10, x9<- x4 * arg2[1]
mov rbp, [ rsi + 0x8 ]; load m64 x1 to register64
mov rdx, rax; x4 to rdx
mulx rax, r12, [ r10 + 0x10 ]; x8, x7<- x4 * arg2[2]
mulx r13, r14, [ r10 + 0x18 ]; x6, x5<- x4 * arg2[3]
mulx rdx, r15, [ r10 + 0x0 ]; x12, x11<- x4 * arg2[0]
mov rcx, [ rsi + 0x10 ]; load m64 x2 to register64
xor r8, r8
adox rbx, rdx
mov rdx, rcx; x2 to rdx
mulx rcx, r9, [ r10 + 0x0 ]; x107, x106<- x2 * arg2[0]
adox r12, r11
mulx r11, r8, [ r10 + 0x18 ]; x101, x100<- x2 * arg2[3]
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov [ rsp + 0x8 ], r9; spilling x106 to mem
mulx rdi, r9, [ r10 + 0x10 ]; x103, x102<- x2 * arg2[2]
mov [ rsp + 0x10 ], r12; spilling x15 to mem
mulx rdx, r12, [ r10 + 0x8 ]; x105, x104<- x2 * arg2[1]
adcx r12, rcx
adox r14, rax
adcx r9, rdx
adcx r8, rdi
mov rax, 0x0 ; moving imm to reg
adox r13, rax
mov rdx, rbp; x1 to rdx
mulx rbp, rcx, [ r10 + 0x0 ]; x54, x53<- x1 * arg2[0]
adc r11, 0x0
mulx rdi, rax, [ r10 + 0x18 ]; x48, x47<- x1 * arg2[3]
mov [ rsp + 0x18 ], r11; spilling x114 to mem
mov [ rsp + 0x20 ], r8; spilling x112 to mem
mulx r11, r8, [ r10 + 0x8 ]; x52, x51<- x1 * arg2[1]
mov [ rsp + 0x28 ], r9; spilling x110 to mem
mulx rdx, r9, [ r10 + 0x10 ]; x50, x49<- x1 * arg2[2]
mov [ rsp + 0x30 ], r13; spilling x19 to mem
mov r13, [ rsi + 0x18 ]; load m64 x3 to register64
test al, al
adox r8, rbp
adox r9, r11
adox rax, rdx
mov rdx, r13; x3 to rdx
mulx r13, rbp, [ r10 + 0x10 ]; x156, x155<- x3 * arg2[2]
mov [ rsp + 0x38 ], rax; spilling x59 to mem
mulx r11, rax, [ r10 + 0x18 ]; x154, x153<- x3 * arg2[3]
mov [ rsp + 0x40 ], r12; spilling x108 to mem
mov [ rsp + 0x48 ], r9; spilling x57 to mem
mulx r12, r9, [ r10 + 0x8 ]; x158, x157<- x3 * arg2[1]
mov [ rsp + 0x50 ], r14; spilling x17 to mem
mov r14, 0x0 ; moving imm to reg
adox rdi, r14
mulx rdx, r14, [ r10 + 0x0 ]; x160, x159<- x3 * arg2[0]
adcx r9, rdx
adcx rbp, r12
adcx rax, r13
mov r13, 0xd838091dd2253531 ; moving imm to reg
mov rdx, r15; x11 to rdx
mulx r15, r12, r13; _, x20<- x11 * 0xd838091dd2253531
adc r11, 0x0
mov r15, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r15; 0xffffffffffffffff, swapping with x11, which is currently in rdx
mov [ rsp + 0x58 ], r11; spilling x167 to mem
mulx r13, r11, r12; x27, x26<- x20 * 0xffffffffffffffff
mov rdx, 0xfffffffefffffc2f ; moving imm to reg
mov [ rsp + 0x60 ], rax; spilling x165 to mem
mov [ rsp + 0x68 ], rbp; spilling x163 to mem
mulx rax, rbp, r12; x29, x28<- x20 * 0xfffffffefffffc2f
test al, al
adox rbp, r15
adcx r11, rax
adox r11, rbx
seto bpl; spill OF x40 to reg (rbp)
mov r15, -0x2 ; moving imm to reg
inc r15; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rcx, r11
mov rbx, 0xd838091dd2253531 ; moving imm to reg
xchg rdx, rbx; 0xd838091dd2253531, swapping with 0xfffffffefffffc2f, which is currently in rdx
mulx rax, r11, rcx; _, x72<- x62 * 0xd838091dd2253531
xchg rdx, r11; x72, swapping with 0xd838091dd2253531, which is currently in rdx
mulx rax, r15, rbx; x81, x80<- x72 * 0xfffffffefffffc2f
mov rbx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x70 ], r9; spilling x161 to mem
mulx r11, r9, rbx; x75, x74<- x72 * 0xffffffffffffffff
mov [ rsp + 0x78 ], rdi; spilling x61 to mem
mov [ rsp + 0x80 ], r14; spilling x159 to mem
mulx rdi, r14, rbx; x79, x78<- x72 * 0xffffffffffffffff
seto bl; spill OF x63 to reg (rbx)
mov [ rsp + 0x88 ], r8; spilling x55 to mem
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, rax
mov rax, 0xffffffffffffffff ; moving imm to reg
mulx rdx, r8, rax; x77, x76<- x72 * 0xffffffffffffffff
adox r8, rdi
adox r9, rdx
mov rdi, 0x0 ; moving imm to reg
adox r11, rdi
mov rdx, rax; 0xffffffffffffffff to rdx
mulx rax, rdi, r12; x25, x24<- x20 * 0xffffffffffffffff
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, rcx
adcx rdi, r13
setc r15b; spill CF x33 to reg (r15)
clc;
movzx rbp, bpl
adcx rbp, rdx; loading flag
adcx rdi, [ rsp + 0x10 ]
setc r13b; spill CF x42 to reg (r13)
clc;
movzx rbx, bl
adcx rbx, rdx; loading flag
adcx rdi, [ rsp + 0x88 ]
adox r14, rdi
setc bpl; spill CF x65 to reg (rbp)
clc;
adcx r14, [ rsp + 0x8 ]
mov rcx, 0xd838091dd2253531 ; moving imm to reg
mov rdx, rcx; 0xd838091dd2253531 to rdx
mulx rcx, rbx, r14; _, x125<- x115 * 0xd838091dd2253531
mov rcx, 0xfffffffefffffc2f ; moving imm to reg
xchg rdx, rcx; 0xfffffffefffffc2f, swapping with 0xd838091dd2253531, which is currently in rdx
mulx rdi, rcx, rbx; x134, x133<- x125 * 0xfffffffefffffc2f
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x90 ], r11; spilling x88 to mem
mulx r12, r11, r12; x23, x22<- x20 * 0xffffffffffffffff
setc dl; spill CF x116 to reg (rdx)
clc;
mov [ rsp + 0x98 ], r9; spilling x86 to mem
mov r9, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, r9; loading flag
adcx rax, r11
setc r15b; spill CF x35 to reg (r15)
clc;
movzx r13, r13b
adcx r13, r9; loading flag
adcx rax, [ rsp + 0x50 ]
setc r13b; spill CF x44 to reg (r13)
clc;
movzx rbp, bpl
adcx rbp, r9; loading flag
adcx rax, [ rsp + 0x48 ]
setc bpl; spill CF x67 to reg (rbp)
clc;
adcx rcx, r14
adox r8, rax
seto cl; spill OF x94 to reg (rcx)
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
movzx rdx, dl
adox rdx, r14; loading flag
adox r8, [ rsp + 0x40 ]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mulx r11, rax, rbx; x132, x131<- x125 * 0xffffffffffffffff
seto r14b; spill OF x118 to reg (r14)
mov rdx, -0x3 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rax, rdi
adcx rax, r8
setc dil; spill CF x145 to reg (rdi)
clc;
adcx rax, [ rsp + 0x80 ]
mov r8, 0xd838091dd2253531 ; moving imm to reg
mov rdx, r8; 0xd838091dd2253531 to rdx
mulx r8, r9, rax; _, x178<- x168 * 0xd838091dd2253531
mov r8, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r9; x178, swapping with 0xd838091dd2253531, which is currently in rdx
mov [ rsp + 0xa0 ], rsi; spilling arg1 to mem
mulx r9, rsi, r8; x181, x180<- x178 * 0xffffffffffffffff
mov byte [ rsp + 0xa8 ], dil; spilling byte x145 to mem
mov [ rsp + 0xb0 ], r11; spilling x132 to mem
mulx rdi, r11, r8; x183, x182<- x178 * 0xffffffffffffffff
mov byte [ rsp + 0xb8 ], r14b; spilling byte x118 to mem
mov byte [ rsp + 0xc0 ], cl; spilling byte x94 to mem
mulx r14, rcx, r8; x185, x184<- x178 * 0xffffffffffffffff
movzx r8, r15b; x36, copying x35 here, cause x35 is needed in a reg for other than x36, namely all: , x36, size: 1
lea r8, [ r8 + r12 ]
mov r12, 0xfffffffefffffc2f ; moving imm to reg
mulx rdx, r15, r12; x187, x186<- x178 * 0xfffffffefffffc2f
seto r12b; spill OF x136 to reg (r12)
mov byte [ rsp + 0xc8 ], bpl; spilling byte x67 to mem
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, rax
setc r15b; spill CF x169 to reg (r15)
clc;
adcx rcx, rdx
adcx r11, r14
adcx rsi, rdi
mov rax, 0x0 ; moving imm to reg
adcx r9, rax
clc;
movzx r13, r13b
adcx r13, rbp; loading flag
adcx r8, [ rsp + 0x30 ]
setc r13b; spill CF x46 to reg (r13)
movzx rdi, byte [ rsp + 0xc8 ]; load byte memx67 to register64
clc;
adcx rdi, rbp; loading flag
adcx r8, [ rsp + 0x38 ]
setc dil; spill CF x69 to reg (rdi)
movzx r14, byte [ rsp + 0xc0 ]; load byte memx94 to register64
clc;
adcx r14, rbp; loading flag
adcx r8, [ rsp + 0x98 ]
setc r14b; spill CF x96 to reg (r14)
movzx rdx, byte [ rsp + 0xb8 ]; load byte memx118 to register64
clc;
adcx rdx, rbp; loading flag
adcx r8, [ rsp + 0x28 ]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mulx rax, rbp, rbx; x130, x129<- x125 * 0xffffffffffffffff
setc dl; spill CF x120 to reg (rdx)
clc;
mov [ rsp + 0xd0 ], r10; spilling arg2 to mem
mov r10, -0x1 ; moving imm to reg
movzx r12, r12b
adcx r12, r10; loading flag
adcx rbp, [ rsp + 0xb0 ]
movzx r12, r13b; x70, copying x46 here, cause x46 is needed in a reg for other than x70, namely all: , x70--x71, size: 1
setc r10b; spill CF x138 to reg (r10)
clc;
mov [ rsp + 0xd8 ], r9; spilling x194 to mem
mov r9, -0x1 ; moving imm to reg
movzx rdi, dil
adcx rdi, r9; loading flag
adcx r12, [ rsp + 0x78 ]
setc r13b; spill CF x71 to reg (r13)
movzx rdi, byte [ rsp + 0xa8 ]; load byte memx145 to register64
clc;
adcx rdi, r9; loading flag
adcx r8, rbp
setc dil; spill CF x147 to reg (rdi)
clc;
movzx r15, r15b
adcx r15, r9; loading flag
adcx r8, [ rsp + 0x70 ]
adox rcx, r8
setc r15b; spill CF x171 to reg (r15)
clc;
movzx r14, r14b
adcx r14, r9; loading flag
adcx r12, [ rsp + 0x90 ]
movzx r14, r13b; x99, copying x71 here, cause x71 is needed in a reg for other than x99, namely all: , x99, size: 1
mov rbp, 0x0 ; moving imm to reg
adcx r14, rbp
seto r13b; spill OF x198 to reg (r13)
mov r8, rcx; x206, copying x197 here, cause x197 is needed in a reg for other than x206, namely all: , x216, x206--x207, size: 2
mov r9, 0xfffffffefffffc2f ; moving imm to reg
sub r8, r9
dec rbp; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx rdx, dl
adox rdx, rbp; loading flag
adox r12, [ rsp + 0x20 ]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mulx rbx, rbp, rbx; x128, x127<- x125 * 0xffffffffffffffff
mov r9, [ rsp + 0x18 ]; x123, copying x114 here, cause x114 is needed in a reg for other than x123, namely all: , x123--x124, size: 1
adox r9, r14
setc r14b; spill CF x207 to reg (r14)
clc;
mov rdx, -0x1 ; moving imm to reg
movzx r10, r10b
adcx r10, rdx; loading flag
adcx rax, rbp
seto r10b; spill OF x124 to reg (r10)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx rdi, dil
adox rdi, rbp; loading flag
adox r12, rax
adcx rbx, rdx
adox rbx, r9
movzx rdi, r10b; x152, copying x124 here, cause x124 is needed in a reg for other than x152, namely all: , x152, size: 1
adox rdi, rdx
add r15b, 0x7F; load flag from rm/8 into OF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
seto r15b; since that has deps, resore it whereever it was
adox r12, [ rsp + 0x68 ]
mov r15, [ rsp + 0x60 ]; x174, copying x165 here, cause x165 is needed in a reg for other than x174, namely all: , x174--x175, size: 1
adox r15, rbx
movzx r13, r13b
adcx r13, rbp; loading flag
adcx r12, r11
mov r11, [ rsp + 0x58 ]; x176, copying x167 here, cause x167 is needed in a reg for other than x176, namely all: , x176--x177, size: 1
adox r11, rdi
adcx rsi, r15
mov r13, [ rsp + 0xd8 ]; x203, copying x194 here, cause x194 is needed in a reg for other than x203, namely all: , x203--x204, size: 1
adcx r13, r11
seto r10b; spill OF x205 to reg (r10)
adc r10b, 0x0
movzx r10, r10b
movzx r9, r14b; x207, copying x207 here, cause x207 is needed in a reg for other than x207, namely all: , x208--x209, size: 1
add r9, -0x1
mov r14, r12; x208, copying x199 here, cause x199 is needed in a reg for other than x208, namely all: , x217, x208--x209, size: 2
mov r9, 0xffffffffffffffff ; moving imm to reg
sbb r14, r9
mov rax, rsi; x210, copying x201 here, cause x201 is needed in a reg for other than x210, namely all: , x210--x211, x218, size: 2
sbb rax, r9
mov rbx, r13; x212, copying x203 here, cause x203 is needed in a reg for other than x212, namely all: , x212--x213, x219, size: 2
sbb rbx, r9
movzx rdi, r10b; _, copying x205 here, cause x205 is needed in a reg for other than _, namely all: , _--x215, size: 1
sbb rdi, 0x00000000
cmovc rax, rsi; if CF, x218<- x201 (nzVar)
cmovc r14, r12; if CF, x217<- x199 (nzVar)
mov r15, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r15 + 0x10 ], rax; out1[2] = x218
cmovc r8, rcx; if CF, x216<- x197 (nzVar)
mov [ r15 + 0x8 ], r14; out1[1] = x217
mov [ r15 + 0x0 ], r8; out1[0] = x216
cmovc rbx, r13; if CF, x219<- x203 (nzVar)
mov [ r15 + 0x18 ], rbx; out1[3] = x219
mov rbx, [ rsp + 0xe0 ]; restoring from stack
mov rbp, [ rsp + 0xe8 ]; restoring from stack
mov r12, [ rsp + 0xf0 ]; restoring from stack
mov r13, [ rsp + 0xf8 ]; restoring from stack
mov r14, [ rsp + 0x100 ]; restoring from stack
mov r15, [ rsp + 0x108 ]; restoring from stack
add rsp, 0x110 
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; clocked at 2600 MHz
; first cyclecount 99.16, best 81.88235294117646, lastGood 82.95049504950495
; seed 2924025841174363 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1243023 ms / 60000 runs=> 20.71705ms/run
; Time spent for assembling and measureing (initial batch_size=101, initial num_batches=101): 184743 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.14862395949230223
; number reverted permutation/ tried permutation: 24451 / 29698 =82.332%
; number reverted decision/ tried decision: 21822 / 30303 =72.013%