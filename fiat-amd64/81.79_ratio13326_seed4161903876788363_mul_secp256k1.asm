SECTION .text
	GLOBAL mul_secp256k1
mul_secp256k1:
sub rsp, 0x100 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0xd0 ], rbx; saving to stack
mov [ rsp + 0xd8 ], rbp; saving to stack
mov [ rsp + 0xe0 ], r12; saving to stack
mov [ rsp + 0xe8 ], r13; saving to stack
mov [ rsp + 0xf0 ], r14; saving to stack
mov [ rsp + 0xf8 ], r15; saving to stack
mov rax, [ rsi + 0x18 ]; load m64 x3 to register64
mov r10, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x8 ]; saving arg2[1] in rdx.
mulx r11, rbx, rax; x158, x157<- x3 * arg2[1]
mov rbp, [ rsi + 0x0 ]; load m64 x4 to register64
mov rdx, rax; x3 to rdx
mulx rax, r12, [ r10 + 0x10 ]; x156, x155<- x3 * arg2[2]
mulx r13, r14, [ r10 + 0x0 ]; x160, x159<- x3 * arg2[0]
mulx rdx, r15, [ r10 + 0x18 ]; x154, x153<- x3 * arg2[3]
mov rcx, rdx; preserving value of x154 into a new reg
mov rdx, [ r10 + 0x0 ]; saving arg2[0] in rdx.
mulx r8, r9, rbp; x12, x11<- x4 * arg2[0]
test al, al
adox rbx, r13
adox r12, r11
adox r15, rax
mov r11, 0xd838091dd2253531 ; moving imm to reg
mov rdx, r11; 0xd838091dd2253531 to rdx
mulx r11, rax, r9; _, x20<- x11 * 0xd838091dd2253531
mov r11, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r11; 0xffffffffffffffff, swapping with 0xd838091dd2253531, which is currently in rdx
mulx r13, r11, rax; x27, x26<- x20 * 0xffffffffffffffff
mov rdx, 0xfffffffefffffc2f ; moving imm to reg
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov [ rsp + 0x8 ], r15; spilling x165 to mem
mulx rdi, r15, rax; x29, x28<- x20 * 0xfffffffefffffc2f
mov rdx, [ rsi + 0x8 ]; load m64 x1 to register64
mov [ rsp + 0x10 ], r12; spilling x163 to mem
mov r12, 0x0 ; moving imm to reg
adox rcx, r12
mov [ rsp + 0x18 ], rcx; spilling x167 to mem
mulx r12, rcx, [ r10 + 0x0 ]; x54, x53<- x1 * arg2[0]
mov [ rsp + 0x20 ], rbx; spilling x161 to mem
mov rbx, rdx; preserving value of x1 into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mov [ rsp + 0x28 ], r14; spilling x159 to mem
mov [ rsp + 0x30 ], r13; spilling x27 to mem
mulx r14, r13, rbp; x10, x9<- x4 * arg2[1]
adcx r15, r9
mov r15, -0x2 ; moving imm to reg
inc r15; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, rdi
seto r9b; spill OF x31 to reg (r9)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r13, r8
mov rdx, [ r10 + 0x8 ]; arg2[1] to rdx
mulx r8, rdi, rbx; x52, x51<- x1 * arg2[1]
adcx r11, r13
setc r13b; spill CF x40 to reg (r13)
clc;
adcx rcx, r11
mov r11, 0xd838091dd2253531 ; moving imm to reg
mov rdx, r11; 0xd838091dd2253531 to rdx
mulx r11, r15, rcx; _, x72<- x62 * 0xd838091dd2253531
mov r11, [ rsi + 0x10 ]; load m64 x2 to register64
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x38 ], r8; spilling x52 to mem
mov [ rsp + 0x40 ], r11; spilling x2 to mem
mulx r8, r11, r15; x79, x78<- x72 * 0xffffffffffffffff
mov [ rsp + 0x48 ], r8; spilling x79 to mem
mov [ rsp + 0x50 ], r11; spilling x78 to mem
mulx r8, r11, rax; x25, x24<- x20 * 0xffffffffffffffff
mov rdx, 0xfffffffefffffc2f ; moving imm to reg
mov [ rsp + 0x58 ], r8; spilling x25 to mem
mov byte [ rsp + 0x60 ], r13b; spilling byte x40 to mem
mulx r8, r13, r15; x81, x80<- x72 * 0xfffffffefffffc2f
setc dl; spill CF x63 to reg (rdx)
clc;
adcx rdi, r12
setc r12b; spill CF x56 to reg (r12)
clc;
adcx r13, rcx
mov r13b, dl; preserving value of x63 into a new reg
mov rdx, [ r10 + 0x10 ]; saving arg2[2] in rdx.
mov byte [ rsp + 0x68 ], r12b; spilling byte x56 to mem
mulx rcx, r12, rbp; x8, x7<- x4 * arg2[2]
mov [ rsp + 0x70 ], rcx; spilling x8 to mem
setc cl; spill CF x90 to reg (rcx)
clc;
mov [ rsp + 0x78 ], rdi; spilling x55 to mem
mov rdi, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, rdi; loading flag
adcx r11, [ rsp + 0x30 ]
adox r12, r14
setc r14b; spill CF x33 to reg (r14)
movzx r9, byte [ rsp + 0x60 ]; load byte memx40 to register64
clc;
adcx r9, rdi; loading flag
adcx r12, r11
mov rdx, [ r10 + 0x0 ]; arg2[0] to rdx
mulx r9, r11, [ rsp + 0x40 ]; x107, x106<- x2 * arg2[0]
setc dil; spill CF x42 to reg (rdi)
clc;
adcx r8, [ rsp + 0x50 ]
mov [ rsp + 0x80 ], r9; spilling x107 to mem
setc r9b; spill CF x83 to reg (r9)
clc;
mov byte [ rsp + 0x88 ], dil; spilling byte x42 to mem
mov rdi, -0x1 ; moving imm to reg
movzx r13, r13b
adcx r13, rdi; loading flag
adcx r12, [ rsp + 0x78 ]
setc r13b; spill CF x65 to reg (r13)
clc;
movzx rcx, cl
adcx rcx, rdi; loading flag
adcx r12, r8
setc cl; spill CF x92 to reg (rcx)
clc;
adcx r11, r12
mov r8, 0xd838091dd2253531 ; moving imm to reg
mov rdx, r11; x115 to rdx
mulx r11, r12, r8; _, x125<- x115 * 0xd838091dd2253531
mov r11, rdx; preserving value of x115 into a new reg
mov rdx, [ r10 + 0x18 ]; saving arg2[3] in rdx.
mulx rbp, rdi, rbp; x6, x5<- x4 * arg2[3]
mov r8, 0xfffffffefffffc2f ; moving imm to reg
mov rdx, r12; x125 to rdx
mov byte [ rsp + 0x90 ], cl; spilling byte x92 to mem
mulx r12, rcx, r8; x134, x133<- x125 * 0xfffffffefffffc2f
mov r8, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x98 ], rcx; spilling x133 to mem
mov byte [ rsp + 0xa0 ], r13b; spilling byte x65 to mem
mulx rcx, r13, r8; x132, x131<- x125 * 0xffffffffffffffff
setc r8b; spill CF x116 to reg (r8)
clc;
adcx r13, r12
mov r12, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0xa8 ], r13; spilling x135 to mem
mov byte [ rsp + 0xb0 ], r8b; spilling byte x116 to mem
mulx r13, r8, r12; x128, x127<- x125 * 0xffffffffffffffff
mov byte [ rsp + 0xb8 ], r9b; spilling byte x83 to mem
mulx rdx, r9, r12; x130, x129<- x125 * 0xffffffffffffffff
adcx r9, rcx
mov rcx, [ rsp + 0x70 ]; x17, copying x8 here, cause x8 is needed in a reg for other than x17, namely all: , x17--x18, size: 1
adox rcx, rdi
adcx r8, rdx
mov rdi, 0x0 ; moving imm to reg
adox rbp, rdi
mov rdx, r12; 0xffffffffffffffff to rdx
mulx r12, rdi, r15; x77, x76<- x72 * 0xffffffffffffffff
adc r13, 0x0
mov [ rsp + 0xc0 ], r13; spilling x141 to mem
mulx rax, r13, rax; x23, x22<- x20 * 0xffffffffffffffff
add r14b, 0x7F; load flag from rm/8 into OF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
seto r14b; since that has deps, resore it whereever it was
adox r13, [ rsp + 0x58 ]
movzx r14, byte [ rsp + 0x88 ]; load byte memx42 to register64
mov rdx, -0x1 ; moving imm to reg
adcx r14, rdx; loading flag
adcx rcx, r13
mov r14, 0x0 ; moving imm to reg
adox rax, r14
mov rdx, rbx; x1 to rdx
mulx rbx, r13, [ r10 + 0x10 ]; x50, x49<- x1 * arg2[2]
adcx rax, rbp
movzx rbp, byte [ rsp + 0xb8 ]; load byte memx83 to register64
dec r14; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
adox rbp, r14; loading flag
adox rdi, [ rsp + 0x48 ]
setc bpl; spill CF x46 to reg (rbp)
movzx r14, byte [ rsp + 0x68 ]; load byte memx56 to register64
clc;
mov [ rsp + 0xc8 ], r8; spilling x139 to mem
mov r8, -0x1 ; moving imm to reg
adcx r14, r8; loading flag
adcx r13, [ rsp + 0x38 ]
mulx rdx, r14, [ r10 + 0x18 ]; x48, x47<- x1 * arg2[3]
adcx r14, rbx
mov rbx, 0x0 ; moving imm to reg
adcx rdx, rbx
movzx rbx, byte [ rsp + 0xa0 ]; load byte memx65 to register64
clc;
adcx rbx, r8; loading flag
adcx rcx, r13
adcx r14, rax
movzx rbx, bpl; x70, copying x46 here, cause x46 is needed in a reg for other than x70, namely all: , x70--x71, size: 1
adcx rbx, rdx
mov rbp, 0xffffffffffffffff ; moving imm to reg
mov rdx, rbp; 0xffffffffffffffff to rdx
mulx r15, rbp, r15; x75, x74<- x72 * 0xffffffffffffffff
adox rbp, r12
setc r12b; spill CF x71 to reg (r12)
movzx rax, byte [ rsp + 0x90 ]; load byte memx92 to register64
clc;
adcx rax, r8; loading flag
adcx rcx, rdi
mov rax, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mulx rdi, r13, [ rsp + 0x40 ]; x105, x104<- x2 * arg2[1]
mov r8, 0x0 ; moving imm to reg
adox r15, r8
adcx rbp, r14
mov rdx, [ rsp + 0x40 ]; x2 to rdx
mulx r14, r8, [ r10 + 0x10 ]; x103, x102<- x2 * arg2[2]
adcx r15, rbx
movzx rbx, r12b; x99, copying x71 here, cause x71 is needed in a reg for other than x99, namely all: , x99, size: 1
adc rbx, 0x0
xor r12, r12
adox r13, [ rsp + 0x80 ]
adox r8, rdi
mulx rdx, rdi, [ r10 + 0x18 ]; x101, x100<- x2 * arg2[3]
adox rdi, r14
adcx r11, [ rsp + 0x98 ]
adox rdx, r12
movzx r11, byte [ rsp + 0xb0 ]; load byte memx116 to register64
dec r12; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
adox r11, r12; loading flag
adox rcx, r13
mov r11, [ rsp + 0xa8 ]; x144, copying x135 here, cause x135 is needed in a reg for other than x144, namely all: , x144--x145, size: 1
adcx r11, rcx
adox r8, rbp
adox rdi, r15
adcx r9, r8
adox rdx, rbx
mov rbp, [ rsp + 0xc8 ]; x148, copying x139 here, cause x139 is needed in a reg for other than x148, namely all: , x148--x149, size: 1
adcx rbp, rdi
mov r14, [ rsp + 0xc0 ]; x150, copying x141 here, cause x141 is needed in a reg for other than x150, namely all: , x150--x151, size: 1
adcx r14, rdx
setc r15b; spill CF x151 to reg (r15)
clc;
adcx r11, [ rsp + 0x28 ]
mov rbx, 0xd838091dd2253531 ; moving imm to reg
mov rdx, rbx; 0xd838091dd2253531 to rdx
mulx rbx, r13, r11; _, x178<- x168 * 0xd838091dd2253531
movzx rbx, r15b; x152, copying x151 here, cause x151 is needed in a reg for other than x152, namely all: , x152, size: 1
mov rcx, 0x0 ; moving imm to reg
adox rbx, rcx
xchg rdx, r13; x178, swapping with 0xd838091dd2253531, which is currently in rdx
mulx r8, rdi, rax; x185, x184<- x178 * 0xffffffffffffffff
mov r15, [ rsp + 0x20 ]; x170, copying x161 here, cause x161 is needed in a reg for other than x170, namely all: , x170--x171, size: 1
adcx r15, r9
mov r9, 0xfffffffefffffc2f ; moving imm to reg
mulx rcx, r12, r9; x187, x186<- x178 * 0xfffffffefffffc2f
mulx r9, r13, rax; x181, x180<- x178 * 0xffffffffffffffff
mov rax, -0x2 ; moving imm to reg
inc rax; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, r11
mov r12, 0xffffffffffffffff ; moving imm to reg
mulx rdx, r11, r12; x183, x182<- x178 * 0xffffffffffffffff
setc al; spill CF x171 to reg (rax)
clc;
adcx rdi, rcx
adcx r11, r8
adcx r13, rdx
adox rdi, r15
mov r8, 0x0 ; moving imm to reg
adcx r9, r8
seto r15b; spill OF x198 to reg (r15)
mov rcx, rdi; x206, copying x197 here, cause x197 is needed in a reg for other than x206, namely all: , x206--x207, x216, size: 2
mov rdx, 0xfffffffefffffc2f ; moving imm to reg
sub rcx, rdx
dec r8; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx rax, al
adox rax, r8; loading flag
adox rbp, [ rsp + 0x10 ]
setc al; spill CF x207 to reg (rax)
clc;
movzx r15, r15b
adcx r15, r8; loading flag
adcx rbp, r11
mov r11, [ rsp + 0x8 ]; x174, copying x165 here, cause x165 is needed in a reg for other than x174, namely all: , x174--x175, size: 1
adox r11, r14
mov r14, [ rsp + 0x18 ]; x176, copying x167 here, cause x167 is needed in a reg for other than x176, namely all: , x176--x177, size: 1
adox r14, rbx
adcx r13, r11
adcx r9, r14
seto bl; spill OF x205 to reg (rbx)
adc bl, 0x0
movzx rbx, bl
movzx r15, al; x207, copying x207 here, cause x207 is needed in a reg for other than x207, namely all: , x208--x209, size: 1
add r15, -0x1
mov rax, rbp; x208, copying x199 here, cause x199 is needed in a reg for other than x208, namely all: , x208--x209, x217, size: 2
sbb rax, r12
mov r15, r13; x210, copying x201 here, cause x201 is needed in a reg for other than x210, namely all: , x218, x210--x211, size: 2
sbb r15, r12
mov r11, r9; x212, copying x203 here, cause x203 is needed in a reg for other than x212, namely all: , x219, x212--x213, size: 2
sbb r11, r12
movzx r14, bl; _, copying x205 here, cause x205 is needed in a reg for other than _, namely all: , _--x215, size: 1
sbb r14, 0x00000000
cmovc rax, rbp; if CF, x217<- x199 (nzVar)
cmovc r11, r9; if CF, x219<- x203 (nzVar)
mov r14, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r14 + 0x18 ], r11; out1[3] = x219
cmovc rcx, rdi; if CF, x216<- x197 (nzVar)
cmovc r15, r13; if CF, x218<- x201 (nzVar)
mov [ r14 + 0x8 ], rax; out1[1] = x217
mov [ r14 + 0x0 ], rcx; out1[0] = x216
mov [ r14 + 0x10 ], r15; out1[2] = x218
mov rbx, [ rsp + 0xd0 ]; restoring from stack
mov rbp, [ rsp + 0xd8 ]; restoring from stack
mov r12, [ rsp + 0xe0 ]; restoring from stack
mov r13, [ rsp + 0xe8 ]; restoring from stack
mov r14, [ rsp + 0xf0 ]; restoring from stack
mov r15, [ rsp + 0xf8 ]; restoring from stack
add rsp, 0x100 
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; clocked at 4823 MHz
; first cyclecount 103.67, best 81.47826086956522, lastGood 81.79347826086956
; seed 4161903876788363 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 903731 ms / 60000 runs=> 15.062183333333333ms/run
; Time spent for assembling and measureing (initial batch_size=92, initial num_batches=101): 98482 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.10897269209532483
; number reverted permutation/ tried permutation: 23722 / 29887 =79.372%
; number reverted decision/ tried decision: 22376 / 30114 =74.304%