SECTION .text
	GLOBAL square_secp256k1
square_secp256k1:
sub rsp, 0xc0 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x90 ], rbx; saving to stack
mov [ rsp + 0x98 ], rbp; saving to stack
mov [ rsp + 0xa0 ], r12; saving to stack
mov [ rsp + 0xa8 ], r13; saving to stack
mov [ rsp + 0xb0 ], r14; saving to stack
mov [ rsp + 0xb8 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x4 to register64
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r10, r11, rax; x6, x5<- x4 * arg1[3]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rbx, rbp, rax; x12, x11<- x4 * arg1[0]
mov r12, 0xd838091dd2253531 ; moving imm to reg
mov rdx, r12; 0xd838091dd2253531 to rdx
mulx r12, r13, rbp; _, x20<- x11 * 0xd838091dd2253531
mov r12, rdx; preserving value of 0xd838091dd2253531 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r14, r15, rax; x10, x9<- x4 * arg1[1]
add r15, rbx; could be done better, if r0 has been u8 as well
mov rdx, 0xfffffffefffffc2f ; moving imm to reg
mulx rcx, r8, r13; x29, x28<- x20 * 0xfffffffefffffc2f
mov r9, rdx; preserving value of 0xfffffffefffffc2f into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx rax, rbx, rax; x8, x7<- x4 * arg1[2]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mulx r9, r12, r13; x27, x26<- x20 * 0xffffffffffffffff
adcx rbx, r14
adcx r11, rax
mov r14, [ rsi + 0x8 ]; load m64 x1 to register64
mov rax, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov [ rsp + 0x8 ], r11; spilling x17 to mem
mulx rdi, r11, r14; x54, x53<- x1 * arg1[0]
adc r10, 0x0
add r8, rbp; could be done better, if r0 has been u8 as well
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, rcx
adcx r12, r15
setc r8b; spill CF x40 to reg (r8)
clc;
adcx r11, r12
mov rbp, 0xd838091dd2253531 ; moving imm to reg
mov rdx, rbp; 0xd838091dd2253531 to rdx
mulx rbp, r15, r11; _, x72<- x62 * 0xd838091dd2253531
xchg rdx, rax; 0xffffffffffffffff, swapping with 0xd838091dd2253531, which is currently in rdx
mulx rbp, rcx, r13; x25, x24<- x20 * 0xffffffffffffffff
mulx r12, rax, r15; x79, x78<- x72 * 0xffffffffffffffff
mov rdx, 0xfffffffefffffc2f ; moving imm to reg
mov [ rsp + 0x10 ], r10; spilling x19 to mem
mov [ rsp + 0x18 ], r12; spilling x79 to mem
mulx r10, r12, r15; x81, x80<- x72 * 0xfffffffefffffc2f
adox rcx, r9
seto r9b; spill OF x33 to reg (r9)
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rax, r10
seto r10b; spill OF x83 to reg (r10)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, rdx; loading flag
adox rbx, rcx
mov rdx, r14; x1 to rdx
mulx r14, r8, [ rsi + 0x8 ]; x52, x51<- x1 * arg1[1]
seto cl; spill OF x42 to reg (rcx)
mov byte [ rsp + 0x20 ], r10b; spilling byte x83 to mem
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, rdi
adcx r8, rbx
mulx rdi, rbx, [ rsi + 0x10 ]; x50, x49<- x1 * arg1[2]
setc r10b; spill CF x65 to reg (r10)
clc;
adcx r12, r11
adcx rax, r8
mov r12, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r12; 0xffffffffffffffff, swapping with x1, which is currently in rdx
mulx r13, r11, r13; x23, x22<- x20 * 0xffffffffffffffff
setc r8b; spill CF x92 to reg (r8)
clc;
mov rdx, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, rdx; loading flag
adcx rbp, r11
mov r9, 0x0 ; moving imm to reg
adcx r13, r9
adox rbx, r14
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r12, r14, r12; x48, x47<- x1 * arg1[3]
adox r14, rdi
mov rdx, 0xffffffffffffffff ; moving imm to reg
mulx rdi, r11, r15; x77, x76<- x72 * 0xffffffffffffffff
mulx r15, r9, r15; x75, x74<- x72 * 0xffffffffffffffff
clc;
mov rdx, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, rdx; loading flag
adcx rbp, [ rsp + 0x8 ]
setc cl; spill CF x44 to reg (rcx)
clc;
movzx r10, r10b
adcx r10, rdx; loading flag
adcx rbp, rbx
mov r10, 0x0 ; moving imm to reg
adox r12, r10
movzx rbx, byte [ rsp + 0x20 ]; load byte memx83 to register64
dec r10; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
adox rbx, r10; loading flag
adox r11, [ rsp + 0x18 ]
adox r9, rdi
mov rdx, 0x0 ; moving imm to reg
adox r15, rdx
inc r10; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, rdx; loading flag
adox r13, [ rsp + 0x10 ]
adcx r14, r13
setc bl; spill CF x69 to reg (rbx)
clc;
movzx r8, r8b
adcx r8, rdx; loading flag
adcx rbp, r11
movzx r8, bl; x70, copying x69 here, cause x69 is needed in a reg for other than x70, namely all: , x70--x71, size: 1
adox r8, r12
adcx r9, r14
mov rdi, [ rsi + 0x10 ]; load m64 x2 to register64
adcx r15, r8
seto cl; spill OF x99 to reg (rcx)
adc cl, 0x0
movzx rcx, cl
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r12, r11, rdi; x107, x106<- x2 * arg1[0]
adox r11, rax
mov rdx, 0xd838091dd2253531 ; moving imm to reg
mulx rax, r13, r11; _, x125<- x115 * 0xd838091dd2253531
mov rax, rdx; preserving value of 0xd838091dd2253531 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx rbx, r14, rdi; x105, x104<- x2 * arg1[1]
mov rdx, 0xfffffffefffffc2f ; moving imm to reg
mulx r8, r10, r13; x134, x133<- x125 * 0xfffffffefffffc2f
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov byte [ rsp + 0x28 ], cl; spilling byte x99 to mem
mulx rax, rcx, r13; x132, x131<- x125 * 0xffffffffffffffff
mov rdx, [ rsi + 0x18 ]; load m64 x3 to register64
adcx rcx, r8
setc r8b; spill CF x136 to reg (r8)
clc;
adcx r14, r12
adox r14, rbp
seto bpl; spill OF x118 to reg (rbp)
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r10, r11
mulx r10, r11, [ rsi + 0x0 ]; x160, x159<- x3 * arg1[0]
adox rcx, r14
seto r14b; spill OF x145 to reg (r14)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r11, rcx
mov rcx, rdx; preserving value of x3 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x30 ], r15; spilling x97 to mem
mulx r12, r15, rdi; x103, x102<- x2 * arg1[2]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x38 ], r12; spilling x103 to mem
mov byte [ rsp + 0x40 ], r14b; spilling byte x145 to mem
mulx r12, r14, r13; x130, x129<- x125 * 0xffffffffffffffff
mov rdx, 0xd838091dd2253531 ; moving imm to reg
mov [ rsp + 0x48 ], r12; spilling x130 to mem
mov [ rsp + 0x50 ], r9; spilling x95 to mem
mulx r12, r9, r11; _, x178<- x168 * 0xd838091dd2253531
seto r12b; spill OF x169 to reg (r12)
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r8, r8b
adox r8, rdx; loading flag
adox rax, r14
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r8, r14, rcx; x158, x157<- x3 * arg1[1]
adcx r15, rbx
mov rdx, 0xfffffffefffffc2f ; moving imm to reg
mov [ rsp + 0x58 ], r8; spilling x158 to mem
mulx rbx, r8, r9; x187, x186<- x178 * 0xfffffffefffffc2f
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x60 ], r8; spilling x186 to mem
mov byte [ rsp + 0x68 ], r12b; spilling byte x169 to mem
mulx r8, r12, r9; x185, x184<- x178 * 0xffffffffffffffff
seto dl; spill OF x138 to reg (rdx)
mov [ rsp + 0x70 ], r8; spilling x185 to mem
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, r10
setc r10b; spill CF x111 to reg (r10)
clc;
adcx r12, rbx
setc bl; spill CF x189 to reg (rbx)
clc;
movzx rbp, bpl
adcx rbp, r8; loading flag
adcx r15, [ rsp + 0x50 ]
setc bpl; spill CF x120 to reg (rbp)
movzx r8, byte [ rsp + 0x40 ]; load byte memx145 to register64
clc;
mov byte [ rsp + 0x78 ], bl; spilling byte x189 to mem
mov rbx, -0x1 ; moving imm to reg
adcx r8, rbx; loading flag
adcx r15, rax
setc r8b; spill CF x147 to reg (r8)
movzx rax, byte [ rsp + 0x68 ]; load byte memx169 to register64
clc;
adcx rax, rbx; loading flag
adcx r15, r14
setc al; spill CF x171 to reg (rax)
clc;
adcx r11, [ rsp + 0x60 ]
adcx r12, r15
mov r11b, dl; preserving value of x138 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx rdi, r14, rdi; x101, x100<- x2 * arg1[3]
setc dl; spill CF x198 to reg (rdx)
clc;
movzx r10, r10b
adcx r10, rbx; loading flag
adcx r14, [ rsp + 0x38 ]
mov r10b, dl; preserving value of x198 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r15, rbx, rcx; x156, x155<- x3 * arg1[2]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x80 ], r12; spilling x197 to mem
mulx r13, r12, r13; x128, x127<- x125 * 0xffffffffffffffff
setc dl; spill CF x113 to reg (rdx)
clc;
mov byte [ rsp + 0x88 ], r10b; spilling byte x198 to mem
mov r10, -0x1 ; moving imm to reg
movzx r11, r11b
adcx r11, r10; loading flag
adcx r12, [ rsp + 0x48 ]
mov r11, [ rsp + 0x58 ]; x163, copying x158 here, cause x158 is needed in a reg for other than x163, namely all: , x163--x164, size: 1
adox r11, rbx
mov rbx, 0x0 ; moving imm to reg
adcx r13, rbx
clc;
movzx rbp, bpl
adcx rbp, r10; loading flag
adcx r14, [ rsp + 0x30 ]
movzx rbp, dl; x114, copying x113 here, cause x113 is needed in a reg for other than x114, namely all: , x114, size: 1
lea rbp, [ rbp + rdi ]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rcx, rdi, rcx; x154, x153<- x3 * arg1[3]
movzx rdx, byte [ rsp + 0x28 ]; x123, copying x99 here, cause x99 is needed in a reg for other than x123, namely all: , x123--x124, size: 1
adcx rdx, rbp
setc bpl; spill CF x124 to reg (rbp)
clc;
movzx r8, r8b
adcx r8, r10; loading flag
adcx r14, r12
adox rdi, r15
adcx r13, rdx
adox rcx, rbx
mov r8, 0xffffffffffffffff ; moving imm to reg
mov rdx, r8; 0xffffffffffffffff to rdx
mulx r8, r15, r9; x181, x180<- x178 * 0xffffffffffffffff
movzx r12, bpl; x152, copying x124 here, cause x124 is needed in a reg for other than x152, namely all: , x152, size: 1
adc r12, 0x0
mulx r9, rbp, r9; x183, x182<- x178 * 0xffffffffffffffff
add al, 0xFF; load flag from rm/8 into CF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
setc al; since that has deps, resore it whereever it was
adcx r14, r11
movzx rax, byte [ rsp + 0x78 ]; load byte memx189 to register64
adox rax, r10; loading flag
adox rbp, [ rsp + 0x70 ]
adcx rdi, r13
adcx rcx, r12
adox r15, r9
setc al; spill CF x177 to reg (rax)
movzx r11, byte [ rsp + 0x88 ]; load byte memx198 to register64
clc;
adcx r11, r10; loading flag
adcx r14, rbp
adox r8, rbx
adcx r15, rdi
adcx r8, rcx
movzx r11, al; x205, copying x177 here, cause x177 is needed in a reg for other than x205, namely all: , x205, size: 1
adc r11, 0x0
mov r13, [ rsp + 0x80 ]; x206, copying x197 here, cause x197 is needed in a reg for other than x206, namely all: , x206--x207, x216, size: 2
mov r12, 0xfffffffefffffc2f ; moving imm to reg
sub r13, r12
mov r9, r14; x208, copying x199 here, cause x199 is needed in a reg for other than x208, namely all: , x208--x209, x217, size: 2
sbb r9, rdx
mov rbp, r15; x210, copying x201 here, cause x201 is needed in a reg for other than x210, namely all: , x218, x210--x211, size: 2
sbb rbp, rdx
mov rdi, r8; x212, copying x203 here, cause x203 is needed in a reg for other than x212, namely all: , x219, x212--x213, size: 2
sbb rdi, rdx
sbb r11, 0x00000000
cmovc rdi, r8; if CF, x219<- x203 (nzVar)
cmovc r9, r14; if CF, x217<- x199 (nzVar)
cmovc r13, [ rsp + 0x80 ]; if CF, x216<- x197 (nzVar)
mov r11, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r11 + 0x8 ], r9; out1[1] = x217
cmovc rbp, r15; if CF, x218<- x201 (nzVar)
mov [ r11 + 0x18 ], rdi; out1[3] = x219
mov [ r11 + 0x0 ], r13; out1[0] = x216
mov [ r11 + 0x10 ], rbp; out1[2] = x218
mov rbx, [ rsp + 0x90 ]; restoring from stack
mov rbp, [ rsp + 0x98 ]; restoring from stack
mov r12, [ rsp + 0xa0 ]; restoring from stack
mov r13, [ rsp + 0xa8 ]; restoring from stack
mov r14, [ rsp + 0xb0 ]; restoring from stack
mov r15, [ rsp + 0xb8 ]; restoring from stack
add rsp, 0xc0 
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; clocked at 2600 MHz
; first cyclecount 106.965, best 80.33962264150944, lastGood 81.16190476190476
; seed 4228455700821548 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1191372 ms / 60000 runs=> 19.8562ms/run
; Time spent for assembling and measureing (initial batch_size=105, initial num_batches=101): 193148 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.16212232619198705
; number reverted permutation/ tried permutation: 24468 / 30054 =81.413%
; number reverted decision/ tried decision: 22024 / 29947 =73.543%