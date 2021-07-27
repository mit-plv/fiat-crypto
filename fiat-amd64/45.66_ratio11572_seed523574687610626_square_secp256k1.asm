SECTION .text
	GLOBAL square_secp256k1
square_secp256k1:
sub rsp, 0xc8 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x98 ], rbx; saving to stack
mov [ rsp + 0xa0 ], rbp; saving to stack
mov [ rsp + 0xa8 ], r12; saving to stack
mov [ rsp + 0xb0 ], r13; saving to stack
mov [ rsp + 0xb8 ], r14; saving to stack
mov [ rsp + 0xc0 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x4 to register64
mov rdx, rax; x4 to rdx
mulx rax, r10, [ rsi + 0x8 ]; x10, x9<- x4 * arg1[1]
mulx r11, rbx, [ rsi + 0x0 ]; x12, x11<- x4 * arg1[0]
mulx rbp, r12, [ rsi + 0x18 ]; x6, x5<- x4 * arg1[3]
xor r13, r13
adox r10, r11
mulx rdx, r14, [ rsi + 0x10 ]; x8, x7<- x4 * arg1[2]
adox r14, rax
adox r12, rdx
mov r15, 0xd838091dd2253531 ; moving imm to reg
mov rdx, r15; 0xd838091dd2253531 to rdx
mulx r15, rcx, rbx; _, x20<- x11 * 0xd838091dd2253531
mov r15, 0xfffffffefffffc2f ; moving imm to reg
xchg rdx, rcx; x20, swapping with 0xd838091dd2253531, which is currently in rdx
mulx r8, r9, r15; x29, x28<- x20 * 0xfffffffefffffc2f
mov rax, 0xffffffffffffffff ; moving imm to reg
mulx r11, r13, rax; x27, x26<- x20 * 0xffffffffffffffff
mov rax, 0x0 ; moving imm to reg
adox rbp, rax
adcx r13, r8
mov r8, -0x3 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r9, rbx
adox r13, r10
mov r9, [ rsi + 0x8 ]; load m64 x1 to register64
mov rbx, rdx; preserving value of x20 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r10, rax, r9; x54, x53<- x1 * arg1[0]
seto dl; spill OF x40 to reg (rdx)
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rax, r13
xchg rdx, rcx; 0xd838091dd2253531, swapping with x40, which is currently in rdx
mulx r13, r8, rax; _, x72<- x62 * 0xd838091dd2253531
xchg rdx, r15; 0xfffffffefffffc2f, swapping with 0xd838091dd2253531, which is currently in rdx
mulx r13, r15, r8; x81, x80<- x72 * 0xfffffffefffffc2f
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov [ rsp + 0x8 ], rbp; spilling x19 to mem
mulx rdi, rbp, rbx; x25, x24<- x20 * 0xffffffffffffffff
adcx rbp, r11
setc r11b; spill CF x33 to reg (r11)
clc;
mov rdx, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, rdx; loading flag
adcx r14, rbp
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rcx, rbp, r9; x52, x51<- x1 * arg1[1]
setc dl; spill CF x42 to reg (rdx)
clc;
adcx r15, rax
setc r15b; spill CF x90 to reg (r15)
clc;
adcx rbp, r10
mov r10, [ rsi + 0x10 ]; load m64 x2 to register64
mov al, dl; preserving value of x42 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x10 ], r12; spilling x17 to mem
mov [ rsp + 0x18 ], rdi; spilling x25 to mem
mulx r12, rdi, r10; x107, x106<- x2 * arg1[0]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x20 ], r12; spilling x107 to mem
mov byte [ rsp + 0x28 ], al; spilling byte x42 to mem
mulx r12, rax, r8; x79, x78<- x72 * 0xffffffffffffffff
adox rbp, r14
setc r14b; spill CF x56 to reg (r14)
clc;
adcx rax, r13
setc r13b; spill CF x83 to reg (r13)
clc;
mov rdx, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, rdx; loading flag
adcx rbp, rax
setc r15b; spill CF x92 to reg (r15)
clc;
adcx rdi, rbp
mov rax, 0xd838091dd2253531 ; moving imm to reg
mov rdx, rax; 0xd838091dd2253531 to rdx
mulx rax, rbp, rdi; _, x125<- x115 * 0xd838091dd2253531
mov rax, rdx; preserving value of 0xd838091dd2253531 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov byte [ rsp + 0x30 ], r15b; spilling byte x92 to mem
mov [ rsp + 0x38 ], r12; spilling x79 to mem
mulx r15, r12, r9; x50, x49<- x1 * arg1[2]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mulx rbx, rax, rbx; x23, x22<- x20 * 0xffffffffffffffff
mov rdx, 0xfffffffefffffc2f ; moving imm to reg
mov [ rsp + 0x40 ], r15; spilling x50 to mem
mov [ rsp + 0x48 ], rbx; spilling x23 to mem
mulx r15, rbx, rbp; x134, x133<- x125 * 0xfffffffefffffc2f
setc dl; spill CF x116 to reg (rdx)
clc;
mov [ rsp + 0x50 ], r15; spilling x134 to mem
mov r15, -0x1 ; moving imm to reg
movzx r14, r14b
adcx r14, r15; loading flag
adcx rcx, r12
setc r14b; spill CF x58 to reg (r14)
clc;
movzx r11, r11b
adcx r11, r15; loading flag
adcx rax, [ rsp + 0x18 ]
setc r11b; spill CF x35 to reg (r11)
clc;
adcx rbx, rdi
setc bl; spill CF x143 to reg (rbx)
movzx rdi, byte [ rsp + 0x28 ]; load byte memx42 to register64
clc;
adcx rdi, r15; loading flag
adcx rax, [ rsp + 0x10 ]
mov dil, dl; preserving value of x116 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r12, r15, r10; x105, x104<- x2 * arg1[1]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x58 ], r12; spilling x105 to mem
mov byte [ rsp + 0x60 ], r14b; spilling byte x58 to mem
mulx r12, r14, r8; x77, x76<- x72 * 0xffffffffffffffff
adox rcx, rax
mov byte [ rsp + 0x68 ], bl; spilling byte x143 to mem
mulx rax, rbx, rbp; x132, x131<- x125 * 0xffffffffffffffff
seto dl; spill OF x67 to reg (rdx)
mov [ rsp + 0x70 ], rax; spilling x132 to mem
mov rax, 0x0 ; moving imm to reg
dec rax; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r13, r13b
adox r13, rax; loading flag
adox r14, [ rsp + 0x38 ]
setc r13b; spill CF x44 to reg (r13)
movzx rax, byte [ rsp + 0x30 ]; load byte memx92 to register64
clc;
mov byte [ rsp + 0x78 ], dl; spilling byte x67 to mem
mov rdx, -0x1 ; moving imm to reg
adcx rax, rdx; loading flag
adcx rcx, r14
setc al; spill CF x94 to reg (rax)
clc;
adcx r15, [ rsp + 0x20 ]
setc r14b; spill CF x109 to reg (r14)
clc;
movzx rdi, dil
adcx rdi, rdx; loading flag
adcx rcx, r15
movzx rdi, r11b; x36, copying x35 here, cause x35 is needed in a reg for other than x36, namely all: , x36, size: 1
mov r15, [ rsp + 0x48 ]; load m64 x23 to register64
lea rdi, [ rdi + r15 ]; r8/64 + m8
setc r15b; spill CF x118 to reg (r15)
clc;
adcx rbx, [ rsp + 0x50 ]
setc r11b; spill CF x136 to reg (r11)
clc;
movzx r13, r13b
adcx r13, rdx; loading flag
adcx rdi, [ rsp + 0x8 ]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r9, r13, r9; x48, x47<- x1 * arg1[3]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov byte [ rsp + 0x80 ], r11b; spilling byte x136 to mem
mulx r8, r11, r8; x75, x74<- x72 * 0xffffffffffffffff
adox r11, r12
setc r12b; spill CF x46 to reg (r12)
movzx rdx, byte [ rsp + 0x68 ]; load byte memx143 to register64
clc;
mov byte [ rsp + 0x88 ], r15b; spilling byte x118 to mem
mov r15, -0x1 ; moving imm to reg
adcx rdx, r15; loading flag
adcx rcx, rbx
setc dl; spill CF x145 to reg (rdx)
movzx rbx, byte [ rsp + 0x60 ]; load byte memx58 to register64
clc;
adcx rbx, r15; loading flag
adcx r13, [ rsp + 0x40 ]
mov rbx, 0x0 ; moving imm to reg
adcx r9, rbx
movzx rbx, byte [ rsp + 0x78 ]; load byte memx67 to register64
clc;
adcx rbx, r15; loading flag
adcx rdi, r13
movzx rbx, r12b; x70, copying x46 here, cause x46 is needed in a reg for other than x70, namely all: , x70--x71, size: 1
adcx rbx, r9
mov r12b, dl; preserving value of x145 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r13, r9, r10; x103, x102<- x2 * arg1[2]
mov rdx, 0x0 ; moving imm to reg
adox r8, rdx
dec rdx; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx rax, al
adox rax, rdx; loading flag
adox rdi, r11
setc r15b; spill CF x71 to reg (r15)
clc;
movzx r14, r14b
adcx r14, rdx; loading flag
adcx r9, [ rsp + 0x58 ]
mov rax, 0xffffffffffffffff ; moving imm to reg
mov rdx, rbp; x125 to rdx
mulx rbp, r14, rax; x128, x127<- x125 * 0xffffffffffffffff
mulx rdx, r11, rax; x130, x129<- x125 * 0xffffffffffffffff
adox r8, rbx
movzx rbx, r15b; x99, copying x71 here, cause x71 is needed in a reg for other than x99, namely all: , x99, size: 1
mov rax, 0x0 ; moving imm to reg
adox rbx, rax
movzx r15, byte [ rsp + 0x88 ]; load byte memx118 to register64
dec rax; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
adox r15, rax; loading flag
adox rdi, r9
seto r15b; spill OF x120 to reg (r15)
movzx r9, byte [ rsp + 0x80 ]; load byte memx136 to register64
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rax, -0x1 ; moving imm to reg
adox r9, rax; loading flag
adox r11, [ rsp + 0x70 ]
adox r14, rdx
mov rdx, r10; x2 to rdx
mulx rdx, r10, [ rsi + 0x18 ]; x101, x100<- x2 * arg1[3]
mov r9, 0x0 ; moving imm to reg
adox rbp, r9
adcx r10, r13
mov r13, [ rsi + 0x18 ]; load m64 x3 to register64
adc rdx, 0x0
add r15b, 0x7F; load flag from rm/8 into OF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
seto r15b; since that has deps, resore it whereever it was
adox r8, r10
adox rdx, rbx
movzx r12, r12b
adcx r12, rax; loading flag
adcx rdi, r11
adcx r14, r8
adcx rbp, rdx
seto r12b; spill OF x152 to reg (r12)
adc r12b, 0x0
movzx r12, r12b
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rbx, r15, r13; x160, x159<- x3 * arg1[0]
adox r15, rcx
mov rdx, 0xd838091dd2253531 ; moving imm to reg
mulx rcx, r11, r15; _, x178<- x168 * 0xd838091dd2253531
mov rcx, 0xfffffffefffffc2f ; moving imm to reg
xchg rdx, r11; x178, swapping with 0xd838091dd2253531, which is currently in rdx
mulx r10, r8, rcx; x187, x186<- x178 * 0xfffffffefffffc2f
mov r9, 0xffffffffffffffff ; moving imm to reg
mulx rax, rcx, r9; x183, x182<- x178 * 0xffffffffffffffff
mov byte [ rsp + 0x90 ], r12b; spilling byte x152 to mem
mulx r11, r12, r9; x185, x184<- x178 * 0xffffffffffffffff
adcx r12, r10
adcx rcx, r11
mulx rdx, r10, r9; x181, x180<- x178 * 0xffffffffffffffff
adcx r10, rax
mov rax, 0x0 ; moving imm to reg
adcx rdx, rax
clc;
adcx r8, r15
mov r8, rdx; preserving value of x194 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r15, r11, r13; x158, x157<- x3 * arg1[1]
setc dl; spill CF x196 to reg (rdx)
clc;
adcx r11, rbx
adox r11, rdi
seto dil; spill OF x171 to reg (rdi)
dec rax; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx rdx, dl
adox rdx, rax; loading flag
adox r11, r12
mov rdx, r13; x3 to rdx
mulx r13, rbx, [ rsi + 0x10 ]; x156, x155<- x3 * arg1[2]
adcx rbx, r15
mulx rdx, r12, [ rsi + 0x18 ]; x154, x153<- x3 * arg1[3]
adcx r12, r13
mov r15, 0x0 ; moving imm to reg
adcx rdx, r15
clc;
movzx rdi, dil
adcx rdi, rax; loading flag
adcx r14, rbx
adox rcx, r14
adcx r12, rbp
adox r10, r12
movzx rbp, byte [ rsp + 0x90 ]; x176, copying x152 here, cause x152 is needed in a reg for other than x176, namely all: , x176--x177, size: 1
adcx rbp, rdx
adox r8, rbp
seto dil; spill OF x205 to reg (rdi)
adc dil, 0x0
movzx rdi, dil
mov r13, r11; x206, copying x197 here, cause x197 is needed in a reg for other than x206, namely all: , x206--x207, x216, size: 2
mov rbx, 0xfffffffefffffc2f ; moving imm to reg
sub r13, rbx
mov rdx, rcx; x208, copying x199 here, cause x199 is needed in a reg for other than x208, namely all: , x217, x208--x209, size: 2
sbb rdx, r9
mov r14, r10; x210, copying x201 here, cause x201 is needed in a reg for other than x210, namely all: , x210--x211, x218, size: 2
sbb r14, r9
mov r12, r8; x212, copying x203 here, cause x203 is needed in a reg for other than x212, namely all: , x219, x212--x213, size: 2
sbb r12, r9
movzx rbp, dil; _, copying x205 here, cause x205 is needed in a reg for other than _, namely all: , _--x215, size: 1
sbb rbp, 0x00000000
cmovc r12, r8; if CF, x219<- x203 (nzVar)
cmovc r14, r10; if CF, x218<- x201 (nzVar)
cmovc r13, r11; if CF, x216<- x197 (nzVar)
mov rbp, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rbp + 0x18 ], r12; out1[3] = x219
cmovc rdx, rcx; if CF, x217<- x199 (nzVar)
mov [ rbp + 0x0 ], r13; out1[0] = x216
mov [ rbp + 0x10 ], r14; out1[2] = x218
mov [ rbp + 0x8 ], rdx; out1[1] = x217
mov rbx, [ rsp + 0x98 ]; restoring from stack
mov rbp, [ rsp + 0xa0 ]; restoring from stack
mov r12, [ rsp + 0xa8 ]; restoring from stack
mov r13, [ rsp + 0xb0 ]; restoring from stack
mov r14, [ rsp + 0xb8 ]; restoring from stack
mov r15, [ rsp + 0xc0 ]; restoring from stack
add rsp, 0xc8 
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; clocked at 1600 MHz
; first cyclecount 62.105, best 45.48947368421052, lastGood 45.65608465608466
; seed 523574687610626 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1280382 ms / 60000 runs=> 21.3397ms/run
; Time spent for assembling and measureing (initial batch_size=189, initial num_batches=101): 358217 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.27977353633524993
; number reverted permutation/ tried permutation: 24924 / 30066 =82.898%
; number reverted decision/ tried decision: 22268 / 29935 =74.388%