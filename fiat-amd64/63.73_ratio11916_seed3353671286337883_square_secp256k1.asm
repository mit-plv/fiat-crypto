SECTION .text
	GLOBAL square_secp256k1
square_secp256k1:
sub rsp, 0xf8 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0xc8 ], rbx; saving to stack
mov [ rsp + 0xd0 ], rbp; saving to stack
mov [ rsp + 0xd8 ], r12; saving to stack
mov [ rsp + 0xe0 ], r13; saving to stack
mov [ rsp + 0xe8 ], r14; saving to stack
mov [ rsp + 0xf0 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x4 to register64
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r10, r11, rax; x12, x11<- x4 * arg1[0]
mov rbx, 0xd838091dd2253531 ; moving imm to reg
mov rdx, rbx; 0xd838091dd2253531 to rdx
mulx rbx, rbp, r11; _, x20<- x11 * 0xd838091dd2253531
mov rbx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbp; x20, swapping with 0xd838091dd2253531, which is currently in rdx
mulx r12, r13, rbx; x25, x24<- x20 * 0xffffffffffffffff
mulx r14, r15, rbx; x27, x26<- x20 * 0xffffffffffffffff
mulx rcx, r8, rbx; x23, x22<- x20 * 0xffffffffffffffff
mov r9, 0xfffffffefffffc2f ; moving imm to reg
mulx rdx, rbx, r9; x29, x28<- x20 * 0xfffffffefffffc2f
xor rbp, rbp
adox r15, rdx
mov rdx, rax; x4 to rdx
mulx rax, rbp, [ rsi + 0x8 ]; x10, x9<- x4 * arg1[1]
mov r9, [ rsi + 0x8 ]; load m64 x1 to register64
adcx rbp, r10
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r10, rdi, [ rsi + 0x18 ]; x6, x5<- x4 * arg1[3]
adox r13, r14
mulx rdx, r14, [ rsi + 0x10 ]; x8, x7<- x4 * arg1[2]
adcx r14, rax
adox r8, r12
mov r12, 0x0 ; moving imm to reg
adox rcx, r12
mov rax, -0x3 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbx, r11
adcx rdi, rdx
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rbx, r11, r9; x54, x53<- x1 * arg1[0]
adcx r10, r12
adox r15, rbp
clc;
adcx r11, r15
adox r13, r14
mov rdx, 0xd838091dd2253531 ; moving imm to reg
mulx rbp, r14, r11; _, x72<- x62 * 0xd838091dd2253531
mov rbp, 0xfffffffefffffc2f ; moving imm to reg
xchg rdx, rbp; 0xfffffffefffffc2f, swapping with 0xd838091dd2253531, which is currently in rdx
mulx r15, r12, r14; x81, x80<- x72 * 0xfffffffefffffc2f
seto al; spill OF x42 to reg (rax)
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, r11
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r12, r11, r9; x52, x51<- x1 * arg1[1]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x8 ], rcx; spilling x36 to mem
mulx rbp, rcx, r14; x79, x78<- x72 * 0xffffffffffffffff
setc dl; spill CF x63 to reg (rdx)
clc;
adcx rcx, r15
setc r15b; spill CF x83 to reg (r15)
clc;
adcx r11, rbx
mov rbx, [ rsi + 0x10 ]; load m64 x2 to register64
mov [ rsp + 0x10 ], r10; spilling x19 to mem
setc r10b; spill CF x56 to reg (r10)
clc;
mov [ rsp + 0x18 ], r8; spilling x34 to mem
mov r8, -0x1 ; moving imm to reg
movzx rdx, dl
adcx rdx, r8; loading flag
adcx r13, r11
mov rdx, rbx; x2 to rdx
mulx rbx, r11, [ rsi + 0x0 ]; x107, x106<- x2 * arg1[0]
adox rcx, r13
seto r13b; spill OF x92 to reg (r13)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r11, rcx
mov rcx, 0xd838091dd2253531 ; moving imm to reg
xchg rdx, rcx; 0xd838091dd2253531, swapping with x2, which is currently in rdx
mov byte [ rsp + 0x20 ], r13b; spilling byte x92 to mem
mulx r8, r13, r11; _, x125<- x115 * 0xd838091dd2253531
mov r8, 0xfffffffefffffc2f ; moving imm to reg
xchg rdx, r8; 0xfffffffefffffc2f, swapping with 0xd838091dd2253531, which is currently in rdx
mov [ rsp + 0x28 ], rbx; spilling x107 to mem
mulx r8, rbx, r13; x134, x133<- x125 * 0xfffffffefffffc2f
setc dl; spill CF x65 to reg (rdx)
clc;
adcx rbx, r11
mov bl, dl; preserving value of x65 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x30 ], r8; spilling x134 to mem
mulx r11, r8, r9; x50, x49<- x1 * arg1[2]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x38 ], r11; spilling x50 to mem
mov byte [ rsp + 0x40 ], bl; spilling byte x65 to mem
mulx r11, rbx, r14; x77, x76<- x72 * 0xffffffffffffffff
setc dl; spill CF x143 to reg (rdx)
clc;
mov [ rsp + 0x48 ], r11; spilling x77 to mem
mov r11, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, r11; loading flag
adcx rbp, rbx
setc r15b; spill CF x85 to reg (r15)
clc;
movzx r10, r10b
adcx r10, r11; loading flag
adcx r12, r8
setc r10b; spill CF x58 to reg (r10)
clc;
movzx rax, al
adcx rax, r11; loading flag
adcx rdi, [ rsp + 0x18 ]
setc al; spill CF x44 to reg (rax)
movzx r8, byte [ rsp + 0x40 ]; load byte memx65 to register64
clc;
adcx r8, r11; loading flag
adcx rdi, r12
mov r8b, dl; preserving value of x143 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx rbx, r12, rcx; x105, x104<- x2 * arg1[1]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x50 ], rbx; spilling x105 to mem
mulx r11, rbx, r13; x132, x131<- x125 * 0xffffffffffffffff
setc dl; spill CF x67 to reg (rdx)
clc;
adcx r12, [ rsp + 0x28 ]
mov [ rsp + 0x58 ], r11; spilling x132 to mem
mov r11, [ rsi + 0x18 ]; load m64 x3 to register64
mov byte [ rsp + 0x60 ], dl; spilling byte x67 to mem
setc dl; spill CF x109 to reg (rdx)
mov byte [ rsp + 0x68 ], r15b; spilling byte x85 to mem
movzx r15, byte [ rsp + 0x20 ]; load byte memx92 to register64
clc;
mov byte [ rsp + 0x70 ], r10b; spilling byte x58 to mem
mov r10, -0x1 ; moving imm to reg
adcx r15, r10; loading flag
adcx rdi, rbp
adox r12, rdi
mov r15b, dl; preserving value of x109 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx rbp, rdi, r11; x160, x159<- x3 * arg1[0]
setc dl; spill CF x94 to reg (rdx)
clc;
adcx rbx, [ rsp + 0x30 ]
setc r10b; spill CF x136 to reg (r10)
clc;
mov [ rsp + 0x78 ], rbp; spilling x160 to mem
mov rbp, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, rbp; loading flag
adcx r12, rbx
setc r8b; spill CF x145 to reg (r8)
clc;
adcx rdi, r12
mov rbx, 0xd838091dd2253531 ; moving imm to reg
xchg rdx, rbx; 0xd838091dd2253531, swapping with x94, which is currently in rdx
mulx r12, rbp, rdi; _, x178<- x168 * 0xd838091dd2253531
mov r12, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r12; 0xffffffffffffffff, swapping with 0xd838091dd2253531, which is currently in rdx
mov byte [ rsp + 0x80 ], r8b; spilling byte x145 to mem
mulx r12, r8, rbp; x181, x180<- x178 * 0xffffffffffffffff
mov rdx, 0xfffffffefffffc2f ; moving imm to reg
mov byte [ rsp + 0x88 ], r10b; spilling byte x136 to mem
mov byte [ rsp + 0x90 ], r15b; spilling byte x109 to mem
mulx r10, r15, rbp; x187, x186<- x178 * 0xfffffffefffffc2f
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x98 ], r15; spilling x186 to mem
mov byte [ rsp + 0xa0 ], bl; spilling byte x94 to mem
mulx r15, rbx, rbp; x183, x182<- x178 * 0xffffffffffffffff
mov byte [ rsp + 0xa8 ], al; spilling byte x44 to mem
mulx rbp, rax, rbp; x185, x184<- x178 * 0xffffffffffffffff
setc dl; spill CF x169 to reg (rdx)
clc;
adcx rax, r10
adcx rbx, rbp
adcx r8, r15
mov r10, 0x0 ; moving imm to reg
adcx r12, r10
mov r15, [ rsp + 0x8 ]; load m64 x36 to register64
movzx rbp, byte [ rsp + 0xa8 ]; load byte memx44 to register64
clc;
mov r10, -0x1 ; moving imm to reg
adcx rbp, r10; loading flag
adcx r15, [ rsp + 0x10 ]
mov bpl, dl; preserving value of x169 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx r9, r10, r9; x48, x47<- x1 * arg1[3]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0xb0 ], r12; spilling x194 to mem
mulx r14, r12, r14; x75, x74<- x72 * 0xffffffffffffffff
setc dl; spill CF x46 to reg (rdx)
mov [ rsp + 0xb8 ], r8; spilling x192 to mem
movzx r8, byte [ rsp + 0x70 ]; load byte memx58 to register64
clc;
mov [ rsp + 0xc0 ], rbx; spilling x190 to mem
mov rbx, -0x1 ; moving imm to reg
adcx r8, rbx; loading flag
adcx r10, [ rsp + 0x38 ]
mov r8, 0x0 ; moving imm to reg
adcx r9, r8
movzx r8, byte [ rsp + 0x68 ]; load byte memx85 to register64
clc;
adcx r8, rbx; loading flag
adcx r12, [ rsp + 0x48 ]
mov r8, 0x0 ; moving imm to reg
adcx r14, r8
movzx r8, byte [ rsp + 0x60 ]; load byte memx67 to register64
clc;
adcx r8, rbx; loading flag
adcx r15, r10
setc r8b; spill CF x69 to reg (r8)
movzx r10, byte [ rsp + 0xa0 ]; load byte memx94 to register64
clc;
adcx r10, rbx; loading flag
adcx r15, r12
seto r10b; spill OF x118 to reg (r10)
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
movzx rdx, dl
movzx r8, r8b
adox r8, r12; loading flag
adox r9, rdx
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r8, rbx, rcx; x103, x102<- x2 * arg1[2]
adcx r14, r9
setc dl; spill CF x98 to reg (rdx)
movzx r9, byte [ rsp + 0x90 ]; load byte memx109 to register64
clc;
adcx r9, r12; loading flag
adcx rbx, [ rsp + 0x50 ]
movzx r9, dl; x99, copying x98 here, cause x98 is needed in a reg for other than x99, namely all: , x99, size: 1
mov r12, 0x0 ; moving imm to reg
adox r9, r12
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rcx, r12, rcx; x101, x100<- x2 * arg1[3]
adcx r12, r8
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r8, -0x1 ; moving imm to reg
movzx r10, r10b
adox r10, r8; loading flag
adox r15, rbx
adox r12, r14
adcx rcx, rdx
mov r10, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r10; 0xffffffffffffffff, swapping with 0x0, which is currently in rdx
mulx r14, rbx, r13; x130, x129<- x125 * 0xffffffffffffffff
movzx r10, byte [ rsp + 0x88 ]; load byte memx136 to register64
clc;
adcx r10, r8; loading flag
adcx rbx, [ rsp + 0x58 ]
mulx r13, r10, r13; x128, x127<- x125 * 0xffffffffffffffff
adox rcx, r9
seto r9b; spill OF x124 to reg (r9)
movzx r8, byte [ rsp + 0x80 ]; load byte memx145 to register64
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r8, rdx; loading flag
adox r15, rbx
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r8, rbx, r11; x156, x155<- x3 * arg1[2]
adcx r10, r14
adox r10, r12
mov rdx, r11; x3 to rdx
mulx r11, r12, [ rsi + 0x8 ]; x158, x157<- x3 * arg1[1]
mov r14, 0x0 ; moving imm to reg
adcx r13, r14
adox r13, rcx
clc;
adcx r12, [ rsp + 0x78 ]
movzx rcx, r9b; x152, copying x124 here, cause x124 is needed in a reg for other than x152, namely all: , x152, size: 1
adox rcx, r14
mulx rdx, r9, [ rsi + 0x18 ]; x154, x153<- x3 * arg1[3]
dec r14; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx rbp, bpl
adox rbp, r14; loading flag
adox r15, r12
adcx rbx, r11
adox rbx, r10
seto bpl; spill OF x173 to reg (rbp)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rdi, [ rsp + 0x98 ]
adcx r9, r8
adox rax, r15
mov r8, [ rsp + 0xc0 ]; x199, copying x190 here, cause x190 is needed in a reg for other than x199, namely all: , x199--x200, size: 1
adox r8, rbx
adcx rdx, r14
seto r10b; spill OF x200 to reg (r10)
mov r11, rax; x206, copying x197 here, cause x197 is needed in a reg for other than x206, namely all: , x216, x206--x207, size: 2
mov r12, 0xfffffffefffffc2f ; moving imm to reg
sub r11, r12
mov r15, r8; x208, copying x199 here, cause x199 is needed in a reg for other than x208, namely all: , x217, x208--x209, size: 2
mov rbx, 0xffffffffffffffff ; moving imm to reg
sbb r15, rbx
dec r14; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx rbp, bpl
adox rbp, r14; loading flag
adox r13, r9
adox rdx, rcx
seto cl; spill OF x177 to reg (rcx)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx r10, r10b
adox r10, rbp; loading flag
adox r13, [ rsp + 0xb8 ]
mov r9, [ rsp + 0xb0 ]; x203, copying x194 here, cause x194 is needed in a reg for other than x203, namely all: , x203--x204, size: 1
adox r9, rdx
movzx r10, cl; x205, copying x177 here, cause x177 is needed in a reg for other than x205, namely all: , x205, size: 1
adox r10, r14
mov rcx, r13; x210, copying x201 here, cause x201 is needed in a reg for other than x210, namely all: , x218, x210--x211, size: 2
sbb rcx, rbx
mov rdx, r9; x212, copying x203 here, cause x203 is needed in a reg for other than x212, namely all: , x212--x213, x219, size: 2
sbb rdx, rbx
sbb r10, 0x00000000
cmovc rcx, r13; if CF, x218<- x201 (nzVar)
cmovc rdx, r9; if CF, x219<- x203 (nzVar)
cmovc r11, rax; if CF, x216<- x197 (nzVar)
mov r10, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r10 + 0x18 ], rdx; out1[3] = x219
mov [ r10 + 0x0 ], r11; out1[0] = x216
cmovc r15, r8; if CF, x217<- x199 (nzVar)
mov [ r10 + 0x8 ], r15; out1[1] = x217
mov [ r10 + 0x10 ], rcx; out1[2] = x218
mov rbx, [ rsp + 0xc8 ]; restoring from stack
mov rbp, [ rsp + 0xd0 ]; restoring from stack
mov r12, [ rsp + 0xd8 ]; restoring from stack
mov r13, [ rsp + 0xe0 ]; restoring from stack
mov r14, [ rsp + 0xe8 ]; restoring from stack
mov r15, [ rsp + 0xf0 ]; restoring from stack
add rsp, 0xf8 
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; clocked at 3600 MHz
; first cyclecount 85.535, best 63.465648854961835, lastGood 63.73076923076923
; seed 3353671286337883 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 747226 ms / 60000 runs=> 12.453766666666667ms/run
; Time spent for assembling and measureing (initial batch_size=131, initial num_batches=101): 137938 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.18460010759796902
; number reverted permutation/ tried permutation: 24026 / 29903 =80.346%
; number reverted decision/ tried decision: 22732 / 30098 =75.527%