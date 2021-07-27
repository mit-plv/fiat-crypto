SECTION .text
	GLOBAL mul_secp256k1
mul_secp256k1:
sub rsp, 0x150 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x120 ], rbx; saving to stack
mov [ rsp + 0x128 ], rbp; saving to stack
mov [ rsp + 0x130 ], r12; saving to stack
mov [ rsp + 0x138 ], r13; saving to stack
mov [ rsp + 0x140 ], r14; saving to stack
mov [ rsp + 0x148 ], r15; saving to stack
mov rax, [ rsi + 0x8 ]; load m64 x1 to register64
mov r10, [ rsi + 0x0 ]; load m64 x4 to register64
mov r11, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x0 ]; saving arg2[0] in rdx.
mulx rbx, rbp, r10; x12, x11<- x4 * arg2[0]
mov r12, 0xd838091dd2253531 ; moving imm to reg
mov rdx, r12; 0xd838091dd2253531 to rdx
mulx r12, r13, rbp; _, x20<- x11 * 0xd838091dd2253531
mov r12, 0xfffffffefffffc2f ; moving imm to reg
xchg rdx, r13; x20, swapping with 0xd838091dd2253531, which is currently in rdx
mulx r14, r15, r12; x29, x28<- x20 * 0xfffffffefffffc2f
mov rcx, 0xffffffffffffffff ; moving imm to reg
mulx r8, r9, rcx; x27, x26<- x20 * 0xffffffffffffffff
mulx r12, r13, rcx; x25, x24<- x20 * 0xffffffffffffffff
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx rdx, rdi, rcx; x23, x22<- x20 * 0xffffffffffffffff
xor rcx, rcx
adox r9, r14
mov r14, rdx; preserving value of x23 into a new reg
mov rdx, [ r11 + 0x10 ]; saving arg2[2] in rdx.
mov [ rsp + 0x8 ], rsi; spilling arg1 to mem
mulx rcx, rsi, r10; x8, x7<- x4 * arg2[2]
adox r13, r8
adcx r15, rbp
mov rdx, [ r11 + 0x8 ]; arg2[1] to rdx
mulx r15, rbp, r10; x10, x9<- x4 * arg2[1]
adox rdi, r12
seto r8b; spill OF x35 to reg (r8)
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, rbx
adox rsi, r15
mov rdx, rax; x1 to rdx
mulx rax, rbx, [ r11 + 0x8 ]; x52, x51<- x1 * arg2[1]
mulx r15, r12, [ r11 + 0x0 ]; x54, x53<- x1 * arg2[0]
adcx r9, rbp
adcx r13, rsi
movzx rbp, r8b; x36, copying x35 here, cause x35 is needed in a reg for other than x36, namely all: , x36, size: 1
lea rbp, [ rbp + r14 ]
setc r14b; spill CF x42 to reg (r14)
clc;
adcx rbx, r15
setc r8b; spill CF x56 to reg (r8)
clc;
adcx r12, r9
mov rsi, 0xd838091dd2253531 ; moving imm to reg
xchg rdx, r12; x62, swapping with x1, which is currently in rdx
mulx r15, r9, rsi; _, x72<- x62 * 0xd838091dd2253531
mov r15, rdx; preserving value of x62 into a new reg
mov rdx, [ r11 + 0x18 ]; saving arg2[3] in rdx.
mulx r10, rsi, r10; x6, x5<- x4 * arg2[3]
adcx rbx, r13
mov r13, 0xfffffffefffffc2f ; moving imm to reg
mov rdx, r9; x72 to rdx
mov [ rsp + 0x10 ], rbp; spilling x36 to mem
mulx r9, rbp, r13; x81, x80<- x72 * 0xfffffffefffffc2f
setc r13b; spill CF x65 to reg (r13)
clc;
adcx rbp, r15
mov rbp, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x18 ], r10; spilling x6 to mem
mulx r15, r10, rbp; x79, x78<- x72 * 0xffffffffffffffff
seto bpl; spill OF x16 to reg (rbp)
mov [ rsp + 0x20 ], r15; spilling x79 to mem
mov r15, -0x2 ; moving imm to reg
inc r15; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r10, r9
mov r9, [ rsp + 0x8 ]; load m64 arg1 to register64
mov r15, [ r9 + 0x10 ]; load m64 x2 to register64
mov byte [ rsp + 0x28 ], r13b; spilling byte x65 to mem
mov r13, rdx; preserving value of x72 into a new reg
mov rdx, [ r11 + 0x10 ]; saving arg2[2] in rdx.
mov [ rsp + 0x30 ], rax; spilling x52 to mem
mov byte [ rsp + 0x38 ], r8b; spilling byte x56 to mem
mulx rax, r8, r12; x50, x49<- x1 * arg2[2]
adcx r10, rbx
mov rdx, [ r11 + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x40 ], rax; spilling x50 to mem
mulx rbx, rax, r15; x107, x106<- x2 * arg2[0]
mov [ rsp + 0x48 ], rbx; spilling x107 to mem
setc bl; spill CF x92 to reg (rbx)
clc;
adcx rax, r10
setc r10b; spill CF x116 to reg (r10)
clc;
mov byte [ rsp + 0x50 ], bl; spilling byte x92 to mem
mov rbx, -0x1 ; moving imm to reg
movzx rbp, bpl
adcx rbp, rbx; loading flag
adcx rcx, rsi
mov rbp, 0xd838091dd2253531 ; moving imm to reg
mov rdx, rbp; 0xd838091dd2253531 to rdx
mulx rbp, rsi, rax; _, x125<- x115 * 0xd838091dd2253531
setc bpl; spill CF x18 to reg (rbp)
clc;
movzx r14, r14b
adcx r14, rbx; loading flag
adcx rcx, rdi
setc dil; spill CF x44 to reg (rdi)
movzx r14, byte [ rsp + 0x38 ]; load byte memx56 to register64
clc;
adcx r14, rbx; loading flag
adcx r8, [ rsp + 0x30 ]
setc r14b; spill CF x58 to reg (r14)
movzx rbx, byte [ rsp + 0x28 ]; load byte memx65 to register64
clc;
mov rdx, -0x1 ; moving imm to reg
adcx rbx, rdx; loading flag
adcx rcx, r8
mov rbx, 0xfffffffefffffc2f ; moving imm to reg
mov rdx, rsi; x125 to rdx
mov byte [ rsp + 0x58 ], r14b; spilling byte x58 to mem
mulx r8, r14, rbx; x134, x133<- x125 * 0xfffffffefffffc2f
mov rbx, rdx; preserving value of x125 into a new reg
mov rdx, [ r11 + 0x8 ]; saving arg2[1] in rdx.
mov byte [ rsp + 0x60 ], r10b; spilling byte x116 to mem
mov byte [ rsp + 0x68 ], dil; spilling byte x44 to mem
mulx r10, rdi, r15; x105, x104<- x2 * arg2[1]
mov [ rsp + 0x70 ], r10; spilling x105 to mem
movzx r10, bpl; x19, copying x18 here, cause x18 is needed in a reg for other than x19, namely all: , x19, size: 1
mov [ rsp + 0x78 ], rcx; spilling x66 to mem
mov rcx, [ rsp + 0x18 ]; load m64 x6 to register64
lea r10, [ r10 + rcx ]; r8/64 + m8
setc cl; spill CF x67 to reg (rcx)
clc;
adcx r14, rax
mov r14, 0xffffffffffffffff ; moving imm to reg
mov rdx, r14; 0xffffffffffffffff to rdx
mulx r14, rax, r13; x77, x76<- x72 * 0xffffffffffffffff
setc bpl; spill CF x143 to reg (rbp)
clc;
adcx rdi, [ rsp + 0x48 ]
mov byte [ rsp + 0x80 ], cl; spilling byte x67 to mem
mov byte [ rsp + 0x88 ], bpl; spilling byte x143 to mem
mulx rcx, rbp, rbx; x132, x131<- x125 * 0xffffffffffffffff
mov rdx, [ rsp + 0x20 ]; x84, copying x79 here, cause x79 is needed in a reg for other than x84, namely all: , x84--x85, size: 1
adox rdx, rax
setc al; spill CF x109 to reg (rax)
clc;
adcx rbp, r8
setc r8b; spill CF x136 to reg (r8)
mov [ rsp + 0x90 ], rcx; spilling x132 to mem
movzx rcx, byte [ rsp + 0x50 ]; load byte memx92 to register64
clc;
mov byte [ rsp + 0x98 ], al; spilling byte x109 to mem
mov rax, -0x1 ; moving imm to reg
adcx rcx, rax; loading flag
adcx rdx, [ rsp + 0x78 ]
setc cl; spill CF x94 to reg (rcx)
movzx rax, byte [ rsp + 0x68 ]; load byte memx44 to register64
clc;
mov byte [ rsp + 0xa0 ], r8b; spilling byte x136 to mem
mov r8, -0x1 ; moving imm to reg
adcx rax, r8; loading flag
adcx r10, [ rsp + 0x10 ]
mov rax, rdx; preserving value of x93 into a new reg
mov rdx, [ r11 + 0x10 ]; saving arg2[2] in rdx.
mov byte [ rsp + 0xa8 ], cl; spilling byte x94 to mem
mulx r8, rcx, r15; x103, x102<- x2 * arg2[2]
mov [ rsp + 0xb0 ], r8; spilling x103 to mem
mov r8, 0xffffffffffffffff ; moving imm to reg
mov rdx, r8; 0xffffffffffffffff to rdx
mov [ rsp + 0xb8 ], rcx; spilling x102 to mem
mulx r8, rcx, rbx; x130, x129<- x125 * 0xffffffffffffffff
mov [ rsp + 0xc0 ], r8; spilling x130 to mem
mov r8, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ r11 + 0x18 ]; saving arg2[3] in rdx.
mov [ rsp + 0xc8 ], rcx; spilling x129 to mem
mulx r12, rcx, r12; x48, x47<- x1 * arg2[3]
mov rdx, r8; 0xffffffffffffffff to rdx
mulx r13, r8, r13; x75, x74<- x72 * 0xffffffffffffffff
adox r8, r14
setc r14b; spill CF x46 to reg (r14)
movzx rdx, byte [ rsp + 0x60 ]; load byte memx116 to register64
clc;
mov [ rsp + 0xd0 ], r8; spilling x86 to mem
mov r8, -0x1 ; moving imm to reg
adcx rdx, r8; loading flag
adcx rax, rdi
mov rdx, 0x0 ; moving imm to reg
adox r13, rdx
movzx rdi, byte [ rsp + 0x58 ]; load byte memx58 to register64
dec rdx; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
adox rdi, rdx; loading flag
adox rcx, [ rsp + 0x40 ]
setc r8b; spill CF x118 to reg (r8)
movzx rdi, byte [ rsp + 0x88 ]; load byte memx143 to register64
clc;
adcx rdi, rdx; loading flag
adcx rax, rbp
mov rdi, 0x0 ; moving imm to reg
adox r12, rdi
movzx rbp, byte [ rsp + 0x80 ]; load byte memx67 to register64
inc rdx; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
adox rbp, rdx; loading flag
adox r10, rcx
movzx rbp, r14b; x70, copying x46 here, cause x46 is needed in a reg for other than x70, namely all: , x70--x71, size: 1
adox rbp, r12
mov r14, [ rsp + 0x70 ]; load m64 x105 to register64
seto cl; spill OF x71 to reg (rcx)
movzx r12, byte [ rsp + 0x98 ]; load byte memx109 to register64
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
adox r12, rdx; loading flag
adox r14, [ rsp + 0xb8 ]
mov rdx, [ r11 + 0x18 ]; arg2[3] to rdx
mulx r15, r12, r15; x101, x100<- x2 * arg2[3]
mov [ rsp + 0xd8 ], rax; spilling x144 to mem
mov rax, [ rsp + 0xb0 ]; x112, copying x103 here, cause x103 is needed in a reg for other than x112, namely all: , x112--x113, size: 1
adox rax, r12
setc r12b; spill CF x145 to reg (r12)
mov [ rsp + 0xe0 ], r15; spilling x101 to mem
movzx r15, byte [ rsp + 0xa8 ]; load byte memx94 to register64
clc;
mov [ rsp + 0xe8 ], rax; spilling x112 to mem
mov rax, -0x1 ; moving imm to reg
adcx r15, rax; loading flag
adcx r10, [ rsp + 0xd0 ]
adcx r13, rbp
movzx r15, cl; x99, copying x71 here, cause x71 is needed in a reg for other than x99, namely all: , x99, size: 1
mov rbp, 0x0 ; moving imm to reg
adcx r15, rbp
clc;
movzx r8, r8b
adcx r8, rax; loading flag
adcx r10, r14
mov r8, [ rsp + 0xc8 ]; load m64 x129 to register64
seto cl; spill OF x113 to reg (rcx)
movzx r14, byte [ rsp + 0xa0 ]; load byte memx136 to register64
inc rax; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
adox r14, rbp; loading flag
adox r8, [ rsp + 0x90 ]
mov r14, [ rsp + 0xe8 ]; x121, copying x112 here, cause x112 is needed in a reg for other than x121, namely all: , x121--x122, size: 1
adcx r14, r13
mov r13, [ r9 + 0x18 ]; load m64 x3 to register64
movzx rax, cl; x114, copying x113 here, cause x113 is needed in a reg for other than x114, namely all: , x114, size: 1
mov rbp, [ rsp + 0xe0 ]; load m64 x101 to register64
lea rax, [ rax + rbp ]; r8/64 + m8
mov rbp, 0xffffffffffffffff ; moving imm to reg
mov rdx, rbx; x125 to rdx
mulx rdx, rbx, rbp; x128, x127<- x125 * 0xffffffffffffffff
mov rcx, [ rsp + 0xc0 ]; x139, copying x130 here, cause x130 is needed in a reg for other than x139, namely all: , x139--x140, size: 1
adox rcx, rbx
adcx rax, r15
setc r15b; spill CF x124 to reg (r15)
clc;
mov rbx, -0x1 ; moving imm to reg
movzx r12, r12b
adcx r12, rbx; loading flag
adcx r10, r8
mov r12, 0x0 ; moving imm to reg
adox rdx, r12
adcx rcx, r14
adcx rdx, rax
mov r8, rdx; preserving value of x150 into a new reg
mov rdx, [ r11 + 0x0 ]; saving arg2[0] in rdx.
mulx r14, rax, r13; x160, x159<- x3 * arg2[0]
mov rdx, [ r11 + 0x8 ]; arg2[1] to rdx
mulx r12, rbx, r13; x158, x157<- x3 * arg2[1]
movzx rbp, r15b; x152, copying x124 here, cause x124 is needed in a reg for other than x152, namely all: , x152, size: 1
adc rbp, 0x0
xor r15, r15
adox rax, [ rsp + 0xd8 ]
mov r15, 0xd838091dd2253531 ; moving imm to reg
mov rdx, r15; 0xd838091dd2253531 to rdx
mov [ rsp + 0xf0 ], rbp; spilling x152 to mem
mulx r15, rbp, rax; _, x178<- x168 * 0xd838091dd2253531
mov r15, 0xfffffffefffffc2f ; moving imm to reg
xchg rdx, r15; 0xfffffffefffffc2f, swapping with 0xd838091dd2253531, which is currently in rdx
mov [ rsp + 0xf8 ], r8; spilling x150 to mem
mulx r15, r8, rbp; x187, x186<- x178 * 0xfffffffefffffc2f
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x100 ], rcx; spilling x148 to mem
mov [ rsp + 0x108 ], r10; spilling x146 to mem
mulx rcx, r10, rbp; x185, x184<- x178 * 0xffffffffffffffff
adcx r8, rax
setc r8b; spill CF x196 to reg (r8)
clc;
adcx r10, r15
setc al; spill CF x189 to reg (rax)
clc;
adcx rbx, r14
mov r14, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ r11 + 0x10 ]; saving arg2[2] in rdx.
mov [ rsp + 0x110 ], r10; spilling x188 to mem
mulx r15, r10, r13; x156, x155<- x3 * arg2[2]
adcx r10, r12
mov r12, [ rsp + 0x108 ]; x170, copying x146 here, cause x146 is needed in a reg for other than x170, namely all: , x170--x171, size: 1
adox r12, rbx
mov rdx, [ r11 + 0x18 ]; arg2[3] to rdx
mulx r13, rbx, r13; x154, x153<- x3 * arg2[3]
mov rdx, rbp; x178 to rdx
mov [ rsp + 0x118 ], r12; spilling x170 to mem
mulx rbp, r12, r14; x183, x182<- x178 * 0xffffffffffffffff
adcx rbx, r15
mov r15, [ rsp + 0x100 ]; x172, copying x148 here, cause x148 is needed in a reg for other than x172, namely all: , x172--x173, size: 1
adox r15, r10
mov r10, [ rsp + 0xf8 ]; x174, copying x150 here, cause x150 is needed in a reg for other than x174, namely all: , x174--x175, size: 1
adox r10, rbx
mov rbx, 0x0 ; moving imm to reg
adcx r13, rbx
clc;
mov rbx, -0x1 ; moving imm to reg
movzx rax, al
adcx rax, rbx; loading flag
adcx rcx, r12
mov rax, [ rsp + 0xf0 ]; x176, copying x152 here, cause x152 is needed in a reg for other than x176, namely all: , x176--x177, size: 1
adox rax, r13
mov r12, [ rsp + 0x110 ]; load m64 x188 to register64
seto r13b; spill OF x177 to reg (r13)
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, rbx; loading flag
adox r12, [ rsp + 0x118 ]
adox rcx, r15
mulx rdx, r8, r14; x181, x180<- x178 * 0xffffffffffffffff
adcx r8, rbp
adox r8, r10
mov rbp, 0x0 ; moving imm to reg
adcx rdx, rbp
adox rdx, rax
movzx r15, r13b; x205, copying x177 here, cause x177 is needed in a reg for other than x205, namely all: , x205, size: 1
adox r15, rbp
mov r10, r12; x206, copying x197 here, cause x197 is needed in a reg for other than x206, namely all: , x216, x206--x207, size: 2
mov r13, 0xfffffffefffffc2f ; moving imm to reg
sub r10, r13
mov rax, rcx; x208, copying x199 here, cause x199 is needed in a reg for other than x208, namely all: , x208--x209, x217, size: 2
sbb rax, r14
mov rbp, r8; x210, copying x201 here, cause x201 is needed in a reg for other than x210, namely all: , x210--x211, x218, size: 2
sbb rbp, r14
mov rbx, rdx; x212, copying x203 here, cause x203 is needed in a reg for other than x212, namely all: , x219, x212--x213, size: 2
sbb rbx, r14
sbb r15, 0x00000000
cmovc rbp, r8; if CF, x218<- x201 (nzVar)
cmovc r10, r12; if CF, x216<- x197 (nzVar)
cmovc rbx, rdx; if CF, x219<- x203 (nzVar)
cmovc rax, rcx; if CF, x217<- x199 (nzVar)
mov r15, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r15 + 0x10 ], rbp; out1[2] = x218
mov [ r15 + 0x18 ], rbx; out1[3] = x219
mov [ r15 + 0x0 ], r10; out1[0] = x216
mov [ r15 + 0x8 ], rax; out1[1] = x217
mov rbx, [ rsp + 0x120 ]; restoring from stack
mov rbp, [ rsp + 0x128 ]; restoring from stack
mov r12, [ rsp + 0x130 ]; restoring from stack
mov r13, [ rsp + 0x138 ]; restoring from stack
mov r14, [ rsp + 0x140 ]; restoring from stack
mov r15, [ rsp + 0x148 ]; restoring from stack
add rsp, 0x150 
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; clocked at 3600 MHz
; first cyclecount 80.34, best 62.31404958677686, lastGood 65.35042735042735
; seed 2003353293586321 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 774461 ms / 60000 runs=> 12.907683333333333ms/run
; Time spent for assembling and measureing (initial batch_size=116, initial num_batches=101): 125733 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.1623490401711642
; number reverted permutation/ tried permutation: 22714 / 29934 =75.880%
; number reverted decision/ tried decision: 22421 / 30067 =74.570%