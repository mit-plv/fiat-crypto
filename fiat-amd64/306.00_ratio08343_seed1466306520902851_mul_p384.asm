SECTION .text
	GLOBAL mul_p384
mul_p384:
sub rsp, 0x3b8 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x388 ], rbx; saving to stack
mov [ rsp + 0x390 ], rbp; saving to stack
mov [ rsp + 0x398 ], r12; saving to stack
mov [ rsp + 0x3a0 ], r13; saving to stack
mov [ rsp + 0x3a8 ], r14; saving to stack
mov [ rsp + 0x3b0 ], r15; saving to stack
mov rax, [ rsi + 0x8 ]; load m64 x1 to register64
mov r10, [ rsi + 0x0 ]; load m64 x6 to register64
xchg rdx, r10; x6, swapping with arg2, which is currently in rdx
mulx r11, rbx, [ r10 + 0x0 ]; x18, x17<- x6 * arg2[0]
mov rbp, 0x100000001 ; moving imm to reg
xchg rdx, rbx; x17, swapping with x6, which is currently in rdx
mulx r12, r13, rbp; _, x30<- x17 * 0x100000001
mov r12, 0xffffffff00000000 ; moving imm to reg
xchg rdx, r12; 0xffffffff00000000, swapping with x17, which is currently in rdx
mulx r14, r15, r13; x41, x40<- x30 * 0xffffffff00000000
mov rcx, 0xffffffff ; moving imm to reg
xchg rdx, rcx; 0xffffffff, swapping with 0xffffffff00000000, which is currently in rdx
mulx r8, r9, r13; x43, x42<- x30 * 0xffffffff
mov rcx, rdx; preserving value of 0xffffffff into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx rbp, rdi, rbx; x16, x15<- x6 * arg2[1]
add r15, r8; could be done better, if r0 has been u8 as well
mov rdx, [ r10 + 0x0 ]; arg2[0] to rdx
mulx r8, rcx, rax; x80, x79<- x1 * arg2[0]
mov [ rsp + 0x8 ], r8; spilling x80 to mem
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rdi, r11
seto r11b; spill OF x20 to reg (r11)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r9, r12
adox r15, rdi
seto r9b; spill OF x58 to reg (r9)
mov r12, -0x3 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rcx, r15
mov rdi, 0x100000001 ; moving imm to reg
mov rdx, rcx; x92 to rdx
mulx rcx, r15, rdi; _, x106<- x92 * 0x100000001
mov rcx, 0xfffffffffffffffe ; moving imm to reg
xchg rdx, rcx; 0xfffffffffffffffe, swapping with x92, which is currently in rdx
mulx r8, r12, r15; x115, x114<- x106 * 0xfffffffffffffffe
mov rdx, 0xffffffff ; moving imm to reg
mov byte [ rsp + 0x10 ], r9b; spilling byte x58 to mem
mulx rdi, r9, r15; x119, x118<- x106 * 0xffffffff
mov rdx, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x18 ], rbp; spilling x16 to mem
mov byte [ rsp + 0x20 ], r11b; spilling byte x20 to mem
mulx rbp, r11, r15; x117, x116<- x106 * 0xffffffff00000000
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x28 ], rbx; spilling x6 to mem
mov [ rsp + 0x30 ], r9; spilling x118 to mem
mulx rbx, r9, r13; x35, x34<- x30 * 0xffffffffffffffff
seto dl; spill OF x93 to reg (rdx)
mov [ rsp + 0x38 ], rbx; spilling x35 to mem
mov rbx, -0x2 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, rdi
mov rdi, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r15; x106, swapping with x93, which is currently in rdx
mov [ rsp + 0x40 ], r11; spilling x120 to mem
mulx rbx, r11, rdi; x113, x112<- x106 * 0xffffffffffffffff
adox r12, rbp
mov rbp, 0xfffffffffffffffe ; moving imm to reg
xchg rdx, r13; x30, swapping with x106, which is currently in rdx
mov [ rsp + 0x48 ], r12; spilling x122 to mem
mulx rdi, r12, rbp; x39, x38<- x30 * 0xfffffffffffffffe
adox r11, r8
mov r8, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r8; 0xffffffffffffffff, swapping with x30, which is currently in rdx
mov [ rsp + 0x50 ], r11; spilling x124 to mem
mulx rbp, r11, r13; x111, x110<- x106 * 0xffffffffffffffff
mov rdx, [ rsi + 0x18 ]; load m64 x3 to register64
adcx r12, r14
adox r11, rbx
mov r14, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r14; 0xffffffffffffffff, swapping with x3, which is currently in rdx
mulx r13, rbx, r13; x109, x108<- x106 * 0xffffffffffffffff
mov [ rsp + 0x58 ], r11; spilling x126 to mem
mov byte [ rsp + 0x60 ], r15b; spilling byte x93 to mem
mulx r11, r15, r8; x37, x36<- x30 * 0xffffffffffffffff
adcx r15, rdi
adcx r9, r11
mov rdi, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ r10 + 0x20 ]; saving arg2[4] in rdx.
mov [ rsp + 0x68 ], r9; spilling x50 to mem
mulx r11, r9, r14; x226, x225<- x3 * arg2[4]
mov rdx, r8; x30 to rdx
mulx rdx, r8, rdi; x33, x32<- x30 * 0xffffffffffffffff
mov rdi, rdx; preserving value of x33 into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mov [ rsp + 0x70 ], r15; spilling x48 to mem
mov [ rsp + 0x78 ], r12; spilling x46 to mem
mulx r15, r12, r14; x232, x231<- x3 * arg2[1]
mov [ rsp + 0x80 ], rax; spilling x1 to mem
mov rax, [ rsi + 0x20 ]; load m64 x4 to register64
mov [ rsp + 0x88 ], r11; spilling x226 to mem
mov r11, [ rsp + 0x38 ]; x52, copying x35 here, cause x35 is needed in a reg for other than x52, namely all: , x52--x53, size: 1
adcx r11, r8
mov rdx, r14; x3 to rdx
mulx r14, r8, [ r10 + 0x0 ]; x234, x233<- x3 * arg2[0]
mov [ rsp + 0x90 ], r8; spilling x233 to mem
mov r8, 0x0 ; moving imm to reg
adcx rdi, r8
clc;
adcx r12, r14
adox rbx, rbp
adox r13, r8
mulx rbp, r14, [ r10 + 0x10 ]; x230, x229<- x3 * arg2[2]
adcx r14, r15
mulx r15, r8, [ r10 + 0x28 ]; x224, x223<- x3 * arg2[5]
xchg rdx, rax; x4, swapping with x3, which is currently in rdx
mov [ rsp + 0x98 ], r14; spilling x237 to mem
mov [ rsp + 0xa0 ], r12; spilling x235 to mem
mulx r14, r12, [ r10 + 0x10 ]; x307, x306<- x4 * arg2[2]
xchg rdx, rax; x3, swapping with x4, which is currently in rdx
mov [ rsp + 0xa8 ], r13; spilling x130 to mem
mulx rdx, r13, [ r10 + 0x18 ]; x228, x227<- x3 * arg2[3]
adcx r13, rbp
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rcx, [ rsp + 0x30 ]
adcx r9, rdx
mov rdx, [ r10 + 0x8 ]; arg2[1] to rdx
mulx rcx, rbp, rax; x309, x308<- x4 * arg2[1]
mov rdx, [ r10 + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0xb0 ], r9; spilling x241 to mem
mov [ rsp + 0xb8 ], r13; spilling x239 to mem
mulx r9, r13, rax; x305, x304<- x4 * arg2[3]
mov rdx, [ r10 + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0xc0 ], rbx; spilling x128 to mem
mov [ rsp + 0xc8 ], rdi; spilling x54 to mem
mulx rbx, rdi, rax; x311, x310<- x4 * arg2[0]
mov [ rsp + 0xd0 ], rdi; spilling x310 to mem
mov rdi, [ rsp + 0x88 ]; x243, copying x226 here, cause x226 is needed in a reg for other than x243, namely all: , x243--x244, size: 1
adcx rdi, r8
mov rdx, [ r10 + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0xd8 ], rdi; spilling x243 to mem
mulx r8, rdi, rax; x301, x300<- x4 * arg2[5]
mov rdx, [ r10 + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0xe0 ], r11; spilling x52 to mem
mov [ rsp + 0xe8 ], r8; spilling x301 to mem
mulx r11, r8, [ rsp + 0x80 ]; x78, x77<- x1 * arg2[1]
mov [ rsp + 0xf0 ], r11; spilling x78 to mem
seto r11b; spill OF x132 to reg (r11)
mov [ rsp + 0xf8 ], r8; spilling x77 to mem
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, rbx
mov rbx, 0x0 ; moving imm to reg
adcx r15, rbx
adox r12, rcx
mov rdx, [ rsp + 0x28 ]; x6 to rdx
mulx rcx, rbx, [ r10 + 0x10 ]; x14, x13<- x6 * arg2[2]
mov r8, rdx; preserving value of x6 into a new reg
mov rdx, [ r10 + 0x20 ]; saving arg2[4] in rdx.
mov [ rsp + 0x100 ], r15; spilling x245 to mem
mulx rax, r15, rax; x303, x302<- x4 * arg2[4]
adox r13, r14
adox r15, r9
adox rdi, rax
movzx r14, byte [ rsp + 0x20 ]; load byte memx20 to register64
clc;
mov r9, -0x1 ; moving imm to reg
adcx r14, r9; loading flag
adcx rbx, [ rsp + 0x18 ]
setc r14b; spill CF x22 to reg (r14)
movzx rax, byte [ rsp + 0x10 ]; load byte memx58 to register64
clc;
adcx rax, r9; loading flag
adcx rbx, [ rsp + 0x78 ]
mov rax, [ rsi + 0x10 ]; load m64 x2 to register64
mov r9, [ rsp + 0xf8 ]; load m64 x77 to register64
mov [ rsp + 0x108 ], rdi; spilling x320 to mem
seto dil; spill OF x321 to reg (rdi)
mov [ rsp + 0x110 ], r15; spilling x318 to mem
mov r15, -0x2 ; moving imm to reg
inc r15; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r9, [ rsp + 0x8 ]
mov rdx, rax; x2 to rdx
mulx rax, r15, [ r10 + 0x0 ]; x157, x156<- x2 * arg2[0]
xchg rdx, r8; x6, swapping with x2, which is currently in rdx
mov [ rsp + 0x118 ], r13; spilling x316 to mem
mov [ rsp + 0x120 ], r12; spilling x314 to mem
mulx r13, r12, [ r10 + 0x18 ]; x12, x11<- x6 * arg2[3]
mov [ rsp + 0x128 ], rbp; spilling x312 to mem
seto bpl; spill OF x82 to reg (rbp)
mov [ rsp + 0x130 ], r13; spilling x12 to mem
mov r13, -0x1 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r13, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, r13; loading flag
adox rcx, r12
setc r14b; spill CF x60 to reg (r14)
movzx r12, byte [ rsp + 0x60 ]; load byte memx93 to register64
clc;
adcx r12, r13; loading flag
adcx rbx, r9
mov r12, rdx; preserving value of x6 into a new reg
mov rdx, [ rsp + 0x80 ]; saving x1 in rdx.
mulx r9, r13, [ r10 + 0x10 ]; x76, x75<- x1 * arg2[2]
mov [ rsp + 0x138 ], r9; spilling x76 to mem
seto r9b; spill OF x24 to reg (r9)
mov byte [ rsp + 0x140 ], dil; spilling byte x321 to mem
mov rdi, 0x0 ; moving imm to reg
dec rdi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r11, r11b
adox r11, rdi; loading flag
adox rbx, [ rsp + 0x40 ]
xchg rdx, r8; x2, swapping with x1, which is currently in rdx
mulx r11, rdi, [ r10 + 0x8 ]; x155, x154<- x2 * arg2[1]
mov [ rsp + 0x148 ], r11; spilling x155 to mem
setc r11b; spill CF x95 to reg (r11)
clc;
mov byte [ rsp + 0x150 ], r9b; spilling byte x24 to mem
mov r9, -0x1 ; moving imm to reg
movzx rbp, bpl
adcx rbp, r9; loading flag
adcx r13, [ rsp + 0xf0 ]
setc bpl; spill CF x84 to reg (rbp)
clc;
adcx r15, rbx
setc bl; spill CF x170 to reg (rbx)
clc;
movzx r14, r14b
adcx r14, r9; loading flag
adcx rcx, [ rsp + 0x70 ]
setc r14b; spill CF x62 to reg (r14)
clc;
movzx r11, r11b
adcx r11, r9; loading flag
adcx rcx, r13
mov r11, [ rsp + 0x48 ]; x135, copying x122 here, cause x122 is needed in a reg for other than x135, namely all: , x135--x136, size: 1
adox r11, rcx
mov r13, 0x100000001 ; moving imm to reg
xchg rdx, r15; x169, swapping with x2, which is currently in rdx
mulx rcx, r9, r13; _, x183<- x169 * 0x100000001
mov rcx, 0xffffffff ; moving imm to reg
xchg rdx, r9; x183, swapping with x169, which is currently in rdx
mov byte [ rsp + 0x158 ], bpl; spilling byte x84 to mem
mulx r13, rbp, rcx; x196, x195<- x183 * 0xffffffff
mov rcx, rdx; preserving value of x183 into a new reg
mov rdx, [ r10 + 0x18 ]; saving arg2[3] in rdx.
mov byte [ rsp + 0x160 ], r14b; spilling byte x62 to mem
mov [ rsp + 0x168 ], r13; spilling x196 to mem
mulx r14, r13, r8; x74, x73<- x1 * arg2[3]
mov [ rsp + 0x170 ], r14; spilling x74 to mem
seto r14b; spill OF x136 to reg (r14)
mov [ rsp + 0x178 ], r13; spilling x73 to mem
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rdi, rax
setc al; spill CF x97 to reg (rax)
clc;
adcx rbp, r9
seto bpl; spill OF x159 to reg (rbp)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, r9; loading flag
adox r11, rdi
mov rbx, 0xffffffff00000000 ; moving imm to reg
mov rdx, rcx; x183 to rdx
mulx rcx, rdi, rbx; x194, x193<- x183 * 0xffffffff00000000
seto r9b; spill OF x172 to reg (r9)
mov rbx, -0x3 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rdi, [ rsp + 0x168 ]
xchg rdx, r12; x6, swapping with x183, which is currently in rdx
mulx r13, rbx, [ r10 + 0x20 ]; x10, x9<- x6 * arg2[4]
adcx rdi, r11
mov r11, 0xfffffffffffffffe ; moving imm to reg
xchg rdx, r11; 0xfffffffffffffffe, swapping with x6, which is currently in rdx
mov [ rsp + 0x180 ], rdi; spilling x210 to mem
mov byte [ rsp + 0x188 ], r9b; spilling byte x172 to mem
mulx rdi, r9, r12; x192, x191<- x183 * 0xfffffffffffffffe
adox r9, rcx
movzx rcx, byte [ rsp + 0x140 ]; x322, copying x321 here, cause x321 is needed in a reg for other than x322, namely all: , x322, size: 1
mov rdx, [ rsp + 0xe8 ]; load m64 x301 to register64
lea rcx, [ rcx + rdx ]; r8/64 + m8
mov rdx, [ r10 + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x190 ], rcx; spilling x322 to mem
mulx r11, rcx, r11; x8, x7<- x6 * arg2[5]
mov rdx, r15; x2 to rdx
mov [ rsp + 0x198 ], r11; spilling x8 to mem
mulx r15, r11, [ r10 + 0x10 ]; x153, x152<- x2 * arg2[2]
mov [ rsp + 0x1a0 ], rdi; spilling x192 to mem
seto dil; spill OF x200 to reg (rdi)
mov [ rsp + 0x1a8 ], r9; spilling x199 to mem
movzx r9, byte [ rsp + 0x150 ]; load byte memx24 to register64
mov byte [ rsp + 0x1b0 ], r14b; spilling byte x136 to mem
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r9, r14; loading flag
adox rbx, [ rsp + 0x130 ]
setc r9b; spill CF x211 to reg (r9)
movzx r14, byte [ rsp + 0x160 ]; load byte memx62 to register64
clc;
mov byte [ rsp + 0x1b8 ], dil; spilling byte x200 to mem
mov rdi, -0x1 ; moving imm to reg
adcx r14, rdi; loading flag
adcx rbx, [ rsp + 0x68 ]
adox rcx, r13
mov r14, [ rsp + 0xe0 ]; x65, copying x52 here, cause x52 is needed in a reg for other than x65, namely all: , x65--x66, size: 1
adcx r14, rcx
xchg rdx, r8; x1, swapping with x2, which is currently in rdx
mulx r13, rcx, [ r10 + 0x28 ]; x70, x69<- x1 * arg2[5]
setc dil; spill CF x66 to reg (rdi)
clc;
mov [ rsp + 0x1c0 ], r13; spilling x70 to mem
mov r13, -0x1 ; moving imm to reg
movzx rbp, bpl
adcx rbp, r13; loading flag
adcx r11, [ rsp + 0x148 ]
mov rbp, [ rsp + 0x178 ]; load m64 x73 to register64
setc r13b; spill CF x161 to reg (r13)
mov byte [ rsp + 0x1c8 ], dil; spilling byte x66 to mem
movzx rdi, byte [ rsp + 0x158 ]; load byte memx84 to register64
clc;
mov byte [ rsp + 0x1d0 ], r9b; spilling byte x211 to mem
mov r9, -0x1 ; moving imm to reg
adcx rdi, r9; loading flag
adcx rbp, [ rsp + 0x138 ]
xchg rdx, r8; x2, swapping with x1, which is currently in rdx
mulx rdi, r9, [ r10 + 0x18 ]; x151, x150<- x2 * arg2[3]
mov [ rsp + 0x1d8 ], rdi; spilling x151 to mem
seto dil; spill OF x28 to reg (rdi)
mov [ rsp + 0x1e0 ], rcx; spilling x69 to mem
mov rcx, -0x1 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rcx, -0x1 ; moving imm to reg
movzx rax, al
adox rax, rcx; loading flag
adox rbx, rbp
seto al; spill OF x99 to reg (rax)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, rbp; loading flag
adox r15, r9
setc r13b; spill CF x86 to reg (r13)
movzx r9, byte [ rsp + 0x1b0 ]; load byte memx136 to register64
clc;
adcx r9, rbp; loading flag
adcx rbx, [ rsp + 0x50 ]
seto r9b; spill OF x163 to reg (r9)
movzx rcx, byte [ rsp + 0x188 ]; load byte memx172 to register64
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
adox rcx, rbp; loading flag
adox rbx, r11
mov rcx, rdx; preserving value of x2 into a new reg
mov rdx, [ r10 + 0x20 ]; saving arg2[4] in rdx.
mulx r8, r11, r8; x72, x71<- x1 * arg2[4]
setc bpl; spill CF x138 to reg (rbp)
clc;
mov byte [ rsp + 0x1e8 ], r9b; spilling byte x163 to mem
mov r9, -0x1 ; moving imm to reg
movzx r13, r13b
adcx r13, r9; loading flag
adcx r11, [ rsp + 0x170 ]
setc r13b; spill CF x88 to reg (r13)
clc;
movzx rax, al
adcx rax, r9; loading flag
adcx r14, r11
setc al; spill CF x101 to reg (rax)
clc;
movzx r13, r13b
adcx r13, r9; loading flag
adcx r8, [ rsp + 0x1e0 ]
setc r11b; spill CF x90 to reg (r11)
clc;
movzx rbp, bpl
adcx rbp, r9; loading flag
adcx r14, [ rsp + 0x58 ]
adox r15, r14
mov rbp, 0xffffffffffffffff ; moving imm to reg
mov rdx, r12; x183 to rdx
mulx r12, r13, rbp; x190, x189<- x183 * 0xffffffffffffffff
setc r14b; spill CF x140 to reg (r14)
movzx r9, byte [ rsp + 0x1d0 ]; load byte memx211 to register64
clc;
mov rbp, -0x1 ; moving imm to reg
adcx r9, rbp; loading flag
adcx rbx, [ rsp + 0x1a8 ]
seto r9b; spill OF x176 to reg (r9)
movzx rbp, byte [ rsp + 0x1b8 ]; load byte memx200 to register64
mov [ rsp + 0x1f0 ], rbx; spilling x212 to mem
mov rbx, -0x1 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbx, -0x1 ; moving imm to reg
adox rbp, rbx; loading flag
adox r13, [ rsp + 0x1a0 ]
mov rbp, 0xffffffffffffffff ; moving imm to reg
mov byte [ rsp + 0x1f8 ], r9b; spilling byte x176 to mem
mulx rbx, r9, rbp; x188, x187<- x183 * 0xffffffffffffffff
movzx rbp, dil; x29, copying x28 here, cause x28 is needed in a reg for other than x29, namely all: , x29, size: 1
mov [ rsp + 0x200 ], rbx; spilling x188 to mem
mov rbx, [ rsp + 0x198 ]; load m64 x8 to register64
lea rbp, [ rbp + rbx ]; r8/64 + m8
adcx r13, r15
movzx rbx, r11b; x91, copying x90 here, cause x90 is needed in a reg for other than x91, namely all: , x91, size: 1
mov rdi, [ rsp + 0x1c0 ]; load m64 x70 to register64
lea rbx, [ rbx + rdi ]; r8/64 + m8
setc dil; spill CF x215 to reg (rdi)
movzx r11, byte [ rsp + 0x1c8 ]; load byte memx66 to register64
clc;
mov r15, -0x1 ; moving imm to reg
adcx r11, r15; loading flag
adcx rbp, [ rsp + 0xc8 ]
setc r11b; spill CF x68 to reg (r11)
clc;
movzx rax, al
adcx rax, r15; loading flag
adcx rbp, r8
mov rax, rdx; preserving value of x183 into a new reg
mov rdx, [ r10 + 0x20 ]; saving arg2[4] in rdx.
mulx r8, r15, rcx; x149, x148<- x2 * arg2[4]
adox r9, r12
mov r12, 0xffffffffffffffff ; moving imm to reg
mov rdx, r12; 0xffffffffffffffff to rdx
mulx rax, r12, rax; x186, x185<- x183 * 0xffffffffffffffff
xchg rdx, rcx; x2, swapping with 0xffffffffffffffff, which is currently in rdx
mulx rdx, rcx, [ r10 + 0x28 ]; x147, x146<- x2 * arg2[5]
mov [ rsp + 0x208 ], rax; spilling x186 to mem
seto al; spill OF x204 to reg (rax)
mov [ rsp + 0x210 ], r13; spilling x214 to mem
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r14, r14b
adox r14, r13; loading flag
adox rbp, [ rsp + 0xc0 ]
movzx r14, r11b; x104, copying x68 here, cause x68 is needed in a reg for other than x104, namely all: , x104--x105, size: 1
adcx r14, rbx
mov rbx, [ rsp + 0xa8 ]; x143, copying x130 here, cause x130 is needed in a reg for other than x143, namely all: , x143--x144, size: 1
adox rbx, r14
seto r11b; spill OF x144 to reg (r11)
movzx r14, byte [ rsp + 0x1e8 ]; load byte memx163 to register64
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
adox r14, r13; loading flag
adox r15, [ rsp + 0x1d8 ]
adox rcx, r8
mov r14, 0x0 ; moving imm to reg
adox rdx, r14
dec r14; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx rax, al
adox rax, r14; loading flag
adox r12, [ rsp + 0x200 ]
setc r13b; spill CF x105 to reg (r13)
movzx r8, byte [ rsp + 0x1f8 ]; load byte memx176 to register64
clc;
adcx r8, r14; loading flag
adcx rbp, r15
adcx rcx, rbx
mov r8, [ rsp + 0x180 ]; load m64 x210 to register64
seto al; spill OF x206 to reg (rax)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r8, [ rsp + 0x90 ]
setc bl; spill CF x180 to reg (rbx)
clc;
mov r15, -0x1 ; moving imm to reg
movzx rdi, dil
adcx rdi, r15; loading flag
adcx rbp, r9
adcx r12, rcx
mov rdi, [ rsp + 0xa0 ]; load m64 x235 to register64
mov r9, [ rsp + 0x1f0 ]; x248, copying x212 here, cause x212 is needed in a reg for other than x248, namely all: , x248--x249, size: 1
adox r9, rdi
movzx rdi, r11b; x145, copying x144 here, cause x144 is needed in a reg for other than x145, namely all: , x145, size: 1
movzx r13, r13b
lea rdi, [ rdi + r13 ]
mov r13, 0x100000001 ; moving imm to reg
xchg rdx, r13; 0x100000001, swapping with x168, which is currently in rdx
mulx r11, rcx, r8; _, x260<- x246 * 0x100000001
mov r11, 0xffffffff ; moving imm to reg
xchg rdx, rcx; x260, swapping with 0x100000001, which is currently in rdx
mulx r14, r15, r11; x273, x272<- x260 * 0xffffffff
mov r11, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x218 ], r12; spilling x218 to mem
mulx rcx, r12, r11; x271, x270<- x260 * 0xffffffff00000000
mov r11, [ rsi + 0x28 ]; load m64 x5 to register64
mov [ rsp + 0x220 ], r11; spilling x5 to mem
setc r11b; spill CF x219 to reg (r11)
clc;
mov [ rsp + 0x228 ], rbp; spilling x216 to mem
mov rbp, -0x1 ; moving imm to reg
movzx rbx, bl
adcx rbx, rbp; loading flag
adcx rdi, r13
mov r13, [ rsp + 0x210 ]; load m64 x214 to register64
mov rbx, [ rsp + 0x98 ]; x250, copying x237 here, cause x237 is needed in a reg for other than x250, namely all: , x250--x251, size: 1
adox rbx, r13
setc r13b; spill CF x182 to reg (r13)
clc;
adcx r15, r8
movzx r15, al; x207, copying x206 here, cause x206 is needed in a reg for other than x207, namely all: , x207, size: 1
mov r8, [ rsp + 0x208 ]; load m64 x186 to register64
lea r15, [ r15 + r8 ]; r8/64 + m8
seto r8b; spill OF x251 to reg (r8)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rax, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, rax; loading flag
adox rdi, r15
movzx r11, r13b; x222, copying x182 here, cause x182 is needed in a reg for other than x222, namely all: , x222, size: 1
adox r11, rbp
mov r13, -0x3 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r12, r14
adcx r12, r9
mov r9, 0xfffffffffffffffe ; moving imm to reg
mulx r14, r15, r9; x269, x268<- x260 * 0xfffffffffffffffe
setc r13b; spill CF x288 to reg (r13)
clc;
adcx r12, [ rsp + 0xd0 ]
mov rbp, 0x100000001 ; moving imm to reg
xchg rdx, r12; x323, swapping with x260, which is currently in rdx
mulx rax, r9, rbp; _, x337<- x323 * 0x100000001
mov rax, 0xffffffff ; moving imm to reg
xchg rdx, r9; x337, swapping with x323, which is currently in rdx
mov [ rsp + 0x230 ], r11; spilling x222 to mem
mulx rbp, r11, rax; x350, x349<- x337 * 0xffffffff
adox r15, rcx
setc cl; spill CF x324 to reg (rcx)
clc;
mov rax, -0x1 ; moving imm to reg
movzx r13, r13b
adcx r13, rax; loading flag
adcx rbx, r15
mov r13, 0xffffffff00000000 ; moving imm to reg
mulx r15, rax, r13; x348, x347<- x337 * 0xffffffff00000000
mov r13, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r13; 0xffffffffffffffff, swapping with x337, which is currently in rdx
mov [ rsp + 0x238 ], rdi; spilling x220 to mem
mov [ rsp + 0x240 ], r15; spilling x348 to mem
mulx rdi, r15, r12; x267, x266<- x260 * 0xffffffffffffffff
setc dl; spill CF x290 to reg (rdx)
clc;
adcx r11, r9
adox r15, r14
setc r11b; spill CF x363 to reg (r11)
clc;
adcx rax, rbp
mov r14, [ rsp + 0xb8 ]; load m64 x239 to register64
seto r9b; spill OF x279 to reg (r9)
mov rbp, -0x1 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, rbp; loading flag
adox r14, [ rsp + 0x228 ]
mov r8b, dl; preserving value of x290 into a new reg
mov rdx, [ r10 + 0x0 ]; saving arg2[0] in rdx.
mov [ rsp + 0x248 ], rdi; spilling x267 to mem
mulx rbp, rdi, [ rsp + 0x220 ]; x388, x387<- x5 * arg2[0]
mov byte [ rsp + 0x250 ], r9b; spilling byte x279 to mem
seto r9b; spill OF x253 to reg (r9)
mov [ rsp + 0x258 ], rdi; spilling x387 to mem
mov rdi, -0x1 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdi, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, rdi; loading flag
adox r14, r15
setc r8b; spill CF x352 to reg (r8)
clc;
movzx rcx, cl
adcx rcx, rdi; loading flag
adcx rbx, [ rsp + 0x128 ]
setc cl; spill CF x326 to reg (rcx)
clc;
movzx r11, r11b
adcx r11, rdi; loading flag
adcx rbx, rax
mov r11, 0xffffffffffffffff ; moving imm to reg
mov rdx, r12; x260 to rdx
mulx r12, r15, r11; x265, x264<- x260 * 0xffffffffffffffff
mov rax, rdx; preserving value of x260 into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mulx rdi, r11, [ rsp + 0x220 ]; x386, x385<- x5 * arg2[1]
mov [ rsp + 0x260 ], r12; spilling x265 to mem
mov r12, 0xffffffffffffffff ; moving imm to reg
mov rdx, r12; 0xffffffffffffffff to rdx
mov [ rsp + 0x268 ], rdi; spilling x386 to mem
mulx r12, rdi, r13; x344, x343<- x337 * 0xffffffffffffffff
setc dl; spill CF x365 to reg (rdx)
clc;
adcx r11, rbp
seto bpl; spill OF x292 to reg (rbp)
mov [ rsp + 0x270 ], r12; spilling x344 to mem
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, [ rsp + 0x258 ]
setc r12b; spill CF x390 to reg (r12)
clc;
mov [ rsp + 0x278 ], r11; spilling x389 to mem
mov r11, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, r11; loading flag
adcx r14, [ rsp + 0x120 ]
mov rcx, 0x100000001 ; moving imm to reg
xchg rdx, rcx; 0x100000001, swapping with x365, which is currently in rdx
mov byte [ rsp + 0x280 ], r12b; spilling byte x390 to mem
mulx r11, r12, rbx; _, x414<- x400 * 0x100000001
setc r11b; spill CF x328 to reg (r11)
movzx rdx, byte [ rsp + 0x250 ]; load byte memx279 to register64
clc;
mov [ rsp + 0x288 ], r14; spilling x327 to mem
mov r14, -0x1 ; moving imm to reg
adcx rdx, r14; loading flag
adcx r15, [ rsp + 0x248 ]
mov rdx, 0xfffffffffffffffe ; moving imm to reg
mov byte [ rsp + 0x290 ], cl; spilling byte x365 to mem
mulx r14, rcx, r13; x346, x345<- x337 * 0xfffffffffffffffe
mov byte [ rsp + 0x298 ], r11b; spilling byte x328 to mem
mov r11, rdx; preserving value of 0xfffffffffffffffe into a new reg
mov rdx, [ r10 + 0x10 ]; saving arg2[2] in rdx.
mov [ rsp + 0x2a0 ], r15; spilling x280 to mem
mov byte [ rsp + 0x2a8 ], bpl; spilling byte x292 to mem
mulx r15, rbp, [ rsp + 0x220 ]; x384, x383<- x5 * arg2[2]
mov r11, [ rsp + 0xb0 ]; load m64 x241 to register64
mov [ rsp + 0x2b0 ], r15; spilling x384 to mem
seto r15b; spill OF x401 to reg (r15)
mov [ rsp + 0x2b8 ], rbp; spilling x383 to mem
mov rbp, -0x1 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, rbp; loading flag
adox r11, [ rsp + 0x218 ]
mov r9, 0xffffffff ; moving imm to reg
mov rdx, r12; x414 to rdx
mulx r12, rbp, r9; x427, x426<- x414 * 0xffffffff
seto r9b; spill OF x255 to reg (r9)
mov [ rsp + 0x2c0 ], r12; spilling x427 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, r12; loading flag
adox rcx, [ rsp + 0x240 ]
adox rdi, r14
mov r8, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r8; 0xffffffffffffffff, swapping with x414, which is currently in rdx
mulx rax, r14, rax; x263, x262<- x260 * 0xffffffffffffffff
setc r12b; spill CF x281 to reg (r12)
movzx rdx, byte [ rsp + 0x2a8 ]; load byte memx292 to register64
clc;
mov [ rsp + 0x2c8 ], rax; spilling x263 to mem
mov rax, -0x1 ; moving imm to reg
adcx rdx, rax; loading flag
adcx r11, [ rsp + 0x2a0 ]
seto dl; spill OF x356 to reg (rdx)
movzx rax, byte [ rsp + 0x298 ]; load byte memx328 to register64
mov [ rsp + 0x2d0 ], r14; spilling x262 to mem
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rax, r14; loading flag
adox r11, [ rsp + 0x118 ]
mov rax, 0xfffffffffffffffe ; moving imm to reg
xchg rdx, rax; 0xfffffffffffffffe, swapping with x356, which is currently in rdx
mov byte [ rsp + 0x2d8 ], al; spilling byte x356 to mem
mulx r14, rax, r8; x423, x422<- x414 * 0xfffffffffffffffe
seto dl; spill OF x330 to reg (rdx)
mov [ rsp + 0x2e0 ], r14; spilling x423 to mem
movzx r14, byte [ rsp + 0x290 ]; load byte memx365 to register64
mov byte [ rsp + 0x2e8 ], r12b; spilling byte x281 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r14, r12; loading flag
adox rcx, [ rsp + 0x288 ]
mov r14, 0xffffffff00000000 ; moving imm to reg
xchg rdx, r14; 0xffffffff00000000, swapping with x330, which is currently in rdx
mov byte [ rsp + 0x2f0 ], r14b; spilling byte x330 to mem
mulx r12, r14, r8; x425, x424<- x414 * 0xffffffff00000000
adox rdi, r11
seto r11b; spill OF x369 to reg (r11)
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r15, r15b
adox r15, rdx; loading flag
adox rcx, [ rsp + 0x278 ]
setc r15b; spill CF x294 to reg (r15)
clc;
adcx rbp, rbx
mov rbp, [ rsp + 0xd8 ]; load m64 x243 to register64
seto bl; spill OF x403 to reg (rbx)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, rdx; loading flag
adox rbp, [ rsp + 0x238 ]
seto r9b; spill OF x257 to reg (r9)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r14, [ rsp + 0x2c0 ]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov byte [ rsp + 0x2f8 ], r11b; spilling byte x369 to mem
mov byte [ rsp + 0x300 ], r9b; spilling byte x257 to mem
mulx r11, r9, r13; x340, x339<- x337 * 0xffffffffffffffff
adcx r14, rcx
mov rcx, [ rsp + 0x2b8 ]; load m64 x383 to register64
setc dl; spill CF x442 to reg (rdx)
mov [ rsp + 0x308 ], r14; spilling x441 to mem
movzx r14, byte [ rsp + 0x280 ]; load byte memx390 to register64
clc;
mov [ rsp + 0x310 ], r11; spilling x340 to mem
mov r11, -0x1 ; moving imm to reg
adcx r14, r11; loading flag
adcx rcx, [ rsp + 0x268 ]
adox rax, r12
setc r14b; spill CF x392 to reg (r14)
clc;
movzx rbx, bl
adcx rbx, r11; loading flag
adcx rdi, rcx
mov r12, [ rsp + 0x2d0 ]; load m64 x262 to register64
setc bl; spill CF x405 to reg (rbx)
movzx rcx, byte [ rsp + 0x2e8 ]; load byte memx281 to register64
clc;
adcx rcx, r11; loading flag
adcx r12, [ rsp + 0x260 ]
mov cl, dl; preserving value of x442 into a new reg
mov rdx, [ rsp + 0x220 ]; saving x5 in rdx.
mov byte [ rsp + 0x318 ], bl; spilling byte x405 to mem
mulx r11, rbx, [ r10 + 0x18 ]; x382, x381<- x5 * arg2[3]
mov [ rsp + 0x320 ], r11; spilling x382 to mem
setc r11b; spill CF x283 to reg (r11)
clc;
mov [ rsp + 0x328 ], r9; spilling x339 to mem
mov r9, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, r9; loading flag
adcx rdi, rax
movzx rcx, r11b; x284, copying x283 here, cause x283 is needed in a reg for other than x284, namely all: , x284, size: 1
mov rax, [ rsp + 0x2c8 ]; load m64 x263 to register64
lea rcx, [ rcx + rax ]; r8/64 + m8
seto al; spill OF x431 to reg (rax)
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r11, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, r11; loading flag
adox rbp, r12
seto r15b; spill OF x296 to reg (r15)
dec r9; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx r14, r14b
adox r14, r9; loading flag
adox rbx, [ rsp + 0x2b0 ]
mov r11, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r8; x414, swapping with x5, which is currently in rdx
mulx r14, r12, r11; x421, x420<- x414 * 0xffffffffffffffff
setc r9b; spill CF x444 to reg (r9)
movzx r11, byte [ rsp + 0x2f0 ]; load byte memx330 to register64
clc;
mov [ rsp + 0x330 ], rdi; spilling x443 to mem
mov rdi, -0x1 ; moving imm to reg
adcx r11, rdi; loading flag
adcx rbp, [ rsp + 0x110 ]
setc r11b; spill CF x332 to reg (r11)
clc;
movzx rax, al
adcx rax, rdi; loading flag
adcx r12, [ rsp + 0x2e0 ]
mov rax, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r13; x337, swapping with x414, which is currently in rdx
mulx rdx, rdi, rax; x342, x341<- x337 * 0xffffffffffffffff
seto al; spill OF x394 to reg (rax)
mov [ rsp + 0x338 ], r14; spilling x421 to mem
movzx r14, byte [ rsp + 0x2d8 ]; load byte memx356 to register64
mov [ rsp + 0x340 ], r12; spilling x432 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r14, r12; loading flag
adox rdi, [ rsp + 0x270 ]
mov r14, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r14; 0xffffffffffffffff, swapping with x342, which is currently in rdx
mov byte [ rsp + 0x348 ], r9b; spilling byte x444 to mem
mulx r12, r9, r13; x419, x418<- x414 * 0xffffffffffffffff
mov rdx, [ rsp + 0x328 ]; x359, copying x339 here, cause x339 is needed in a reg for other than x359, namely all: , x359--x360, size: 1
adox rdx, r14
mov r14, [ rsp + 0x100 ]; load m64 x245 to register64
mov [ rsp + 0x350 ], r12; spilling x419 to mem
seto r12b; spill OF x360 to reg (r12)
mov [ rsp + 0x358 ], r9; spilling x418 to mem
movzx r9, byte [ rsp + 0x300 ]; load byte memx257 to register64
mov [ rsp + 0x360 ], rdx; spilling x359 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r9, rdx; loading flag
adox r14, [ rsp + 0x230 ]
mov rdx, r8; x5 to rdx
mulx r8, r9, [ r10 + 0x28 ]; x378, x377<- x5 * arg2[5]
mov [ rsp + 0x368 ], r8; spilling x378 to mem
mulx rdx, r8, [ r10 + 0x20 ]; x380, x379<- x5 * arg2[4]
mov byte [ rsp + 0x370 ], r11b; spilling byte x332 to mem
seto r11b; spill OF x259 to reg (r11)
mov [ rsp + 0x378 ], r9; spilling x377 to mem
movzx r9, byte [ rsp + 0x2f8 ]; load byte memx369 to register64
mov [ rsp + 0x380 ], rdx; spilling x380 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r9, rdx; loading flag
adox rbp, rdi
movzx r9, r12b; x361, copying x360 here, cause x360 is needed in a reg for other than x361, namely all: , x361, size: 1
mov rdi, [ rsp + 0x310 ]; load m64 x340 to register64
lea r9, [ r9 + rdi ]; r8/64 + m8
seto dil; spill OF x371 to reg (rdi)
movzx r12, byte [ rsp + 0x318 ]; load byte memx405 to register64
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
adox r12, rdx; loading flag
adox rbp, rbx
setc r12b; spill CF x433 to reg (r12)
clc;
movzx r15, r15b
adcx r15, rdx; loading flag
adcx r14, rcx
setc cl; spill CF x298 to reg (rcx)
clc;
movzx rax, al
adcx rax, rdx; loading flag
adcx r8, [ rsp + 0x320 ]
movzx r15, cl; x299, copying x298 here, cause x298 is needed in a reg for other than x299, namely all: , x299, size: 1
movzx r11, r11b
lea r15, [ r15 + r11 ]
mov rbx, [ rsp + 0x378 ]; load m64 x377 to register64
mov rax, [ rsp + 0x380 ]; x397, copying x380 here, cause x380 is needed in a reg for other than x397, namely all: , x397--x398, size: 1
adcx rax, rbx
seto r11b; spill OF x407 to reg (r11)
movzx rbx, byte [ rsp + 0x370 ]; load byte memx332 to register64
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rcx, -0x1 ; moving imm to reg
adox rbx, rcx; loading flag
adox r14, [ rsp + 0x108 ]
setc bl; spill CF x398 to reg (rbx)
clc;
movzx rdi, dil
adcx rdi, rcx; loading flag
adcx r14, [ rsp + 0x360 ]
mov rdi, [ rsp + 0x190 ]; x335, copying x322 here, cause x322 is needed in a reg for other than x335, namely all: , x335--x336, size: 1
adox rdi, r15
seto r15b; spill OF x336 to reg (r15)
movzx rdx, byte [ rsp + 0x348 ]; load byte memx444 to register64
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rcx, -0x1 ; moving imm to reg
adox rdx, rcx; loading flag
adox rbp, [ rsp + 0x340 ]
adcx r9, rdi
mov rdx, [ rsp + 0x358 ]; load m64 x418 to register64
seto dil; spill OF x446 to reg (rdi)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rcx, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, rcx; loading flag
adox rdx, [ rsp + 0x338 ]
movzx r12, bl; x399, copying x398 here, cause x398 is needed in a reg for other than x399, namely all: , x399, size: 1
mov rcx, [ rsp + 0x368 ]; load m64 x378 to register64
lea r12, [ r12 + rcx ]; r8/64 + m8
setc cl; spill CF x375 to reg (rcx)
clc;
mov rbx, -0x1 ; moving imm to reg
movzx r11, r11b
adcx r11, rbx; loading flag
adcx r14, r8
movzx r11, cl; x376, copying x375 here, cause x375 is needed in a reg for other than x376, namely all: , x376, size: 1
movzx r15, r15b
lea r11, [ r11 + r15 ]
adcx rax, r9
mov r8, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r13; x414, swapping with x434, which is currently in rdx
mulx rdx, r15, r8; x417, x416<- x414 * 0xffffffffffffffff
mov rcx, [ rsp + 0x350 ]; x436, copying x419 here, cause x419 is needed in a reg for other than x436, namely all: , x436--x437, size: 1
adox rcx, r15
mov r9, 0x0 ; moving imm to reg
adox rdx, r9
setc r15b; spill CF x411 to reg (r15)
mov rbx, [ rsp + 0x308 ]; x454, copying x441 here, cause x441 is needed in a reg for other than x454, namely all: , x468, x454--x455, size: 2
mov r8, 0xffffffff ; moving imm to reg
sub rbx, r8
mov r9, [ rsp + 0x330 ]; x456, copying x443 here, cause x443 is needed in a reg for other than x456, namely all: , x456--x457, x469, size: 2
mov r8, 0xffffffff00000000 ; moving imm to reg
sbb r9, r8
mov r8, -0x1 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r8, -0x1 ; moving imm to reg
movzx rdi, dil
adox rdi, r8; loading flag
adox r14, r13
seto dil; spill OF x448 to reg (rdi)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, r13; loading flag
adox r11, r12
seto r12b; spill OF x413 to reg (r12)
dec r8; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx rdi, dil
adox rdi, r8; loading flag
adox rax, rcx
adox rdx, r11
seto r13b; spill OF x452 to reg (r13)
mov r15, rbp; x458, copying x445 here, cause x445 is needed in a reg for other than x458, namely all: , x470, x458--x459, size: 2
mov rcx, 0xfffffffffffffffe ; moving imm to reg
sbb r15, rcx
movzx rdi, r13b; x453, copying x452 here, cause x452 is needed in a reg for other than x453, namely all: , x453, size: 1
movzx r12, r12b
lea rdi, [ rdi + r12 ]
mov r11, r14; x460, copying x447 here, cause x447 is needed in a reg for other than x460, namely all: , x471, x460--x461, size: 2
mov r12, 0xffffffffffffffff ; moving imm to reg
sbb r11, r12
mov r13, rax; x462, copying x449 here, cause x449 is needed in a reg for other than x462, namely all: , x462--x463, x472, size: 2
sbb r13, r12
mov r8, rdx; x464, copying x451 here, cause x451 is needed in a reg for other than x464, namely all: , x473, x464--x465, size: 2
sbb r8, r12
sbb rdi, 0x00000000
cmovc r11, r14; if CF, x471<- x447 (nzVar)
cmovc r8, rdx; if CF, x473<- x451 (nzVar)
cmovc rbx, [ rsp + 0x308 ]; if CF, x468<- x441 (nzVar)
mov r14, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r14 + 0x18 ], r11; out1[3] = x471
cmovc r13, rax; if CF, x472<- x449 (nzVar)
mov [ r14 + 0x0 ], rbx; out1[0] = x468
cmovc r9, [ rsp + 0x330 ]; if CF, x469<- x443 (nzVar)
cmovc r15, rbp; if CF, x470<- x445 (nzVar)
mov [ r14 + 0x10 ], r15; out1[2] = x470
mov [ r14 + 0x20 ], r13; out1[4] = x472
mov [ r14 + 0x8 ], r9; out1[1] = x469
mov [ r14 + 0x28 ], r8; out1[5] = x473
mov rbx, [ rsp + 0x388 ]; restoring from stack
mov rbp, [ rsp + 0x390 ]; restoring from stack
mov r12, [ rsp + 0x398 ]; restoring from stack
mov r13, [ rsp + 0x3a0 ]; restoring from stack
mov r14, [ rsp + 0x3a8 ]; restoring from stack
mov r15, [ rsp + 0x3b0 ]; restoring from stack
add rsp, 0x3b8 
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; clocked at 2200 MHz
; first cyclecount 373.16, best 293.28205128205127, lastGood 306
; seed 1466306520902851 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4950505 ms / 60000 runs=> 82.50841666666666ms/run
; Time spent for assembling and measureing (initial batch_size=38, initial num_batches=101): 187320 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.037838563944486474
; number reverted permutation/ tried permutation: 20462 / 30023 =68.154%
; number reverted decision/ tried decision: 18333 / 29978 =61.155%