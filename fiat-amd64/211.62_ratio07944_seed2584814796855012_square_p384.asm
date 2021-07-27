SECTION .text
	GLOBAL square_p384
square_p384:
sub rsp, 0x510 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x4e0 ], rbx; saving to stack
mov [ rsp + 0x4e8 ], rbp; saving to stack
mov [ rsp + 0x4f0 ], r12; saving to stack
mov [ rsp + 0x4f8 ], r13; saving to stack
mov [ rsp + 0x500 ], r14; saving to stack
mov [ rsp + 0x508 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x6 to register64
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r10, r11, rax; x16, x15<- x6 * arg1[1]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rbx, rbp, rax; x12, x11<- x6 * arg1[3]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r12, r13, rax; x18, x17<- x6 * arg1[0]
xor r14, r14
adox r11, r12
mov r15, [ rsi + 0x20 ]; load m64 x4 to register64
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx rcx, r8, rax; x10, x9<- x6 * arg1[4]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r9, r12, r15; x303, x302<- x4 * arg1[4]
mov rdx, rax; x6 to rdx
mulx rax, r14, [ rsi + 0x10 ]; x14, x13<- x6 * arg1[2]
adox r14, r10
adox rbp, rax
adox r8, rbx
mov r10, rdx; preserving value of x6 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx rbx, rax, r15; x307, x306<- x4 * arg1[2]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov [ rsp + 0x8 ], r8; spilling x25 to mem
mulx rdi, r8, r15; x305, x304<- x4 * arg1[3]
mov rdx, r10; x6 to rdx
mulx rdx, r10, [ rsi + 0x28 ]; x8, x7<- x6 * arg1[5]
xchg rdx, r15; x4, swapping with x8, which is currently in rdx
mov [ rsp + 0x10 ], rbp; spilling x23 to mem
mov [ rsp + 0x18 ], r14; spilling x21 to mem
mulx rbp, r14, [ rsi + 0x8 ]; x309, x308<- x4 * arg1[1]
adox r10, rcx
mov [ rsp + 0x20 ], r10; spilling x27 to mem
mulx rcx, r10, [ rsi + 0x0 ]; x311, x310<- x4 * arg1[0]
mov [ rsp + 0x28 ], r10; spilling x310 to mem
mov r10, 0x0 ; moving imm to reg
adox r15, r10
mulx rdx, r10, [ rsi + 0x28 ]; x301, x300<- x4 * arg1[5]
mov [ rsp + 0x30 ], r15; spilling x29 to mem
mov r15, [ rsi + 0x10 ]; load m64 x2 to register64
adcx r14, rcx
xchg rdx, r15; x2, swapping with x301, which is currently in rdx
mov [ rsp + 0x38 ], r14; spilling x312 to mem
mulx rcx, r14, [ rsi + 0x28 ]; x147, x146<- x2 * arg1[5]
adcx rax, rbp
mov [ rsp + 0x40 ], rax; spilling x314 to mem
mulx rbp, rax, [ rsi + 0x18 ]; x151, x150<- x2 * arg1[3]
adcx r8, rbx
mov [ rsp + 0x48 ], r8; spilling x316 to mem
mulx rbx, r8, [ rsi + 0x8 ]; x155, x154<- x2 * arg1[1]
mov [ rsp + 0x50 ], r11; spilling x19 to mem
mov r11, [ rsi + 0x18 ]; load m64 x3 to register64
mov [ rsp + 0x58 ], rcx; spilling x147 to mem
mov [ rsp + 0x60 ], r13; spilling x17 to mem
mulx rcx, r13, [ rsi + 0x0 ]; x157, x156<- x2 * arg1[0]
mov [ rsp + 0x68 ], r13; spilling x156 to mem
mov [ rsp + 0x70 ], r15; spilling x301 to mem
mulx r13, r15, [ rsi + 0x10 ]; x153, x152<- x2 * arg1[2]
mov [ rsp + 0x78 ], r14; spilling x146 to mem
mulx rdx, r14, [ rsi + 0x20 ]; x149, x148<- x2 * arg1[4]
mov [ rsp + 0x80 ], rdx; spilling x149 to mem
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, rcx
adox r15, rbx
adox rax, r13
adcx r12, rdi
adcx r10, r9
adox r14, rbp
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r9, rdi, r11; x234, x233<- x3 * arg1[0]
mov rdx, r11; x3 to rdx
mulx r11, rbp, [ rsi + 0x20 ]; x226, x225<- x3 * arg1[4]
mov rbx, [ rsp + 0x78 ]; load m64 x146 to register64
mov rcx, [ rsp + 0x80 ]; x166, copying x149 here, cause x149 is needed in a reg for other than x166, namely all: , x166--x167, size: 1
adox rcx, rbx
mulx rbx, r13, [ rsi + 0x18 ]; x228, x227<- x3 * arg1[3]
mov [ rsp + 0x88 ], r10; spilling x320 to mem
mov r10, [ rsi + 0x8 ]; load m64 x1 to register64
mov [ rsp + 0x90 ], r12; spilling x318 to mem
mov [ rsp + 0x98 ], rcx; spilling x166 to mem
mulx r12, rcx, [ rsi + 0x10 ]; x230, x229<- x3 * arg1[2]
mov [ rsp + 0xa0 ], r14; spilling x164 to mem
mov [ rsp + 0xa8 ], rax; spilling x162 to mem
mulx r14, rax, [ rsi + 0x8 ]; x232, x231<- x3 * arg1[1]
mov [ rsp + 0xb0 ], r15; spilling x160 to mem
mov r15, [ rsp + 0x70 ]; x322, copying x301 here, cause x301 is needed in a reg for other than x322, namely all: , x322, size: 1
mov [ rsp + 0xb8 ], rdi; spilling x233 to mem
mov rdi, 0x0 ; moving imm to reg
adcx r15, rdi
xchg rdx, r10; x1, swapping with x3, which is currently in rdx
mov [ rsp + 0xc0 ], r15; spilling x322 to mem
mulx rdi, r15, [ rsi + 0x0 ]; x80, x79<- x1 * arg1[0]
clc;
adcx rax, r9
adcx rcx, r14
adcx r13, r12
mov r9, 0x100000001 ; moving imm to reg
mov r12, rdx; preserving value of x1 into a new reg
mov rdx, [ rsp + 0x60 ]; saving x17 in rdx.
mov [ rsp + 0xc8 ], r13; spilling x239 to mem
mulx r14, r13, r9; _, x30<- x17 * 0x100000001
xchg rdx, r12; x1, swapping with x17, which is currently in rdx
mulx r14, r9, [ rsi + 0x10 ]; x76, x75<- x1 * arg1[2]
mov [ rsp + 0xd0 ], rcx; spilling x237 to mem
mov [ rsp + 0xd8 ], rax; spilling x235 to mem
mulx rcx, rax, [ rsi + 0x20 ]; x72, x71<- x1 * arg1[4]
mov [ rsp + 0xe0 ], r8; spilling x158 to mem
mov r8, [ rsp + 0x58 ]; x168, copying x147 here, cause x147 is needed in a reg for other than x168, namely all: , x168, size: 1
mov [ rsp + 0xe8 ], rcx; spilling x72 to mem
mov rcx, 0x0 ; moving imm to reg
adox r8, rcx
mov rcx, 0xffffffff ; moving imm to reg
xchg rdx, rcx; 0xffffffff, swapping with x1, which is currently in rdx
mov [ rsp + 0xf0 ], r8; spilling x168 to mem
mov [ rsp + 0xf8 ], rax; spilling x71 to mem
mulx r8, rax, r13; x43, x42<- x30 * 0xffffffff
adcx rbp, rbx
xchg rdx, r10; x3, swapping with 0xffffffff, which is currently in rdx
mulx rdx, rbx, [ rsi + 0x28 ]; x224, x223<- x3 * arg1[5]
mov r10, rdx; preserving value of x224 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x100 ], rbp; spilling x241 to mem
mov [ rsp + 0x108 ], r15; spilling x79 to mem
mulx rbp, r15, rcx; x78, x77<- x1 * arg1[1]
mov rdx, 0xfffffffffffffffe ; moving imm to reg
mov [ rsp + 0x110 ], rax; spilling x42 to mem
mov [ rsp + 0x118 ], r14; spilling x76 to mem
mulx rax, r14, r13; x39, x38<- x30 * 0xfffffffffffffffe
adcx rbx, r11
adc r10, 0x0
add r15, rdi; could be done better, if r0 has been u8 as well
xchg rdx, rcx; x1, swapping with 0xfffffffffffffffe, which is currently in rdx
mulx r11, rdi, [ rsi + 0x28 ]; x70, x69<- x1 * arg1[5]
mov rcx, 0xffffffff00000000 ; moving imm to reg
xchg rdx, rcx; 0xffffffff00000000, swapping with x1, which is currently in rdx
mov [ rsp + 0x120 ], r10; spilling x245 to mem
mov [ rsp + 0x128 ], rbx; spilling x243 to mem
mulx r10, rbx, r13; x41, x40<- x30 * 0xffffffff00000000
mov [ rsp + 0x130 ], r15; spilling x81 to mem
mov r15, rdx; preserving value of 0xffffffff00000000 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x138 ], rax; spilling x39 to mem
mulx rcx, rax, rcx; x74, x73<- x1 * arg1[3]
adcx r9, rbp
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, r8
mov r8, [ rsp + 0x118 ]; x85, copying x76 here, cause x76 is needed in a reg for other than x85, namely all: , x85--x86, size: 1
adcx r8, rax
setc bpl; spill CF x86 to reg (rbp)
clc;
adcx r12, [ rsp + 0x110 ]
mov r12, [ rsp + 0x50 ]; x57, copying x19 here, cause x19 is needed in a reg for other than x57, namely all: , x57--x58, size: 1
adcx r12, rbx
adox r14, r10
setc r10b; spill CF x58 to reg (r10)
clc;
adcx r12, [ rsp + 0x108 ]
setc al; spill CF x93 to reg (rax)
clc;
movzx rbp, bpl
adcx rbp, rdx; loading flag
adcx rcx, [ rsp + 0xf8 ]
seto bl; spill OF x47 to reg (rbx)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx r10, r10b
adox r10, rbp; loading flag
adox r14, [ rsp + 0x18 ]
mov r10, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r13; x30, swapping with 0x0, which is currently in rdx
mulx r13, rbp, r10; x37, x36<- x30 * 0xffffffffffffffff
mov r10, 0x100000001 ; moving imm to reg
xchg rdx, r10; 0x100000001, swapping with x30, which is currently in rdx
mov [ rsp + 0x140 ], rcx; spilling x87 to mem
mulx r15, rcx, r12; _, x106<- x92 * 0x100000001
mov r15, [ rsp + 0xe8 ]; x89, copying x72 here, cause x72 is needed in a reg for other than x89, namely all: , x89--x90, size: 1
adcx r15, rdi
mov rdi, 0xffffffff ; moving imm to reg
xchg rdx, rcx; x106, swapping with 0x100000001, which is currently in rdx
mov [ rsp + 0x148 ], r15; spilling x89 to mem
mulx rcx, r15, rdi; x119, x118<- x106 * 0xffffffff
setc dil; spill CF x90 to reg (rdi)
clc;
adcx r15, r12
movzx r15, dil; x91, copying x90 here, cause x90 is needed in a reg for other than x91, namely all: , x91, size: 1
lea r15, [ r15 + r11 ]
setc r11b; spill CF x132 to reg (r11)
clc;
mov r12, -0x1 ; moving imm to reg
movzx rbx, bl
adcx rbx, r12; loading flag
adcx rbp, [ rsp + 0x138 ]
mov rbx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbx; 0xffffffffffffffff, swapping with x106, which is currently in rdx
mulx rdi, r12, r10; x35, x34<- x30 * 0xffffffffffffffff
mov rdx, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x150 ], r15; spilling x91 to mem
mov [ rsp + 0x158 ], rdi; spilling x35 to mem
mulx r15, rdi, rbx; x117, x116<- x106 * 0xffffffff00000000
setc dl; spill CF x49 to reg (rdx)
clc;
mov [ rsp + 0x160 ], r8; spilling x85 to mem
mov r8, -0x1 ; moving imm to reg
movzx rax, al
adcx rax, r8; loading flag
adcx r14, [ rsp + 0x130 ]
mov rax, 0xfffffffffffffffe ; moving imm to reg
xchg rdx, rbx; x106, swapping with x49, which is currently in rdx
mov [ rsp + 0x168 ], r12; spilling x34 to mem
mulx r8, r12, rax; x115, x114<- x106 * 0xfffffffffffffffe
mov rax, [ rsp + 0x10 ]; x61, copying x23 here, cause x23 is needed in a reg for other than x61, namely all: , x61--x62, size: 1
adox rax, rbp
adcx r9, rax
seto bpl; spill OF x62 to reg (rbp)
mov rax, -0x2 ; moving imm to reg
inc rax; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rdi, rcx
mov rcx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x170 ], r8; spilling x115 to mem
mulx rax, r8, rcx; x113, x112<- x106 * 0xffffffffffffffff
adox r12, r15
seto r15b; spill OF x123 to reg (r15)
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r11, r11b
adox r11, rcx; loading flag
adox r14, rdi
adox r12, r9
setc r11b; spill CF x97 to reg (r11)
clc;
adcx r14, [ rsp + 0x68 ]
setc r9b; spill CF x170 to reg (r9)
clc;
movzx rbx, bl
adcx rbx, rcx; loading flag
adcx r13, [ rsp + 0x168 ]
mov rbx, 0x100000001 ; moving imm to reg
xchg rdx, rbx; 0x100000001, swapping with x106, which is currently in rdx
mulx rdi, rcx, r14; _, x183<- x169 * 0x100000001
mov rdx, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x178 ], rax; spilling x113 to mem
mov byte [ rsp + 0x180 ], r11b; spilling byte x97 to mem
mulx rax, r11, rcx; x194, x193<- x183 * 0xffffffff00000000
seto dl; spill OF x136 to reg (rdx)
mov [ rsp + 0x188 ], rax; spilling x194 to mem
mov rax, -0x1 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rax, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, rax; loading flag
adox r13, [ rsp + 0x8 ]
mov rbp, 0xffffffff ; moving imm to reg
xchg rdx, rcx; x183, swapping with x136, which is currently in rdx
mov byte [ rsp + 0x190 ], cl; spilling byte x136 to mem
mulx rax, rcx, rbp; x196, x195<- x183 * 0xffffffff
setc bpl; spill CF x51 to reg (rbp)
clc;
adcx r11, rax
seto al; spill OF x64 to reg (rax)
mov byte [ rsp + 0x198 ], bpl; spilling byte x51 to mem
mov rbp, -0x1 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, rbp; loading flag
adox r12, [ rsp + 0xe0 ]
setc r9b; spill CF x198 to reg (r9)
clc;
movzx r15, r15b
adcx r15, rbp; loading flag
adcx r8, [ rsp + 0x170 ]
setc r15b; spill CF x125 to reg (r15)
clc;
adcx rcx, r14
adcx r11, r12
setc cl; spill CF x211 to reg (rcx)
clc;
adcx r11, [ rsp + 0xb8 ]
setc r14b; spill CF x247 to reg (r14)
movzx r12, byte [ rsp + 0x180 ]; load byte memx97 to register64
clc;
adcx r12, rbp; loading flag
adcx r13, [ rsp + 0x160 ]
mov r12, 0xfffffffffffffffe ; moving imm to reg
mov byte [ rsp + 0x1a0 ], al; spilling byte x64 to mem
mulx rbp, rax, r12; x192, x191<- x183 * 0xfffffffffffffffe
mov r12, 0x100000001 ; moving imm to reg
xchg rdx, r12; 0x100000001, swapping with x183, which is currently in rdx
mov [ rsp + 0x1a8 ], rbp; spilling x192 to mem
mov byte [ rsp + 0x1b0 ], r15b; spilling byte x125 to mem
mulx rbp, r15, r11; _, x260<- x246 * 0x100000001
setc bpl; spill CF x99 to reg (rbp)
clc;
mov rdx, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, rdx; loading flag
adcx rax, [ rsp + 0x188 ]
mov r9, 0xffffffff ; moving imm to reg
mov rdx, r15; x260 to rdx
mov byte [ rsp + 0x1b8 ], bpl; spilling byte x99 to mem
mulx r15, rbp, r9; x273, x272<- x260 * 0xffffffff
mov r9, 0xffffffff00000000 ; moving imm to reg
mov byte [ rsp + 0x1c0 ], r14b; spilling byte x247 to mem
mov [ rsp + 0x1c8 ], rbp; spilling x272 to mem
mulx r14, rbp, r9; x271, x270<- x260 * 0xffffffff00000000
setc r9b; spill CF x200 to reg (r9)
clc;
adcx rbp, r15
setc r15b; spill CF x275 to reg (r15)
mov [ rsp + 0x1d0 ], r14; spilling x271 to mem
movzx r14, byte [ rsp + 0x190 ]; load byte memx136 to register64
clc;
mov byte [ rsp + 0x1d8 ], r9b; spilling byte x200 to mem
mov r9, -0x1 ; moving imm to reg
adcx r14, r9; loading flag
adcx r13, r8
mov r14, [ rsp + 0xb0 ]; x173, copying x160 here, cause x160 is needed in a reg for other than x173, namely all: , x173--x174, size: 1
adox r14, r13
setc r8b; spill CF x138 to reg (r8)
clc;
movzx rcx, cl
adcx rcx, r9; loading flag
adcx r14, rax
setc cl; spill CF x213 to reg (rcx)
clc;
adcx r11, [ rsp + 0x1c8 ]
mov r11, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r11; 0xffffffffffffffff, swapping with x260, which is currently in rdx
mulx rax, r13, rbx; x111, x110<- x106 * 0xffffffffffffffff
seto r9b; spill OF x174 to reg (r9)
movzx rdx, byte [ rsp + 0x1c0 ]; load byte memx247 to register64
mov [ rsp + 0x1e0 ], rax; spilling x111 to mem
mov rax, -0x1 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rax, -0x1 ; moving imm to reg
adox rdx, rax; loading flag
adox r14, [ rsp + 0xd8 ]
adcx rbp, r14
setc dl; spill CF x288 to reg (rdx)
clc;
adcx rbp, [ rsp + 0x28 ]
mov r14, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r14; 0xffffffffffffffff, swapping with x288, which is currently in rdx
mulx r10, rax, r10; x33, x32<- x30 * 0xffffffffffffffff
seto dl; spill OF x249 to reg (rdx)
mov byte [ rsp + 0x1e8 ], r14b; spilling byte x288 to mem
movzx r14, byte [ rsp + 0x1b0 ]; load byte memx125 to register64
mov byte [ rsp + 0x1f0 ], r15b; spilling byte x275 to mem
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r15, -0x1 ; moving imm to reg
adox r14, r15; loading flag
adox r13, [ rsp + 0x178 ]
setc r14b; spill CF x324 to reg (r14)
movzx r15, byte [ rsp + 0x198 ]; load byte memx51 to register64
clc;
mov byte [ rsp + 0x1f8 ], dl; spilling byte x249 to mem
mov rdx, -0x1 ; moving imm to reg
adcx r15, rdx; loading flag
adcx rax, [ rsp + 0x158 ]
mov r15, 0xffffffffffffffff ; moving imm to reg
mov rdx, r12; x183 to rdx
mov byte [ rsp + 0x200 ], r14b; spilling byte x324 to mem
mulx r12, r14, r15; x190, x189<- x183 * 0xffffffffffffffff
mov r15, 0x100000001 ; moving imm to reg
xchg rdx, r15; 0x100000001, swapping with x183, which is currently in rdx
mov [ rsp + 0x208 ], r12; spilling x190 to mem
mov byte [ rsp + 0x210 ], cl; spilling byte x213 to mem
mulx r12, rcx, rbp; _, x337<- x323 * 0x100000001
mov r12, 0x0 ; moving imm to reg
adcx r10, r12
mov r12, 0xffffffff ; moving imm to reg
xchg rdx, r12; 0xffffffff, swapping with 0x100000001, which is currently in rdx
mov [ rsp + 0x218 ], r10; spilling x54 to mem
mulx r12, r10, rcx; x350, x349<- x337 * 0xffffffff
movzx rdx, byte [ rsp + 0x1a0 ]; load byte memx64 to register64
clc;
mov [ rsp + 0x220 ], r12; spilling x350 to mem
mov r12, -0x1 ; moving imm to reg
adcx rdx, r12; loading flag
adcx rax, [ rsp + 0x20 ]
setc dl; spill CF x66 to reg (rdx)
movzx r12, byte [ rsp + 0x1b8 ]; load byte memx99 to register64
clc;
mov byte [ rsp + 0x228 ], r9b; spilling byte x174 to mem
mov r9, -0x1 ; moving imm to reg
adcx r12, r9; loading flag
adcx rax, [ rsp + 0x140 ]
setc r12b; spill CF x101 to reg (r12)
movzx r9, byte [ rsp + 0x1d8 ]; load byte memx200 to register64
clc;
mov byte [ rsp + 0x230 ], dl; spilling byte x66 to mem
mov rdx, -0x1 ; moving imm to reg
adcx r9, rdx; loading flag
adcx r14, [ rsp + 0x1a8 ]
setc r9b; spill CF x202 to reg (r9)
clc;
movzx r8, r8b
adcx r8, rdx; loading flag
adcx rax, r13
mov r8, 0xfffffffffffffffe ; moving imm to reg
mov rdx, r8; 0xfffffffffffffffe to rdx
mulx r8, r13, r11; x269, x268<- x260 * 0xfffffffffffffffe
setc dl; spill CF x140 to reg (rdx)
clc;
adcx r10, rbp
setc r10b; spill CF x363 to reg (r10)
movzx rbp, byte [ rsp + 0x228 ]; load byte memx174 to register64
clc;
mov byte [ rsp + 0x238 ], dl; spilling byte x140 to mem
mov rdx, -0x1 ; moving imm to reg
adcx rbp, rdx; loading flag
adcx rax, [ rsp + 0xa8 ]
mov rbp, 0xffffffff00000000 ; moving imm to reg
mov rdx, rbp; 0xffffffff00000000 to rdx
mov byte [ rsp + 0x240 ], r10b; spilling byte x363 to mem
mulx rbp, r10, rcx; x348, x347<- x337 * 0xffffffff00000000
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x248 ], rbp; spilling x348 to mem
mov [ rsp + 0x250 ], r8; spilling x269 to mem
mulx rbp, r8, r11; x267, x266<- x260 * 0xffffffffffffffff
setc dl; spill CF x176 to reg (rdx)
clc;
adcx r10, [ rsp + 0x220 ]
mov [ rsp + 0x258 ], rbp; spilling x267 to mem
mov rbp, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r15; x183, swapping with x176, which is currently in rdx
mov byte [ rsp + 0x260 ], r15b; spilling byte x176 to mem
mov [ rsp + 0x268 ], r10; spilling x351 to mem
mulx r15, r10, rbp; x188, x187<- x183 * 0xffffffffffffffff
seto bpl; spill OF x127 to reg (rbp)
mov [ rsp + 0x270 ], r15; spilling x188 to mem
movzx r15, byte [ rsp + 0x210 ]; load byte memx213 to register64
mov [ rsp + 0x278 ], r8; spilling x266 to mem
mov r8, -0x1 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r8, -0x1 ; moving imm to reg
adox r15, r8; loading flag
adox rax, r14
setc r15b; spill CF x352 to reg (r15)
movzx r14, byte [ rsp + 0x1f0 ]; load byte memx275 to register64
clc;
adcx r14, r8; loading flag
adcx r13, [ rsp + 0x1d0 ]
setc r14b; spill CF x277 to reg (r14)
movzx r8, byte [ rsp + 0x1f8 ]; load byte memx249 to register64
clc;
mov byte [ rsp + 0x280 ], r15b; spilling byte x352 to mem
mov r15, -0x1 ; moving imm to reg
adcx r8, r15; loading flag
adcx rax, [ rsp + 0xd0 ]
setc r8b; spill CF x251 to reg (r8)
movzx r15, byte [ rsp + 0x1e8 ]; load byte memx288 to register64
clc;
mov byte [ rsp + 0x288 ], r14b; spilling byte x277 to mem
mov r14, -0x1 ; moving imm to reg
adcx r15, r14; loading flag
adcx rax, r13
mov r15, 0xfffffffffffffffe ; moving imm to reg
xchg rdx, r15; 0xfffffffffffffffe, swapping with x183, which is currently in rdx
mulx r13, r14, rcx; x346, x345<- x337 * 0xfffffffffffffffe
setc dl; spill CF x290 to reg (rdx)
clc;
mov [ rsp + 0x290 ], r13; spilling x346 to mem
mov r13, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, r13; loading flag
adcx r10, [ rsp + 0x208 ]
mov r9, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r9; 0xffffffffffffffff, swapping with x290, which is currently in rdx
mulx rbx, r13, rbx; x109, x108<- x106 * 0xffffffffffffffff
mov rdx, [ rsi + 0x28 ]; load m64 x5 to register64
mov [ rsp + 0x298 ], r14; spilling x345 to mem
mov r14, [ rsp + 0x218 ]; load m64 x54 to register64
mov byte [ rsp + 0x2a0 ], r9b; spilling byte x290 to mem
setc r9b; spill CF x204 to reg (r9)
mov [ rsp + 0x2a8 ], rbx; spilling x109 to mem
movzx rbx, byte [ rsp + 0x230 ]; load byte memx66 to register64
clc;
mov byte [ rsp + 0x2b0 ], r8b; spilling byte x251 to mem
mov r8, -0x1 ; moving imm to reg
adcx rbx, r8; loading flag
adcx r14, [ rsp + 0x30 ]
mulx rbx, r8, [ rsi + 0x0 ]; x388, x387<- x5 * arg1[0]
mov [ rsp + 0x2b8 ], rbx; spilling x388 to mem
setc bl; spill CF x68 to reg (rbx)
clc;
mov byte [ rsp + 0x2c0 ], r9b; spilling byte x204 to mem
mov r9, -0x1 ; moving imm to reg
movzx rbp, bpl
adcx rbp, r9; loading flag
adcx r13, [ rsp + 0x1e0 ]
setc bpl; spill CF x129 to reg (rbp)
clc;
movzx r12, r12b
adcx r12, r9; loading flag
adcx r14, [ rsp + 0x148 ]
mov r12, [ rsp + 0x278 ]; load m64 x266 to register64
seto r9b; spill OF x215 to reg (r9)
mov byte [ rsp + 0x2c8 ], bl; spilling byte x68 to mem
movzx rbx, byte [ rsp + 0x288 ]; load byte memx277 to register64
mov byte [ rsp + 0x2d0 ], bpl; spilling byte x129 to mem
mov rbp, 0x0 ; moving imm to reg
dec rbp; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbx, rbp; loading flag
adox r12, [ rsp + 0x250 ]
setc bl; spill CF x103 to reg (rbx)
movzx rbp, byte [ rsp + 0x200 ]; load byte memx324 to register64
clc;
mov [ rsp + 0x2d8 ], r12; spilling x278 to mem
mov r12, -0x1 ; moving imm to reg
adcx rbp, r12; loading flag
adcx rax, [ rsp + 0x38 ]
setc bpl; spill CF x326 to reg (rbp)
movzx r12, byte [ rsp + 0x240 ]; load byte memx363 to register64
clc;
mov byte [ rsp + 0x2e0 ], bl; spilling byte x103 to mem
mov rbx, -0x1 ; moving imm to reg
adcx r12, rbx; loading flag
adcx rax, [ rsp + 0x268 ]
setc r12b; spill CF x365 to reg (r12)
movzx rbx, byte [ rsp + 0x238 ]; load byte memx140 to register64
clc;
mov byte [ rsp + 0x2e8 ], bpl; spilling byte x326 to mem
mov rbp, -0x1 ; moving imm to reg
adcx rbx, rbp; loading flag
adcx r14, r13
setc bl; spill CF x142 to reg (rbx)
clc;
adcx r8, rax
setc r13b; spill CF x401 to reg (r13)
movzx rax, byte [ rsp + 0x260 ]; load byte memx176 to register64
clc;
adcx rax, rbp; loading flag
adcx r14, [ rsp + 0xa0 ]
mov rax, 0x100000001 ; moving imm to reg
xchg rdx, r8; x400, swapping with x5, which is currently in rdx
mov byte [ rsp + 0x2f0 ], r13b; spilling byte x401 to mem
mulx rbp, r13, rax; _, x414<- x400 * 0x100000001
setc bpl; spill CF x178 to reg (rbp)
clc;
mov rax, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, rax; loading flag
adcx r14, r10
mov r9, rdx; preserving value of x400 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r10, rax, r8; x386, x385<- x5 * arg1[1]
mov rdx, 0xffffffff ; moving imm to reg
mov [ rsp + 0x2f8 ], r10; spilling x386 to mem
mov byte [ rsp + 0x300 ], bpl; spilling byte x178 to mem
mulx r10, rbp, r13; x427, x426<- x414 * 0xffffffff
mov rdx, 0xffffffff00000000 ; moving imm to reg
mov byte [ rsp + 0x308 ], bl; spilling byte x142 to mem
mov byte [ rsp + 0x310 ], r12b; spilling byte x365 to mem
mulx rbx, r12, r13; x425, x424<- x414 * 0xffffffff00000000
seto dl; spill OF x279 to reg (rdx)
mov [ rsp + 0x318 ], rbx; spilling x425 to mem
mov rbx, -0x2 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, r10
setc r10b; spill CF x217 to reg (r10)
movzx rbx, byte [ rsp + 0x2b0 ]; load byte memx251 to register64
clc;
mov [ rsp + 0x320 ], r12; spilling x428 to mem
mov r12, -0x1 ; moving imm to reg
adcx rbx, r12; loading flag
adcx r14, [ rsp + 0xc8 ]
mov rbx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbx; 0xffffffffffffffff, swapping with x279, which is currently in rdx
mulx r15, r12, r15; x186, x185<- x183 * 0xffffffffffffffff
seto dl; spill OF x429 to reg (rdx)
mov [ rsp + 0x328 ], r15; spilling x186 to mem
movzx r15, byte [ rsp + 0x2c0 ]; load byte memx204 to register64
mov byte [ rsp + 0x330 ], r10b; spilling byte x217 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, r10; loading flag
adox r12, [ rsp + 0x270 ]
movzx r15, byte [ rsp + 0x2d0 ]; x130, copying x129 here, cause x129 is needed in a reg for other than x130, namely all: , x130, size: 1
mov r10, [ rsp + 0x2a8 ]; load m64 x109 to register64
lea r15, [ r15 + r10 ]; r8/64 + m8
setc r10b; spill CF x253 to reg (r10)
clc;
adcx rax, [ rsp + 0x2b8 ]
mov byte [ rsp + 0x338 ], dl; spilling byte x429 to mem
setc dl; spill CF x390 to reg (rdx)
clc;
adcx rbp, r9
setc bpl; spill CF x440 to reg (rbp)
movzx r9, byte [ rsp + 0x2a0 ]; load byte memx290 to register64
clc;
mov byte [ rsp + 0x340 ], dl; spilling byte x390 to mem
mov rdx, -0x1 ; moving imm to reg
adcx r9, rdx; loading flag
adcx r14, [ rsp + 0x2d8 ]
mov r9, 0xffffffffffffffff ; moving imm to reg
mov rdx, r11; x260 to rdx
mov byte [ rsp + 0x348 ], r10b; spilling byte x253 to mem
mulx r11, r10, r9; x265, x264<- x260 * 0xffffffffffffffff
seto r9b; spill OF x206 to reg (r9)
mov [ rsp + 0x350 ], r11; spilling x265 to mem
movzx r11, byte [ rsp + 0x2e8 ]; load byte memx326 to register64
mov [ rsp + 0x358 ], r12; spilling x205 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r11, r12; loading flag
adox r14, [ rsp + 0x40 ]
setc r11b; spill CF x292 to reg (r11)
clc;
movzx rbx, bl
adcx rbx, r12; loading flag
adcx r10, [ rsp + 0x258 ]
mov rbx, [ rsp + 0x298 ]; load m64 x345 to register64
seto r12b; spill OF x328 to reg (r12)
mov byte [ rsp + 0x360 ], r9b; spilling byte x206 to mem
movzx r9, byte [ rsp + 0x280 ]; load byte memx352 to register64
mov [ rsp + 0x368 ], r10; spilling x280 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r9, r10; loading flag
adox rbx, [ rsp + 0x248 ]
mov r9, rdx; preserving value of x260 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov byte [ rsp + 0x370 ], r12b; spilling byte x328 to mem
mulx r10, r12, r8; x384, x383<- x5 * arg1[2]
seto dl; spill OF x354 to reg (rdx)
mov [ rsp + 0x378 ], r10; spilling x384 to mem
movzx r10, byte [ rsp + 0x310 ]; load byte memx365 to register64
mov [ rsp + 0x380 ], r12; spilling x383 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r10, r12; loading flag
adox r14, rbx
movzx r10, byte [ rsp + 0x2c8 ]; load byte memx68 to register64
setc bl; spill CF x281 to reg (rbx)
movzx r12, byte [ rsp + 0x2e0 ]; load byte memx103 to register64
clc;
mov byte [ rsp + 0x388 ], dl; spilling byte x354 to mem
mov rdx, -0x1 ; moving imm to reg
adcx r12, rdx; loading flag
adcx r10, [ rsp + 0x150 ]
setc r12b; spill CF x105 to reg (r12)
movzx rdx, byte [ rsp + 0x308 ]; load byte memx142 to register64
clc;
mov byte [ rsp + 0x390 ], bl; spilling byte x281 to mem
mov rbx, -0x1 ; moving imm to reg
adcx rdx, rbx; loading flag
adcx r10, r15
setc dl; spill CF x144 to reg (rdx)
movzx r15, byte [ rsp + 0x2f0 ]; load byte memx401 to register64
clc;
adcx r15, rbx; loading flag
adcx r14, rax
setc r15b; spill CF x403 to reg (r15)
clc;
movzx rbp, bpl
adcx rbp, rbx; loading flag
adcx r14, [ rsp + 0x320 ]
setc al; spill CF x442 to reg (rax)
movzx rbp, byte [ rsp + 0x300 ]; load byte memx178 to register64
clc;
adcx rbp, rbx; loading flag
adcx r10, [ rsp + 0x98 ]
seto bpl; spill OF x367 to reg (rbp)
movzx rbx, byte [ rsp + 0x330 ]; load byte memx217 to register64
mov byte [ rsp + 0x398 ], al; spilling byte x442 to mem
mov rax, 0x0 ; moving imm to reg
dec rax; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbx, rax; loading flag
adox r10, [ rsp + 0x358 ]
setc bl; spill CF x180 to reg (rbx)
movzx rax, byte [ rsp + 0x348 ]; load byte memx253 to register64
clc;
mov byte [ rsp + 0x3a0 ], r15b; spilling byte x403 to mem
mov r15, -0x1 ; moving imm to reg
adcx rax, r15; loading flag
adcx r10, [ rsp + 0x100 ]
setc al; spill CF x255 to reg (rax)
seto r15b; spill OF x219 to reg (r15)
mov byte [ rsp + 0x3a8 ], bpl; spilling byte x367 to mem
mov rbp, r14; x454, copying x441 here, cause x441 is needed in a reg for other than x454, namely all: , x468, x454--x455, size: 2
mov byte [ rsp + 0x3b0 ], bl; spilling byte x180 to mem
mov rbx, 0xffffffff ; moving imm to reg
sub rbp, rbx
mov rbx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbx; 0xffffffffffffffff, swapping with x144, which is currently in rdx
mov [ rsp + 0x3b8 ], rbp; spilling x454 to mem
mulx r9, rbp, r9; x263, x262<- x260 * 0xffffffffffffffff
mov byte [ rsp + 0x3c0 ], al; spilling byte x255 to mem
mov byte [ rsp + 0x3c8 ], r15b; spilling byte x219 to mem
mulx rax, r15, rcx; x344, x343<- x337 * 0xffffffffffffffff
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, rdx; loading flag
adox r10, [ rsp + 0x368 ]
setc r11b; spill CF x455 to reg (r11)
movzx rdx, byte [ rsp + 0x370 ]; load byte memx328 to register64
clc;
mov [ rsp + 0x3d0 ], rax; spilling x344 to mem
mov rax, -0x1 ; moving imm to reg
adcx rdx, rax; loading flag
adcx r10, [ rsp + 0x48 ]
seto dl; spill OF x294 to reg (rdx)
movzx rax, byte [ rsp + 0x388 ]; load byte memx354 to register64
mov byte [ rsp + 0x3d8 ], r11b; spilling byte x455 to mem
mov r11, 0x0 ; moving imm to reg
dec r11; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rax, r11; loading flag
adox r15, [ rsp + 0x290 ]
mov rax, 0xfffffffffffffffe ; moving imm to reg
xchg rdx, rax; 0xfffffffffffffffe, swapping with x294, which is currently in rdx
mov byte [ rsp + 0x3e0 ], al; spilling byte x294 to mem
mulx r11, rax, r13; x423, x422<- x414 * 0xfffffffffffffffe
mov rdx, [ rsp + 0x380 ]; load m64 x383 to register64
mov [ rsp + 0x3e8 ], r11; spilling x423 to mem
seto r11b; spill OF x356 to reg (r11)
mov [ rsp + 0x3f0 ], r15; spilling x355 to mem
movzx r15, byte [ rsp + 0x340 ]; load byte memx390 to register64
mov [ rsp + 0x3f8 ], r10; spilling x329 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, r10; loading flag
adox rdx, [ rsp + 0x2f8 ]
mov r15, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r15; 0xffffffffffffffff, swapping with x391, which is currently in rdx
mov byte [ rsp + 0x400 ], r11b; spilling byte x356 to mem
mulx r10, r11, rcx; x342, x341<- x337 * 0xffffffffffffffff
setc dl; spill CF x330 to reg (rdx)
mov [ rsp + 0x408 ], r10; spilling x342 to mem
movzx r10, byte [ rsp + 0x390 ]; load byte memx281 to register64
clc;
mov [ rsp + 0x410 ], r11; spilling x341 to mem
mov r11, -0x1 ; moving imm to reg
adcx r10, r11; loading flag
adcx rbp, [ rsp + 0x350 ]
movzx r10, bl; x145, copying x144 here, cause x144 is needed in a reg for other than x145, namely all: , x145, size: 1
movzx r12, r12b
lea r10, [ r10 + r12 ]
mov r12, 0x0 ; moving imm to reg
adcx r9, r12
movzx rbx, byte [ rsp + 0x360 ]; x207, copying x206 here, cause x206 is needed in a reg for other than x207, namely all: , x207, size: 1
mov r12, [ rsp + 0x328 ]; load m64 x186 to register64
lea rbx, [ rbx + r12 ]; r8/64 + m8
movzx r12, byte [ rsp + 0x3b0 ]; load byte memx180 to register64
clc;
adcx r12, r11; loading flag
adcx r10, [ rsp + 0xf0 ]
setc r12b; spill CF x182 to reg (r12)
movzx r11, byte [ rsp + 0x338 ]; load byte memx429 to register64
clc;
mov [ rsp + 0x418 ], r9; spilling x284 to mem
mov r9, -0x1 ; moving imm to reg
adcx r11, r9; loading flag
adcx rax, [ rsp + 0x318 ]
seto r11b; spill OF x392 to reg (r11)
movzx r9, byte [ rsp + 0x3c8 ]; load byte memx219 to register64
mov byte [ rsp + 0x420 ], dl; spilling byte x330 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r9, rdx; loading flag
adox r10, rbx
setc r9b; spill CF x431 to reg (r9)
movzx rbx, byte [ rsp + 0x3c0 ]; load byte memx255 to register64
clc;
adcx rbx, rdx; loading flag
adcx r10, [ rsp + 0x128 ]
mov rbx, [ rsp + 0x3f0 ]; load m64 x355 to register64
setc dl; spill CF x257 to reg (rdx)
mov byte [ rsp + 0x428 ], r9b; spilling byte x431 to mem
movzx r9, byte [ rsp + 0x3a8 ]; load byte memx367 to register64
clc;
mov byte [ rsp + 0x430 ], r11b; spilling byte x392 to mem
mov r11, -0x1 ; moving imm to reg
adcx r9, r11; loading flag
adcx rbx, [ rsp + 0x3f8 ]
setc r9b; spill CF x369 to reg (r9)
movzx r11, byte [ rsp + 0x3a0 ]; load byte memx403 to register64
clc;
mov byte [ rsp + 0x438 ], dl; spilling byte x257 to mem
mov rdx, -0x1 ; moving imm to reg
adcx r11, rdx; loading flag
adcx rbx, r15
mov rdx, r8; x5 to rdx
mulx r8, r11, [ rsi + 0x18 ]; x382, x381<- x5 * arg1[3]
setc r15b; spill CF x405 to reg (r15)
mov [ rsp + 0x440 ], r8; spilling x382 to mem
movzx r8, byte [ rsp + 0x398 ]; load byte memx442 to register64
clc;
mov [ rsp + 0x448 ], r11; spilling x381 to mem
mov r11, -0x1 ; moving imm to reg
adcx r8, r11; loading flag
adcx rbx, rax
setc r8b; spill CF x444 to reg (r8)
seto al; spill OF x221 to reg (rax)
movzx r11, byte [ rsp + 0x3d8 ]; x455, copying x455 here, cause x455 is needed in a reg for other than x455, namely all: , x456--x457, size: 1
add r11, -0x1
mov r11, rbx; x456, copying x443 here, cause x443 is needed in a reg for other than x456, namely all: , x456--x457, x469, size: 2
mov byte [ rsp + 0x450 ], r15b; spilling byte x405 to mem
mov r15, 0xffffffff00000000 ; moving imm to reg
sbb r11, r15
movzx r15, byte [ rsp + 0x3e0 ]; load byte memx294 to register64
mov [ rsp + 0x458 ], r11; spilling x456 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
adox r15, r11; loading flag
adox r10, rbp
movzx r15, al; x222, copying x221 here, cause x221 is needed in a reg for other than x222, namely all: , x222, size: 1
movzx r12, r12b
lea r15, [ r15 + r12 ]
seto bpl; spill OF x296 to reg (rbp)
movzx r12, byte [ rsp + 0x420 ]; load byte memx330 to register64
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rax, -0x1 ; moving imm to reg
adox r12, rax; loading flag
adox r10, [ rsp + 0x90 ]
mov r12, [ rsp + 0x410 ]; load m64 x341 to register64
setc r11b; spill CF x457 to reg (r11)
movzx rax, byte [ rsp + 0x400 ]; load byte memx356 to register64
clc;
mov byte [ rsp + 0x460 ], bpl; spilling byte x296 to mem
mov rbp, -0x1 ; moving imm to reg
adcx rax, rbp; loading flag
adcx r12, [ rsp + 0x3d0 ]
seto al; spill OF x332 to reg (rax)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, rbp; loading flag
adox r10, r12
mov r9, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r13; x414, swapping with x5, which is currently in rdx
mulx r12, rbp, r9; x421, x420<- x414 * 0xffffffffffffffff
mov r9, [ rsp + 0x378 ]; load m64 x384 to register64
mov byte [ rsp + 0x468 ], r11b; spilling byte x457 to mem
seto r11b; spill OF x371 to reg (r11)
mov [ rsp + 0x470 ], r12; spilling x421 to mem
movzx r12, byte [ rsp + 0x430 ]; load byte memx392 to register64
mov byte [ rsp + 0x478 ], al; spilling byte x332 to mem
mov rax, -0x1 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rax, -0x1 ; moving imm to reg
adox r12, rax; loading flag
adox r9, [ rsp + 0x448 ]
mov r12, rdx; preserving value of x414 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov byte [ rsp + 0x480 ], r11b; spilling byte x371 to mem
mulx rax, r11, r13; x380, x379<- x5 * arg1[4]
setc dl; spill CF x358 to reg (rdx)
mov [ rsp + 0x488 ], rax; spilling x380 to mem
movzx rax, byte [ rsp + 0x428 ]; load byte memx431 to register64
clc;
mov [ rsp + 0x490 ], r11; spilling x379 to mem
mov r11, -0x1 ; moving imm to reg
adcx rax, r11; loading flag
adcx rbp, [ rsp + 0x3e8 ]
mov rax, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rax; 0xffffffffffffffff, swapping with x358, which is currently in rdx
mulx rcx, r11, rcx; x340, x339<- x337 * 0xffffffffffffffff
seto dl; spill OF x394 to reg (rdx)
mov [ rsp + 0x498 ], rcx; spilling x340 to mem
movzx rcx, byte [ rsp + 0x450 ]; load byte memx405 to register64
mov [ rsp + 0x4a0 ], r15; spilling x222 to mem
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r15, -0x1 ; moving imm to reg
adox rcx, r15; loading flag
adox r10, r9
mov rcx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rcx; 0xffffffffffffffff, swapping with x394, which is currently in rdx
mulx r9, r15, r12; x419, x418<- x414 * 0xffffffffffffffff
seto dl; spill OF x407 to reg (rdx)
mov [ rsp + 0x4a8 ], r9; spilling x419 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r8, r8b
adox r8, r9; loading flag
adox r10, rbp
setc r8b; spill CF x433 to reg (r8)
clc;
movzx rax, al
adcx rax, r9; loading flag
adcx r11, [ rsp + 0x408 ]
mov rax, [ rsp + 0x4a0 ]; load m64 x222 to register64
setc bpl; spill CF x360 to reg (rbp)
movzx r9, byte [ rsp + 0x438 ]; load byte memx257 to register64
clc;
mov [ rsp + 0x4b0 ], r10; spilling x445 to mem
mov r10, -0x1 ; moving imm to reg
adcx r9, r10; loading flag
adcx rax, [ rsp + 0x120 ]
mov r9, [ rsp + 0x490 ]; load m64 x379 to register64
seto r10b; spill OF x446 to reg (r10)
mov byte [ rsp + 0x4b8 ], dl; spilling byte x407 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rcx, cl
adox rcx, rdx; loading flag
adox r9, [ rsp + 0x440 ]
setc cl; spill CF x259 to reg (rcx)
movzx rdx, byte [ rsp + 0x460 ]; load byte memx296 to register64
clc;
mov byte [ rsp + 0x4c0 ], r10b; spilling byte x446 to mem
mov r10, -0x1 ; moving imm to reg
adcx rdx, r10; loading flag
adcx rax, [ rsp + 0x418 ]
movzx rdx, bpl; x361, copying x360 here, cause x360 is needed in a reg for other than x361, namely all: , x361, size: 1
mov r10, [ rsp + 0x498 ]; load m64 x340 to register64
lea rdx, [ rdx + r10 ]; r8/64 + m8
mov r10, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r10; 0xffffffffffffffff, swapping with x361, which is currently in rdx
mulx r12, rbp, r12; x417, x416<- x414 * 0xffffffffffffffff
movzx rdx, cl; x299, copying x259 here, cause x259 is needed in a reg for other than x299, namely all: , x299, size: 1
mov [ rsp + 0x4c8 ], r12; spilling x417 to mem
mov r12, 0x0 ; moving imm to reg
adcx rdx, r12
movzx rcx, byte [ rsp + 0x478 ]; load byte memx332 to register64
clc;
mov r12, -0x1 ; moving imm to reg
adcx rcx, r12; loading flag
adcx rax, [ rsp + 0x88 ]
mov rcx, rdx; preserving value of x299 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx r13, r12, r13; x378, x377<- x5 * arg1[5]
mov rdx, [ rsp + 0xc0 ]; x335, copying x322 here, cause x322 is needed in a reg for other than x335, namely all: , x335--x336, size: 1
adcx rdx, rcx
setc cl; spill CF x336 to reg (rcx)
mov [ rsp + 0x4d0 ], r13; spilling x378 to mem
movzx r13, byte [ rsp + 0x480 ]; load byte memx371 to register64
clc;
mov [ rsp + 0x4d8 ], rbp; spilling x416 to mem
mov rbp, -0x1 ; moving imm to reg
adcx r13, rbp; loading flag
adcx rax, r11
mov r13, [ rsp + 0x488 ]; x397, copying x380 here, cause x380 is needed in a reg for other than x397, namely all: , x397--x398, size: 1
adox r13, r12
adcx r10, rdx
setc r11b; spill CF x375 to reg (r11)
clc;
movzx r8, r8b
adcx r8, rbp; loading flag
adcx r15, [ rsp + 0x470 ]
seto r8b; spill OF x398 to reg (r8)
movzx r12, byte [ rsp + 0x4b8 ]; load byte memx407 to register64
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
adox r12, rdx; loading flag
adox rax, r9
mov r12, [ rsp + 0x4d8 ]; load m64 x416 to register64
mov r9, [ rsp + 0x4a8 ]; x436, copying x419 here, cause x419 is needed in a reg for other than x436, namely all: , x436--x437, size: 1
adcx r9, r12
mov r12, [ rsp + 0x4c8 ]; x438, copying x417 here, cause x417 is needed in a reg for other than x438, namely all: , x438, size: 1
adcx r12, rbp
movzx rbp, byte [ rsp + 0x4c0 ]; load byte memx446 to register64
clc;
adcx rbp, rdx; loading flag
adcx rax, r15
adox r13, r10
movzx rbp, r11b; x376, copying x375 here, cause x375 is needed in a reg for other than x376, namely all: , x376, size: 1
movzx rcx, cl
lea rbp, [ rbp + rcx ]
movzx rcx, r8b; x399, copying x398 here, cause x398 is needed in a reg for other than x399, namely all: , x399, size: 1
mov r11, [ rsp + 0x4d0 ]; load m64 x378 to register64
lea rcx, [ rcx + r11 ]; r8/64 + m8
adcx r9, r13
setc r11b; spill CF x450 to reg (r11)
seto r8b; spill OF x411 to reg (r8)
movzx r10, byte [ rsp + 0x468 ]; x457, copying x457 here, cause x457 is needed in a reg for other than x457, namely all: , x458--x459, size: 1
add r10, -0x1
mov r10, [ rsp + 0x4b0 ]; x458, copying x445 here, cause x445 is needed in a reg for other than x458, namely all: , x470, x458--x459, size: 2
mov r15, 0xfffffffffffffffe ; moving imm to reg
sbb r10, r15
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, r13; loading flag
adox rbp, rcx
seto r8b; spill OF x413 to reg (r8)
mov rcx, rax; x460, copying x447 here, cause x447 is needed in a reg for other than x460, namely all: , x471, x460--x461, size: 2
mov rdx, 0xffffffffffffffff ; moving imm to reg
sbb rcx, rdx
mov r13, r9; x462, copying x449 here, cause x449 is needed in a reg for other than x462, namely all: , x462--x463, x472, size: 2
sbb r13, rdx
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r15, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, r15; loading flag
adox rbp, r12
movzx r12, r8b; x453, copying x413 here, cause x413 is needed in a reg for other than x453, namely all: , x453, size: 1
mov r11, 0x0 ; moving imm to reg
adox r12, r11
mov r8, rbp; x464, copying x451 here, cause x451 is needed in a reg for other than x464, namely all: , x464--x465, x473, size: 2
sbb r8, rdx
sbb r12, 0x00000000
cmovc r13, r9; if CF, x472<- x449 (nzVar)
cmovc rcx, rax; if CF, x471<- x447 (nzVar)
mov r12, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r12 + 0x18 ], rcx; out1[3] = x471
cmovc r10, [ rsp + 0x4b0 ]; if CF, x470<- x445 (nzVar)
cmovc r8, rbp; if CF, x473<- x451 (nzVar)
mov [ r12 + 0x28 ], r8; out1[5] = x473
mov [ r12 + 0x20 ], r13; out1[4] = x472
mov rax, [ rsp + 0x3b8 ]; x468, copying x454 here, cause x454 is needed in a reg for other than x468, namely all: , x468, size: 1
cmovc rax, r14; if CF, x468<- x441 (nzVar)
mov [ r12 + 0x0 ], rax; out1[0] = x468
mov [ r12 + 0x10 ], r10; out1[2] = x470
mov r14, [ rsp + 0x458 ]; x469, copying x456 here, cause x456 is needed in a reg for other than x469, namely all: , x469, size: 1
cmovc r14, rbx; if CF, x469<- x443 (nzVar)
mov [ r12 + 0x8 ], r14; out1[1] = x469
mov rbx, [ rsp + 0x4e0 ]; restoring from stack
mov rbp, [ rsp + 0x4e8 ]; restoring from stack
mov r12, [ rsp + 0x4f0 ]; restoring from stack
mov r13, [ rsp + 0x4f8 ]; restoring from stack
mov r14, [ rsp + 0x500 ]; restoring from stack
mov r15, [ rsp + 0x508 ]; restoring from stack
add rsp, 0x510 
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; clocked at 2200 MHz
; first cyclecount 226.67, best 206.10169491525423, lastGood 211.6206896551724
; seed 2584814796855012 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3817564 ms / 60000 runs=> 63.62606666666667ms/run
; Time spent for assembling and measureing (initial batch_size=59, initial num_batches=101): 132929 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.03482037236310904
; number reverted permutation/ tried permutation: 18169 / 30026 =60.511%
; number reverted decision/ tried decision: 16696 / 29975 =55.700%