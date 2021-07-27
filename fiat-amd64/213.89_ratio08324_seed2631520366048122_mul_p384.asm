SECTION .text
	GLOBAL mul_p384
mul_p384:
sub rsp, 0x550 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x520 ], rbx; saving to stack
mov [ rsp + 0x528 ], rbp; saving to stack
mov [ rsp + 0x530 ], r12; saving to stack
mov [ rsp + 0x538 ], r13; saving to stack
mov [ rsp + 0x540 ], r14; saving to stack
mov [ rsp + 0x548 ], r15; saving to stack
mov rax, [ rsi + 0x20 ]; load m64 x4 to register64
xchg rdx, rax; x4, swapping with arg2, which is currently in rdx
mulx r10, r11, [ rax + 0x8 ]; x309, x308<- x4 * arg2[1]
mulx rbx, rbp, [ rax + 0x0 ]; x311, x310<- x4 * arg2[0]
mov r12, [ rsi + 0x10 ]; load m64 x2 to register64
mulx r13, r14, [ rax + 0x10 ]; x307, x306<- x4 * arg2[2]
mulx r15, rcx, [ rax + 0x28 ]; x301, x300<- x4 * arg2[5]
mov r8, [ rsi + 0x8 ]; load m64 x1 to register64
test al, al
adox r11, rbx
mulx r9, rbx, [ rax + 0x18 ]; x305, x304<- x4 * arg2[3]
xchg rdx, r12; x2, swapping with x4, which is currently in rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov [ rsp + 0x8 ], r11; spilling x312 to mem
mulx rdi, r11, [ rax + 0x18 ]; x151, x150<- x2 * arg2[3]
adox r14, r10
mov [ rsp + 0x10 ], r14; spilling x314 to mem
mulx r10, r14, [ rax + 0x8 ]; x155, x154<- x2 * arg2[1]
mov [ rsp + 0x18 ], rbp; spilling x310 to mem
mov [ rsp + 0x20 ], r8; spilling x1 to mem
mulx rbp, r8, [ rax + 0x20 ]; x149, x148<- x2 * arg2[4]
mov [ rsp + 0x28 ], rbp; spilling x149 to mem
mov [ rsp + 0x30 ], r8; spilling x148 to mem
mulx rbp, r8, [ rax + 0x10 ]; x153, x152<- x2 * arg2[2]
adox rbx, r13
xchg rdx, r12; x4, swapping with x2, which is currently in rdx
mulx rdx, r13, [ rax + 0x20 ]; x303, x302<- x4 * arg2[4]
adox r13, r9
adox rcx, rdx
mov r9, 0x0 ; moving imm to reg
adox r15, r9
mov rdx, [ rsi + 0x0 ]; load m64 x6 to register64
xchg rdx, r12; x2, swapping with x6, which is currently in rdx
mov [ rsp + 0x38 ], r15; spilling x322 to mem
mulx r9, r15, [ rax + 0x0 ]; x157, x156<- x2 * arg2[0]
adcx r14, r9
adcx r8, r10
adcx r11, rbp
mulx rdx, r10, [ rax + 0x28 ]; x147, x146<- x2 * arg2[5]
mov rbp, [ rsp + 0x30 ]; x164, copying x148 here, cause x148 is needed in a reg for other than x164, namely all: , x164--x165, size: 1
adcx rbp, rdi
mov rdi, rdx; preserving value of x147 into a new reg
mov rdx, [ rax + 0x0 ]; saving arg2[0] in rdx.
mov [ rsp + 0x40 ], rcx; spilling x320 to mem
mulx r9, rcx, r12; x18, x17<- x6 * arg2[0]
mov [ rsp + 0x48 ], r13; spilling x318 to mem
mov r13, 0x100000001 ; moving imm to reg
mov rdx, r13; 0x100000001 to rdx
mov [ rsp + 0x50 ], rbx; spilling x316 to mem
mulx r13, rbx, rcx; _, x30<- x17 * 0x100000001
mov r13, 0xffffffff ; moving imm to reg
xchg rdx, rbx; x30, swapping with 0x100000001, which is currently in rdx
mov [ rsp + 0x58 ], rbp; spilling x164 to mem
mulx rbx, rbp, r13; x43, x42<- x30 * 0xffffffff
mov r13, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x60 ], r11; spilling x162 to mem
mov [ rsp + 0x68 ], r8; spilling x160 to mem
mulx r11, r8, r13; x41, x40<- x30 * 0xffffffff00000000
mov r13, [ rsp + 0x28 ]; x166, copying x149 here, cause x149 is needed in a reg for other than x166, namely all: , x166--x167, size: 1
adcx r13, r10
xchg rdx, r12; x6, swapping with x30, which is currently in rdx
mov [ rsp + 0x70 ], r13; spilling x166 to mem
mulx r10, r13, [ rax + 0x8 ]; x16, x15<- x6 * arg2[1]
mov [ rsp + 0x78 ], r14; spilling x158 to mem
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, rcx
mov rbp, 0x0 ; moving imm to reg
adcx rdi, rbp
clc;
adcx r8, rbx
mov rcx, rdx; preserving value of x6 into a new reg
mov rdx, [ rsp + 0x20 ]; saving x1 in rdx.
mulx rbx, rbp, [ rax + 0x0 ]; x80, x79<- x1 * arg2[0]
setc r14b; spill CF x45 to reg (r14)
clc;
adcx r13, r9
adox r8, r13
setc r9b; spill CF x20 to reg (r9)
clc;
adcx rbp, r8
mov r13, 0x100000001 ; moving imm to reg
xchg rdx, rbp; x92, swapping with x1, which is currently in rdx
mov [ rsp + 0x80 ], rdi; spilling x168 to mem
mulx r8, rdi, r13; _, x106<- x92 * 0x100000001
mov r8, 0xffffffff00000000 ; moving imm to reg
xchg rdx, rdi; x106, swapping with x92, which is currently in rdx
mov [ rsp + 0x88 ], r15; spilling x156 to mem
mulx r13, r15, r8; x117, x116<- x106 * 0xffffffff00000000
xchg rdx, rbp; x1, swapping with x106, which is currently in rdx
mov [ rsp + 0x90 ], rbx; spilling x80 to mem
mulx r8, rbx, [ rax + 0x8 ]; x78, x77<- x1 * arg2[1]
mov [ rsp + 0x98 ], r8; spilling x78 to mem
mov r8, 0xffffffff ; moving imm to reg
xchg rdx, r8; 0xffffffff, swapping with x1, which is currently in rdx
mov [ rsp + 0xa0 ], rbx; spilling x77 to mem
mov [ rsp + 0xa8 ], r10; spilling x16 to mem
mulx rbx, r10, rbp; x119, x118<- x106 * 0xffffffff
setc dl; spill CF x93 to reg (rdx)
clc;
adcx r10, rdi
setc r10b; spill CF x132 to reg (r10)
clc;
adcx r15, rbx
mov rdi, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rdi; 0xffffffffffffffff, swapping with x93, which is currently in rdx
mov [ rsp + 0xb0 ], r15; spilling x120 to mem
mulx rbx, r15, rbp; x111, x110<- x106 * 0xffffffffffffffff
mov rdx, 0xfffffffffffffffe ; moving imm to reg
mov byte [ rsp + 0xb8 ], r10b; spilling byte x132 to mem
mov byte [ rsp + 0xc0 ], dil; spilling byte x93 to mem
mulx r10, rdi, rbp; x115, x114<- x106 * 0xfffffffffffffffe
mov byte [ rsp + 0xc8 ], r9b; spilling byte x20 to mem
mov [ rsp + 0xd0 ], rbx; spilling x111 to mem
mulx r9, rbx, r12; x39, x38<- x30 * 0xfffffffffffffffe
adcx rdi, r13
mov r13, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r12; x30, swapping with 0xfffffffffffffffe, which is currently in rdx
mov [ rsp + 0xd8 ], rdi; spilling x122 to mem
mulx r12, rdi, r13; x37, x36<- x30 * 0xffffffffffffffff
seto r13b; spill OF x58 to reg (r13)
mov [ rsp + 0xe0 ], r12; spilling x37 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, r12; loading flag
adox r11, rbx
adox rdi, r9
mov r14, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r14; 0xffffffffffffffff, swapping with x30, which is currently in rdx
mulx r9, rbx, rbp; x113, x112<- x106 * 0xffffffffffffffff
mulx rbp, r12, rbp; x109, x108<- x106 * 0xffffffffffffffff
adcx rbx, r10
adcx r15, r9
xchg rdx, rcx; x6, swapping with 0xffffffffffffffff, which is currently in rdx
mulx r10, r9, [ rax + 0x18 ]; x12, x11<- x6 * arg2[3]
mov [ rsp + 0xe8 ], r15; spilling x126 to mem
mulx rcx, r15, [ rax + 0x10 ]; x14, x13<- x6 * arg2[2]
mov [ rsp + 0xf0 ], rbx; spilling x124 to mem
mov rbx, [ rsp + 0xd0 ]; x128, copying x111 here, cause x111 is needed in a reg for other than x128, namely all: , x128--x129, size: 1
adcx rbx, r12
setc r12b; spill CF x129 to reg (r12)
mov [ rsp + 0xf8 ], rbx; spilling x128 to mem
movzx rbx, byte [ rsp + 0xc8 ]; load byte memx20 to register64
clc;
mov [ rsp + 0x100 ], r10; spilling x12 to mem
mov r10, -0x1 ; moving imm to reg
adcx rbx, r10; loading flag
adcx r15, [ rsp + 0xa8 ]
mov rbx, [ rsp + 0xa0 ]; load m64 x77 to register64
seto r10b; spill OF x49 to reg (r10)
mov [ rsp + 0x108 ], rsi; spilling arg1 to mem
mov rsi, -0x2 ; moving imm to reg
inc rsi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, [ rsp + 0x90 ]
mov rsi, rdx; preserving value of x6 into a new reg
mov rdx, [ rax + 0x10 ]; saving arg2[2] in rdx.
mov byte [ rsp + 0x110 ], r10b; spilling byte x49 to mem
mov [ rsp + 0x118 ], rbp; spilling x109 to mem
mulx r10, rbp, r8; x76, x75<- x1 * arg2[2]
mov [ rsp + 0x120 ], r10; spilling x76 to mem
seto r10b; spill OF x82 to reg (r10)
mov byte [ rsp + 0x128 ], r12b; spilling byte x129 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r13, r13b
adox r13, r12; loading flag
adox r15, r11
setc r13b; spill CF x22 to reg (r13)
clc;
movzx r10, r10b
adcx r10, r12; loading flag
adcx rbp, [ rsp + 0x98 ]
setc r11b; spill CF x84 to reg (r11)
movzx r10, byte [ rsp + 0xc0 ]; load byte memx93 to register64
clc;
adcx r10, r12; loading flag
adcx r15, rbx
setc r10b; spill CF x95 to reg (r10)
movzx rbx, byte [ rsp + 0xb8 ]; load byte memx132 to register64
clc;
adcx rbx, r12; loading flag
adcx r15, [ rsp + 0xb0 ]
setc bl; spill CF x134 to reg (rbx)
clc;
movzx r13, r13b
adcx r13, r12; loading flag
adcx rcx, r9
adox rdi, rcx
movzx r9, byte [ rsp + 0x128 ]; x130, copying x129 here, cause x129 is needed in a reg for other than x130, namely all: , x130, size: 1
mov r13, [ rsp + 0x118 ]; load m64 x109 to register64
lea r9, [ r9 + r13 ]; r8/64 + m8
mov r13, [ rsp + 0x108 ]; load m64 arg1 to register64
mov rcx, [ r13 + 0x18 ]; load m64 x3 to register64
setc r12b; spill CF x24 to reg (r12)
clc;
adcx r15, [ rsp + 0x88 ]
mov [ rsp + 0x130 ], r9; spilling x130 to mem
setc r9b; spill CF x170 to reg (r9)
clc;
mov byte [ rsp + 0x138 ], r11b; spilling byte x84 to mem
mov r11, -0x1 ; moving imm to reg
movzx r10, r10b
adcx r10, r11; loading flag
adcx rdi, rbp
mov rbp, 0x100000001 ; moving imm to reg
mov rdx, rbp; 0x100000001 to rdx
mulx rbp, r10, r15; _, x183<- x169 * 0x100000001
mov rbp, 0xffffffff ; moving imm to reg
xchg rdx, r10; x183, swapping with 0x100000001, which is currently in rdx
mulx r11, r10, rbp; x196, x195<- x183 * 0xffffffff
seto bpl; spill OF x62 to reg (rbp)
mov byte [ rsp + 0x140 ], r12b; spilling byte x24 to mem
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r10, r15
mov r10, 0xffffffff00000000 ; moving imm to reg
mulx r15, r12, r10; x194, x193<- x183 * 0xffffffff00000000
setc r10b; spill CF x97 to reg (r10)
clc;
adcx r12, r11
setc r11b; spill CF x198 to reg (r11)
clc;
mov byte [ rsp + 0x148 ], r10b; spilling byte x97 to mem
mov r10, -0x1 ; moving imm to reg
movzx rbx, bl
adcx rbx, r10; loading flag
adcx rdi, [ rsp + 0xd8 ]
mov rbx, rdx; preserving value of x183 into a new reg
mov rdx, [ rax + 0x20 ]; saving arg2[4] in rdx.
mov byte [ rsp + 0x150 ], bpl; spilling byte x62 to mem
mulx r10, rbp, rsi; x10, x9<- x6 * arg2[4]
mov [ rsp + 0x158 ], r10; spilling x10 to mem
setc r10b; spill CF x136 to reg (r10)
clc;
mov [ rsp + 0x160 ], r15; spilling x194 to mem
mov r15, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, r15; loading flag
adcx rdi, [ rsp + 0x78 ]
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx r9, r15, rcx; x234, x233<- x3 * arg2[0]
adox r12, rdi
seto dil; spill OF x211 to reg (rdi)
mov [ rsp + 0x168 ], r9; spilling x234 to mem
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, r12
mov r12, 0xfffffffffffffffe ; moving imm to reg
mov rdx, r12; 0xfffffffffffffffe to rdx
mulx r12, r9, rbx; x192, x191<- x183 * 0xfffffffffffffffe
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x170 ], r12; spilling x192 to mem
mov byte [ rsp + 0x178 ], dil; spilling byte x211 to mem
mulx r12, rdi, r14; x35, x34<- x30 * 0xffffffffffffffff
setc dl; spill CF x172 to reg (rdx)
mov [ rsp + 0x180 ], r12; spilling x35 to mem
movzx r12, byte [ rsp + 0x140 ]; load byte memx24 to register64
clc;
mov byte [ rsp + 0x188 ], r10b; spilling byte x136 to mem
mov r10, -0x1 ; moving imm to reg
adcx r12, r10; loading flag
adcx rbp, [ rsp + 0x100 ]
mov r12, 0x100000001 ; moving imm to reg
xchg rdx, r12; 0x100000001, swapping with x172, which is currently in rdx
mov byte [ rsp + 0x190 ], r12b; spilling byte x172 to mem
mulx r10, r12, r15; _, x260<- x246 * 0x100000001
mov r10, 0xffffffff ; moving imm to reg
xchg rdx, r10; 0xffffffff, swapping with 0x100000001, which is currently in rdx
mov [ rsp + 0x198 ], rbp; spilling x25 to mem
mulx r10, rbp, r12; x273, x272<- x260 * 0xffffffff
mov rdx, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x1a0 ], rbp; spilling x272 to mem
mov [ rsp + 0x1a8 ], r9; spilling x191 to mem
mulx rbp, r9, r12; x271, x270<- x260 * 0xffffffff00000000
seto dl; spill OF x247 to reg (rdx)
mov [ rsp + 0x1b0 ], rbp; spilling x271 to mem
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r9, r10
setc r10b; spill CF x26 to reg (r10)
movzx rbp, byte [ rsp + 0x110 ]; load byte memx49 to register64
clc;
mov [ rsp + 0x1b8 ], r9; spilling x274 to mem
mov r9, -0x1 ; moving imm to reg
adcx rbp, r9; loading flag
adcx rdi, [ rsp + 0xe0 ]
mov rbp, [ rsp + 0x160 ]; load m64 x194 to register64
seto r9b; spill OF x275 to reg (r9)
mov byte [ rsp + 0x1c0 ], r10b; spilling byte x26 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r11, r11b
adox r11, r10; loading flag
adox rbp, [ rsp + 0x1a8 ]
xchg rdx, r8; x1, swapping with x247, which is currently in rdx
mulx r11, r10, [ rax + 0x18 ]; x74, x73<- x1 * arg2[3]
mov byte [ rsp + 0x1c8 ], r9b; spilling byte x275 to mem
setc r9b; spill CF x51 to reg (r9)
clc;
adcx r15, [ rsp + 0x1a0 ]
setc r15b; spill CF x286 to reg (r15)
mov byte [ rsp + 0x1d0 ], r9b; spilling byte x51 to mem
movzx r9, byte [ rsp + 0x138 ]; load byte memx84 to register64
clc;
mov [ rsp + 0x1d8 ], r11; spilling x74 to mem
mov r11, -0x1 ; moving imm to reg
adcx r9, r11; loading flag
adcx r10, [ rsp + 0x120 ]
setc r9b; spill CF x86 to reg (r9)
movzx r11, byte [ rsp + 0x150 ]; load byte memx62 to register64
clc;
mov byte [ rsp + 0x1e0 ], r15b; spilling byte x286 to mem
mov r15, -0x1 ; moving imm to reg
adcx r11, r15; loading flag
adcx rdi, [ rsp + 0x198 ]
seto r11b; spill OF x200 to reg (r11)
movzx r15, byte [ rsp + 0x148 ]; load byte memx97 to register64
mov byte [ rsp + 0x1e8 ], r9b; spilling byte x86 to mem
mov r9, -0x1 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r9, -0x1 ; moving imm to reg
adox r15, r9; loading flag
adox rdi, r10
seto r15b; spill OF x99 to reg (r15)
movzx r10, byte [ rsp + 0x188 ]; load byte memx136 to register64
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
adox r10, r9; loading flag
adox rdi, [ rsp + 0xf0 ]
xchg rdx, rcx; x3, swapping with x1, which is currently in rdx
mulx r10, r9, [ rax + 0x8 ]; x232, x231<- x3 * arg2[1]
mov byte [ rsp + 0x1f0 ], r11b; spilling byte x200 to mem
seto r11b; spill OF x138 to reg (r11)
mov byte [ rsp + 0x1f8 ], r15b; spilling byte x99 to mem
movzx r15, byte [ rsp + 0x190 ]; load byte memx172 to register64
mov [ rsp + 0x200 ], r10; spilling x232 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, r10; loading flag
adox rdi, [ rsp + 0x68 ]
setc r15b; spill CF x64 to reg (r15)
clc;
adcx r9, [ rsp + 0x168 ]
mov byte [ rsp + 0x208 ], r11b; spilling byte x138 to mem
mulx r10, r11, [ rax + 0x10 ]; x230, x229<- x3 * arg2[2]
mov byte [ rsp + 0x210 ], r15b; spilling byte x64 to mem
seto r15b; spill OF x174 to reg (r15)
mov [ rsp + 0x218 ], r10; spilling x230 to mem
movzx r10, byte [ rsp + 0x178 ]; load byte memx211 to register64
mov [ rsp + 0x220 ], r11; spilling x229 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
adox r10, r11; loading flag
adox rdi, rbp
seto r10b; spill OF x213 to reg (r10)
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, rbp; loading flag
adox rdi, r9
seto r8b; spill OF x249 to reg (r8)
movzx r9, byte [ rsp + 0x1e0 ]; load byte memx286 to register64
dec r11; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
adox r9, r11; loading flag
adox rdi, [ rsp + 0x1b8 ]
setc bpl; spill CF x236 to reg (rbp)
clc;
adcx rdi, [ rsp + 0x18 ]
mov r9, rdx; preserving value of x3 into a new reg
mov rdx, [ rax + 0x28 ]; saving arg2[5] in rdx.
mulx rsi, r11, rsi; x8, x7<- x6 * arg2[5]
mov byte [ rsp + 0x228 ], r8b; spilling byte x249 to mem
mov r8, 0x100000001 ; moving imm to reg
mov rdx, r8; 0x100000001 to rdx
mov byte [ rsp + 0x230 ], r10b; spilling byte x213 to mem
mulx r8, r10, rdi; _, x337<- x323 * 0x100000001
mov r8, 0xffffffff ; moving imm to reg
xchg rdx, r10; x337, swapping with 0x100000001, which is currently in rdx
mov byte [ rsp + 0x238 ], r15b; spilling byte x174 to mem
mulx r10, r15, r8; x350, x349<- x337 * 0xffffffff
mov r8, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x240 ], r15; spilling x349 to mem
mov [ rsp + 0x248 ], rsi; spilling x8 to mem
mulx r15, rsi, r8; x348, x347<- x337 * 0xffffffff00000000
mov r8, 0xfffffffffffffffe ; moving imm to reg
mov byte [ rsp + 0x250 ], bpl; spilling byte x236 to mem
mov [ rsp + 0x258 ], r11; spilling x7 to mem
mulx rbp, r11, r8; x346, x345<- x337 * 0xfffffffffffffffe
mov r8, rdx; preserving value of x337 into a new reg
mov rdx, [ rax + 0x28 ]; saving arg2[5] in rdx.
mov [ rsp + 0x260 ], rbp; spilling x346 to mem
mov [ rsp + 0x268 ], r11; spilling x345 to mem
mulx rbp, r11, r9; x224, x223<- x3 * arg2[5]
mov [ rsp + 0x270 ], rbp; spilling x224 to mem
seto bpl; spill OF x288 to reg (rbp)
mov [ rsp + 0x278 ], r11; spilling x223 to mem
mov r11, -0x2 ; moving imm to reg
inc r11; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rsi, r10
mov r10, 0xffffffffffffffff ; moving imm to reg
mov rdx, r8; x337 to rdx
mulx r8, r11, r10; x344, x343<- x337 * 0xffffffffffffffff
mov r10, rdx; preserving value of x337 into a new reg
mov rdx, [ rax + 0x18 ]; saving arg2[3] in rdx.
mov [ rsp + 0x280 ], rsi; spilling x351 to mem
mov byte [ rsp + 0x288 ], bpl; spilling byte x288 to mem
mulx rsi, rbp, r9; x228, x227<- x3 * arg2[3]
mov [ rsp + 0x290 ], rsi; spilling x228 to mem
mov rsi, [ rsp + 0x268 ]; x353, copying x345 here, cause x345 is needed in a reg for other than x353, namely all: , x353--x354, size: 1
adox rsi, r15
mov r15, [ rsp + 0x260 ]; x355, copying x346 here, cause x346 is needed in a reg for other than x355, namely all: , x355--x356, size: 1
adox r15, r11
mov r11, 0xffffffffffffffff ; moving imm to reg
mov rdx, r11; 0xffffffffffffffff to rdx
mov [ rsp + 0x298 ], r15; spilling x355 to mem
mulx r11, r15, r10; x342, x341<- x337 * 0xffffffffffffffff
mov rdx, [ rsp + 0x158 ]; load m64 x10 to register64
mov [ rsp + 0x2a0 ], rsi; spilling x353 to mem
setc sil; spill CF x324 to reg (rsi)
mov [ rsp + 0x2a8 ], rbp; spilling x227 to mem
movzx rbp, byte [ rsp + 0x1c0 ]; load byte memx26 to register64
clc;
mov [ rsp + 0x2b0 ], r11; spilling x342 to mem
mov r11, -0x1 ; moving imm to reg
adcx rbp, r11; loading flag
adcx rdx, [ rsp + 0x258 ]
adox r15, r8
mov rbp, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbp; 0xffffffffffffffff, swapping with x27, which is currently in rdx
mulx r10, r8, r10; x340, x339<- x337 * 0xffffffffffffffff
mov r11, [ rsp + 0x2b0 ]; x359, copying x342 here, cause x342 is needed in a reg for other than x359, namely all: , x359--x360, size: 1
adox r11, r8
mov r8, [ rsp + 0x220 ]; load m64 x229 to register64
seto dl; spill OF x360 to reg (rdx)
mov [ rsp + 0x2b8 ], r11; spilling x359 to mem
movzx r11, byte [ rsp + 0x250 ]; load byte memx236 to register64
mov [ rsp + 0x2c0 ], r15; spilling x357 to mem
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r15, -0x1 ; moving imm to reg
adox r11, r15; loading flag
adox r8, [ rsp + 0x200 ]
mov r11b, dl; preserving value of x360 into a new reg
mov rdx, [ rax + 0x20 ]; saving arg2[4] in rdx.
mulx r9, r15, r9; x226, x225<- x3 * arg2[4]
mov byte [ rsp + 0x2c8 ], sil; spilling byte x324 to mem
mov rsi, 0xfffffffffffffffe ; moving imm to reg
mov rdx, r12; x260 to rdx
mov [ rsp + 0x2d0 ], r8; spilling x237 to mem
mulx r12, r8, rsi; x269, x268<- x260 * 0xfffffffffffffffe
mov rsi, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rsi; 0xffffffffffffffff, swapping with x260, which is currently in rdx
mov [ rsp + 0x2d8 ], r12; spilling x269 to mem
mulx r14, r12, r14; x33, x32<- x30 * 0xffffffffffffffff
mov rdx, [ rsp + 0x2a8 ]; load m64 x227 to register64
mov [ rsp + 0x2e0 ], r14; spilling x33 to mem
mov r14, [ rsp + 0x218 ]; x239, copying x230 here, cause x230 is needed in a reg for other than x239, namely all: , x239--x240, size: 1
adox r14, rdx
mov rdx, [ rsp + 0x290 ]; x241, copying x228 here, cause x228 is needed in a reg for other than x241, namely all: , x241--x242, size: 1
adox rdx, r15
xchg rdx, rcx; x1, swapping with x241, which is currently in rdx
mov [ rsp + 0x2e8 ], rcx; spilling x241 to mem
mulx r15, rcx, [ rax + 0x20 ]; x72, x71<- x1 * arg2[4]
mov [ rsp + 0x2f0 ], r14; spilling x239 to mem
movzx r14, r11b; x361, copying x360 here, cause x360 is needed in a reg for other than x361, namely all: , x361, size: 1
lea r14, [ r14 + r10 ]
mov r10, [ rsp + 0x278 ]; x243, copying x223 here, cause x223 is needed in a reg for other than x243, namely all: , x243--x244, size: 1
adox r10, r9
seto r11b; spill OF x244 to reg (r11)
movzx r9, byte [ rsp + 0x1e8 ]; load byte memx86 to register64
mov [ rsp + 0x2f8 ], r14; spilling x361 to mem
mov r14, -0x1 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r14, -0x1 ; moving imm to reg
adox r9, r14; loading flag
adox rcx, [ rsp + 0x1d8 ]
mov r9, [ r13 + 0x28 ]; load m64 x5 to register64
setc r14b; spill CF x28 to reg (r14)
mov [ rsp + 0x300 ], r10; spilling x243 to mem
movzx r10, byte [ rsp + 0x1d0 ]; load byte memx51 to register64
clc;
mov [ rsp + 0x308 ], r15; spilling x72 to mem
mov r15, -0x1 ; moving imm to reg
adcx r10, r15; loading flag
adcx r12, [ rsp + 0x180 ]
seto r10b; spill OF x88 to reg (r10)
movzx r15, byte [ rsp + 0x210 ]; load byte memx64 to register64
mov [ rsp + 0x310 ], r9; spilling x5 to mem
mov r9, -0x1 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r9, -0x1 ; moving imm to reg
adox r15, r9; loading flag
adox rbp, r12
setc r15b; spill CF x53 to reg (r15)
movzx r12, byte [ rsp + 0x1c8 ]; load byte memx275 to register64
clc;
adcx r12, r9; loading flag
adcx r8, [ rsp + 0x1b0 ]
movzx r12, r11b; x245, copying x244 here, cause x244 is needed in a reg for other than x245, namely all: , x245, size: 1
mov r9, [ rsp + 0x270 ]; load m64 x224 to register64
lea r12, [ r12 + r9 ]; r8/64 + m8
movzx r9, r14b; x29, copying x28 here, cause x28 is needed in a reg for other than x29, namely all: , x29, size: 1
mov r11, [ rsp + 0x248 ]; load m64 x8 to register64
lea r9, [ r9 + r11 ]; r8/64 + m8
mov r11, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r11; 0xffffffffffffffff, swapping with x1, which is currently in rdx
mov [ rsp + 0x318 ], r12; spilling x245 to mem
mulx r14, r12, rbx; x190, x189<- x183 * 0xffffffffffffffff
movzx rdx, r15b; x54, copying x53 here, cause x53 is needed in a reg for other than x54, namely all: , x54, size: 1
mov [ rsp + 0x320 ], r14; spilling x190 to mem
mov r14, [ rsp + 0x2e0 ]; load m64 x33 to register64
lea rdx, [ rdx + r14 ]; r8/64 + m8
setc r14b; spill CF x277 to reg (r14)
movzx r15, byte [ rsp + 0x1f8 ]; load byte memx99 to register64
clc;
mov byte [ rsp + 0x328 ], r10b; spilling byte x88 to mem
mov r10, -0x1 ; moving imm to reg
adcx r15, r10; loading flag
adcx rbp, rcx
setc r15b; spill CF x101 to reg (r15)
clc;
adcx rdi, [ rsp + 0x240 ]
seto cl; spill OF x66 to reg (rcx)
movzx r10, byte [ rsp + 0x208 ]; load byte memx138 to register64
mov byte [ rsp + 0x330 ], r14b; spilling byte x277 to mem
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r10, r14; loading flag
adox rbp, [ rsp + 0xe8 ]
seto r10b; spill OF x140 to reg (r10)
movzx r14, byte [ rsp + 0x238 ]; load byte memx174 to register64
mov byte [ rsp + 0x338 ], r15b; spilling byte x101 to mem
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r14, r15; loading flag
adox rbp, [ rsp + 0x60 ]
seto r14b; spill OF x176 to reg (r14)
movzx r15, byte [ rsp + 0x1f0 ]; load byte memx200 to register64
mov byte [ rsp + 0x340 ], r10b; spilling byte x140 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, r10; loading flag
adox r12, [ rsp + 0x170 ]
setc r15b; spill CF x363 to reg (r15)
movzx r10, byte [ rsp + 0x230 ]; load byte memx213 to register64
clc;
mov byte [ rsp + 0x348 ], r14b; spilling byte x176 to mem
mov r14, -0x1 ; moving imm to reg
adcx r10, r14; loading flag
adcx rbp, r12
setc r10b; spill CF x215 to reg (r10)
movzx r12, byte [ rsp + 0x228 ]; load byte memx249 to register64
clc;
adcx r12, r14; loading flag
adcx rbp, [ rsp + 0x2d0 ]
setc r12b; spill CF x251 to reg (r12)
movzx r14, byte [ rsp + 0x288 ]; load byte memx288 to register64
clc;
mov byte [ rsp + 0x350 ], r10b; spilling byte x215 to mem
mov r10, -0x1 ; moving imm to reg
adcx r14, r10; loading flag
adcx rbp, r8
mov r14, rdx; preserving value of x54 into a new reg
mov rdx, [ rsp + 0x310 ]; saving x5 in rdx.
mulx r8, r10, [ rax + 0x0 ]; x388, x387<- x5 * arg2[0]
xchg rdx, r11; x1, swapping with x5, which is currently in rdx
mov [ rsp + 0x358 ], r8; spilling x388 to mem
mulx rdx, r8, [ rax + 0x28 ]; x70, x69<- x1 * arg2[5]
mov byte [ rsp + 0x360 ], r12b; spilling byte x251 to mem
setc r12b; spill CF x290 to reg (r12)
mov [ rsp + 0x368 ], rdx; spilling x70 to mem
movzx rdx, byte [ rsp + 0x2c8 ]; load byte memx324 to register64
clc;
mov [ rsp + 0x370 ], r10; spilling x387 to mem
mov r10, -0x1 ; moving imm to reg
adcx rdx, r10; loading flag
adcx rbp, [ rsp + 0x8 ]
setc dl; spill CF x326 to reg (rdx)
clc;
movzx rcx, cl
adcx rcx, r10; loading flag
adcx r9, r14
mov rcx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rcx; 0xffffffffffffffff, swapping with x326, which is currently in rdx
mulx r14, r10, rbx; x188, x187<- x183 * 0xffffffffffffffff
mov [ rsp + 0x378 ], r14; spilling x188 to mem
mov byte [ rsp + 0x380 ], cl; spilling byte x326 to mem
mulx r14, rcx, rsi; x265, x264<- x260 * 0xffffffffffffffff
seto dl; spill OF x202 to reg (rdx)
mov [ rsp + 0x388 ], r14; spilling x265 to mem
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r15, r15b
adox r15, r14; loading flag
adox rbp, [ rsp + 0x280 ]
seto r15b; spill OF x365 to reg (r15)
movzx r14, byte [ rsp + 0x328 ]; load byte memx88 to register64
mov [ rsp + 0x390 ], rcx; spilling x264 to mem
mov rcx, -0x1 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rcx, -0x1 ; moving imm to reg
adox r14, rcx; loading flag
adox r8, [ rsp + 0x308 ]
setc r14b; spill CF x68 to reg (r14)
clc;
adcx rbp, [ rsp + 0x370 ]
mov rcx, 0x100000001 ; moving imm to reg
xchg rdx, rcx; 0x100000001, swapping with x202, which is currently in rdx
mov byte [ rsp + 0x398 ], r15b; spilling byte x365 to mem
mov byte [ rsp + 0x3a0 ], r12b; spilling byte x290 to mem
mulx r15, r12, rbp; _, x414<- x400 * 0x100000001
mov r15, 0xffffffff ; moving imm to reg
xchg rdx, r12; x414, swapping with 0x100000001, which is currently in rdx
mov byte [ rsp + 0x3a8 ], r14b; spilling byte x68 to mem
mulx r12, r14, r15; x427, x426<- x414 * 0xffffffff
setc r15b; spill CF x401 to reg (r15)
mov [ rsp + 0x3b0 ], r12; spilling x427 to mem
movzx r12, byte [ rsp + 0x338 ]; load byte memx101 to register64
clc;
mov [ rsp + 0x3b8 ], r14; spilling x426 to mem
mov r14, -0x1 ; moving imm to reg
adcx r12, r14; loading flag
adcx r9, r8
xchg rdx, r11; x5, swapping with x414, which is currently in rdx
mulx r12, r8, [ rax + 0x8 ]; x386, x385<- x5 * arg2[1]
mov r14, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r14; 0xffffffffffffffff, swapping with x5, which is currently in rdx
mov [ rsp + 0x3c0 ], r12; spilling x386 to mem
mov byte [ rsp + 0x3c8 ], r15b; spilling byte x401 to mem
mulx r12, r15, rsi; x267, x266<- x260 * 0xffffffffffffffff
setc dl; spill CF x103 to reg (rdx)
mov [ rsp + 0x3d0 ], r12; spilling x267 to mem
movzx r12, byte [ rsp + 0x340 ]; load byte memx140 to register64
clc;
mov [ rsp + 0x3d8 ], r8; spilling x385 to mem
mov r8, -0x1 ; moving imm to reg
adcx r12, r8; loading flag
adcx r9, [ rsp + 0xf8 ]
setc r12b; spill CF x142 to reg (r12)
clc;
movzx rcx, cl
adcx rcx, r8; loading flag
adcx r10, [ rsp + 0x320 ]
setc cl; spill CF x204 to reg (rcx)
movzx r8, byte [ rsp + 0x348 ]; load byte memx176 to register64
clc;
mov byte [ rsp + 0x3e0 ], r12b; spilling byte x142 to mem
mov r12, -0x1 ; moving imm to reg
adcx r8, r12; loading flag
adcx r9, [ rsp + 0x58 ]
mov r8, [ rsp + 0x368 ]; x91, copying x70 here, cause x70 is needed in a reg for other than x91, namely all: , x91, size: 1
mov r12, 0x0 ; moving imm to reg
adox r8, r12
movzx r12, byte [ rsp + 0x350 ]; load byte memx215 to register64
mov byte [ rsp + 0x3e8 ], cl; spilling byte x204 to mem
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r12, rcx; loading flag
adox r9, r10
setc r12b; spill CF x178 to reg (r12)
clc;
adcx rbp, [ rsp + 0x3b8 ]
setc bpl; spill CF x440 to reg (rbp)
movzx r10, byte [ rsp + 0x330 ]; load byte memx277 to register64
clc;
adcx r10, rcx; loading flag
adcx r15, [ rsp + 0x2d8 ]
setc r10b; spill CF x279 to reg (r10)
clc;
mov byte [ rsp + 0x3f0 ], bpl; spilling byte x440 to mem
movzx rbp, byte [ rsp + 0x3a8 ]; load byte memx68 to register64
movzx rdx, dl
adcx rdx, rcx; loading flag
adcx r8, rbp
mov rbp, 0xffffffffffffffff ; moving imm to reg
mov rdx, rbx; x183 to rdx
mulx rdx, rbx, rbp; x186, x185<- x183 * 0xffffffffffffffff
setc cl; spill CF x105 to reg (rcx)
movzx rbp, byte [ rsp + 0x360 ]; load byte memx251 to register64
clc;
mov byte [ rsp + 0x3f8 ], r10b; spilling byte x279 to mem
mov r10, -0x1 ; moving imm to reg
adcx rbp, r10; loading flag
adcx r9, [ rsp + 0x2f0 ]
mov rbp, 0xffffffff00000000 ; moving imm to reg
xchg rdx, r11; x414, swapping with x186, which is currently in rdx
mov byte [ rsp + 0x400 ], cl; spilling byte x105 to mem
mulx r10, rcx, rbp; x425, x424<- x414 * 0xffffffff00000000
setc bpl; spill CF x253 to reg (rbp)
clc;
adcx rcx, [ rsp + 0x3b0 ]
mov [ rsp + 0x408 ], r10; spilling x425 to mem
mov r10, [ rsp + 0x3d8 ]; load m64 x385 to register64
mov byte [ rsp + 0x410 ], bpl; spilling byte x253 to mem
seto bpl; spill OF x217 to reg (rbp)
mov [ rsp + 0x418 ], rcx; spilling x428 to mem
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r10, [ rsp + 0x358 ]
setc cl; spill CF x429 to reg (rcx)
mov [ rsp + 0x420 ], r10; spilling x389 to mem
movzx r10, byte [ rsp + 0x3a0 ]; load byte memx290 to register64
clc;
mov byte [ rsp + 0x428 ], bpl; spilling byte x217 to mem
mov rbp, -0x1 ; moving imm to reg
adcx r10, rbp; loading flag
adcx r9, r15
setc r10b; spill CF x292 to reg (r10)
movzx r15, byte [ rsp + 0x380 ]; load byte memx326 to register64
clc;
adcx r15, rbp; loading flag
adcx r9, [ rsp + 0x10 ]
mov r15, 0xfffffffffffffffe ; moving imm to reg
mov byte [ rsp + 0x430 ], cl; spilling byte x429 to mem
mulx rbp, rcx, r15; x423, x422<- x414 * 0xfffffffffffffffe
setc r15b; spill CF x328 to reg (r15)
mov [ rsp + 0x438 ], rbp; spilling x423 to mem
movzx rbp, byte [ rsp + 0x3e8 ]; load byte memx204 to register64
clc;
mov [ rsp + 0x440 ], rcx; spilling x422 to mem
mov rcx, -0x1 ; moving imm to reg
adcx rbp, rcx; loading flag
adcx rbx, [ rsp + 0x378 ]
mov rbp, 0x0 ; moving imm to reg
adcx r11, rbp
movzx rbp, byte [ rsp + 0x3e0 ]; load byte memx142 to register64
clc;
adcx rbp, rcx; loading flag
adcx r8, [ rsp + 0x130 ]
seto bpl; spill OF x390 to reg (rbp)
movzx rcx, byte [ rsp + 0x398 ]; load byte memx365 to register64
mov [ rsp + 0x448 ], r11; spilling x207 to mem
mov r11, 0x0 ; moving imm to reg
dec r11; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rcx, r11; loading flag
adox r9, [ rsp + 0x2a0 ]
setc cl; spill CF x144 to reg (rcx)
clc;
movzx r12, r12b
adcx r12, r11; loading flag
adcx r8, [ rsp + 0x70 ]
mov r12, [ rsp + 0x3d0 ]; load m64 x267 to register64
setc r11b; spill CF x180 to reg (r11)
mov byte [ rsp + 0x450 ], cl; spilling byte x144 to mem
movzx rcx, byte [ rsp + 0x3f8 ]; load byte memx279 to register64
clc;
mov byte [ rsp + 0x458 ], r15b; spilling byte x328 to mem
mov r15, -0x1 ; moving imm to reg
adcx rcx, r15; loading flag
adcx r12, [ rsp + 0x390 ]
seto cl; spill OF x367 to reg (rcx)
movzx r15, byte [ rsp + 0x428 ]; load byte memx217 to register64
mov byte [ rsp + 0x460 ], r11b; spilling byte x180 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
adox r15, r11; loading flag
adox r8, rbx
mov r15, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r15; 0xffffffffffffffff, swapping with x414, which is currently in rdx
mulx rsi, rbx, rsi; x263, x262<- x260 * 0xffffffffffffffff
setc r11b; spill CF x281 to reg (r11)
movzx rdx, byte [ rsp + 0x3c8 ]; load byte memx401 to register64
clc;
mov [ rsp + 0x468 ], rsi; spilling x263 to mem
mov rsi, -0x1 ; moving imm to reg
adcx rdx, rsi; loading flag
adcx r9, [ rsp + 0x420 ]
setc dl; spill CF x403 to reg (rdx)
clc;
movzx r11, r11b
adcx r11, rsi; loading flag
adcx rbx, [ rsp + 0x388 ]
setc r11b; spill CF x283 to reg (r11)
movzx rsi, byte [ rsp + 0x3f0 ]; load byte memx440 to register64
clc;
mov [ rsp + 0x470 ], rbx; spilling x282 to mem
mov rbx, -0x1 ; moving imm to reg
adcx rsi, rbx; loading flag
adcx r9, [ rsp + 0x418 ]
mov sil, dl; preserving value of x403 into a new reg
mov rdx, [ rax + 0x10 ]; saving arg2[2] in rdx.
mov [ rsp + 0x478 ], r9; spilling x441 to mem
mulx rbx, r9, r14; x384, x383<- x5 * arg2[2]
mov [ rsp + 0x480 ], rbx; spilling x384 to mem
seto bl; spill OF x219 to reg (rbx)
mov byte [ rsp + 0x488 ], r11b; spilling byte x283 to mem
mov r11, 0x0 ; moving imm to reg
dec r11; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbp, bpl
adox rbp, r11; loading flag
adox r9, [ rsp + 0x3c0 ]
setc bpl; spill CF x442 to reg (rbp)
movzx r11, byte [ rsp + 0x410 ]; load byte memx253 to register64
clc;
mov byte [ rsp + 0x490 ], bl; spilling byte x219 to mem
mov rbx, -0x1 ; moving imm to reg
adcx r11, rbx; loading flag
adcx r8, [ rsp + 0x2e8 ]
setc r11b; spill CF x255 to reg (r11)
clc;
movzx r10, r10b
adcx r10, rbx; loading flag
adcx r8, r12
mov r10, [ rsp + 0x440 ]; load m64 x422 to register64
setc r12b; spill CF x294 to reg (r12)
movzx rbx, byte [ rsp + 0x430 ]; load byte memx429 to register64
clc;
mov byte [ rsp + 0x498 ], r11b; spilling byte x255 to mem
mov r11, -0x1 ; moving imm to reg
adcx rbx, r11; loading flag
adcx r10, [ rsp + 0x408 ]
setc bl; spill CF x431 to reg (rbx)
movzx r11, byte [ rsp + 0x458 ]; load byte memx328 to register64
clc;
mov byte [ rsp + 0x4a0 ], r12b; spilling byte x294 to mem
mov r12, -0x1 ; moving imm to reg
adcx r11, r12; loading flag
adcx r8, [ rsp + 0x50 ]
setc r11b; spill CF x330 to reg (r11)
clc;
movzx rcx, cl
adcx rcx, r12; loading flag
adcx r8, [ rsp + 0x298 ]
movzx rcx, byte [ rsp + 0x450 ]; x145, copying x144 here, cause x144 is needed in a reg for other than x145, namely all: , x145, size: 1
movzx r12, byte [ rsp + 0x400 ]; load byte memx105 to register64
lea rcx, [ rcx + r12 ]; r64+m8
setc r12b; spill CF x369 to reg (r12)
clc;
mov byte [ rsp + 0x4a8 ], r11b; spilling byte x330 to mem
mov r11, -0x1 ; moving imm to reg
movzx rsi, sil
adcx rsi, r11; loading flag
adcx r8, r9
seto sil; spill OF x392 to reg (rsi)
movzx r9, byte [ rsp + 0x460 ]; load byte memx180 to register64
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r11, -0x1 ; moving imm to reg
adox r9, r11; loading flag
adox rcx, [ rsp + 0x80 ]
movzx r9, byte [ rsp + 0x488 ]; x284, copying x283 here, cause x283 is needed in a reg for other than x284, namely all: , x284, size: 1
mov r11, [ rsp + 0x468 ]; load m64 x263 to register64
lea r9, [ r9 + r11 ]; r8/64 + m8
setc r11b; spill CF x405 to reg (r11)
mov byte [ rsp + 0x4b0 ], sil; spilling byte x392 to mem
movzx rsi, byte [ rsp + 0x490 ]; load byte memx219 to register64
clc;
mov byte [ rsp + 0x4b8 ], r12b; spilling byte x369 to mem
mov r12, -0x1 ; moving imm to reg
adcx rsi, r12; loading flag
adcx rcx, [ rsp + 0x448 ]
mov rsi, 0xffffffffffffffff ; moving imm to reg
mov rdx, rsi; 0xffffffffffffffff to rdx
mov byte [ rsp + 0x4c0 ], r11b; spilling byte x405 to mem
mulx r12, r11, r15; x421, x420<- x414 * 0xffffffffffffffff
seto dl; spill OF x222 to reg (rdx)
adc dl, 0x0
movzx rdx, dl
add bpl, 0xFF; load flag from rm/8 into CF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
setc bpl; since that has deps, resore it whereever it was
adcx r8, r10
mov rbp, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, rbp; loading flag
adox r11, [ rsp + 0x438 ]
seto r10b; spill OF x433 to reg (r10)
movzx rbx, byte [ rsp + 0x498 ]; load byte memx255 to register64
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
adox rbx, rbp; loading flag
adox rcx, [ rsp + 0x300 ]
mov bl, dl; preserving value of x222 into a new reg
mov rdx, [ rax + 0x18 ]; saving arg2[3] in rdx.
mov [ rsp + 0x4c8 ], r8; spilling x443 to mem
mulx rbp, r8, r14; x382, x381<- x5 * arg2[3]
movzx rbx, bl
mov [ rsp + 0x4d0 ], r12; spilling x421 to mem
mov r12, [ rsp + 0x318 ]; x258, copying x245 here, cause x245 is needed in a reg for other than x258, namely all: , x258--x259, size: 1
adox r12, rbx
setc bl; spill CF x444 to reg (rbx)
mov byte [ rsp + 0x4d8 ], r10b; spilling byte x433 to mem
movzx r10, byte [ rsp + 0x4a0 ]; load byte memx294 to register64
clc;
mov [ rsp + 0x4e0 ], r11; spilling x432 to mem
mov r11, -0x1 ; moving imm to reg
adcx r10, r11; loading flag
adcx rcx, [ rsp + 0x470 ]
adcx r9, r12
seto r10b; spill OF x259 to reg (r10)
movzx r12, byte [ rsp + 0x4a8 ]; load byte memx330 to register64
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r11, -0x1 ; moving imm to reg
adox r12, r11; loading flag
adox rcx, [ rsp + 0x48 ]
mov rdx, r14; x5 to rdx
mulx r14, r12, [ rax + 0x28 ]; x378, x377<- x5 * arg2[5]
movzx r11, r10b; x299, copying x259 here, cause x259 is needed in a reg for other than x299, namely all: , x299, size: 1
mov [ rsp + 0x4e8 ], r14; spilling x378 to mem
mov r14, 0x0 ; moving imm to reg
adcx r11, r14
movzx r10, byte [ rsp + 0x4b8 ]; load byte memx369 to register64
clc;
mov r14, -0x1 ; moving imm to reg
adcx r10, r14; loading flag
adcx rcx, [ rsp + 0x2c0 ]
mulx rdx, r10, [ rax + 0x20 ]; x380, x379<- x5 * arg2[4]
mov r14, [ rsp + 0x40 ]; x333, copying x320 here, cause x320 is needed in a reg for other than x333, namely all: , x333--x334, size: 1
adox r14, r9
setc r9b; spill CF x371 to reg (r9)
mov [ rsp + 0x4f0 ], r14; spilling x333 to mem
movzx r14, byte [ rsp + 0x4b0 ]; load byte memx392 to register64
clc;
mov [ rsp + 0x4f8 ], r12; spilling x377 to mem
mov r12, -0x1 ; moving imm to reg
adcx r14, r12; loading flag
adcx r8, [ rsp + 0x480 ]
mov r14, [ rsp + 0x38 ]; x335, copying x322 here, cause x322 is needed in a reg for other than x335, namely all: , x335--x336, size: 1
adox r14, r11
seto r11b; spill OF x336 to reg (r11)
movzx r12, byte [ rsp + 0x4c0 ]; load byte memx405 to register64
mov [ rsp + 0x500 ], r14; spilling x335 to mem
mov r14, -0x1 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r14, -0x1 ; moving imm to reg
adox r12, r14; loading flag
adox rcx, r8
adcx r10, rbp
seto r12b; spill OF x407 to reg (r12)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, rbp; loading flag
adox rcx, [ rsp + 0x4e0 ]
mov rbx, [ rsp + 0x4f8 ]; x397, copying x377 here, cause x377 is needed in a reg for other than x397, namely all: , x397--x398, size: 1
adcx rbx, rdx
mov rdx, [ rsp + 0x2b8 ]; load m64 x359 to register64
setc r8b; spill CF x398 to reg (r8)
clc;
movzx r9, r9b
adcx r9, rbp; loading flag
adcx rdx, [ rsp + 0x4f0 ]
mov r9, [ rsp + 0x2f8 ]; load m64 x361 to register64
mov r14, [ rsp + 0x500 ]; x374, copying x335 here, cause x335 is needed in a reg for other than x374, namely all: , x374--x375, size: 1
adcx r14, r9
mov r9, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r15; x414, swapping with x372, which is currently in rdx
mov [ rsp + 0x508 ], rcx; spilling x445 to mem
mulx rbp, rcx, r9; x417, x416<- x414 * 0xffffffffffffffff
mov [ rsp + 0x510 ], rbp; spilling x417 to mem
mulx rdx, rbp, r9; x419, x418<- x414 * 0xffffffffffffffff
movzx r9, r11b; x376, copying x336 here, cause x336 is needed in a reg for other than x376, namely all: , x376, size: 1
mov [ rsp + 0x518 ], rbx; spilling x397 to mem
mov rbx, 0x0 ; moving imm to reg
adcx r9, rbx
movzx r11, byte [ rsp + 0x4d8 ]; load byte memx433 to register64
clc;
mov rbx, -0x1 ; moving imm to reg
adcx r11, rbx; loading flag
adcx rbp, [ rsp + 0x4d0 ]
adcx rcx, rdx
movzx r11, r8b; x399, copying x398 here, cause x398 is needed in a reg for other than x399, namely all: , x399, size: 1
mov rdx, [ rsp + 0x4e8 ]; load m64 x378 to register64
lea r11, [ r11 + rdx ]; r8/64 + m8
setc dl; spill CF x437 to reg (rdx)
clc;
movzx r12, r12b
adcx r12, rbx; loading flag
adcx r15, r10
adox rbp, r15
mov r12, [ rsp + 0x518 ]; x410, copying x397 here, cause x397 is needed in a reg for other than x410, namely all: , x410--x411, size: 1
adcx r12, r14
movzx r10, dl; x438, copying x437 here, cause x437 is needed in a reg for other than x438, namely all: , x438, size: 1
mov r8, [ rsp + 0x510 ]; load m64 x417 to register64
lea r10, [ r10 + r8 ]; r8/64 + m8
adcx r11, r9
adox rcx, r12
setc r14b; spill CF x413 to reg (r14)
seto r8b; spill OF x450 to reg (r8)
mov r9, [ rsp + 0x478 ]; x454, copying x441 here, cause x441 is needed in a reg for other than x454, namely all: , x468, x454--x455, size: 2
mov rdx, 0xffffffff ; moving imm to reg
sub r9, rdx
mov r15, [ rsp + 0x4c8 ]; x456, copying x443 here, cause x443 is needed in a reg for other than x456, namely all: , x456--x457, x469, size: 2
mov r12, 0xffffffff00000000 ; moving imm to reg
sbb r15, r12
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, rbx; loading flag
adox r11, r10
movzx r10, r14b; x453, copying x413 here, cause x413 is needed in a reg for other than x453, namely all: , x453, size: 1
mov r8, 0x0 ; moving imm to reg
adox r10, r8
mov r14, [ rsp + 0x508 ]; x458, copying x445 here, cause x445 is needed in a reg for other than x458, namely all: , x470, x458--x459, size: 2
mov r8, 0xfffffffffffffffe ; moving imm to reg
sbb r14, r8
mov rbx, rbp; x460, copying x447 here, cause x447 is needed in a reg for other than x460, namely all: , x471, x460--x461, size: 2
mov r8, 0xffffffffffffffff ; moving imm to reg
sbb rbx, r8
mov r12, rcx; x462, copying x449 here, cause x449 is needed in a reg for other than x462, namely all: , x472, x462--x463, size: 2
sbb r12, r8
mov rdx, r11; x464, copying x451 here, cause x451 is needed in a reg for other than x464, namely all: , x473, x464--x465, size: 2
sbb rdx, r8
sbb r10, 0x00000000
cmovc r12, rcx; if CF, x472<- x449 (nzVar)
cmovc r15, [ rsp + 0x4c8 ]; if CF, x469<- x443 (nzVar)
cmovc r9, [ rsp + 0x478 ]; if CF, x468<- x441 (nzVar)
cmovc rdx, r11; if CF, x473<- x451 (nzVar)
cmovc rbx, rbp; if CF, x471<- x447 (nzVar)
cmovc r14, [ rsp + 0x508 ]; if CF, x470<- x445 (nzVar)
mov r10, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r10 + 0x8 ], r15; out1[1] = x469
mov [ r10 + 0x28 ], rdx; out1[5] = x473
mov [ r10 + 0x18 ], rbx; out1[3] = x471
mov [ r10 + 0x20 ], r12; out1[4] = x472
mov [ r10 + 0x10 ], r14; out1[2] = x470
mov [ r10 + 0x0 ], r9; out1[0] = x468
mov rbx, [ rsp + 0x520 ]; restoring from stack
mov rbp, [ rsp + 0x528 ]; restoring from stack
mov r12, [ rsp + 0x530 ]; restoring from stack
mov r13, [ rsp + 0x538 ]; restoring from stack
mov r14, [ rsp + 0x540 ]; restoring from stack
mov r15, [ rsp + 0x548 ]; restoring from stack
add rsp, 0x550 
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; clocked at 2200 MHz
; first cyclecount 247.69, best 201.57142857142858, lastGood 213.8909090909091
; seed 2631520366048122 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4773812 ms / 60000 runs=> 79.56353333333334ms/run
; Time spent for assembling and measureing (initial batch_size=54, initial num_batches=101): 146950 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.030782527673900856
; number reverted permutation/ tried permutation: 19192 / 29951 =64.078%
; number reverted decision/ tried decision: 18008 / 30050 =59.927%