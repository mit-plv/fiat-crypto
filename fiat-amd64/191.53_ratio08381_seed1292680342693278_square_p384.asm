SECTION .text
	GLOBAL square_p384
square_p384:
sub rsp, 0x4a8 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x478 ], rbx; saving to stack
mov [ rsp + 0x480 ], rbp; saving to stack
mov [ rsp + 0x488 ], r12; saving to stack
mov [ rsp + 0x490 ], r13; saving to stack
mov [ rsp + 0x498 ], r14; saving to stack
mov [ rsp + 0x4a0 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x6 to register64
mov rdx, rax; x6 to rdx
mulx rax, r10, [ rsi + 0x0 ]; x18, x17<- x6 * arg1[0]
mov r11, 0x100000001 ; moving imm to reg
xchg rdx, r11; 0x100000001, swapping with x6, which is currently in rdx
mulx rbx, rbp, r10; _, x30<- x17 * 0x100000001
xchg rdx, r11; x6, swapping with 0x100000001, which is currently in rdx
mulx rbx, r12, [ rsi + 0x10 ]; x14, x13<- x6 * arg1[2]
mulx r13, r14, [ rsi + 0x8 ]; x16, x15<- x6 * arg1[1]
mov r15, [ rsi + 0x8 ]; load m64 x1 to register64
mov rcx, 0xffffffff ; moving imm to reg
xchg rdx, rcx; 0xffffffff, swapping with x6, which is currently in rdx
mulx r8, r9, rbp; x43, x42<- x30 * 0xffffffff
add r14, rax; could be done better, if r0 has been u8 as well
mov rax, 0xffffffff00000000 ; moving imm to reg
xchg rdx, rax; 0xffffffff00000000, swapping with 0xffffffff, which is currently in rdx
mulx r11, rax, rbp; x41, x40<- x30 * 0xffffffff00000000
xchg rdx, r15; x1, swapping with 0xffffffff00000000, which is currently in rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r15, rdi, [ rsi + 0x8 ]; x78, x77<- x1 * arg1[1]
mov [ rsp + 0x8 ], r15; spilling x78 to mem
mov r15, -0x2 ; moving imm to reg
inc r15; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rax, r8
mulx r8, r15, [ rsi + 0x0 ]; x80, x79<- x1 * arg1[0]
mov [ rsp + 0x10 ], rbx; spilling x14 to mem
setc bl; spill CF x20 to reg (rbx)
clc;
adcx r9, r10
adcx rax, r14
seto r9b; spill OF x45 to reg (r9)
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rdi, r8
setc r14b; spill CF x58 to reg (r14)
clc;
adcx r15, rax
seto r8b; spill OF x82 to reg (r8)
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rax, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, rax; loading flag
adox r13, r12
mov r12, [ rsi + 0x10 ]; load m64 x2 to register64
mulx rbx, r10, [ rsi + 0x10 ]; x76, x75<- x1 * arg1[2]
mov rax, 0xfffffffffffffffe ; moving imm to reg
xchg rdx, rbp; x30, swapping with x1, which is currently in rdx
mov [ rsp + 0x18 ], rbx; spilling x76 to mem
mov [ rsp + 0x20 ], r10; spilling x75 to mem
mulx rbx, r10, rax; x39, x38<- x30 * 0xfffffffffffffffe
mov rax, rdx; preserving value of x30 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov byte [ rsp + 0x28 ], r8b; spilling byte x82 to mem
mov [ rsp + 0x30 ], rbx; spilling x39 to mem
mulx r8, rbx, r12; x157, x156<- x2 * arg1[0]
mov rdx, 0x100000001 ; moving imm to reg
mov [ rsp + 0x38 ], r8; spilling x157 to mem
mov [ rsp + 0x40 ], rcx; spilling x6 to mem
mulx r8, rcx, r15; _, x106<- x92 * 0x100000001
setc r8b; spill CF x93 to reg (r8)
clc;
mov rdx, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, rdx; loading flag
adcx r11, r10
mov r9, 0xffffffff00000000 ; moving imm to reg
mov rdx, rcx; x106 to rdx
mulx rcx, r10, r9; x117, x116<- x106 * 0xffffffff00000000
mov r9, 0xffffffff ; moving imm to reg
mov [ rsp + 0x48 ], rcx; spilling x117 to mem
mov [ rsp + 0x50 ], rbx; spilling x156 to mem
mulx rcx, rbx, r9; x119, x118<- x106 * 0xffffffff
setc r9b; spill CF x47 to reg (r9)
clc;
adcx r10, rcx
mov rcx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rcx; 0xffffffffffffffff, swapping with x106, which is currently in rdx
mov byte [ rsp + 0x58 ], r9b; spilling byte x47 to mem
mov [ rsp + 0x60 ], r10; spilling x120 to mem
mulx r9, r10, rax; x37, x36<- x30 * 0xffffffffffffffff
seto dl; spill OF x22 to reg (rdx)
mov [ rsp + 0x68 ], r9; spilling x37 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r14, r14b
adox r14, r9; loading flag
adox r13, r11
setc r14b; spill CF x121 to reg (r14)
clc;
movzx r8, r8b
adcx r8, r9; loading flag
adcx r13, rdi
setc dil; spill CF x95 to reg (rdi)
clc;
adcx rbx, r15
mov rbx, [ rsp + 0x60 ]; x133, copying x120 here, cause x120 is needed in a reg for other than x133, namely all: , x133--x134, size: 1
adcx rbx, r13
setc r15b; spill CF x134 to reg (r15)
clc;
adcx rbx, [ rsp + 0x50 ]
mov r8b, dl; preserving value of x22 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx r11, r13, [ rsp + 0x40 ]; x12, x11<- x6 * arg1[3]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x70 ], r11; spilling x12 to mem
mulx r9, r11, r12; x155, x154<- x2 * arg1[1]
mov rdx, 0x100000001 ; moving imm to reg
mov [ rsp + 0x78 ], r9; spilling x155 to mem
mov byte [ rsp + 0x80 ], r15b; spilling byte x134 to mem
mulx r9, r15, rbx; _, x183<- x169 * 0x100000001
mov r9, 0xffffffff ; moving imm to reg
xchg rdx, r15; x183, swapping with 0x100000001, which is currently in rdx
mov [ rsp + 0x88 ], r11; spilling x154 to mem
mulx r15, r11, r9; x196, x195<- x183 * 0xffffffff
setc r9b; spill CF x170 to reg (r9)
mov [ rsp + 0x90 ], r15; spilling x196 to mem
movzx r15, byte [ rsp + 0x58 ]; load byte memx47 to register64
clc;
mov byte [ rsp + 0x98 ], r14b; spilling byte x121 to mem
mov r14, -0x1 ; moving imm to reg
adcx r15, r14; loading flag
adcx r10, [ rsp + 0x30 ]
setc r15b; spill CF x49 to reg (r15)
clc;
movzx r8, r8b
adcx r8, r14; loading flag
adcx r13, [ rsp + 0x10 ]
mov r8, [ rsp + 0x20 ]; load m64 x75 to register64
setc r14b; spill CF x24 to reg (r14)
mov byte [ rsp + 0xa0 ], r15b; spilling byte x49 to mem
movzx r15, byte [ rsp + 0x28 ]; load byte memx82 to register64
clc;
mov byte [ rsp + 0xa8 ], r9b; spilling byte x170 to mem
mov r9, -0x1 ; moving imm to reg
adcx r15, r9; loading flag
adcx r8, [ rsp + 0x8 ]
adox r10, r13
seto r15b; spill OF x62 to reg (r15)
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r11, rbx
mov r11, [ rsi + 0x18 ]; load m64 x3 to register64
setc bl; spill CF x84 to reg (rbx)
clc;
mov r13, -0x1 ; moving imm to reg
movzx rdi, dil
adcx rdi, r13; loading flag
adcx r10, r8
mov rdi, 0xfffffffffffffffe ; moving imm to reg
xchg rdx, rdi; 0xfffffffffffffffe, swapping with x183, which is currently in rdx
mulx r8, r9, rcx; x115, x114<- x106 * 0xfffffffffffffffe
setc r13b; spill CF x97 to reg (r13)
movzx rdx, byte [ rsp + 0x98 ]; load byte memx121 to register64
clc;
mov byte [ rsp + 0xb0 ], r15b; spilling byte x62 to mem
mov r15, -0x1 ; moving imm to reg
adcx rdx, r15; loading flag
adcx r9, [ rsp + 0x48 ]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov byte [ rsp + 0xb8 ], r13b; spilling byte x97 to mem
mulx r15, r13, r11; x234, x233<- x3 * arg1[0]
mov rdx, [ rsp + 0x88 ]; load m64 x154 to register64
mov byte [ rsp + 0xc0 ], r14b; spilling byte x24 to mem
seto r14b; spill OF x209 to reg (r14)
mov byte [ rsp + 0xc8 ], bl; spilling byte x84 to mem
mov rbx, -0x2 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rdx, [ rsp + 0x38 ]
setc bl; spill CF x123 to reg (rbx)
mov [ rsp + 0xd0 ], r8; spilling x115 to mem
movzx r8, byte [ rsp + 0x80 ]; load byte memx134 to register64
clc;
mov [ rsp + 0xd8 ], r15; spilling x234 to mem
mov r15, -0x1 ; moving imm to reg
adcx r8, r15; loading flag
adcx r10, r9
mov r8, 0xffffffff00000000 ; moving imm to reg
xchg rdx, r8; 0xffffffff00000000, swapping with x158, which is currently in rdx
mulx r9, r15, rdi; x194, x193<- x183 * 0xffffffff00000000
setc dl; spill CF x136 to reg (rdx)
mov byte [ rsp + 0xe0 ], bl; spilling byte x123 to mem
movzx rbx, byte [ rsp + 0xa8 ]; load byte memx170 to register64
clc;
mov [ rsp + 0xe8 ], rbp; spilling x1 to mem
mov rbp, -0x1 ; moving imm to reg
adcx rbx, rbp; loading flag
adcx r10, r8
setc bl; spill CF x172 to reg (rbx)
clc;
adcx r15, [ rsp + 0x90 ]
setc r8b; spill CF x198 to reg (r8)
clc;
movzx r14, r14b
adcx r14, rbp; loading flag
adcx r10, r15
setc r14b; spill CF x211 to reg (r14)
clc;
adcx r13, r10
mov r15, 0x100000001 ; moving imm to reg
xchg rdx, r13; x246, swapping with x136, which is currently in rdx
mulx r10, rbp, r15; _, x260<- x246 * 0x100000001
mov r10, 0xfffffffffffffffe ; moving imm to reg
xchg rdx, rbp; x260, swapping with x246, which is currently in rdx
mov byte [ rsp + 0xf0 ], r14b; spilling byte x211 to mem
mulx r15, r14, r10; x269, x268<- x260 * 0xfffffffffffffffe
mov r10, 0xffffffffffffffff ; moving imm to reg
mov byte [ rsp + 0xf8 ], bl; spilling byte x172 to mem
mov byte [ rsp + 0x100 ], r13b; spilling byte x136 to mem
mulx rbx, r13, r10; x263, x262<- x260 * 0xffffffffffffffff
mov [ rsp + 0x108 ], r9; spilling x194 to mem
mov byte [ rsp + 0x110 ], r8b; spilling byte x198 to mem
mulx r9, r8, r10; x267, x266<- x260 * 0xffffffffffffffff
mov r10, 0xffffffff ; moving imm to reg
mov [ rsp + 0x118 ], rbx; spilling x263 to mem
mov [ rsp + 0x120 ], r13; spilling x262 to mem
mulx rbx, r13, r10; x273, x272<- x260 * 0xffffffff
mov r10, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x128 ], r13; spilling x272 to mem
mov [ rsp + 0x130 ], r9; spilling x267 to mem
mulx r13, r9, r10; x265, x264<- x260 * 0xffffffffffffffff
mov r10, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x138 ], r13; spilling x265 to mem
mulx rdx, r13, r10; x271, x270<- x260 * 0xffffffff00000000
setc r10b; spill CF x247 to reg (r10)
clc;
adcx r13, rbx
adcx r14, rdx
mov rbx, [ rsi + 0x28 ]; load m64 x5 to register64
adcx r8, r15
mov r15, [ rsp + 0x130 ]; x280, copying x267 here, cause x267 is needed in a reg for other than x280, namely all: , x280--x281, size: 1
adcx r15, r9
mov r9, [ rsp + 0x120 ]; load m64 x262 to register64
mov rdx, [ rsp + 0x138 ]; x282, copying x265 here, cause x265 is needed in a reg for other than x282, namely all: , x282--x283, size: 1
adcx rdx, r9
mov r9, rdx; preserving value of x282 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x140 ], r15; spilling x280 to mem
mov [ rsp + 0x148 ], r8; spilling x278 to mem
mulx r15, r8, rbx; x378, x377<- x5 * arg1[5]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x150 ], r9; spilling x282 to mem
mov [ rsp + 0x158 ], r14; spilling x276 to mem
mulx r9, r14, r11; x226, x225<- x3 * arg1[4]
mov rdx, rbx; x5 to rdx
mov [ rsp + 0x160 ], r13; spilling x274 to mem
mulx rbx, r13, [ rsi + 0x0 ]; x388, x387<- x5 * arg1[0]
mov [ rsp + 0x168 ], r13; spilling x387 to mem
mov byte [ rsp + 0x170 ], r10b; spilling byte x247 to mem
mulx r13, r10, [ rsi + 0x18 ]; x382, x381<- x5 * arg1[3]
mov [ rsp + 0x178 ], r9; spilling x226 to mem
mov r9, rdx; preserving value of x5 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x180 ], r14; spilling x225 to mem
mov [ rsp + 0x188 ], rax; spilling x30 to mem
mulx r14, rax, r12; x149, x148<- x2 * arg1[4]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x190 ], r14; spilling x149 to mem
mov [ rsp + 0x198 ], r15; spilling x378 to mem
mulx r14, r15, r12; x151, x150<- x2 * arg1[3]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x1a0 ], r8; spilling x377 to mem
mov [ rsp + 0x1a8 ], rax; spilling x148 to mem
mulx r8, rax, r9; x386, x385<- x5 * arg1[1]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x1b0 ], r14; spilling x151 to mem
mov [ rsp + 0x1b8 ], r13; spilling x382 to mem
mulx r14, r13, r12; x153, x152<- x2 * arg1[2]
mov rdx, r9; x5 to rdx
mov [ rsp + 0x1c0 ], r15; spilling x150 to mem
mulx r9, r15, [ rsi + 0x10 ]; x384, x383<- x5 * arg1[2]
mov [ rsp + 0x1c8 ], r14; spilling x153 to mem
setc r14b; spill CF x283 to reg (r14)
clc;
adcx rax, rbx
adcx r15, r8
adcx r10, r9
movzx rbx, r14b; x284, copying x283 here, cause x283 is needed in a reg for other than x284, namely all: , x284, size: 1
mov r8, [ rsp + 0x118 ]; load m64 x263 to register64
lea rbx, [ rbx + r8 ]; r8/64 + m8
mulx rdx, r8, [ rsi + 0x20 ]; x380, x379<- x5 * arg1[4]
mov r14, rdx; preserving value of x380 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx r12, r9, r12; x147, x146<- x2 * arg1[5]
mov rdx, [ rsp + 0x78 ]; x160, copying x155 here, cause x155 is needed in a reg for other than x160, namely all: , x160--x161, size: 1
adox rdx, r13
mov r13, [ rsp + 0x1c8 ]; load m64 x153 to register64
mov [ rsp + 0x1d0 ], r10; spilling x393 to mem
mov r10, [ rsp + 0x1c0 ]; x162, copying x150 here, cause x150 is needed in a reg for other than x162, namely all: , x162--x163, size: 1
adox r10, r13
mov r13, [ rsp + 0x1b8 ]; x395, copying x382 here, cause x382 is needed in a reg for other than x395, namely all: , x395--x396, size: 1
adcx r13, r8
mov r8, rdx; preserving value of x160 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x1d8 ], r13; spilling x395 to mem
mov [ rsp + 0x1e0 ], rbx; spilling x284 to mem
mulx r13, rbx, r11; x232, x231<- x3 * arg1[1]
mov rdx, [ rsp + 0x1a8 ]; load m64 x148 to register64
mov [ rsp + 0x1e8 ], r15; spilling x391 to mem
mov r15, [ rsp + 0x1b0 ]; x164, copying x151 here, cause x151 is needed in a reg for other than x164, namely all: , x164--x165, size: 1
adox r15, rdx
mov rdx, [ rsp + 0x1a0 ]; x397, copying x377 here, cause x377 is needed in a reg for other than x397, namely all: , x397--x398, size: 1
adcx rdx, r14
mov r14, rdx; preserving value of x397 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x1f0 ], rax; spilling x389 to mem
mov [ rsp + 0x1f8 ], r15; spilling x164 to mem
mulx rax, r15, r11; x230, x229<- x3 * arg1[2]
mov rdx, [ rsp + 0x198 ]; x399, copying x378 here, cause x378 is needed in a reg for other than x399, namely all: , x399, size: 1
mov [ rsp + 0x200 ], r14; spilling x397 to mem
mov r14, 0x0 ; moving imm to reg
adcx rdx, r14
mov r14, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rcx; x106, swapping with x399, which is currently in rdx
mov [ rsp + 0x208 ], rcx; spilling x399 to mem
mov [ rsp + 0x210 ], r10; spilling x162 to mem
mulx rcx, r10, r14; x113, x112<- x106 * 0xffffffffffffffff
xchg rdx, r11; x3, swapping with x106, which is currently in rdx
mov [ rsp + 0x218 ], rcx; spilling x113 to mem
mulx r14, rcx, [ rsi + 0x28 ]; x224, x223<- x3 * arg1[5]
mov [ rsp + 0x220 ], r12; spilling x147 to mem
mov r12, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r12; 0xffffffffffffffff, swapping with x3, which is currently in rdx
mov [ rsp + 0x228 ], r8; spilling x160 to mem
mov [ rsp + 0x230 ], r10; spilling x112 to mem
mulx r8, r10, [ rsp + 0x188 ]; x35, x34<- x30 * 0xffffffffffffffff
clc;
adcx rbx, [ rsp + 0xd8 ]
adcx r15, r13
xchg rdx, r12; x3, swapping with 0xffffffffffffffff, which is currently in rdx
mulx rdx, r13, [ rsi + 0x18 ]; x228, x227<- x3 * arg1[3]
adcx r13, rax
mov rax, [ rsp + 0x190 ]; x166, copying x149 here, cause x149 is needed in a reg for other than x166, namely all: , x166--x167, size: 1
adox rax, r9
seto r9b; spill OF x167 to reg (r9)
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, [ rsp + 0x128 ]
mov rbp, [ rsp + 0x180 ]; x241, copying x225 here, cause x225 is needed in a reg for other than x241, namely all: , x241--x242, size: 1
adcx rbp, rdx
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x238 ], rbp; spilling x241 to mem
mulx r12, rbp, [ rsp + 0x40 ]; x10, x9<- x6 * arg1[4]
mov rdx, 0xfffffffffffffffe ; moving imm to reg
mov [ rsp + 0x240 ], rax; spilling x166 to mem
mov [ rsp + 0x248 ], r13; spilling x239 to mem
mulx rax, r13, rdi; x192, x191<- x183 * 0xfffffffffffffffe
mov rdx, [ rsp + 0x178 ]; x243, copying x226 here, cause x226 is needed in a reg for other than x243, namely all: , x243--x244, size: 1
adcx rdx, rcx
seto cl; spill OF x286 to reg (rcx)
mov [ rsp + 0x250 ], rdx; spilling x243 to mem
movzx rdx, byte [ rsp + 0x110 ]; load byte memx198 to register64
mov [ rsp + 0x258 ], r15; spilling x237 to mem
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r15, -0x1 ; moving imm to reg
adox rdx, r15; loading flag
adox r13, [ rsp + 0x108 ]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x260 ], rax; spilling x192 to mem
mulx r15, rax, [ rsp + 0xe8 ]; x74, x73<- x1 * arg1[3]
mov rdx, [ rsi + 0x20 ]; load m64 x4 to register64
mov byte [ rsp + 0x268 ], cl; spilling byte x286 to mem
mov rcx, 0x0 ; moving imm to reg
adcx r14, rcx
mov rcx, [ rsp + 0xd0 ]; load m64 x115 to register64
mov [ rsp + 0x270 ], r14; spilling x245 to mem
movzx r14, byte [ rsp + 0xe0 ]; load byte memx123 to register64
clc;
mov [ rsp + 0x278 ], r12; spilling x10 to mem
mov r12, -0x1 ; moving imm to reg
adcx r14, r12; loading flag
adcx rcx, [ rsp + 0x230 ]
seto r14b; spill OF x200 to reg (r14)
movzx r12, byte [ rsp + 0xa0 ]; load byte memx49 to register64
mov [ rsp + 0x280 ], rdx; spilling x4 to mem
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
adox r12, rdx; loading flag
adox r10, [ rsp + 0x68 ]
setc r12b; spill CF x125 to reg (r12)
movzx rdx, byte [ rsp + 0xc8 ]; load byte memx84 to register64
clc;
mov byte [ rsp + 0x288 ], r14b; spilling byte x200 to mem
mov r14, -0x1 ; moving imm to reg
adcx rdx, r14; loading flag
adcx rax, [ rsp + 0x18 ]
setc dl; spill CF x86 to reg (rdx)
movzx r14, byte [ rsp + 0xc0 ]; load byte memx24 to register64
clc;
mov byte [ rsp + 0x290 ], r12b; spilling byte x125 to mem
mov r12, -0x1 ; moving imm to reg
adcx r14, r12; loading flag
adcx rbp, [ rsp + 0x70 ]
setc r14b; spill CF x26 to reg (r14)
movzx r12, byte [ rsp + 0xb0 ]; load byte memx62 to register64
clc;
mov [ rsp + 0x298 ], rbx; spilling x235 to mem
mov rbx, -0x1 ; moving imm to reg
adcx r12, rbx; loading flag
adcx rbp, r10
mov r12b, dl; preserving value of x86 into a new reg
mov rdx, [ rsp + 0x40 ]; saving x6 in rdx.
mulx rdx, r10, [ rsi + 0x28 ]; x8, x7<- x6 * arg1[5]
setc bl; spill CF x64 to reg (rbx)
mov [ rsp + 0x2a0 ], rdx; spilling x8 to mem
movzx rdx, byte [ rsp + 0xb8 ]; load byte memx97 to register64
clc;
mov [ rsp + 0x2a8 ], r10; spilling x7 to mem
mov r10, -0x1 ; moving imm to reg
adcx rdx, r10; loading flag
adcx rbp, rax
mov rdx, 0xffffffffffffffff ; moving imm to reg
mulx rax, r10, [ rsp + 0x188 ]; x33, x32<- x30 * 0xffffffffffffffff
setc dl; spill CF x99 to reg (rdx)
mov [ rsp + 0x2b0 ], rax; spilling x33 to mem
movzx rax, byte [ rsp + 0x100 ]; load byte memx136 to register64
clc;
mov byte [ rsp + 0x2b8 ], bl; spilling byte x64 to mem
mov rbx, -0x1 ; moving imm to reg
adcx rax, rbx; loading flag
adcx rbp, rcx
setc al; spill CF x138 to reg (rax)
movzx rcx, byte [ rsp + 0xf8 ]; load byte memx172 to register64
clc;
adcx rcx, rbx; loading flag
adcx rbp, [ rsp + 0x228 ]
adox r10, r8
setc cl; spill CF x174 to reg (rcx)
movzx r8, byte [ rsp + 0xf0 ]; load byte memx211 to register64
clc;
adcx r8, rbx; loading flag
adcx rbp, r13
movzx r8, r9b; x168, copying x167 here, cause x167 is needed in a reg for other than x168, namely all: , x168, size: 1
mov r13, [ rsp + 0x220 ]; load m64 x147 to register64
lea r8, [ r8 + r13 ]; r8/64 + m8
mov r13b, dl; preserving value of x99 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r9, rbx, [ rsp + 0xe8 ]; x72, x71<- x1 * arg1[4]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x2c0 ], r8; spilling x168 to mem
mov [ rsp + 0x2c8 ], r9; spilling x72 to mem
mulx r8, r9, r11; x111, x110<- x106 * 0xffffffffffffffff
setc dl; spill CF x213 to reg (rdx)
clc;
mov [ rsp + 0x2d0 ], r8; spilling x111 to mem
mov r8, -0x1 ; moving imm to reg
movzx r12, r12b
adcx r12, r8; loading flag
adcx r15, rbx
setc r12b; spill CF x88 to reg (r12)
movzx rbx, byte [ rsp + 0x170 ]; load byte memx247 to register64
clc;
adcx rbx, r8; loading flag
adcx rbp, [ rsp + 0x298 ]
mov bl, dl; preserving value of x213 into a new reg
mov rdx, [ rsp + 0x280 ]; saving x4 in rdx.
mov byte [ rsp + 0x2d8 ], r12b; spilling byte x88 to mem
mulx r8, r12, [ rsi + 0x8 ]; x309, x308<- x4 * arg1[1]
mov [ rsp + 0x2e0 ], r8; spilling x309 to mem
mov r8, [ rsp + 0x2a8 ]; load m64 x7 to register64
mov byte [ rsp + 0x2e8 ], bl; spilling byte x213 to mem
setc bl; spill CF x249 to reg (rbx)
clc;
mov [ rsp + 0x2f0 ], r12; spilling x308 to mem
mov r12, -0x1 ; moving imm to reg
movzx r14, r14b
adcx r14, r12; loading flag
adcx r8, [ rsp + 0x278 ]
setc r14b; spill CF x28 to reg (r14)
movzx r12, byte [ rsp + 0x2b8 ]; load byte memx64 to register64
clc;
mov byte [ rsp + 0x2f8 ], bl; spilling byte x249 to mem
mov rbx, -0x1 ; moving imm to reg
adcx r12, rbx; loading flag
adcx r8, r10
mulx r12, r10, [ rsi + 0x0 ]; x311, x310<- x4 * arg1[0]
setc bl; spill CF x66 to reg (rbx)
mov byte [ rsp + 0x300 ], r14b; spilling byte x28 to mem
movzx r14, byte [ rsp + 0x268 ]; load byte memx286 to register64
clc;
mov [ rsp + 0x308 ], r12; spilling x311 to mem
mov r12, -0x1 ; moving imm to reg
adcx r14, r12; loading flag
adcx rbp, [ rsp + 0x160 ]
seto r14b; spill OF x53 to reg (r14)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r10, rbp
mov rbp, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rdi; x183, swapping with x4, which is currently in rdx
mov byte [ rsp + 0x310 ], bl; spilling byte x66 to mem
mulx r12, rbx, rbp; x190, x189<- x183 * 0xffffffffffffffff
mov rbp, 0x100000001 ; moving imm to reg
xchg rdx, r10; x323, swapping with x183, which is currently in rdx
mov [ rsp + 0x318 ], r12; spilling x190 to mem
mov byte [ rsp + 0x320 ], r14b; spilling byte x53 to mem
mulx r12, r14, rbp; _, x337<- x323 * 0x100000001
mov r12, 0xffffffff00000000 ; moving imm to reg
xchg rdx, r12; 0xffffffff00000000, swapping with x323, which is currently in rdx
mov byte [ rsp + 0x328 ], cl; spilling byte x174 to mem
mulx rbp, rcx, r14; x348, x347<- x337 * 0xffffffff00000000
mov rdx, 0xffffffff ; moving imm to reg
mov [ rsp + 0x330 ], rbp; spilling x348 to mem
mov [ rsp + 0x338 ], rcx; spilling x347 to mem
mulx rbp, rcx, r14; x350, x349<- x337 * 0xffffffff
setc dl; spill CF x288 to reg (rdx)
clc;
adcx rcx, r12
setc cl; spill CF x363 to reg (rcx)
movzx r12, byte [ rsp + 0x290 ]; load byte memx125 to register64
clc;
mov byte [ rsp + 0x340 ], dl; spilling byte x288 to mem
mov rdx, -0x1 ; moving imm to reg
adcx r12, rdx; loading flag
adcx r9, [ rsp + 0x218 ]
setc r12b; spill CF x127 to reg (r12)
clc;
movzx r13, r13b
adcx r13, rdx; loading flag
adcx r8, r15
setc r13b; spill CF x101 to reg (r13)
movzx r15, byte [ rsp + 0x288 ]; load byte memx200 to register64
clc;
adcx r15, rdx; loading flag
adcx rbx, [ rsp + 0x260 ]
setc r15b; spill CF x202 to reg (r15)
clc;
movzx rax, al
adcx rax, rdx; loading flag
adcx r8, r9
seto al; spill OF x324 to reg (rax)
movzx r9, byte [ rsp + 0x328 ]; load byte memx174 to register64
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
adox r9, rdx; loading flag
adox r8, [ rsp + 0x210 ]
mov r9, [ rsp + 0x308 ]; load m64 x311 to register64
setc dl; spill CF x140 to reg (rdx)
clc;
adcx r9, [ rsp + 0x2f0 ]
mov byte [ rsp + 0x348 ], dl; spilling byte x140 to mem
setc dl; spill CF x313 to reg (rdx)
clc;
adcx rbp, [ rsp + 0x338 ]
mov byte [ rsp + 0x350 ], r12b; spilling byte x127 to mem
seto r12b; spill OF x176 to reg (r12)
mov byte [ rsp + 0x358 ], r15b; spilling byte x202 to mem
movzx r15, byte [ rsp + 0x2e8 ]; load byte memx213 to register64
mov byte [ rsp + 0x360 ], r13b; spilling byte x101 to mem
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, r13; loading flag
adox r8, rbx
setc r15b; spill CF x352 to reg (r15)
movzx rbx, byte [ rsp + 0x2f8 ]; load byte memx249 to register64
clc;
adcx rbx, r13; loading flag
adcx r8, [ rsp + 0x258 ]
setc bl; spill CF x251 to reg (rbx)
movzx r13, byte [ rsp + 0x340 ]; load byte memx288 to register64
clc;
mov byte [ rsp + 0x368 ], r15b; spilling byte x352 to mem
mov r15, -0x1 ; moving imm to reg
adcx r13, r15; loading flag
adcx r8, [ rsp + 0x158 ]
seto r13b; spill OF x215 to reg (r13)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
movzx rax, al
adox rax, r15; loading flag
adox r8, r9
seto al; spill OF x326 to reg (rax)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r9; loading flag
adox r8, rbp
setc cl; spill CF x290 to reg (rcx)
clc;
adcx r8, [ rsp + 0x168 ]
mov rbp, 0x100000001 ; moving imm to reg
xchg rdx, rbp; 0x100000001, swapping with x313, which is currently in rdx
mulx r15, r9, r8; _, x414<- x400 * 0x100000001
mov r15, 0xffffffff00000000 ; moving imm to reg
xchg rdx, r9; x414, swapping with 0x100000001, which is currently in rdx
mov byte [ rsp + 0x370 ], al; spilling byte x326 to mem
mulx r9, rax, r15; x425, x424<- x414 * 0xffffffff00000000
mov r15, 0xffffffff ; moving imm to reg
mov byte [ rsp + 0x378 ], cl; spilling byte x290 to mem
mov byte [ rsp + 0x380 ], bl; spilling byte x251 to mem
mulx rcx, rbx, r15; x427, x426<- x414 * 0xffffffff
mov r15, rdx; preserving value of x414 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov byte [ rsp + 0x388 ], r13b; spilling byte x215 to mem
mov [ rsp + 0x390 ], rbx; spilling x426 to mem
mulx r13, rbx, rdi; x303, x302<- x4 * arg1[4]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov byte [ rsp + 0x398 ], r12b; spilling byte x176 to mem
mov [ rsp + 0x3a0 ], r13; spilling x303 to mem
mulx r12, r13, rdi; x307, x306<- x4 * arg1[2]
seto dl; spill OF x365 to reg (rdx)
mov [ rsp + 0x3a8 ], rbx; spilling x302 to mem
mov rbx, -0x2 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rax, rcx
movzx rcx, byte [ rsp + 0x320 ]; x54, copying x53 here, cause x53 is needed in a reg for other than x54, namely all: , x54, size: 1
mov rbx, [ rsp + 0x2b0 ]; load m64 x33 to register64
lea rcx, [ rcx + rbx ]; r8/64 + m8
mov rbx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r15; x414, swapping with x365, which is currently in rdx
mov [ rsp + 0x3b0 ], rax; spilling x428 to mem
mov byte [ rsp + 0x3b8 ], r15b; spilling byte x365 to mem
mulx rax, r15, rbx; x417, x416<- x414 * 0xffffffffffffffff
mov rbx, 0xfffffffffffffffe ; moving imm to reg
mov [ rsp + 0x3c0 ], rcx; spilling x54 to mem
mov [ rsp + 0x3c8 ], rax; spilling x417 to mem
mulx rcx, rax, rbx; x423, x422<- x414 * 0xfffffffffffffffe
mov rbx, rdx; preserving value of x414 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x3d0 ], r12; spilling x307 to mem
mov [ rsp + 0x3d8 ], r15; spilling x416 to mem
mulx r12, r15, rdi; x301, x300<- x4 * arg1[5]
adox rax, r9
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x3e0 ], rax; spilling x430 to mem
mulx r9, rax, rbx; x419, x418<- x414 * 0xffffffffffffffff
mov [ rsp + 0x3e8 ], r12; spilling x301 to mem
mulx rbx, r12, rbx; x421, x420<- x414 * 0xffffffffffffffff
adox r12, rcx
xchg rdx, rdi; x4, swapping with 0xffffffffffffffff, which is currently in rdx
mulx rdx, rcx, [ rsi + 0x18 ]; x305, x304<- x4 * arg1[3]
adox rax, rbx
setc bl; spill CF x401 to reg (rbx)
clc;
mov rdi, -0x1 ; moving imm to reg
movzx rbp, bpl
adcx rbp, rdi; loading flag
adcx r13, [ rsp + 0x2e0 ]
mov rbp, [ rsp + 0x3d8 ]; x436, copying x416 here, cause x416 is needed in a reg for other than x436, namely all: , x436--x437, size: 1
adox rbp, r9
mov r9, rdx; preserving value of x305 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x3f0 ], rbp; spilling x436 to mem
mulx rdi, rbp, [ rsp + 0xe8 ]; x70, x69<- x1 * arg1[5]
mov rdx, [ rsp + 0x3d0 ]; x316, copying x307 here, cause x307 is needed in a reg for other than x316, namely all: , x316--x317, size: 1
adcx rdx, rcx
mov rcx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r10; x183, swapping with x316, which is currently in rdx
mov [ rsp + 0x3f8 ], rax; spilling x434 to mem
mov [ rsp + 0x400 ], r12; spilling x432 to mem
mulx rax, r12, rcx; x186, x185<- x183 * 0xffffffffffffffff
movzx rcx, byte [ rsp + 0x300 ]; x29, copying x28 here, cause x28 is needed in a reg for other than x29, namely all: , x29, size: 1
mov [ rsp + 0x408 ], r10; spilling x316 to mem
mov r10, [ rsp + 0x2a0 ]; load m64 x8 to register64
lea rcx, [ rcx + r10 ]; r8/64 + m8
mov r10, [ rsp + 0x3a8 ]; x318, copying x302 here, cause x302 is needed in a reg for other than x318, namely all: , x318--x319, size: 1
adcx r10, r9
mov r9, [ rsp + 0x3a0 ]; x320, copying x303 here, cause x303 is needed in a reg for other than x320, namely all: , x320--x321, size: 1
adcx r9, r15
mov r15, [ rsp + 0x3c8 ]; x438, copying x417 here, cause x417 is needed in a reg for other than x438, namely all: , x438, size: 1
mov [ rsp + 0x410 ], r9; spilling x320 to mem
mov r9, 0x0 ; moving imm to reg
adox r15, r9
mov r9, [ rsp + 0x3e8 ]; x322, copying x301 here, cause x301 is needed in a reg for other than x322, namely all: , x322, size: 1
adc r9, 0x0
add byte [ rsp + 0x310 ], 0xFF; load flag from rm/8 into CF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
setc [ rsp + 0x310 ]; since that has deps, resore it whereever it was
adcx rcx, [ rsp + 0x3c0 ]
mov [ rsp + 0x418 ], r15; spilling x438 to mem
mov r15, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x420 ], r9; spilling x322 to mem
mulx rdx, r9, r15; x188, x187<- x183 * 0xffffffffffffffff
xchg rdx, r11; x106, swapping with x188, which is currently in rdx
mov [ rsp + 0x428 ], r10; spilling x318 to mem
mulx rdx, r10, r15; x109, x108<- x106 * 0xffffffffffffffff
movzx r15, byte [ rsp + 0x2d8 ]; load byte memx88 to register64
mov [ rsp + 0x430 ], rax; spilling x186 to mem
mov rax, -0x1 ; moving imm to reg
adox r15, rax; loading flag
adox rbp, [ rsp + 0x2c8 ]
seto r15b; spill OF x90 to reg (r15)
movzx rax, byte [ rsp + 0x360 ]; load byte memx101 to register64
mov byte [ rsp + 0x438 ], bl; spilling byte x401 to mem
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rax, rbx; loading flag
adox rcx, rbp
setc al; spill CF x68 to reg (rax)
movzx rbp, byte [ rsp + 0x358 ]; load byte memx202 to register64
clc;
adcx rbp, rbx; loading flag
adcx r9, [ rsp + 0x318 ]
seto bpl; spill OF x103 to reg (rbp)
movzx rbx, byte [ rsp + 0x350 ]; load byte memx127 to register64
mov byte [ rsp + 0x440 ], al; spilling byte x68 to mem
mov rax, -0x1 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rax, -0x1 ; moving imm to reg
adox rbx, rax; loading flag
adox r10, [ rsp + 0x2d0 ]
setc bl; spill CF x204 to reg (rbx)
movzx rax, byte [ rsp + 0x348 ]; load byte memx140 to register64
clc;
mov byte [ rsp + 0x448 ], bpl; spilling byte x103 to mem
mov rbp, -0x1 ; moving imm to reg
adcx rax, rbp; loading flag
adcx rcx, r10
seto al; spill OF x129 to reg (rax)
movzx r10, byte [ rsp + 0x398 ]; load byte memx176 to register64
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
adox r10, rbp; loading flag
adox rcx, [ rsp + 0x1f8 ]
setc r10b; spill CF x142 to reg (r10)
clc;
adcx r8, [ rsp + 0x390 ]
movzx r8, r15b; x91, copying x90 here, cause x90 is needed in a reg for other than x91, namely all: , x91, size: 1
lea r8, [ r8 + rdi ]
seto dil; spill OF x178 to reg (rdi)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, r15; loading flag
adox r11, r12
seto r12b; spill OF x206 to reg (r12)
movzx rbx, byte [ rsp + 0x388 ]; load byte memx215 to register64
inc r15; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
adox rbx, rbp; loading flag
adox rcx, r9
movzx rbx, al; x130, copying x129 here, cause x129 is needed in a reg for other than x130, namely all: , x130, size: 1
lea rbx, [ rbx + rdx ]
setc dl; spill CF x440 to reg (rdx)
movzx r9, byte [ rsp + 0x380 ]; load byte memx251 to register64
clc;
adcx r9, rbp; loading flag
adcx rcx, [ rsp + 0x248 ]
setc r9b; spill CF x253 to reg (r9)
movzx rax, byte [ rsp + 0x378 ]; load byte memx290 to register64
clc;
adcx rax, rbp; loading flag
adcx rcx, [ rsp + 0x148 ]
setc al; spill CF x292 to reg (rax)
movzx r15, byte [ rsp + 0x370 ]; load byte memx326 to register64
clc;
adcx r15, rbp; loading flag
adcx rcx, r13
setc r15b; spill CF x328 to reg (r15)
movzx r13, byte [ rsp + 0x448 ]; load byte memx103 to register64
clc;
mov byte [ rsp + 0x450 ], dl; spilling byte x440 to mem
movzx rdx, byte [ rsp + 0x440 ]; load byte memx68 to register64
adcx r13, rbp; loading flag
adcx r8, rdx
mov rdx, 0xfffffffffffffffe ; moving imm to reg
mulx r13, rbp, r14; x346, x345<- x337 * 0xfffffffffffffffe
setc dl; spill CF x105 to reg (rdx)
clc;
mov [ rsp + 0x458 ], r13; spilling x346 to mem
mov r13, -0x1 ; moving imm to reg
movzx r10, r10b
adcx r10, r13; loading flag
adcx r8, rbx
movzx r10, dl; x145, copying x105 here, cause x105 is needed in a reg for other than x145, namely all: , x145, size: 1
mov rbx, 0x0 ; moving imm to reg
adcx r10, rbx
movzx rdx, byte [ rsp + 0x368 ]; load byte memx352 to register64
clc;
adcx rdx, r13; loading flag
adcx rbp, [ rsp + 0x330 ]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mulx rbx, r13, r14; x344, x343<- x337 * 0xffffffffffffffff
seto dl; spill OF x217 to reg (rdx)
mov [ rsp + 0x460 ], rbx; spilling x344 to mem
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rdi, dil
adox rdi, rbx; loading flag
adox r8, [ rsp + 0x240 ]
setc dil; spill CF x354 to reg (rdi)
movzx rbx, byte [ rsp + 0x3b8 ]; load byte memx365 to register64
clc;
mov [ rsp + 0x468 ], r10; spilling x145 to mem
mov r10, -0x1 ; moving imm to reg
adcx rbx, r10; loading flag
adcx rcx, rbp
setc bl; spill CF x367 to reg (rbx)
clc;
movzx rdx, dl
adcx rdx, r10; loading flag
adcx r8, r11
seto r11b; spill OF x180 to reg (r11)
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, rdx; loading flag
adox r8, [ rsp + 0x238 ]
seto r9b; spill OF x255 to reg (r9)
inc rdx; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov r10, -0x1 ; moving imm to reg
movzx rax, al
adox rax, r10; loading flag
adox r8, [ rsp + 0x140 ]
setc al; spill CF x219 to reg (rax)
movzx rbp, byte [ rsp + 0x438 ]; load byte memx401 to register64
clc;
adcx rbp, r10; loading flag
adcx rcx, [ rsp + 0x1f0 ]
movzx rbp, r12b; x207, copying x206 here, cause x206 is needed in a reg for other than x207, namely all: , x207, size: 1
mov rdx, [ rsp + 0x430 ]; load m64 x186 to register64
lea rbp, [ rbp + rdx ]; r8/64 + m8
setc dl; spill CF x403 to reg (rdx)
clc;
movzx r15, r15b
adcx r15, r10; loading flag
adcx r8, [ rsp + 0x408 ]
seto r12b; spill OF x294 to reg (r12)
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
movzx rdi, dil
adox rdi, r15; loading flag
adox r13, [ rsp + 0x458 ]
setc dil; spill CF x330 to reg (rdi)
clc;
movzx rbx, bl
adcx rbx, r15; loading flag
adcx r8, r13
setc bl; spill CF x369 to reg (rbx)
clc;
movzx rdx, dl
adcx rdx, r15; loading flag
adcx r8, [ rsp + 0x1e8 ]
mov rdx, [ rsp + 0x2c0 ]; load m64 x168 to register64
setc r13b; spill CF x405 to reg (r13)
clc;
movzx r11, r11b
adcx r11, r15; loading flag
adcx rdx, [ rsp + 0x468 ]
setc r11b; spill CF x182 to reg (r11)
clc;
movzx rax, al
adcx rax, r15; loading flag
adcx rdx, rbp
setc al; spill CF x221 to reg (rax)
movzx rbp, byte [ rsp + 0x450 ]; load byte memx440 to register64
clc;
adcx rbp, r15; loading flag
adcx rcx, [ rsp + 0x3b0 ]
mov rbp, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r14; x337, swapping with x220, which is currently in rdx
mulx r10, r15, rbp; x342, x341<- x337 * 0xffffffffffffffff
setc bpl; spill CF x442 to reg (rbp)
clc;
mov [ rsp + 0x470 ], rcx; spilling x441 to mem
mov rcx, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, rcx; loading flag
adcx r14, [ rsp + 0x250 ]
movzx r9, al; x222, copying x221 here, cause x221 is needed in a reg for other than x222, namely all: , x222, size: 1
movzx r11, r11b
lea r9, [ r9 + r11 ]
mov r11, [ rsp + 0x460 ]; x357, copying x344 here, cause x344 is needed in a reg for other than x357, namely all: , x357--x358, size: 1
adox r11, r15
mov rax, [ rsp + 0x270 ]; x258, copying x245 here, cause x245 is needed in a reg for other than x258, namely all: , x258--x259, size: 1
adcx rax, r9
mov r15, 0xffffffffffffffff ; moving imm to reg
mulx rdx, r9, r15; x340, x339<- x337 * 0xffffffffffffffff
seto cl; spill OF x358 to reg (rcx)
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r12, r12b
adox r12, r15; loading flag
adox r14, [ rsp + 0x150 ]
mov r12, [ rsp + 0x1e0 ]; x297, copying x284 here, cause x284 is needed in a reg for other than x297, namely all: , x297--x298, size: 1
adox r12, rax
seto al; spill OF x298 to reg (rax)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r15; loading flag
adox r10, r9
mov rcx, 0x0 ; moving imm to reg
adox rdx, rcx
movzx r9, al; x299, copying x298 here, cause x298 is needed in a reg for other than x299, namely all: , x299, size: 1
adc r9, 0x0
add dil, 0xFF; load flag from rm/8 into CF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
setc dil; since that has deps, resore it whereever it was
adcx r14, [ rsp + 0x428 ]
mov rdi, [ rsp + 0x410 ]; x333, copying x320 here, cause x320 is needed in a reg for other than x333, namely all: , x333--x334, size: 1
adcx rdi, r12
movzx rbp, bpl
adox rbp, r15; loading flag
adox r8, [ rsp + 0x3e0 ]
mov rbp, [ rsp + 0x420 ]; x335, copying x322 here, cause x322 is needed in a reg for other than x335, namely all: , x335--x336, size: 1
adcx rbp, r9
seto al; spill OF x444 to reg (rax)
dec rcx; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx rbx, bl
adox rbx, rcx; loading flag
adox r14, r11
adox r10, rdi
adox rdx, rbp
setc r15b; spill CF x336 to reg (r15)
clc;
movzx r13, r13b
adcx r13, rcx; loading flag
adcx r14, [ rsp + 0x1d0 ]
mov rbx, [ rsp + 0x1d8 ]; x408, copying x395 here, cause x395 is needed in a reg for other than x408, namely all: , x408--x409, size: 1
adcx rbx, r10
movzx r13, r15b; x376, copying x336 here, cause x336 is needed in a reg for other than x376, namely all: , x376, size: 1
mov r11, 0x0 ; moving imm to reg
adox r13, r11
dec r11; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx rax, al
adox rax, r11; loading flag
adox r14, [ rsp + 0x400 ]
mov rcx, [ rsp + 0x200 ]; x410, copying x397 here, cause x397 is needed in a reg for other than x410, namely all: , x410--x411, size: 1
adcx rcx, rdx
mov r12, [ rsp + 0x3f8 ]; x447, copying x434 here, cause x434 is needed in a reg for other than x447, namely all: , x447--x448, size: 1
adox r12, rbx
mov r9, [ rsp + 0x208 ]; x412, copying x399 here, cause x399 is needed in a reg for other than x412, namely all: , x412--x413, size: 1
adcx r9, r13
mov rdi, [ rsp + 0x3f0 ]; x449, copying x436 here, cause x436 is needed in a reg for other than x449, namely all: , x449--x450, size: 1
adox rdi, rcx
mov rax, [ rsp + 0x418 ]; x451, copying x438 here, cause x438 is needed in a reg for other than x451, namely all: , x451--x452, size: 1
adox rax, r9
setc r15b; spill CF x413 to reg (r15)
seto bpl; spill OF x452 to reg (rbp)
mov r10, [ rsp + 0x470 ]; x454, copying x441 here, cause x441 is needed in a reg for other than x454, namely all: , x454--x455, x468, size: 2
mov rdx, 0xffffffff ; moving imm to reg
sub r10, rdx
mov rbx, r8; x456, copying x443 here, cause x443 is needed in a reg for other than x456, namely all: , x469, x456--x457, size: 2
mov r13, 0xffffffff00000000 ; moving imm to reg
sbb rbx, r13
mov rcx, r14; x458, copying x445 here, cause x445 is needed in a reg for other than x458, namely all: , x470, x458--x459, size: 2
mov r9, 0xfffffffffffffffe ; moving imm to reg
sbb rcx, r9
mov r11, r12; x460, copying x447 here, cause x447 is needed in a reg for other than x460, namely all: , x460--x461, x471, size: 2
mov rdx, 0xffffffffffffffff ; moving imm to reg
sbb r11, rdx
movzx r13, bpl; x453, copying x452 here, cause x452 is needed in a reg for other than x453, namely all: , x453, size: 1
movzx r15, r15b
lea r13, [ r13 + r15 ]
mov r15, rdi; x462, copying x449 here, cause x449 is needed in a reg for other than x462, namely all: , x472, x462--x463, size: 2
sbb r15, rdx
mov rbp, rax; x464, copying x451 here, cause x451 is needed in a reg for other than x464, namely all: , x473, x464--x465, size: 2
sbb rbp, rdx
sbb r13, 0x00000000
cmovc rbx, r8; if CF, x469<- x443 (nzVar)
cmovc rcx, r14; if CF, x470<- x445 (nzVar)
cmovc r10, [ rsp + 0x470 ]; if CF, x468<- x441 (nzVar)
cmovc r11, r12; if CF, x471<- x447 (nzVar)
mov r13, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r13 + 0x8 ], rbx; out1[1] = x469
mov [ r13 + 0x0 ], r10; out1[0] = x468
cmovc r15, rdi; if CF, x472<- x449 (nzVar)
mov [ r13 + 0x20 ], r15; out1[4] = x472
cmovc rbp, rax; if CF, x473<- x451 (nzVar)
mov [ r13 + 0x28 ], rbp; out1[5] = x473
mov [ r13 + 0x10 ], rcx; out1[2] = x470
mov [ r13 + 0x18 ], r11; out1[3] = x471
mov rbx, [ rsp + 0x478 ]; restoring from stack
mov rbp, [ rsp + 0x480 ]; restoring from stack
mov r12, [ rsp + 0x488 ]; restoring from stack
mov r13, [ rsp + 0x490 ]; restoring from stack
mov r14, [ rsp + 0x498 ]; restoring from stack
mov r15, [ rsp + 0x4a0 ]; restoring from stack
add rsp, 0x4a8 
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; clocked at 2200 MHz
; first cyclecount 235.11, best 188.7, lastGood 191.53333333333333
; seed 1292680342693278 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4730986 ms / 60000 runs=> 78.84976666666667ms/run
; Time spent for assembling and measureing (initial batch_size=62, initial num_batches=101): 146932 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.03105737366375635
; number reverted permutation/ tried permutation: 19603 / 29964 =65.422%
; number reverted decision/ tried decision: 18061 / 30037 =60.129%