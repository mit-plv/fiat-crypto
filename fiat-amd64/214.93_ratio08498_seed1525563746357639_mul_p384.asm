SECTION .text
	GLOBAL mul_p384
mul_p384:
sub rsp, 0x408 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x3d8 ], rbx; saving to stack
mov [ rsp + 0x3e0 ], rbp; saving to stack
mov [ rsp + 0x3e8 ], r12; saving to stack
mov [ rsp + 0x3f0 ], r13; saving to stack
mov [ rsp + 0x3f8 ], r14; saving to stack
mov [ rsp + 0x400 ], r15; saving to stack
mov rax, [ rsi + 0x20 ]; load m64 x4 to register64
mov r10, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x18 ]; saving arg2[3] in rdx.
mulx r11, rbx, rax; x305, x304<- x4 * arg2[3]
mov rdx, [ r10 + 0x10 ]; arg2[2] to rdx
mulx rbp, r12, rax; x307, x306<- x4 * arg2[2]
mov rdx, rax; x4 to rdx
mulx rax, r13, [ r10 + 0x8 ]; x309, x308<- x4 * arg2[1]
mulx r14, r15, [ r10 + 0x0 ]; x311, x310<- x4 * arg2[0]
add r13, r14; could be done better, if r0 has been u8 as well
mulx rcx, r8, [ r10 + 0x28 ]; x301, x300<- x4 * arg2[5]
mulx rdx, r9, [ r10 + 0x20 ]; x303, x302<- x4 * arg2[4]
adcx r12, rax
mov rax, [ rsi + 0x0 ]; load m64 x6 to register64
adcx rbx, rbp
mov rbp, rdx; preserving value of x303 into a new reg
mov rdx, [ r10 + 0x0 ]; saving arg2[0] in rdx.
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r14, rdi, rax; x18, x17<- x6 * arg2[0]
adcx r9, r11
mov r11, 0x100000001 ; moving imm to reg
mov rdx, r11; 0x100000001 to rdx
mov [ rsp + 0x8 ], r9; spilling x318 to mem
mulx r11, r9, rdi; _, x30<- x17 * 0x100000001
adcx r8, rbp
mov r11, rdx; preserving value of 0x100000001 into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mov [ rsp + 0x10 ], r8; spilling x320 to mem
mulx rbp, r8, rax; x16, x15<- x6 * arg2[1]
mov r11, 0xffffffff ; moving imm to reg
mov rdx, r9; x30 to rdx
mov [ rsp + 0x18 ], rbx; spilling x316 to mem
mulx r9, rbx, r11; x43, x42<- x30 * 0xffffffff
mov r11, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x20 ], r12; spilling x314 to mem
mov [ rsp + 0x28 ], r13; spilling x312 to mem
mulx r12, r13, r11; x41, x40<- x30 * 0xffffffff00000000
adc rcx, 0x0
test al, al
adox r8, r14
adcx r13, r9
setc r14b; spill CF x45 to reg (r14)
clc;
adcx rbx, rdi
adcx r13, r8
mov rbx, [ rsi + 0x8 ]; load m64 x1 to register64
xchg rdx, rax; x6, swapping with x30, which is currently in rdx
mulx rdi, r9, [ r10 + 0x10 ]; x14, x13<- x6 * arg2[2]
xchg rdx, rbx; x1, swapping with x6, which is currently in rdx
mulx r8, r11, [ r10 + 0x0 ]; x80, x79<- x1 * arg2[0]
mov [ rsp + 0x30 ], rcx; spilling x322 to mem
mov rcx, 0xfffffffffffffffe ; moving imm to reg
xchg rdx, rcx; 0xfffffffffffffffe, swapping with x1, which is currently in rdx
mov [ rsp + 0x38 ], r15; spilling x310 to mem
mov [ rsp + 0x40 ], rdi; spilling x14 to mem
mulx r15, rdi, rax; x39, x38<- x30 * 0xfffffffffffffffe
setc dl; spill CF x58 to reg (rdx)
clc;
adcx r11, r13
mov r13, 0x100000001 ; moving imm to reg
xchg rdx, r11; x92, swapping with x58, which is currently in rdx
mov [ rsp + 0x48 ], r15; spilling x39 to mem
mov byte [ rsp + 0x50 ], r11b; spilling byte x58 to mem
mulx r15, r11, r13; _, x106<- x92 * 0x100000001
mov r15, rdx; preserving value of x92 into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mov [ rsp + 0x58 ], rdi; spilling x38 to mem
mulx r13, rdi, rcx; x78, x77<- x1 * arg2[1]
mov [ rsp + 0x60 ], r13; spilling x78 to mem
mov r13, 0xffffffff ; moving imm to reg
mov rdx, r13; 0xffffffff to rdx
mov [ rsp + 0x68 ], r12; spilling x41 to mem
mulx r13, r12, r11; x119, x118<- x106 * 0xffffffff
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x70 ], r13; spilling x119 to mem
mov byte [ rsp + 0x78 ], r14b; spilling byte x45 to mem
mulx r13, r14, rax; x37, x36<- x30 * 0xffffffffffffffff
adox r9, rbp
mov rbp, 0xffffffff00000000 ; moving imm to reg
xchg rdx, r11; x106, swapping with 0xffffffffffffffff, which is currently in rdx
mov [ rsp + 0x80 ], r13; spilling x37 to mem
mulx r11, r13, rbp; x117, x116<- x106 * 0xffffffff00000000
mov rbp, [ rsi + 0x10 ]; load m64 x2 to register64
mov [ rsp + 0x88 ], r11; spilling x117 to mem
setc r11b; spill CF x93 to reg (r11)
clc;
adcx rdi, r8
setc r8b; spill CF x82 to reg (r8)
clc;
adcx r12, r15
mov r12, [ rsp + 0x58 ]; load m64 x38 to register64
setc r15b; spill CF x132 to reg (r15)
mov byte [ rsp + 0x90 ], r8b; spilling byte x82 to mem
movzx r8, byte [ rsp + 0x78 ]; load byte memx45 to register64
clc;
mov [ rsp + 0x98 ], rbp; spilling x2 to mem
mov rbp, -0x1 ; moving imm to reg
adcx r8, rbp; loading flag
adcx r12, [ rsp + 0x68 ]
setc r8b; spill CF x47 to reg (r8)
movzx rbp, byte [ rsp + 0x50 ]; load byte memx58 to register64
clc;
mov byte [ rsp + 0xa0 ], r15b; spilling byte x132 to mem
mov r15, -0x1 ; moving imm to reg
adcx rbp, r15; loading flag
adcx r9, r12
seto bpl; spill OF x22 to reg (rbp)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, r12; loading flag
adox r9, rdi
setc r11b; spill CF x60 to reg (r11)
clc;
movzx r8, r8b
adcx r8, r12; loading flag
adcx r14, [ rsp + 0x48 ]
mov rdi, 0xfffffffffffffffe ; moving imm to reg
mulx r8, r15, rdi; x115, x114<- x106 * 0xfffffffffffffffe
setc r12b; spill CF x49 to reg (r12)
clc;
adcx r13, [ rsp + 0x70 ]
setc dil; spill CF x121 to reg (rdi)
mov [ rsp + 0xa8 ], r8; spilling x115 to mem
movzx r8, byte [ rsp + 0xa0 ]; load byte memx132 to register64
clc;
mov byte [ rsp + 0xb0 ], r12b; spilling byte x49 to mem
mov r12, -0x1 ; moving imm to reg
adcx r8, r12; loading flag
adcx r9, r13
mov r8, rdx; preserving value of x106 into a new reg
mov rdx, [ r10 + 0x0 ]; saving arg2[0] in rdx.
mulx r13, r12, [ rsp + 0x98 ]; x157, x156<- x2 * arg2[0]
mov rdx, [ r10 + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0xb8 ], r13; spilling x157 to mem
mov [ rsp + 0xc0 ], r14; spilling x48 to mem
mulx r13, r14, rbx; x12, x11<- x6 * arg2[3]
mov rdx, rcx; x1 to rdx
mov byte [ rsp + 0xc8 ], r11b; spilling byte x60 to mem
mulx rcx, r11, [ r10 + 0x10 ]; x76, x75<- x1 * arg2[2]
mov [ rsp + 0xd0 ], rcx; spilling x76 to mem
setc cl; spill CF x134 to reg (rcx)
clc;
adcx r12, r9
setc r9b; spill CF x170 to reg (r9)
clc;
mov byte [ rsp + 0xd8 ], cl; spilling byte x134 to mem
mov rcx, -0x1 ; moving imm to reg
movzx rdi, dil
adcx rdi, rcx; loading flag
adcx r15, [ rsp + 0x88 ]
mov rdi, 0x100000001 ; moving imm to reg
xchg rdx, r12; x169, swapping with x1, which is currently in rdx
mov byte [ rsp + 0xe0 ], r9b; spilling byte x170 to mem
mulx rcx, r9, rdi; _, x183<- x169 * 0x100000001
setc cl; spill CF x123 to reg (rcx)
movzx rdi, byte [ rsp + 0x90 ]; load byte memx82 to register64
clc;
mov [ rsp + 0xe8 ], r15; spilling x122 to mem
mov r15, -0x1 ; moving imm to reg
adcx rdi, r15; loading flag
adcx r11, [ rsp + 0x60 ]
setc dil; spill CF x84 to reg (rdi)
clc;
movzx rbp, bpl
adcx rbp, r15; loading flag
adcx r14, [ rsp + 0x40 ]
xchg rdx, rbx; x6, swapping with x169, which is currently in rdx
mulx rbp, r15, [ r10 + 0x20 ]; x10, x9<- x6 * arg2[4]
adcx r15, r13
mov r13, 0xffffffff ; moving imm to reg
xchg rdx, r13; 0xffffffff, swapping with x6, which is currently in rdx
mov [ rsp + 0xf0 ], rbp; spilling x10 to mem
mov byte [ rsp + 0xf8 ], cl; spilling byte x123 to mem
mulx rbp, rcx, r9; x196, x195<- x183 * 0xffffffff
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x100 ], rbp; spilling x196 to mem
mov byte [ rsp + 0x108 ], dil; spilling byte x84 to mem
mulx rbp, rdi, rax; x35, x34<- x30 * 0xffffffffffffffff
setc dl; spill CF x26 to reg (rdx)
mov [ rsp + 0x110 ], rbp; spilling x35 to mem
movzx rbp, byte [ rsp + 0xc8 ]; load byte memx60 to register64
clc;
mov [ rsp + 0x118 ], r15; spilling x25 to mem
mov r15, -0x1 ; moving imm to reg
adcx rbp, r15; loading flag
adcx r14, [ rsp + 0xc0 ]
adox r11, r14
seto bpl; spill OF x97 to reg (rbp)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rcx, rbx
mov cl, dl; preserving value of x26 into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mulx rbx, r14, [ rsp + 0x98 ]; x155, x154<- x2 * arg2[1]
mov r15, 0xffffffff00000000 ; moving imm to reg
mov rdx, r9; x183 to rdx
mov byte [ rsp + 0x120 ], cl; spilling byte x26 to mem
mulx r9, rcx, r15; x194, x193<- x183 * 0xffffffff00000000
seto r15b; spill OF x209 to reg (r15)
mov byte [ rsp + 0x128 ], bpl; spilling byte x97 to mem
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, [ rsp + 0xb8 ]
setc bpl; spill CF x62 to reg (rbp)
mov byte [ rsp + 0x130 ], r15b; spilling byte x209 to mem
movzx r15, byte [ rsp + 0xd8 ]; load byte memx134 to register64
clc;
mov [ rsp + 0x138 ], r9; spilling x194 to mem
mov r9, -0x1 ; moving imm to reg
adcx r15, r9; loading flag
adcx r11, [ rsp + 0xe8 ]
mov r15, 0xfffffffffffffffe ; moving imm to reg
mov [ rsp + 0x140 ], rbx; spilling x155 to mem
mulx r9, rbx, r15; x192, x191<- x183 * 0xfffffffffffffffe
seto r15b; spill OF x159 to reg (r15)
mov [ rsp + 0x148 ], r9; spilling x192 to mem
movzx r9, byte [ rsp + 0xb0 ]; load byte memx49 to register64
mov [ rsp + 0x150 ], rbx; spilling x191 to mem
mov rbx, -0x1 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbx, -0x1 ; moving imm to reg
adox r9, rbx; loading flag
adox rdi, [ rsp + 0x80 ]
setc r9b; spill CF x136 to reg (r9)
clc;
movzx rbp, bpl
adcx rbp, rbx; loading flag
adcx rdi, [ rsp + 0x118 ]
setc bpl; spill CF x64 to reg (rbp)
movzx rbx, byte [ rsp + 0xe0 ]; load byte memx170 to register64
clc;
mov byte [ rsp + 0x158 ], r9b; spilling byte x136 to mem
mov r9, -0x1 ; moving imm to reg
adcx rbx, r9; loading flag
adcx r11, r14
xchg rdx, r12; x1, swapping with x183, which is currently in rdx
mulx rbx, r14, [ r10 + 0x18 ]; x74, x73<- x1 * arg2[3]
mov r9, rdx; preserving value of x1 into a new reg
mov rdx, [ r10 + 0x10 ]; saving arg2[2] in rdx.
mov [ rsp + 0x160 ], r11; spilling x171 to mem
mov [ rsp + 0x168 ], rbx; spilling x74 to mem
mulx r11, rbx, [ rsp + 0x98 ]; x153, x152<- x2 * arg2[2]
mov [ rsp + 0x170 ], r11; spilling x153 to mem
seto r11b; spill OF x51 to reg (r11)
mov byte [ rsp + 0x178 ], bpl; spilling byte x64 to mem
movzx rbp, byte [ rsp + 0x108 ]; load byte memx84 to register64
mov [ rsp + 0x180 ], rdi; spilling x63 to mem
mov rdi, -0x1 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdi, -0x1 ; moving imm to reg
adox rbp, rdi; loading flag
adox r14, [ rsp + 0xd0 ]
seto bpl; spill OF x86 to reg (rbp)
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rcx, [ rsp + 0x100 ]
mov rdi, 0xffffffffffffffff ; moving imm to reg
mov rdx, rax; x30 to rdx
mulx rdx, rax, rdi; x33, x32<- x30 * 0xffffffffffffffff
setc dil; spill CF x172 to reg (rdi)
clc;
mov [ rsp + 0x188 ], rcx; spilling x197 to mem
mov rcx, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, rcx; loading flag
adcx rbx, [ rsp + 0x140 ]
xchg rdx, r13; x6, swapping with x33, which is currently in rdx
mulx rdx, r15, [ r10 + 0x28 ]; x8, x7<- x6 * arg2[5]
mov rcx, [ rsp + 0x150 ]; load m64 x191 to register64
mov byte [ rsp + 0x190 ], bpl; spilling byte x86 to mem
mov rbp, [ rsp + 0x138 ]; x199, copying x194 here, cause x194 is needed in a reg for other than x199, namely all: , x199--x200, size: 1
adox rbp, rcx
setc cl; spill CF x161 to reg (rcx)
mov [ rsp + 0x198 ], rbp; spilling x199 to mem
movzx rbp, byte [ rsp + 0x128 ]; load byte memx97 to register64
clc;
mov [ rsp + 0x1a0 ], rdx; spilling x8 to mem
mov rdx, -0x1 ; moving imm to reg
adcx rbp, rdx; loading flag
adcx r14, [ rsp + 0x180 ]
mov rbp, 0xffffffffffffffff ; moving imm to reg
mov rdx, rbp; 0xffffffffffffffff to rdx
mov byte [ rsp + 0x1a8 ], cl; spilling byte x161 to mem
mulx rbp, rcx, r8; x113, x112<- x106 * 0xffffffffffffffff
seto dl; spill OF x200 to reg (rdx)
mov [ rsp + 0x1b0 ], rbp; spilling x113 to mem
movzx rbp, byte [ rsp + 0xf8 ]; load byte memx123 to register64
mov [ rsp + 0x1b8 ], r13; spilling x33 to mem
mov r13, -0x1 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r13, -0x1 ; moving imm to reg
adox rbp, r13; loading flag
adox rcx, [ rsp + 0xa8 ]
seto bpl; spill OF x125 to reg (rbp)
movzx r13, byte [ rsp + 0x158 ]; load byte memx136 to register64
mov byte [ rsp + 0x1c0 ], dl; spilling byte x200 to mem
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
adox r13, rdx; loading flag
adox r14, rcx
mov r13, 0xffffffffffffffff ; moving imm to reg
mov rdx, r13; 0xffffffffffffffff to rdx
mulx r13, rcx, r12; x190, x189<- x183 * 0xffffffffffffffff
mov [ rsp + 0x1c8 ], r13; spilling x190 to mem
mov r13, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ r10 + 0x20 ]; saving arg2[4] in rdx.
mov [ rsp + 0x1d0 ], rcx; spilling x189 to mem
mov byte [ rsp + 0x1d8 ], bpl; spilling byte x125 to mem
mulx rcx, rbp, r9; x72, x71<- x1 * arg2[4]
seto r13b; spill OF x138 to reg (r13)
mov [ rsp + 0x1e0 ], rcx; spilling x72 to mem
mov rcx, -0x1 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rcx, -0x1 ; moving imm to reg
movzx rdi, dil
adox rdi, rcx; loading flag
adox r14, rbx
setc dil; spill CF x99 to reg (rdi)
clc;
movzx r11, r11b
adcx r11, rcx; loading flag
adcx rax, [ rsp + 0x110 ]
seto r11b; spill OF x174 to reg (r11)
movzx rbx, byte [ rsp + 0x120 ]; load byte memx26 to register64
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rcx, -0x1 ; moving imm to reg
adox rbx, rcx; loading flag
adox r15, [ rsp + 0xf0 ]
mov rbx, [ rsp + 0x1b8 ]; x54, copying x33 here, cause x33 is needed in a reg for other than x54, namely all: , x54, size: 1
mov rcx, 0x0 ; moving imm to reg
adcx rbx, rcx
mov rcx, [ rsp + 0x1a0 ]; x29, copying x8 here, cause x8 is needed in a reg for other than x29, namely all: , x29, size: 1
mov byte [ rsp + 0x1e8 ], r11b; spilling byte x174 to mem
mov r11, 0x0 ; moving imm to reg
adox rcx, r11
mov rdx, [ r10 + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x1f0 ], rbx; spilling x54 to mem
mulx r11, rbx, [ rsp + 0x98 ]; x151, x150<- x2 * arg2[3]
add byte [ rsp + 0x178 ], 0x7F; load flag from rm/8 into OF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
seto [ rsp + 0x178 ]; since that has deps, resore it whereever it was
adox r15, rax
movzx rax, byte [ rsp + 0x190 ]; load byte memx86 to register64
mov [ rsp + 0x1f8 ], r11; spilling x151 to mem
mov r11, -0x1 ; moving imm to reg
adcx rax, r11; loading flag
adcx rbp, [ rsp + 0x168 ]
mov rax, [ rsp + 0x160 ]; load m64 x171 to register64
setc r11b; spill CF x88 to reg (r11)
mov [ rsp + 0x200 ], rcx; spilling x29 to mem
movzx rcx, byte [ rsp + 0x130 ]; load byte memx209 to register64
clc;
mov byte [ rsp + 0x208 ], r13b; spilling byte x138 to mem
mov r13, -0x1 ; moving imm to reg
adcx rcx, r13; loading flag
adcx rax, [ rsp + 0x188 ]
mov rcx, [ rsp + 0x198 ]; x212, copying x199 here, cause x199 is needed in a reg for other than x212, namely all: , x212--x213, size: 1
adcx rcx, r14
mov r14, 0xffffffffffffffff ; moving imm to reg
mov rdx, r8; x106 to rdx
mulx r8, r13, r14; x111, x110<- x106 * 0xffffffffffffffff
mov [ rsp + 0x210 ], rcx; spilling x212 to mem
mulx rdx, rcx, r14; x109, x108<- x106 * 0xffffffffffffffff
seto r14b; spill OF x66 to reg (r14)
mov [ rsp + 0x218 ], rax; spilling x210 to mem
movzx rax, byte [ rsp + 0x1a8 ]; load byte memx161 to register64
mov [ rsp + 0x220 ], rsi; spilling arg1 to mem
mov rsi, 0x0 ; moving imm to reg
dec rsi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rax, rsi; loading flag
adox rbx, [ rsp + 0x170 ]
setc al; spill CF x213 to reg (rax)
movzx rsi, byte [ rsp + 0x1d8 ]; load byte memx125 to register64
clc;
mov [ rsp + 0x228 ], rdx; spilling x109 to mem
mov rdx, -0x1 ; moving imm to reg
adcx rsi, rdx; loading flag
adcx r13, [ rsp + 0x1b0 ]
setc sil; spill CF x127 to reg (rsi)
clc;
movzx rdi, dil
adcx rdi, rdx; loading flag
adcx r15, rbp
setc dil; spill CF x101 to reg (rdi)
movzx rbp, byte [ rsp + 0x208 ]; load byte memx138 to register64
clc;
adcx rbp, rdx; loading flag
adcx r15, r13
mov rdx, [ r10 + 0x28 ]; arg2[5] to rdx
mulx r9, rbp, r9; x70, x69<- x1 * arg2[5]
mov r13, [ rsp + 0x1d0 ]; load m64 x189 to register64
mov [ rsp + 0x230 ], rcx; spilling x108 to mem
seto cl; spill OF x163 to reg (rcx)
mov [ rsp + 0x238 ], r8; spilling x111 to mem
movzx r8, byte [ rsp + 0x1c0 ]; load byte memx200 to register64
mov byte [ rsp + 0x240 ], sil; spilling byte x127 to mem
mov rsi, -0x1 ; moving imm to reg
inc rsi; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rsi, -0x1 ; moving imm to reg
adox r8, rsi; loading flag
adox r13, [ rsp + 0x148 ]
mov rdx, [ rsp + 0x98 ]; x2 to rdx
mulx r8, rsi, [ r10 + 0x28 ]; x147, x146<- x2 * arg2[5]
mov [ rsp + 0x248 ], r8; spilling x147 to mem
mov r8, [ rsp + 0x1f0 ]; load m64 x54 to register64
mov [ rsp + 0x250 ], rsi; spilling x146 to mem
setc sil; spill CF x140 to reg (rsi)
clc;
mov byte [ rsp + 0x258 ], cl; spilling byte x163 to mem
mov rcx, -0x1 ; moving imm to reg
movzx r14, r14b
adcx r14, rcx; loading flag
adcx r8, [ rsp + 0x200 ]
setc r14b; spill CF x68 to reg (r14)
movzx rcx, byte [ rsp + 0x1e8 ]; load byte memx174 to register64
clc;
mov byte [ rsp + 0x260 ], sil; spilling byte x140 to mem
mov rsi, -0x1 ; moving imm to reg
adcx rcx, rsi; loading flag
adcx r15, rbx
setc cl; spill CF x176 to reg (rcx)
clc;
movzx rax, al
adcx rax, rsi; loading flag
adcx r15, r13
seto al; spill OF x202 to reg (rax)
inc rsi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, rbx; loading flag
adox rbp, [ rsp + 0x1e0 ]
setc r11b; spill CF x215 to reg (r11)
clc;
movzx rdi, dil
adcx rdi, rbx; loading flag
adcx r8, rbp
mulx rdx, rdi, [ r10 + 0x20 ]; x149, x148<- x2 * arg2[4]
adox r9, rsi
movzx r13, byte [ rsp + 0x258 ]; load byte memx163 to register64
inc rbx; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
adox r13, rbp; loading flag
adox rdi, [ rsp + 0x1f8 ]
mov r13, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r12; x183, swapping with x149, which is currently in rdx
mulx rbx, rbp, r13; x188, x187<- x183 * 0xffffffffffffffff
mov r13, [ rsp + 0x238 ]; load m64 x111 to register64
mov [ rsp + 0x268 ], r15; spilling x214 to mem
setc r15b; spill CF x103 to reg (r15)
mov byte [ rsp + 0x270 ], r11b; spilling byte x215 to mem
movzx r11, byte [ rsp + 0x240 ]; load byte memx127 to register64
clc;
mov [ rsp + 0x278 ], rdi; spilling x164 to mem
mov rdi, -0x1 ; moving imm to reg
adcx r11, rdi; loading flag
adcx r13, [ rsp + 0x230 ]
mov r11, [ rsp + 0x250 ]; x166, copying x146 here, cause x146 is needed in a reg for other than x166, namely all: , x166--x167, size: 1
adox r11, r12
seto r12b; spill OF x167 to reg (r12)
movzx rdi, byte [ rsp + 0x260 ]; load byte memx140 to register64
mov [ rsp + 0x280 ], r11; spilling x166 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
adox rdi, r11; loading flag
adox r8, r13
mov rdi, [ rsp + 0x228 ]; x130, copying x109 here, cause x109 is needed in a reg for other than x130, namely all: , x130, size: 1
mov r13, 0x0 ; moving imm to reg
adcx rdi, r13
mov r13, 0xffffffffffffffff ; moving imm to reg
mulx rdx, r11, r13; x186, x185<- x183 * 0xffffffffffffffff
clc;
mov r13, -0x1 ; moving imm to reg
movzx r14, r14b
movzx r15, r15b
adcx r15, r13; loading flag
adcx r9, r14
setc r14b; spill CF x105 to reg (r14)
clc;
movzx rax, al
adcx rax, r13; loading flag
adcx rbp, [ rsp + 0x1c8 ]
mov rax, [ rsp + 0x220 ]; load m64 arg1 to register64
mov r15, [ rax + 0x18 ]; load m64 x3 to register64
adcx r11, rbx
setc bl; spill CF x206 to reg (rbx)
clc;
movzx rcx, cl
adcx rcx, r13; loading flag
adcx r8, [ rsp + 0x278 ]
adox rdi, r9
mov rcx, [ rsp + 0x280 ]; x179, copying x166 here, cause x166 is needed in a reg for other than x179, namely all: , x179--x180, size: 1
adcx rcx, rdi
movzx r9, r14b; x145, copying x105 here, cause x105 is needed in a reg for other than x145, namely all: , x145, size: 1
mov rdi, 0x0 ; moving imm to reg
adox r9, rdi
movzx r14, r12b; x168, copying x167 here, cause x167 is needed in a reg for other than x168, namely all: , x168, size: 1
mov rdi, [ rsp + 0x248 ]; load m64 x147 to register64
lea r14, [ r14 + rdi ]; r8/64 + m8
movzx rdi, byte [ rsp + 0x270 ]; load byte memx215 to register64
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
adox rdi, r12; loading flag
adox r8, rbp
xchg rdx, r15; x3, swapping with x186, which is currently in rdx
mulx rdi, rbp, [ r10 + 0x0 ]; x234, x233<- x3 * arg2[0]
mulx r13, r12, [ r10 + 0x8 ]; x232, x231<- x3 * arg2[1]
adcx r14, r9
adox r11, rcx
movzx rcx, bl; x207, copying x206 here, cause x206 is needed in a reg for other than x207, namely all: , x207, size: 1
lea rcx, [ rcx + r15 ]
adox rcx, r14
seto r15b; spill OF x221 to reg (r15)
mov rbx, -0x2 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, [ rsp + 0x218 ]
mov r9, 0x100000001 ; moving imm to reg
xchg rdx, rbp; x246, swapping with x3, which is currently in rdx
mulx r14, rbx, r9; _, x260<- x246 * 0x100000001
mov r14, 0xfffffffffffffffe ; moving imm to reg
xchg rdx, r14; 0xfffffffffffffffe, swapping with x246, which is currently in rdx
mov [ rsp + 0x288 ], rcx; spilling x220 to mem
mulx r9, rcx, rbx; x269, x268<- x260 * 0xfffffffffffffffe
mov rdx, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x290 ], r11; spilling x218 to mem
mov [ rsp + 0x298 ], r8; spilling x216 to mem
mulx r11, r8, rbx; x271, x270<- x260 * 0xffffffff00000000
mov [ rsp + 0x2a0 ], r9; spilling x269 to mem
mov r9, rdx; preserving value of 0xffffffff00000000 into a new reg
mov rdx, [ r10 + 0x10 ]; saving arg2[2] in rdx.
mov [ rsp + 0x2a8 ], rcx; spilling x268 to mem
mov [ rsp + 0x2b0 ], r11; spilling x271 to mem
mulx rcx, r11, rbp; x230, x229<- x3 * arg2[2]
setc r9b; spill CF x182 to reg (r9)
clc;
adcx r12, rdi
mov rdi, 0xffffffff ; moving imm to reg
mov rdx, rbx; x260 to rdx
mov [ rsp + 0x2b8 ], rcx; spilling x230 to mem
mulx rbx, rcx, rdi; x273, x272<- x260 * 0xffffffff
setc dil; spill CF x236 to reg (rdi)
clc;
adcx r8, rbx
movzx rbx, r15b; x222, copying x221 here, cause x221 is needed in a reg for other than x222, namely all: , x222, size: 1
movzx r9, r9b
lea rbx, [ rbx + r9 ]
mov r9, [ rsp + 0x210 ]; x248, copying x212 here, cause x212 is needed in a reg for other than x248, namely all: , x248--x249, size: 1
adox r9, r12
setc r15b; spill CF x275 to reg (r15)
clc;
mov r12, -0x1 ; moving imm to reg
movzx rdi, dil
adcx rdi, r12; loading flag
adcx r13, r11
seto r11b; spill OF x249 to reg (r11)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rcx, r14
mov rcx, [ rsp + 0x2b0 ]; load m64 x271 to register64
setc r14b; spill CF x238 to reg (r14)
clc;
mov rdi, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, rdi; loading flag
adcx rcx, [ rsp + 0x2a8 ]
setc r15b; spill CF x277 to reg (r15)
clc;
movzx r11, r11b
adcx r11, rdi; loading flag
adcx r13, [ rsp + 0x268 ]
adox r8, r9
adox rcx, r13
setc r11b; spill CF x251 to reg (r11)
clc;
adcx r8, [ rsp + 0x38 ]
mov r9, 0xffffffffffffffff ; moving imm to reg
mulx r13, r12, r9; x267, x266<- x260 * 0xffffffffffffffff
mov rdi, [ rsp + 0x28 ]; x325, copying x312 here, cause x312 is needed in a reg for other than x325, namely all: , x325--x326, size: 1
adcx rdi, rcx
mov rcx, 0x100000001 ; moving imm to reg
xchg rdx, rcx; 0x100000001, swapping with x260, which is currently in rdx
mov [ rsp + 0x2c0 ], rbx; spilling x222 to mem
mulx r9, rbx, r8; _, x337<- x323 * 0x100000001
mov r9, 0xffffffff00000000 ; moving imm to reg
xchg rdx, rbx; x337, swapping with 0x100000001, which is currently in rdx
mov [ rsp + 0x2c8 ], r13; spilling x267 to mem
mulx rbx, r13, r9; x348, x347<- x337 * 0xffffffff00000000
mov r9, 0xffffffff ; moving imm to reg
mov [ rsp + 0x2d0 ], rbx; spilling x348 to mem
mov byte [ rsp + 0x2d8 ], r11b; spilling byte x251 to mem
mulx rbx, r11, r9; x350, x349<- x337 * 0xffffffff
setc r9b; spill CF x326 to reg (r9)
clc;
adcx r13, rbx
setc bl; spill CF x352 to reg (rbx)
clc;
adcx r11, r8
xchg rdx, rbp; x3, swapping with x337, which is currently in rdx
mulx r11, r8, [ r10 + 0x20 ]; x226, x225<- x3 * arg2[4]
mov byte [ rsp + 0x2e0 ], bl; spilling byte x352 to mem
mov rbx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbx; 0xffffffffffffffff, swapping with x3, which is currently in rdx
mov byte [ rsp + 0x2e8 ], r9b; spilling byte x326 to mem
mov [ rsp + 0x2f0 ], r11; spilling x226 to mem
mulx r9, r11, rcx; x265, x264<- x260 * 0xffffffffffffffff
mov [ rsp + 0x2f8 ], r9; spilling x265 to mem
mov r9, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ r10 + 0x18 ]; saving arg2[3] in rdx.
mov [ rsp + 0x300 ], r11; spilling x264 to mem
mov [ rsp + 0x308 ], r8; spilling x225 to mem
mulx r11, r8, rbx; x228, x227<- x3 * arg2[3]
adcx r13, rdi
setc dil; spill CF x365 to reg (rdi)
clc;
mov r9, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, r9; loading flag
adcx r12, [ rsp + 0x2a0 ]
mov rdx, [ r10 + 0x28 ]; arg2[5] to rdx
mulx rbx, r15, rbx; x224, x223<- x3 * arg2[5]
setc r9b; spill CF x279 to reg (r9)
clc;
mov [ rsp + 0x310 ], r13; spilling x364 to mem
mov r13, -0x1 ; moving imm to reg
movzx r14, r14b
adcx r14, r13; loading flag
adcx r8, [ rsp + 0x2b8 ]
mov r14, 0xfffffffffffffffe ; moving imm to reg
mov rdx, r14; 0xfffffffffffffffe to rdx
mulx r14, r13, rbp; x346, x345<- x337 * 0xfffffffffffffffe
mov rdx, [ rsp + 0x308 ]; x241, copying x225 here, cause x225 is needed in a reg for other than x241, namely all: , x241--x242, size: 1
adcx rdx, r11
seto r11b; spill OF x290 to reg (r11)
mov byte [ rsp + 0x318 ], r9b; spilling byte x279 to mem
movzx r9, byte [ rsp + 0x2d8 ]; load byte memx251 to register64
mov [ rsp + 0x320 ], rdx; spilling x241 to mem
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
adox r9, rdx; loading flag
adox r8, [ rsp + 0x298 ]
setc r9b; spill CF x242 to reg (r9)
clc;
movzx r11, r11b
adcx r11, rdx; loading flag
adcx r8, r12
setc r11b; spill CF x292 to reg (r11)
clc;
movzx r9, r9b
adcx r9, rdx; loading flag
adcx r15, [ rsp + 0x2f0 ]
setc r12b; spill CF x244 to reg (r12)
movzx r9, byte [ rsp + 0x2e8 ]; load byte memx326 to register64
clc;
adcx r9, rdx; loading flag
adcx r8, [ rsp + 0x20 ]
mov r9, 0xffffffffffffffff ; moving imm to reg
mov rdx, r9; 0xffffffffffffffff to rdx
mov byte [ rsp + 0x328 ], r11b; spilling byte x292 to mem
mulx r9, r11, rbp; x344, x343<- x337 * 0xffffffffffffffff
setc dl; spill CF x328 to reg (rdx)
mov [ rsp + 0x330 ], r9; spilling x344 to mem
movzx r9, byte [ rsp + 0x2e0 ]; load byte memx352 to register64
clc;
mov [ rsp + 0x338 ], r15; spilling x243 to mem
mov r15, -0x1 ; moving imm to reg
adcx r9, r15; loading flag
adcx r13, [ rsp + 0x2d0 ]
movzx r9, r12b; x245, copying x244 here, cause x244 is needed in a reg for other than x245, namely all: , x245, size: 1
lea r9, [ r9 + rbx ]
mov rbx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbx; 0xffffffffffffffff, swapping with x328, which is currently in rdx
mulx rcx, r12, rcx; x263, x262<- x260 * 0xffffffffffffffff
adcx r11, r14
setc r14b; spill CF x356 to reg (r14)
clc;
movzx rdi, dil
adcx rdi, r15; loading flag
adcx r8, r13
mov rdi, [ rsp + 0x320 ]; load m64 x241 to register64
mov r13, [ rsp + 0x290 ]; x254, copying x218 here, cause x218 is needed in a reg for other than x254, namely all: , x254--x255, size: 1
adox r13, rdi
mov rdi, [ rsp + 0x338 ]; load m64 x243 to register64
mov r15, [ rsp + 0x288 ]; x256, copying x220 here, cause x220 is needed in a reg for other than x256, namely all: , x256--x257, size: 1
adox r15, rdi
mov rdi, [ rsp + 0x2c8 ]; load m64 x267 to register64
setc dl; spill CF x367 to reg (rdx)
mov [ rsp + 0x340 ], r8; spilling x366 to mem
movzx r8, byte [ rsp + 0x318 ]; load byte memx279 to register64
clc;
mov byte [ rsp + 0x348 ], r14b; spilling byte x356 to mem
mov r14, -0x1 ; moving imm to reg
adcx r8, r14; loading flag
adcx rdi, [ rsp + 0x300 ]
mov r8, [ rsp + 0x2f8 ]; x282, copying x265 here, cause x265 is needed in a reg for other than x282, namely all: , x282--x283, size: 1
adcx r8, r12
mov r12, 0x0 ; moving imm to reg
adcx rcx, r12
mov r12, [ rsp + 0x2c0 ]; x258, copying x222 here, cause x222 is needed in a reg for other than x258, namely all: , x258--x259, size: 1
adox r12, r9
movzx r9, byte [ rsp + 0x328 ]; load byte memx292 to register64
clc;
adcx r9, r14; loading flag
adcx r13, rdi
seto r9b; spill OF x259 to reg (r9)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdi, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, rdi; loading flag
adox r13, [ rsp + 0x18 ]
adcx r8, r15
adcx rcx, r12
movzx rbx, r9b; x299, copying x259 here, cause x259 is needed in a reg for other than x299, namely all: , x299, size: 1
adcx rbx, r14
mov r15, [ rsp + 0x8 ]; x331, copying x318 here, cause x318 is needed in a reg for other than x331, namely all: , x331--x332, size: 1
adox r15, r8
mov r9, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbp; x337, swapping with x367, which is currently in rdx
mulx r12, r8, r9; x340, x339<- x337 * 0xffffffffffffffff
mov r14, [ rsp + 0x10 ]; x333, copying x320 here, cause x320 is needed in a reg for other than x333, namely all: , x333--x334, size: 1
adox r14, rcx
clc;
movzx rbp, bpl
adcx rbp, rdi; loading flag
adcx r13, r11
mulx rdx, r11, r9; x342, x341<- x337 * 0xffffffffffffffff
setc bpl; spill CF x369 to reg (rbp)
movzx rcx, byte [ rsp + 0x348 ]; load byte memx356 to register64
clc;
adcx rcx, rdi; loading flag
adcx r11, [ rsp + 0x330 ]
mov rcx, [ rsp + 0x30 ]; x335, copying x322 here, cause x322 is needed in a reg for other than x335, namely all: , x335--x336, size: 1
adox rcx, rbx
mov rbx, [ rax + 0x28 ]; load m64 x5 to register64
adcx r8, rdx
setc dl; spill CF x360 to reg (rdx)
clc;
movzx rbp, bpl
adcx rbp, rdi; loading flag
adcx r15, r11
movzx rbp, dl; x361, copying x360 here, cause x360 is needed in a reg for other than x361, namely all: , x361, size: 1
lea rbp, [ rbp + r12 ]
adcx r8, r14
mov rdx, [ r10 + 0x0 ]; arg2[0] to rdx
mulx r12, r14, rbx; x388, x387<- x5 * arg2[0]
mov rdx, [ r10 + 0x8 ]; arg2[1] to rdx
mulx r11, rdi, rbx; x386, x385<- x5 * arg2[1]
seto r9b; spill OF x336 to reg (r9)
mov [ rsp + 0x350 ], r8; spilling x372 to mem
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, [ rsp + 0x310 ]
adcx rbp, rcx
mov rdx, rbx; x5 to rdx
mulx rbx, rcx, [ r10 + 0x20 ]; x380, x379<- x5 * arg2[4]
mov [ rsp + 0x358 ], rbp; spilling x374 to mem
mulx r8, rbp, [ r10 + 0x10 ]; x384, x383<- x5 * arg2[2]
mov [ rsp + 0x360 ], rbx; spilling x380 to mem
movzx rbx, r9b; x376, copying x336 here, cause x336 is needed in a reg for other than x376, namely all: , x376, size: 1
mov [ rsp + 0x368 ], rcx; spilling x379 to mem
mov rcx, 0x0 ; moving imm to reg
adcx rbx, rcx
mov r9, 0x100000001 ; moving imm to reg
xchg rdx, r14; x400, swapping with x5, which is currently in rdx
mov [ rsp + 0x370 ], rbx; spilling x376 to mem
mulx rcx, rbx, r9; _, x414<- x400 * 0x100000001
clc;
adcx rdi, r12
mov rcx, 0xffffffff00000000 ; moving imm to reg
xchg rdx, rcx; 0xffffffff00000000, swapping with x400, which is currently in rdx
mulx r12, r9, rbx; x425, x424<- x414 * 0xffffffff00000000
mov rdx, 0xffffffff ; moving imm to reg
mov [ rsp + 0x378 ], r15; spilling x370 to mem
mov [ rsp + 0x380 ], r13; spilling x368 to mem
mulx r15, r13, rbx; x427, x426<- x414 * 0xffffffff
mov rdx, [ rsp + 0x340 ]; x402, copying x366 here, cause x366 is needed in a reg for other than x402, namely all: , x402--x403, size: 1
adox rdx, rdi
adcx rbp, r11
seto r11b; spill OF x403 to reg (r11)
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r9, r15
xchg rdx, r14; x5, swapping with x402, which is currently in rdx
mulx r15, rdi, [ r10 + 0x18 ]; x382, x381<- x5 * arg2[3]
mov [ rsp + 0x388 ], r15; spilling x382 to mem
mov r15, 0xfffffffffffffffe ; moving imm to reg
xchg rdx, rbx; x414, swapping with x5, which is currently in rdx
mov [ rsp + 0x390 ], rbp; spilling x391 to mem
mov byte [ rsp + 0x398 ], r11b; spilling byte x403 to mem
mulx rbp, r11, r15; x423, x422<- x414 * 0xfffffffffffffffe
adcx rdi, r8
mov r8, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x3a0 ], rdi; spilling x393 to mem
mulx r15, rdi, r8; x421, x420<- x414 * 0xffffffffffffffff
adox r11, r12
adox rdi, rbp
seto r12b; spill OF x433 to reg (r12)
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, rcx
adox r9, r14
mov r13, [ rsp + 0x390 ]; load m64 x391 to register64
setc cl; spill CF x394 to reg (rcx)
movzx r14, byte [ rsp + 0x398 ]; load byte memx403 to register64
clc;
adcx r14, rbp; loading flag
adcx r13, [ rsp + 0x380 ]
mov r14, [ rsp + 0x3a0 ]; load m64 x393 to register64
mov rbp, [ rsp + 0x378 ]; x406, copying x370 here, cause x370 is needed in a reg for other than x406, namely all: , x406--x407, size: 1
adcx rbp, r14
adox r11, r13
mulx r14, r13, r8; x419, x418<- x414 * 0xffffffffffffffff
mov byte [ rsp + 0x3a8 ], cl; spilling byte x394 to mem
mulx rdx, rcx, r8; x417, x416<- x414 * 0xffffffffffffffff
adox rdi, rbp
setc bpl; spill CF x407 to reg (rbp)
seto r8b; spill OF x446 to reg (r8)
mov [ rsp + 0x3b0 ], rdx; spilling x417 to mem
mov rdx, r9; x454, copying x441 here, cause x441 is needed in a reg for other than x454, namely all: , x454--x455, x468, size: 2
mov [ rsp + 0x3b8 ], rdi; spilling x445 to mem
mov rdi, 0xffffffff ; moving imm to reg
sub rdx, rdi
mov rdi, 0x0 ; moving imm to reg
dec rdi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r12, r12b
adox r12, rdi; loading flag
adox r15, r13
seto r12b; spill OF x435 to reg (r12)
mov r13, r11; x456, copying x443 here, cause x443 is needed in a reg for other than x456, namely all: , x456--x457, x469, size: 2
mov rdi, 0xffffffff00000000 ; moving imm to reg
sbb r13, rdi
mov rdi, 0x0 ; moving imm to reg
dec rdi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r12, r12b
adox r12, rdi; loading flag
adox r14, rcx
seto cl; spill OF x437 to reg (rcx)
mov r12, [ rsp + 0x3b8 ]; x458, copying x445 here, cause x445 is needed in a reg for other than x458, namely all: , x470, x458--x459, size: 2
mov rdi, 0xfffffffffffffffe ; moving imm to reg
sbb r12, rdi
mov rdi, [ rsp + 0x368 ]; load m64 x379 to register64
mov [ rsp + 0x3c0 ], r13; spilling x456 to mem
movzx r13, byte [ rsp + 0x3a8 ]; load byte memx394 to register64
mov [ rsp + 0x3c8 ], r12; spilling x458 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r13, r12; loading flag
adox rdi, [ rsp + 0x388 ]
setc r13b; spill CF x459 to reg (r13)
clc;
movzx rbp, bpl
adcx rbp, r12; loading flag
adcx rdi, [ rsp + 0x350 ]
xchg rdx, rbx; x5, swapping with x454, which is currently in rdx
mulx rdx, rbp, [ r10 + 0x28 ]; x378, x377<- x5 * arg2[5]
movzx r12, cl; x438, copying x437 here, cause x437 is needed in a reg for other than x438, namely all: , x438, size: 1
mov [ rsp + 0x3d0 ], rbx; spilling x454 to mem
mov rbx, [ rsp + 0x3b0 ]; load m64 x417 to register64
lea r12, [ r12 + rbx ]; r8/64 + m8
mov rbx, [ rsp + 0x360 ]; x397, copying x380 here, cause x380 is needed in a reg for other than x397, namely all: , x397--x398, size: 1
adox rbx, rbp
mov rcx, [ rsp + 0x358 ]; x410, copying x374 here, cause x374 is needed in a reg for other than x410, namely all: , x410--x411, size: 1
adcx rcx, rbx
setc bpl; spill CF x411 to reg (rbp)
clc;
mov rbx, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, rbx; loading flag
adcx rdi, r15
mov r8, 0x0 ; moving imm to reg
adox rdx, r8
dec r8; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx rbp, bpl
adox rbp, r8; loading flag
adox rdx, [ rsp + 0x370 ]
adcx r14, rcx
adcx r12, rdx
setc bl; spill CF x452 to reg (rbx)
seto r15b; spill OF x413 to reg (r15)
movzx rbp, r13b; x459, copying x459 here, cause x459 is needed in a reg for other than x459, namely all: , x460--x461, size: 1
add rbp, -0x1
mov rbp, rdi; x460, copying x447 here, cause x447 is needed in a reg for other than x460, namely all: , x471, x460--x461, size: 2
mov r13, 0xffffffffffffffff ; moving imm to reg
sbb rbp, r13
mov rcx, r14; x462, copying x449 here, cause x449 is needed in a reg for other than x462, namely all: , x462--x463, x472, size: 2
sbb rcx, r13
mov rdx, r12; x464, copying x451 here, cause x451 is needed in a reg for other than x464, namely all: , x464--x465, x473, size: 2
sbb rdx, r13
movzx r8, bl; x453, copying x452 here, cause x452 is needed in a reg for other than x453, namely all: , x453, size: 1
movzx r15, r15b
lea r8, [ r8 + r15 ]
sbb r8, 0x00000000
cmovc rbp, rdi; if CF, x471<- x447 (nzVar)
mov r8, [ rsp + 0x3d0 ]; x468, copying x454 here, cause x454 is needed in a reg for other than x468, namely all: , x468, size: 1
cmovc r8, r9; if CF, x468<- x441 (nzVar)
cmovc rcx, r14; if CF, x472<- x449 (nzVar)
cmovc rdx, r12; if CF, x473<- x451 (nzVar)
mov r9, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r9 + 0x20 ], rcx; out1[4] = x472
mov [ r9 + 0x0 ], r8; out1[0] = x468
mov rdi, [ rsp + 0x3c8 ]; x470, copying x458 here, cause x458 is needed in a reg for other than x470, namely all: , x470, size: 1
cmovc rdi, [ rsp + 0x3b8 ]; if CF, x470<- x445 (nzVar)
mov [ r9 + 0x28 ], rdx; out1[5] = x473
mov [ r9 + 0x18 ], rbp; out1[3] = x471
mov [ r9 + 0x10 ], rdi; out1[2] = x470
mov r15, [ rsp + 0x3c0 ]; x469, copying x456 here, cause x456 is needed in a reg for other than x469, namely all: , x469, size: 1
cmovc r15, r11; if CF, x469<- x443 (nzVar)
mov [ r9 + 0x8 ], r15; out1[1] = x469
mov rbx, [ rsp + 0x3d8 ]; restoring from stack
mov rbp, [ rsp + 0x3e0 ]; restoring from stack
mov r12, [ rsp + 0x3e8 ]; restoring from stack
mov r13, [ rsp + 0x3f0 ]; restoring from stack
mov r14, [ rsp + 0x3f8 ]; restoring from stack
mov r15, [ rsp + 0x400 ]; restoring from stack
add rsp, 0x408 
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; clocked at 3600 MHz
; first cyclecount 235.775, best 208.5185185185185, lastGood 214.92592592592592
; seed 1525563746357639 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2987766 ms / 60000 runs=> 49.7961ms/run
; Time spent for assembling and measureing (initial batch_size=53, initial num_batches=101): 115010 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.0384936437458623
; number reverted permutation/ tried permutation: 19511 / 29951 =65.143%
; number reverted decision/ tried decision: 18654 / 30050 =62.077%