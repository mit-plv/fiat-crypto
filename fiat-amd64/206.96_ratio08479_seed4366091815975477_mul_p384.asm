SECTION .text
	GLOBAL mul_p384
mul_p384:
sub rsp, 0x3a8 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x378 ], rbx; saving to stack
mov [ rsp + 0x380 ], rbp; saving to stack
mov [ rsp + 0x388 ], r12; saving to stack
mov [ rsp + 0x390 ], r13; saving to stack
mov [ rsp + 0x398 ], r14; saving to stack
mov [ rsp + 0x3a0 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x6 to register64
mov r10, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x0 ]; saving arg2[0] in rdx.
mulx r11, rbx, rax; x18, x17<- x6 * arg2[0]
mov rbp, 0x100000001 ; moving imm to reg
mov rdx, rbx; x17 to rdx
mulx rbx, r12, rbp; _, x30<- x17 * 0x100000001
mov rbx, rdx; preserving value of x17 into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mulx r13, r14, rax; x16, x15<- x6 * arg2[1]
xor r15, r15
adox r14, r11
mov rcx, 0xffffffff ; moving imm to reg
mov rdx, rcx; 0xffffffff to rdx
mulx rcx, r8, r12; x43, x42<- x30 * 0xffffffff
mov r9, 0xffffffff00000000 ; moving imm to reg
xchg rdx, r12; x30, swapping with 0xffffffff, which is currently in rdx
mulx r11, r15, r9; x41, x40<- x30 * 0xffffffff00000000
adcx r15, rcx
mov rcx, [ rsi + 0x8 ]; load m64 x1 to register64
xchg rdx, rcx; x1, swapping with x30, which is currently in rdx
mulx rbp, r9, [ r10 + 0x0 ]; x80, x79<- x1 * arg2[0]
seto r12b; spill OF x20 to reg (r12)
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, rbx
adox r15, r14
setc r8b; spill CF x45 to reg (r8)
clc;
adcx r9, r15
mov rbx, 0x100000001 ; moving imm to reg
xchg rdx, r9; x92, swapping with x1, which is currently in rdx
mulx r14, r15, rbx; _, x106<- x92 * 0x100000001
xchg rdx, rax; x6, swapping with x92, which is currently in rdx
mulx r14, rdi, [ r10 + 0x10 ]; x14, x13<- x6 * arg2[2]
mov rbx, rdx; preserving value of x6 into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mov [ rsp + 0x8 ], r14; spilling x14 to mem
mov [ rsp + 0x10 ], rbp; spilling x80 to mem
mulx r14, rbp, r9; x78, x77<- x1 * arg2[1]
mov [ rsp + 0x18 ], r14; spilling x78 to mem
mov r14, 0xffffffff ; moving imm to reg
mov rdx, r14; 0xffffffff to rdx
mov [ rsp + 0x20 ], rbp; spilling x77 to mem
mulx r14, rbp, r15; x119, x118<- x106 * 0xffffffff
setc dl; spill CF x93 to reg (rdx)
clc;
adcx rbp, rax
mov rbp, 0xfffffffffffffffe ; moving imm to reg
xchg rdx, rcx; x30, swapping with x93, which is currently in rdx
mov [ rsp + 0x28 ], r14; spilling x119 to mem
mulx rax, r14, rbp; x39, x38<- x30 * 0xfffffffffffffffe
seto bpl; spill OF x58 to reg (rbp)
mov byte [ rsp + 0x30 ], cl; spilling byte x93 to mem
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r12, r12b
adox r12, rcx; loading flag
adox r13, rdi
setc r12b; spill CF x132 to reg (r12)
clc;
movzx r8, r8b
adcx r8, rcx; loading flag
adcx r11, r14
setc r8b; spill CF x47 to reg (r8)
clc;
movzx rbp, bpl
adcx rbp, rcx; loading flag
adcx r13, r11
mov rbp, 0xffffffffffffffff ; moving imm to reg
mulx rdi, r14, rbp; x37, x36<- x30 * 0xffffffffffffffff
mov r11, [ rsp + 0x10 ]; load m64 x80 to register64
setc cl; spill CF x60 to reg (rcx)
clc;
adcx r11, [ rsp + 0x20 ]
mov [ rsp + 0x38 ], rsi; spilling arg1 to mem
mov byte [ rsp + 0x40 ], r12b; spilling byte x132 to mem
mulx rsi, r12, rbp; x35, x34<- x30 * 0xffffffffffffffff
mov rbp, rdx; preserving value of x30 into a new reg
mov rdx, [ r10 + 0x18 ]; saving arg2[3] in rdx.
mov [ rsp + 0x48 ], rsi; spilling x35 to mem
mov byte [ rsp + 0x50 ], cl; spilling byte x60 to mem
mulx rsi, rcx, rbx; x12, x11<- x6 * arg2[3]
mov rdx, r9; x1 to rdx
mov [ rsp + 0x58 ], rsi; spilling x12 to mem
mulx r9, rsi, [ r10 + 0x10 ]; x76, x75<- x1 * arg2[2]
mov [ rsp + 0x60 ], r9; spilling x76 to mem
mov r9, [ rsp + 0x18 ]; x83, copying x78 here, cause x78 is needed in a reg for other than x83, namely all: , x83--x84, size: 1
adcx r9, rsi
mov rsi, [ rsp + 0x8 ]; x23, copying x14 here, cause x14 is needed in a reg for other than x23, namely all: , x23--x24, size: 1
adox rsi, rcx
seto cl; spill OF x24 to reg (rcx)
mov [ rsp + 0x68 ], r9; spilling x83 to mem
mov r9, -0x1 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r9, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, r9; loading flag
adox rax, r14
mov r8, rdx; preserving value of x1 into a new reg
mov rdx, [ r10 + 0x20 ]; saving arg2[4] in rdx.
mulx r14, r9, rbx; x10, x9<- x6 * arg2[4]
mov [ rsp + 0x70 ], r14; spilling x10 to mem
setc r14b; spill CF x84 to reg (r14)
mov [ rsp + 0x78 ], rax; spilling x48 to mem
movzx rax, byte [ rsp + 0x30 ]; load byte memx93 to register64
clc;
mov [ rsp + 0x80 ], rsi; spilling x23 to mem
mov rsi, -0x1 ; moving imm to reg
adcx rax, rsi; loading flag
adcx r13, r11
adox r12, rdi
mov rax, 0xffffffff00000000 ; moving imm to reg
mov rdx, r15; x106 to rdx
mulx r15, rdi, rax; x117, x116<- x106 * 0xffffffff00000000
setc r11b; spill CF x95 to reg (r11)
clc;
movzx rcx, cl
adcx rcx, rsi; loading flag
adcx r9, [ rsp + 0x58 ]
setc cl; spill CF x26 to reg (rcx)
clc;
adcx rdi, [ rsp + 0x28 ]
mov rsi, 0xfffffffffffffffe ; moving imm to reg
mov byte [ rsp + 0x88 ], cl; spilling byte x26 to mem
mulx rax, rcx, rsi; x115, x114<- x106 * 0xfffffffffffffffe
mov rsi, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x90 ], rax; spilling x115 to mem
mov byte [ rsp + 0x98 ], r14b; spilling byte x84 to mem
mulx rax, r14, rsi; x113, x112<- x106 * 0xffffffffffffffff
adcx rcx, r15
mov r15, [ rsp + 0x78 ]; load m64 x48 to register64
setc sil; spill CF x123 to reg (rsi)
mov [ rsp + 0xa0 ], rax; spilling x113 to mem
movzx rax, byte [ rsp + 0x50 ]; load byte memx60 to register64
clc;
mov [ rsp + 0xa8 ], r14; spilling x112 to mem
mov r14, -0x1 ; moving imm to reg
adcx rax, r14; loading flag
adcx r15, [ rsp + 0x80 ]
adcx r12, r9
mov rax, rdx; preserving value of x106 into a new reg
mov rdx, [ r10 + 0x18 ]; saving arg2[3] in rdx.
mulx r9, r14, r8; x74, x73<- x1 * arg2[3]
mov [ rsp + 0xb0 ], r12; spilling x63 to mem
setc r12b; spill CF x64 to reg (r12)
mov [ rsp + 0xb8 ], r9; spilling x74 to mem
movzx r9, byte [ rsp + 0x40 ]; load byte memx132 to register64
clc;
mov byte [ rsp + 0xc0 ], sil; spilling byte x123 to mem
mov rsi, -0x1 ; moving imm to reg
adcx r9, rsi; loading flag
adcx r13, rdi
seto r9b; spill OF x51 to reg (r9)
inc rsi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdi, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, rdi; loading flag
adox r15, [ rsp + 0x68 ]
mov r11, 0xffffffffffffffff ; moving imm to reg
mov rdx, r11; 0xffffffffffffffff to rdx
mulx rbp, r11, rbp; x33, x32<- x30 * 0xffffffffffffffff
adcx rcx, r15
seto r15b; spill OF x97 to reg (r15)
movzx rsi, byte [ rsp + 0x98 ]; load byte memx84 to register64
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdi, -0x1 ; moving imm to reg
adox rsi, rdi; loading flag
adox r14, [ rsp + 0x60 ]
mov rsi, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ r10 + 0x20 ]; saving arg2[4] in rdx.
mov [ rsp + 0xc8 ], rcx; spilling x135 to mem
mulx rdi, rcx, r8; x72, x71<- x1 * arg2[4]
mov rdx, rax; x106 to rdx
mov [ rsp + 0xd0 ], r13; spilling x133 to mem
mulx rax, r13, rsi; x111, x110<- x106 * 0xffffffffffffffff
mov rsi, [ rsp + 0xa8 ]; load m64 x112 to register64
mov [ rsp + 0xd8 ], rdi; spilling x72 to mem
setc dil; spill CF x136 to reg (rdi)
mov [ rsp + 0xe0 ], rax; spilling x111 to mem
movzx rax, byte [ rsp + 0xc0 ]; load byte memx123 to register64
clc;
mov [ rsp + 0xe8 ], rbp; spilling x33 to mem
mov rbp, -0x1 ; moving imm to reg
adcx rax, rbp; loading flag
adcx rsi, [ rsp + 0x90 ]
mov rax, [ rsp + 0xb8 ]; x87, copying x74 here, cause x74 is needed in a reg for other than x87, namely all: , x87--x88, size: 1
adox rax, rcx
mov rcx, [ rsp + 0xa0 ]; x126, copying x113 here, cause x113 is needed in a reg for other than x126, namely all: , x126--x127, size: 1
adcx rcx, r13
seto r13b; spill OF x88 to reg (r13)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, rbp; loading flag
adox r11, [ rsp + 0x48 ]
seto r9b; spill OF x53 to reg (r9)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, rbp; loading flag
adox r14, [ rsp + 0xb0 ]
xchg rdx, rbx; x6, swapping with x106, which is currently in rdx
mulx rdx, r15, [ r10 + 0x28 ]; x8, x7<- x6 * arg2[5]
setc bpl; spill CF x127 to reg (rbp)
clc;
mov byte [ rsp + 0xf0 ], r13b; spilling byte x88 to mem
mov r13, -0x1 ; moving imm to reg
movzx rdi, dil
adcx rdi, r13; loading flag
adcx r14, rsi
setc dil; spill CF x138 to reg (rdi)
movzx rsi, byte [ rsp + 0x88 ]; load byte memx26 to register64
clc;
adcx rsi, r13; loading flag
adcx r15, [ rsp + 0x70 ]
setc sil; spill CF x28 to reg (rsi)
clc;
movzx r12, r12b
adcx r12, r13; loading flag
adcx r15, r11
mov r12, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbx; x106, swapping with x8, which is currently in rdx
mulx rdx, r11, r12; x109, x108<- x106 * 0xffffffffffffffff
adox rax, r15
movzx r15, r9b; x54, copying x53 here, cause x53 is needed in a reg for other than x54, namely all: , x54, size: 1
mov r13, [ rsp + 0xe8 ]; load m64 x33 to register64
lea r15, [ r15 + r13 ]; r8/64 + m8
movzx r13, sil; x29, copying x28 here, cause x28 is needed in a reg for other than x29, namely all: , x29, size: 1
lea r13, [ r13 + rbx ]
setc r9b; spill CF x66 to reg (r9)
clc;
mov rbx, -0x1 ; moving imm to reg
movzx rbp, bpl
adcx rbp, rbx; loading flag
adcx r11, [ rsp + 0xe0 ]
mov rbp, rdx; preserving value of x109 into a new reg
mov rdx, [ r10 + 0x28 ]; saving arg2[5] in rdx.
mulx r8, rsi, r8; x70, x69<- x1 * arg2[5]
seto bl; spill OF x101 to reg (rbx)
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
movzx rdi, dil
adox rdi, r12; loading flag
adox rax, rcx
setc cl; spill CF x129 to reg (rcx)
clc;
movzx r9, r9b
adcx r9, r12; loading flag
adcx r13, r15
seto dil; spill OF x140 to reg (rdi)
movzx r9, byte [ rsp + 0xf0 ]; load byte memx88 to register64
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
adox r9, r15; loading flag
adox rsi, [ rsp + 0xd8 ]
adox r8, r12
mov r9, [ rsp + 0x38 ]; load m64 arg1 to register64
mov r12, [ r9 + 0x10 ]; load m64 x2 to register64
mov rdx, r12; x2 to rdx
mulx r12, r15, [ r10 + 0x0 ]; x157, x156<- x2 * arg2[0]
mov [ rsp + 0xf8 ], rax; spilling x139 to mem
mov rax, 0x0 ; moving imm to reg
dec rax; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbx, bl
adox rbx, rax; loading flag
adox r13, rsi
setc bl; spill CF x68 to reg (rbx)
clc;
movzx rdi, dil
adcx rdi, rax; loading flag
adcx r13, r11
seto r11b; spill OF x103 to reg (r11)
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r15, [ rsp + 0xd0 ]
mov rdi, [ r9 + 0x18 ]; load m64 x3 to register64
seto sil; spill OF x170 to reg (rsi)
dec rax; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx rbx, bl
movzx r11, r11b
adox r11, rax; loading flag
adox r8, rbx
mulx rbx, r11, [ r10 + 0x8 ]; x155, x154<- x2 * arg2[1]
mov rax, 0x100000001 ; moving imm to reg
xchg rdx, r15; x169, swapping with x2, which is currently in rdx
mov [ rsp + 0x100 ], r13; spilling x141 to mem
mov [ rsp + 0x108 ], r14; spilling x137 to mem
mulx r13, r14, rax; _, x183<- x169 * 0x100000001
movzx r13, cl; x130, copying x129 here, cause x129 is needed in a reg for other than x130, namely all: , x130, size: 1
lea r13, [ r13 + rbp ]
mov rbp, 0xffffffff ; moving imm to reg
xchg rdx, rbp; 0xffffffff, swapping with x169, which is currently in rdx
mulx rcx, rax, r14; x196, x195<- x183 * 0xffffffff
adcx r13, r8
mov r8, rdx; preserving value of 0xffffffff into a new reg
mov rdx, [ r10 + 0x18 ]; saving arg2[3] in rdx.
mov [ rsp + 0x110 ], r13; spilling x143 to mem
mov [ rsp + 0x118 ], rbx; spilling x155 to mem
mulx r13, rbx, r15; x151, x150<- x2 * arg2[3]
mov r8, 0xffffffff00000000 ; moving imm to reg
mov rdx, r8; 0xffffffff00000000 to rdx
mov [ rsp + 0x120 ], r13; spilling x151 to mem
mulx r8, r13, r14; x194, x193<- x183 * 0xffffffff00000000
seto dl; spill OF x145 to reg (rdx)
adc dl, 0x0
movzx rdx, dl
adox rax, rbp
adcx r13, rcx
setc al; spill CF x198 to reg (rax)
clc;
adcx r11, r12
setc r12b; spill CF x159 to reg (r12)
clc;
mov rbp, -0x1 ; moving imm to reg
movzx rsi, sil
adcx rsi, rbp; loading flag
adcx r11, [ rsp + 0xc8 ]
xchg rdx, rdi; x3, swapping with x145, which is currently in rdx
mulx rsi, rcx, [ r10 + 0x0 ]; x234, x233<- x3 * arg2[0]
adox r13, r11
setc r11b; spill CF x172 to reg (r11)
clc;
adcx rcx, r13
mov r13, 0x100000001 ; moving imm to reg
xchg rdx, rcx; x246, swapping with x3, which is currently in rdx
mov byte [ rsp + 0x128 ], dil; spilling byte x145 to mem
mulx rbp, rdi, r13; _, x260<- x246 * 0x100000001
mov rbp, rdx; preserving value of x246 into a new reg
mov rdx, [ r10 + 0x10 ]; saving arg2[2] in rdx.
mov [ rsp + 0x130 ], rsi; spilling x234 to mem
mulx r13, rsi, r15; x153, x152<- x2 * arg2[2]
mov [ rsp + 0x138 ], rdi; spilling x260 to mem
seto dil; spill OF x211 to reg (rdi)
mov byte [ rsp + 0x140 ], r11b; spilling byte x172 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, r11; loading flag
adox rsi, [ rsp + 0x118 ]
mov r12, 0xffffffffffffffff ; moving imm to reg
mov rdx, r14; x183 to rdx
mulx r14, r11, r12; x190, x189<- x183 * 0xffffffffffffffff
adox rbx, r13
mov r13, rdx; preserving value of x183 into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mov [ rsp + 0x148 ], r14; spilling x190 to mem
mulx r12, r14, rcx; x232, x231<- x3 * arg2[1]
mov [ rsp + 0x150 ], r12; spilling x232 to mem
mov r12, 0xfffffffffffffffe ; moving imm to reg
mov rdx, r12; 0xfffffffffffffffe to rdx
mov [ rsp + 0x158 ], r11; spilling x189 to mem
mulx r12, r11, r13; x192, x191<- x183 * 0xfffffffffffffffe
seto dl; spill OF x163 to reg (rdx)
mov [ rsp + 0x160 ], r12; spilling x192 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rax, al
adox rax, r12; loading flag
adox r8, r11
setc al; spill CF x247 to reg (rax)
movzx r11, byte [ rsp + 0x140 ]; load byte memx172 to register64
clc;
adcx r11, r12; loading flag
adcx rsi, [ rsp + 0x108 ]
mov r11, [ rsp + 0xf8 ]; x175, copying x139 here, cause x139 is needed in a reg for other than x175, namely all: , x175--x176, size: 1
adcx r11, rbx
xchg rdx, r15; x2, swapping with x163, which is currently in rdx
mulx rbx, r12, [ r10 + 0x20 ]; x149, x148<- x2 * arg2[4]
mov [ rsp + 0x168 ], rbx; spilling x149 to mem
mov rbx, 0xffffffff ; moving imm to reg
mov [ rsp + 0x170 ], r11; spilling x175 to mem
mov r11, rdx; preserving value of x2 into a new reg
mov rdx, [ rsp + 0x138 ]; saving x260 in rdx.
mov [ rsp + 0x178 ], r12; spilling x148 to mem
mov byte [ rsp + 0x180 ], r15b; spilling byte x163 to mem
mulx r12, r15, rbx; x273, x272<- x260 * 0xffffffff
setc bl; spill CF x176 to reg (rbx)
clc;
adcx r15, rbp
seto r15b; spill OF x200 to reg (r15)
mov rbp, 0x0 ; moving imm to reg
dec rbp; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rdi, dil
adox rdi, rbp; loading flag
adox rsi, r8
seto dil; spill OF x213 to reg (rdi)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r14, [ rsp + 0x130 ]
seto r8b; spill OF x236 to reg (r8)
dec rbp; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx rax, al
adox rax, rbp; loading flag
adox rsi, r14
xchg rdx, rcx; x3, swapping with x260, which is currently in rdx
mulx rax, r14, [ r10 + 0x10 ]; x230, x229<- x3 * arg2[2]
mov rbp, 0xffffffff00000000 ; moving imm to reg
xchg rdx, rcx; x260, swapping with x3, which is currently in rdx
mov [ rsp + 0x188 ], rax; spilling x230 to mem
mov byte [ rsp + 0x190 ], dil; spilling byte x213 to mem
mulx rax, rdi, rbp; x271, x270<- x260 * 0xffffffff00000000
seto bpl; spill OF x249 to reg (rbp)
mov [ rsp + 0x198 ], r14; spilling x229 to mem
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rdi, r12
mov r12, 0xfffffffffffffffe ; moving imm to reg
mov byte [ rsp + 0x1a0 ], bpl; spilling byte x249 to mem
mulx r14, rbp, r12; x269, x268<- x260 * 0xfffffffffffffffe
mov r12, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r13; x183, swapping with x260, which is currently in rdx
mov [ rsp + 0x1a8 ], r14; spilling x269 to mem
mov byte [ rsp + 0x1b0 ], r8b; spilling byte x236 to mem
mulx r14, r8, r12; x188, x187<- x183 * 0xffffffffffffffff
adox rbp, rax
adcx rdi, rsi
mov rsi, [ rsp + 0x120 ]; load m64 x151 to register64
setc al; spill CF x288 to reg (rax)
movzx r12, byte [ rsp + 0x180 ]; load byte memx163 to register64
clc;
mov [ rsp + 0x1b8 ], rdi; spilling x287 to mem
mov rdi, -0x1 ; moving imm to reg
adcx r12, rdi; loading flag
adcx rsi, [ rsp + 0x178 ]
mov r12, [ rsp + 0x158 ]; load m64 x189 to register64
seto dil; spill OF x277 to reg (rdi)
mov [ rsp + 0x1c0 ], r14; spilling x188 to mem
mov r14, -0x1 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r14, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, r14; loading flag
adox r12, [ rsp + 0x160 ]
seto r15b; spill OF x202 to reg (r15)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, r14; loading flag
adox rsi, [ rsp + 0x100 ]
mov rbx, [ rsp + 0x150 ]; load m64 x232 to register64
seto r14b; spill OF x178 to reg (r14)
mov byte [ rsp + 0x1c8 ], dil; spilling byte x277 to mem
movzx rdi, byte [ rsp + 0x1b0 ]; load byte memx236 to register64
mov [ rsp + 0x1d0 ], rbp; spilling x276 to mem
mov rbp, -0x1 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
adox rdi, rbp; loading flag
adox rbx, [ rsp + 0x198 ]
seto dil; spill OF x238 to reg (rdi)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, rbp; loading flag
adox r8, [ rsp + 0x148 ]
setc r15b; spill CF x165 to reg (r15)
movzx rbp, byte [ rsp + 0x190 ]; load byte memx213 to register64
clc;
mov byte [ rsp + 0x1d8 ], r14b; spilling byte x178 to mem
mov r14, -0x1 ; moving imm to reg
adcx rbp, r14; loading flag
adcx r12, [ rsp + 0x170 ]
adcx r8, rsi
mov rbp, rdx; preserving value of x183 into a new reg
mov rdx, [ r10 + 0x18 ]; saving arg2[3] in rdx.
mulx rsi, r14, rcx; x228, x227<- x3 * arg2[3]
mov [ rsp + 0x1e0 ], rsi; spilling x228 to mem
setc sil; spill CF x217 to reg (rsi)
mov [ rsp + 0x1e8 ], r8; spilling x216 to mem
movzx r8, byte [ rsp + 0x1a0 ]; load byte memx249 to register64
clc;
mov byte [ rsp + 0x1f0 ], r15b; spilling byte x165 to mem
mov r15, -0x1 ; moving imm to reg
adcx r8, r15; loading flag
adcx r12, rbx
mov rdx, [ r10 + 0x28 ]; arg2[5] to rdx
mulx r11, r8, r11; x147, x146<- x2 * arg2[5]
seto bl; spill OF x204 to reg (rbx)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
movzx rax, al
adox rax, r15; loading flag
adox r12, [ rsp + 0x1d0 ]
seto al; spill OF x290 to reg (rax)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
movzx rdi, dil
adox rdi, r15; loading flag
adox r14, [ rsp + 0x188 ]
mov rdi, 0xffffffffffffffff ; moving imm to reg
mov rdx, r13; x260 to rdx
mulx r13, r15, rdi; x267, x266<- x260 * 0xffffffffffffffff
mov [ rsp + 0x1f8 ], r12; spilling x289 to mem
mov byte [ rsp + 0x200 ], sil; spilling byte x217 to mem
mulx r12, rsi, rdi; x265, x264<- x260 * 0xffffffffffffffff
xchg rdx, rbp; x183, swapping with x260, which is currently in rdx
mov [ rsp + 0x208 ], r12; spilling x265 to mem
mulx rdx, r12, rdi; x186, x185<- x183 * 0xffffffffffffffff
setc dil; spill CF x251 to reg (rdi)
clc;
mov [ rsp + 0x210 ], rdx; spilling x186 to mem
mov rdx, -0x1 ; moving imm to reg
movzx rbx, bl
adcx rbx, rdx; loading flag
adcx r12, [ rsp + 0x1c0 ]
setc bl; spill CF x206 to reg (rbx)
movzx rdx, byte [ rsp + 0x1f0 ]; load byte memx165 to register64
clc;
mov [ rsp + 0x218 ], r12; spilling x205 to mem
mov r12, -0x1 ; moving imm to reg
adcx rdx, r12; loading flag
adcx r8, [ rsp + 0x168 ]
mov rdx, 0x0 ; moving imm to reg
adcx r11, rdx
clc;
movzx rdi, dil
adcx rdi, r12; loading flag
adcx r14, [ rsp + 0x1e8 ]
setc dil; spill CF x253 to reg (rdi)
movzx rdx, byte [ rsp + 0x1d8 ]; load byte memx178 to register64
clc;
adcx rdx, r12; loading flag
adcx r8, [ rsp + 0x110 ]
seto dl; spill OF x240 to reg (rdx)
movzx r12, byte [ rsp + 0x1c8 ]; load byte memx277 to register64
mov byte [ rsp + 0x220 ], dil; spilling byte x253 to mem
mov rdi, 0x0 ; moving imm to reg
dec rdi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r12, rdi; loading flag
adox r15, [ rsp + 0x1a8 ]
xchg rdx, rcx; x3, swapping with x240, which is currently in rdx
mulx r12, rdi, [ r10 + 0x28 ]; x224, x223<- x3 * arg2[5]
adox rsi, r13
seto r13b; spill OF x281 to reg (r13)
mov [ rsp + 0x228 ], r12; spilling x224 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
movzx rax, al
adox rax, r12; loading flag
adox r14, r15
mov rax, [ r9 + 0x28 ]; load m64 x5 to register64
mulx rdx, r15, [ r10 + 0x20 ]; x226, x225<- x3 * arg2[4]
movzx r12, byte [ rsp + 0x128 ]; x181, copying x145 here, cause x145 is needed in a reg for other than x181, namely all: , x181--x182, size: 1
adcx r12, r11
setc r11b; spill CF x182 to reg (r11)
clc;
mov [ rsp + 0x230 ], r14; spilling x291 to mem
mov r14, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, r14; loading flag
adcx r15, [ rsp + 0x1e0 ]
xchg rdx, rax; x5, swapping with x226, which is currently in rdx
mulx rcx, r14, [ r10 + 0x8 ]; x386, x385<- x5 * arg2[1]
adcx rdi, rax
movzx rax, bl; x207, copying x206 here, cause x206 is needed in a reg for other than x207, namely all: , x207, size: 1
mov [ rsp + 0x238 ], rcx; spilling x386 to mem
mov rcx, [ rsp + 0x210 ]; load m64 x186 to register64
lea rax, [ rax + rcx ]; r8/64 + m8
setc cl; spill CF x244 to reg (rcx)
movzx rbx, byte [ rsp + 0x200 ]; load byte memx217 to register64
clc;
mov [ rsp + 0x240 ], r14; spilling x385 to mem
mov r14, -0x1 ; moving imm to reg
adcx rbx, r14; loading flag
adcx r8, [ rsp + 0x218 ]
setc bl; spill CF x219 to reg (rbx)
movzx r14, byte [ rsp + 0x220 ]; load byte memx253 to register64
clc;
mov byte [ rsp + 0x248 ], r13b; spilling byte x281 to mem
mov r13, -0x1 ; moving imm to reg
adcx r14, r13; loading flag
adcx r8, r15
mulx r14, r15, [ r10 + 0x10 ]; x384, x383<- x5 * arg2[2]
seto r13b; spill OF x292 to reg (r13)
mov [ rsp + 0x250 ], r14; spilling x384 to mem
mov r14, -0x1 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r14, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, r14; loading flag
adox r12, rax
mov rax, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbp; x260, swapping with x5, which is currently in rdx
mulx rdx, rbx, rax; x263, x262<- x260 * 0xffffffffffffffff
movzx r14, r11b; x222, copying x182 here, cause x182 is needed in a reg for other than x222, namely all: , x222, size: 1
mov rax, 0x0 ; moving imm to reg
adox r14, rax
adcx rdi, r12
dec rax; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r13, r13b
adox r13, rax; loading flag
adox r8, rsi
mov rsi, rdx; preserving value of x263 into a new reg
mov rdx, [ r10 + 0x0 ]; saving arg2[0] in rdx.
mulx r13, r11, rbp; x388, x387<- x5 * arg2[0]
mov rdx, [ r10 + 0x20 ]; arg2[4] to rdx
mulx r12, rax, rbp; x380, x379<- x5 * arg2[4]
mov [ rsp + 0x258 ], r8; spilling x293 to mem
movzx r8, cl; x245, copying x244 here, cause x244 is needed in a reg for other than x245, namely all: , x245, size: 1
mov [ rsp + 0x260 ], r11; spilling x387 to mem
mov r11, [ rsp + 0x228 ]; load m64 x224 to register64
lea r8, [ r8 + r11 ]; r8/64 + m8
adcx r8, r14
mov r11, [ r9 + 0x20 ]; load m64 x4 to register64
setc cl; spill CF x259 to reg (rcx)
movzx r14, byte [ rsp + 0x248 ]; load byte memx281 to register64
clc;
mov [ rsp + 0x268 ], r8; spilling x258 to mem
mov r8, -0x1 ; moving imm to reg
adcx r14, r8; loading flag
adcx rbx, [ rsp + 0x208 ]
mov r14, 0x0 ; moving imm to reg
adcx rsi, r14
mov rdx, [ r10 + 0x18 ]; arg2[3] to rdx
mulx r14, r8, rbp; x382, x381<- x5 * arg2[3]
adox rbx, rdi
clc;
adcx r13, [ rsp + 0x240 ]
mov rdi, [ rsp + 0x238 ]; x391, copying x386 here, cause x386 is needed in a reg for other than x391, namely all: , x391--x392, size: 1
adcx rdi, r15
mov r15, [ rsp + 0x250 ]; x393, copying x384 here, cause x384 is needed in a reg for other than x393, namely all: , x393--x394, size: 1
adcx r15, r8
adcx rax, r14
mov rdx, r11; x4 to rdx
mulx r11, r14, [ r10 + 0x0 ]; x311, x310<- x4 * arg2[0]
mov r8, rdx; preserving value of x4 into a new reg
mov rdx, [ r10 + 0x28 ]; saving arg2[5] in rdx.
mov [ rsp + 0x270 ], rax; spilling x395 to mem
mulx rbp, rax, rbp; x378, x377<- x5 * arg2[5]
adcx rax, r12
mov r12, [ rsp + 0x268 ]; x297, copying x258 here, cause x258 is needed in a reg for other than x297, namely all: , x297--x298, size: 1
adox r12, rsi
mov rsi, 0x0 ; moving imm to reg
adcx rbp, rsi
clc;
adcx r14, [ rsp + 0x1b8 ]
mov rdx, [ r10 + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x278 ], rbp; spilling x399 to mem
mulx rsi, rbp, r8; x307, x306<- x4 * arg2[2]
mov [ rsp + 0x280 ], rax; spilling x397 to mem
mov rax, 0x100000001 ; moving imm to reg
mov rdx, r14; x323 to rdx
mov [ rsp + 0x288 ], r15; spilling x393 to mem
mulx r14, r15, rax; _, x337<- x323 * 0x100000001
xchg rdx, r8; x4, swapping with x323, which is currently in rdx
mulx r14, rax, [ r10 + 0x8 ]; x309, x308<- x4 * arg2[1]
mov [ rsp + 0x290 ], r12; spilling x297 to mem
mov [ rsp + 0x298 ], rbx; spilling x295 to mem
mulx r12, rbx, [ r10 + 0x18 ]; x305, x304<- x4 * arg2[3]
mov [ rsp + 0x2a0 ], r12; spilling x305 to mem
movzx r12, cl; x299, copying x259 here, cause x259 is needed in a reg for other than x299, namely all: , x299, size: 1
mov [ rsp + 0x2a8 ], rdi; spilling x391 to mem
mov rdi, 0x0 ; moving imm to reg
adox r12, rdi
mov rcx, -0x3 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rax, r11
mov r11, 0xffffffff ; moving imm to reg
xchg rdx, r15; x337, swapping with x4, which is currently in rdx
mulx rdi, rcx, r11; x350, x349<- x337 * 0xffffffff
mov r11, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x2b0 ], r12; spilling x299 to mem
mov [ rsp + 0x2b8 ], r13; spilling x389 to mem
mulx r12, r13, r11; x344, x343<- x337 * 0xffffffffffffffff
mov r11, [ rsp + 0x1f8 ]; x325, copying x289 here, cause x289 is needed in a reg for other than x325, namely all: , x325--x326, size: 1
adcx r11, rax
mov rax, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x2c0 ], r12; spilling x344 to mem
mov [ rsp + 0x2c8 ], r13; spilling x343 to mem
mulx r12, r13, rax; x348, x347<- x337 * 0xffffffff00000000
adox rbp, r14
setc r14b; spill CF x326 to reg (r14)
clc;
adcx r13, rdi
setc dil; spill CF x352 to reg (rdi)
clc;
adcx rcx, r8
adcx r13, r11
setc cl; spill CF x365 to reg (rcx)
clc;
adcx r13, [ rsp + 0x260 ]
mov r8, 0x100000001 ; moving imm to reg
xchg rdx, r13; x400, swapping with x337, which is currently in rdx
mulx r11, rax, r8; _, x414<- x400 * 0x100000001
adox rbx, rsi
mov r11, 0xffffffff ; moving imm to reg
xchg rdx, rax; x414, swapping with x400, which is currently in rdx
mulx rsi, r8, r11; x427, x426<- x414 * 0xffffffff
setc r11b; spill CF x401 to reg (r11)
clc;
adcx r8, rax
mov r8, 0xfffffffffffffffe ; moving imm to reg
xchg rdx, r8; 0xfffffffffffffffe, swapping with x414, which is currently in rdx
mov [ rsp + 0x2d0 ], rsi; spilling x427 to mem
mulx rax, rsi, r13; x346, x345<- x337 * 0xfffffffffffffffe
setc dl; spill CF x440 to reg (rdx)
clc;
mov byte [ rsp + 0x2d8 ], r11b; spilling byte x401 to mem
mov r11, -0x1 ; moving imm to reg
movzx r14, r14b
adcx r14, r11; loading flag
adcx rbp, [ rsp + 0x230 ]
mov r14, 0xffffffff00000000 ; moving imm to reg
xchg rdx, r8; x414, swapping with x440, which is currently in rdx
mov byte [ rsp + 0x2e0 ], r8b; spilling byte x440 to mem
mulx r11, r8, r14; x425, x424<- x414 * 0xffffffff00000000
mov r14, [ rsp + 0x258 ]; x329, copying x293 here, cause x293 is needed in a reg for other than x329, namely all: , x329--x330, size: 1
adcx r14, rbx
seto bl; spill OF x317 to reg (rbx)
mov [ rsp + 0x2e8 ], r11; spilling x425 to mem
mov r11, 0x0 ; moving imm to reg
dec r11; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rdi, dil
adox rdi, r11; loading flag
adox r12, rsi
mov rdi, [ rsp + 0x2c8 ]; x355, copying x343 here, cause x343 is needed in a reg for other than x355, namely all: , x355--x356, size: 1
adox rdi, rax
seto al; spill OF x356 to reg (rax)
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rsi, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, rsi; loading flag
adox rbp, r12
mov rcx, 0xfffffffffffffffe ; moving imm to reg
mulx r12, r11, rcx; x423, x422<- x414 * 0xfffffffffffffffe
setc sil; spill CF x330 to reg (rsi)
movzx rcx, byte [ rsp + 0x2d8 ]; load byte memx401 to register64
clc;
mov [ rsp + 0x2f0 ], r12; spilling x423 to mem
mov r12, -0x1 ; moving imm to reg
adcx rcx, r12; loading flag
adcx rbp, [ rsp + 0x2b8 ]
adox rdi, r14
setc cl; spill CF x403 to reg (rcx)
clc;
adcx r8, [ rsp + 0x2d0 ]
mov r14, 0xffffffffffffffff ; moving imm to reg
mov byte [ rsp + 0x2f8 ], al; spilling byte x356 to mem
mulx r12, rax, r14; x419, x418<- x414 * 0xffffffffffffffff
mov [ rsp + 0x300 ], r12; spilling x419 to mem
mov [ rsp + 0x308 ], rax; spilling x418 to mem
mulx r12, rax, r14; x421, x420<- x414 * 0xffffffffffffffff
mov r14, [ rsp + 0x2e8 ]; x430, copying x425 here, cause x425 is needed in a reg for other than x430, namely all: , x430--x431, size: 1
adcx r14, r11
setc r11b; spill CF x431 to reg (r11)
clc;
mov [ rsp + 0x310 ], r12; spilling x421 to mem
mov r12, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, r12; loading flag
adcx rdi, [ rsp + 0x2a8 ]
mov rcx, rdx; preserving value of x414 into a new reg
mov rdx, [ r10 + 0x28 ]; saving arg2[5] in rdx.
mov [ rsp + 0x318 ], rax; spilling x420 to mem
mulx r12, rax, r15; x301, x300<- x4 * arg2[5]
mov byte [ rsp + 0x320 ], r11b; spilling byte x431 to mem
seto r11b; spill OF x369 to reg (r11)
mov [ rsp + 0x328 ], r12; spilling x301 to mem
movzx r12, byte [ rsp + 0x2e0 ]; load byte memx440 to register64
mov [ rsp + 0x330 ], rax; spilling x300 to mem
mov rax, -0x1 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rax, -0x1 ; moving imm to reg
adox r12, rax; loading flag
adox rbp, r8
adox r14, rdi
setc r12b; spill CF x405 to reg (r12)
seto r8b; spill OF x444 to reg (r8)
mov rdi, rbp; x454, copying x441 here, cause x441 is needed in a reg for other than x454, namely all: , x454--x455, x468, size: 2
mov rax, 0xffffffff ; moving imm to reg
sub rdi, rax
mov rdx, r15; x4 to rdx
mulx rdx, r15, [ r10 + 0x20 ]; x303, x302<- x4 * arg2[4]
mov rax, r14; x456, copying x443 here, cause x443 is needed in a reg for other than x456, namely all: , x469, x456--x457, size: 2
mov [ rsp + 0x338 ], rdi; spilling x454 to mem
mov rdi, 0xffffffff00000000 ; moving imm to reg
sbb rax, rdi
mov rdi, 0x0 ; moving imm to reg
dec rdi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbx, bl
adox rbx, rdi; loading flag
adox r15, [ rsp + 0x2a0 ]
setc bl; spill CF x457 to reg (rbx)
clc;
movzx rsi, sil
adcx rsi, rdi; loading flag
adcx r15, [ rsp + 0x298 ]
mov rsi, [ rsp + 0x330 ]; x320, copying x300 here, cause x300 is needed in a reg for other than x320, namely all: , x320--x321, size: 1
adox rsi, rdx
mov rdx, 0xffffffffffffffff ; moving imm to reg
mulx rcx, rdi, rcx; x417, x416<- x414 * 0xffffffffffffffff
mov [ rsp + 0x340 ], rax; spilling x456 to mem
mov [ rsp + 0x348 ], rcx; spilling x417 to mem
mulx rax, rcx, r13; x340, x339<- x337 * 0xffffffffffffffff
mov byte [ rsp + 0x350 ], bl; spilling byte x457 to mem
mulx r13, rbx, r13; x342, x341<- x337 * 0xffffffffffffffff
mov rdx, [ rsp + 0x290 ]; x333, copying x297 here, cause x297 is needed in a reg for other than x333, namely all: , x333--x334, size: 1
adcx rdx, rsi
setc sil; spill CF x334 to reg (rsi)
mov byte [ rsp + 0x358 ], r8b; spilling byte x444 to mem
movzx r8, byte [ rsp + 0x2f8 ]; load byte memx356 to register64
clc;
mov [ rsp + 0x360 ], rdi; spilling x416 to mem
mov rdi, -0x1 ; moving imm to reg
adcx r8, rdi; loading flag
adcx rbx, [ rsp + 0x2c0 ]
mov r8, [ rsp + 0x328 ]; x322, copying x301 here, cause x301 is needed in a reg for other than x322, namely all: , x322, size: 1
mov rdi, 0x0 ; moving imm to reg
adox r8, rdi
adcx rcx, r13
adc rax, 0x0
mov r13, [ rsp + 0x2f0 ]; load m64 x423 to register64
add byte [ rsp + 0x320 ], 0x7F; load flag from rm/8 into OF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
seto [ rsp + 0x320 ]; since that has deps, resore it whereever it was
adox r13, [ rsp + 0x318 ]
mov rdi, -0x1 ; moving imm to reg
movzx r11, r11b
adcx r11, rdi; loading flag
adcx r15, rbx
adcx rcx, rdx
setc r11b; spill CF x373 to reg (r11)
clc;
movzx r12, r12b
adcx r12, rdi; loading flag
adcx r15, [ rsp + 0x288 ]
mov r12, [ rsp + 0x270 ]; x408, copying x395 here, cause x395 is needed in a reg for other than x408, namely all: , x408--x409, size: 1
adcx r12, rcx
mov rdx, [ rsp + 0x308 ]; load m64 x418 to register64
mov rbx, [ rsp + 0x310 ]; x434, copying x421 here, cause x421 is needed in a reg for other than x434, namely all: , x434--x435, size: 1
adox rbx, rdx
mov rdx, [ rsp + 0x360 ]; load m64 x416 to register64
mov rcx, [ rsp + 0x300 ]; x436, copying x419 here, cause x419 is needed in a reg for other than x436, namely all: , x436--x437, size: 1
adox rcx, rdx
seto dl; spill OF x437 to reg (rdx)
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdi, -0x1 ; moving imm to reg
movzx rsi, sil
adox rsi, rdi; loading flag
adox r8, [ rsp + 0x2b0 ]
setc sil; spill CF x409 to reg (rsi)
movzx rdi, byte [ rsp + 0x358 ]; load byte memx444 to register64
clc;
mov [ rsp + 0x368 ], rcx; spilling x436 to mem
mov rcx, -0x1 ; moving imm to reg
adcx rdi, rcx; loading flag
adcx r15, r13
setc dil; spill CF x446 to reg (rdi)
seto r13b; spill OF x336 to reg (r13)
movzx rcx, byte [ rsp + 0x350 ]; x457, copying x457 here, cause x457 is needed in a reg for other than x457, namely all: , x458--x459, size: 1
add rcx, -0x1
mov rcx, r15; x458, copying x445 here, cause x445 is needed in a reg for other than x458, namely all: , x458--x459, x470, size: 2
mov byte [ rsp + 0x370 ], sil; spilling byte x409 to mem
mov rsi, 0xfffffffffffffffe ; moving imm to reg
sbb rcx, rsi
mov rsi, 0x0 ; moving imm to reg
dec rsi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rdi, dil
adox rdi, rsi; loading flag
adox r12, rbx
seto bl; spill OF x448 to reg (rbx)
inc rsi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdi, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, rdi; loading flag
adox r8, rax
movzx rax, r13b; x376, copying x336 here, cause x336 is needed in a reg for other than x376, namely all: , x376, size: 1
adox rax, rsi
mov r11, r12; x460, copying x447 here, cause x447 is needed in a reg for other than x460, namely all: , x460--x461, x471, size: 2
mov r13, 0xffffffffffffffff ; moving imm to reg
sbb r11, r13
movzx rsi, dl; x438, copying x437 here, cause x437 is needed in a reg for other than x438, namely all: , x438, size: 1
mov rdi, [ rsp + 0x348 ]; load m64 x417 to register64
lea rsi, [ rsi + rdi ]; r8/64 + m8
movzx rdi, byte [ rsp + 0x370 ]; load byte memx409 to register64
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rdi, rdx; loading flag
adox r8, [ rsp + 0x280 ]
mov rdi, [ rsp + 0x278 ]; x412, copying x399 here, cause x399 is needed in a reg for other than x412, namely all: , x412--x413, size: 1
adox rdi, rax
setc al; spill CF x461 to reg (rax)
clc;
movzx rbx, bl
adcx rbx, rdx; loading flag
adcx r8, [ rsp + 0x368 ]
adcx rsi, rdi
seto bl; spill OF x453 to reg (rbx)
adc bl, 0x0
movzx rbx, bl
movzx rdi, al; x461, copying x461 here, cause x461 is needed in a reg for other than x461, namely all: , x462--x463, size: 1
add rdi, -0x1
mov rax, r8; x462, copying x449 here, cause x449 is needed in a reg for other than x462, namely all: , x462--x463, x472, size: 2
sbb rax, r13
mov rdx, rsi; x464, copying x451 here, cause x451 is needed in a reg for other than x464, namely all: , x473, x464--x465, size: 2
sbb rdx, r13
movzx r13, bl; _, copying x453 here, cause x453 is needed in a reg for other than _, namely all: , _--x467, size: 1
sbb r13, 0x00000000
cmovc rcx, r15; if CF, x470<- x445 (nzVar)
mov r13, [ rsp + 0x338 ]; x468, copying x454 here, cause x454 is needed in a reg for other than x468, namely all: , x468, size: 1
cmovc r13, rbp; if CF, x468<- x441 (nzVar)
cmovc r11, r12; if CF, x471<- x447 (nzVar)
mov rbp, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rbp + 0x0 ], r13; out1[0] = x468
cmovc rax, r8; if CF, x472<- x449 (nzVar)
mov [ rbp + 0x18 ], r11; out1[3] = x471
mov [ rbp + 0x20 ], rax; out1[4] = x472
mov [ rbp + 0x10 ], rcx; out1[2] = x470
mov r15, [ rsp + 0x340 ]; x469, copying x456 here, cause x456 is needed in a reg for other than x469, namely all: , x469, size: 1
cmovc r15, r14; if CF, x469<- x443 (nzVar)
cmovc rdx, rsi; if CF, x473<- x451 (nzVar)
mov [ rbp + 0x8 ], r15; out1[1] = x469
mov [ rbp + 0x28 ], rdx; out1[5] = x473
mov rbx, [ rsp + 0x378 ]; restoring from stack
mov rbp, [ rsp + 0x380 ]; restoring from stack
mov r12, [ rsp + 0x388 ]; restoring from stack
mov r13, [ rsp + 0x390 ]; restoring from stack
mov r14, [ rsp + 0x398 ]; restoring from stack
mov r15, [ rsp + 0x3a0 ]; restoring from stack
add rsp, 0x3a8 
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; clocked at 3533 MHz
; first cyclecount 248.52, best 196.78571428571428, lastGood 206.96428571428572
; seed 4366091815975477 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3050711 ms / 60000 runs=> 50.84518333333333ms/run
; Time spent for assembling and measureing (initial batch_size=56, initial num_batches=101): 127609 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.04182926537453072
; number reverted permutation/ tried permutation: 20933 / 30032 =69.702%
; number reverted decision/ tried decision: 18917 / 29969 =63.122%