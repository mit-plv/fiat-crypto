SECTION .text
	GLOBAL square_p384
square_p384:
sub rsp, 0x318 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x2e8 ], rbx; saving to stack
mov [ rsp + 0x2f0 ], rbp; saving to stack
mov [ rsp + 0x2f8 ], r12; saving to stack
mov [ rsp + 0x300 ], r13; saving to stack
mov [ rsp + 0x308 ], r14; saving to stack
mov [ rsp + 0x310 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x6 to register64
mov r10, [ rsi + 0x8 ]; load m64 x1 to register64
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r11, rbx, rax; x18, x17<- x6 * arg1[0]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rbp, r12, r10; x80, x79<- x1 * arg1[0]
mov r13, 0x100000001 ; moving imm to reg
mov rdx, rbx; x17 to rdx
mulx rbx, r14, r13; _, x30<- x17 * 0x100000001
mov rbx, rdx; preserving value of x17 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r15, rcx, rax; x16, x15<- x6 * arg1[1]
add rcx, r11; could be done better, if r0 has been u8 as well
mov rdx, 0xffffffff00000000 ; moving imm to reg
mulx r8, r9, r14; x41, x40<- x30 * 0xffffffff00000000
mov r11, 0xffffffff ; moving imm to reg
xchg rdx, r11; 0xffffffff, swapping with 0xffffffff00000000, which is currently in rdx
mulx r11, r13, r14; x43, x42<- x30 * 0xffffffff
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, rbx
setc r13b; spill CF x20 to reg (r13)
clc;
adcx r9, r11
mov rbx, 0xfffffffffffffffe ; moving imm to reg
mov rdx, r14; x30 to rdx
mulx r14, r11, rbx; x39, x38<- x30 * 0xfffffffffffffffe
adox r9, rcx
xchg rdx, r10; x1, swapping with x30, which is currently in rdx
mulx rcx, rbx, [ rsi + 0x8 ]; x78, x77<- x1 * arg1[1]
xchg rdx, rax; x6, swapping with x1, which is currently in rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov [ rsp + 0x8 ], r14; spilling x39 to mem
mulx rdi, r14, [ rsi + 0x10 ]; x14, x13<- x6 * arg1[2]
mov [ rsp + 0x10 ], rcx; spilling x78 to mem
seto cl; spill OF x58 to reg (rcx)
mov [ rsp + 0x18 ], rdi; spilling x14 to mem
mov rdi, 0x0 ; moving imm to reg
dec rdi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r13, r13b
adox r13, rdi; loading flag
adox r15, r14
seto r13b; spill OF x22 to reg (r13)
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r12, r9
mov r9, 0x100000001 ; moving imm to reg
xchg rdx, r12; x92, swapping with x6, which is currently in rdx
mulx r14, rdi, r9; _, x106<- x92 * 0x100000001
mov r14, 0xffffffff ; moving imm to reg
xchg rdx, r14; 0xffffffff, swapping with x92, which is currently in rdx
mov byte [ rsp + 0x20 ], r13b; spilling byte x22 to mem
mulx r9, r13, rdi; x119, x118<- x106 * 0xffffffff
adcx r11, r8
xchg rdx, r12; x6, swapping with 0xffffffff, which is currently in rdx
mulx r8, r12, [ rsi + 0x18 ]; x12, x11<- x6 * arg1[3]
mov [ rsp + 0x28 ], r8; spilling x12 to mem
seto r8b; spill OF x93 to reg (r8)
mov [ rsp + 0x30 ], r13; spilling x118 to mem
mov r13, -0x1 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r13, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r13; loading flag
adox r15, r11
setc cl; spill CF x47 to reg (rcx)
clc;
adcx rbx, rbp
seto bpl; spill OF x60 to reg (rbp)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r11, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, r11; loading flag
adox r15, rbx
seto r8b; spill OF x95 to reg (r8)
movzx rbx, byte [ rsp + 0x20 ]; load byte memx22 to register64
dec r13; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
adox rbx, r13; loading flag
adox r12, [ rsp + 0x18 ]
mov r11, rdx; preserving value of x6 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx rbx, r13, rax; x76, x75<- x1 * arg1[2]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x38 ], rbx; spilling x76 to mem
mov byte [ rsp + 0x40 ], r8b; spilling byte x95 to mem
mulx rbx, r8, r10; x37, x36<- x30 * 0xffffffffffffffff
mov rdx, [ rsp + 0x10 ]; x83, copying x78 here, cause x78 is needed in a reg for other than x83, namely all: , x83--x84, size: 1
adcx rdx, r13
mov r13, 0xffffffff00000000 ; moving imm to reg
xchg rdx, rdi; x106, swapping with x83, which is currently in rdx
mov [ rsp + 0x48 ], rdi; spilling x83 to mem
mov [ rsp + 0x50 ], r12; spilling x23 to mem
mulx rdi, r12, r13; x117, x116<- x106 * 0xffffffff00000000
setc r13b; spill CF x84 to reg (r13)
clc;
adcx r12, r9
seto r9b; spill OF x24 to reg (r9)
mov byte [ rsp + 0x58 ], r13b; spilling byte x84 to mem
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, [ rsp + 0x30 ]
mov r14, 0xfffffffffffffffe ; moving imm to reg
mov byte [ rsp + 0x60 ], r9b; spilling byte x24 to mem
mulx r13, r9, r14; x115, x114<- x106 * 0xfffffffffffffffe
adox r12, r15
adcx r9, rdi
seto r15b; spill OF x134 to reg (r15)
mov rdi, 0x0 ; moving imm to reg
dec rdi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rcx, cl
adox rcx, rdi; loading flag
adox r8, [ rsp + 0x8 ]
mov rcx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r10; x30, swapping with x106, which is currently in rdx
mulx rdi, r14, rcx; x35, x34<- x30 * 0xffffffffffffffff
xchg rdx, rax; x1, swapping with x30, which is currently in rdx
mov [ rsp + 0x68 ], r12; spilling x133 to mem
mulx rcx, r12, [ rsi + 0x18 ]; x74, x73<- x1 * arg1[3]
adox r14, rbx
setc bl; spill CF x123 to reg (rbx)
clc;
mov [ rsp + 0x70 ], rcx; spilling x74 to mem
mov rcx, -0x1 ; moving imm to reg
movzx rbp, bpl
adcx rbp, rcx; loading flag
adcx r8, [ rsp + 0x50 ]
seto bpl; spill OF x51 to reg (rbp)
movzx rcx, byte [ rsp + 0x40 ]; load byte memx95 to register64
mov [ rsp + 0x78 ], rdi; spilling x35 to mem
mov rdi, 0x0 ; moving imm to reg
dec rdi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rcx, rdi; loading flag
adox r8, [ rsp + 0x48 ]
setc cl; spill CF x62 to reg (rcx)
clc;
movzx r15, r15b
adcx r15, rdi; loading flag
adcx r8, r9
xchg rdx, r11; x6, swapping with x1, which is currently in rdx
mulx r15, r9, [ rsi + 0x28 ]; x8, x7<- x6 * arg1[5]
mulx rdx, rdi, [ rsi + 0x20 ]; x10, x9<- x6 * arg1[4]
mov [ rsp + 0x80 ], r8; spilling x135 to mem
mov r8, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r10; x106, swapping with x10, which is currently in rdx
mov byte [ rsp + 0x88 ], bpl; spilling byte x51 to mem
mov [ rsp + 0x90 ], r12; spilling x73 to mem
mulx rbp, r12, r8; x113, x112<- x106 * 0xffffffffffffffff
setc r8b; spill CF x136 to reg (r8)
mov [ rsp + 0x98 ], rbp; spilling x113 to mem
movzx rbp, byte [ rsp + 0x60 ]; load byte memx24 to register64
clc;
mov [ rsp + 0xa0 ], r12; spilling x112 to mem
mov r12, -0x1 ; moving imm to reg
adcx rbp, r12; loading flag
adcx rdi, [ rsp + 0x28 ]
adcx r9, r10
mov rbp, 0x0 ; moving imm to reg
adcx r15, rbp
clc;
movzx rcx, cl
adcx rcx, r12; loading flag
adcx rdi, r14
xchg rdx, r11; x1, swapping with x106, which is currently in rdx
mulx r14, rcx, [ rsi + 0x20 ]; x72, x71<- x1 * arg1[4]
setc r10b; spill CF x64 to reg (r10)
clc;
movzx rbx, bl
adcx rbx, r12; loading flag
adcx r13, [ rsp + 0xa0 ]
mov rbx, [ rsp + 0x90 ]; load m64 x73 to register64
setc bpl; spill CF x125 to reg (rbp)
movzx r12, byte [ rsp + 0x58 ]; load byte memx84 to register64
clc;
mov [ rsp + 0xa8 ], r14; spilling x72 to mem
mov r14, -0x1 ; moving imm to reg
adcx r12, r14; loading flag
adcx rbx, [ rsp + 0x38 ]
mov r12, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r12; 0xffffffffffffffff, swapping with x1, which is currently in rdx
mulx rax, r14, rax; x33, x32<- x30 * 0xffffffffffffffff
mov [ rsp + 0xb0 ], r15; spilling x29 to mem
mov byte [ rsp + 0xb8 ], bpl; spilling byte x125 to mem
mulx r15, rbp, r11; x111, x110<- x106 * 0xffffffffffffffff
adox rbx, rdi
seto dil; spill OF x99 to reg (rdi)
movzx rdx, byte [ rsp + 0x88 ]; load byte memx51 to register64
mov [ rsp + 0xc0 ], r15; spilling x111 to mem
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r15, -0x1 ; moving imm to reg
adox rdx, r15; loading flag
adox r14, [ rsp + 0x78 ]
seto dl; spill OF x53 to reg (rdx)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
movzx r10, r10b
adox r10, r15; loading flag
adox r9, r14
mov r10, [ rsp + 0x70 ]; x87, copying x74 here, cause x74 is needed in a reg for other than x87, namely all: , x87--x88, size: 1
adcx r10, rcx
setc cl; spill CF x88 to reg (rcx)
clc;
movzx rdi, dil
adcx rdi, r15; loading flag
adcx r9, r10
mov rdi, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rdi; 0xffffffffffffffff, swapping with x53, which is currently in rdx
mulx r11, r14, r11; x109, x108<- x106 * 0xffffffffffffffff
seto r10b; spill OF x66 to reg (r10)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, r15; loading flag
adox rbx, r13
mov r8, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx r12, r13, r12; x70, x69<- x1 * arg1[5]
movzx rdx, dil; x54, copying x53 here, cause x53 is needed in a reg for other than x54, namely all: , x54, size: 1
lea rdx, [ rdx + rax ]
setc al; spill CF x101 to reg (rax)
movzx rdi, byte [ rsp + 0xb8 ]; load byte memx125 to register64
clc;
adcx rdi, r15; loading flag
adcx rbp, [ rsp + 0x98 ]
setc dil; spill CF x127 to reg (rdi)
clc;
movzx r10, r10b
adcx r10, r15; loading flag
adcx rdx, [ rsp + 0xb0 ]
adox rbp, r9
mov r10, [ rsi + 0x10 ]; load m64 x2 to register64
setc r9b; spill CF x68 to reg (r9)
clc;
movzx rcx, cl
adcx rcx, r15; loading flag
adcx r13, [ rsp + 0xa8 ]
seto cl; spill OF x140 to reg (rcx)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
movzx rdi, dil
adox rdi, r15; loading flag
adox r14, [ rsp + 0xc0 ]
mov rdi, 0x0 ; moving imm to reg
adcx r12, rdi
adox r11, rdi
add al, 0x7F; load flag from rm/8 into OF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
seto al; since that has deps, resore it whereever it was
adox rdx, r13
mov rax, rdx; preserving value of x102 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r13, rdi, r10; x157, x156<- x2 * arg1[0]
adcx rdi, [ rsp + 0x68 ]
movzx rdx, r9b; x104, copying x68 here, cause x68 is needed in a reg for other than x104, namely all: , x104--x105, size: 1
adox rdx, r12
setc r9b; spill CF x170 to reg (r9)
clc;
movzx rcx, cl
adcx rcx, r15; loading flag
adcx rax, r14
adcx r11, rdx
mov rcx, 0x100000001 ; moving imm to reg
mov rdx, rcx; 0x100000001 to rdx
mulx rcx, r14, rdi; _, x183<- x169 * 0x100000001
seto cl; spill OF x145 to reg (rcx)
adc cl, 0x0
movzx rcx, cl
mov r12, 0xffffffff ; moving imm to reg
xchg rdx, r12; 0xffffffff, swapping with 0x100000001, which is currently in rdx
mulx r15, r12, r14; x196, x195<- x183 * 0xffffffff
mov rdx, 0xffffffff00000000 ; moving imm to reg
mov byte [ rsp + 0xc8 ], cl; spilling byte x145 to mem
mulx r8, rcx, r14; x194, x193<- x183 * 0xffffffff00000000
adox rcx, r15
mov r15, rdx; preserving value of 0xffffffff00000000 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0xd0 ], r11; spilling x143 to mem
mov [ rsp + 0xd8 ], rax; spilling x141 to mem
mulx r11, rax, r10; x155, x154<- x2 * arg1[1]
mov rdx, [ rsi + 0x18 ]; load m64 x3 to register64
adcx rax, r13
seto r13b; spill OF x198 to reg (r13)
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r15, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, r15; loading flag
adox rax, [ rsp + 0x80 ]
mulx r9, r15, [ rsi + 0x0 ]; x234, x233<- x3 * arg1[0]
mov [ rsp + 0xe0 ], r9; spilling x234 to mem
setc r9b; spill CF x159 to reg (r9)
clc;
adcx r12, rdi
adcx rcx, rax
setc r12b; spill CF x211 to reg (r12)
clc;
adcx r15, rcx
mov rdi, 0x100000001 ; moving imm to reg
xchg rdx, rdi; 0x100000001, swapping with x3, which is currently in rdx
mulx rax, rcx, r15; _, x260<- x246 * 0x100000001
mov rax, 0xfffffffffffffffe ; moving imm to reg
xchg rdx, rcx; x260, swapping with 0x100000001, which is currently in rdx
mov byte [ rsp + 0xe8 ], r12b; spilling byte x211 to mem
mulx rcx, r12, rax; x269, x268<- x260 * 0xfffffffffffffffe
mov rax, 0xffffffff ; moving imm to reg
mov [ rsp + 0xf0 ], rbp; spilling x139 to mem
mov [ rsp + 0xf8 ], rbx; spilling x137 to mem
mulx rbp, rbx, rax; x273, x272<- x260 * 0xffffffff
mov rax, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x100 ], r11; spilling x155 to mem
mov byte [ rsp + 0x108 ], r9b; spilling byte x159 to mem
mulx r11, r9, rax; x271, x270<- x260 * 0xffffffff00000000
mov rax, 0xfffffffffffffffe ; moving imm to reg
xchg rdx, r14; x183, swapping with x260, which is currently in rdx
mov [ rsp + 0x110 ], rbx; spilling x272 to mem
mov [ rsp + 0x118 ], r8; spilling x194 to mem
mulx rbx, r8, rax; x192, x191<- x183 * 0xfffffffffffffffe
setc al; spill CF x247 to reg (rax)
clc;
adcx r9, rbp
mov rbp, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r14; x260, swapping with x183, which is currently in rdx
mov [ rsp + 0x120 ], r9; spilling x274 to mem
mov byte [ rsp + 0x128 ], al; spilling byte x247 to mem
mulx r9, rax, rbp; x265, x264<- x260 * 0xffffffffffffffff
mov [ rsp + 0x130 ], rbx; spilling x192 to mem
mov [ rsp + 0x138 ], r8; spilling x191 to mem
mulx rbx, r8, rbp; x267, x266<- x260 * 0xffffffffffffffff
mov byte [ rsp + 0x140 ], r13b; spilling byte x198 to mem
mulx rdx, r13, rbp; x263, x262<- x260 * 0xffffffffffffffff
adcx r12, r11
adcx r8, rcx
adcx rax, rbx
xchg rdx, r14; x183, swapping with x263, which is currently in rdx
mulx rcx, r11, rbp; x188, x187<- x183 * 0xffffffffffffffff
mov [ rsp + 0x148 ], rax; spilling x280 to mem
mulx rbx, rax, rbp; x190, x189<- x183 * 0xffffffffffffffff
adcx r13, r9
mulx rdx, r9, rbp; x186, x185<- x183 * 0xffffffffffffffff
mov rbp, [ rsp + 0x138 ]; load m64 x191 to register64
mov [ rsp + 0x150 ], r13; spilling x282 to mem
seto r13b; spill OF x172 to reg (r13)
mov [ rsp + 0x158 ], r8; spilling x278 to mem
movzx r8, byte [ rsp + 0x140 ]; load byte memx198 to register64
mov [ rsp + 0x160 ], r12; spilling x276 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r8, r12; loading flag
adox rbp, [ rsp + 0x118 ]
seto r8b; spill OF x200 to reg (r8)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r15, [ rsp + 0x110 ]
seto r15b; spill OF x286 to reg (r15)
dec r12; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r8, r8b
adox r8, r12; loading flag
adox rax, [ rsp + 0x130 ]
adox r11, rbx
mov rbx, [ rsi + 0x20 ]; load m64 x4 to register64
adox r9, rcx
mov rcx, 0x0 ; moving imm to reg
adcx r14, rcx
mov r8, rdx; preserving value of x186 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx rcx, r12, r10; x153, x152<- x2 * arg1[2]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x168 ], r14; spilling x284 to mem
mov [ rsp + 0x170 ], r9; spilling x205 to mem
mulx r14, r9, r10; x151, x150<- x2 * arg1[3]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x178 ], r11; spilling x203 to mem
mov [ rsp + 0x180 ], r14; spilling x151 to mem
mulx r11, r14, rbx; x309, x308<- x4 * arg1[1]
movzx rdx, byte [ rsp + 0x108 ]; load byte memx159 to register64
clc;
mov [ rsp + 0x188 ], r11; spilling x309 to mem
mov r11, -0x1 ; moving imm to reg
adcx rdx, r11; loading flag
adcx r12, [ rsp + 0x100 ]
mov rdx, 0x0 ; moving imm to reg
adox r8, rdx
adcx r9, rcx
xchg rdx, rdi; x3, swapping with 0x0, which is currently in rdx
mulx rcx, rdi, [ rsi + 0x8 ]; x232, x231<- x3 * arg1[1]
mov r11, rdx; preserving value of x3 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x190 ], r8; spilling x207 to mem
mov [ rsp + 0x198 ], r14; spilling x308 to mem
mulx r8, r14, r10; x149, x148<- x2 * arg1[4]
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, rdx; loading flag
adox r12, [ rsp + 0xf8 ]
mov r13, [ rsp + 0xf0 ]; x175, copying x139 here, cause x139 is needed in a reg for other than x175, namely all: , x175--x176, size: 1
adox r13, r9
seto r9b; spill OF x176 to reg (r9)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rdi, [ rsp + 0xe0 ]
seto dl; spill OF x236 to reg (rdx)
mov [ rsp + 0x1a0 ], r8; spilling x149 to mem
movzx r8, byte [ rsp + 0xe8 ]; load byte memx211 to register64
mov byte [ rsp + 0x1a8 ], r9b; spilling byte x176 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r8, r9; loading flag
adox r12, rbp
mov r8b, dl; preserving value of x236 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx rbp, r9, r11; x230, x229<- x3 * arg1[2]
setc dl; spill CF x163 to reg (rdx)
clc;
mov [ rsp + 0x1b0 ], rbp; spilling x230 to mem
mov rbp, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, rbp; loading flag
adcx rcx, r9
seto r8b; spill OF x213 to reg (r8)
movzx r9, byte [ rsp + 0x128 ]; load byte memx247 to register64
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
adox r9, rbp; loading flag
adox r12, rdi
setc r9b; spill CF x238 to reg (r9)
clc;
movzx r15, r15b
adcx r15, rbp; loading flag
adcx r12, [ rsp + 0x120 ]
setc r15b; spill CF x288 to reg (r15)
clc;
movzx r8, r8b
adcx r8, rbp; loading flag
adcx r13, rax
setc al; spill CF x215 to reg (rax)
clc;
movzx rdx, dl
adcx rdx, rbp; loading flag
adcx r14, [ rsp + 0x180 ]
adox rcx, r13
mov rdx, rbx; x4 to rdx
mulx rbx, rdi, [ rsi + 0x0 ]; x311, x310<- x4 * arg1[0]
seto r8b; spill OF x251 to reg (r8)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rdi, r12
mov r12, 0x100000001 ; moving imm to reg
xchg rdx, rdi; x323, swapping with x4, which is currently in rdx
mulx r13, rbp, r12; _, x337<- x323 * 0x100000001
mov r13, 0xffffffff ; moving imm to reg
xchg rdx, r13; 0xffffffff, swapping with x323, which is currently in rdx
mov byte [ rsp + 0x1b8 ], r8b; spilling byte x251 to mem
mulx r12, r8, rbp; x350, x349<- x337 * 0xffffffff
setc dl; spill CF x165 to reg (rdx)
mov [ rsp + 0x1c0 ], r12; spilling x350 to mem
movzx r12, byte [ rsp + 0x1a8 ]; load byte memx176 to register64
clc;
mov byte [ rsp + 0x1c8 ], r9b; spilling byte x238 to mem
mov r9, -0x1 ; moving imm to reg
adcx r12, r9; loading flag
adcx r14, [ rsp + 0xd8 ]
setc r12b; spill CF x178 to reg (r12)
clc;
movzx rax, al
adcx rax, r9; loading flag
adcx r14, [ rsp + 0x178 ]
mov al, dl; preserving value of x165 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov byte [ rsp + 0x1d0 ], r12b; spilling byte x178 to mem
mulx r9, r12, r11; x228, x227<- x3 * arg1[3]
setc dl; spill CF x217 to reg (rdx)
clc;
adcx rbx, [ rsp + 0x198 ]
mov [ rsp + 0x1d8 ], r9; spilling x228 to mem
mov r9, 0xffffffff00000000 ; moving imm to reg
xchg rdx, rbp; x337, swapping with x217, which is currently in rdx
mov byte [ rsp + 0x1e0 ], bpl; spilling byte x217 to mem
mov byte [ rsp + 0x1e8 ], al; spilling byte x165 to mem
mulx rbp, rax, r9; x348, x347<- x337 * 0xffffffff00000000
setc r9b; spill CF x313 to reg (r9)
clc;
mov [ rsp + 0x1f0 ], rbp; spilling x348 to mem
mov rbp, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, rbp; loading flag
adcx rcx, [ rsp + 0x160 ]
adox rbx, rcx
mov r15, 0xfffffffffffffffe ; moving imm to reg
mulx rcx, rbp, r15; x346, x345<- x337 * 0xfffffffffffffffe
seto r15b; spill OF x326 to reg (r15)
mov [ rsp + 0x1f8 ], rcx; spilling x346 to mem
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, r13
setc r8b; spill CF x290 to reg (r8)
movzx r13, byte [ rsp + 0x1c8 ]; load byte memx238 to register64
clc;
adcx r13, rcx; loading flag
adcx r12, [ rsp + 0x1b0 ]
mov r13, rdx; preserving value of x337 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x200 ], rbp; spilling x345 to mem
mulx rcx, rbp, rdi; x307, x306<- x4 * arg1[2]
setc dl; spill CF x240 to reg (rdx)
clc;
adcx rax, [ rsp + 0x1c0 ]
adox rax, rbx
mov bl, dl; preserving value of x240 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x208 ], rax; spilling x364 to mem
mov [ rsp + 0x210 ], rcx; spilling x307 to mem
mulx rax, rcx, r11; x226, x225<- x3 * arg1[4]
mov rdx, r10; x2 to rdx
mulx rdx, r10, [ rsi + 0x28 ]; x147, x146<- x2 * arg1[5]
mov [ rsp + 0x218 ], rax; spilling x226 to mem
seto al; spill OF x365 to reg (rax)
mov [ rsp + 0x220 ], rdx; spilling x147 to mem
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, rdx; loading flag
adox rbp, [ rsp + 0x188 ]
seto r9b; spill OF x315 to reg (r9)
movzx rdx, byte [ rsp + 0x1b8 ]; load byte memx251 to register64
mov byte [ rsp + 0x228 ], al; spilling byte x365 to mem
mov rax, -0x1 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rax, -0x1 ; moving imm to reg
adox rdx, rax; loading flag
adox r14, r12
setc dl; spill CF x352 to reg (rdx)
clc;
movzx r8, r8b
adcx r8, rax; loading flag
adcx r14, [ rsp + 0x158 ]
setc r8b; spill CF x292 to reg (r8)
clc;
movzx r15, r15b
adcx r15, rax; loading flag
adcx r14, rbp
seto r15b; spill OF x253 to reg (r15)
movzx r12, byte [ rsp + 0x1e8 ]; load byte memx165 to register64
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
adox r12, rbp; loading flag
adox r10, [ rsp + 0x1a0 ]
setc r12b; spill CF x328 to reg (r12)
movzx rax, byte [ rsp + 0x1d0 ]; load byte memx178 to register64
clc;
adcx rax, rbp; loading flag
adcx r10, [ rsp + 0xd0 ]
seto al; spill OF x167 to reg (rax)
movzx rbp, byte [ rsp + 0x1e0 ]; load byte memx217 to register64
mov [ rsp + 0x230 ], r14; spilling x327 to mem
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbp, r14; loading flag
adox r10, [ rsp + 0x170 ]
mov rbp, [ rsp + 0x200 ]; load m64 x345 to register64
setc r14b; spill CF x180 to reg (r14)
clc;
mov byte [ rsp + 0x238 ], r12b; spilling byte x328 to mem
mov r12, -0x1 ; moving imm to reg
movzx rdx, dl
adcx rdx, r12; loading flag
adcx rbp, [ rsp + 0x1f0 ]
setc dl; spill CF x354 to reg (rdx)
clc;
movzx rbx, bl
adcx rbx, r12; loading flag
adcx rcx, [ rsp + 0x1d8 ]
movzx rbx, al; x168, copying x167 here, cause x167 is needed in a reg for other than x168, namely all: , x168, size: 1
mov r12, [ rsp + 0x220 ]; load m64 x147 to register64
lea rbx, [ rbx + r12 ]; r8/64 + m8
mov r12b, dl; preserving value of x354 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx r11, rax, r11; x224, x223<- x3 * arg1[5]
mov rdx, [ rsp + 0x218 ]; x243, copying x226 here, cause x226 is needed in a reg for other than x243, namely all: , x243--x244, size: 1
adcx rdx, rax
xchg rdx, rdi; x4, swapping with x243, which is currently in rdx
mov [ rsp + 0x240 ], rbp; spilling x353 to mem
mulx rax, rbp, [ rsi + 0x18 ]; x305, x304<- x4 * arg1[3]
mov [ rsp + 0x248 ], rax; spilling x305 to mem
seto al; spill OF x219 to reg (rax)
mov byte [ rsp + 0x250 ], r12b; spilling byte x354 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
mov [ rsp + 0x258 ], rdi; spilling x243 to mem
movzx rdi, byte [ rsp + 0xc8 ]; load byte memx145 to register64
movzx r14, r14b
adox r14, r12; loading flag
adox rbx, rdi
setc dil; spill CF x244 to reg (rdi)
clc;
movzx r15, r15b
adcx r15, r12; loading flag
adcx r10, rcx
movzx r15, dil; x245, copying x244 here, cause x244 is needed in a reg for other than x245, namely all: , x245, size: 1
lea r15, [ r15 + r11 ]
seto r14b; spill OF x182 to reg (r14)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rcx, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, rcx; loading flag
adox rbp, [ rsp + 0x210 ]
seto r9b; spill OF x317 to reg (r9)
dec r12; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx rax, al
adox rax, r12; loading flag
adox rbx, [ rsp + 0x190 ]
mov rcx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r13; x337, swapping with x4, which is currently in rdx
mulx rax, r11, rcx; x344, x343<- x337 * 0xffffffffffffffff
seto dil; spill OF x221 to reg (rdi)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, r12; loading flag
adox r10, [ rsp + 0x148 ]
mulx r8, r12, rcx; x342, x341<- x337 * 0xffffffffffffffff
mov rcx, [ rsp + 0x258 ]; x256, copying x243 here, cause x243 is needed in a reg for other than x256, namely all: , x256--x257, size: 1
adcx rcx, rbx
setc bl; spill CF x257 to reg (rbx)
mov [ rsp + 0x260 ], rcx; spilling x256 to mem
movzx rcx, byte [ rsp + 0x250 ]; load byte memx354 to register64
clc;
mov byte [ rsp + 0x268 ], r9b; spilling byte x317 to mem
mov r9, -0x1 ; moving imm to reg
adcx rcx, r9; loading flag
adcx r11, [ rsp + 0x1f8 ]
movzx rcx, dil; x222, copying x221 here, cause x221 is needed in a reg for other than x222, namely all: , x222, size: 1
movzx r14, r14b
lea rcx, [ rcx + r14 ]
seto r14b; spill OF x294 to reg (r14)
movzx rdi, byte [ rsp + 0x238 ]; load byte memx328 to register64
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
adox rdi, r9; loading flag
adox r10, rbp
mov rdi, 0xffffffffffffffff ; moving imm to reg
mulx rdx, rbp, rdi; x340, x339<- x337 * 0xffffffffffffffff
mov r9, [ rsp + 0x240 ]; load m64 x353 to register64
seto dil; spill OF x330 to reg (rdi)
mov [ rsp + 0x270 ], rdx; spilling x340 to mem
movzx rdx, byte [ rsp + 0x228 ]; load byte memx365 to register64
mov byte [ rsp + 0x278 ], r14b; spilling byte x294 to mem
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rdx, r14; loading flag
adox r9, [ rsp + 0x230 ]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x280 ], r9; spilling x366 to mem
mulx r14, r9, r13; x303, x302<- x4 * arg1[4]
adcx r12, rax
adox r11, r10
seto dl; spill OF x369 to reg (rdx)
mov rax, -0x1 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r10, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, r10; loading flag
adox rcx, r15
adcx rbp, r8
seto r15b; spill OF x259 to reg (r15)
movzx r8, byte [ rsp + 0x268 ]; load byte memx317 to register64
dec rax; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
adox r8, rax; loading flag
adox r9, [ rsp + 0x248 ]
mov r10, [ rsp + 0x150 ]; load m64 x282 to register64
setc r8b; spill CF x360 to reg (r8)
movzx rbx, byte [ rsp + 0x278 ]; load byte memx294 to register64
clc;
adcx rbx, rax; loading flag
adcx r10, [ rsp + 0x260 ]
mov rbx, [ rsp + 0x168 ]; x297, copying x284 here, cause x284 is needed in a reg for other than x297, namely all: , x297--x298, size: 1
adcx rbx, rcx
xchg rdx, r13; x4, swapping with x369, which is currently in rdx
mulx rdx, rcx, [ rsi + 0x28 ]; x301, x300<- x4 * arg1[5]
mov rax, [ rsi + 0x28 ]; load m64 x5 to register64
adox rcx, r14
movzx r14, r8b; x361, copying x360 here, cause x360 is needed in a reg for other than x361, namely all: , x361, size: 1
mov [ rsp + 0x288 ], r11; spilling x368 to mem
mov r11, [ rsp + 0x270 ]; load m64 x340 to register64
lea r14, [ r14 + r11 ]; r8/64 + m8
mov r11, 0x0 ; moving imm to reg
adox rdx, r11
dec r11; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx rdi, dil
adox rdi, r11; loading flag
adox r10, r9
movzx rdi, r15b; x299, copying x259 here, cause x259 is needed in a reg for other than x299, namely all: , x299, size: 1
mov r8, 0x0 ; moving imm to reg
adcx rdi, r8
adox rcx, rbx
clc;
movzx r13, r13b
adcx r13, r11; loading flag
adcx r10, r12
xchg rdx, rax; x5, swapping with x322, which is currently in rdx
mulx r12, r13, [ rsi + 0x0 ]; x388, x387<- x5 * arg1[0]
adox rax, rdi
mulx r15, r9, [ rsi + 0x8 ]; x386, x385<- x5 * arg1[1]
adcx rbp, rcx
mulx rbx, rdi, [ rsi + 0x18 ]; x382, x381<- x5 * arg1[3]
seto cl; spill OF x336 to reg (rcx)
mov r11, -0x3 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r13, [ rsp + 0x208 ]
adcx r14, rax
movzx rax, cl; x376, copying x336 here, cause x336 is needed in a reg for other than x376, namely all: , x376, size: 1
adcx rax, r8
mov rcx, 0x100000001 ; moving imm to reg
xchg rdx, rcx; 0x100000001, swapping with x5, which is currently in rdx
mulx r8, r11, r13; _, x414<- x400 * 0x100000001
clc;
adcx r9, r12
mov r8, 0xffffffff ; moving imm to reg
xchg rdx, r8; 0xffffffff, swapping with 0x100000001, which is currently in rdx
mulx r12, r8, r11; x427, x426<- x414 * 0xffffffff
xchg rdx, rcx; x5, swapping with 0xffffffff, which is currently in rdx
mov [ rsp + 0x290 ], rax; spilling x376 to mem
mulx rcx, rax, [ rsi + 0x10 ]; x384, x383<- x5 * arg1[2]
adcx rax, r15
adcx rdi, rcx
mov r15, 0xffffffff00000000 ; moving imm to reg
xchg rdx, r15; 0xffffffff00000000, swapping with x5, which is currently in rdx
mov [ rsp + 0x298 ], r14; spilling x374 to mem
mulx rcx, r14, r11; x425, x424<- x414 * 0xffffffff00000000
mov rdx, 0xfffffffffffffffe ; moving imm to reg
mov [ rsp + 0x2a0 ], rbp; spilling x372 to mem
mov [ rsp + 0x2a8 ], rbx; spilling x382 to mem
mulx rbp, rbx, r11; x423, x422<- x414 * 0xfffffffffffffffe
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x2b0 ], rdi; spilling x393 to mem
mov [ rsp + 0x2b8 ], r10; spilling x370 to mem
mulx rdi, r10, r11; x421, x420<- x414 * 0xffffffffffffffff
setc dl; spill CF x394 to reg (rdx)
clc;
adcx r8, r13
setc r8b; spill CF x440 to reg (r8)
clc;
adcx r14, r12
adcx rbx, rcx
mov r13, [ rsp + 0x280 ]; x402, copying x366 here, cause x366 is needed in a reg for other than x402, namely all: , x402--x403, size: 1
adox r13, r9
mov r9b, dl; preserving value of x394 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx r12, rcx, r15; x378, x377<- x5 * arg1[5]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x2c0 ], r12; spilling x378 to mem
mov [ rsp + 0x2c8 ], rcx; spilling x377 to mem
mulx r12, rcx, r11; x419, x418<- x414 * 0xffffffffffffffff
adcx r10, rbp
mov rbp, [ rsp + 0x288 ]; x404, copying x368 here, cause x368 is needed in a reg for other than x404, namely all: , x404--x405, size: 1
adox rbp, rax
adcx rcx, rdi
mov rax, [ rsp + 0x2b0 ]; load m64 x393 to register64
mov rdi, [ rsp + 0x2b8 ]; x406, copying x370 here, cause x370 is needed in a reg for other than x406, namely all: , x406--x407, size: 1
adox rdi, rax
setc al; spill CF x435 to reg (rax)
clc;
mov rdx, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, rdx; loading flag
adcx r13, r14
adcx rbx, rbp
setc r8b; spill CF x444 to reg (r8)
seto r14b; spill OF x407 to reg (r14)
mov rbp, r13; x454, copying x441 here, cause x441 is needed in a reg for other than x454, namely all: , x468, x454--x455, size: 2
mov rdx, 0xffffffff ; moving imm to reg
sub rbp, rdx
mov rdx, rbx; x456, copying x443 here, cause x443 is needed in a reg for other than x456, namely all: , x469, x456--x457, size: 2
mov [ rsp + 0x2d0 ], rbp; spilling x454 to mem
mov rbp, 0xffffffff00000000 ; moving imm to reg
sbb rdx, rbp
xchg rdx, r15; x5, swapping with x456, which is currently in rdx
mulx rdx, rbp, [ rsi + 0x20 ]; x380, x379<- x5 * arg1[4]
mov [ rsp + 0x2d8 ], r15; spilling x456 to mem
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r15, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, r15; loading flag
adox rdi, r10
setc r10b; spill CF x457 to reg (r10)
clc;
movzx r9, r9b
adcx r9, r15; loading flag
adcx rbp, [ rsp + 0x2a8 ]
setc r9b; spill CF x396 to reg (r9)
seto r8b; spill OF x446 to reg (r8)
movzx r15, r10b; x457, copying x457 here, cause x457 is needed in a reg for other than x457, namely all: , x458--x459, size: 1
add r15, -0x1
mov r10, rdi; x458, copying x445 here, cause x445 is needed in a reg for other than x458, namely all: , x470, x458--x459, size: 2
mov r15, 0xfffffffffffffffe ; moving imm to reg
sbb r10, r15
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r14, r14b
adox r14, r15; loading flag
adox rbp, [ rsp + 0x2a0 ]
mov r14, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r11; x414, swapping with x380, which is currently in rdx
mulx rdx, r15, r14; x417, x416<- x414 * 0xffffffffffffffff
setc r14b; spill CF x459 to reg (r14)
clc;
mov [ rsp + 0x2e0 ], r10; spilling x458 to mem
mov r10, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, r10; loading flag
adcx rbp, rcx
setc cl; spill CF x448 to reg (rcx)
clc;
movzx rax, al
adcx rax, r10; loading flag
adcx r12, r15
mov rax, 0x0 ; moving imm to reg
adcx rdx, rax
clc;
movzx r9, r9b
adcx r9, r10; loading flag
adcx r11, [ rsp + 0x2c8 ]
mov r8, [ rsp + 0x2c0 ]; x399, copying x378 here, cause x378 is needed in a reg for other than x399, namely all: , x399, size: 1
adcx r8, rax
mov r9, [ rsp + 0x298 ]; x410, copying x374 here, cause x374 is needed in a reg for other than x410, namely all: , x410--x411, size: 1
adox r9, r11
clc;
movzx rcx, cl
adcx rcx, r10; loading flag
adcx r9, r12
mov r15, [ rsp + 0x290 ]; x412, copying x376 here, cause x376 is needed in a reg for other than x412, namely all: , x412--x413, size: 1
adox r15, r8
adcx rdx, r15
setc cl; spill CF x452 to reg (rcx)
seto r12b; spill OF x413 to reg (r12)
movzx r11, r14b; x459, copying x459 here, cause x459 is needed in a reg for other than x459, namely all: , x460--x461, size: 1
add r11, -0x1
mov r11, rbp; x460, copying x447 here, cause x447 is needed in a reg for other than x460, namely all: , x471, x460--x461, size: 2
mov r14, 0xffffffffffffffff ; moving imm to reg
sbb r11, r14
mov r8, r9; x462, copying x449 here, cause x449 is needed in a reg for other than x462, namely all: , x462--x463, x472, size: 2
sbb r8, r14
mov r15, rdx; x464, copying x451 here, cause x451 is needed in a reg for other than x464, namely all: , x464--x465, x473, size: 2
sbb r15, r14
movzx rax, cl; x453, copying x452 here, cause x452 is needed in a reg for other than x453, namely all: , x453, size: 1
movzx r12, r12b
lea rax, [ rax + r12 ]
sbb rax, 0x00000000
mov rax, [ rsp + 0x2d8 ]; x469, copying x456 here, cause x456 is needed in a reg for other than x469, namely all: , x469, size: 1
cmovc rax, rbx; if CF, x469<- x443 (nzVar)
mov rbx, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rbx + 0x8 ], rax; out1[1] = x469
mov r12, [ rsp + 0x2e0 ]; x470, copying x458 here, cause x458 is needed in a reg for other than x470, namely all: , x470, size: 1
cmovc r12, rdi; if CF, x470<- x445 (nzVar)
mov rdi, [ rsp + 0x2d0 ]; x468, copying x454 here, cause x454 is needed in a reg for other than x468, namely all: , x468, size: 1
cmovc rdi, r13; if CF, x468<- x441 (nzVar)
cmovc r8, r9; if CF, x472<- x449 (nzVar)
mov [ rbx + 0x20 ], r8; out1[4] = x472
mov [ rbx + 0x0 ], rdi; out1[0] = x468
cmovc r15, rdx; if CF, x473<- x451 (nzVar)
mov [ rbx + 0x10 ], r12; out1[2] = x470
cmovc r11, rbp; if CF, x471<- x447 (nzVar)
mov [ rbx + 0x28 ], r15; out1[5] = x473
mov [ rbx + 0x18 ], r11; out1[3] = x471
mov rbx, [ rsp + 0x2e8 ]; restoring from stack
mov rbp, [ rsp + 0x2f0 ]; restoring from stack
mov r12, [ rsp + 0x2f8 ]; restoring from stack
mov r13, [ rsp + 0x300 ]; restoring from stack
mov r14, [ rsp + 0x308 ]; restoring from stack
mov r15, [ rsp + 0x310 ]; restoring from stack
add rsp, 0x318 
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; clocked at 4578 MHz
; first cyclecount 527.43, best 253.7674418604651, lastGood 273.5348837209302
; seed 2438481381420792 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3438199 ms / 60000 runs=> 57.30331666666667ms/run
; Time spent for assembling and measureing (initial batch_size=43, initial num_batches=101): 107934 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.031392598276016016
; number reverted permutation/ tried permutation: 21112 / 30152 =70.019%
; number reverted decision/ tried decision: 19029 / 29849 =63.751%