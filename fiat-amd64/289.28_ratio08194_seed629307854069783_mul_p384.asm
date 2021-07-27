SECTION .text
	GLOBAL mul_p384
mul_p384:
sub rsp, 0x398 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x368 ], rbx; saving to stack
mov [ rsp + 0x370 ], rbp; saving to stack
mov [ rsp + 0x378 ], r12; saving to stack
mov [ rsp + 0x380 ], r13; saving to stack
mov [ rsp + 0x388 ], r14; saving to stack
mov [ rsp + 0x390 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x6 to register64
mov r10, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x10 ]; saving arg2[2] in rdx.
mulx r11, rbx, rax; x14, x13<- x6 * arg2[2]
mov rdx, rax; x6 to rdx
mulx rax, rbp, [ r10 + 0x8 ]; x16, x15<- x6 * arg2[1]
mulx r12, r13, [ r10 + 0x0 ]; x18, x17<- x6 * arg2[0]
mov r14, 0x100000001 ; moving imm to reg
xchg rdx, r14; 0x100000001, swapping with x6, which is currently in rdx
mulx r15, rcx, r13; _, x30<- x17 * 0x100000001
mov r15, 0xfffffffffffffffe ; moving imm to reg
xchg rdx, rcx; x30, swapping with 0x100000001, which is currently in rdx
mulx r8, r9, r15; x39, x38<- x30 * 0xfffffffffffffffe
xor r15, r15
adox rbp, r12
mov r12, 0xffffffff ; moving imm to reg
mulx r15, rcx, r12; x43, x42<- x30 * 0xffffffff
mov r12, [ rsi + 0x8 ]; load m64 x1 to register64
adcx rcx, r13
mov rcx, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r13, rdi, rcx; x41, x40<- x30 * 0xffffffff00000000
mov rcx, rdx; preserving value of x30 into a new reg
mov rdx, [ r10 + 0x0 ]; saving arg2[0] in rdx.
mov [ rsp + 0x8 ], r11; spilling x14 to mem
mov [ rsp + 0x10 ], r8; spilling x39 to mem
mulx r11, r8, r12; x80, x79<- x1 * arg2[0]
mov [ rsp + 0x18 ], r14; spilling x6 to mem
setc r14b; spill CF x56 to reg (r14)
clc;
adcx rdi, r15
seto r15b; spill OF x20 to reg (r15)
mov [ rsp + 0x20 ], r11; spilling x80 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, r11; loading flag
adox rbp, rdi
adcx r9, r13
setc r14b; spill CF x47 to reg (r14)
clc;
adcx r8, rbp
mov r13, 0x100000001 ; moving imm to reg
mov rdx, r13; 0x100000001 to rdx
mulx r13, rdi, r8; _, x106<- x92 * 0x100000001
setc r13b; spill CF x93 to reg (r13)
clc;
movzx r15, r15b
adcx r15, r11; loading flag
adcx rax, rbx
mov rbx, rdx; preserving value of 0x100000001 into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mulx r15, rbp, r12; x78, x77<- x1 * arg2[1]
mov r11, 0xffffffff ; moving imm to reg
mov rdx, r11; 0xffffffff to rdx
mulx r11, rbx, rdi; x119, x118<- x106 * 0xffffffff
setc dl; spill CF x22 to reg (rdx)
clc;
adcx rbp, [ rsp + 0x20 ]
mov byte [ rsp + 0x28 ], dl; spilling byte x22 to mem
mov rdx, 0xffffffff00000000 ; moving imm to reg
mov byte [ rsp + 0x30 ], r14b; spilling byte x47 to mem
mov [ rsp + 0x38 ], r15; spilling x78 to mem
mulx r14, r15, rdi; x117, x116<- x106 * 0xffffffff00000000
adox r9, rax
seto al; spill OF x60 to reg (rax)
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, r8
mov rbx, [ rsi + 0x10 ]; load m64 x2 to register64
setc r8b; spill CF x82 to reg (r8)
clc;
movzx r13, r13b
adcx r13, rdx; loading flag
adcx r9, rbp
setc r13b; spill CF x95 to reg (r13)
clc;
adcx r15, r11
adox r15, r9
mov rdx, [ r10 + 0x0 ]; arg2[0] to rdx
mulx r11, rbp, rbx; x157, x156<- x2 * arg2[0]
setc r9b; spill CF x121 to reg (r9)
clc;
adcx rbp, r15
mov r15, 0x100000001 ; moving imm to reg
mov rdx, rbp; x169 to rdx
mov [ rsp + 0x40 ], r14; spilling x117 to mem
mulx rbp, r14, r15; _, x183<- x169 * 0x100000001
mov rbp, 0xffffffff00000000 ; moving imm to reg
xchg rdx, r14; x183, swapping with x169, which is currently in rdx
mov byte [ rsp + 0x48 ], r9b; spilling byte x121 to mem
mulx r15, r9, rbp; x194, x193<- x183 * 0xffffffff00000000
mov rbp, 0xfffffffffffffffe ; moving imm to reg
mov byte [ rsp + 0x50 ], r13b; spilling byte x95 to mem
mov byte [ rsp + 0x58 ], al; spilling byte x60 to mem
mulx r13, rax, rbp; x192, x191<- x183 * 0xfffffffffffffffe
mov rbp, 0xffffffff ; moving imm to reg
mov [ rsp + 0x60 ], r11; spilling x157 to mem
mov byte [ rsp + 0x68 ], r8b; spilling byte x82 to mem
mulx r11, r8, rbp; x196, x195<- x183 * 0xffffffff
seto bpl; spill OF x134 to reg (rbp)
mov [ rsp + 0x70 ], r8; spilling x195 to mem
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r9, r11
adox rax, r15
mov r15, 0xffffffffffffffff ; moving imm to reg
mulx r11, r8, r15; x190, x189<- x183 * 0xffffffffffffffff
mov r15, 0xfffffffffffffffe ; moving imm to reg
xchg rdx, rdi; x106, swapping with x183, which is currently in rdx
mov [ rsp + 0x78 ], rax; spilling x199 to mem
mov [ rsp + 0x80 ], r9; spilling x197 to mem
mulx rax, r9, r15; x115, x114<- x106 * 0xfffffffffffffffe
adox r8, r13
mov r13, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rdi; x183, swapping with x106, which is currently in rdx
mov [ rsp + 0x88 ], r8; spilling x201 to mem
mulx r15, r8, r13; x188, x187<- x183 * 0xffffffffffffffff
mov r13, rdx; preserving value of x183 into a new reg
mov rdx, [ r10 + 0x10 ]; saving arg2[2] in rdx.
mov [ rsp + 0x90 ], rax; spilling x115 to mem
mov byte [ rsp + 0x98 ], bpl; spilling byte x134 to mem
mulx rax, rbp, r12; x76, x75<- x1 * arg2[2]
mov [ rsp + 0xa0 ], rax; spilling x76 to mem
mov rax, 0xffffffffffffffff ; moving imm to reg
mov rdx, rax; 0xffffffffffffffff to rdx
mov [ rsp + 0xa8 ], r9; spilling x114 to mem
mulx rax, r9, rcx; x37, x36<- x30 * 0xffffffffffffffff
mov [ rsp + 0xb0 ], rax; spilling x37 to mem
mulx r13, rax, r13; x186, x185<- x183 * 0xffffffffffffffff
adox r8, r11
setc r11b; spill CF x170 to reg (r11)
movzx rdx, byte [ rsp + 0x68 ]; load byte memx82 to register64
clc;
mov [ rsp + 0xb8 ], r8; spilling x203 to mem
mov r8, -0x1 ; moving imm to reg
adcx rdx, r8; loading flag
adcx rbp, [ rsp + 0x38 ]
adox rax, r15
mov rdx, [ r10 + 0x8 ]; arg2[1] to rdx
mulx r15, r8, rbx; x155, x154<- x2 * arg2[1]
mov [ rsp + 0xc0 ], rax; spilling x205 to mem
setc al; spill CF x84 to reg (rax)
clc;
adcx r8, [ rsp + 0x60 ]
mov rdx, [ rsp + 0x18 ]; x6 to rdx
mov [ rsp + 0xc8 ], r15; spilling x155 to mem
mov byte [ rsp + 0xd0 ], al; spilling byte x84 to mem
mulx r15, rax, [ r10 + 0x18 ]; x12, x11<- x6 * arg2[3]
mov [ rsp + 0xd8 ], r8; spilling x158 to mem
mov byte [ rsp + 0xe0 ], r11b; spilling byte x170 to mem
mulx r8, r11, [ r10 + 0x20 ]; x10, x9<- x6 * arg2[4]
mov [ rsp + 0xe8 ], r8; spilling x10 to mem
mov r8, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rcx; x30, swapping with x6, which is currently in rdx
mov [ rsp + 0xf0 ], r11; spilling x9 to mem
mov [ rsp + 0xf8 ], r15; spilling x12 to mem
mulx r11, r15, r8; x35, x34<- x30 * 0xffffffffffffffff
setc r8b; spill CF x159 to reg (r8)
clc;
adcx r14, [ rsp + 0x70 ]
mov r14, 0x0 ; moving imm to reg
adox r13, r14
movzx r14, byte [ rsp + 0x30 ]; load byte memx47 to register64
mov [ rsp + 0x100 ], r13; spilling x207 to mem
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r14, r13; loading flag
adox r9, [ rsp + 0x10 ]
setc r14b; spill CF x209 to reg (r14)
movzx r13, byte [ rsp + 0x28 ]; load byte memx22 to register64
clc;
mov byte [ rsp + 0x108 ], r8b; spilling byte x159 to mem
mov r8, -0x1 ; moving imm to reg
adcx r13, r8; loading flag
adcx rax, [ rsp + 0x8 ]
seto r13b; spill OF x49 to reg (r13)
movzx r8, byte [ rsp + 0x58 ]; load byte memx60 to register64
mov [ rsp + 0x110 ], r11; spilling x35 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
adox r8, r11; loading flag
adox rax, r9
mov r8, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rdi; x106, swapping with x30, which is currently in rdx
mulx r9, r11, r8; x113, x112<- x106 * 0xffffffffffffffff
seto r8b; spill OF x62 to reg (r8)
mov [ rsp + 0x118 ], r9; spilling x113 to mem
movzx r9, byte [ rsp + 0x50 ]; load byte memx95 to register64
mov byte [ rsp + 0x120 ], r14b; spilling byte x209 to mem
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r9, r14; loading flag
adox rax, rbp
mov r9, [ rsp + 0xa8 ]; load m64 x114 to register64
seto bpl; spill OF x97 to reg (rbp)
movzx r14, byte [ rsp + 0x48 ]; load byte memx121 to register64
mov byte [ rsp + 0x128 ], r8b; spilling byte x62 to mem
mov r8, 0x0 ; moving imm to reg
dec r8; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r14, r8; loading flag
adox r9, [ rsp + 0x40 ]
seto r14b; spill OF x123 to reg (r14)
movzx r8, byte [ rsp + 0x98 ]; load byte memx134 to register64
mov byte [ rsp + 0x130 ], bpl; spilling byte x97 to mem
mov rbp, -0x1 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
adox r8, rbp; loading flag
adox rax, r9
mov r8, [ rsp + 0xf0 ]; load m64 x9 to register64
mov r9, [ rsp + 0xf8 ]; x25, copying x12 here, cause x12 is needed in a reg for other than x25, namely all: , x25--x26, size: 1
adcx r9, r8
xchg rdx, r12; x1, swapping with x106, which is currently in rdx
mulx r8, rbp, [ r10 + 0x18 ]; x74, x73<- x1 * arg2[3]
mov [ rsp + 0x138 ], r8; spilling x74 to mem
seto r8b; spill OF x136 to reg (r8)
mov [ rsp + 0x140 ], rbp; spilling x73 to mem
mov rbp, -0x1 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, rbp; loading flag
adox r15, [ rsp + 0xb0 ]
setc r13b; spill CF x26 to reg (r13)
movzx rbp, byte [ rsp + 0xe0 ]; load byte memx170 to register64
clc;
mov byte [ rsp + 0x148 ], r8b; spilling byte x136 to mem
mov r8, -0x1 ; moving imm to reg
adcx rbp, r8; loading flag
adcx rax, [ rsp + 0xd8 ]
seto bpl; spill OF x51 to reg (rbp)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, r8; loading flag
adox r11, [ rsp + 0x90 ]
seto r14b; spill OF x125 to reg (r14)
movzx r8, byte [ rsp + 0x128 ]; load byte memx62 to register64
mov [ rsp + 0x150 ], rsi; spilling arg1 to mem
mov rsi, 0x0 ; moving imm to reg
dec rsi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r8, rsi; loading flag
adox r9, r15
mulx r8, r15, [ r10 + 0x20 ]; x72, x71<- x1 * arg2[4]
setc sil; spill CF x172 to reg (rsi)
mov [ rsp + 0x158 ], r8; spilling x72 to mem
movzx r8, byte [ rsp + 0x120 ]; load byte memx209 to register64
clc;
mov byte [ rsp + 0x160 ], r14b; spilling byte x125 to mem
mov r14, -0x1 ; moving imm to reg
adcx r8, r14; loading flag
adcx rax, [ rsp + 0x80 ]
mov r8, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rdi; x30, swapping with x1, which is currently in rdx
mulx rdx, r14, r8; x33, x32<- x30 * 0xffffffffffffffff
mov r8, [ rsp + 0x140 ]; load m64 x73 to register64
mov [ rsp + 0x168 ], rax; spilling x210 to mem
seto al; spill OF x64 to reg (rax)
mov byte [ rsp + 0x170 ], sil; spilling byte x172 to mem
movzx rsi, byte [ rsp + 0xd0 ]; load byte memx84 to register64
mov [ rsp + 0x178 ], rdx; spilling x33 to mem
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
adox rsi, rdx; loading flag
adox r8, [ rsp + 0xa0 ]
mov rsi, [ rsp + 0x138 ]; x87, copying x74 here, cause x74 is needed in a reg for other than x87, namely all: , x87--x88, size: 1
adox rsi, r15
seto r15b; spill OF x88 to reg (r15)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, rdx; loading flag
adox r14, [ rsp + 0x110 ]
seto bpl; spill OF x53 to reg (rbp)
movzx rdx, byte [ rsp + 0x130 ]; load byte memx97 to register64
mov byte [ rsp + 0x180 ], r15b; spilling byte x88 to mem
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rdx, r15; loading flag
adox r9, r8
mov rdx, [ r10 + 0x28 ]; arg2[5] to rdx
mulx rcx, r8, rcx; x8, x7<- x6 * arg2[5]
setc r15b; spill CF x211 to reg (r15)
mov [ rsp + 0x188 ], rcx; spilling x8 to mem
movzx rcx, byte [ rsp + 0x148 ]; load byte memx136 to register64
clc;
mov byte [ rsp + 0x190 ], bpl; spilling byte x53 to mem
mov rbp, -0x1 ; moving imm to reg
adcx rcx, rbp; loading flag
adcx r9, r11
setc cl; spill CF x138 to reg (rcx)
clc;
movzx r13, r13b
adcx r13, rbp; loading flag
adcx r8, [ rsp + 0xe8 ]
mov rdx, rbx; x2 to rdx
mulx rbx, r13, [ r10 + 0x10 ]; x153, x152<- x2 * arg2[2]
setc r11b; spill CF x28 to reg (r11)
clc;
movzx rax, al
adcx rax, rbp; loading flag
adcx r8, r14
mulx rax, r14, [ r10 + 0x18 ]; x151, x150<- x2 * arg2[3]
adox rsi, r8
seto r8b; spill OF x101 to reg (r8)
movzx rbp, byte [ rsp + 0x108 ]; load byte memx159 to register64
mov [ rsp + 0x198 ], rax; spilling x151 to mem
mov rax, -0x1 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rax, -0x1 ; moving imm to reg
adox rbp, rax; loading flag
adox r13, [ rsp + 0xc8 ]
mov rbp, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbp; 0xffffffffffffffff, swapping with x2, which is currently in rdx
mov byte [ rsp + 0x1a0 ], r15b; spilling byte x211 to mem
mulx rax, r15, r12; x111, x110<- x106 * 0xffffffffffffffff
adox r14, rbx
setc bl; spill CF x66 to reg (rbx)
movzx rdx, byte [ rsp + 0x160 ]; load byte memx125 to register64
clc;
mov [ rsp + 0x1a8 ], rax; spilling x111 to mem
mov rax, -0x1 ; moving imm to reg
adcx rdx, rax; loading flag
adcx r15, [ rsp + 0x118 ]
movzx rdx, byte [ rsp + 0x190 ]; x54, copying x53 here, cause x53 is needed in a reg for other than x54, namely all: , x54, size: 1
mov rax, [ rsp + 0x178 ]; load m64 x33 to register64
lea rdx, [ rdx + rax ]; r8/64 + m8
setc al; spill CF x127 to reg (rax)
clc;
mov [ rsp + 0x1b0 ], r14; spilling x162 to mem
mov r14, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, r14; loading flag
adcx rsi, r15
movzx rcx, r11b; x29, copying x28 here, cause x28 is needed in a reg for other than x29, namely all: , x29, size: 1
mov r15, [ rsp + 0x188 ]; load m64 x8 to register64
lea rcx, [ rcx + r15 ]; r8/64 + m8
xchg rdx, rdi; x1, swapping with x54, which is currently in rdx
mulx rdx, r15, [ r10 + 0x28 ]; x70, x69<- x1 * arg2[5]
setc r11b; spill CF x140 to reg (r11)
clc;
movzx rbx, bl
adcx rbx, r14; loading flag
adcx rcx, rdi
setc bl; spill CF x68 to reg (rbx)
movzx rdi, byte [ rsp + 0x180 ]; load byte memx88 to register64
clc;
adcx rdi, r14; loading flag
adcx r15, [ rsp + 0x158 ]
seto dil; spill OF x163 to reg (rdi)
movzx r14, byte [ rsp + 0x170 ]; load byte memx172 to register64
mov byte [ rsp + 0x1b8 ], r11b; spilling byte x140 to mem
mov r11, 0x0 ; moving imm to reg
dec r11; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r14, r11; loading flag
adox r9, r13
setc r14b; spill CF x90 to reg (r14)
clc;
movzx r8, r8b
adcx r8, r11; loading flag
adcx rcx, r15
seto r8b; spill OF x174 to reg (r8)
movzx r13, byte [ rsp + 0x1a0 ]; load byte memx211 to register64
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
adox r13, r15; loading flag
adox r9, [ rsp + 0x78 ]
setc r13b; spill CF x103 to reg (r13)
clc;
movzx r8, r8b
adcx r8, r15; loading flag
adcx rsi, [ rsp + 0x1b0 ]
movzx r8, r14b; x91, copying x90 here, cause x90 is needed in a reg for other than x91, namely all: , x91, size: 1
lea r8, [ r8 + rdx ]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mulx r12, r14, r12; x109, x108<- x106 * 0xffffffffffffffff
setc r11b; spill CF x176 to reg (r11)
clc;
movzx rax, al
adcx rax, r15; loading flag
adcx r14, [ rsp + 0x1a8 ]
mov rax, 0x0 ; moving imm to reg
adcx r12, rax
mov rax, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ r10 + 0x20 ]; saving arg2[4] in rdx.
mov [ rsp + 0x1c0 ], r9; spilling x212 to mem
mulx r15, r9, rbp; x149, x148<- x2 * arg2[4]
mov rdx, rbp; x2 to rdx
mulx rdx, rbp, [ r10 + 0x28 ]; x147, x146<- x2 * arg2[5]
clc;
mov rax, -0x1 ; moving imm to reg
movzx rbx, bl
movzx r13, r13b
adcx r13, rax; loading flag
adcx r8, rbx
mov rbx, [ rsp + 0x88 ]; x214, copying x201 here, cause x201 is needed in a reg for other than x214, namely all: , x214--x215, size: 1
adox rbx, rsi
seto r13b; spill OF x215 to reg (r13)
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rsi, -0x1 ; moving imm to reg
movzx rdi, dil
adox rdi, rsi; loading flag
adox r9, [ rsp + 0x198 ]
adox rbp, r15
seto dil; spill OF x167 to reg (rdi)
movzx r15, byte [ rsp + 0x1b8 ]; load byte memx140 to register64
inc rsi; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov rax, -0x1 ; moving imm to reg
adox r15, rax; loading flag
adox rcx, r14
adox r12, r8
mov r15, [ rsp + 0x150 ]; load m64 arg1 to register64
mov r14, [ r15 + 0x18 ]; load m64 x3 to register64
seto r8b; spill OF x144 to reg (r8)
dec rsi; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx r11, r11b
adox r11, rsi; loading flag
adox rcx, r9
movzx rax, r8b; x145, copying x144 here, cause x144 is needed in a reg for other than x145, namely all: , x145, size: 1
mov r11, 0x0 ; moving imm to reg
adcx rax, r11
xchg rdx, r14; x3, swapping with x147, which is currently in rdx
mulx r9, r8, [ r10 + 0x18 ]; x228, x227<- x3 * arg2[3]
clc;
movzx r13, r13b
adcx r13, rsi; loading flag
adcx rcx, [ rsp + 0xb8 ]
mulx r13, r11, [ r10 + 0x8 ]; x232, x231<- x3 * arg2[1]
movzx rsi, dil; x168, copying x167 here, cause x167 is needed in a reg for other than x168, namely all: , x168, size: 1
lea rsi, [ rsi + r14 ]
adox rbp, r12
mov r14, [ rsp + 0xc0 ]; x218, copying x205 here, cause x205 is needed in a reg for other than x218, namely all: , x218--x219, size: 1
adcx r14, rbp
mulx rdi, r12, [ r10 + 0x20 ]; x226, x225<- x3 * arg2[4]
adox rsi, rax
mulx rax, rbp, [ r10 + 0x10 ]; x230, x229<- x3 * arg2[2]
mov [ rsp + 0x1c8 ], r14; spilling x218 to mem
mov r14, [ rsp + 0x100 ]; x220, copying x207 here, cause x207 is needed in a reg for other than x220, namely all: , x220--x221, size: 1
adcx r14, rsi
mov [ rsp + 0x1d0 ], r14; spilling x220 to mem
mulx rsi, r14, [ r10 + 0x0 ]; x234, x233<- x3 * arg2[0]
mov [ rsp + 0x1d8 ], rcx; spilling x216 to mem
seto cl; spill OF x222 to reg (rcx)
adc cl, 0x0
movzx rcx, cl
adox r11, rsi
mulx rdx, rsi, [ r10 + 0x28 ]; x224, x223<- x3 * arg2[5]
adox rbp, r13
adox r8, rax
mov r13, [ r15 + 0x28 ]; load m64 x5 to register64
xchg rdx, r13; x5, swapping with x224, which is currently in rdx
mov byte [ rsp + 0x1e0 ], cl; spilling byte x222 to mem
mulx rax, rcx, [ r10 + 0x28 ]; x378, x377<- x5 * arg2[5]
mov [ rsp + 0x1e8 ], r8; spilling x239 to mem
mov [ rsp + 0x1f0 ], rbp; spilling x237 to mem
mulx r8, rbp, [ r10 + 0x8 ]; x386, x385<- x5 * arg2[1]
adox r12, r9
adox rsi, rdi
mulx r9, rdi, [ r10 + 0x0 ]; x388, x387<- x5 * arg2[0]
mov [ rsp + 0x1f8 ], rsi; spilling x243 to mem
mov [ rsp + 0x200 ], r12; spilling x241 to mem
mulx rsi, r12, [ r10 + 0x20 ]; x380, x379<- x5 * arg2[4]
mov [ rsp + 0x208 ], rdi; spilling x387 to mem
mov [ rsp + 0x210 ], rbx; spilling x214 to mem
mulx rdi, rbx, [ r10 + 0x18 ]; x382, x381<- x5 * arg2[3]
adcx rbp, r9
mov r9, 0x0 ; moving imm to reg
adox r13, r9
mulx rdx, r9, [ r10 + 0x10 ]; x384, x383<- x5 * arg2[2]
adcx r9, r8
mov r8, [ r15 + 0x20 ]; load m64 x4 to register64
mov [ rsp + 0x218 ], r13; spilling x245 to mem
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, [ rsp + 0x168 ]
adcx rbx, rdx
adcx r12, rdi
mov rdx, r8; x4 to rdx
mulx r8, rdi, [ r10 + 0x20 ]; x303, x302<- x4 * arg2[4]
mov [ rsp + 0x220 ], r12; spilling x395 to mem
mulx r13, r12, [ r10 + 0x10 ]; x307, x306<- x4 * arg2[2]
mov [ rsp + 0x228 ], rbx; spilling x393 to mem
mov [ rsp + 0x230 ], r9; spilling x391 to mem
mulx rbx, r9, [ r10 + 0x18 ]; x305, x304<- x4 * arg2[3]
adcx rcx, rsi
mov rsi, [ rsp + 0x1c0 ]; x248, copying x212 here, cause x212 is needed in a reg for other than x248, namely all: , x248--x249, size: 1
adox rsi, r11
mov [ rsp + 0x238 ], rcx; spilling x397 to mem
mulx r11, rcx, [ r10 + 0x8 ]; x309, x308<- x4 * arg2[1]
mov [ rsp + 0x240 ], rbp; spilling x389 to mem
mov [ rsp + 0x248 ], rsi; spilling x248 to mem
mulx rbp, rsi, [ r10 + 0x0 ]; x311, x310<- x4 * arg2[0]
mov [ rsp + 0x250 ], rsi; spilling x310 to mem
setc sil; spill CF x398 to reg (rsi)
clc;
adcx rcx, rbp
mulx rdx, rbp, [ r10 + 0x28 ]; x301, x300<- x4 * arg2[5]
mov [ rsp + 0x258 ], rcx; spilling x312 to mem
movzx rcx, sil; x399, copying x398 here, cause x398 is needed in a reg for other than x399, namely all: , x399, size: 1
lea rcx, [ rcx + rax ]
adcx r12, r11
mov rax, [ rsp + 0x1f0 ]; load m64 x237 to register64
mov rsi, [ rsp + 0x210 ]; x250, copying x214 here, cause x214 is needed in a reg for other than x250, namely all: , x250--x251, size: 1
adox rsi, rax
mov rax, 0x100000001 ; moving imm to reg
xchg rdx, rax; 0x100000001, swapping with x301, which is currently in rdx
mov [ rsp + 0x260 ], rcx; spilling x399 to mem
mulx r11, rcx, r14; _, x260<- x246 * 0x100000001
mov r11, 0xffffffff ; moving imm to reg
xchg rdx, r11; 0xffffffff, swapping with 0x100000001, which is currently in rdx
mov [ rsp + 0x268 ], r12; spilling x314 to mem
mulx r11, r12, rcx; x273, x272<- x260 * 0xffffffff
adcx r9, r13
mov r13, 0xffffffff00000000 ; moving imm to reg
xchg rdx, rcx; x260, swapping with 0xffffffff, which is currently in rdx
mov [ rsp + 0x270 ], r9; spilling x316 to mem
mulx rcx, r9, r13; x271, x270<- x260 * 0xffffffff00000000
adcx rdi, rbx
adcx rbp, r8
mov r8, 0x0 ; moving imm to reg
adcx rax, r8
clc;
adcx r9, r11
mov rbx, 0xfffffffffffffffe ; moving imm to reg
mulx r11, r8, rbx; x269, x268<- x260 * 0xfffffffffffffffe
adcx r8, rcx
seto cl; spill OF x251 to reg (rcx)
mov rbx, -0x2 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, r14
mov r12, [ rsp + 0x248 ]; x287, copying x248 here, cause x248 is needed in a reg for other than x287, namely all: , x287--x288, size: 1
adox r12, r9
adox r8, rsi
setc r14b; spill CF x277 to reg (r14)
clc;
adcx r12, [ rsp + 0x250 ]
mov rsi, [ rsp + 0x258 ]; x325, copying x312 here, cause x312 is needed in a reg for other than x325, namely all: , x325--x326, size: 1
adcx rsi, r8
mov r9, [ rsp + 0x1e8 ]; load m64 x239 to register64
setc r8b; spill CF x326 to reg (r8)
clc;
movzx rcx, cl
adcx rcx, rbx; loading flag
adcx r9, [ rsp + 0x1d8 ]
mov rcx, 0xffffffffffffffff ; moving imm to reg
mulx rbx, r13, rcx; x267, x266<- x260 * 0xffffffffffffffff
mov rcx, 0x100000001 ; moving imm to reg
xchg rdx, r12; x323, swapping with x260, which is currently in rdx
mov [ rsp + 0x278 ], rax; spilling x322 to mem
mov [ rsp + 0x280 ], rbp; spilling x320 to mem
mulx rax, rbp, rcx; _, x337<- x323 * 0x100000001
mov rax, 0xffffffff00000000 ; moving imm to reg
xchg rdx, rax; 0xffffffff00000000, swapping with x323, which is currently in rdx
mov [ rsp + 0x288 ], rdi; spilling x318 to mem
mulx rcx, rdi, rbp; x348, x347<- x337 * 0xffffffff00000000
mov rdx, 0xffffffff ; moving imm to reg
mov [ rsp + 0x290 ], rbx; spilling x267 to mem
mov byte [ rsp + 0x298 ], r8b; spilling byte x326 to mem
mulx rbx, r8, rbp; x350, x349<- x337 * 0xffffffff
mov rdx, 0xfffffffffffffffe ; moving imm to reg
mov [ rsp + 0x2a0 ], r9; spilling x252 to mem
mov [ rsp + 0x2a8 ], rsi; spilling x325 to mem
mulx r9, rsi, rbp; x346, x345<- x337 * 0xfffffffffffffffe
seto dl; spill OF x290 to reg (rdx)
mov [ rsp + 0x2b0 ], r9; spilling x346 to mem
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, rax
setc r8b; spill CF x253 to reg (r8)
clc;
adcx rdi, rbx
seto al; spill OF x363 to reg (rax)
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, rbx; loading flag
adox r11, r13
adcx rsi, rcx
setc r14b; spill CF x354 to reg (r14)
clc;
movzx rax, al
adcx rax, rbx; loading flag
adcx rdi, [ rsp + 0x2a8 ]
setc r13b; spill CF x365 to reg (r13)
clc;
adcx rdi, [ rsp + 0x208 ]
mov rcx, 0x100000001 ; moving imm to reg
xchg rdx, rcx; 0x100000001, swapping with x290, which is currently in rdx
mulx rax, r9, rdi; _, x414<- x400 * 0x100000001
setc al; spill CF x401 to reg (rax)
clc;
movzx rcx, cl
adcx rcx, rbx; loading flag
adcx r11, [ rsp + 0x2a0 ]
mov rcx, 0xffffffff00000000 ; moving imm to reg
xchg rdx, rcx; 0xffffffff00000000, swapping with 0x100000001, which is currently in rdx
mulx rbx, rcx, r9; x425, x424<- x414 * 0xffffffff00000000
mov rdx, 0xffffffff ; moving imm to reg
mov [ rsp + 0x2b8 ], rbx; spilling x425 to mem
mov byte [ rsp + 0x2c0 ], r14b; spilling byte x354 to mem
mulx rbx, r14, r9; x427, x426<- x414 * 0xffffffff
setc dl; spill CF x292 to reg (rdx)
clc;
adcx r14, rdi
mov r14, [ rsp + 0x200 ]; load m64 x241 to register64
setc dil; spill CF x440 to reg (rdi)
clc;
mov byte [ rsp + 0x2c8 ], dl; spilling byte x292 to mem
mov rdx, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, rdx; loading flag
adcx r14, [ rsp + 0x1c8 ]
setc r8b; spill CF x255 to reg (r8)
movzx rdx, byte [ rsp + 0x298 ]; load byte memx326 to register64
clc;
mov [ rsp + 0x2d0 ], r14; spilling x254 to mem
mov r14, -0x1 ; moving imm to reg
adcx rdx, r14; loading flag
adcx r11, [ rsp + 0x268 ]
seto dl; spill OF x279 to reg (rdx)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rcx, rbx
setc bl; spill CF x328 to reg (rbx)
clc;
mov r14, -0x1 ; moving imm to reg
movzx r13, r13b
adcx r13, r14; loading flag
adcx r11, rsi
mov rsi, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r12; x260, swapping with x279, which is currently in rdx
mulx r13, r14, rsi; x265, x264<- x260 * 0xffffffffffffffff
seto sil; spill OF x429 to reg (rsi)
mov byte [ rsp + 0x2d8 ], r8b; spilling byte x255 to mem
mov r8, 0x0 ; moving imm to reg
dec r8; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rax, al
adox rax, r8; loading flag
adox r11, [ rsp + 0x240 ]
setc al; spill CF x367 to reg (rax)
clc;
movzx r12, r12b
adcx r12, r8; loading flag
adcx r14, [ rsp + 0x290 ]
setc r12b; spill CF x281 to reg (r12)
clc;
movzx rdi, dil
adcx rdi, r8; loading flag
adcx r11, rcx
seto dil; spill OF x403 to reg (rdi)
movzx rcx, byte [ rsp + 0x2c8 ]; load byte memx292 to register64
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
adox rcx, r8; loading flag
adox r14, [ rsp + 0x2d0 ]
setc cl; spill CF x442 to reg (rcx)
clc;
movzx rbx, bl
adcx rbx, r8; loading flag
adcx r14, [ rsp + 0x270 ]
setc bl; spill CF x330 to reg (rbx)
seto r8b; spill OF x294 to reg (r8)
mov byte [ rsp + 0x2e0 ], cl; spilling byte x442 to mem
mov rcx, r11; x454, copying x441 here, cause x441 is needed in a reg for other than x454, namely all: , x468, x454--x455, size: 2
mov byte [ rsp + 0x2e8 ], sil; spilling byte x429 to mem
mov rsi, 0xffffffff ; moving imm to reg
sub rcx, rsi
mov rsi, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x2f0 ], rcx; spilling x454 to mem
mulx rdx, rcx, rsi; x263, x262<- x260 * 0xffffffffffffffff
xchg rdx, rsi; 0xffffffffffffffff, swapping with x263, which is currently in rdx
mov byte [ rsp + 0x2f8 ], bl; spilling byte x330 to mem
mov byte [ rsp + 0x300 ], r8b; spilling byte x294 to mem
mulx rbx, r8, rbp; x344, x343<- x337 * 0xffffffffffffffff
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r12, r12b
adox r12, rdx; loading flag
adox r13, rcx
mov r12, 0x0 ; moving imm to reg
adox rsi, r12
movzx rcx, byte [ rsp + 0x2c0 ]; load byte memx354 to register64
inc rdx; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov r12, -0x1 ; moving imm to reg
adox rcx, r12; loading flag
adox r8, [ rsp + 0x2b0 ]
setc cl; spill CF x455 to reg (rcx)
clc;
movzx rax, al
adcx rax, r12; loading flag
adcx r14, r8
seto al; spill OF x356 to reg (rax)
dec rdx; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx rdi, dil
adox rdi, rdx; loading flag
adox r14, [ rsp + 0x230 ]
mov r12, 0xffffffffffffffff ; moving imm to reg
mov rdx, rbp; x337 to rdx
mulx rbp, rdi, r12; x342, x341<- x337 * 0xffffffffffffffff
mov r8, 0xfffffffffffffffe ; moving imm to reg
xchg rdx, r9; x414, swapping with x337, which is currently in rdx
mov [ rsp + 0x308 ], rbp; spilling x342 to mem
mulx r12, rbp, r8; x423, x422<- x414 * 0xfffffffffffffffe
setc r8b; spill CF x369 to reg (r8)
clc;
mov [ rsp + 0x310 ], rsi; spilling x284 to mem
mov rsi, -0x1 ; moving imm to reg
movzx rax, al
adcx rax, rsi; loading flag
adcx rbx, rdi
setc al; spill CF x358 to reg (rax)
movzx rdi, byte [ rsp + 0x2e8 ]; load byte memx429 to register64
clc;
adcx rdi, rsi; loading flag
adcx rbp, [ rsp + 0x2b8 ]
setc dil; spill CF x431 to reg (rdi)
movzx rsi, byte [ rsp + 0x2e0 ]; load byte memx442 to register64
clc;
mov byte [ rsp + 0x318 ], al; spilling byte x358 to mem
mov rax, -0x1 ; moving imm to reg
adcx rsi, rax; loading flag
adcx r14, rbp
mov rsi, [ rsp + 0x1f8 ]; load m64 x243 to register64
setc bpl; spill CF x444 to reg (rbp)
movzx rax, byte [ rsp + 0x2d8 ]; load byte memx255 to register64
clc;
mov [ rsp + 0x320 ], rbx; spilling x357 to mem
mov rbx, -0x1 ; moving imm to reg
adcx rax, rbx; loading flag
adcx rsi, [ rsp + 0x1d0 ]
setc al; spill CF x257 to reg (rax)
seto bl; spill OF x405 to reg (rbx)
mov byte [ rsp + 0x328 ], bpl; spilling byte x444 to mem
movzx rbp, cl; x455, copying x455 here, cause x455 is needed in a reg for other than x455, namely all: , x456--x457, size: 1
add rbp, -0x1
mov rbp, r14; x456, copying x443 here, cause x443 is needed in a reg for other than x456, namely all: , x469, x456--x457, size: 2
mov rcx, 0xffffffff00000000 ; moving imm to reg
sbb rbp, rcx
mov rcx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x330 ], rbp; spilling x456 to mem
mov byte [ rsp + 0x338 ], bl; spilling byte x405 to mem
mulx rbp, rbx, rcx; x421, x420<- x414 * 0xffffffffffffffff
movzx rcx, byte [ rsp + 0x300 ]; load byte memx294 to register64
mov [ rsp + 0x340 ], rbp; spilling x421 to mem
mov rbp, -0x1 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
adox rcx, rbp; loading flag
adox rsi, r13
movzx rcx, byte [ rsp + 0x1e0 ]; load byte memx222 to register64
setc r13b; spill CF x457 to reg (r13)
clc;
movzx rax, al
adcx rax, rbp; loading flag
adcx rcx, [ rsp + 0x218 ]
seto al; spill OF x296 to reg (rax)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx rdi, dil
adox rdi, rbp; loading flag
adox r12, rbx
seto dil; spill OF x433 to reg (rdi)
movzx rbx, byte [ rsp + 0x2f8 ]; load byte memx330 to register64
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
adox rbx, rbp; loading flag
adox rsi, [ rsp + 0x288 ]
setc bl; spill CF x259 to reg (rbx)
clc;
movzx r8, r8b
adcx r8, rbp; loading flag
adcx rsi, [ rsp + 0x320 ]
seto r8b; spill OF x332 to reg (r8)
movzx rbp, byte [ rsp + 0x338 ]; load byte memx405 to register64
mov byte [ rsp + 0x348 ], r13b; spilling byte x457 to mem
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbp, r13; loading flag
adox rsi, [ rsp + 0x228 ]
seto bpl; spill OF x407 to reg (rbp)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
movzx rax, al
adox rax, r13; loading flag
adox rcx, [ rsp + 0x310 ]
movzx rax, bl; x299, copying x259 here, cause x259 is needed in a reg for other than x299, namely all: , x299, size: 1
mov r13, 0x0 ; moving imm to reg
adox rax, r13
dec r13; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r8, r8b
adox r8, r13; loading flag
adox rcx, [ rsp + 0x280 ]
mov rbx, [ rsp + 0x278 ]; x335, copying x322 here, cause x322 is needed in a reg for other than x335, namely all: , x335--x336, size: 1
adox rbx, rax
mov r8, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r8; 0xffffffffffffffff, swapping with x414, which is currently in rdx
mulx r9, rax, r9; x340, x339<- x337 * 0xffffffffffffffff
seto r13b; spill OF x336 to reg (r13)
movzx rdx, byte [ rsp + 0x318 ]; load byte memx358 to register64
mov [ rsp + 0x350 ], rbx; spilling x335 to mem
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rdx, rbx; loading flag
adox rax, [ rsp + 0x308 ]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov byte [ rsp + 0x358 ], r13b; spilling byte x336 to mem
mulx rbx, r13, r8; x417, x416<- x414 * 0xffffffffffffffff
adcx rax, rcx
seto cl; spill OF x360 to reg (rcx)
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbp, bpl
adox rbp, rdx; loading flag
adox rax, [ rsp + 0x220 ]
mov rbp, 0xffffffffffffffff ; moving imm to reg
mov rdx, r8; x414 to rdx
mulx rdx, r8, rbp; x419, x418<- x414 * 0xffffffffffffffff
setc bpl; spill CF x373 to reg (rbp)
clc;
mov [ rsp + 0x360 ], rbx; spilling x417 to mem
mov rbx, -0x1 ; moving imm to reg
movzx rdi, dil
adcx rdi, rbx; loading flag
adcx r8, [ rsp + 0x340 ]
movzx rdi, cl; x361, copying x360 here, cause x360 is needed in a reg for other than x361, namely all: , x361, size: 1
lea rdi, [ rdi + r9 ]
seto r9b; spill OF x409 to reg (r9)
movzx rcx, byte [ rsp + 0x328 ]; load byte memx444 to register64
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
adox rcx, rbx; loading flag
adox rsi, r12
adcx r13, rdx
adox r8, rax
setc cl; spill CF x437 to reg (rcx)
seto r12b; spill OF x448 to reg (r12)
movzx rax, byte [ rsp + 0x348 ]; x457, copying x457 here, cause x457 is needed in a reg for other than x457, namely all: , x458--x459, size: 1
add rax, -0x1
mov rax, rsi; x458, copying x445 here, cause x445 is needed in a reg for other than x458, namely all: , x458--x459, x470, size: 2
mov rdx, 0xfffffffffffffffe ; moving imm to reg
sbb rax, rdx
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, rbx; loading flag
adox rdi, [ rsp + 0x350 ]
seto bpl; spill OF x375 to reg (rbp)
mov rbx, r8; x460, copying x447 here, cause x447 is needed in a reg for other than x460, namely all: , x460--x461, x471, size: 2
mov rdx, 0xffffffffffffffff ; moving imm to reg
sbb rbx, rdx
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r9, r9b
adox r9, rdx; loading flag
adox rdi, [ rsp + 0x238 ]
movzx r9, bpl; x376, copying x375 here, cause x375 is needed in a reg for other than x376, namely all: , x376, size: 1
movzx rdx, byte [ rsp + 0x358 ]; load byte memx336 to register64
lea r9, [ r9 + rdx ]; r64+m8
mov rdx, [ rsp + 0x260 ]; x412, copying x399 here, cause x399 is needed in a reg for other than x412, namely all: , x412--x413, size: 1
adox rdx, r9
seto bpl; spill OF x413 to reg (rbp)
mov r9, -0x1 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r9, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, r9; loading flag
adox rdi, r13
movzx r13, cl; x438, copying x437 here, cause x437 is needed in a reg for other than x438, namely all: , x438, size: 1
mov r12, [ rsp + 0x360 ]; load m64 x417 to register64
lea r13, [ r13 + r12 ]; r8/64 + m8
adox r13, rdx
seto r12b; spill OF x452 to reg (r12)
mov rcx, rdi; x462, copying x449 here, cause x449 is needed in a reg for other than x462, namely all: , x472, x462--x463, size: 2
mov rdx, 0xffffffffffffffff ; moving imm to reg
sbb rcx, rdx
mov r9, r13; x464, copying x451 here, cause x451 is needed in a reg for other than x464, namely all: , x464--x465, x473, size: 2
sbb r9, rdx
movzx rdx, r12b; x453, copying x452 here, cause x452 is needed in a reg for other than x453, namely all: , x453, size: 1
movzx rbp, bpl
lea rdx, [ rdx + rbp ]
sbb rdx, 0x00000000
mov rbp, [ rsp + 0x330 ]; x469, copying x456 here, cause x456 is needed in a reg for other than x469, namely all: , x469, size: 1
cmovc rbp, r14; if CF, x469<- x443 (nzVar)
mov r14, [ rsp + 0x2f0 ]; x468, copying x454 here, cause x454 is needed in a reg for other than x468, namely all: , x468, size: 1
cmovc r14, r11; if CF, x468<- x441 (nzVar)
mov r11, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r11 + 0x8 ], rbp; out1[1] = x469
cmovc rax, rsi; if CF, x470<- x445 (nzVar)
cmovc rcx, rdi; if CF, x472<- x449 (nzVar)
mov [ r11 + 0x0 ], r14; out1[0] = x468
mov [ r11 + 0x20 ], rcx; out1[4] = x472
mov [ r11 + 0x10 ], rax; out1[2] = x470
cmovc r9, r13; if CF, x473<- x451 (nzVar)
mov [ r11 + 0x28 ], r9; out1[5] = x473
cmovc rbx, r8; if CF, x471<- x447 (nzVar)
mov [ r11 + 0x18 ], rbx; out1[3] = x471
mov rbx, [ rsp + 0x368 ]; restoring from stack
mov rbp, [ rsp + 0x370 ]; restoring from stack
mov r12, [ rsp + 0x378 ]; restoring from stack
mov r13, [ rsp + 0x380 ]; restoring from stack
mov r14, [ rsp + 0x388 ]; restoring from stack
mov r15, [ rsp + 0x390 ]; restoring from stack
add rsp, 0x398 
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; clocked at 4556 MHz
; first cyclecount 330.44, best 275.8421052631579, lastGood 289.28205128205127
; seed 629307854069783 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3829109 ms / 60000 runs=> 63.81848333333333ms/run
; Time spent for assembling and measureing (initial batch_size=39, initial num_batches=101): 108834 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.02842280018667528
; number reverted permutation/ tried permutation: 21684 / 30078 =72.093%
; number reverted decision/ tried decision: 19506 / 29923 =65.187%