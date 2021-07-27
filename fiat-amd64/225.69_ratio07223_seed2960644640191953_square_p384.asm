SECTION .text
	GLOBAL square_p384
square_p384:
sub rsp, 0x3c0 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x390 ], rbx; saving to stack
mov [ rsp + 0x398 ], rbp; saving to stack
mov [ rsp + 0x3a0 ], r12; saving to stack
mov [ rsp + 0x3a8 ], r13; saving to stack
mov [ rsp + 0x3b0 ], r14; saving to stack
mov [ rsp + 0x3b8 ], r15; saving to stack
mov rax, [ rsi + 0x20 ]; load m64 x4 to register64
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r10, r11, rax; x307, x306<- x4 * arg1[2]
mov rbx, [ rsi + 0x0 ]; load m64 x6 to register64
mov rdx, rax; x4 to rdx
mulx rax, rbp, [ rsi + 0x0 ]; x311, x310<- x4 * arg1[0]
mulx r12, r13, [ rsi + 0x8 ]; x309, x308<- x4 * arg1[1]
mulx r14, r15, [ rsi + 0x20 ]; x303, x302<- x4 * arg1[4]
mulx rcx, r8, [ rsi + 0x28 ]; x301, x300<- x4 * arg1[5]
add r13, rax; could be done better, if r0 has been u8 as well
adcx r11, r12
mov r9, rdx; preserving value of x4 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx rax, r12, rbx; x18, x17<- x6 * arg1[0]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r9, rdi, r9; x305, x304<- x4 * arg1[3]
mov rdx, 0x100000001 ; moving imm to reg
mov [ rsp + 0x8 ], r11; spilling x314 to mem
mov [ rsp + 0x10 ], r13; spilling x312 to mem
mulx r11, r13, r12; _, x30<- x17 * 0x100000001
mov r11, [ rsi + 0x8 ]; load m64 x1 to register64
mov rdx, 0xffffffff ; moving imm to reg
mov [ rsp + 0x18 ], rbp; spilling x310 to mem
mov [ rsp + 0x20 ], rcx; spilling x301 to mem
mulx rbp, rcx, r13; x43, x42<- x30 * 0xffffffff
mov rdx, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x28 ], rbp; spilling x43 to mem
mov [ rsp + 0x30 ], r8; spilling x300 to mem
mulx rbp, r8, r13; x41, x40<- x30 * 0xffffffff00000000
adcx rdi, r10
adcx r15, r9
mov r10, rdx; preserving value of 0xffffffff00000000 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x38 ], r15; spilling x318 to mem
mulx r9, r15, r11; x80, x79<- x1 * arg1[0]
mov rdx, rbx; x6 to rdx
mulx rbx, r10, [ rsi + 0x8 ]; x16, x15<- x6 * arg1[1]
mov [ rsp + 0x40 ], rdi; spilling x316 to mem
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r10, rax
setc al; spill CF x319 to reg (rax)
clc;
adcx rcx, r12
seto cl; spill OF x20 to reg (rcx)
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
movzx rax, al
adox rax, r12; loading flag
adox r14, [ rsp + 0x30 ]
mov rax, [ rsp + 0x20 ]; x322, copying x301 here, cause x301 is needed in a reg for other than x322, namely all: , x322, size: 1
adox rax, rdi
mov r12, -0x3 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r8, [ rsp + 0x28 ]
adcx r8, r10
mulx r10, rdi, [ rsi + 0x10 ]; x14, x13<- x6 * arg1[2]
seto r12b; spill OF x45 to reg (r12)
mov [ rsp + 0x48 ], rax; spilling x322 to mem
mov rax, -0x2 ; moving imm to reg
inc rax; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, r8
mov r8, rdx; preserving value of x6 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x50 ], r14; spilling x320 to mem
mulx rax, r14, r11; x78, x77<- x1 * arg1[1]
mov rdx, 0xfffffffffffffffe ; moving imm to reg
mov [ rsp + 0x58 ], r10; spilling x14 to mem
mov [ rsp + 0x60 ], rax; spilling x78 to mem
mulx r10, rax, r13; x39, x38<- x30 * 0xfffffffffffffffe
mov rdx, 0x100000001 ; moving imm to reg
mov [ rsp + 0x68 ], r10; spilling x39 to mem
mov [ rsp + 0x70 ], rdi; spilling x13 to mem
mulx r10, rdi, r15; _, x106<- x92 * 0x100000001
mov r10, [ rsi + 0x10 ]; load m64 x2 to register64
setc dl; spill CF x58 to reg (rdx)
clc;
adcx r14, r9
setc r9b; spill CF x82 to reg (r9)
clc;
mov [ rsp + 0x78 ], r14; spilling x81 to mem
mov r14, -0x1 ; moving imm to reg
movzx r12, r12b
adcx r12, r14; loading flag
adcx rbp, rax
mov r12b, dl; preserving value of x58 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx rax, r14, r10; x157, x156<- x2 * arg1[0]
mov rdx, 0xffffffff ; moving imm to reg
mov [ rsp + 0x80 ], rax; spilling x157 to mem
mov byte [ rsp + 0x88 ], r9b; spilling byte x82 to mem
mulx rax, r9, rdi; x119, x118<- x106 * 0xffffffff
mov rdx, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x90 ], r14; spilling x156 to mem
mov [ rsp + 0x98 ], rbp; spilling x46 to mem
mulx r14, rbp, rdi; x117, x116<- x106 * 0xffffffff00000000
seto dl; spill OF x93 to reg (rdx)
mov [ rsp + 0xa0 ], r14; spilling x117 to mem
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rcx, cl
adox rcx, r14; loading flag
adox rbx, [ rsp + 0x70 ]
setc cl; spill CF x47 to reg (rcx)
clc;
adcx r9, r15
seto r9b; spill OF x22 to reg (r9)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rbp, rax
seto r15b; spill OF x121 to reg (r15)
dec r14; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r12, r12b
adox r12, r14; loading flag
adox rbx, [ rsp + 0x98 ]
mov r12, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r13; x30, swapping with x93, which is currently in rdx
mulx rax, r14, r12; x37, x36<- x30 * 0xffffffffffffffff
seto r12b; spill OF x60 to reg (r12)
mov byte [ rsp + 0xa8 ], r9b; spilling byte x22 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r13, r13b
adox r13, r9; loading flag
adox rbx, [ rsp + 0x78 ]
mov r13, 0xfffffffffffffffe ; moving imm to reg
xchg rdx, r13; 0xfffffffffffffffe, swapping with x30, which is currently in rdx
mov byte [ rsp + 0xb0 ], r12b; spilling byte x60 to mem
mulx r9, r12, rdi; x115, x114<- x106 * 0xfffffffffffffffe
adcx rbp, rbx
seto bl; spill OF x95 to reg (rbx)
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, [ rsp + 0x90 ]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0xb8 ], r9; spilling x115 to mem
mov byte [ rsp + 0xc0 ], bl; spilling byte x95 to mem
mulx r9, rbx, r13; x35, x34<- x30 * 0xffffffffffffffff
seto dl; spill OF x170 to reg (rdx)
mov [ rsp + 0xc8 ], r9; spilling x35 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rcx, cl
adox rcx, r9; loading flag
adox r14, [ rsp + 0x68 ]
adox rbx, rax
xchg rdx, r8; x6, swapping with x170, which is currently in rdx
mulx rcx, rax, [ rsi + 0x18 ]; x12, x11<- x6 * arg1[3]
setc r9b; spill CF x134 to reg (r9)
clc;
mov [ rsp + 0xd0 ], rbx; spilling x50 to mem
mov rbx, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, rbx; loading flag
adcx r12, [ rsp + 0xa0 ]
mov r15, rdx; preserving value of x6 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0xd8 ], rcx; spilling x12 to mem
mulx rbx, rcx, r11; x76, x75<- x1 * arg1[2]
setc dl; spill CF x123 to reg (rdx)
mov byte [ rsp + 0xe0 ], r8b; spilling byte x170 to mem
movzx r8, byte [ rsp + 0x88 ]; load byte memx82 to register64
clc;
mov [ rsp + 0xe8 ], rbx; spilling x76 to mem
mov rbx, -0x1 ; moving imm to reg
adcx r8, rbx; loading flag
adcx rcx, [ rsp + 0x60 ]
mov r8b, dl; preserving value of x123 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0xf0 ], r12; spilling x122 to mem
mulx rbx, r12, r10; x155, x154<- x2 * arg1[1]
setc dl; spill CF x84 to reg (rdx)
mov [ rsp + 0xf8 ], rbx; spilling x155 to mem
movzx rbx, byte [ rsp + 0xa8 ]; load byte memx22 to register64
clc;
mov byte [ rsp + 0x100 ], r8b; spilling byte x123 to mem
mov r8, -0x1 ; moving imm to reg
adcx rbx, r8; loading flag
adcx rax, [ rsp + 0x58 ]
mov rbx, 0x100000001 ; moving imm to reg
xchg rdx, rbx; 0x100000001, swapping with x84, which is currently in rdx
mov byte [ rsp + 0x108 ], bl; spilling byte x84 to mem
mulx r8, rbx, rbp; _, x183<- x169 * 0x100000001
seto r8b; spill OF x51 to reg (r8)
movzx rdx, byte [ rsp + 0xb0 ]; load byte memx60 to register64
mov [ rsp + 0x110 ], rbx; spilling x183 to mem
mov rbx, -0x1 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbx, -0x1 ; moving imm to reg
adox rdx, rbx; loading flag
adox rax, r14
seto dl; spill OF x62 to reg (rdx)
movzx r14, byte [ rsp + 0xc0 ]; load byte memx95 to register64
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
adox r14, rbx; loading flag
adox rax, rcx
seto r14b; spill OF x97 to reg (r14)
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r12, [ rsp + 0x80 ]
setc cl; spill CF x24 to reg (rcx)
clc;
mov rbx, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, rbx; loading flag
adcx rax, [ rsp + 0xf0 ]
mov r9b, dl; preserving value of x62 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov byte [ rsp + 0x118 ], r8b; spilling byte x51 to mem
mulx rbx, r8, r11; x74, x73<- x1 * arg1[3]
mov rdx, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x120 ], rbx; spilling x74 to mem
mov byte [ rsp + 0x128 ], r14b; spilling byte x97 to mem
mulx rbx, r14, [ rsp + 0x110 ]; x194, x193<- x183 * 0xffffffff00000000
mov rdx, 0xffffffff ; moving imm to reg
mov [ rsp + 0x130 ], rbx; spilling x194 to mem
mov [ rsp + 0x138 ], r14; spilling x193 to mem
mulx rbx, r14, [ rsp + 0x110 ]; x196, x195<- x183 * 0xffffffff
seto dl; spill OF x159 to reg (rdx)
mov [ rsp + 0x140 ], rbx; spilling x196 to mem
movzx rbx, byte [ rsp + 0x108 ]; load byte memx84 to register64
mov byte [ rsp + 0x148 ], r9b; spilling byte x62 to mem
mov r9, -0x1 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r9, -0x1 ; moving imm to reg
adox rbx, r9; loading flag
adox r8, [ rsp + 0xe8 ]
seto bl; spill OF x86 to reg (rbx)
movzx r9, byte [ rsp + 0xe0 ]; load byte memx170 to register64
mov [ rsp + 0x150 ], r8; spilling x85 to mem
mov r8, -0x1 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r8, -0x1 ; moving imm to reg
adox r9, r8; loading flag
adox rax, r12
mov r9b, dl; preserving value of x159 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r12, r8, r10; x153, x152<- x2 * arg1[2]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x158 ], r12; spilling x153 to mem
mulx r13, r12, r13; x33, x32<- x30 * 0xffffffffffffffff
mov [ rsp + 0x160 ], r13; spilling x33 to mem
mov byte [ rsp + 0x168 ], bl; spilling byte x86 to mem
mulx r13, rbx, rdi; x113, x112<- x106 * 0xffffffffffffffff
xchg rdx, r15; x6, swapping with 0xffffffffffffffff, which is currently in rdx
mov [ rsp + 0x170 ], r13; spilling x113 to mem
mulx r15, r13, [ rsi + 0x28 ]; x8, x7<- x6 * arg1[5]
mov [ rsp + 0x178 ], r15; spilling x8 to mem
mov r15, rdx; preserving value of x6 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x180 ], rax; spilling x171 to mem
mov [ rsp + 0x188 ], r12; spilling x32 to mem
mulx rax, r12, r10; x151, x150<- x2 * arg1[3]
mov rdx, r15; x6 to rdx
mulx rdx, r15, [ rsi + 0x20 ]; x10, x9<- x6 * arg1[4]
mov [ rsp + 0x190 ], rax; spilling x151 to mem
setc al; spill CF x136 to reg (rax)
clc;
mov [ rsp + 0x198 ], r12; spilling x150 to mem
mov r12, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, r12; loading flag
adcx r15, [ rsp + 0xd8 ]
setc cl; spill CF x26 to reg (rcx)
clc;
adcx r14, rbp
seto r14b; spill OF x172 to reg (r14)
movzx rbp, byte [ rsp + 0x148 ]; load byte memx62 to register64
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
adox rbp, r12; loading flag
adox r15, [ rsp + 0xd0 ]
mov rbp, rdx; preserving value of x10 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov byte [ rsp + 0x1a0 ], r14b; spilling byte x172 to mem
mulx r12, r14, r11; x72, x71<- x1 * arg1[4]
seto dl; spill OF x64 to reg (rdx)
mov [ rsp + 0x1a8 ], r12; spilling x72 to mem
movzx r12, byte [ rsp + 0x100 ]; load byte memx123 to register64
mov [ rsp + 0x1b0 ], r14; spilling x71 to mem
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r12, r14; loading flag
adox rbx, [ rsp + 0xb8 ]
seto r12b; spill OF x125 to reg (r12)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r14; loading flag
adox rbp, r13
mov r13, [ rsp + 0x138 ]; load m64 x193 to register64
setc cl; spill CF x209 to reg (rcx)
clc;
adcx r13, [ rsp + 0x140 ]
seto r14b; spill OF x28 to reg (r14)
mov byte [ rsp + 0x1b8 ], r12b; spilling byte x125 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, r12; loading flag
adox r8, [ rsp + 0xf8 ]
setc r9b; spill CF x198 to reg (r9)
movzx r12, byte [ rsp + 0x128 ]; load byte memx97 to register64
clc;
mov byte [ rsp + 0x1c0 ], r14b; spilling byte x28 to mem
mov r14, -0x1 ; moving imm to reg
adcx r12, r14; loading flag
adcx r15, [ rsp + 0x150 ]
mov r12, [ rsp + 0x188 ]; load m64 x32 to register64
seto r14b; spill OF x161 to reg (r14)
mov [ rsp + 0x1c8 ], rbp; spilling x27 to mem
movzx rbp, byte [ rsp + 0x118 ]; load byte memx51 to register64
mov byte [ rsp + 0x1d0 ], dl; spilling byte x64 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbp, rdx; loading flag
adox r12, [ rsp + 0xc8 ]
setc bpl; spill CF x99 to reg (rbp)
clc;
movzx rax, al
adcx rax, rdx; loading flag
adcx r15, rbx
mov rax, 0xfffffffffffffffe ; moving imm to reg
mov rdx, rax; 0xfffffffffffffffe to rdx
mulx rax, rbx, [ rsp + 0x110 ]; x192, x191<- x183 * 0xfffffffffffffffe
setc dl; spill CF x138 to reg (rdx)
clc;
mov byte [ rsp + 0x1d8 ], r14b; spilling byte x161 to mem
mov r14, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, r14; loading flag
adcx rbx, [ rsp + 0x130 ]
setc r9b; spill CF x200 to reg (r9)
movzx r14, byte [ rsp + 0x1a0 ]; load byte memx172 to register64
clc;
mov byte [ rsp + 0x1e0 ], dl; spilling byte x138 to mem
mov rdx, -0x1 ; moving imm to reg
adcx r14, rdx; loading flag
adcx r15, r8
seto r14b; spill OF x53 to reg (r14)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r8; loading flag
adox r13, [ rsp + 0x180 ]
mov rcx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rcx; 0xffffffffffffffff, swapping with 0x0, which is currently in rdx
mulx rcx, r8, rdi; x111, x110<- x106 * 0xffffffffffffffff
setc dl; spill CF x174 to reg (rdx)
mov [ rsp + 0x1e8 ], r13; spilling x210 to mem
movzx r13, byte [ rsp + 0x1d0 ]; load byte memx64 to register64
clc;
mov [ rsp + 0x1f0 ], rcx; spilling x111 to mem
mov rcx, -0x1 ; moving imm to reg
adcx r13, rcx; loading flag
adcx r12, [ rsp + 0x1c8 ]
mov r13, 0xffffffffffffffff ; moving imm to reg
mov cl, dl; preserving value of x174 into a new reg
mov rdx, [ rsp + 0x110 ]; saving x183 in rdx.
mov byte [ rsp + 0x1f8 ], r14b; spilling byte x53 to mem
mov [ rsp + 0x200 ], r12; spilling x65 to mem
mulx r14, r12, r13; x190, x189<- x183 * 0xffffffffffffffff
adox rbx, r15
mov r15, [ rsp + 0x1b0 ]; load m64 x71 to register64
seto r13b; spill OF x213 to reg (r13)
mov [ rsp + 0x208 ], rbx; spilling x212 to mem
movzx rbx, byte [ rsp + 0x168 ]; load byte memx86 to register64
mov [ rsp + 0x210 ], r14; spilling x190 to mem
mov r14, -0x1 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r14, -0x1 ; moving imm to reg
adox rbx, r14; loading flag
adox r15, [ rsp + 0x120 ]
seto bl; spill OF x88 to reg (rbx)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, r14; loading flag
adox rax, r12
setc r9b; spill CF x66 to reg (r9)
movzx r12, byte [ rsp + 0x1b8 ]; load byte memx125 to register64
clc;
adcx r12, r14; loading flag
adcx r8, [ rsp + 0x170 ]
setc r12b; spill CF x127 to reg (r12)
clc;
movzx rbp, bpl
adcx rbp, r14; loading flag
adcx r15, [ rsp + 0x200 ]
mov rbp, rdx; preserving value of x183 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov byte [ rsp + 0x218 ], bl; spilling byte x88 to mem
mulx r14, rbx, r10; x149, x148<- x2 * arg1[4]
mov rdx, [ rsp + 0x198 ]; load m64 x150 to register64
mov [ rsp + 0x220 ], r14; spilling x149 to mem
setc r14b; spill CF x101 to reg (r14)
mov byte [ rsp + 0x228 ], r9b; spilling byte x66 to mem
movzx r9, byte [ rsp + 0x1d8 ]; load byte memx161 to register64
clc;
mov [ rsp + 0x230 ], rbx; spilling x148 to mem
mov rbx, -0x1 ; moving imm to reg
adcx r9, rbx; loading flag
adcx rdx, [ rsp + 0x158 ]
movzx r9, byte [ rsp + 0x1f8 ]; x54, copying x53 here, cause x53 is needed in a reg for other than x54, namely all: , x54, size: 1
mov rbx, [ rsp + 0x160 ]; load m64 x33 to register64
lea r9, [ r9 + rbx ]; r8/64 + m8
seto bl; spill OF x202 to reg (rbx)
mov byte [ rsp + 0x238 ], r14b; spilling byte x101 to mem
movzx r14, byte [ rsp + 0x1e0 ]; load byte memx138 to register64
mov [ rsp + 0x240 ], r9; spilling x54 to mem
mov r9, -0x1 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r9, -0x1 ; moving imm to reg
adox r14, r9; loading flag
adox r15, r8
movzx r14, byte [ rsp + 0x1c0 ]; x29, copying x28 here, cause x28 is needed in a reg for other than x29, namely all: , x29, size: 1
mov r8, [ rsp + 0x178 ]; load m64 x8 to register64
lea r14, [ r14 + r8 ]; r8/64 + m8
seto r8b; spill OF x140 to reg (r8)
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r9; loading flag
adox r15, rdx
seto cl; spill OF x176 to reg (rcx)
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, rdx; loading flag
adox r15, rax
mov r13, 0xffffffffffffffff ; moving imm to reg
mov rdx, r13; 0xffffffffffffffff to rdx
mulx rdi, r13, rdi; x109, x108<- x106 * 0xffffffffffffffff
xchg rdx, r11; x1, swapping with 0xffffffffffffffff, which is currently in rdx
mulx rdx, rax, [ rsi + 0x28 ]; x70, x69<- x1 * arg1[5]
seto r9b; spill OF x215 to reg (r9)
mov r11, 0x0 ; moving imm to reg
dec r11; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r12, r12b
adox r12, r11; loading flag
adox r13, [ rsp + 0x1f0 ]
mov r12, [ rsp + 0x190 ]; load m64 x151 to register64
mov r11, [ rsp + 0x230 ]; x164, copying x148 here, cause x148 is needed in a reg for other than x164, namely all: , x164--x165, size: 1
adcx r11, r12
setc r12b; spill CF x165 to reg (r12)
mov [ rsp + 0x248 ], r15; spilling x214 to mem
movzx r15, byte [ rsp + 0x228 ]; load byte memx66 to register64
clc;
mov byte [ rsp + 0x250 ], r9b; spilling byte x215 to mem
mov r9, -0x1 ; moving imm to reg
adcx r15, r9; loading flag
adcx r14, [ rsp + 0x240 ]
setc r15b; spill CF x68 to reg (r15)
movzx r9, byte [ rsp + 0x218 ]; load byte memx88 to register64
clc;
mov byte [ rsp + 0x258 ], r12b; spilling byte x165 to mem
mov r12, -0x1 ; moving imm to reg
adcx r9, r12; loading flag
adcx rax, [ rsp + 0x1a8 ]
seto r9b; spill OF x129 to reg (r9)
movzx r12, byte [ rsp + 0x238 ]; load byte memx101 to register64
mov [ rsp + 0x260 ], r11; spilling x164 to mem
mov r11, 0x0 ; moving imm to reg
dec r11; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r12, r11; loading flag
adox r14, rax
mov r12, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbp; x183, swapping with x70, which is currently in rdx
mulx rax, r11, r12; x186, x185<- x183 * 0xffffffffffffffff
seto r12b; spill OF x103 to reg (r12)
mov [ rsp + 0x268 ], rax; spilling x186 to mem
mov rax, -0x1 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rax, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, rax; loading flag
adox r14, r13
mov r8, 0xffffffffffffffff ; moving imm to reg
mulx rdx, r13, r8; x188, x187<- x183 * 0xffffffffffffffff
mov rax, 0x0 ; moving imm to reg
adcx rbp, rax
clc;
mov rax, -0x1 ; moving imm to reg
movzx r15, r15b
movzx r12, r12b
adcx r12, rax; loading flag
adcx rbp, r15
setc r15b; spill CF x105 to reg (r15)
clc;
movzx rbx, bl
adcx rbx, rax; loading flag
adcx r13, [ rsp + 0x210 ]
movzx rbx, r9b; x130, copying x129 here, cause x129 is needed in a reg for other than x130, namely all: , x130, size: 1
lea rbx, [ rbx + rdi ]
xchg rdx, r10; x2, swapping with x188, which is currently in rdx
mulx rdx, rdi, [ rsi + 0x28 ]; x147, x146<- x2 * arg1[5]
adcx r11, r10
setc r9b; spill CF x206 to reg (r9)
clc;
movzx rcx, cl
adcx rcx, rax; loading flag
adcx r14, [ rsp + 0x260 ]
adox rbx, rbp
setc cl; spill CF x178 to reg (rcx)
movzx r12, byte [ rsp + 0x250 ]; load byte memx215 to register64
clc;
adcx r12, rax; loading flag
adcx r14, r13
setc r12b; spill CF x217 to reg (r12)
movzx r10, byte [ rsp + 0x258 ]; load byte memx165 to register64
clc;
adcx r10, rax; loading flag
adcx rdi, [ rsp + 0x220 ]
seto r10b; spill OF x144 to reg (r10)
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, rbp; loading flag
adox rbx, rdi
movzx r13, r9b; x207, copying x206 here, cause x206 is needed in a reg for other than x207, namely all: , x207, size: 1
mov rcx, [ rsp + 0x268 ]; load m64 x186 to register64
lea r13, [ r13 + rcx ]; r8/64 + m8
adcx rdx, rax
mov rcx, [ rsi + 0x18 ]; load m64 x3 to register64
mov r9, rdx; preserving value of x168 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx rdi, rax, rcx; x234, x233<- x3 * arg1[0]
movzx rdx, r10b; x145, copying x144 here, cause x144 is needed in a reg for other than x145, namely all: , x145, size: 1
movzx r15, r15b
lea rdx, [ rdx + r15 ]
clc;
movzx r12, r12b
adcx r12, rbp; loading flag
adcx rbx, r11
setc r15b; spill CF x219 to reg (r15)
clc;
adcx rax, [ rsp + 0x1e8 ]
adox r9, rdx
mov r11, 0x100000001 ; moving imm to reg
mov rdx, rax; x246 to rdx
mulx rax, r10, r11; _, x260<- x246 * 0x100000001
setc al; spill CF x247 to reg (rax)
clc;
movzx r15, r15b
adcx r15, rbp; loading flag
adcx r9, r13
seto r12b; spill OF x222 to reg (r12)
adc r12b, 0x0
movzx r12, r12b
mov r13, rdx; preserving value of x246 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r15, rbp, rcx; x232, x231<- x3 * arg1[1]
adox rbp, rdi
mov rdx, 0xffffffff ; moving imm to reg
mulx rdi, r8, r10; x273, x272<- x260 * 0xffffffff
mov rdx, 0xfffffffffffffffe ; moving imm to reg
mov byte [ rsp + 0x270 ], r12b; spilling byte x222 to mem
mulx r11, r12, r10; x269, x268<- x260 * 0xfffffffffffffffe
mov rdx, -0x1 ; moving imm to reg
movzx rax, al
adcx rax, rdx; loading flag
adcx rbp, [ rsp + 0x208 ]
setc al; spill CF x249 to reg (rax)
clc;
adcx r8, r13
mov r8, 0xffffffff00000000 ; moving imm to reg
mov rdx, r10; x260 to rdx
mulx r10, r13, r8; x271, x270<- x260 * 0xffffffff00000000
mov r8, rdx; preserving value of x260 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x278 ], r9; spilling x220 to mem
mov [ rsp + 0x280 ], rbx; spilling x218 to mem
mulx r9, rbx, rcx; x230, x229<- x3 * arg1[2]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x288 ], r14; spilling x216 to mem
mov [ rsp + 0x290 ], r11; spilling x269 to mem
mulx r14, r11, r8; x267, x266<- x260 * 0xffffffffffffffff
adox rbx, r15
setc r15b; spill CF x286 to reg (r15)
clc;
adcx r13, rdi
setc dil; spill CF x275 to reg (rdi)
clc;
mov rdx, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, rdx; loading flag
adcx rbp, r13
setc r15b; spill CF x288 to reg (r15)
clc;
movzx rax, al
adcx rax, rdx; loading flag
adcx rbx, [ rsp + 0x248 ]
setc al; spill CF x251 to reg (rax)
clc;
movzx rdi, dil
adcx rdi, rdx; loading flag
adcx r10, r12
setc r12b; spill CF x277 to reg (r12)
clc;
adcx rbp, [ rsp + 0x18 ]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r13, rdi, rcx; x228, x227<- x3 * arg1[3]
mov rdx, 0x100000001 ; moving imm to reg
mov [ rsp + 0x298 ], r14; spilling x267 to mem
mov [ rsp + 0x2a0 ], r13; spilling x228 to mem
mulx r14, r13, rbp; _, x337<- x323 * 0x100000001
setc r14b; spill CF x324 to reg (r14)
clc;
mov rdx, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, rdx; loading flag
adcx rbx, r10
adox rdi, r9
seto r9b; spill OF x240 to reg (r9)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, r15; loading flag
adox r11, [ rsp + 0x290 ]
seto r10b; spill OF x279 to reg (r10)
inc r15; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
movzx rax, al
adox rax, rdx; loading flag
adox rdi, [ rsp + 0x288 ]
mov rax, 0xffffffff00000000 ; moving imm to reg
mov rdx, rax; 0xffffffff00000000 to rdx
mulx rax, r12, r13; x348, x347<- x337 * 0xffffffff00000000
mov r15, 0xffffffff ; moving imm to reg
xchg rdx, r13; x337, swapping with 0xffffffff00000000, which is currently in rdx
mov byte [ rsp + 0x2a8 ], r10b; spilling byte x279 to mem
mulx r13, r10, r15; x350, x349<- x337 * 0xffffffff
setc r15b; spill CF x290 to reg (r15)
clc;
adcx r12, r13
mov r13, 0xfffffffffffffffe ; moving imm to reg
mov [ rsp + 0x2b0 ], r12; spilling x351 to mem
mov [ rsp + 0x2b8 ], rbx; spilling x289 to mem
mulx r12, rbx, r13; x346, x345<- x337 * 0xfffffffffffffffe
adcx rbx, rax
seto al; spill OF x253 to reg (rax)
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r15, r15b
adox r15, r13; loading flag
adox rdi, r11
mov r15, rdx; preserving value of x337 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r11, r13, rcx; x226, x225<- x3 * arg1[4]
seto dl; spill OF x292 to reg (rdx)
mov [ rsp + 0x2c0 ], r12; spilling x346 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, r12; loading flag
adox r13, [ rsp + 0x2a0 ]
seto r9b; spill OF x242 to reg (r9)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r10, rbp
xchg rdx, rcx; x3, swapping with x292, which is currently in rdx
mulx rdx, r10, [ rsi + 0x28 ]; x224, x223<- x3 * arg1[5]
mov rbp, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbp; 0xffffffffffffffff, swapping with x224, which is currently in rdx
mov byte [ rsp + 0x2c8 ], cl; spilling byte x292 to mem
mulx r12, rcx, r8; x263, x262<- x260 * 0xffffffffffffffff
seto dl; spill OF x363 to reg (rdx)
mov [ rsp + 0x2d0 ], r12; spilling x263 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rax, al
adox rax, r12; loading flag
adox r13, [ rsp + 0x280 ]
mov rax, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rax; 0xffffffffffffffff, swapping with x363, which is currently in rdx
mov [ rsp + 0x2d8 ], r13; spilling x254 to mem
mulx r12, r13, r15; x342, x341<- x337 * 0xffffffffffffffff
mov rdx, [ rsp + 0x2b8 ]; load m64 x289 to register64
mov [ rsp + 0x2e0 ], r12; spilling x342 to mem
seto r12b; spill OF x255 to reg (r12)
mov [ rsp + 0x2e8 ], r13; spilling x341 to mem
mov r13, -0x1 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r13, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, r13; loading flag
adox rdx, [ rsp + 0x10 ]
mov r14, [ rsp + 0x8 ]; x327, copying x314 here, cause x314 is needed in a reg for other than x327, namely all: , x327--x328, size: 1
adox r14, rdi
seto dil; spill OF x328 to reg (rdi)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
movzx rax, al
adox rax, r13; loading flag
adox rdx, [ rsp + 0x2b0 ]
setc al; spill CF x354 to reg (rax)
clc;
movzx r9, r9b
adcx r9, r13; loading flag
adcx r11, r10
adox rbx, r14
mov r9, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r9; 0xffffffffffffffff, swapping with x364, which is currently in rdx
mulx r10, r14, r15; x344, x343<- x337 * 0xffffffffffffffff
mulx r15, r13, r15; x340, x339<- x337 * 0xffffffffffffffff
mov [ rsp + 0x2f0 ], rbx; spilling x366 to mem
mulx r8, rbx, r8; x265, x264<- x260 * 0xffffffffffffffff
seto dl; spill OF x367 to reg (rdx)
mov [ rsp + 0x2f8 ], r15; spilling x340 to mem
movzx r15, byte [ rsp + 0x2a8 ]; load byte memx279 to register64
mov [ rsp + 0x300 ], r9; spilling x364 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, r9; loading flag
adox rbx, [ rsp + 0x298 ]
adox rcx, r8
mov r15, 0x0 ; moving imm to reg
adcx rbp, r15
clc;
movzx r12, r12b
adcx r12, r9; loading flag
adcx r11, [ rsp + 0x278 ]
seto r12b; spill OF x283 to reg (r12)
movzx r8, byte [ rsp + 0x2c8 ]; load byte memx292 to register64
inc r9; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov r15, -0x1 ; moving imm to reg
adox r8, r15; loading flag
adox rbx, [ rsp + 0x2d8 ]
movzx r8, byte [ rsp + 0x270 ]; x258, copying x222 here, cause x222 is needed in a reg for other than x258, namely all: , x258--x259, size: 1
adcx r8, rbp
seto bpl; spill OF x294 to reg (rbp)
dec r9; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx rax, al
adox rax, r9; loading flag
adox r14, [ rsp + 0x2c0 ]
seto r15b; spill OF x356 to reg (r15)
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rax, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, rax; loading flag
adox r11, rcx
seto cl; spill OF x296 to reg (rcx)
dec r9; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx rdi, dil
adox rdi, r9; loading flag
adox rbx, [ rsp + 0x40 ]
setc al; spill CF x259 to reg (rax)
clc;
movzx r15, r15b
adcx r15, r9; loading flag
adcx r10, [ rsp + 0x2e8 ]
mov rdi, [ rsp + 0x38 ]; x331, copying x318 here, cause x318 is needed in a reg for other than x331, namely all: , x331--x332, size: 1
adox rdi, r11
mov rbp, [ rsi + 0x28 ]; load m64 x5 to register64
mov r15, [ rsp + 0x2e0 ]; x359, copying x342 here, cause x342 is needed in a reg for other than x359, namely all: , x359--x360, size: 1
adcx r15, r13
setc r13b; spill CF x360 to reg (r13)
clc;
movzx rdx, dl
adcx rdx, r9; loading flag
adcx rbx, r14
movzx rdx, r12b; x284, copying x283 here, cause x283 is needed in a reg for other than x284, namely all: , x284, size: 1
mov r14, [ rsp + 0x2d0 ]; load m64 x263 to register64
lea rdx, [ rdx + r14 ]; r8/64 + m8
setc r14b; spill CF x369 to reg (r14)
clc;
movzx rcx, cl
adcx rcx, r9; loading flag
adcx r8, rdx
mov rdx, rbp; x5 to rdx
mulx rbp, r12, [ rsi + 0x8 ]; x386, x385<- x5 * arg1[1]
mov r11, [ rsp + 0x50 ]; x333, copying x320 here, cause x320 is needed in a reg for other than x333, namely all: , x333--x334, size: 1
adox r11, r8
mulx rcx, r8, [ rsi + 0x0 ]; x388, x387<- x5 * arg1[0]
setc r9b; spill CF x298 to reg (r9)
clc;
adcx r8, [ rsp + 0x300 ]
mov [ rsp + 0x308 ], rbx; spilling x368 to mem
movzx rbx, r9b; x299, copying x298 here, cause x298 is needed in a reg for other than x299, namely all: , x299, size: 1
movzx rax, al
lea rbx, [ rbx + rax ]
mov rax, 0x100000001 ; moving imm to reg
xchg rdx, rax; 0x100000001, swapping with x5, which is currently in rdx
mov [ rsp + 0x310 ], rbp; spilling x386 to mem
mulx r9, rbp, r8; _, x414<- x400 * 0x100000001
mov r9, [ rsp + 0x48 ]; x335, copying x322 here, cause x322 is needed in a reg for other than x335, namely all: , x335--x336, size: 1
adox r9, rbx
seto bl; spill OF x336 to reg (rbx)
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, rdx; loading flag
adox rdi, r10
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r10, r14, rax; x384, x383<- x5 * arg1[2]
adox r15, r11
mov rdx, 0xfffffffffffffffe ; moving imm to reg
mov [ rsp + 0x318 ], r15; spilling x372 to mem
mulx r11, r15, rbp; x423, x422<- x414 * 0xfffffffffffffffe
movzx rdx, r13b; x361, copying x360 here, cause x360 is needed in a reg for other than x361, namely all: , x361, size: 1
mov [ rsp + 0x320 ], rdi; spilling x370 to mem
mov rdi, [ rsp + 0x2f8 ]; load m64 x340 to register64
lea rdx, [ rdx + rdi ]; r8/64 + m8
mov rdi, 0xffffffff00000000 ; moving imm to reg
xchg rdx, rdi; 0xffffffff00000000, swapping with x361, which is currently in rdx
mov [ rsp + 0x328 ], r11; spilling x423 to mem
mulx r13, r11, rbp; x425, x424<- x414 * 0xffffffff00000000
adox rdi, r9
mov r9, 0xffffffff ; moving imm to reg
xchg rdx, r9; 0xffffffff, swapping with 0xffffffff00000000, which is currently in rdx
mov [ rsp + 0x330 ], rdi; spilling x374 to mem
mulx r9, rdi, rbp; x427, x426<- x414 * 0xffffffff
seto dl; spill OF x375 to reg (rdx)
mov [ rsp + 0x338 ], r10; spilling x384 to mem
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, rcx
movzx rcx, dl; x376, copying x375 here, cause x375 is needed in a reg for other than x376, namely all: , x376, size: 1
movzx rbx, bl
lea rcx, [ rcx + rbx ]
mov rbx, [ rsp + 0x310 ]; x391, copying x386 here, cause x386 is needed in a reg for other than x391, namely all: , x391--x392, size: 1
adox rbx, r14
seto r14b; spill OF x392 to reg (r14)
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r11, r9
setc dl; spill CF x401 to reg (rdx)
clc;
adcx rdi, r8
mov r8, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbp; x414, swapping with x401, which is currently in rdx
mulx r9, r10, r8; x419, x418<- x414 * 0xffffffffffffffff
seto r8b; spill OF x429 to reg (r8)
mov [ rsp + 0x340 ], rcx; spilling x376 to mem
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbp, bpl
adox rbp, rcx; loading flag
adox r12, [ rsp + 0x2f0 ]
seto bpl; spill OF x403 to reg (rbp)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rcx, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, rcx; loading flag
adox r13, r15
adcx r11, r12
mov r15, 0xffffffffffffffff ; moving imm to reg
mulx r8, r12, r15; x421, x420<- x414 * 0xffffffffffffffff
mov rcx, rdx; preserving value of x414 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x348 ], r9; spilling x419 to mem
mulx r15, r9, rax; x382, x381<- x5 * arg1[3]
seto dl; spill OF x431 to reg (rdx)
mov [ rsp + 0x350 ], r15; spilling x382 to mem
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbp, bpl
adox rbp, r15; loading flag
adox rbx, [ rsp + 0x308 ]
setc bpl; spill CF x442 to reg (rbp)
seto r15b; spill OF x405 to reg (r15)
mov [ rsp + 0x358 ], r10; spilling x418 to mem
mov r10, r11; x454, copying x441 here, cause x441 is needed in a reg for other than x454, namely all: , x468, x454--x455, size: 2
mov [ rsp + 0x360 ], r8; spilling x421 to mem
mov r8, 0xffffffff ; moving imm to reg
sub r10, r8
mov r8, 0x0 ; moving imm to reg
dec r8; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbp, bpl
adox rbp, r8; loading flag
adox rbx, r13
xchg rdx, rax; x5, swapping with x431, which is currently in rdx
mulx r13, rbp, [ rsi + 0x28 ]; x378, x377<- x5 * arg1[5]
mov r8, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r8; 0xffffffffffffffff, swapping with x5, which is currently in rdx
mov [ rsp + 0x368 ], r10; spilling x454 to mem
mulx rcx, r10, rcx; x417, x416<- x414 * 0xffffffffffffffff
seto dl; spill OF x444 to reg (rdx)
mov [ rsp + 0x370 ], rcx; spilling x417 to mem
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r14, r14b
adox r14, rcx; loading flag
adox r9, [ rsp + 0x338 ]
setc r14b; spill CF x455 to reg (r14)
clc;
movzx rax, al
adcx rax, rcx; loading flag
adcx r12, [ rsp + 0x328 ]
mov rax, [ rsp + 0x360 ]; load m64 x421 to register64
mov rcx, [ rsp + 0x358 ]; x434, copying x418 here, cause x418 is needed in a reg for other than x434, namely all: , x434--x435, size: 1
adcx rcx, rax
xchg rdx, r8; x5, swapping with x444, which is currently in rdx
mulx rdx, rax, [ rsi + 0x20 ]; x380, x379<- x5 * arg1[4]
mov [ rsp + 0x378 ], rcx; spilling x434 to mem
mov rcx, [ rsp + 0x350 ]; x395, copying x382 here, cause x382 is needed in a reg for other than x395, namely all: , x395--x396, size: 1
adox rcx, rax
adox rbp, rdx
setc dl; spill CF x435 to reg (rdx)
seto al; spill OF x398 to reg (rax)
mov [ rsp + 0x380 ], r12; spilling x432 to mem
movzx r12, r14b; x455, copying x455 here, cause x455 is needed in a reg for other than x455, namely all: , x456--x457, size: 1
add r12, -0x1
mov r12, rbx; x456, copying x443 here, cause x443 is needed in a reg for other than x456, namely all: , x456--x457, x469, size: 2
mov r14, 0xffffffff00000000 ; moving imm to reg
sbb r12, r14
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rdx, dl
adox rdx, r14; loading flag
adox r10, [ rsp + 0x348 ]
setc dl; spill CF x457 to reg (rdx)
clc;
movzx r15, r15b
adcx r15, r14; loading flag
adcx r9, [ rsp + 0x320 ]
mov r15, [ rsp + 0x318 ]; x408, copying x372 here, cause x372 is needed in a reg for other than x408, namely all: , x408--x409, size: 1
adcx r15, rcx
movzx rcx, al; x399, copying x398 here, cause x398 is needed in a reg for other than x399, namely all: , x399, size: 1
lea rcx, [ rcx + r13 ]
mov r13, [ rsp + 0x330 ]; x410, copying x374 here, cause x374 is needed in a reg for other than x410, namely all: , x410--x411, size: 1
adcx r13, rbp
mov rax, [ rsp + 0x340 ]; x412, copying x376 here, cause x376 is needed in a reg for other than x412, namely all: , x412--x413, size: 1
adcx rax, rcx
seto bpl; spill OF x437 to reg (rbp)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rcx, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, rcx; loading flag
adox r9, [ rsp + 0x380 ]
setc r8b; spill CF x413 to reg (r8)
seto r14b; spill OF x446 to reg (r14)
movzx rcx, dl; x457, copying x457 here, cause x457 is needed in a reg for other than x457, namely all: , x458--x459, size: 1
add rcx, -0x1
mov rdx, r9; x458, copying x445 here, cause x445 is needed in a reg for other than x458, namely all: , x458--x459, x470, size: 2
mov rcx, 0xfffffffffffffffe ; moving imm to reg
sbb rdx, rcx
movzx rcx, bpl; x438, copying x437 here, cause x437 is needed in a reg for other than x438, namely all: , x438, size: 1
mov [ rsp + 0x388 ], r12; spilling x456 to mem
mov r12, [ rsp + 0x370 ]; load m64 x417 to register64
lea rcx, [ rcx + r12 ]; r8/64 + m8
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r14, r14b
adox r14, r12; loading flag
adox r15, [ rsp + 0x378 ]
adox r10, r13
adox rcx, rax
seto bpl; spill OF x452 to reg (rbp)
mov r13, r15; x460, copying x447 here, cause x447 is needed in a reg for other than x460, namely all: , x460--x461, x471, size: 2
mov rax, 0xffffffffffffffff ; moving imm to reg
sbb r13, rax
mov r14, r10; x462, copying x449 here, cause x449 is needed in a reg for other than x462, namely all: , x472, x462--x463, size: 2
sbb r14, rax
mov r12, rcx; x464, copying x451 here, cause x451 is needed in a reg for other than x464, namely all: , x464--x465, x473, size: 2
sbb r12, rax
movzx rax, bpl; x453, copying x452 here, cause x452 is needed in a reg for other than x453, namely all: , x453, size: 1
movzx r8, r8b
lea rax, [ rax + r8 ]
sbb rax, 0x00000000
cmovc r13, r15; if CF, x471<- x447 (nzVar)
mov rax, [ rsp + 0x368 ]; x468, copying x454 here, cause x454 is needed in a reg for other than x468, namely all: , x468, size: 1
cmovc rax, r11; if CF, x468<- x441 (nzVar)
cmovc r14, r10; if CF, x472<- x449 (nzVar)
cmovc rdx, r9; if CF, x470<- x445 (nzVar)
mov r11, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r11 + 0x18 ], r13; out1[3] = x471
mov [ r11 + 0x10 ], rdx; out1[2] = x470
cmovc r12, rcx; if CF, x473<- x451 (nzVar)
mov [ r11 + 0x28 ], r12; out1[5] = x473
mov r8, [ rsp + 0x388 ]; x469, copying x456 here, cause x456 is needed in a reg for other than x469, namely all: , x469, size: 1
cmovc r8, rbx; if CF, x469<- x443 (nzVar)
mov [ r11 + 0x20 ], r14; out1[4] = x472
mov [ r11 + 0x8 ], r8; out1[1] = x469
mov [ r11 + 0x0 ], rax; out1[0] = x468
mov rbx, [ rsp + 0x390 ]; restoring from stack
mov rbp, [ rsp + 0x398 ]; restoring from stack
mov r12, [ rsp + 0x3a0 ]; restoring from stack
mov r13, [ rsp + 0x3a8 ]; restoring from stack
mov r14, [ rsp + 0x3b0 ]; restoring from stack
mov r15, [ rsp + 0x3b8 ]; restoring from stack
add rsp, 0x3c0 
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; clocked at 3600 MHz
; first cyclecount 235.455, best 213.83333333333334, lastGood 225.6949152542373
; seed 2960644640191953 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2999278 ms / 60000 runs=> 49.987966666666665ms/run
; Time spent for assembling and measureing (initial batch_size=60, initial num_batches=101): 120753 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.040260689405917024
; number reverted permutation/ tried permutation: 18470 / 29870 =61.835%
; number reverted decision/ tried decision: 17431 / 30131 =57.851%