SECTION .text
	GLOBAL square_p384
square_p384:
sub rsp, 0x328 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x2f8 ], rbx; saving to stack
mov [ rsp + 0x300 ], rbp; saving to stack
mov [ rsp + 0x308 ], r12; saving to stack
mov [ rsp + 0x310 ], r13; saving to stack
mov [ rsp + 0x318 ], r14; saving to stack
mov [ rsp + 0x320 ], r15; saving to stack
mov rax, [ rsi + 0x8 ]; load m64 x1 to register64
mov r10, [ rsi + 0x0 ]; load m64 x6 to register64
mov rdx, r10; x6 to rdx
mulx r10, r11, [ rsi + 0x0 ]; x18, x17<- x6 * arg1[0]
mov rbx, 0x100000001 ; moving imm to reg
xchg rdx, r11; x17, swapping with x6, which is currently in rdx
mulx rbp, r12, rbx; _, x30<- x17 * 0x100000001
mov rbp, 0xffffffff ; moving imm to reg
xchg rdx, rbp; 0xffffffff, swapping with x17, which is currently in rdx
mulx r13, r14, r12; x43, x42<- x30 * 0xffffffff
mov r15, 0xffffffff00000000 ; moving imm to reg
xchg rdx, r15; 0xffffffff00000000, swapping with 0xffffffff, which is currently in rdx
mulx rcx, r8, r12; x41, x40<- x30 * 0xffffffff00000000
mov r9, rdx; preserving value of 0xffffffff00000000 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r15, rbx, r11; x16, x15<- x6 * arg1[1]
xor rdx, rdx
adox rbx, r10
mov r10, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r9, rdi, rax; x80, x79<- x1 * arg1[0]
adcx r8, r13
setc dl; spill CF x45 to reg (rdx)
clc;
adcx r14, rbp
adcx r8, rbx
seto r14b; spill OF x20 to reg (r14)
mov rbp, -0x3 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rdi, r8
mov r13, 0x100000001 ; moving imm to reg
xchg rdx, r13; 0x100000001, swapping with x45, which is currently in rdx
mulx rbx, r8, rdi; _, x106<- x92 * 0x100000001
mov rbx, rdx; preserving value of 0x100000001 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r10, rbp, r11; x14, x13<- x6 * arg1[2]
mov rdx, 0xfffffffffffffffe ; moving imm to reg
mov [ rsp + 0x8 ], r10; spilling x14 to mem
mulx rbx, r10, r12; x39, x38<- x30 * 0xfffffffffffffffe
mov rdx, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x10 ], rbx; spilling x39 to mem
mov [ rsp + 0x18 ], r9; spilling x80 to mem
mulx rbx, r9, r8; x117, x116<- x106 * 0xffffffff00000000
xchg rdx, rax; x1, swapping with 0xffffffff00000000, which is currently in rdx
mov [ rsp + 0x20 ], rbx; spilling x117 to mem
mulx rax, rbx, [ rsi + 0x10 ]; x76, x75<- x1 * arg1[2]
mov [ rsp + 0x28 ], rax; spilling x76 to mem
setc al; spill CF x58 to reg (rax)
clc;
mov [ rsp + 0x30 ], rbx; spilling x75 to mem
mov rbx, -0x1 ; moving imm to reg
movzx r13, r13b
adcx r13, rbx; loading flag
adcx rcx, r10
mov r13, 0xffffffff ; moving imm to reg
xchg rdx, r8; x106, swapping with x1, which is currently in rdx
mulx r10, rbx, r13; x119, x118<- x106 * 0xffffffff
seto r13b; spill OF x93 to reg (r13)
mov [ rsp + 0x38 ], rcx; spilling x46 to mem
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r9, r10
setc r10b; spill CF x47 to reg (r10)
clc;
movzx r14, r14b
adcx r14, rcx; loading flag
adcx r15, rbp
mov r14, rdx; preserving value of x106 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx rbp, rcx, r11; x12, x11<- x6 * arg1[3]
mov rdx, r8; x1 to rdx
mov [ rsp + 0x40 ], rbp; spilling x12 to mem
mulx r8, rbp, [ rsi + 0x8 ]; x78, x77<- x1 * arg1[1]
mov [ rsp + 0x48 ], r9; spilling x120 to mem
mov r9, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r9; 0xffffffffffffffff, swapping with x1, which is currently in rdx
mov [ rsp + 0x50 ], r8; spilling x78 to mem
mov [ rsp + 0x58 ], rcx; spilling x11 to mem
mulx r8, rcx, r12; x37, x36<- x30 * 0xffffffffffffffff
seto dl; spill OF x121 to reg (rdx)
mov [ rsp + 0x60 ], r8; spilling x37 to mem
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, rdi
mov rbx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r12; x30, swapping with x121, which is currently in rdx
mulx rdi, r8, rbx; x35, x34<- x30 * 0xffffffffffffffff
seto bl; spill OF x132 to reg (rbx)
mov [ rsp + 0x68 ], rdi; spilling x35 to mem
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, [ rsp + 0x18 ]
mov rdi, 0xfffffffffffffffe ; moving imm to reg
xchg rdx, rdi; 0xfffffffffffffffe, swapping with x30, which is currently in rdx
mov [ rsp + 0x70 ], r8; spilling x34 to mem
mov byte [ rsp + 0x78 ], bl; spilling byte x132 to mem
mulx r8, rbx, r14; x115, x114<- x106 * 0xfffffffffffffffe
seto dl; spill OF x82 to reg (rdx)
mov [ rsp + 0x80 ], r8; spilling x115 to mem
mov r8, 0x0 ; moving imm to reg
dec r8; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r10, r10b
adox r10, r8; loading flag
adox rcx, [ rsp + 0x10 ]
seto r10b; spill OF x49 to reg (r10)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, r8; loading flag
adox rbx, [ rsp + 0x20 ]
seto r12b; spill OF x123 to reg (r12)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
movzx rax, al
adox rax, r8; loading flag
adox r15, [ rsp + 0x38 ]
seto al; spill OF x60 to reg (rax)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, r8; loading flag
adox r15, rbp
mov r13, [ rsp + 0x58 ]; load m64 x11 to register64
mov rbp, [ rsp + 0x8 ]; x23, copying x14 here, cause x14 is needed in a reg for other than x23, namely all: , x23--x24, size: 1
adcx rbp, r13
mov r13b, dl; preserving value of x82 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov byte [ rsp + 0x88 ], r12b; spilling byte x123 to mem
mulx r8, r12, r9; x72, x71<- x1 * arg1[4]
mov rdx, [ rsp + 0x50 ]; load m64 x78 to register64
mov [ rsp + 0x90 ], r8; spilling x72 to mem
setc r8b; spill CF x24 to reg (r8)
clc;
mov [ rsp + 0x98 ], r12; spilling x71 to mem
mov r12, -0x1 ; moving imm to reg
movzx r13, r13b
adcx r13, r12; loading flag
adcx rdx, [ rsp + 0x30 ]
setc r13b; spill CF x84 to reg (r13)
clc;
movzx rax, al
adcx rax, r12; loading flag
adcx rbp, rcx
setc cl; spill CF x62 to reg (rcx)
movzx rax, byte [ rsp + 0x78 ]; load byte memx132 to register64
clc;
adcx rax, r12; loading flag
adcx r15, [ rsp + 0x48 ]
adox rdx, rbp
mov rax, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rax; 0xffffffffffffffff, swapping with x96, which is currently in rdx
mulx rbp, r12, r14; x113, x112<- x106 * 0xffffffffffffffff
adcx rbx, rax
mov rax, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0xa0 ], rbx; spilling x135 to mem
mov [ rsp + 0xa8 ], r15; spilling x133 to mem
mulx rbx, r15, r11; x10, x9<- x6 * arg1[4]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0xb0 ], rbp; spilling x113 to mem
mulx rax, rbp, r9; x70, x69<- x1 * arg1[5]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0xb8 ], rax; spilling x70 to mem
mulx rdi, rax, rdi; x33, x32<- x30 * 0xffffffffffffffff
mov [ rsp + 0xc0 ], rdi; spilling x33 to mem
mov rdi, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0xc8 ], rbp; spilling x69 to mem
mulx r11, rbp, r11; x8, x7<- x6 * arg1[5]
setc dl; spill CF x136 to reg (rdx)
clc;
mov rdi, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, rdi; loading flag
adcx r15, [ rsp + 0x40 ]
mov r8, [ rsp + 0x70 ]; load m64 x34 to register64
setc dil; spill CF x26 to reg (rdi)
clc;
mov [ rsp + 0xd0 ], r11; spilling x8 to mem
mov r11, -0x1 ; moving imm to reg
movzx r10, r10b
adcx r10, r11; loading flag
adcx r8, [ rsp + 0x60 ]
seto r10b; spill OF x97 to reg (r10)
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r11, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r11; loading flag
adox r15, r8
seto cl; spill OF x64 to reg (rcx)
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
movzx rdi, dil
adox rdi, r8; loading flag
adox rbx, rbp
xchg rdx, r9; x1, swapping with x136, which is currently in rdx
mulx rdx, rbp, [ rsi + 0x18 ]; x74, x73<- x1 * arg1[3]
mov rdi, [ rsp + 0x68 ]; x52, copying x35 here, cause x35 is needed in a reg for other than x52, namely all: , x52--x53, size: 1
adcx rdi, rax
setc al; spill CF x53 to reg (rax)
movzx r11, byte [ rsp + 0x88 ]; load byte memx123 to register64
clc;
adcx r11, r8; loading flag
adcx r12, [ rsp + 0x80 ]
setc r11b; spill CF x125 to reg (r11)
clc;
movzx rcx, cl
adcx rcx, r8; loading flag
adcx rbx, rdi
seto cl; spill OF x28 to reg (rcx)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdi, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, rdi; loading flag
adox rbp, [ rsp + 0x28 ]
mov r13, [ rsp + 0x98 ]; x87, copying x71 here, cause x71 is needed in a reg for other than x87, namely all: , x87--x88, size: 1
adox r13, rdx
mov rdx, [ rsp + 0x90 ]; load m64 x72 to register64
mov r8, [ rsp + 0xc8 ]; x89, copying x69 here, cause x69 is needed in a reg for other than x89, namely all: , x89--x90, size: 1
adox r8, rdx
seto dl; spill OF x90 to reg (rdx)
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdi, -0x1 ; moving imm to reg
movzx r10, r10b
adox r10, rdi; loading flag
adox r15, rbp
movzx r10, dl; x91, copying x90 here, cause x90 is needed in a reg for other than x91, namely all: , x91, size: 1
mov rbp, [ rsp + 0xb8 ]; load m64 x70 to register64
lea r10, [ r10 + rbp ]; r8/64 + m8
seto bpl; spill OF x99 to reg (rbp)
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, rdx; loading flag
adox r15, r12
movzx r9, al; x54, copying x53 here, cause x53 is needed in a reg for other than x54, namely all: , x54, size: 1
mov r12, [ rsp + 0xc0 ]; load m64 x33 to register64
lea r9, [ r9 + r12 ]; r8/64 + m8
mov r12, [ rsi + 0x10 ]; load m64 x2 to register64
movzx rax, cl; x29, copying x28 here, cause x28 is needed in a reg for other than x29, namely all: , x29, size: 1
mov rdi, [ rsp + 0xd0 ]; load m64 x8 to register64
lea rax, [ rax + rdi ]; r8/64 + m8
adcx r9, rax
mov rdi, 0xffffffffffffffff ; moving imm to reg
mov rdx, rdi; 0xffffffffffffffff to rdx
mulx rcx, rax, r14; x111, x110<- x106 * 0xffffffffffffffff
setc dl; spill CF x68 to reg (rdx)
clc;
mov [ rsp + 0xd8 ], r15; spilling x137 to mem
mov r15, -0x1 ; moving imm to reg
movzx r11, r11b
adcx r11, r15; loading flag
adcx rax, [ rsp + 0xb0 ]
setc r11b; spill CF x127 to reg (r11)
clc;
movzx rbp, bpl
adcx rbp, r15; loading flag
adcx rbx, r13
adox rax, rbx
adcx r8, r9
xchg rdx, r12; x2, swapping with x68, which is currently in rdx
mulx r13, rbp, [ rsi + 0x8 ]; x155, x154<- x2 * arg1[1]
mov r9, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r9; 0xffffffffffffffff, swapping with x2, which is currently in rdx
mulx r14, rbx, r14; x109, x108<- x106 * 0xffffffffffffffff
movzx r15, r12b; x104, copying x68 here, cause x68 is needed in a reg for other than x104, namely all: , x104--x105, size: 1
adcx r15, r10
setc r10b; spill CF x105 to reg (r10)
clc;
mov r12, -0x1 ; moving imm to reg
movzx r11, r11b
adcx r11, r12; loading flag
adcx rcx, rbx
adox rcx, r8
mov r11, 0x0 ; moving imm to reg
adcx r14, r11
mov r8, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx rbx, r11, r9; x157, x156<- x2 * arg1[0]
adox r14, r15
clc;
adcx r11, [ rsp + 0xa8 ]
mov rdx, 0x100000001 ; moving imm to reg
mulx r15, r12, r11; _, x183<- x169 * 0x100000001
mov r15, 0xffffffff ; moving imm to reg
xchg rdx, r15; 0xffffffff, swapping with 0x100000001, which is currently in rdx
mulx r15, r8, r12; x196, x195<- x183 * 0xffffffff
seto dl; spill OF x144 to reg (rdx)
mov [ rsp + 0xe0 ], r14; spilling x143 to mem
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, rbx
mov rbx, 0xfffffffffffffffe ; moving imm to reg
xchg rdx, r12; x183, swapping with x144, which is currently in rdx
mov [ rsp + 0xe8 ], rcx; spilling x141 to mem
mulx r14, rcx, rbx; x192, x191<- x183 * 0xfffffffffffffffe
mov rbx, rdx; preserving value of x183 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0xf0 ], rax; spilling x139 to mem
mov [ rsp + 0xf8 ], rbp; spilling x158 to mem
mulx rax, rbp, r9; x153, x152<- x2 * arg1[2]
mov rdx, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x100 ], rax; spilling x153 to mem
mov [ rsp + 0x108 ], rbp; spilling x152 to mem
mulx rax, rbp, rbx; x194, x193<- x183 * 0xffffffff00000000
movzx rdx, r12b; x145, copying x144 here, cause x144 is needed in a reg for other than x145, namely all: , x145, size: 1
movzx r10, r10b
lea rdx, [ rdx + r10 ]
setc r10b; spill CF x170 to reg (r10)
clc;
adcx rbp, r15
adcx rcx, rax
mov r12, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r12; 0xffffffffffffffff, swapping with x145, which is currently in rdx
mulx r15, rax, rbx; x190, x189<- x183 * 0xffffffffffffffff
adcx rax, r14
setc r14b; spill CF x202 to reg (r14)
clc;
adcx r8, r11
mov r8, [ rsp + 0x108 ]; x160, copying x152 here, cause x152 is needed in a reg for other than x160, namely all: , x160--x161, size: 1
adox r8, r13
mov r13, [ rsp + 0xf8 ]; load m64 x158 to register64
setc r11b; spill CF x209 to reg (r11)
clc;
mov rdx, -0x1 ; moving imm to reg
movzx r10, r10b
adcx r10, rdx; loading flag
adcx r13, [ rsp + 0xa0 ]
mov rdx, r9; x2 to rdx
mulx r9, r10, [ rsi + 0x18 ]; x151, x150<- x2 * arg1[3]
mov [ rsp + 0x110 ], r12; spilling x145 to mem
mov r12, [ rsp + 0x100 ]; x162, copying x153 here, cause x153 is needed in a reg for other than x162, namely all: , x162--x163, size: 1
adox r12, r10
setc r10b; spill CF x172 to reg (r10)
clc;
mov [ rsp + 0x118 ], r15; spilling x190 to mem
mov r15, -0x1 ; moving imm to reg
movzx r11, r11b
adcx r11, r15; loading flag
adcx r13, rbp
mulx rbp, r11, [ rsi + 0x20 ]; x149, x148<- x2 * arg1[4]
setc r15b; spill CF x211 to reg (r15)
clc;
mov [ rsp + 0x120 ], r13; spilling x210 to mem
mov r13, -0x1 ; moving imm to reg
movzx r10, r10b
adcx r10, r13; loading flag
adcx r8, [ rsp + 0xd8 ]
mulx rdx, r10, [ rsi + 0x28 ]; x147, x146<- x2 * arg1[5]
mov r13, [ rsp + 0xf0 ]; x175, copying x139 here, cause x139 is needed in a reg for other than x175, namely all: , x175--x176, size: 1
adcx r13, r12
adox r11, r9
adox r10, rbp
mov r9, [ rsp + 0xe8 ]; x177, copying x141 here, cause x141 is needed in a reg for other than x177, namely all: , x177--x178, size: 1
adcx r9, r11
mov r12, [ rsp + 0xe0 ]; x179, copying x143 here, cause x143 is needed in a reg for other than x179, namely all: , x179--x180, size: 1
adcx r12, r10
mov rbp, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbp; 0xffffffffffffffff, swapping with x147, which is currently in rdx
mulx r11, r10, rbx; x188, x187<- x183 * 0xffffffffffffffff
mov rdx, [ rsi + 0x18 ]; load m64 x3 to register64
mov [ rsp + 0x128 ], r12; spilling x179 to mem
seto r12b; spill OF x167 to reg (r12)
mov [ rsp + 0x130 ], r11; spilling x188 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, r11; loading flag
adox r8, rcx
mulx rcx, r15, [ rsi + 0x18 ]; x228, x227<- x3 * arg1[3]
adox rax, r13
mov r13, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r13; 0xffffffffffffffff, swapping with x3, which is currently in rdx
mulx rbx, r11, rbx; x186, x185<- x183 * 0xffffffffffffffff
setc dl; spill CF x180 to reg (rdx)
clc;
mov [ rsp + 0x138 ], rax; spilling x214 to mem
mov rax, -0x1 ; moving imm to reg
movzx r14, r14b
adcx r14, rax; loading flag
adcx r10, [ rsp + 0x118 ]
adox r10, r9
movzx r14, r12b; x168, copying x167 here, cause x167 is needed in a reg for other than x168, namely all: , x168, size: 1
lea r14, [ r14 + rbp ]
mov bpl, dl; preserving value of x180 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r12, r9, r13; x232, x231<- x3 * arg1[1]
mov rdx, [ rsp + 0x130 ]; x205, copying x188 here, cause x188 is needed in a reg for other than x205, namely all: , x205--x206, size: 1
adcx rdx, r11
mov r11, 0x0 ; moving imm to reg
adcx rbx, r11
clc;
movzx rbp, bpl
adcx rbp, rax; loading flag
adcx r14, [ rsp + 0x110 ]
xchg rdx, r13; x3, swapping with x205, which is currently in rdx
mulx rbp, r11, [ rsi + 0x0 ]; x234, x233<- x3 * arg1[0]
mov rax, [ rsp + 0x128 ]; x218, copying x179 here, cause x179 is needed in a reg for other than x218, namely all: , x218--x219, size: 1
adox rax, r13
mov [ rsp + 0x140 ], rax; spilling x218 to mem
mulx r13, rax, [ rsi + 0x10 ]; x230, x229<- x3 * arg1[2]
mov [ rsp + 0x148 ], r10; spilling x216 to mem
seto r10b; spill OF x219 to reg (r10)
mov [ rsp + 0x150 ], r8; spilling x212 to mem
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r9, rbp
adox rax, r12
adox r15, r13
seto r12b; spill OF x240 to reg (r12)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r11, [ rsp + 0x120 ]
mulx rbp, r13, [ rsi + 0x20 ]; x226, x225<- x3 * arg1[4]
mov r8, 0x100000001 ; moving imm to reg
xchg rdx, r11; x246, swapping with x3, which is currently in rdx
mov [ rsp + 0x158 ], r15; spilling x239 to mem
mov [ rsp + 0x160 ], rax; spilling x237 to mem
mulx r15, rax, r8; _, x260<- x246 * 0x100000001
setc r15b; spill CF x182 to reg (r15)
clc;
mov r8, -0x1 ; moving imm to reg
movzx r10, r10b
adcx r10, r8; loading flag
adcx r14, rbx
movzx rbx, r15b; x222, copying x182 here, cause x182 is needed in a reg for other than x222, namely all: , x222, size: 1
mov r10, 0x0 ; moving imm to reg
adcx rbx, r10
mov r15, 0xfffffffffffffffe ; moving imm to reg
xchg rdx, rax; x260, swapping with x246, which is currently in rdx
mulx r10, r8, r15; x269, x268<- x260 * 0xfffffffffffffffe
mov r15, rdx; preserving value of x260 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x168 ], rbx; spilling x222 to mem
mulx r11, rbx, r11; x224, x223<- x3 * arg1[5]
mov rdx, [ rsi + 0x20 ]; load m64 x4 to register64
mov [ rsp + 0x170 ], r14; spilling x220 to mem
mov [ rsp + 0x178 ], r10; spilling x269 to mem
mulx r14, r10, [ rsi + 0x8 ]; x309, x308<- x4 * arg1[1]
clc;
mov [ rsp + 0x180 ], r14; spilling x309 to mem
mov r14, -0x1 ; moving imm to reg
movzx r12, r12b
adcx r12, r14; loading flag
adcx rcx, r13
adcx rbx, rbp
mov r12, [ rsp + 0x150 ]; x248, copying x212 here, cause x212 is needed in a reg for other than x248, namely all: , x248--x249, size: 1
adox r12, r9
mov r9, 0xffffffff ; moving imm to reg
xchg rdx, r15; x260, swapping with x4, which is currently in rdx
mulx rbp, r13, r9; x273, x272<- x260 * 0xffffffff
mov r14, rdx; preserving value of x260 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x188 ], rbx; spilling x243 to mem
mulx r9, rbx, r15; x311, x310<- x4 * arg1[0]
mov rdx, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x190 ], rcx; spilling x241 to mem
mov [ rsp + 0x198 ], rbx; spilling x310 to mem
mulx rcx, rbx, r14; x271, x270<- x260 * 0xffffffff00000000
mov rdx, 0x0 ; moving imm to reg
adcx r11, rdx
clc;
adcx r13, rax
seto r13b; spill OF x249 to reg (r13)
mov rax, -0x3 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbx, rbp
adcx rbx, r12
adox r8, rcx
mov r12, [ rsp + 0x160 ]; load m64 x237 to register64
seto bpl; spill OF x277 to reg (rbp)
dec rdx; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r13, r13b
adox r13, rdx; loading flag
adox r12, [ rsp + 0x138 ]
setc r13b; spill CF x288 to reg (r13)
clc;
adcx r10, r9
setc r9b; spill CF x313 to reg (r9)
clc;
adcx rbx, [ rsp + 0x198 ]
mov rcx, 0x100000001 ; moving imm to reg
mov rdx, rbx; x323 to rdx
mulx rbx, rax, rcx; _, x337<- x323 * 0x100000001
mov rbx, 0xffffffff00000000 ; moving imm to reg
xchg rdx, rax; x337, swapping with x323, which is currently in rdx
mov byte [ rsp + 0x1a0 ], r9b; spilling byte x313 to mem
mulx rcx, r9, rbx; x348, x347<- x337 * 0xffffffff00000000
mov rbx, [ rsi + 0x28 ]; load m64 x5 to register64
mov [ rsp + 0x1a8 ], r11; spilling x245 to mem
seto r11b; spill OF x251 to reg (r11)
mov byte [ rsp + 0x1b0 ], bpl; spilling byte x277 to mem
mov rbp, -0x1 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, rbp; loading flag
adox r12, r8
adcx r10, r12
mov r13, rdx; preserving value of x337 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r8, r12, rbx; x388, x387<- x5 * arg1[0]
mov rdx, 0xffffffff ; moving imm to reg
mov [ rsp + 0x1b8 ], r8; spilling x388 to mem
mulx rbp, r8, r13; x350, x349<- x337 * 0xffffffff
seto dl; spill OF x290 to reg (rdx)
mov byte [ rsp + 0x1c0 ], r11b; spilling byte x251 to mem
mov r11, -0x2 ; moving imm to reg
inc r11; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r9, rbp
setc bpl; spill CF x326 to reg (rbp)
clc;
adcx r8, rax
adcx r9, r10
setc r8b; spill CF x365 to reg (r8)
clc;
adcx r12, r9
mov rax, 0x100000001 ; moving imm to reg
xchg rdx, r12; x400, swapping with x290, which is currently in rdx
mulx r10, r9, rax; _, x414<- x400 * 0x100000001
mov r10, 0xffffffff00000000 ; moving imm to reg
xchg rdx, r9; x414, swapping with x400, which is currently in rdx
mulx r11, rax, r10; x425, x424<- x414 * 0xffffffff00000000
mov r10, 0xffffffff ; moving imm to reg
mov byte [ rsp + 0x1c8 ], r8b; spilling byte x365 to mem
mov byte [ rsp + 0x1d0 ], bpl; spilling byte x326 to mem
mulx r8, rbp, r10; x427, x426<- x414 * 0xffffffff
setc r10b; spill CF x401 to reg (r10)
clc;
adcx rax, r8
mov r8, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x1d8 ], rax; spilling x428 to mem
mov byte [ rsp + 0x1e0 ], r10b; spilling byte x401 to mem
mulx rax, r10, r8; x419, x418<- x414 * 0xffffffffffffffff
mov r8, 0xfffffffffffffffe ; moving imm to reg
mov byte [ rsp + 0x1e8 ], r12b; spilling byte x290 to mem
mov [ rsp + 0x1f0 ], rbp; spilling x426 to mem
mulx r12, rbp, r8; x423, x422<- x414 * 0xfffffffffffffffe
mov r8, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x1f8 ], rax; spilling x419 to mem
mov [ rsp + 0x200 ], rcx; spilling x348 to mem
mulx rax, rcx, r8; x417, x416<- x414 * 0xffffffffffffffff
mov [ rsp + 0x208 ], rax; spilling x417 to mem
mulx rdx, rax, r8; x421, x420<- x414 * 0xffffffffffffffff
adcx rbp, r11
adcx rax, r12
adcx r10, rdx
mov r11, 0xfffffffffffffffe ; moving imm to reg
mov rdx, r13; x337 to rdx
mulx r13, r12, r11; x346, x345<- x337 * 0xfffffffffffffffe
mov [ rsp + 0x210 ], r10; spilling x434 to mem
mulx r11, r10, r8; x344, x343<- x337 * 0xffffffffffffffff
mov r8, [ rsp + 0x200 ]; x353, copying x348 here, cause x348 is needed in a reg for other than x353, namely all: , x353--x354, size: 1
adox r8, r12
mov r12, [ rsp + 0x1f8 ]; x436, copying x419 here, cause x419 is needed in a reg for other than x436, namely all: , x436--x437, size: 1
adcx r12, rcx
mov rcx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x218 ], r12; spilling x436 to mem
mov [ rsp + 0x220 ], rax; spilling x432 to mem
mulx r12, rax, rcx; x342, x341<- x337 * 0xffffffffffffffff
adox r10, r13
mov r13, [ rsp + 0x208 ]; x438, copying x417 here, cause x417 is needed in a reg for other than x438, namely all: , x438, size: 1
mov rcx, 0x0 ; moving imm to reg
adcx r13, rcx
mov rcx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rcx; 0xffffffffffffffff, swapping with x337, which is currently in rdx
mov [ rsp + 0x228 ], r13; spilling x438 to mem
mov [ rsp + 0x230 ], rbp; spilling x430 to mem
mulx r13, rbp, r14; x263, x262<- x260 * 0xffffffffffffffff
mov [ rsp + 0x238 ], r10; spilling x355 to mem
mov [ rsp + 0x240 ], r8; spilling x353 to mem
mulx r10, r8, r14; x267, x266<- x260 * 0xffffffffffffffff
mov [ rsp + 0x248 ], r13; spilling x263 to mem
mulx rcx, r13, rcx; x340, x339<- x337 * 0xffffffffffffffff
adox rax, r11
adox r13, r12
mulx r14, r11, r14; x265, x264<- x260 * 0xffffffffffffffff
clc;
adcx r9, [ rsp + 0x1f0 ]
setc r9b; spill CF x440 to reg (r9)
movzx r12, byte [ rsp + 0x1b0 ]; load byte memx277 to register64
clc;
mov rdx, -0x1 ; moving imm to reg
adcx r12, rdx; loading flag
adcx r8, [ rsp + 0x178 ]
adcx r11, r10
mov r12, 0x0 ; moving imm to reg
adox rcx, r12
mov r10, [ rsp + 0x158 ]; load m64 x239 to register64
movzx r12, byte [ rsp + 0x1c0 ]; load byte memx251 to register64
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
adox r12, rdx; loading flag
adox r10, [ rsp + 0x148 ]
mov r12, [ rsp + 0x190 ]; load m64 x241 to register64
mov rdx, [ rsp + 0x140 ]; x254, copying x218 here, cause x218 is needed in a reg for other than x254, namely all: , x254--x255, size: 1
adox rdx, r12
adcx rbp, r14
mov r12, [ rsp + 0x188 ]; load m64 x243 to register64
mov r14, [ rsp + 0x170 ]; x256, copying x220 here, cause x220 is needed in a reg for other than x256, namely all: , x256--x257, size: 1
adox r14, r12
xchg rdx, r15; x4, swapping with x254, which is currently in rdx
mov [ rsp + 0x250 ], rcx; spilling x361 to mem
mulx r12, rcx, [ rsi + 0x10 ]; x307, x306<- x4 * arg1[2]
mov [ rsp + 0x258 ], r13; spilling x359 to mem
mov r13, [ rsp + 0x248 ]; x284, copying x263 here, cause x263 is needed in a reg for other than x284, namely all: , x284, size: 1
mov [ rsp + 0x260 ], rax; spilling x357 to mem
mov rax, 0x0 ; moving imm to reg
adcx r13, rax
movzx rax, byte [ rsp + 0x1e8 ]; load byte memx290 to register64
clc;
mov byte [ rsp + 0x268 ], r9b; spilling byte x440 to mem
mov r9, -0x1 ; moving imm to reg
adcx rax, r9; loading flag
adcx r10, r8
adcx r11, r15
mov rax, rdx; preserving value of x4 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r8, r15, rbx; x386, x385<- x5 * arg1[1]
adcx rbp, r14
mov rdx, rax; x4 to rdx
mulx rax, r14, [ rsi + 0x18 ]; x305, x304<- x4 * arg1[3]
mov r9, [ rsp + 0x168 ]; load m64 x222 to register64
mov [ rsp + 0x270 ], r8; spilling x386 to mem
mov r8, [ rsp + 0x1a8 ]; x258, copying x245 here, cause x245 is needed in a reg for other than x258, namely all: , x258--x259, size: 1
adox r8, r9
seto r9b; spill OF x259 to reg (r9)
mov [ rsp + 0x278 ], rbp; spilling x295 to mem
movzx rbp, byte [ rsp + 0x1a0 ]; load byte memx313 to register64
mov [ rsp + 0x280 ], r11; spilling x293 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
adox rbp, r11; loading flag
adox rcx, [ rsp + 0x180 ]
xchg rdx, rbx; x5, swapping with x4, which is currently in rdx
mulx rbp, r11, [ rsi + 0x10 ]; x384, x383<- x5 * arg1[2]
mov [ rsp + 0x288 ], rbp; spilling x384 to mem
seto bpl; spill OF x315 to reg (rbp)
mov [ rsp + 0x290 ], r11; spilling x383 to mem
mov r11, -0x2 ; moving imm to reg
inc r11; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, [ rsp + 0x1b8 ]
mov r11, rdx; preserving value of x5 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x298 ], r15; spilling x389 to mem
mov byte [ rsp + 0x2a0 ], r9b; spilling byte x259 to mem
mulx r15, r9, rbx; x303, x302<- x4 * arg1[4]
setc dl; spill CF x296 to reg (rdx)
clc;
mov [ rsp + 0x2a8 ], r15; spilling x303 to mem
mov r15, -0x1 ; moving imm to reg
movzx rbp, bpl
adcx rbp, r15; loading flag
adcx r12, r14
seto r14b; spill OF x390 to reg (r14)
movzx rbp, byte [ rsp + 0x1d0 ]; load byte memx326 to register64
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
adox rbp, r15; loading flag
adox r10, rcx
adcx r9, rax
setc bpl; spill CF x319 to reg (rbp)
movzx rax, byte [ rsp + 0x1c8 ]; load byte memx365 to register64
clc;
adcx rax, r15; loading flag
adcx r10, [ rsp + 0x240 ]
setc al; spill CF x367 to reg (rax)
clc;
movzx rdx, dl
adcx rdx, r15; loading flag
adcx r8, r13
movzx r13, byte [ rsp + 0x2a0 ]; x299, copying x259 here, cause x259 is needed in a reg for other than x299, namely all: , x299, size: 1
mov rdx, 0x0 ; moving imm to reg
adcx r13, rdx
mov rcx, [ rsp + 0x280 ]; x329, copying x293 here, cause x293 is needed in a reg for other than x329, namely all: , x329--x330, size: 1
adox rcx, r12
xchg rdx, rbx; x4, swapping with 0x0, which is currently in rdx
mulx rdx, r12, [ rsi + 0x28 ]; x301, x300<- x4 * arg1[5]
movzx rbx, byte [ rsp + 0x1e0 ]; load byte memx401 to register64
clc;
adcx rbx, r15; loading flag
adcx r10, [ rsp + 0x298 ]
mov rbx, [ rsp + 0x278 ]; x331, copying x295 here, cause x295 is needed in a reg for other than x331, namely all: , x331--x332, size: 1
adox rbx, r9
seto r9b; spill OF x332 to reg (r9)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, r15; loading flag
adox r12, [ rsp + 0x2a8 ]
setc bpl; spill CF x403 to reg (rbp)
clc;
movzx rax, al
adcx rax, r15; loading flag
adcx rcx, [ rsp + 0x238 ]
mov rax, [ rsp + 0x290 ]; load m64 x383 to register64
seto r15b; spill OF x321 to reg (r15)
mov [ rsp + 0x2b0 ], r13; spilling x299 to mem
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r14, r14b
adox r14, r13; loading flag
adox rax, [ rsp + 0x270 ]
xchg rdx, r11; x5, swapping with x301, which is currently in rdx
mulx r14, r13, [ rsi + 0x18 ]; x382, x381<- x5 * arg1[3]
mov [ rsp + 0x2b8 ], r14; spilling x382 to mem
seto r14b; spill OF x392 to reg (r14)
mov [ rsp + 0x2c0 ], r11; spilling x301 to mem
movzx r11, byte [ rsp + 0x268 ]; load byte memx440 to register64
mov byte [ rsp + 0x2c8 ], r15b; spilling byte x321 to mem
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r15, -0x1 ; moving imm to reg
adox r11, r15; loading flag
adox r10, [ rsp + 0x1d8 ]
seto r11b; spill OF x442 to reg (r11)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, r15; loading flag
adox rcx, rax
mulx rbp, rax, [ rsi + 0x20 ]; x380, x379<- x5 * arg1[4]
mov r15, [ rsp + 0x260 ]; x370, copying x357 here, cause x357 is needed in a reg for other than x370, namely all: , x370--x371, size: 1
adcx r15, rbx
seto bl; spill OF x405 to reg (rbx)
mov [ rsp + 0x2d0 ], rbp; spilling x380 to mem
mov rbp, -0x1 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, rbp; loading flag
adox r13, [ rsp + 0x288 ]
seto r14b; spill OF x394 to reg (r14)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, rbp; loading flag
adox r8, r12
setc r9b; spill CF x371 to reg (r9)
clc;
movzx r11, r11b
adcx r11, rbp; loading flag
adcx rcx, [ rsp + 0x230 ]
movzx r12, byte [ rsp + 0x2c8 ]; x322, copying x321 here, cause x321 is needed in a reg for other than x322, namely all: , x322, size: 1
mov r11, [ rsp + 0x2c0 ]; load m64 x301 to register64
lea r12, [ r12 + r11 ]; r8/64 + m8
mov r11, [ rsp + 0x2b0 ]; x335, copying x299 here, cause x299 is needed in a reg for other than x335, namely all: , x335--x336, size: 1
adox r11, r12
mulx rdx, r12, [ rsi + 0x28 ]; x378, x377<- x5 * arg1[5]
seto bpl; spill OF x336 to reg (rbp)
mov [ rsp + 0x2d8 ], rdx; spilling x378 to mem
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, rdx; loading flag
adox r15, r13
setc bl; spill CF x444 to reg (rbx)
seto r13b; spill OF x407 to reg (r13)
mov rdx, r10; x454, copying x441 here, cause x441 is needed in a reg for other than x454, namely all: , x454--x455, x468, size: 2
mov byte [ rsp + 0x2e0 ], bpl; spilling byte x336 to mem
mov rbp, 0xffffffff ; moving imm to reg
sub rdx, rbp
mov rbp, rcx; x456, copying x443 here, cause x443 is needed in a reg for other than x456, namely all: , x469, x456--x457, size: 2
mov [ rsp + 0x2e8 ], rdx; spilling x454 to mem
mov rdx, 0xffffffff00000000 ; moving imm to reg
sbb rbp, rdx
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, rdx; loading flag
adox rax, [ rsp + 0x2b8 ]
setc r14b; spill CF x457 to reg (r14)
clc;
movzx rbx, bl
adcx rbx, rdx; loading flag
adcx r15, [ rsp + 0x220 ]
setc bl; spill CF x446 to reg (rbx)
clc;
movzx r9, r9b
adcx r9, rdx; loading flag
adcx r8, [ rsp + 0x258 ]
mov r9, [ rsp + 0x2d0 ]; x397, copying x380 here, cause x380 is needed in a reg for other than x397, namely all: , x397--x398, size: 1
adox r9, r12
mov r12, [ rsp + 0x250 ]; x374, copying x361 here, cause x361 is needed in a reg for other than x374, namely all: , x374--x375, size: 1
adcx r12, r11
mov r11, [ rsp + 0x2d8 ]; x399, copying x378 here, cause x378 is needed in a reg for other than x399, namely all: , x399, size: 1
mov rdx, 0x0 ; moving imm to reg
adox r11, rdx
setc dl; spill CF x375 to reg (rdx)
mov [ rsp + 0x2f0 ], rbp; spilling x456 to mem
movzx rbp, r14b; x457, copying x457 here, cause x457 is needed in a reg for other than x457, namely all: , x458--x459, size: 1
add rbp, -0x1
mov rbp, r15; x458, copying x445 here, cause x445 is needed in a reg for other than x458, namely all: , x470, x458--x459, size: 2
mov r14, 0xfffffffffffffffe ; moving imm to reg
sbb rbp, r14
mov r14, -0x1 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r14, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, r14; loading flag
adox r8, rax
movzx r13, dl; x376, copying x375 here, cause x375 is needed in a reg for other than x376, namely all: , x376, size: 1
movzx rax, byte [ rsp + 0x2e0 ]; load byte memx336 to register64
lea r13, [ r13 + rax ]; r64+m8
adox r9, r12
adox r11, r13
setc al; spill CF x459 to reg (rax)
clc;
movzx rbx, bl
adcx rbx, r14; loading flag
adcx r8, [ rsp + 0x210 ]
mov rbx, [ rsp + 0x218 ]; x449, copying x436 here, cause x436 is needed in a reg for other than x449, namely all: , x449--x450, size: 1
adcx rbx, r9
mov rdx, [ rsp + 0x228 ]; x451, copying x438 here, cause x438 is needed in a reg for other than x451, namely all: , x451--x452, size: 1
adcx rdx, r11
setc r12b; spill CF x452 to reg (r12)
seto r13b; spill OF x413 to reg (r13)
movzx r9, al; x459, copying x459 here, cause x459 is needed in a reg for other than x459, namely all: , x460--x461, size: 1
add r9, -0x1
mov rax, r8; x460, copying x447 here, cause x447 is needed in a reg for other than x460, namely all: , x460--x461, x471, size: 2
mov r9, 0xffffffffffffffff ; moving imm to reg
sbb rax, r9
movzx r11, r12b; x453, copying x452 here, cause x452 is needed in a reg for other than x453, namely all: , x453, size: 1
movzx r13, r13b
lea r11, [ r11 + r13 ]
mov r13, rbx; x462, copying x449 here, cause x449 is needed in a reg for other than x462, namely all: , x472, x462--x463, size: 2
sbb r13, r9
mov r12, rdx; x464, copying x451 here, cause x451 is needed in a reg for other than x464, namely all: , x464--x465, x473, size: 2
sbb r12, r9
sbb r11, 0x00000000
mov r11, [ rsp + 0x2e8 ]; x468, copying x454 here, cause x454 is needed in a reg for other than x468, namely all: , x468, size: 1
cmovc r11, r10; if CF, x468<- x441 (nzVar)
cmovc rax, r8; if CF, x471<- x447 (nzVar)
cmovc r12, rdx; if CF, x473<- x451 (nzVar)
mov r10, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r10 + 0x28 ], r12; out1[5] = x473
mov [ r10 + 0x18 ], rax; out1[3] = x471
cmovc rbp, r15; if CF, x470<- x445 (nzVar)
mov r15, [ rsp + 0x2f0 ]; x469, copying x456 here, cause x456 is needed in a reg for other than x469, namely all: , x469, size: 1
cmovc r15, rcx; if CF, x469<- x443 (nzVar)
mov [ r10 + 0x0 ], r11; out1[0] = x468
cmovc r13, rbx; if CF, x472<- x449 (nzVar)
mov [ r10 + 0x8 ], r15; out1[1] = x469
mov [ r10 + 0x10 ], rbp; out1[2] = x470
mov [ r10 + 0x20 ], r13; out1[4] = x472
mov rbx, [ rsp + 0x2f8 ]; restoring from stack
mov rbp, [ rsp + 0x300 ]; restoring from stack
mov r12, [ rsp + 0x308 ]; restoring from stack
mov r13, [ rsp + 0x310 ]; restoring from stack
mov r14, [ rsp + 0x318 ]; restoring from stack
mov r15, [ rsp + 0x320 ]; restoring from stack
add rsp, 0x328 
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; clocked at 2200 MHz
; first cyclecount 301.15, best 260.4390243902439, lastGood 289.1707317073171
; seed 4091147453534096 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4071032 ms / 60000 runs=> 67.85053333333333ms/run
; Time spent for assembling and measureing (initial batch_size=40, initial num_batches=101): 178010 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.04372601345309985
; number reverted permutation/ tried permutation: 20066 / 29801 =67.333%
; number reverted decision/ tried decision: 18232 / 30200 =60.371%