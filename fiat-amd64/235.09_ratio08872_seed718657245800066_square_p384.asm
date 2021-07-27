SECTION .text
	GLOBAL square_p384
square_p384:
sub rsp, 0x238 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x208 ], rbx; saving to stack
mov [ rsp + 0x210 ], rbp; saving to stack
mov [ rsp + 0x218 ], r12; saving to stack
mov [ rsp + 0x220 ], r13; saving to stack
mov [ rsp + 0x228 ], r14; saving to stack
mov [ rsp + 0x230 ], r15; saving to stack
mov rax, [ rsi + 0x28 ]; load m64 x5 to register64
mov rdx, rax; x5 to rdx
mulx rax, r10, [ rsi + 0x10 ]; x384, x383<- x5 * arg1[2]
mulx r11, rbx, [ rsi + 0x18 ]; x382, x381<- x5 * arg1[3]
mulx rbp, r12, [ rsi + 0x8 ]; x386, x385<- x5 * arg1[1]
mulx r13, r14, [ rsi + 0x0 ]; x388, x387<- x5 * arg1[0]
xor r15, r15
adox r12, r13
mulx rcx, r8, [ rsi + 0x28 ]; x378, x377<- x5 * arg1[5]
mulx rdx, r9, [ rsi + 0x20 ]; x380, x379<- x5 * arg1[4]
adox r10, rbp
mov rbp, [ rsi + 0x0 ]; load m64 x6 to register64
adox rbx, rax
mov rax, rdx; preserving value of x380 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r13, r15, rbp; x16, x15<- x6 * arg1[1]
adox r9, r11
mov rdx, rbp; x6 to rdx
mulx rbp, r11, [ rsi + 0x0 ]; x18, x17<- x6 * arg1[0]
adox r8, rax
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx rax, rdi, [ rsi + 0x20 ]; x10, x9<- x6 * arg1[4]
adcx r15, rbp
mov [ rsp + 0x8 ], r8; spilling x397 to mem
mulx rbp, r8, [ rsi + 0x18 ]; x12, x11<- x6 * arg1[3]
mov [ rsp + 0x10 ], r9; spilling x395 to mem
mov [ rsp + 0x18 ], rbx; spilling x393 to mem
mulx r9, rbx, [ rsi + 0x28 ]; x8, x7<- x6 * arg1[5]
mov [ rsp + 0x20 ], r10; spilling x391 to mem
mulx rdx, r10, [ rsi + 0x10 ]; x14, x13<- x6 * arg1[2]
adcx r10, r13
adcx r8, rdx
mov r13, 0x100000001 ; moving imm to reg
mov rdx, r11; x17 to rdx
mov [ rsp + 0x28 ], r12; spilling x389 to mem
mulx r11, r12, r13; _, x30<- x17 * 0x100000001
mov r11, 0x0 ; moving imm to reg
adox rcx, r11
adcx rdi, rbp
mov rbp, 0xffffffff ; moving imm to reg
xchg rdx, rbp; 0xffffffff, swapping with x17, which is currently in rdx
mulx r11, r13, r12; x43, x42<- x30 * 0xffffffff
mov rdx, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x30 ], rcx; spilling x399 to mem
mov [ rsp + 0x38 ], r14; spilling x387 to mem
mulx rcx, r14, r12; x41, x40<- x30 * 0xffffffff00000000
adcx rbx, rax
mov rax, -0x2 ; moving imm to reg
inc rax; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, r11
mov r11, 0x0 ; moving imm to reg
adcx r9, r11
mov r11, [ rsi + 0x8 ]; load m64 x1 to register64
mov rax, rdx; preserving value of 0xffffffff00000000 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x40 ], r9; spilling x29 to mem
mov [ rsp + 0x48 ], rbx; spilling x27 to mem
mulx r9, rbx, r11; x80, x79<- x1 * arg1[0]
clc;
adcx r13, rbp
adcx r14, r15
setc r13b; spill CF x58 to reg (r13)
clc;
adcx rbx, r14
mov rdx, 0x100000001 ; moving imm to reg
mulx rbp, r15, rbx; _, x106<- x92 * 0x100000001
mov rbp, rdx; preserving value of 0x100000001 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r14, rax, r11; x78, x77<- x1 * arg1[1]
mov rdx, 0xfffffffffffffffe ; moving imm to reg
mov [ rsp + 0x50 ], rdi; spilling x25 to mem
mulx rbp, rdi, r12; x39, x38<- x30 * 0xfffffffffffffffe
adox rdi, rcx
seto cl; spill OF x47 to reg (rcx)
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, rdx; loading flag
adox r10, rdi
mov r13, 0xffffffff00000000 ; moving imm to reg
mov rdx, r13; 0xffffffff00000000 to rdx
mulx r13, rdi, r15; x117, x116<- x106 * 0xffffffff00000000
mov rdx, 0xffffffff ; moving imm to reg
mov [ rsp + 0x58 ], r14; spilling x78 to mem
mov [ rsp + 0x60 ], r13; spilling x117 to mem
mulx r14, r13, r15; x119, x118<- x106 * 0xffffffff
seto dl; spill OF x60 to reg (rdx)
mov [ rsp + 0x68 ], r8; spilling x23 to mem
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rax, r9
mov r9, [ rsi + 0x10 ]; load m64 x2 to register64
seto r8b; spill OF x82 to reg (r8)
mov byte [ rsp + 0x70 ], dl; spilling byte x60 to mem
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rdi, r14
adcx rax, r10
setc r10b; spill CF x95 to reg (r10)
clc;
adcx r13, rbx
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r13, rbx, r9; x157, x156<- x2 * arg1[0]
adcx rdi, rax
setc dl; spill CF x134 to reg (rdx)
clc;
adcx rbx, rdi
mov r14, 0x100000001 ; moving imm to reg
xchg rdx, r14; 0x100000001, swapping with x134, which is currently in rdx
mulx rax, rdi, rbx; _, x183<- x169 * 0x100000001
mov rax, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rax; 0xffffffffffffffff, swapping with 0x100000001, which is currently in rdx
mov [ rsp + 0x78 ], r13; spilling x157 to mem
mulx rax, r13, r12; x37, x36<- x30 * 0xffffffffffffffff
mov rdx, 0xffffffff ; moving imm to reg
mov [ rsp + 0x80 ], rax; spilling x37 to mem
mov byte [ rsp + 0x88 ], r14b; spilling byte x134 to mem
mulx rax, r14, rdi; x196, x195<- x183 * 0xffffffff
setc dl; spill CF x170 to reg (rdx)
clc;
adcx r14, rbx
mov r14b, dl; preserving value of x170 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x90 ], rax; spilling x196 to mem
mulx rbx, rax, r11; x76, x75<- x1 * arg1[2]
setc dl; spill CF x209 to reg (rdx)
clc;
mov [ rsp + 0x98 ], rbx; spilling x76 to mem
mov rbx, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, rbx; loading flag
adcx rbp, r13
setc cl; spill CF x49 to reg (rcx)
movzx r13, byte [ rsp + 0x70 ]; load byte memx60 to register64
clc;
adcx r13, rbx; loading flag
adcx rbp, [ rsp + 0x68 ]
mov r13, 0xfffffffffffffffe ; moving imm to reg
xchg rdx, r13; 0xfffffffffffffffe, swapping with x209, which is currently in rdx
mov byte [ rsp + 0xa0 ], cl; spilling byte x49 to mem
mulx rbx, rcx, r15; x115, x114<- x106 * 0xfffffffffffffffe
mov rdx, [ rsp + 0x60 ]; x122, copying x117 here, cause x117 is needed in a reg for other than x122, namely all: , x122--x123, size: 1
adox rdx, rcx
seto cl; spill OF x123 to reg (rcx)
mov [ rsp + 0xa8 ], rbx; spilling x115 to mem
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r8, r8b
adox r8, rbx; loading flag
adox rax, [ rsp + 0x58 ]
seto r8b; spill OF x84 to reg (r8)
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
movzx r10, r10b
adox r10, rbx; loading flag
adox rbp, rax
setc r10b; spill CF x62 to reg (r10)
movzx rax, byte [ rsp + 0x88 ]; load byte memx134 to register64
clc;
adcx rax, rbx; loading flag
adcx rbp, rdx
mov rdx, r9; x2 to rdx
mulx r9, rax, [ rsi + 0x8 ]; x155, x154<- x2 * arg1[1]
setc bl; spill CF x136 to reg (rbx)
clc;
adcx rax, [ rsp + 0x78 ]
mov [ rsp + 0xb0 ], r9; spilling x155 to mem
setc r9b; spill CF x159 to reg (r9)
clc;
mov byte [ rsp + 0xb8 ], bl; spilling byte x136 to mem
mov rbx, -0x1 ; moving imm to reg
movzx r14, r14b
adcx r14, rbx; loading flag
adcx rbp, rax
mov r14, 0xffffffff00000000 ; moving imm to reg
xchg rdx, r14; 0xffffffff00000000, swapping with x2, which is currently in rdx
mulx rax, rbx, rdi; x194, x193<- x183 * 0xffffffff00000000
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov byte [ rsp + 0xc0 ], r9b; spilling byte x159 to mem
mov [ rsp + 0xc8 ], rax; spilling x194 to mem
mulx r9, rax, r12; x35, x34<- x30 * 0xffffffffffffffff
setc dl; spill CF x172 to reg (rdx)
clc;
adcx rbx, [ rsp + 0x90 ]
mov byte [ rsp + 0xd0 ], dl; spilling byte x172 to mem
setc dl; spill CF x198 to reg (rdx)
clc;
mov [ rsp + 0xd8 ], r9; spilling x35 to mem
mov r9, -0x1 ; moving imm to reg
movzx r13, r13b
adcx r13, r9; loading flag
adcx rbp, rbx
setc r13b; spill CF x211 to reg (r13)
movzx rbx, byte [ rsp + 0xa0 ]; load byte memx49 to register64
clc;
adcx rbx, r9; loading flag
adcx rax, [ rsp + 0x80 ]
setc bl; spill CF x51 to reg (rbx)
clc;
movzx r10, r10b
adcx r10, r9; loading flag
adcx rax, [ rsp + 0x50 ]
mov r10b, dl; preserving value of x198 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0xe0 ], rbp; spilling x210 to mem
mulx r9, rbp, r11; x74, x73<- x1 * arg1[3]
setc dl; spill CF x64 to reg (rdx)
clc;
mov byte [ rsp + 0xe8 ], r13b; spilling byte x211 to mem
mov r13, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, r13; loading flag
adcx rbp, [ rsp + 0x98 ]
mov r8, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r8; 0xffffffffffffffff, swapping with x64, which is currently in rdx
mulx r12, r13, r12; x33, x32<- x30 * 0xffffffffffffffff
mov [ rsp + 0xf0 ], r12; spilling x33 to mem
mov byte [ rsp + 0xf8 ], r8b; spilling byte x64 to mem
mulx r12, r8, r15; x113, x112<- x106 * 0xffffffffffffffff
adox rbp, rax
setc al; spill CF x86 to reg (rax)
clc;
mov rdx, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, rdx; loading flag
adcx r8, [ rsp + 0xa8 ]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x100 ], r12; spilling x113 to mem
mulx rcx, r12, r14; x153, x152<- x2 * arg1[2]
mov rdx, 0xfffffffffffffffe ; moving imm to reg
mov [ rsp + 0x108 ], rcx; spilling x153 to mem
mov [ rsp + 0x110 ], r9; spilling x74 to mem
mulx rcx, r9, rdi; x192, x191<- x183 * 0xfffffffffffffffe
setc dl; spill CF x125 to reg (rdx)
mov [ rsp + 0x118 ], rcx; spilling x192 to mem
movzx rcx, byte [ rsp + 0xb8 ]; load byte memx136 to register64
clc;
mov byte [ rsp + 0x120 ], al; spilling byte x86 to mem
mov rax, -0x1 ; moving imm to reg
adcx rcx, rax; loading flag
adcx rbp, r8
setc cl; spill CF x138 to reg (rcx)
clc;
movzx r10, r10b
adcx r10, rax; loading flag
adcx r9, [ rsp + 0xc8 ]
setc r10b; spill CF x200 to reg (r10)
movzx r8, byte [ rsp + 0xc0 ]; load byte memx159 to register64
clc;
adcx r8, rax; loading flag
adcx r12, [ rsp + 0xb0 ]
mov r8b, dl; preserving value of x125 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov byte [ rsp + 0x128 ], r10b; spilling byte x200 to mem
mulx rax, r10, r11; x72, x71<- x1 * arg1[4]
setc dl; spill CF x161 to reg (rdx)
clc;
mov byte [ rsp + 0x130 ], cl; spilling byte x138 to mem
mov rcx, -0x1 ; moving imm to reg
movzx rbx, bl
adcx rbx, rcx; loading flag
adcx r13, [ rsp + 0xd8 ]
setc bl; spill CF x53 to reg (rbx)
movzx rcx, byte [ rsp + 0xd0 ]; load byte memx172 to register64
clc;
mov byte [ rsp + 0x138 ], dl; spilling byte x161 to mem
mov rdx, -0x1 ; moving imm to reg
adcx rcx, rdx; loading flag
adcx rbp, r12
mov rcx, 0xffffffffffffffff ; moving imm to reg
mov rdx, rcx; 0xffffffffffffffff to rdx
mulx rcx, r12, r15; x111, x110<- x106 * 0xffffffffffffffff
setc dl; spill CF x174 to reg (rdx)
mov [ rsp + 0x140 ], rcx; spilling x111 to mem
movzx rcx, byte [ rsp + 0x120 ]; load byte memx86 to register64
clc;
mov byte [ rsp + 0x148 ], bl; spilling byte x53 to mem
mov rbx, -0x1 ; moving imm to reg
adcx rcx, rbx; loading flag
adcx r10, [ rsp + 0x110 ]
setc cl; spill CF x88 to reg (rcx)
movzx rbx, byte [ rsp + 0xe8 ]; load byte memx211 to register64
clc;
mov byte [ rsp + 0x150 ], dl; spilling byte x174 to mem
mov rdx, -0x1 ; moving imm to reg
adcx rbx, rdx; loading flag
adcx rbp, r9
setc bl; spill CF x213 to reg (rbx)
clc;
movzx r8, r8b
adcx r8, rdx; loading flag
adcx r12, [ rsp + 0x100 ]
setc r8b; spill CF x127 to reg (r8)
movzx r9, byte [ rsp + 0xf8 ]; load byte memx64 to register64
clc;
adcx r9, rdx; loading flag
adcx r13, [ rsp + 0x48 ]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x158 ], rbp; spilling x212 to mem
mulx r9, rbp, r14; x151, x150<- x2 * arg1[3]
adox r10, r13
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mulx r11, r13, r11; x70, x69<- x1 * arg1[5]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x160 ], r9; spilling x151 to mem
mov byte [ rsp + 0x168 ], r8b; spilling byte x127 to mem
mulx r9, r8, rdi; x190, x189<- x183 * 0xffffffffffffffff
setc dl; spill CF x66 to reg (rdx)
clc;
mov [ rsp + 0x170 ], r9; spilling x190 to mem
mov r9, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, r9; loading flag
adcx rax, r13
setc cl; spill CF x90 to reg (rcx)
movzx r13, byte [ rsp + 0x138 ]; load byte memx161 to register64
clc;
adcx r13, r9; loading flag
adcx rbp, [ rsp + 0x108 ]
setc r13b; spill CF x163 to reg (r13)
movzx r9, byte [ rsp + 0x130 ]; load byte memx138 to register64
clc;
mov [ rsp + 0x178 ], rax; spilling x89 to mem
mov rax, -0x1 ; moving imm to reg
adcx r9, rax; loading flag
adcx r10, r12
setc r9b; spill CF x140 to reg (r9)
movzx r12, byte [ rsp + 0x150 ]; load byte memx174 to register64
clc;
adcx r12, rax; loading flag
adcx r10, rbp
setc r12b; spill CF x176 to reg (r12)
movzx rbp, byte [ rsp + 0x128 ]; load byte memx200 to register64
clc;
adcx rbp, rax; loading flag
adcx r8, [ rsp + 0x118 ]
setc bpl; spill CF x202 to reg (rbp)
clc;
movzx rbx, bl
adcx rbx, rax; loading flag
adcx r10, r8
movzx rbx, byte [ rsp + 0x148 ]; x54, copying x53 here, cause x53 is needed in a reg for other than x54, namely all: , x54, size: 1
mov r8, [ rsp + 0xf0 ]; load m64 x33 to register64
lea rbx, [ rbx + r8 ]; r8/64 + m8
setc r8b; spill CF x215 to reg (r8)
clc;
movzx rdx, dl
adcx rdx, rax; loading flag
adcx rbx, [ rsp + 0x40 ]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x180 ], r10; spilling x214 to mem
mulx rax, r10, r14; x149, x148<- x2 * arg1[4]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x188 ], rax; spilling x149 to mem
mulx r15, rax, r15; x109, x108<- x106 * 0xffffffffffffffff
mov byte [ rsp + 0x190 ], r8b; spilling byte x215 to mem
mov byte [ rsp + 0x198 ], r12b; spilling byte x176 to mem
mulx r8, r12, rdi; x188, x187<- x183 * 0xffffffffffffffff
movzx rdx, cl; x91, copying x90 here, cause x90 is needed in a reg for other than x91, namely all: , x91, size: 1
lea rdx, [ rdx + r11 ]
mov r11, [ rsp + 0x178 ]; x102, copying x89 here, cause x89 is needed in a reg for other than x102, namely all: , x102--x103, size: 1
adox r11, rbx
setc cl; spill CF x68 to reg (rcx)
movzx rbx, byte [ rsp + 0x168 ]; load byte memx127 to register64
clc;
mov [ rsp + 0x1a0 ], r8; spilling x188 to mem
mov r8, -0x1 ; moving imm to reg
adcx rbx, r8; loading flag
adcx rax, [ rsp + 0x140 ]
movzx rbx, cl; x104, copying x68 here, cause x68 is needed in a reg for other than x104, namely all: , x104--x105, size: 1
adox rbx, rdx
mov rcx, 0x0 ; moving imm to reg
adcx r15, rcx
clc;
movzx r13, r13b
adcx r13, r8; loading flag
adcx r10, [ rsp + 0x160 ]
seto r13b; spill OF x105 to reg (r13)
inc r8; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov rcx, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, rcx; loading flag
adox r11, rax
setc r9b; spill CF x165 to reg (r9)
clc;
movzx rbp, bpl
adcx rbp, rcx; loading flag
adcx r12, [ rsp + 0x170 ]
adox r15, rbx
setc bpl; spill CF x204 to reg (rbp)
movzx rdx, byte [ rsp + 0x198 ]; load byte memx176 to register64
clc;
adcx rdx, rcx; loading flag
adcx r11, r10
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mulx r14, rax, r14; x147, x146<- x2 * arg1[5]
setc dl; spill CF x178 to reg (rdx)
movzx rbx, byte [ rsp + 0x190 ]; load byte memx215 to register64
clc;
adcx rbx, rcx; loading flag
adcx r11, r12
mov rbx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbx; 0xffffffffffffffff, swapping with x178, which is currently in rdx
mulx rdi, r10, rdi; x186, x185<- x183 * 0xffffffffffffffff
movzx r12, r13b; x145, copying x105 here, cause x105 is needed in a reg for other than x145, namely all: , x145, size: 1
adox r12, r8
dec r8; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx r9, r9b
adox r9, r8; loading flag
adox rax, [ rsp + 0x188 ]
mov rcx, 0x0 ; moving imm to reg
adox r14, rcx
dec rcx; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx rbx, bl
adox rbx, rcx; loading flag
adox r15, rax
adox r14, r12
seto r8b; spill OF x182 to reg (r8)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, r13; loading flag
adox r10, [ rsp + 0x1a0 ]
adox rdi, rcx
mov r9, [ rsi + 0x18 ]; load m64 x3 to register64
xchg rdx, r9; x3, swapping with 0xffffffffffffffff, which is currently in rdx
mulx rbp, rbx, [ rsi + 0x8 ]; x232, x231<- x3 * arg1[1]
adcx r10, r15
adcx rdi, r14
mulx r12, rax, [ rsi + 0x0 ]; x234, x233<- x3 * arg1[0]
movzx r15, r8b; x222, copying x182 here, cause x182 is needed in a reg for other than x222, namely all: , x222, size: 1
adc r15, 0x0
add rax, [ rsp + 0xe0 ]; could be done better, if r0 has been u8 as well
mov r8, 0x100000001 ; moving imm to reg
xchg rdx, rax; x246, swapping with x3, which is currently in rdx
mulx r14, rcx, r8; _, x260<- x246 * 0x100000001
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rbx, r12
mov r14, 0xffffffff00000000 ; moving imm to reg
xchg rdx, rcx; x260, swapping with x246, which is currently in rdx
mulx r12, r13, r14; x271, x270<- x260 * 0xffffffff00000000
mov r14, 0xffffffff ; moving imm to reg
mulx r9, r8, r14; x273, x272<- x260 * 0xffffffff
mov r14, 0xfffffffffffffffe ; moving imm to reg
mov [ rsp + 0x1a8 ], r15; spilling x222 to mem
mov [ rsp + 0x1b0 ], rdi; spilling x220 to mem
mulx r15, rdi, r14; x269, x268<- x260 * 0xfffffffffffffffe
mov r14, [ rsp + 0x158 ]; x248, copying x212 here, cause x212 is needed in a reg for other than x248, namely all: , x248--x249, size: 1
adcx r14, rbx
setc bl; spill CF x249 to reg (rbx)
clc;
adcx r13, r9
adcx rdi, r12
xchg rdx, rax; x3, swapping with x260, which is currently in rdx
mulx r12, r9, [ rsi + 0x10 ]; x230, x229<- x3 * arg1[2]
mov [ rsp + 0x1b8 ], r10; spilling x218 to mem
setc r10b; spill CF x277 to reg (r10)
clc;
adcx r8, rcx
mulx r8, rcx, [ rsi + 0x18 ]; x228, x227<- x3 * arg1[3]
adox r9, rbp
adox rcx, r12
mov rbp, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rax; x260, swapping with x3, which is currently in rdx
mov [ rsp + 0x1c0 ], r8; spilling x228 to mem
mulx r12, r8, rbp; x267, x266<- x260 * 0xffffffffffffffff
adcx r13, r14
seto r14b; spill OF x240 to reg (r14)
mov rbp, 0x0 ; moving imm to reg
dec rbp; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbx, bl
adox rbx, rbp; loading flag
adox r9, [ rsp + 0x180 ]
adox rcx, r11
mov r11, 0xffffffffffffffff ; moving imm to reg
mulx rbx, rbp, r11; x265, x264<- x260 * 0xffffffffffffffff
adcx rdi, r9
seto r9b; spill OF x253 to reg (r9)
mov r11, 0x0 ; moving imm to reg
dec r11; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r10, r10b
adox r10, r11; loading flag
adox r15, r8
xchg rdx, rax; x3, swapping with x260, which is currently in rdx
mulx r10, r8, [ rsi + 0x28 ]; x224, x223<- x3 * arg1[5]
adcx r15, rcx
adox rbp, r12
mulx rdx, r12, [ rsi + 0x20 ]; x226, x225<- x3 * arg1[4]
setc cl; spill CF x292 to reg (rcx)
clc;
movzx r14, r14b
adcx r14, r11; loading flag
adcx r12, [ rsp + 0x1c0 ]
adcx r8, rdx
setc r14b; spill CF x244 to reg (r14)
clc;
movzx r9, r9b
adcx r9, r11; loading flag
adcx r12, [ rsp + 0x1b8 ]
mov r9, [ rsp + 0x1b0 ]; x256, copying x220 here, cause x220 is needed in a reg for other than x256, namely all: , x256--x257, size: 1
adcx r9, r8
mov rdx, 0xffffffffffffffff ; moving imm to reg
mulx rax, r8, rax; x263, x262<- x260 * 0xffffffffffffffff
mov r11, [ rsi + 0x20 ]; load m64 x4 to register64
movzx rdx, r14b; x245, copying x244 here, cause x244 is needed in a reg for other than x245, namely all: , x245, size: 1
lea rdx, [ rdx + r10 ]
adox r8, rbx
mov rbx, [ rsp + 0x1a8 ]; x258, copying x222 here, cause x222 is needed in a reg for other than x258, namely all: , x258--x259, size: 1
adcx rbx, rdx
mov r10, 0x0 ; moving imm to reg
adox rax, r10
dec r10; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx rcx, cl
adox rcx, r10; loading flag
adox r12, rbp
adox r8, r9
adox rax, rbx
seto cl; spill OF x299 to reg (rcx)
adc cl, 0x0
movzx rcx, cl
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbp, r14, r11; x309, x308<- x4 * arg1[1]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r9, rbx, r11; x311, x310<- x4 * arg1[0]
adox rbx, r13
mov rdx, 0x100000001 ; moving imm to reg
mulx r13, r10, rbx; _, x337<- x323 * 0x100000001
adcx r14, r9
mov r13, 0xffffffff00000000 ; moving imm to reg
xchg rdx, r10; x337, swapping with 0x100000001, which is currently in rdx
mulx r9, r10, r13; x348, x347<- x337 * 0xffffffff00000000
mov r13, 0xffffffff ; moving imm to reg
mov byte [ rsp + 0x1c8 ], cl; spilling byte x299 to mem
mov [ rsp + 0x1d0 ], rax; spilling x297 to mem
mulx rcx, rax, r13; x350, x349<- x337 * 0xffffffff
adox r14, rdi
seto dil; spill OF x326 to reg (rdi)
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r10, rcx
seto cl; spill OF x352 to reg (rcx)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rax, rbx
mov rax, rdx; preserving value of x337 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx rbx, r13, r11; x307, x306<- x4 * arg1[2]
adox r10, r14
mov rdx, 0xfffffffffffffffe ; moving imm to reg
mov [ rsp + 0x1d8 ], r10; spilling x364 to mem
mulx r14, r10, rax; x346, x345<- x337 * 0xfffffffffffffffe
adcx r13, rbp
setc bpl; spill CF x315 to reg (rbp)
clc;
mov rdx, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, rdx; loading flag
adcx r9, r10
setc cl; spill CF x354 to reg (rcx)
clc;
movzx rdi, dil
adcx rdi, rdx; loading flag
adcx r15, r13
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rdi, r10, r11; x305, x304<- x4 * arg1[3]
adox r9, r15
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r13, r15, r11; x303, x302<- x4 * arg1[4]
seto dl; spill OF x367 to reg (rdx)
mov [ rsp + 0x1e0 ], r9; spilling x366 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbp, bpl
adox rbp, r9; loading flag
adox rbx, r10
adcx rbx, r12
adox r15, rdi
mov r12, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rax; x337, swapping with x367, which is currently in rdx
mulx rbp, rdi, r12; x344, x343<- x337 * 0xffffffffffffffff
adcx r15, r8
seto r8b; spill OF x319 to reg (r8)
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r10, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r10; loading flag
adox r14, rdi
setc cl; spill CF x332 to reg (rcx)
clc;
movzx rax, al
adcx rax, r10; loading flag
adcx rbx, r14
mulx rax, rdi, r12; x342, x341<- x337 * 0xffffffffffffffff
adox rdi, rbp
mulx rdx, rbp, r12; x340, x339<- x337 * 0xffffffffffffffff
adox rbp, rax
adox rdx, r9
xchg rdx, r11; x4, swapping with x361, which is currently in rdx
mulx rdx, r14, [ rsi + 0x28 ]; x301, x300<- x4 * arg1[5]
dec r9; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx r8, r8b
adox r8, r9; loading flag
adox r13, r14
mov r10, 0x0 ; moving imm to reg
adox rdx, r10
adcx rdi, r15
dec r10; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx rcx, cl
adox rcx, r10; loading flag
adox r13, [ rsp + 0x1d0 ]
adcx rbp, r13
movzx r9, byte [ rsp + 0x1c8 ]; x335, copying x299 here, cause x299 is needed in a reg for other than x335, namely all: , x335--x336, size: 1
adox r9, rdx
mov r8, [ rsp + 0x1d8 ]; load m64 x364 to register64
seto cl; spill OF x336 to reg (rcx)
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r8, [ rsp + 0x38 ]
mov r15, [ rsp + 0x1e0 ]; load m64 x366 to register64
mov rax, [ rsp + 0x28 ]; x402, copying x389 here, cause x389 is needed in a reg for other than x402, namely all: , x402--x403, size: 1
adox rax, r15
adcx r11, r9
mov r15, [ rsp + 0x20 ]; x404, copying x391 here, cause x391 is needed in a reg for other than x404, namely all: , x404--x405, size: 1
adox r15, rbx
movzx rbx, cl; x376, copying x336 here, cause x336 is needed in a reg for other than x376, namely all: , x376, size: 1
adcx rbx, r10
mov r14, 0x100000001 ; moving imm to reg
mov rdx, r14; 0x100000001 to rdx
mulx r14, r13, r8; _, x414<- x400 * 0x100000001
mov r14, 0xffffffff00000000 ; moving imm to reg
xchg rdx, r13; x414, swapping with 0x100000001, which is currently in rdx
mulx rcx, r9, r14; x425, x424<- x414 * 0xffffffff00000000
mov r10, 0xfffffffffffffffe ; moving imm to reg
mulx r14, r13, r10; x423, x422<- x414 * 0xfffffffffffffffe
mov r10, 0xffffffff ; moving imm to reg
mov [ rsp + 0x1e8 ], rbx; spilling x376 to mem
mulx r12, rbx, r10; x427, x426<- x414 * 0xffffffff
clc;
adcx rbx, r8
mov rbx, [ rsp + 0x18 ]; x406, copying x393 here, cause x393 is needed in a reg for other than x406, namely all: , x406--x407, size: 1
adox rbx, rdi
seto dil; spill OF x407 to reg (rdi)
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r9, r12
adox r13, rcx
adcx r9, rax
adcx r13, r15
setc al; spill CF x444 to reg (rax)
seto r15b; spill OF x431 to reg (r15)
mov rcx, r9; x454, copying x441 here, cause x441 is needed in a reg for other than x454, namely all: , x468, x454--x455, size: 2
sub rcx, r10
mov r12, 0xffffffffffffffff ; moving imm to reg
mulx r8, r10, r12; x419, x418<- x414 * 0xffffffffffffffff
mov r12, r13; x456, copying x443 here, cause x443 is needed in a reg for other than x456, namely all: , x456--x457, x469, size: 2
mov [ rsp + 0x1f0 ], rcx; spilling x454 to mem
mov rcx, 0xffffffff00000000 ; moving imm to reg
sbb r12, rcx
mov rcx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x1f8 ], r12; spilling x456 to mem
mov [ rsp + 0x200 ], r8; spilling x419 to mem
mulx r12, r8, rcx; x421, x420<- x414 * 0xffffffffffffffff
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r15, r15b
adox r15, rcx; loading flag
adox r14, r8
adox r10, r12
setc r15b; spill CF x457 to reg (r15)
clc;
movzx rdi, dil
adcx rdi, rcx; loading flag
adcx rbp, [ rsp + 0x10 ]
setc dil; spill CF x409 to reg (rdi)
clc;
movzx rax, al
adcx rax, rcx; loading flag
adcx rbx, r14
adcx r10, rbp
setc al; spill CF x448 to reg (rax)
seto r12b; spill OF x435 to reg (r12)
movzx r8, r15b; x457, copying x457 here, cause x457 is needed in a reg for other than x457, namely all: , x458--x459, size: 1
add r8, -0x1
mov r15, rbx; x458, copying x445 here, cause x445 is needed in a reg for other than x458, namely all: , x458--x459, x470, size: 2
mov r8, 0xfffffffffffffffe ; moving imm to reg
sbb r15, r8
mov r14, r10; x460, copying x447 here, cause x447 is needed in a reg for other than x460, namely all: , x460--x461, x471, size: 2
mov rbp, 0xffffffffffffffff ; moving imm to reg
sbb r14, rbp
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rcx, -0x1 ; moving imm to reg
movzx rdi, dil
adox rdi, rcx; loading flag
adox r11, [ rsp + 0x8 ]
mulx rdx, rdi, rbp; x417, x416<- x414 * 0xffffffffffffffff
mov rcx, [ rsp + 0x30 ]; load m64 x399 to register64
mov r8, [ rsp + 0x1e8 ]; x412, copying x376 here, cause x376 is needed in a reg for other than x412, namely all: , x412--x413, size: 1
adox r8, rcx
seto cl; spill OF x413 to reg (rcx)
mov rbp, -0x1 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, rbp; loading flag
adox rdi, [ rsp + 0x200 ]
mov r12, 0x0 ; moving imm to reg
adox rdx, r12
inc rbp; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov r12, -0x1 ; moving imm to reg
movzx rax, al
adox rax, r12; loading flag
adox r11, rdi
adox rdx, r8
movzx rax, cl; x453, copying x413 here, cause x413 is needed in a reg for other than x453, namely all: , x453, size: 1
adox rax, rbp
mov rcx, r11; x462, copying x449 here, cause x449 is needed in a reg for other than x462, namely all: , x462--x463, x472, size: 2
mov r8, 0xffffffffffffffff ; moving imm to reg
sbb rcx, r8
mov rdi, rdx; x464, copying x451 here, cause x451 is needed in a reg for other than x464, namely all: , x464--x465, x473, size: 2
sbb rdi, r8
sbb rax, 0x00000000
cmovc r14, r10; if CF, x471<- x447 (nzVar)
mov rax, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rax + 0x18 ], r14; out1[3] = x471
cmovc rcx, r11; if CF, x472<- x449 (nzVar)
mov [ rax + 0x20 ], rcx; out1[4] = x472
mov r10, [ rsp + 0x1f8 ]; x469, copying x456 here, cause x456 is needed in a reg for other than x469, namely all: , x469, size: 1
cmovc r10, r13; if CF, x469<- x443 (nzVar)
cmovc r15, rbx; if CF, x470<- x445 (nzVar)
cmovc rdi, rdx; if CF, x473<- x451 (nzVar)
mov [ rax + 0x10 ], r15; out1[2] = x470
mov [ rax + 0x8 ], r10; out1[1] = x469
mov r13, [ rsp + 0x1f0 ]; x468, copying x454 here, cause x454 is needed in a reg for other than x468, namely all: , x468, size: 1
cmovc r13, r9; if CF, x468<- x441 (nzVar)
mov [ rax + 0x28 ], rdi; out1[5] = x473
mov [ rax + 0x0 ], r13; out1[0] = x468
mov rbx, [ rsp + 0x208 ]; restoring from stack
mov rbp, [ rsp + 0x210 ]; restoring from stack
mov r12, [ rsp + 0x218 ]; restoring from stack
mov r13, [ rsp + 0x220 ]; restoring from stack
mov r14, [ rsp + 0x228 ]; restoring from stack
mov r15, [ rsp + 0x230 ]; restoring from stack
add rsp, 0x238 
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; clocked at 2600 MHz
; first cyclecount 282.885, best 230.75555555555556, lastGood 235.0909090909091
; seed 718657245800066 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4020872 ms / 60000 runs=> 67.01453333333333ms/run
; Time spent for assembling and measureing (initial batch_size=44, initial num_batches=101): 160297 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.03986622802218026
; number reverted permutation/ tried permutation: 24675 / 30167 =81.795%
; number reverted decision/ tried decision: 21484 / 29834 =72.012%