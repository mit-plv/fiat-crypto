SECTION .text
	GLOBAL mul_p384
mul_p384:
sub rsp, 0x2e8 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x2b8 ], rbx; saving to stack
mov [ rsp + 0x2c0 ], rbp; saving to stack
mov [ rsp + 0x2c8 ], r12; saving to stack
mov [ rsp + 0x2d0 ], r13; saving to stack
mov [ rsp + 0x2d8 ], r14; saving to stack
mov [ rsp + 0x2e0 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x6 to register64
mov r10, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x0 ]; saving arg2[0] in rdx.
mulx r11, rbx, rax; x18, x17<- x6 * arg2[0]
mov rbp, 0x100000001 ; moving imm to reg
mov rdx, rbx; x17 to rdx
mulx rbx, r12, rbp; _, x30<- x17 * 0x100000001
xchg rdx, rax; x6, swapping with x17, which is currently in rdx
mulx rbx, r13, [ r10 + 0x8 ]; x16, x15<- x6 * arg2[1]
add r13, r11; could be done better, if r0 has been u8 as well
mov r14, 0xffffffff ; moving imm to reg
xchg rdx, r12; x30, swapping with x6, which is currently in rdx
mulx r15, rcx, r14; x43, x42<- x30 * 0xffffffff
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rcx, rax
mov rcx, 0xffffffff00000000 ; moving imm to reg
mulx r9, r11, rcx; x41, x40<- x30 * 0xffffffff00000000
seto al; spill OF x56 to reg (rax)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r11, r15
mov r15, [ rsi + 0x8 ]; load m64 x1 to register64
mov r8, rdx; preserving value of x30 into a new reg
mov rdx, [ r10 + 0x0 ]; saving arg2[0] in rdx.
mulx rbp, rcx, r15; x80, x79<- x1 * arg2[0]
seto r14b; spill OF x45 to reg (r14)
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov rdi, 0x0 ; moving imm to reg
dec rdi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rax, al
adox rax, rdi; loading flag
adox r13, r11
seto al; spill OF x58 to reg (rax)
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rcx, r13
mov r11, 0x100000001 ; moving imm to reg
mov rdx, r11; 0x100000001 to rdx
mulx r11, r13, rcx; _, x106<- x92 * 0x100000001
mov r11, 0xffffffff ; moving imm to reg
xchg rdx, r13; x106, swapping with 0x100000001, which is currently in rdx
mulx rdi, r13, r11; x119, x118<- x106 * 0xffffffff
mov r11, rdx; preserving value of x106 into a new reg
mov rdx, [ r10 + 0x10 ]; saving arg2[2] in rdx.
mov [ rsp + 0x8 ], rdi; spilling x119 to mem
mov [ rsp + 0x10 ], rbp; spilling x80 to mem
mulx rdi, rbp, r12; x14, x13<- x6 * arg2[2]
adcx rbp, rbx
seto bl; spill OF x93 to reg (rbx)
mov [ rsp + 0x18 ], rdi; spilling x14 to mem
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, rcx
mov r13, 0xfffffffffffffffe ; moving imm to reg
mov rdx, r13; 0xfffffffffffffffe to rdx
mulx r13, rcx, r8; x39, x38<- x30 * 0xfffffffffffffffe
seto dil; spill OF x132 to reg (rdi)
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, rdx; loading flag
adox r9, rcx
mov r14, 0xffffffff00000000 ; moving imm to reg
mov rdx, r14; 0xffffffff00000000 to rdx
mulx r14, rcx, r11; x117, x116<- x106 * 0xffffffff00000000
setc dl; spill CF x22 to reg (rdx)
clc;
mov [ rsp + 0x20 ], r14; spilling x117 to mem
mov r14, -0x1 ; moving imm to reg
movzx rax, al
adcx rax, r14; loading flag
adcx rbp, r9
mov al, dl; preserving value of x22 into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mulx r9, r14, r15; x78, x77<- x1 * arg2[1]
mov [ rsp + 0x28 ], r9; spilling x78 to mem
setc r9b; spill CF x60 to reg (r9)
clc;
adcx r14, [ rsp + 0x10 ]
mov byte [ rsp + 0x30 ], r9b; spilling byte x60 to mem
setc r9b; spill CF x82 to reg (r9)
clc;
mov [ rsp + 0x38 ], r13; spilling x39 to mem
mov r13, -0x1 ; moving imm to reg
movzx rbx, bl
adcx rbx, r13; loading flag
adcx rbp, r14
seto bl; spill OF x47 to reg (rbx)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rcx, [ rsp + 0x8 ]
seto r14b; spill OF x121 to reg (r14)
dec r13; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx rdi, dil
adox rdi, r13; loading flag
adox rbp, rcx
mov rdi, [ rsi + 0x10 ]; load m64 x2 to register64
mov rdx, [ r10 + 0x0 ]; arg2[0] to rdx
mulx rcx, r13, rdi; x157, x156<- x2 * arg2[0]
mov [ rsp + 0x40 ], rcx; spilling x157 to mem
seto cl; spill OF x134 to reg (rcx)
mov byte [ rsp + 0x48 ], r14b; spilling byte x121 to mem
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, rbp
mov rbp, 0x100000001 ; moving imm to reg
mov rdx, r13; x169 to rdx
mulx r13, r14, rbp; _, x183<- x169 * 0x100000001
mov r13, 0xffffffff ; moving imm to reg
xchg rdx, r13; 0xffffffff, swapping with x169, which is currently in rdx
mov byte [ rsp + 0x50 ], cl; spilling byte x134 to mem
mulx rbp, rcx, r14; x196, x195<- x183 * 0xffffffff
seto dl; spill OF x170 to reg (rdx)
mov [ rsp + 0x58 ], rbp; spilling x196 to mem
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rcx, r13
mov cl, dl; preserving value of x170 into a new reg
mov rdx, [ r10 + 0x18 ]; saving arg2[3] in rdx.
mulx r13, rbp, r12; x12, x11<- x6 * arg2[3]
mov [ rsp + 0x60 ], r13; spilling x12 to mem
mov r13, 0xffffffffffffffff ; moving imm to reg
mov rdx, r13; 0xffffffffffffffff to rdx
mov byte [ rsp + 0x68 ], cl; spilling byte x170 to mem
mulx r13, rcx, r8; x37, x36<- x30 * 0xffffffffffffffff
seto dl; spill OF x209 to reg (rdx)
mov [ rsp + 0x70 ], r13; spilling x37 to mem
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rax, al
adox rax, r13; loading flag
adox rbp, [ rsp + 0x18 ]
seto al; spill OF x24 to reg (rax)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, r13; loading flag
adox rcx, [ rsp + 0x38 ]
seto bl; spill OF x49 to reg (rbx)
movzx r13, byte [ rsp + 0x30 ]; load byte memx60 to register64
mov byte [ rsp + 0x78 ], al; spilling byte x24 to mem
mov rax, 0x0 ; moving imm to reg
dec rax; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r13, rax; loading flag
adox rbp, rcx
mov r13b, dl; preserving value of x209 into a new reg
mov rdx, [ r10 + 0x10 ]; saving arg2[2] in rdx.
mulx rcx, rax, r15; x76, x75<- x1 * arg2[2]
mov [ rsp + 0x80 ], rcx; spilling x76 to mem
mov rcx, 0xfffffffffffffffe ; moving imm to reg
mov rdx, rcx; 0xfffffffffffffffe to rdx
mov byte [ rsp + 0x88 ], bl; spilling byte x49 to mem
mulx rcx, rbx, r11; x115, x114<- x106 * 0xfffffffffffffffe
seto dl; spill OF x62 to reg (rdx)
mov [ rsp + 0x90 ], rcx; spilling x115 to mem
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r9, r9b
adox r9, rcx; loading flag
adox rax, [ rsp + 0x28 ]
adcx rax, rbp
setc r9b; spill CF x97 to reg (r9)
movzx rbp, byte [ rsp + 0x48 ]; load byte memx121 to register64
clc;
adcx rbp, rcx; loading flag
adcx rbx, [ rsp + 0x20 ]
mov bpl, dl; preserving value of x62 into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mov byte [ rsp + 0x98 ], r9b; spilling byte x97 to mem
mulx rcx, r9, rdi; x155, x154<- x2 * arg2[1]
mov [ rsp + 0xa0 ], rcx; spilling x155 to mem
setc cl; spill CF x123 to reg (rcx)
mov byte [ rsp + 0xa8 ], bpl; spilling byte x62 to mem
movzx rbp, byte [ rsp + 0x50 ]; load byte memx134 to register64
clc;
mov byte [ rsp + 0xb0 ], r13b; spilling byte x209 to mem
mov r13, -0x1 ; moving imm to reg
adcx rbp, r13; loading flag
adcx rax, rbx
setc bpl; spill CF x136 to reg (rbp)
clc;
adcx r9, [ rsp + 0x40 ]
mov rdx, [ r10 + 0x20 ]; arg2[4] to rdx
mulx rbx, r13, r12; x10, x9<- x6 * arg2[4]
mov [ rsp + 0xb8 ], rbx; spilling x10 to mem
setc bl; spill CF x159 to reg (rbx)
mov byte [ rsp + 0xc0 ], bpl; spilling byte x136 to mem
movzx rbp, byte [ rsp + 0x68 ]; load byte memx170 to register64
clc;
mov byte [ rsp + 0xc8 ], cl; spilling byte x123 to mem
mov rcx, -0x1 ; moving imm to reg
adcx rbp, rcx; loading flag
adcx rax, r9
mov rbp, 0xffffffff00000000 ; moving imm to reg
mov rdx, r14; x183 to rdx
mulx r14, r9, rbp; x194, x193<- x183 * 0xffffffff00000000
setc cl; spill CF x172 to reg (rcx)
clc;
adcx r9, [ rsp + 0x58 ]
setc bpl; spill CF x198 to reg (rbp)
mov [ rsp + 0xd0 ], r14; spilling x194 to mem
movzx r14, byte [ rsp + 0xb0 ]; load byte memx209 to register64
clc;
mov byte [ rsp + 0xd8 ], cl; spilling byte x172 to mem
mov rcx, -0x1 ; moving imm to reg
adcx r14, rcx; loading flag
adcx rax, r9
setc r14b; spill CF x211 to reg (r14)
movzx r9, byte [ rsp + 0x78 ]; load byte memx24 to register64
clc;
adcx r9, rcx; loading flag
adcx r13, [ rsp + 0x60 ]
mov r9, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r9; 0xffffffffffffffff, swapping with x183, which is currently in rdx
mov [ rsp + 0xe0 ], rax; spilling x210 to mem
mulx rcx, rax, r8; x35, x34<- x30 * 0xffffffffffffffff
setc dl; spill CF x26 to reg (rdx)
mov [ rsp + 0xe8 ], rcx; spilling x35 to mem
movzx rcx, byte [ rsp + 0x88 ]; load byte memx49 to register64
clc;
mov byte [ rsp + 0xf0 ], r14b; spilling byte x211 to mem
mov r14, -0x1 ; moving imm to reg
adcx rcx, r14; loading flag
adcx rax, [ rsp + 0x70 ]
setc cl; spill CF x51 to reg (rcx)
movzx r14, byte [ rsp + 0xa8 ]; load byte memx62 to register64
clc;
mov byte [ rsp + 0xf8 ], dl; spilling byte x26 to mem
mov rdx, -0x1 ; moving imm to reg
adcx r14, rdx; loading flag
adcx r13, rax
mov rdx, [ r10 + 0x18 ]; arg2[3] to rdx
mulx r14, rax, r15; x74, x73<- x1 * arg2[3]
mov byte [ rsp + 0x100 ], cl; spilling byte x51 to mem
mov rcx, 0xffffffffffffffff ; moving imm to reg
mov rdx, rcx; 0xffffffffffffffff to rdx
mov [ rsp + 0x108 ], r14; spilling x74 to mem
mulx rcx, r14, r11; x113, x112<- x106 * 0xffffffffffffffff
mov rdx, [ rsp + 0x80 ]; x85, copying x76 here, cause x76 is needed in a reg for other than x85, namely all: , x85--x86, size: 1
adox rdx, rax
setc al; spill CF x64 to reg (rax)
mov [ rsp + 0x110 ], rcx; spilling x113 to mem
movzx rcx, byte [ rsp + 0xc8 ]; load byte memx123 to register64
clc;
mov byte [ rsp + 0x118 ], bpl; spilling byte x198 to mem
mov rbp, -0x1 ; moving imm to reg
adcx rcx, rbp; loading flag
adcx r14, [ rsp + 0x90 ]
setc cl; spill CF x125 to reg (rcx)
movzx rbp, byte [ rsp + 0x98 ]; load byte memx97 to register64
clc;
mov byte [ rsp + 0x120 ], al; spilling byte x64 to mem
mov rax, -0x1 ; moving imm to reg
adcx rbp, rax; loading flag
adcx r13, rdx
setc bpl; spill CF x99 to reg (rbp)
movzx rdx, byte [ rsp + 0xc0 ]; load byte memx136 to register64
clc;
adcx rdx, rax; loading flag
adcx r13, r14
mov rdx, [ r10 + 0x10 ]; arg2[2] to rdx
mulx r14, rax, rdi; x153, x152<- x2 * arg2[2]
mov [ rsp + 0x128 ], r14; spilling x153 to mem
setc r14b; spill CF x138 to reg (r14)
clc;
mov byte [ rsp + 0x130 ], bpl; spilling byte x99 to mem
mov rbp, -0x1 ; moving imm to reg
movzx rbx, bl
adcx rbx, rbp; loading flag
adcx rax, [ rsp + 0xa0 ]
mov rbx, 0xfffffffffffffffe ; moving imm to reg
mov rdx, r9; x183 to rdx
mulx r9, rbp, rbx; x192, x191<- x183 * 0xfffffffffffffffe
seto bl; spill OF x86 to reg (rbx)
mov [ rsp + 0x138 ], r9; spilling x192 to mem
movzx r9, byte [ rsp + 0xd8 ]; load byte memx172 to register64
mov byte [ rsp + 0x140 ], r14b; spilling byte x138 to mem
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r9, r14; loading flag
adox r13, rax
setc r9b; spill CF x161 to reg (r9)
movzx rax, byte [ rsp + 0x118 ]; load byte memx198 to register64
clc;
adcx rax, r14; loading flag
adcx rbp, [ rsp + 0xd0 ]
seto al; spill OF x174 to reg (rax)
movzx r14, byte [ rsp + 0xf0 ]; load byte memx211 to register64
mov byte [ rsp + 0x148 ], r9b; spilling byte x161 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r14, r9; loading flag
adox r13, rbp
xchg rdx, r15; x1, swapping with x183, which is currently in rdx
mulx r14, rbp, [ r10 + 0x20 ]; x72, x71<- x1 * arg2[4]
xchg rdx, r12; x6, swapping with x1, which is currently in rdx
mulx rdx, r9, [ r10 + 0x28 ]; x8, x7<- x6 * arg2[5]
mov [ rsp + 0x150 ], r13; spilling x212 to mem
seto r13b; spill OF x213 to reg (r13)
mov [ rsp + 0x158 ], r14; spilling x72 to mem
movzx r14, byte [ rsp + 0xf8 ]; load byte memx26 to register64
mov [ rsp + 0x160 ], rdx; spilling x8 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r14, rdx; loading flag
adox r9, [ rsp + 0xb8 ]
mov r14, 0xffffffffffffffff ; moving imm to reg
mov rdx, r8; x30 to rdx
mulx rdx, r8, r14; x33, x32<- x30 * 0xffffffffffffffff
seto r14b; spill OF x28 to reg (r14)
mov byte [ rsp + 0x168 ], r13b; spilling byte x213 to mem
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbx, bl
adox rbx, r13; loading flag
adox rbp, [ rsp + 0x108 ]
setc bl; spill CF x200 to reg (rbx)
movzx r13, byte [ rsp + 0x100 ]; load byte memx51 to register64
clc;
mov byte [ rsp + 0x170 ], r14b; spilling byte x28 to mem
mov r14, -0x1 ; moving imm to reg
adcx r13, r14; loading flag
adcx r8, [ rsp + 0xe8 ]
mov r13, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r13; 0xffffffffffffffff, swapping with x33, which is currently in rdx
mov [ rsp + 0x178 ], rsi; spilling arg1 to mem
mulx r14, rsi, r11; x111, x110<- x106 * 0xffffffffffffffff
setc dl; spill CF x53 to reg (rdx)
clc;
mov [ rsp + 0x180 ], r14; spilling x111 to mem
mov r14, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, r14; loading flag
adcx rsi, [ rsp + 0x110 ]
seto cl; spill OF x88 to reg (rcx)
movzx r14, byte [ rsp + 0x120 ]; load byte memx64 to register64
mov byte [ rsp + 0x188 ], bl; spilling byte x200 to mem
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r14, rbx; loading flag
adox r9, r8
seto r14b; spill OF x66 to reg (r14)
movzx r8, byte [ rsp + 0x130 ]; load byte memx99 to register64
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
adox r8, rbx; loading flag
adox r9, rbp
mov r8, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r8; 0xffffffffffffffff, swapping with x53, which is currently in rdx
mulx rbp, rbx, r15; x190, x189<- x183 * 0xffffffffffffffff
seto dl; spill OF x101 to reg (rdx)
mov [ rsp + 0x190 ], rbp; spilling x190 to mem
movzx rbp, byte [ rsp + 0x140 ]; load byte memx138 to register64
mov byte [ rsp + 0x198 ], cl; spilling byte x88 to mem
mov rcx, -0x1 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rcx, -0x1 ; moving imm to reg
adox rbp, rcx; loading flag
adox r9, rsi
mov bpl, dl; preserving value of x101 into a new reg
mov rdx, [ r10 + 0x18 ]; saving arg2[3] in rdx.
mulx rsi, rcx, rdi; x151, x150<- x2 * arg2[3]
mov [ rsp + 0x1a0 ], rsi; spilling x151 to mem
setc sil; spill CF x127 to reg (rsi)
mov byte [ rsp + 0x1a8 ], bpl; spilling byte x101 to mem
movzx rbp, byte [ rsp + 0x148 ]; load byte memx161 to register64
clc;
mov byte [ rsp + 0x1b0 ], r14b; spilling byte x66 to mem
mov r14, -0x1 ; moving imm to reg
adcx rbp, r14; loading flag
adcx rcx, [ rsp + 0x128 ]
movzx rbp, r8b; x54, copying x53 here, cause x53 is needed in a reg for other than x54, namely all: , x54, size: 1
lea rbp, [ rbp + r13 ]
setc r13b; spill CF x163 to reg (r13)
clc;
movzx rax, al
adcx rax, r14; loading flag
adcx r9, rcx
setc al; spill CF x176 to reg (rax)
movzx r8, byte [ rsp + 0x188 ]; load byte memx200 to register64
clc;
adcx r8, r14; loading flag
adcx rbx, [ rsp + 0x138 ]
mov rdx, [ r10 + 0x28 ]; arg2[5] to rdx
mulx r12, r8, r12; x70, x69<- x1 * arg2[5]
seto cl; spill OF x140 to reg (rcx)
movzx r14, byte [ rsp + 0x168 ]; load byte memx213 to register64
mov [ rsp + 0x1b8 ], r12; spilling x70 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
adox r14, r12; loading flag
adox r9, rbx
movzx r14, byte [ rsp + 0x170 ]; x29, copying x28 here, cause x28 is needed in a reg for other than x29, namely all: , x29, size: 1
mov rbx, [ rsp + 0x160 ]; load m64 x8 to register64
lea r14, [ r14 + rbx ]; r8/64 + m8
setc bl; spill CF x202 to reg (rbx)
movzx r12, byte [ rsp + 0x1b0 ]; load byte memx66 to register64
clc;
mov [ rsp + 0x1c0 ], r9; spilling x214 to mem
mov r9, -0x1 ; moving imm to reg
adcx r12, r9; loading flag
adcx r14, rbp
seto r12b; spill OF x215 to reg (r12)
movzx rbp, byte [ rsp + 0x198 ]; load byte memx88 to register64
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
adox rbp, r9; loading flag
adox r8, [ rsp + 0x158 ]
seto bpl; spill OF x90 to reg (rbp)
movzx r9, byte [ rsp + 0x1a8 ]; load byte memx101 to register64
mov byte [ rsp + 0x1c8 ], r12b; spilling byte x215 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r9, r12; loading flag
adox r14, r8
mov r9, 0xffffffffffffffff ; moving imm to reg
mov rdx, r15; x183 to rdx
mulx r15, r8, r9; x188, x187<- x183 * 0xffffffffffffffff
xchg rdx, r9; 0xffffffffffffffff, swapping with x183, which is currently in rdx
mulx r11, r12, r11; x109, x108<- x106 * 0xffffffffffffffff
seto dl; spill OF x103 to reg (rdx)
mov [ rsp + 0x1d0 ], r15; spilling x188 to mem
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r15, -0x1 ; moving imm to reg
movzx rsi, sil
adox rsi, r15; loading flag
adox r12, [ rsp + 0x180 ]
seto sil; spill OF x129 to reg (rsi)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r15; loading flag
adox r14, r12
xchg rdx, rdi; x2, swapping with x103, which is currently in rdx
mulx rcx, r12, [ r10 + 0x20 ]; x149, x148<- x2 * arg2[4]
seto r15b; spill OF x142 to reg (r15)
mov [ rsp + 0x1d8 ], rcx; spilling x149 to mem
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r13, r13b
adox r13, rcx; loading flag
adox r12, [ rsp + 0x1a0 ]
seto r13b; spill OF x165 to reg (r13)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rcx, -0x1 ; moving imm to reg
movzx rax, al
adox rax, rcx; loading flag
adox r14, r12
movzx rax, bpl; x91, copying x90 here, cause x90 is needed in a reg for other than x91, namely all: , x91, size: 1
mov r12, [ rsp + 0x1b8 ]; load m64 x70 to register64
lea rax, [ rax + r12 ]; r8/64 + m8
seto r12b; spill OF x178 to reg (r12)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, rbp; loading flag
adox r8, [ rsp + 0x190 ]
movzx rbx, sil; x130, copying x129 here, cause x129 is needed in a reg for other than x130, namely all: , x130, size: 1
lea rbx, [ rbx + r11 ]
mulx rdx, r11, [ r10 + 0x28 ]; x147, x146<- x2 * arg2[5]
movzx rsi, dil; x104, copying x103 here, cause x103 is needed in a reg for other than x104, namely all: , x104--x105, size: 1
adcx rsi, rax
setc dil; spill CF x105 to reg (rdi)
clc;
movzx r13, r13b
adcx r13, rbp; loading flag
adcx r11, [ rsp + 0x1d8 ]
adcx rdx, rcx
movzx r13, byte [ rsp + 0x1c8 ]; load byte memx215 to register64
clc;
adcx r13, rbp; loading flag
adcx r14, r8
setc r13b; spill CF x217 to reg (r13)
clc;
movzx r15, r15b
adcx r15, rbp; loading flag
adcx rsi, rbx
mov r15, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r9; x183, swapping with x168, which is currently in rdx
mulx rdx, rax, r15; x186, x185<- x183 * 0xffffffffffffffff
setc r8b; spill CF x144 to reg (r8)
clc;
movzx r12, r12b
adcx r12, rbp; loading flag
adcx rsi, r11
movzx r12, r8b; x145, copying x144 here, cause x144 is needed in a reg for other than x145, namely all: , x145, size: 1
movzx rdi, dil
lea r12, [ r12 + rdi ]
mov rbx, [ rsp + 0x1d0 ]; x205, copying x188 here, cause x188 is needed in a reg for other than x205, namely all: , x205--x206, size: 1
adox rbx, rax
mov rdi, [ rsp + 0x178 ]; load m64 arg1 to register64
mov r11, [ rdi + 0x18 ]; load m64 x3 to register64
adox rdx, rcx
dec rcx; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx r13, r13b
adox r13, rcx; loading flag
adox rsi, rbx
adcx r9, r12
adox rdx, r9
seto bpl; spill OF x222 to reg (rbp)
adc bpl, 0x0
movzx rbp, bpl
mov r13, rdx; preserving value of x220 into a new reg
mov rdx, [ r10 + 0x0 ]; saving arg2[0] in rdx.
mulx r8, rax, r11; x234, x233<- x3 * arg2[0]
adox rax, [ rsp + 0xe0 ]
mov r12, 0x100000001 ; moving imm to reg
mov rdx, rax; x246 to rdx
mulx rax, rbx, r12; _, x260<- x246 * 0x100000001
xchg rdx, rbx; x260, swapping with x246, which is currently in rdx
mulx rax, r9, r15; x267, x266<- x260 * 0xffffffffffffffff
mov rcx, 0xffffffff ; moving imm to reg
mulx r12, r15, rcx; x273, x272<- x260 * 0xffffffff
mov rcx, 0xffffffff00000000 ; moving imm to reg
mov byte [ rsp + 0x1e0 ], bpl; spilling byte x222 to mem
mov [ rsp + 0x1e8 ], r13; spilling x220 to mem
mulx rbp, r13, rcx; x271, x270<- x260 * 0xffffffff00000000
mov rcx, 0xfffffffffffffffe ; moving imm to reg
mov [ rsp + 0x1f0 ], rsi; spilling x218 to mem
mov [ rsp + 0x1f8 ], r14; spilling x216 to mem
mulx rsi, r14, rcx; x269, x268<- x260 * 0xfffffffffffffffe
adcx r13, r12
mov r12, [ rdi + 0x20 ]; load m64 x4 to register64
adcx r14, rbp
adcx r9, rsi
mov rbp, 0xffffffffffffffff ; moving imm to reg
mulx rsi, rcx, rbp; x263, x262<- x260 * 0xffffffffffffffff
mov [ rsp + 0x200 ], r9; spilling x278 to mem
mulx rdx, r9, rbp; x265, x264<- x260 * 0xffffffffffffffff
adcx r9, rax
adcx rcx, rdx
mov rdx, [ r10 + 0x8 ]; arg2[1] to rdx
mulx rax, rbp, r12; x309, x308<- x4 * arg2[1]
mov rdx, r12; x4 to rdx
mov [ rsp + 0x208 ], rcx; spilling x282 to mem
mulx r12, rcx, [ r10 + 0x10 ]; x307, x306<- x4 * arg2[2]
mov [ rsp + 0x210 ], r9; spilling x280 to mem
mov r9, 0x0 ; moving imm to reg
adcx rsi, r9
mov [ rsp + 0x218 ], rsi; spilling x284 to mem
mulx r9, rsi, [ r10 + 0x0 ]; x311, x310<- x4 * arg2[0]
clc;
adcx rbp, r9
adcx rcx, rax
mulx rax, r9, [ r10 + 0x18 ]; x305, x304<- x4 * arg2[3]
adcx r9, r12
mov [ rsp + 0x220 ], r9; spilling x316 to mem
mulx r12, r9, [ r10 + 0x20 ]; x303, x302<- x4 * arg2[4]
adcx r9, rax
mulx rdx, rax, [ r10 + 0x28 ]; x301, x300<- x4 * arg2[5]
adcx rax, r12
mov r12, 0x0 ; moving imm to reg
adcx rdx, r12
mov r12, rdx; preserving value of x322 into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mov [ rsp + 0x228 ], rax; spilling x320 to mem
mov [ rsp + 0x230 ], r9; spilling x318 to mem
mulx rax, r9, r11; x232, x231<- x3 * arg2[1]
clc;
adcx r9, r8
mov r8, [ rsp + 0x150 ]; x248, copying x212 here, cause x212 is needed in a reg for other than x248, namely all: , x248--x249, size: 1
adox r8, r9
seto r9b; spill OF x249 to reg (r9)
mov [ rsp + 0x238 ], r12; spilling x322 to mem
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, rbx
adox r13, r8
seto r15b; spill OF x288 to reg (r15)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rsi, r13
mov rdx, [ r10 + 0x10 ]; arg2[2] to rdx
mulx rbx, r8, r11; x230, x229<- x3 * arg2[2]
mov r13, 0x100000001 ; moving imm to reg
mov rdx, r13; 0x100000001 to rdx
mulx r13, r12, rsi; _, x337<- x323 * 0x100000001
mov r13, 0xffffffff ; moving imm to reg
xchg rdx, r12; x337, swapping with 0x100000001, which is currently in rdx
mov [ rsp + 0x240 ], rcx; spilling x314 to mem
mulx r12, rcx, r13; x350, x349<- x337 * 0xffffffff
adcx r8, rax
setc al; spill CF x238 to reg (rax)
clc;
adcx rcx, rsi
seto cl; spill OF x324 to reg (rcx)
mov rsi, 0x0 ; moving imm to reg
dec rsi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r9, r9b
adox r9, rsi; loading flag
adox r8, [ rsp + 0x1c0 ]
seto r9b; spill OF x251 to reg (r9)
inc rsi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rsi, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, rsi; loading flag
adox r8, r14
mov r14, 0xffffffff00000000 ; moving imm to reg
mulx r15, rsi, r14; x348, x347<- x337 * 0xffffffff00000000
mov r14, rdx; preserving value of x337 into a new reg
mov rdx, [ r10 + 0x18 ]; saving arg2[3] in rdx.
mov [ rsp + 0x248 ], r15; spilling x348 to mem
mulx r13, r15, r11; x228, x227<- x3 * arg2[3]
mov byte [ rsp + 0x250 ], r9b; spilling byte x251 to mem
setc r9b; spill CF x363 to reg (r9)
clc;
mov [ rsp + 0x258 ], r13; spilling x228 to mem
mov r13, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, r13; loading flag
adcx r8, rbp
setc bpl; spill CF x326 to reg (rbp)
clc;
adcx rsi, r12
setc cl; spill CF x352 to reg (rcx)
clc;
movzx r9, r9b
adcx r9, r13; loading flag
adcx r8, rsi
setc r12b; spill CF x365 to reg (r12)
clc;
movzx rax, al
adcx rax, r13; loading flag
adcx rbx, r15
mov rdx, r11; x3 to rdx
mulx r11, rax, [ r10 + 0x20 ]; x226, x225<- x3 * arg2[4]
mov r9, [ rsp + 0x258 ]; x241, copying x228 here, cause x228 is needed in a reg for other than x241, namely all: , x241--x242, size: 1
adcx r9, rax
mov r15, 0xfffffffffffffffe ; moving imm to reg
xchg rdx, r15; 0xfffffffffffffffe, swapping with x3, which is currently in rdx
mulx rsi, rax, r14; x346, x345<- x337 * 0xfffffffffffffffe
seto r13b; spill OF x290 to reg (r13)
movzx rdx, byte [ rsp + 0x250 ]; load byte memx251 to register64
mov [ rsp + 0x260 ], r8; spilling x364 to mem
mov r8, 0x0 ; moving imm to reg
dec r8; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rdx, r8; loading flag
adox rbx, [ rsp + 0x1f8 ]
setc dl; spill CF x242 to reg (rdx)
clc;
movzx r13, r13b
adcx r13, r8; loading flag
adcx rbx, [ rsp + 0x200 ]
mov r13, [ rsp + 0x1f0 ]; x254, copying x218 here, cause x218 is needed in a reg for other than x254, namely all: , x254--x255, size: 1
adox r13, r9
seto r9b; spill OF x255 to reg (r9)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, r8; loading flag
adox rbx, [ rsp + 0x240 ]
seto bpl; spill OF x328 to reg (rbp)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r8; loading flag
adox rax, [ rsp + 0x248 ]
setc cl; spill CF x292 to reg (rcx)
clc;
movzx r12, r12b
adcx r12, r8; loading flag
adcx rbx, rax
mov r12, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r14; x337, swapping with x242, which is currently in rdx
mulx rax, r8, r12; x344, x343<- x337 * 0xffffffffffffffff
setc r12b; spill CF x367 to reg (r12)
clc;
mov [ rsp + 0x268 ], rbx; spilling x366 to mem
mov rbx, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, rbx; loading flag
adcx r13, [ rsp + 0x210 ]
adox r8, rsi
setc sil; spill CF x294 to reg (rsi)
clc;
movzx rbp, bpl
adcx rbp, rbx; loading flag
adcx r13, [ rsp + 0x220 ]
setc cl; spill CF x330 to reg (rcx)
clc;
movzx r12, r12b
adcx r12, rbx; loading flag
adcx r13, r8
mov rbp, rdx; preserving value of x337 into a new reg
mov rdx, [ r10 + 0x28 ]; saving arg2[5] in rdx.
mulx r15, r12, r15; x224, x223<- x3 * arg2[5]
setc r8b; spill CF x369 to reg (r8)
clc;
movzx r14, r14b
adcx r14, rbx; loading flag
adcx r11, r12
mov r14, 0x0 ; moving imm to reg
adcx r15, r14
clc;
movzx r9, r9b
adcx r9, rbx; loading flag
adcx r11, [ rsp + 0x1e8 ]
mov r9, 0xffffffffffffffff ; moving imm to reg
mov rdx, r9; 0xffffffffffffffff to rdx
mulx r9, r12, rbp; x342, x341<- x337 * 0xffffffffffffffff
movzx r14, byte [ rsp + 0x1e0 ]; x258, copying x222 here, cause x222 is needed in a reg for other than x258, namely all: , x258--x259, size: 1
adcx r14, r15
adox r12, rax
mov rax, [ rdi + 0x28 ]; load m64 x5 to register64
mulx rbp, r15, rbp; x340, x339<- x337 * 0xffffffffffffffff
setc bl; spill CF x259 to reg (rbx)
clc;
mov rdx, -0x1 ; moving imm to reg
movzx rsi, sil
adcx rsi, rdx; loading flag
adcx r11, [ rsp + 0x208 ]
adox r15, r9
mov rsi, [ rsp + 0x218 ]; x297, copying x284 here, cause x284 is needed in a reg for other than x297, namely all: , x297--x298, size: 1
adcx rsi, r14
movzx r9, bl; x299, copying x259 here, cause x259 is needed in a reg for other than x299, namely all: , x299, size: 1
mov r14, 0x0 ; moving imm to reg
adcx r9, r14
adox rbp, r14
add cl, 0x7F; load flag from rm/8 into OF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
seto cl; since that has deps, resore it whereever it was
adox r11, [ rsp + 0x230 ]
mov rcx, [ rsp + 0x228 ]; x333, copying x320 here, cause x320 is needed in a reg for other than x333, namely all: , x333--x334, size: 1
adox rcx, rsi
mov rbx, [ rsp + 0x238 ]; x335, copying x322 here, cause x322 is needed in a reg for other than x335, namely all: , x335--x336, size: 1
adox rbx, r9
mov rdx, rax; x5 to rdx
mulx rax, rsi, [ r10 + 0x0 ]; x388, x387<- x5 * arg2[0]
mov r9, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, r9; loading flag
adcx r11, r12
adcx r15, rcx
adcx rbp, rbx
seto r8b; spill OF x376 to reg (r8)
adc r8b, 0x0
movzx r8, r8b
adox rsi, [ rsp + 0x260 ]
mov r12, 0x100000001 ; moving imm to reg
xchg rdx, r12; 0x100000001, swapping with x5, which is currently in rdx
mulx rcx, rbx, rsi; _, x414<- x400 * 0x100000001
mov rcx, 0xffffffff ; moving imm to reg
xchg rdx, rbx; x414, swapping with 0x100000001, which is currently in rdx
mulx r14, r9, rcx; x427, x426<- x414 * 0xffffffff
mov rcx, 0xffffffff00000000 ; moving imm to reg
mov byte [ rsp + 0x270 ], r8b; spilling byte x376 to mem
mulx rbx, r8, rcx; x425, x424<- x414 * 0xffffffff00000000
adcx r9, rsi
xchg rdx, r12; x5, swapping with x414, which is currently in rdx
mulx r9, rsi, [ r10 + 0x8 ]; x386, x385<- x5 * arg2[1]
mov [ rsp + 0x278 ], rbp; spilling x374 to mem
mulx rcx, rbp, [ r10 + 0x10 ]; x384, x383<- x5 * arg2[2]
mov [ rsp + 0x280 ], r15; spilling x372 to mem
setc r15b; spill CF x440 to reg (r15)
clc;
adcx rsi, rax
adcx rbp, r9
mov rax, [ rsp + 0x268 ]; x402, copying x366 here, cause x366 is needed in a reg for other than x402, namely all: , x402--x403, size: 1
adox rax, rsi
setc r9b; spill CF x392 to reg (r9)
clc;
adcx r8, r14
adox rbp, r13
seto r13b; spill OF x405 to reg (r13)
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r15, r15b
adox r15, r14; loading flag
adox rax, r8
setc r15b; spill CF x429 to reg (r15)
seto sil; spill OF x442 to reg (rsi)
mov r8, rax; x454, copying x441 here, cause x441 is needed in a reg for other than x454, namely all: , x454--x455, x468, size: 2
mov r14, 0xffffffff ; moving imm to reg
sub r8, r14
mov r14, 0xfffffffffffffffe ; moving imm to reg
xchg rdx, r12; x414, swapping with x5, which is currently in rdx
mov [ rsp + 0x288 ], r8; spilling x454 to mem
mov [ rsp + 0x290 ], r11; spilling x370 to mem
mulx r8, r11, r14; x423, x422<- x414 * 0xfffffffffffffffe
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r15, r15b
adox r15, r14; loading flag
adox rbx, r11
mov r15, 0xffffffffffffffff ; moving imm to reg
mulx r11, r14, r15; x421, x420<- x414 * 0xffffffffffffffff
adox r14, r8
seto r8b; spill OF x433 to reg (r8)
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r15, -0x1 ; moving imm to reg
movzx rsi, sil
adox rsi, r15; loading flag
adox rbp, rbx
seto sil; spill OF x444 to reg (rsi)
mov rbx, rbp; x456, copying x443 here, cause x443 is needed in a reg for other than x456, namely all: , x469, x456--x457, size: 2
mov r15, 0xffffffff00000000 ; moving imm to reg
sbb rbx, r15
xchg rdx, r12; x5, swapping with x414, which is currently in rdx
mov [ rsp + 0x298 ], rbx; spilling x456 to mem
mulx r15, rbx, [ r10 + 0x18 ]; x382, x381<- x5 * arg2[3]
mov [ rsp + 0x2a0 ], r11; spilling x421 to mem
mov r11, 0x0 ; moving imm to reg
dec r11; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r9, r9b
adox r9, r11; loading flag
adox rcx, rbx
mulx r9, rbx, [ r10 + 0x20 ]; x380, x379<- x5 * arg2[4]
adox rbx, r15
seto r15b; spill OF x396 to reg (r15)
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r11, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, r11; loading flag
adox rcx, [ rsp + 0x290 ]
setc r13b; spill CF x457 to reg (r13)
clc;
movzx rsi, sil
adcx rsi, r11; loading flag
adcx rcx, r14
mov r14, [ rsp + 0x280 ]; x408, copying x372 here, cause x372 is needed in a reg for other than x408, namely all: , x408--x409, size: 1
adox r14, rbx
setc sil; spill CF x446 to reg (rsi)
seto bl; spill OF x409 to reg (rbx)
movzx r11, r13b; x457, copying x457 here, cause x457 is needed in a reg for other than x457, namely all: , x458--x459, size: 1
add r11, -0x1
mov r11, rcx; x458, copying x445 here, cause x445 is needed in a reg for other than x458, namely all: , x458--x459, x470, size: 2
mov r13, 0xfffffffffffffffe ; moving imm to reg
sbb r11, r13
mov r13, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r13; 0xffffffffffffffff, swapping with x5, which is currently in rdx
mov [ rsp + 0x2a8 ], r11; spilling x458 to mem
mov byte [ rsp + 0x2b0 ], bl; spilling byte x409 to mem
mulx r11, rbx, r12; x419, x418<- x414 * 0xffffffffffffffff
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r8, r8b
adox r8, rdx; loading flag
adox rbx, [ rsp + 0x2a0 ]
mov r8, 0xffffffffffffffff ; moving imm to reg
mov rdx, r8; 0xffffffffffffffff to rdx
mulx r12, r8, r12; x417, x416<- x414 * 0xffffffffffffffff
adox r8, r11
mov r11, 0x0 ; moving imm to reg
adox r12, r11
dec r11; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx rsi, sil
adox rsi, r11; loading flag
adox r14, rbx
seto sil; spill OF x448 to reg (rsi)
mov rbx, r14; x460, copying x447 here, cause x447 is needed in a reg for other than x460, namely all: , x471, x460--x461, size: 2
sbb rbx, rdx
xchg rdx, r13; x5, swapping with 0xffffffffffffffff, which is currently in rdx
mulx rdx, r11, [ r10 + 0x28 ]; x378, x377<- x5 * arg2[5]
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r15, r15b
adox r15, r13; loading flag
adox r9, r11
mov r15, 0x0 ; moving imm to reg
adox rdx, r15
movzx r11, byte [ rsp + 0x2b0 ]; load byte memx409 to register64
dec r15; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
adox r11, r15; loading flag
adox r9, [ rsp + 0x278 ]
movzx r13, byte [ rsp + 0x270 ]; x412, copying x376 here, cause x376 is needed in a reg for other than x412, namely all: , x412--x413, size: 1
adox r13, rdx
seto r11b; spill OF x413 to reg (r11)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
movzx rsi, sil
adox rsi, rdx; loading flag
adox r9, r8
adox r12, r13
movzx r8, r11b; x453, copying x413 here, cause x413 is needed in a reg for other than x453, namely all: , x453, size: 1
adox r8, r15
mov rsi, r9; x462, copying x449 here, cause x449 is needed in a reg for other than x462, namely all: , x462--x463, x472, size: 2
mov r11, 0xffffffffffffffff ; moving imm to reg
sbb rsi, r11
mov r13, r12; x464, copying x451 here, cause x451 is needed in a reg for other than x464, namely all: , x464--x465, x473, size: 2
sbb r13, r11
sbb r8, 0x00000000
cmovc rsi, r9; if CF, x472<- x449 (nzVar)
cmovc rbx, r14; if CF, x471<- x447 (nzVar)
mov r8, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r8 + 0x20 ], rsi; out1[4] = x472
mov r14, [ rsp + 0x2a8 ]; x470, copying x458 here, cause x458 is needed in a reg for other than x470, namely all: , x470, size: 1
cmovc r14, rcx; if CF, x470<- x445 (nzVar)
mov rcx, [ rsp + 0x288 ]; x468, copying x454 here, cause x454 is needed in a reg for other than x468, namely all: , x468, size: 1
cmovc rcx, rax; if CF, x468<- x441 (nzVar)
mov rax, [ rsp + 0x298 ]; x469, copying x456 here, cause x456 is needed in a reg for other than x469, namely all: , x469, size: 1
cmovc rax, rbp; if CF, x469<- x443 (nzVar)
mov [ r8 + 0x0 ], rcx; out1[0] = x468
mov [ r8 + 0x8 ], rax; out1[1] = x469
mov [ r8 + 0x10 ], r14; out1[2] = x470
cmovc r13, r12; if CF, x473<- x451 (nzVar)
mov [ r8 + 0x18 ], rbx; out1[3] = x471
mov [ r8 + 0x28 ], r13; out1[5] = x473
mov rbx, [ rsp + 0x2b8 ]; restoring from stack
mov rbp, [ rsp + 0x2c0 ]; restoring from stack
mov r12, [ rsp + 0x2c8 ]; restoring from stack
mov r13, [ rsp + 0x2d0 ]; restoring from stack
mov r14, [ rsp + 0x2d8 ]; restoring from stack
mov r15, [ rsp + 0x2e0 ]; restoring from stack
add rsp, 0x2e8 
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; clocked at 1600 MHz
; first cyclecount 170.855, best 135.43529411764706, lastGood 137.1829268292683
; seed 3764303852282748 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4420790 ms / 60000 runs=> 73.67983333333333ms/run
; Time spent for assembling and measureing (initial batch_size=85, initial num_batches=101): 250435 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.056649377147523404
; number reverted permutation/ tried permutation: 26453 / 30191 =87.619%
; number reverted decision/ tried decision: 22631 / 29810 =75.917%