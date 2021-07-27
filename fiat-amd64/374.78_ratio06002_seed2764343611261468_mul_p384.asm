SECTION .text
	GLOBAL mul_p384
mul_p384:
sub rsp, 0x508 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x4d8 ], rbx; saving to stack
mov [ rsp + 0x4e0 ], rbp; saving to stack
mov [ rsp + 0x4e8 ], r12; saving to stack
mov [ rsp + 0x4f0 ], r13; saving to stack
mov [ rsp + 0x4f8 ], r14; saving to stack
mov [ rsp + 0x500 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x6 to register64
mov r10, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x0 ]; saving arg2[0] in rdx.
mulx r11, rbx, rax; x18, x17<- x6 * arg2[0]
mov rbp, 0x100000001 ; moving imm to reg
mov rdx, rbx; x17 to rdx
mulx rbx, r12, rbp; _, x30<- x17 * 0x100000001
mov rbx, 0xffffffff ; moving imm to reg
xchg rdx, rbx; 0xffffffff, swapping with x17, which is currently in rdx
mulx r13, r14, r12; x43, x42<- x30 * 0xffffffff
add r14, rbx; could be done better, if r0 has been u8 as well
mov r14, rdx; preserving value of 0xffffffff into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mulx r15, rcx, rax; x16, x15<- x6 * arg2[1]
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rcx, r11
mov r9, 0xffffffff00000000 ; moving imm to reg
mov rdx, r12; x30 to rdx
mulx r12, r11, r9; x41, x40<- x30 * 0xffffffff00000000
seto bl; spill OF x20 to reg (rbx)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r11, r13
adcx r11, rcx
mov r13, [ rsi + 0x8 ]; load m64 x1 to register64
mov rcx, rdx; preserving value of x30 into a new reg
mov rdx, [ r10 + 0x0 ]; saving arg2[0] in rdx.
mulx r8, r14, r13; x80, x79<- x1 * arg2[0]
seto bpl; spill OF x45 to reg (rbp)
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, r11
mov r11, 0x100000001 ; moving imm to reg
mov rdx, r11; 0x100000001 to rdx
mulx r11, r9, r14; _, x106<- x92 * 0x100000001
mov r11, rdx; preserving value of 0x100000001 into a new reg
mov rdx, [ r10 + 0x10 ]; saving arg2[2] in rdx.
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov [ rsp + 0x8 ], r8; spilling x80 to mem
mulx rdi, r8, rax; x14, x13<- x6 * arg2[2]
mov r11, 0xffffffff ; moving imm to reg
mov rdx, r11; 0xffffffff to rdx
mov [ rsp + 0x10 ], rdi; spilling x14 to mem
mulx r11, rdi, r9; x119, x118<- x106 * 0xffffffff
mov rdx, 0xfffffffffffffffe ; moving imm to reg
mov [ rsp + 0x18 ], r11; spilling x119 to mem
mov [ rsp + 0x20 ], r12; spilling x41 to mem
mulx r11, r12, rcx; x39, x38<- x30 * 0xfffffffffffffffe
seto dl; spill OF x93 to reg (rdx)
mov [ rsp + 0x28 ], r11; spilling x39 to mem
mov r11, -0x2 ; moving imm to reg
inc r11; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rdi, r14
setc r14b; spill CF x58 to reg (r14)
clc;
movzx rbx, bl
adcx rbx, r11; loading flag
adcx r15, r8
seto bl; spill OF x132 to reg (rbx)
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, r8; loading flag
adox r12, [ rsp + 0x20 ]
setc bpl; spill CF x22 to reg (rbp)
clc;
movzx r14, r14b
adcx r14, r8; loading flag
adcx r15, r12
mov r14b, dl; preserving value of x93 into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mulx r12, r11, r13; x78, x77<- x1 * arg2[1]
setc r8b; spill CF x60 to reg (r8)
clc;
adcx r11, [ rsp + 0x8 ]
mov [ rsp + 0x30 ], r12; spilling x78 to mem
seto r12b; spill OF x47 to reg (r12)
mov byte [ rsp + 0x38 ], r8b; spilling byte x60 to mem
mov r8, 0x0 ; moving imm to reg
dec r8; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r14, r14b
adox r14, r8; loading flag
adox r15, r11
mov r14, 0xffffffff00000000 ; moving imm to reg
mov rdx, r14; 0xffffffff00000000 to rdx
mulx r14, r11, r9; x117, x116<- x106 * 0xffffffff00000000
setc r8b; spill CF x82 to reg (r8)
clc;
adcx r11, [ rsp + 0x18 ]
mov rdx, [ rsi + 0x10 ]; load m64 x2 to register64
mov [ rsp + 0x40 ], r14; spilling x117 to mem
mov byte [ rsp + 0x48 ], r8b; spilling byte x82 to mem
mulx r14, r8, [ r10 + 0x0 ]; x157, x156<- x2 * arg2[0]
mov byte [ rsp + 0x50 ], r12b; spilling byte x47 to mem
setc r12b; spill CF x121 to reg (r12)
clc;
mov byte [ rsp + 0x58 ], bpl; spilling byte x22 to mem
mov rbp, -0x1 ; moving imm to reg
movzx rbx, bl
adcx rbx, rbp; loading flag
adcx r15, r11
seto bl; spill OF x95 to reg (rbx)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r8, r15
mov r11, 0x100000001 ; moving imm to reg
xchg rdx, r8; x169, swapping with x2, which is currently in rdx
mulx r15, rbp, r11; _, x183<- x169 * 0x100000001
mov r15, 0xffffffff ; moving imm to reg
xchg rdx, rbp; x183, swapping with x169, which is currently in rdx
mov byte [ rsp + 0x60 ], r12b; spilling byte x121 to mem
mulx r11, r12, r15; x196, x195<- x183 * 0xffffffff
mov r15, 0xffffffff00000000 ; moving imm to reg
mov byte [ rsp + 0x68 ], bl; spilling byte x95 to mem
mov [ rsp + 0x70 ], r12; spilling x195 to mem
mulx rbx, r12, r15; x194, x193<- x183 * 0xffffffff00000000
seto r15b; spill OF x170 to reg (r15)
mov [ rsp + 0x78 ], r14; spilling x157 to mem
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, r11
mov r11, 0xfffffffffffffffe ; moving imm to reg
mov [ rsp + 0x80 ], r12; spilling x197 to mem
mulx r14, r12, r11; x192, x191<- x183 * 0xfffffffffffffffe
mov r11, 0xffffffffffffffff ; moving imm to reg
mov byte [ rsp + 0x88 ], r15b; spilling byte x170 to mem
mov [ rsp + 0x90 ], r14; spilling x192 to mem
mulx r15, r14, r11; x190, x189<- x183 * 0xffffffffffffffff
adox r12, rbx
mov rbx, [ rsp + 0x90 ]; x201, copying x192 here, cause x192 is needed in a reg for other than x201, namely all: , x201--x202, size: 1
adox rbx, r14
mov [ rsp + 0x98 ], rbx; spilling x201 to mem
mulx r14, rbx, r11; x188, x187<- x183 * 0xffffffffffffffff
adox rbx, r15
mulx rdx, r15, r11; x186, x185<- x183 * 0xffffffffffffffff
adox r15, r14
mov r14, 0x0 ; moving imm to reg
adox rdx, r14
mov r14, rdx; preserving value of x207 into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mov [ rsp + 0xa0 ], r15; spilling x205 to mem
mulx r11, r15, r8; x155, x154<- x2 * arg2[1]
mov rdx, [ r10 + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0xa8 ], r14; spilling x207 to mem
mov [ rsp + 0xb0 ], rbx; spilling x203 to mem
mulx r14, rbx, r8; x153, x152<- x2 * arg2[2]
mov [ rsp + 0xb8 ], r12; spilling x199 to mem
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, [ rsp + 0x78 ]
adox rbx, r11
mov rdx, r8; x2 to rdx
mulx r8, r11, [ r10 + 0x18 ]; x151, x150<- x2 * arg2[3]
mov [ rsp + 0xc0 ], rbx; spilling x160 to mem
mulx r12, rbx, [ r10 + 0x20 ]; x149, x148<- x2 * arg2[4]
adox r11, r14
mulx rdx, r14, [ r10 + 0x28 ]; x147, x146<- x2 * arg2[5]
adox rbx, r8
adox r14, r12
mov r8, 0x0 ; moving imm to reg
adox rdx, r8
mov r12, -0x3 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbp, [ rsp + 0x70 ]
mov rbp, rdx; preserving value of x168 into a new reg
mov rdx, [ r10 + 0x18 ]; saving arg2[3] in rdx.
mulx r8, r12, rax; x12, x11<- x6 * arg2[3]
mov [ rsp + 0xc8 ], rbp; spilling x168 to mem
mov rbp, 0xffffffffffffffff ; moving imm to reg
mov rdx, rcx; x30 to rdx
mov [ rsp + 0xd0 ], r14; spilling x166 to mem
mulx rcx, r14, rbp; x37, x36<- x30 * 0xffffffffffffffff
seto bpl; spill OF x209 to reg (rbp)
mov [ rsp + 0xd8 ], rbx; spilling x164 to mem
movzx rbx, byte [ rsp + 0x58 ]; load byte memx22 to register64
mov [ rsp + 0xe0 ], r11; spilling x162 to mem
mov r11, 0x0 ; moving imm to reg
dec r11; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbx, r11; loading flag
adox r12, [ rsp + 0x10 ]
seto bl; spill OF x24 to reg (rbx)
movzx r11, byte [ rsp + 0x50 ]; load byte memx47 to register64
mov [ rsp + 0xe8 ], rcx; spilling x37 to mem
mov rcx, -0x1 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rcx, -0x1 ; moving imm to reg
adox r11, rcx; loading flag
adox r14, [ rsp + 0x28 ]
seto r11b; spill OF x49 to reg (r11)
movzx rcx, byte [ rsp + 0x38 ]; load byte memx60 to register64
mov [ rsp + 0xf0 ], r8; spilling x12 to mem
mov r8, -0x1 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r8, -0x1 ; moving imm to reg
adox rcx, r8; loading flag
adox r12, r14
xchg rdx, r13; x1, swapping with x30, which is currently in rdx
mulx rcx, r14, [ r10 + 0x10 ]; x76, x75<- x1 * arg2[2]
seto r8b; spill OF x62 to reg (r8)
mov [ rsp + 0xf8 ], rcx; spilling x76 to mem
movzx rcx, byte [ rsp + 0x48 ]; load byte memx82 to register64
mov byte [ rsp + 0x100 ], r11b; spilling byte x49 to mem
mov r11, 0x0 ; moving imm to reg
dec r11; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rcx, r11; loading flag
adox r14, [ rsp + 0x30 ]
mov rcx, 0xfffffffffffffffe ; moving imm to reg
xchg rdx, r9; x106, swapping with x1, which is currently in rdx
mov byte [ rsp + 0x108 ], r8b; spilling byte x62 to mem
mulx r11, r8, rcx; x115, x114<- x106 * 0xfffffffffffffffe
seto cl; spill OF x84 to reg (rcx)
mov [ rsp + 0x110 ], r11; spilling x115 to mem
movzx r11, byte [ rsp + 0x68 ]; load byte memx95 to register64
mov byte [ rsp + 0x118 ], bl; spilling byte x24 to mem
mov rbx, -0x1 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbx, -0x1 ; moving imm to reg
adox r11, rbx; loading flag
adox r12, r14
seto r11b; spill OF x97 to reg (r11)
movzx r14, byte [ rsp + 0x60 ]; load byte memx121 to register64
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
adox r14, rbx; loading flag
adox r8, [ rsp + 0x40 ]
adcx r8, r12
seto r14b; spill OF x123 to reg (r14)
movzx r12, byte [ rsp + 0x88 ]; load byte memx170 to register64
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
adox r12, rbx; loading flag
adox r8, r15
setc r12b; spill CF x136 to reg (r12)
clc;
movzx rbp, bpl
adcx rbp, rbx; loading flag
adcx r8, [ rsp + 0x80 ]
mov r15, [ rsi + 0x18 ]; load m64 x3 to register64
xchg rdx, r15; x3, swapping with x106, which is currently in rdx
mulx rbp, rbx, [ r10 + 0x0 ]; x234, x233<- x3 * arg2[0]
mov [ rsp + 0x120 ], rbp; spilling x234 to mem
seto bpl; spill OF x172 to reg (rbp)
mov byte [ rsp + 0x128 ], r12b; spilling byte x136 to mem
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, r8
mov r8, 0x100000001 ; moving imm to reg
xchg rdx, rbx; x246, swapping with x3, which is currently in rdx
mov byte [ rsp + 0x130 ], bpl; spilling byte x172 to mem
mulx r12, rbp, r8; _, x260<- x246 * 0x100000001
mov r12, 0xffffffff ; moving imm to reg
xchg rdx, r12; 0xffffffff, swapping with x246, which is currently in rdx
mov byte [ rsp + 0x138 ], r14b; spilling byte x123 to mem
mulx r8, r14, rbp; x273, x272<- x260 * 0xffffffff
mov rdx, 0xffffffff00000000 ; moving imm to reg
mov byte [ rsp + 0x140 ], r11b; spilling byte x97 to mem
mov byte [ rsp + 0x148 ], cl; spilling byte x84 to mem
mulx r11, rcx, rbp; x271, x270<- x260 * 0xffffffff00000000
setc dl; spill CF x211 to reg (rdx)
clc;
adcx rcx, r8
mov r8, 0xfffffffffffffffe ; moving imm to reg
xchg rdx, r8; 0xfffffffffffffffe, swapping with x211, which is currently in rdx
mov [ rsp + 0x150 ], rcx; spilling x274 to mem
mov byte [ rsp + 0x158 ], r8b; spilling byte x211 to mem
mulx rcx, r8, rbp; x269, x268<- x260 * 0xfffffffffffffffe
adcx r8, r11
mov r11, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r11; 0xffffffffffffffff, swapping with 0xfffffffffffffffe, which is currently in rdx
mov [ rsp + 0x160 ], r8; spilling x276 to mem
mulx r11, r8, rbp; x267, x266<- x260 * 0xffffffffffffffff
adcx r8, rcx
mov [ rsp + 0x168 ], r8; spilling x278 to mem
mulx rcx, r8, rbp; x265, x264<- x260 * 0xffffffffffffffff
adcx r8, r11
mulx rbp, r11, rbp; x263, x262<- x260 * 0xffffffffffffffff
adcx r11, rcx
seto cl; spill OF x247 to reg (rcx)
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, r12
mov r14, 0x0 ; moving imm to reg
adcx rbp, r14
mov rdx, [ r10 + 0x20 ]; arg2[4] to rdx
mulx r12, r14, rax; x10, x9<- x6 * arg2[4]
mov [ rsp + 0x170 ], rbp; spilling x284 to mem
mov rbp, 0xffffffffffffffff ; moving imm to reg
mov rdx, rbp; 0xffffffffffffffff to rdx
mov [ rsp + 0x178 ], r11; spilling x282 to mem
mulx rbp, r11, r13; x35, x34<- x30 * 0xffffffffffffffff
movzx rdx, byte [ rsp + 0x118 ]; load byte memx24 to register64
clc;
mov [ rsp + 0x180 ], r8; spilling x280 to mem
mov r8, -0x1 ; moving imm to reg
adcx rdx, r8; loading flag
adcx r14, [ rsp + 0xf0 ]
setc dl; spill CF x26 to reg (rdx)
movzx r8, byte [ rsp + 0x100 ]; load byte memx49 to register64
clc;
mov [ rsp + 0x188 ], rbp; spilling x35 to mem
mov rbp, -0x1 ; moving imm to reg
adcx r8, rbp; loading flag
adcx r11, [ rsp + 0xe8 ]
seto r8b; spill OF x286 to reg (r8)
movzx rbp, byte [ rsp + 0x108 ]; load byte memx62 to register64
mov [ rsp + 0x190 ], r12; spilling x10 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
adox rbp, r12; loading flag
adox r14, r11
mov bpl, dl; preserving value of x26 into a new reg
mov rdx, [ r10 + 0x18 ]; saving arg2[3] in rdx.
mulx r11, r12, r9; x74, x73<- x1 * arg2[3]
mov [ rsp + 0x198 ], r11; spilling x74 to mem
setc r11b; spill CF x51 to reg (r11)
mov byte [ rsp + 0x1a0 ], bpl; spilling byte x26 to mem
movzx rbp, byte [ rsp + 0x148 ]; load byte memx84 to register64
clc;
mov byte [ rsp + 0x1a8 ], r8b; spilling byte x286 to mem
mov r8, -0x1 ; moving imm to reg
adcx rbp, r8; loading flag
adcx r12, [ rsp + 0xf8 ]
mov rbp, 0xffffffffffffffff ; moving imm to reg
mov rdx, r15; x106 to rdx
mulx r15, r8, rbp; x113, x112<- x106 * 0xffffffffffffffff
seto bpl; spill OF x64 to reg (rbp)
mov [ rsp + 0x1b0 ], r15; spilling x113 to mem
movzx r15, byte [ rsp + 0x140 ]; load byte memx97 to register64
mov byte [ rsp + 0x1b8 ], r11b; spilling byte x51 to mem
mov r11, 0x0 ; moving imm to reg
dec r11; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, r11; loading flag
adox r14, r12
setc r15b; spill CF x86 to reg (r15)
movzx r12, byte [ rsp + 0x138 ]; load byte memx123 to register64
clc;
adcx r12, r11; loading flag
adcx r8, [ rsp + 0x110 ]
setc r12b; spill CF x125 to reg (r12)
movzx r11, byte [ rsp + 0x128 ]; load byte memx136 to register64
clc;
mov byte [ rsp + 0x1c0 ], r15b; spilling byte x86 to mem
mov r15, -0x1 ; moving imm to reg
adcx r11, r15; loading flag
adcx r14, r8
setc r11b; spill CF x138 to reg (r11)
movzx r8, byte [ rsp + 0x130 ]; load byte memx172 to register64
clc;
adcx r8, r15; loading flag
adcx r14, [ rsp + 0xc0 ]
seto r8b; spill OF x99 to reg (r8)
movzx r15, byte [ rsp + 0x158 ]; load byte memx211 to register64
mov byte [ rsp + 0x1c8 ], r11b; spilling byte x138 to mem
mov r11, 0x0 ; moving imm to reg
dec r11; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, r11; loading flag
adox r14, [ rsp + 0xb8 ]
mov r15, rdx; preserving value of x106 into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mov byte [ rsp + 0x1d0 ], r12b; spilling byte x125 to mem
mulx r11, r12, rbx; x232, x231<- x3 * arg2[1]
mov [ rsp + 0x1d8 ], r11; spilling x232 to mem
seto r11b; spill OF x213 to reg (r11)
mov byte [ rsp + 0x1e0 ], r8b; spilling byte x99 to mem
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, [ rsp + 0x120 ]
seto r8b; spill OF x236 to reg (r8)
mov byte [ rsp + 0x1e8 ], r11b; spilling byte x213 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r11; loading flag
adox r14, r12
seto cl; spill OF x249 to reg (rcx)
movzx r12, byte [ rsp + 0x1a8 ]; load byte memx286 to register64
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r11, -0x1 ; moving imm to reg
adox r12, r11; loading flag
adox r14, [ rsp + 0x150 ]
mov r12, [ rsi + 0x20 ]; load m64 x4 to register64
mov rdx, r12; x4 to rdx
mulx r12, r11, [ r10 + 0x0 ]; x311, x310<- x4 * arg2[0]
mov [ rsp + 0x1f0 ], r12; spilling x311 to mem
seto r12b; spill OF x288 to reg (r12)
mov byte [ rsp + 0x1f8 ], cl; spilling byte x249 to mem
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, r14
mov r14, 0x100000001 ; moving imm to reg
xchg rdx, r11; x323, swapping with x4, which is currently in rdx
mov byte [ rsp + 0x200 ], r12b; spilling byte x288 to mem
mulx rcx, r12, r14; _, x337<- x323 * 0x100000001
mov rcx, 0xffffffff ; moving imm to reg
xchg rdx, rcx; 0xffffffff, swapping with x323, which is currently in rdx
mov byte [ rsp + 0x208 ], r8b; spilling byte x236 to mem
mulx r14, r8, r12; x350, x349<- x337 * 0xffffffff
xchg rdx, rax; x6, swapping with 0xffffffff, which is currently in rdx
mulx rdx, rax, [ r10 + 0x28 ]; x8, x7<- x6 * arg2[5]
mov [ rsp + 0x210 ], rdx; spilling x8 to mem
seto dl; spill OF x324 to reg (rdx)
mov [ rsp + 0x218 ], r14; spilling x350 to mem
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, rcx
seto r8b; spill OF x363 to reg (r8)
movzx rcx, byte [ rsp + 0x1a0 ]; load byte memx26 to register64
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
adox rcx, r14; loading flag
adox rax, [ rsp + 0x190 ]
mov rcx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r13; x30, swapping with x324, which is currently in rdx
mulx rdx, r14, rcx; x33, x32<- x30 * 0xffffffffffffffff
setc cl; spill CF x174 to reg (rcx)
mov [ rsp + 0x220 ], rdx; spilling x33 to mem
movzx rdx, byte [ rsp + 0x1b8 ]; load byte memx51 to register64
clc;
mov byte [ rsp + 0x228 ], r8b; spilling byte x363 to mem
mov r8, -0x1 ; moving imm to reg
adcx rdx, r8; loading flag
adcx r14, [ rsp + 0x188 ]
setc dl; spill CF x53 to reg (rdx)
clc;
movzx rbp, bpl
adcx rbp, r8; loading flag
adcx rax, r14
xchg rdx, r9; x1, swapping with x53, which is currently in rdx
mulx rbp, r14, [ r10 + 0x20 ]; x72, x71<- x1 * arg2[4]
setc r8b; spill CF x66 to reg (r8)
mov [ rsp + 0x230 ], rbp; spilling x72 to mem
movzx rbp, byte [ rsp + 0x1c0 ]; load byte memx86 to register64
clc;
mov byte [ rsp + 0x238 ], r9b; spilling byte x53 to mem
mov r9, -0x1 ; moving imm to reg
adcx rbp, r9; loading flag
adcx r14, [ rsp + 0x198 ]
mov rbp, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbp; 0xffffffffffffffff, swapping with x1, which is currently in rdx
mov byte [ rsp + 0x240 ], r8b; spilling byte x66 to mem
mulx r9, r8, r15; x111, x110<- x106 * 0xffffffffffffffff
seto dl; spill OF x28 to reg (rdx)
mov [ rsp + 0x248 ], r9; spilling x111 to mem
movzx r9, byte [ rsp + 0x1e0 ]; load byte memx99 to register64
mov byte [ rsp + 0x250 ], r13b; spilling byte x324 to mem
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r9, r13; loading flag
adox rax, r14
seto r9b; spill OF x101 to reg (r9)
movzx r14, byte [ rsp + 0x1d0 ]; load byte memx125 to register64
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
adox r14, r13; loading flag
adox r8, [ rsp + 0x1b0 ]
setc r14b; spill CF x88 to reg (r14)
movzx r13, byte [ rsp + 0x1c8 ]; load byte memx138 to register64
clc;
mov byte [ rsp + 0x258 ], r9b; spilling byte x101 to mem
mov r9, -0x1 ; moving imm to reg
adcx r13, r9; loading flag
adcx rax, r8
seto r13b; spill OF x127 to reg (r13)
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r8; loading flag
adox rax, [ rsp + 0xe0 ]
setc cl; spill CF x140 to reg (rcx)
movzx r9, byte [ rsp + 0x1e8 ]; load byte memx213 to register64
clc;
adcx r9, r8; loading flag
adcx rax, [ rsp + 0x98 ]
xchg rdx, rbx; x3, swapping with x28, which is currently in rdx
mulx r9, r8, [ r10 + 0x10 ]; x230, x229<- x3 * arg2[2]
mov [ rsp + 0x260 ], r9; spilling x230 to mem
seto r9b; spill OF x176 to reg (r9)
mov byte [ rsp + 0x268 ], cl; spilling byte x140 to mem
movzx rcx, byte [ rsp + 0x208 ]; load byte memx236 to register64
mov byte [ rsp + 0x270 ], r13b; spilling byte x127 to mem
mov r13, -0x1 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r13, -0x1 ; moving imm to reg
adox rcx, r13; loading flag
adox r8, [ rsp + 0x1d8 ]
seto cl; spill OF x238 to reg (rcx)
movzx r13, byte [ rsp + 0x1f8 ]; load byte memx249 to register64
mov byte [ rsp + 0x278 ], r9b; spilling byte x176 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r13, r9; loading flag
adox rax, r8
xchg rdx, r11; x4, swapping with x3, which is currently in rdx
mulx r13, r8, [ r10 + 0x8 ]; x309, x308<- x4 * arg2[1]
setc r9b; spill CF x215 to reg (r9)
mov [ rsp + 0x280 ], r13; spilling x309 to mem
movzx r13, byte [ rsp + 0x200 ]; load byte memx288 to register64
clc;
mov byte [ rsp + 0x288 ], cl; spilling byte x238 to mem
mov rcx, -0x1 ; moving imm to reg
adcx r13, rcx; loading flag
adcx rax, [ rsp + 0x160 ]
seto r13b; spill OF x251 to reg (r13)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r8, [ rsp + 0x1f0 ]
seto cl; spill OF x313 to reg (rcx)
mov byte [ rsp + 0x290 ], r13b; spilling byte x251 to mem
movzx r13, byte [ rsp + 0x250 ]; load byte memx324 to register64
mov byte [ rsp + 0x298 ], r9b; spilling byte x215 to mem
mov r9, -0x1 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r9, -0x1 ; moving imm to reg
adox r13, r9; loading flag
adox rax, r8
mov r13, 0xffffffff00000000 ; moving imm to reg
xchg rdx, r12; x337, swapping with x4, which is currently in rdx
mulx r8, r9, r13; x348, x347<- x337 * 0xffffffff00000000
mov r13, [ rsi + 0x28 ]; load m64 x5 to register64
mov [ rsp + 0x2a0 ], r8; spilling x348 to mem
setc r8b; spill CF x290 to reg (r8)
clc;
adcx r9, [ rsp + 0x218 ]
mov byte [ rsp + 0x2a8 ], cl; spilling byte x313 to mem
setc cl; spill CF x352 to reg (rcx)
mov byte [ rsp + 0x2b0 ], r8b; spilling byte x290 to mem
movzx r8, byte [ rsp + 0x228 ]; load byte memx363 to register64
clc;
mov byte [ rsp + 0x2b8 ], r14b; spilling byte x88 to mem
mov r14, -0x1 ; moving imm to reg
adcx r8, r14; loading flag
adcx rax, r9
mov r8, rdx; preserving value of x337 into a new reg
mov rdx, [ r10 + 0x0 ]; saving arg2[0] in rdx.
mulx r9, r14, r13; x388, x387<- x5 * arg2[0]
mov [ rsp + 0x2c0 ], r9; spilling x388 to mem
setc r9b; spill CF x365 to reg (r9)
clc;
adcx r14, rax
mov rax, 0x100000001 ; moving imm to reg
mov rdx, rax; 0x100000001 to rdx
mov byte [ rsp + 0x2c8 ], r9b; spilling byte x365 to mem
mulx rax, r9, r14; _, x414<- x400 * 0x100000001
mov rax, 0xffffffff ; moving imm to reg
xchg rdx, r9; x414, swapping with 0x100000001, which is currently in rdx
mov byte [ rsp + 0x2d0 ], cl; spilling byte x352 to mem
mulx r9, rcx, rax; x427, x426<- x414 * 0xffffffff
seto al; spill OF x326 to reg (rax)
mov [ rsp + 0x2d8 ], r9; spilling x427 to mem
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rcx, r14
movzx rcx, byte [ rsp + 0x238 ]; x54, copying x53 here, cause x53 is needed in a reg for other than x54, namely all: , x54, size: 1
mov r14, [ rsp + 0x220 ]; load m64 x33 to register64
lea rcx, [ rcx + r14 ]; r8/64 + m8
movzx r14, bl; x29, copying x28 here, cause x28 is needed in a reg for other than x29, namely all: , x29, size: 1
mov r9, [ rsp + 0x210 ]; load m64 x8 to register64
lea r14, [ r14 + r9 ]; r8/64 + m8
xchg rdx, rbp; x1, swapping with x414, which is currently in rdx
mulx rdx, r9, [ r10 + 0x28 ]; x70, x69<- x1 * arg2[5]
seto bl; spill OF x440 to reg (rbx)
mov [ rsp + 0x2e0 ], rdx; spilling x70 to mem
movzx rdx, byte [ rsp + 0x240 ]; load byte memx66 to register64
mov byte [ rsp + 0x2e8 ], al; spilling byte x326 to mem
mov rax, -0x1 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rax, -0x1 ; moving imm to reg
adox rdx, rax; loading flag
adox r14, rcx
seto dl; spill OF x68 to reg (rdx)
movzx rcx, byte [ rsp + 0x2b8 ]; load byte memx88 to register64
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rax, -0x1 ; moving imm to reg
adox rcx, rax; loading flag
adox r9, [ rsp + 0x230 ]
setc cl; spill CF x401 to reg (rcx)
movzx rax, byte [ rsp + 0x258 ]; load byte memx101 to register64
clc;
mov byte [ rsp + 0x2f0 ], bl; spilling byte x440 to mem
mov rbx, -0x1 ; moving imm to reg
adcx rax, rbx; loading flag
adcx r14, r9
mov rax, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rax; 0xffffffffffffffff, swapping with x68, which is currently in rdx
mulx r15, r9, r15; x109, x108<- x106 * 0xffffffffffffffff
seto bl; spill OF x90 to reg (rbx)
movzx rdx, byte [ rsp + 0x270 ]; load byte memx127 to register64
mov [ rsp + 0x2f8 ], r15; spilling x109 to mem
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rdx, r15; loading flag
adox r9, [ rsp + 0x248 ]
seto dl; spill OF x129 to reg (rdx)
movzx r15, byte [ rsp + 0x268 ]; load byte memx140 to register64
mov byte [ rsp + 0x300 ], al; spilling byte x68 to mem
mov rax, 0x0 ; moving imm to reg
dec rax; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, rax; loading flag
adox r14, r9
seto r15b; spill OF x142 to reg (r15)
movzx r9, byte [ rsp + 0x278 ]; load byte memx176 to register64
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rax, -0x1 ; moving imm to reg
adox r9, rax; loading flag
adox r14, [ rsp + 0xd8 ]
setc r9b; spill CF x103 to reg (r9)
movzx rax, byte [ rsp + 0x298 ]; load byte memx215 to register64
clc;
mov byte [ rsp + 0x308 ], r15b; spilling byte x142 to mem
mov r15, -0x1 ; moving imm to reg
adcx rax, r15; loading flag
adcx r14, [ rsp + 0xb0 ]
mov al, dl; preserving value of x129 into a new reg
mov rdx, [ r10 + 0x18 ]; saving arg2[3] in rdx.
mov byte [ rsp + 0x310 ], r9b; spilling byte x103 to mem
mulx r15, r9, r11; x228, x227<- x3 * arg2[3]
mov [ rsp + 0x318 ], r15; spilling x228 to mem
seto r15b; spill OF x178 to reg (r15)
mov byte [ rsp + 0x320 ], al; spilling byte x129 to mem
movzx rax, byte [ rsp + 0x288 ]; load byte memx238 to register64
mov byte [ rsp + 0x328 ], bl; spilling byte x90 to mem
mov rbx, -0x1 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbx, -0x1 ; moving imm to reg
adox rax, rbx; loading flag
adox r9, [ rsp + 0x260 ]
setc al; spill CF x217 to reg (rax)
movzx rbx, byte [ rsp + 0x290 ]; load byte memx251 to register64
clc;
mov byte [ rsp + 0x330 ], r15b; spilling byte x178 to mem
mov r15, -0x1 ; moving imm to reg
adcx rbx, r15; loading flag
adcx r14, r9
setc bl; spill CF x253 to reg (rbx)
movzx r9, byte [ rsp + 0x2b0 ]; load byte memx290 to register64
clc;
adcx r9, r15; loading flag
adcx r14, [ rsp + 0x168 ]
mov rdx, [ r10 + 0x10 ]; arg2[2] to rdx
mulx r9, r15, r12; x307, x306<- x4 * arg2[2]
mov [ rsp + 0x338 ], r9; spilling x307 to mem
seto r9b; spill OF x240 to reg (r9)
mov byte [ rsp + 0x340 ], bl; spilling byte x253 to mem
movzx rbx, byte [ rsp + 0x2a8 ]; load byte memx313 to register64
mov byte [ rsp + 0x348 ], al; spilling byte x217 to mem
mov rax, -0x1 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rax, -0x1 ; moving imm to reg
adox rbx, rax; loading flag
adox r15, [ rsp + 0x280 ]
seto bl; spill OF x315 to reg (rbx)
movzx rax, byte [ rsp + 0x2e8 ]; load byte memx326 to register64
mov byte [ rsp + 0x350 ], r9b; spilling byte x240 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rax, r9; loading flag
adox r14, r15
mov rax, 0xfffffffffffffffe ; moving imm to reg
mov rdx, r8; x337 to rdx
mulx r8, r15, rax; x346, x345<- x337 * 0xfffffffffffffffe
setc r9b; spill CF x292 to reg (r9)
movzx rax, byte [ rsp + 0x2d0 ]; load byte memx352 to register64
clc;
mov [ rsp + 0x358 ], r8; spilling x346 to mem
mov r8, -0x1 ; moving imm to reg
adcx rax, r8; loading flag
adcx r15, [ rsp + 0x2a0 ]
xchg rdx, r13; x5, swapping with x337, which is currently in rdx
mulx rax, r8, [ r10 + 0x8 ]; x386, x385<- x5 * arg2[1]
mov [ rsp + 0x360 ], rax; spilling x386 to mem
setc al; spill CF x354 to reg (rax)
clc;
adcx r8, [ rsp + 0x2c0 ]
mov byte [ rsp + 0x368 ], al; spilling byte x354 to mem
setc al; spill CF x390 to reg (rax)
mov byte [ rsp + 0x370 ], bl; spilling byte x315 to mem
movzx rbx, byte [ rsp + 0x2c8 ]; load byte memx365 to register64
clc;
mov byte [ rsp + 0x378 ], r9b; spilling byte x292 to mem
mov r9, -0x1 ; moving imm to reg
adcx rbx, r9; loading flag
adcx r14, r15
seto bl; spill OF x328 to reg (rbx)
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r15; loading flag
adox r14, r8
mov rcx, 0xffffffff00000000 ; moving imm to reg
xchg rdx, rbp; x414, swapping with x5, which is currently in rdx
mulx r8, r9, rcx; x425, x424<- x414 * 0xffffffff00000000
movzx r15, byte [ rsp + 0x328 ]; x91, copying x90 here, cause x90 is needed in a reg for other than x91, namely all: , x91, size: 1
mov rcx, [ rsp + 0x2e0 ]; load m64 x70 to register64
lea r15, [ r15 + rcx ]; r8/64 + m8
setc cl; spill CF x367 to reg (rcx)
clc;
adcx r9, [ rsp + 0x2d8 ]
mov [ rsp + 0x380 ], r8; spilling x425 to mem
setc r8b; spill CF x429 to reg (r8)
mov byte [ rsp + 0x388 ], al; spilling byte x390 to mem
movzx rax, byte [ rsp + 0x310 ]; load byte memx103 to register64
clc;
mov byte [ rsp + 0x390 ], cl; spilling byte x367 to mem
mov rcx, -0x1 ; moving imm to reg
mov byte [ rsp + 0x398 ], bl; spilling byte x328 to mem
movzx rbx, byte [ rsp + 0x300 ]; load byte memx68 to register64
adcx rax, rcx; loading flag
adcx r15, rbx
movzx rbx, byte [ rsp + 0x320 ]; x130, copying x129 here, cause x129 is needed in a reg for other than x130, namely all: , x130, size: 1
mov rax, [ rsp + 0x2f8 ]; load m64 x109 to register64
lea rbx, [ rbx + rax ]; r8/64 + m8
setc al; spill CF x105 to reg (rax)
movzx rcx, byte [ rsp + 0x2f0 ]; load byte memx440 to register64
clc;
mov byte [ rsp + 0x3a0 ], r8b; spilling byte x429 to mem
mov r8, -0x1 ; moving imm to reg
adcx rcx, r8; loading flag
adcx r14, r9
setc cl; spill CF x442 to reg (rcx)
movzx r9, byte [ rsp + 0x308 ]; load byte memx142 to register64
clc;
adcx r9, r8; loading flag
adcx r15, rbx
setc r9b; spill CF x144 to reg (r9)
movzx rbx, byte [ rsp + 0x330 ]; load byte memx178 to register64
clc;
adcx rbx, r8; loading flag
adcx r15, [ rsp + 0xd0 ]
seto bl; spill OF x403 to reg (rbx)
movzx r8, byte [ rsp + 0x348 ]; load byte memx217 to register64
mov [ rsp + 0x3a8 ], r14; spilling x441 to mem
mov r14, -0x1 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r14, -0x1 ; moving imm to reg
adox r8, r14; loading flag
adox r15, [ rsp + 0xa0 ]
mov r8, rdx; preserving value of x414 into a new reg
mov rdx, [ r10 + 0x20 ]; saving arg2[4] in rdx.
mov byte [ rsp + 0x3b0 ], al; spilling byte x105 to mem
mulx r14, rax, r11; x226, x225<- x3 * arg2[4]
mov [ rsp + 0x3b8 ], r14; spilling x226 to mem
setc r14b; spill CF x180 to reg (r14)
mov byte [ rsp + 0x3c0 ], r9b; spilling byte x144 to mem
movzx r9, byte [ rsp + 0x350 ]; load byte memx240 to register64
clc;
mov byte [ rsp + 0x3c8 ], cl; spilling byte x442 to mem
mov rcx, -0x1 ; moving imm to reg
adcx r9, rcx; loading flag
adcx rax, [ rsp + 0x318 ]
seto r9b; spill OF x219 to reg (r9)
movzx rcx, byte [ rsp + 0x340 ]; load byte memx253 to register64
mov byte [ rsp + 0x3d0 ], r14b; spilling byte x180 to mem
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rcx, r14; loading flag
adox r15, rax
seto cl; spill OF x255 to reg (rcx)
movzx rax, byte [ rsp + 0x378 ]; load byte memx292 to register64
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
adox rax, r14; loading flag
adox r15, [ rsp + 0x180 ]
mov rdx, [ r10 + 0x18 ]; arg2[3] to rdx
mulx rax, r14, r12; x305, x304<- x4 * arg2[3]
mov [ rsp + 0x3d8 ], rax; spilling x305 to mem
seto al; spill OF x294 to reg (rax)
mov byte [ rsp + 0x3e0 ], cl; spilling byte x255 to mem
movzx rcx, byte [ rsp + 0x370 ]; load byte memx315 to register64
mov byte [ rsp + 0x3e8 ], r9b; spilling byte x219 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rcx, r9; loading flag
adox r14, [ rsp + 0x338 ]
seto cl; spill OF x317 to reg (rcx)
movzx r9, byte [ rsp + 0x398 ]; load byte memx328 to register64
mov byte [ rsp + 0x3f0 ], al; spilling byte x294 to mem
mov rax, -0x1 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rax, -0x1 ; moving imm to reg
adox r9, rax; loading flag
adox r15, r14
mov r9, 0xffffffffffffffff ; moving imm to reg
mov rdx, r9; 0xffffffffffffffff to rdx
mulx r9, r14, r13; x344, x343<- x337 * 0xffffffffffffffff
seto al; spill OF x330 to reg (rax)
movzx rdx, byte [ rsp + 0x368 ]; load byte memx354 to register64
mov [ rsp + 0x3f8 ], r9; spilling x344 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rdx, r9; loading flag
adox r14, [ rsp + 0x358 ]
seto dl; spill OF x356 to reg (rdx)
movzx r9, byte [ rsp + 0x390 ]; load byte memx367 to register64
mov byte [ rsp + 0x400 ], al; spilling byte x330 to mem
mov rax, -0x1 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rax, -0x1 ; moving imm to reg
adox r9, rax; loading flag
adox r15, r14
xchg rdx, rbp; x5, swapping with x356, which is currently in rdx
mulx r9, r14, [ r10 + 0x10 ]; x384, x383<- x5 * arg2[2]
seto al; spill OF x369 to reg (rax)
mov [ rsp + 0x408 ], r9; spilling x384 to mem
movzx r9, byte [ rsp + 0x388 ]; load byte memx390 to register64
mov byte [ rsp + 0x410 ], bpl; spilling byte x356 to mem
mov rbp, -0x1 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
adox r9, rbp; loading flag
adox r14, [ rsp + 0x360 ]
seto r9b; spill OF x392 to reg (r9)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, rbp; loading flag
adox r15, r14
mov rbx, 0xfffffffffffffffe ; moving imm to reg
xchg rdx, rbx; 0xfffffffffffffffe, swapping with x5, which is currently in rdx
mulx r14, rbp, r8; x423, x422<- x414 * 0xfffffffffffffffe
seto dl; spill OF x405 to reg (rdx)
mov [ rsp + 0x418 ], r14; spilling x423 to mem
movzx r14, byte [ rsp + 0x3a0 ]; load byte memx429 to register64
mov byte [ rsp + 0x420 ], r9b; spilling byte x392 to mem
mov r9, -0x1 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r9, -0x1 ; moving imm to reg
adox r14, r9; loading flag
adox rbp, [ rsp + 0x380 ]
seto r14b; spill OF x431 to reg (r14)
movzx r9, byte [ rsp + 0x3c8 ]; load byte memx442 to register64
mov byte [ rsp + 0x428 ], dl; spilling byte x405 to mem
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
adox r9, rdx; loading flag
adox r15, rbp
movzx r9, byte [ rsp + 0x3c0 ]; x145, copying x144 here, cause x144 is needed in a reg for other than x145, namely all: , x145, size: 1
movzx rbp, byte [ rsp + 0x3b0 ]; load byte memx105 to register64
lea r9, [ r9 + rbp ]; r64+m8
seto bpl; spill OF x444 to reg (rbp)
movzx rdx, byte [ rsp + 0x3d0 ]; load byte memx180 to register64
mov [ rsp + 0x430 ], r15; spilling x443 to mem
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rdx, r15; loading flag
adox r9, [ rsp + 0xc8 ]
mov rdx, r11; x3 to rdx
mulx rdx, r11, [ r10 + 0x28 ]; x224, x223<- x3 * arg2[5]
mov r15, [ rsp + 0x3b8 ]; x243, copying x226 here, cause x226 is needed in a reg for other than x243, namely all: , x243--x244, size: 1
adcx r15, r11
setc r11b; spill CF x244 to reg (r11)
mov [ rsp + 0x438 ], rdx; spilling x224 to mem
movzx rdx, byte [ rsp + 0x3e8 ]; load byte memx219 to register64
clc;
mov byte [ rsp + 0x440 ], bpl; spilling byte x444 to mem
mov rbp, -0x1 ; moving imm to reg
adcx rdx, rbp; loading flag
adcx r9, [ rsp + 0xa8 ]
mov rdx, r12; x4 to rdx
mulx r12, rbp, [ r10 + 0x20 ]; x303, x302<- x4 * arg2[4]
mov [ rsp + 0x448 ], r12; spilling x303 to mem
setc r12b; spill CF x221 to reg (r12)
mov byte [ rsp + 0x450 ], r11b; spilling byte x244 to mem
movzx r11, byte [ rsp + 0x3e0 ]; load byte memx255 to register64
clc;
mov byte [ rsp + 0x458 ], r14b; spilling byte x431 to mem
mov r14, -0x1 ; moving imm to reg
adcx r11, r14; loading flag
adcx r9, r15
setc r11b; spill CF x257 to reg (r11)
movzx r15, byte [ rsp + 0x3f0 ]; load byte memx294 to register64
clc;
adcx r15, r14; loading flag
adcx r9, [ rsp + 0x178 ]
seto r15b; spill OF x182 to reg (r15)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r14; loading flag
adox rbp, [ rsp + 0x3d8 ]
setc cl; spill CF x296 to reg (rcx)
movzx r14, byte [ rsp + 0x400 ]; load byte memx330 to register64
clc;
mov byte [ rsp + 0x460 ], r11b; spilling byte x257 to mem
mov r11, -0x1 ; moving imm to reg
adcx r14, r11; loading flag
adcx r9, rbp
mov r14, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r14; 0xffffffffffffffff, swapping with x4, which is currently in rdx
mulx rbp, r11, r13; x342, x341<- x337 * 0xffffffffffffffff
seto dl; spill OF x319 to reg (rdx)
mov [ rsp + 0x468 ], rbp; spilling x342 to mem
movzx rbp, byte [ rsp + 0x410 ]; load byte memx356 to register64
mov byte [ rsp + 0x470 ], cl; spilling byte x296 to mem
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbp, rcx; loading flag
adox r11, [ rsp + 0x3f8 ]
xchg rdx, rbx; x5, swapping with x319, which is currently in rdx
mulx rbp, rcx, [ r10 + 0x18 ]; x382, x381<- x5 * arg2[3]
mov [ rsp + 0x478 ], rbp; spilling x382 to mem
seto bpl; spill OF x358 to reg (rbp)
mov byte [ rsp + 0x480 ], bl; spilling byte x319 to mem
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rax, al
adox rax, rbx; loading flag
adox r9, r11
seto al; spill OF x371 to reg (rax)
movzx r11, byte [ rsp + 0x420 ]; load byte memx392 to register64
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
adox r11, rbx; loading flag
adox rcx, [ rsp + 0x408 ]
seto r11b; spill OF x394 to reg (r11)
movzx rbx, byte [ rsp + 0x428 ]; load byte memx405 to register64
mov byte [ rsp + 0x488 ], al; spilling byte x371 to mem
mov rax, -0x1 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rax, -0x1 ; moving imm to reg
adox rbx, rax; loading flag
adox r9, rcx
mov rbx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r8; x414, swapping with x5, which is currently in rdx
mulx rcx, rax, rbx; x421, x420<- x414 * 0xffffffffffffffff
seto bl; spill OF x407 to reg (rbx)
mov [ rsp + 0x490 ], rcx; spilling x421 to mem
movzx rcx, byte [ rsp + 0x458 ]; load byte memx431 to register64
mov byte [ rsp + 0x498 ], r11b; spilling byte x394 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
adox rcx, r11; loading flag
adox rax, [ rsp + 0x418 ]
movzx rcx, r12b; x222, copying x221 here, cause x221 is needed in a reg for other than x222, namely all: , x222, size: 1
movzx r15, r15b
lea rcx, [ rcx + r15 ]
setc r15b; spill CF x332 to reg (r15)
movzx r12, byte [ rsp + 0x440 ]; load byte memx444 to register64
clc;
adcx r12, r11; loading flag
adcx r9, rax
movzx r12, byte [ rsp + 0x450 ]; x245, copying x244 here, cause x244 is needed in a reg for other than x245, namely all: , x245, size: 1
mov rax, [ rsp + 0x438 ]; load m64 x224 to register64
lea r12, [ r12 + rax ]; r8/64 + m8
setc al; spill CF x446 to reg (rax)
movzx r11, byte [ rsp + 0x460 ]; load byte memx257 to register64
clc;
mov [ rsp + 0x4a0 ], r9; spilling x445 to mem
mov r9, -0x1 ; moving imm to reg
adcx r11, r9; loading flag
adcx rcx, r12
setc r11b; spill CF x259 to reg (r11)
movzx r12, byte [ rsp + 0x470 ]; load byte memx296 to register64
clc;
adcx r12, r9; loading flag
adcx rcx, [ rsp + 0x170 ]
xchg rdx, r14; x4, swapping with x414, which is currently in rdx
mulx rdx, r12, [ r10 + 0x28 ]; x301, x300<- x4 * arg2[5]
seto r9b; spill OF x433 to reg (r9)
mov [ rsp + 0x4a8 ], rdx; spilling x301 to mem
movzx rdx, byte [ rsp + 0x480 ]; load byte memx319 to register64
mov byte [ rsp + 0x4b0 ], r11b; spilling byte x259 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
adox rdx, r11; loading flag
adox r12, [ rsp + 0x448 ]
seto dl; spill OF x321 to reg (rdx)
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r11, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, r11; loading flag
adox rcx, r12
mov r15, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r13; x337, swapping with x321, which is currently in rdx
mulx rdx, r12, r15; x340, x339<- x337 * 0xffffffffffffffff
seto r11b; spill OF x334 to reg (r11)
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r15, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, r15; loading flag
adox r12, [ rsp + 0x468 ]
seto bpl; spill OF x360 to reg (rbp)
movzx r15, byte [ rsp + 0x488 ]; load byte memx371 to register64
mov [ rsp + 0x4b8 ], rdx; spilling x340 to mem
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
adox r15, rdx; loading flag
adox rcx, r12
mov rdx, r8; x5 to rdx
mulx r8, r15, [ r10 + 0x20 ]; x380, x379<- x5 * arg2[4]
setc r12b; spill CF x298 to reg (r12)
mov [ rsp + 0x4c0 ], r8; spilling x380 to mem
movzx r8, byte [ rsp + 0x498 ]; load byte memx394 to register64
clc;
mov byte [ rsp + 0x4c8 ], bpl; spilling byte x360 to mem
mov rbp, -0x1 ; moving imm to reg
adcx r8, rbp; loading flag
adcx r15, [ rsp + 0x478 ]
setc r8b; spill CF x396 to reg (r8)
clc;
movzx rbx, bl
adcx rbx, rbp; loading flag
adcx rcx, r15
mov rbx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbx; 0xffffffffffffffff, swapping with x5, which is currently in rdx
mulx r15, rbp, r14; x419, x418<- x414 * 0xffffffffffffffff
seto dl; spill OF x373 to reg (rdx)
mov [ rsp + 0x4d0 ], r15; spilling x419 to mem
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r15, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, r15; loading flag
adox rbp, [ rsp + 0x490 ]
setc r9b; spill CF x409 to reg (r9)
clc;
movzx rax, al
adcx rax, r15; loading flag
adcx rcx, rbp
movzx rax, r12b; x299, copying x298 here, cause x298 is needed in a reg for other than x299, namely all: , x299, size: 1
movzx rbp, byte [ rsp + 0x4b0 ]; load byte memx259 to register64
lea rax, [ rax + rbp ]; r64+m8
movzx rbp, r13b; x322, copying x321 here, cause x321 is needed in a reg for other than x322, namely all: , x322, size: 1
mov r12, [ rsp + 0x4a8 ]; load m64 x301 to register64
lea rbp, [ rbp + r12 ]; r8/64 + m8
seto r12b; spill OF x435 to reg (r12)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, r13; loading flag
adox rax, rbp
movzx r11, byte [ rsp + 0x4c8 ]; x361, copying x360 here, cause x360 is needed in a reg for other than x361, namely all: , x361, size: 1
mov rbp, [ rsp + 0x4b8 ]; load m64 x340 to register64
lea r11, [ r11 + rbp ]; r8/64 + m8
setc bpl; spill CF x448 to reg (rbp)
clc;
movzx rdx, dl
adcx rdx, r13; loading flag
adcx rax, r11
mov rdx, [ r10 + 0x28 ]; arg2[5] to rdx
mulx rbx, r11, rbx; x378, x377<- x5 * arg2[5]
seto r15b; spill OF x336 to reg (r15)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, r13; loading flag
adox r11, [ rsp + 0x4c0 ]
setc r8b; spill CF x375 to reg (r8)
clc;
movzx r9, r9b
adcx r9, r13; loading flag
adcx rax, r11
mov r9, 0xffffffffffffffff ; moving imm to reg
mov rdx, r14; x414 to rdx
mulx rdx, r14, r9; x417, x416<- x414 * 0xffffffffffffffff
seto r11b; spill OF x398 to reg (r11)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, r13; loading flag
adox r14, [ rsp + 0x4d0 ]
seto r12b; spill OF x437 to reg (r12)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, r13; loading flag
adox rax, r14
movzx rbp, r11b; x399, copying x398 here, cause x398 is needed in a reg for other than x399, namely all: , x399, size: 1
lea rbp, [ rbp + rbx ]
movzx rbx, r8b; x376, copying x375 here, cause x375 is needed in a reg for other than x376, namely all: , x376, size: 1
movzx r15, r15b
lea rbx, [ rbx + r15 ]
adcx rbp, rbx
movzx r15, r12b; x438, copying x437 here, cause x437 is needed in a reg for other than x438, namely all: , x438, size: 1
lea r15, [ r15 + rdx ]
adox r15, rbp
seto r8b; spill OF x453 to reg (r8)
adc r8b, 0x0
movzx r8, r8b
mov r11, [ rsp + 0x3a8 ]; x454, copying x441 here, cause x441 is needed in a reg for other than x454, namely all: , x468, x454--x455, size: 2
mov rdx, 0xffffffff ; moving imm to reg
sub r11, rdx
mov r14, [ rsp + 0x430 ]; x456, copying x443 here, cause x443 is needed in a reg for other than x456, namely all: , x469, x456--x457, size: 2
mov r12, 0xffffffff00000000 ; moving imm to reg
sbb r14, r12
mov rbx, [ rsp + 0x4a0 ]; x458, copying x445 here, cause x445 is needed in a reg for other than x458, namely all: , x458--x459, x470, size: 2
mov rbp, 0xfffffffffffffffe ; moving imm to reg
sbb rbx, rbp
mov r13, rcx; x460, copying x447 here, cause x447 is needed in a reg for other than x460, namely all: , x471, x460--x461, size: 2
sbb r13, r9
mov rbp, rax; x462, copying x449 here, cause x449 is needed in a reg for other than x462, namely all: , x472, x462--x463, size: 2
sbb rbp, r9
mov r12, r15; x464, copying x451 here, cause x451 is needed in a reg for other than x464, namely all: , x464--x465, x473, size: 2
sbb r12, r9
movzx rdx, r8b; _, copying x453 here, cause x453 is needed in a reg for other than _, namely all: , _--x467, size: 1
sbb rdx, 0x00000000
cmovc r11, [ rsp + 0x3a8 ]; if CF, x468<- x441 (nzVar)
mov r8, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r8 + 0x0 ], r11; out1[0] = x468
cmovc rbp, rax; if CF, x472<- x449 (nzVar)
cmovc r13, rcx; if CF, x471<- x447 (nzVar)
cmovc r12, r15; if CF, x473<- x451 (nzVar)
cmovc rbx, [ rsp + 0x4a0 ]; if CF, x470<- x445 (nzVar)
mov [ r8 + 0x28 ], r12; out1[5] = x473
mov [ r8 + 0x10 ], rbx; out1[2] = x470
cmovc r14, [ rsp + 0x430 ]; if CF, x469<- x443 (nzVar)
mov [ r8 + 0x8 ], r14; out1[1] = x469
mov [ r8 + 0x20 ], rbp; out1[4] = x472
mov [ r8 + 0x18 ], r13; out1[3] = x471
mov rbx, [ rsp + 0x4d8 ]; restoring from stack
mov rbp, [ rsp + 0x4e0 ]; restoring from stack
mov r12, [ rsp + 0x4e8 ]; restoring from stack
mov r13, [ rsp + 0x4f0 ]; restoring from stack
mov r14, [ rsp + 0x4f8 ]; restoring from stack
mov r15, [ rsp + 0x500 ]; restoring from stack
add rsp, 0x508 
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; clocked at 2600 MHz
; first cyclecount 366.81, best 364, lastGood 374.780487804878
; seed 2764343611261468 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 56246 ms / 500 runs=> 112.492ms/run
; Time spent for assembling and measureing (initial batch_size=41, initial num_batches=101): 1791 ms
; Ratio (time for assembling + measure)/(total runtime for 500runs): 0.03184226433879742
; number reverted permutation/ tried permutation: 188 / 250 =75.200%
; number reverted decision/ tried decision: 157 / 251 =62.550%