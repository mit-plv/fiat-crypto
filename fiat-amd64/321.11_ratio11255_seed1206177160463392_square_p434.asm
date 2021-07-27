SECTION .text
	GLOBAL square_p434
square_p434:
sub rsp, 0x430 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x400 ], rbx; saving to stack
mov [ rsp + 0x408 ], rbp; saving to stack
mov [ rsp + 0x410 ], r12; saving to stack
mov [ rsp + 0x418 ], r13; saving to stack
mov [ rsp + 0x420 ], r14; saving to stack
mov [ rsp + 0x428 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x7 to register64
mov rdx, rax; x7 to rdx
mulx rax, r10, [ rsi + 0x8 ]; x19, x18<- x7 * arg1[1]
mulx r11, rbx, [ rsi + 0x0 ]; x21, x20<- x7 * arg1[0]
mov rbp, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbp; 0xffffffffffffffff, swapping with x7, which is currently in rdx
mulx r12, r13, rbx; x48, x47<- x20 * 0xffffffffffffffff
test al, al
adox r10, r11
adcx r13, rbx
mulx r13, r14, rbx; x46, x45<- x20 * 0xffffffffffffffff
seto r15b; spill OF x23 to reg (r15)
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, r12
mov r8, [ rsi + 0x8 ]; load m64 x1 to register64
adcx r14, r10
xchg rdx, r8; x1, swapping with 0xffffffffffffffff, which is currently in rdx
mulx r9, r11, [ rsi + 0x0 ]; x91, x90<- x1 * arg1[0]
setc r12b; spill CF x65 to reg (r12)
clc;
adcx r11, r14
xchg rdx, r11; x105, swapping with x1, which is currently in rdx
mulx r10, r14, r8; x134, x133<- x105 * 0xffffffffffffffff
mov rcx, rdx; preserving value of x105 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r8, rdi, rbp; x17, x16<- x7 * arg1[2]
setc dl; spill CF x106 to reg (rdx)
clc;
mov [ rsp + 0x8 ], r8; spilling x17 to mem
mov r8, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, r8; loading flag
adcx rax, rdi
mov r15, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbx; x20, swapping with x106, which is currently in rdx
mulx rdi, r8, r15; x44, x43<- x20 * 0xffffffffffffffff
adox r8, r13
setc r13b; spill CF x25 to reg (r13)
clc;
adcx r14, rcx
setc r14b; spill CF x149 to reg (r14)
clc;
mov r15, -0x1 ; moving imm to reg
movzx r12, r12b
adcx r12, r15; loading flag
adcx rax, r8
mov r12, rdx; preserving value of x20 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r8, r15, r11; x89, x88<- x1 * arg1[1]
seto dl; spill OF x52 to reg (rdx)
mov [ rsp + 0x10 ], r8; spilling x89 to mem
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, r9
seto r9b; spill OF x93 to reg (r9)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, r8; loading flag
adox rax, r15
mov rbx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rcx; x105, swapping with x52, which is currently in rdx
mulx r15, r8, rbx; x132, x131<- x105 * 0xffffffffffffffff
seto bl; spill OF x108 to reg (rbx)
mov [ rsp + 0x18 ], r15; spilling x132 to mem
mov r15, -0x2 ; moving imm to reg
inc r15; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, r10
mov r10, [ rsi + 0x10 ]; load m64 x2 to register64
setc r15b; spill CF x67 to reg (r15)
clc;
mov byte [ rsp + 0x20 ], bl; spilling byte x108 to mem
mov rbx, -0x1 ; moving imm to reg
movzx r14, r14b
adcx r14, rbx; loading flag
adcx rax, r8
mov r14, rdx; preserving value of x105 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r8, rbx, r10; x178, x177<- x2 * arg1[0]
seto dl; spill OF x136 to reg (rdx)
mov [ rsp + 0x28 ], r8; spilling x178 to mem
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, rax
mov rax, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbx; x192, swapping with x136, which is currently in rdx
mov byte [ rsp + 0x30 ], bl; spilling byte x136 to mem
mulx r8, rbx, rax; x221, x220<- x192 * 0xffffffffffffffff
mov byte [ rsp + 0x38 ], r9b; spilling byte x93 to mem
mov byte [ rsp + 0x40 ], r15b; spilling byte x67 to mem
mulx r9, r15, rax; x219, x218<- x192 * 0xffffffffffffffff
mov [ rsp + 0x48 ], rdi; spilling x44 to mem
mov byte [ rsp + 0x50 ], cl; spilling byte x52 to mem
mulx rdi, rcx, rax; x217, x216<- x192 * 0xffffffffffffffff
seto al; spill OF x193 to reg (rax)
mov byte [ rsp + 0x58 ], r13b; spilling byte x25 to mem
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, r8
adox rcx, r9
mov r8, 0xfdc1767ae2ffffff ; moving imm to reg
mulx r9, r13, r8; x215, x214<- x192 * 0xfdc1767ae2ffffff
adox r13, rdi
mov rdi, 0x7bc65c783158aea3 ; moving imm to reg
mov [ rsp + 0x60 ], r13; spilling x226 to mem
mulx r8, r13, rdi; x213, x212<- x192 * 0x7bc65c783158aea3
adox r13, r9
mov r9, 0x6cfc5fd681c52056 ; moving imm to reg
mov [ rsp + 0x68 ], r13; spilling x228 to mem
mulx rdi, r13, r9; x211, x210<- x192 * 0x6cfc5fd681c52056
adox r13, r8
mov r8, 0x2341f27177344 ; moving imm to reg
mov [ rsp + 0x70 ], r13; spilling x230 to mem
mulx r9, r13, r8; x209, x208<- x192 * 0x2341f27177344
adox r13, rdi
mov rdi, [ rsi + 0x18 ]; load m64 x3 to register64
mov r8, 0x0 ; moving imm to reg
adox r9, r8
mov [ rsp + 0x78 ], r9; spilling x234 to mem
mov r9, -0x3 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbx, rdx
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rbx, r8, rbp; x15, x14<- x7 * arg1[3]
mov rdx, 0xfdc1767ae2ffffff ; moving imm to reg
mov [ rsp + 0x80 ], r13; spilling x232 to mem
mulx r9, r13, r12; x42, x41<- x20 * 0xfdc1767ae2ffffff
seto dl; spill OF x236 to reg (rdx)
mov [ rsp + 0x88 ], rcx; spilling x224 to mem
movzx rcx, byte [ rsp + 0x58 ]; load byte memx25 to register64
mov [ rsp + 0x90 ], r9; spilling x42 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rcx, r9; loading flag
adox r8, [ rsp + 0x8 ]
seto cl; spill OF x27 to reg (rcx)
movzx r9, byte [ rsp + 0x50 ]; load byte memx52 to register64
mov [ rsp + 0x98 ], rbx; spilling x15 to mem
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r9, rbx; loading flag
adox r13, [ rsp + 0x48 ]
mov r9b, dl; preserving value of x236 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov byte [ rsp + 0xa0 ], cl; spilling byte x27 to mem
mulx rbx, rcx, r11; x87, x86<- x1 * arg1[2]
setc dl; spill CF x151 to reg (rdx)
mov [ rsp + 0xa8 ], rbx; spilling x87 to mem
movzx rbx, byte [ rsp + 0x40 ]; load byte memx67 to register64
clc;
mov [ rsp + 0xb0 ], r15; spilling x222 to mem
mov r15, -0x1 ; moving imm to reg
adcx rbx, r15; loading flag
adcx r8, r13
setc bl; spill CF x69 to reg (rbx)
movzx r13, byte [ rsp + 0x38 ]; load byte memx93 to register64
clc;
adcx r13, r15; loading flag
adcx rcx, [ rsp + 0x10 ]
seto r13b; spill OF x54 to reg (r13)
movzx r15, byte [ rsp + 0x20 ]; load byte memx108 to register64
mov byte [ rsp + 0xb8 ], bl; spilling byte x69 to mem
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, rbx; loading flag
adox r8, rcx
mov r15, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r14; x105, swapping with x151, which is currently in rdx
mulx rcx, rbx, r15; x130, x129<- x105 * 0xffffffffffffffff
setc r15b; spill CF x95 to reg (r15)
mov [ rsp + 0xc0 ], rcx; spilling x130 to mem
movzx rcx, byte [ rsp + 0x30 ]; load byte memx136 to register64
clc;
mov byte [ rsp + 0xc8 ], r13b; spilling byte x54 to mem
mov r13, -0x1 ; moving imm to reg
adcx rcx, r13; loading flag
adcx rbx, [ rsp + 0x18 ]
seto cl; spill OF x110 to reg (rcx)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, r13; loading flag
adox r8, rbx
mov r14, rdx; preserving value of x105 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx rbx, r13, r10; x176, x175<- x2 * arg1[1]
mov rdx, rdi; x3 to rdx
mov [ rsp + 0xd0 ], rbx; spilling x176 to mem
mov byte [ rsp + 0xd8 ], cl; spilling byte x110 to mem
mulx rbx, rcx, [ rsi + 0x0 ]; x265, x264<- x3 * arg1[0]
mov [ rsp + 0xe0 ], rbx; spilling x265 to mem
setc bl; spill CF x138 to reg (rbx)
clc;
adcx r13, [ rsp + 0x28 ]
mov byte [ rsp + 0xe8 ], bl; spilling byte x138 to mem
setc bl; spill CF x180 to reg (rbx)
clc;
mov byte [ rsp + 0xf0 ], r15b; spilling byte x95 to mem
mov r15, -0x1 ; moving imm to reg
movzx rax, al
adcx rax, r15; loading flag
adcx r8, r13
setc al; spill CF x195 to reg (rax)
clc;
movzx r9, r9b
adcx r9, r15; loading flag
adcx r8, [ rsp + 0xb0 ]
setc r9b; spill CF x238 to reg (r9)
clc;
adcx rcx, r8
mov r13, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r13; 0xffffffffffffffff, swapping with x3, which is currently in rdx
mulx r8, r15, rcx; x308, x307<- x279 * 0xffffffffffffffff
setc dl; spill CF x280 to reg (rdx)
clc;
adcx r15, rcx
xchg rdx, rbp; x7, swapping with x280, which is currently in rdx
mov [ rsp + 0xf8 ], r8; spilling x308 to mem
mulx r15, r8, [ rsi + 0x20 ]; x13, x12<- x7 * arg1[4]
mov [ rsp + 0x100 ], r15; spilling x13 to mem
mov r15, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, r12; x20, swapping with x7, which is currently in rdx
mov byte [ rsp + 0x108 ], bpl; spilling byte x280 to mem
mov byte [ rsp + 0x110 ], r9b; spilling byte x238 to mem
mulx rbp, r9, r15; x40, x39<- x20 * 0x7bc65c783158aea3
setc r15b; spill CF x323 to reg (r15)
mov [ rsp + 0x118 ], rbp; spilling x40 to mem
movzx rbp, byte [ rsp + 0xa0 ]; load byte memx27 to register64
clc;
mov byte [ rsp + 0x120 ], al; spilling byte x195 to mem
mov rax, -0x1 ; moving imm to reg
adcx rbp, rax; loading flag
adcx r8, [ rsp + 0x98 ]
seto bpl; spill OF x153 to reg (rbp)
movzx rax, byte [ rsp + 0xc8 ]; load byte memx54 to register64
mov byte [ rsp + 0x128 ], r15b; spilling byte x323 to mem
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rax, r15; loading flag
adox r9, [ rsp + 0x90 ]
setc al; spill CF x29 to reg (rax)
movzx r15, byte [ rsp + 0xb8 ]; load byte memx69 to register64
clc;
mov byte [ rsp + 0x130 ], bl; spilling byte x180 to mem
mov rbx, -0x1 ; moving imm to reg
adcx r15, rbx; loading flag
adcx r8, r9
xchg rdx, r11; x1, swapping with x20, which is currently in rdx
mulx r15, r9, [ rsi + 0x18 ]; x85, x84<- x1 * arg1[3]
seto bl; spill OF x56 to reg (rbx)
mov [ rsp + 0x138 ], r15; spilling x85 to mem
movzx r15, byte [ rsp + 0xf0 ]; load byte memx95 to register64
mov byte [ rsp + 0x140 ], al; spilling byte x29 to mem
mov rax, 0x0 ; moving imm to reg
dec rax; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, rax; loading flag
adox r9, [ rsp + 0xa8 ]
setc r15b; spill CF x71 to reg (r15)
movzx rax, byte [ rsp + 0xd8 ]; load byte memx110 to register64
clc;
mov byte [ rsp + 0x148 ], bl; spilling byte x56 to mem
mov rbx, -0x1 ; moving imm to reg
adcx rax, rbx; loading flag
adcx r8, r9
mov rax, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, rax; 0xfdc1767ae2ffffff, swapping with x1, which is currently in rdx
mulx r9, rbx, r14; x128, x127<- x105 * 0xfdc1767ae2ffffff
setc dl; spill CF x112 to reg (rdx)
mov [ rsp + 0x150 ], r9; spilling x128 to mem
movzx r9, byte [ rsp + 0xe8 ]; load byte memx138 to register64
clc;
mov byte [ rsp + 0x158 ], r15b; spilling byte x71 to mem
mov r15, -0x1 ; moving imm to reg
adcx r9, r15; loading flag
adcx rbx, [ rsp + 0xc0 ]
mov r9b, dl; preserving value of x112 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x160 ], rbx; spilling x139 to mem
mulx r15, rbx, r10; x174, x173<- x2 * arg1[2]
setc dl; spill CF x140 to reg (rdx)
clc;
mov [ rsp + 0x168 ], r15; spilling x174 to mem
mov r15, -0x1 ; moving imm to reg
movzx rbp, bpl
adcx rbp, r15; loading flag
adcx r8, [ rsp + 0x160 ]
seto bpl; spill OF x97 to reg (rbp)
movzx r15, byte [ rsp + 0x130 ]; load byte memx180 to register64
mov byte [ rsp + 0x170 ], dl; spilling byte x140 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, rdx; loading flag
adox rbx, [ rsp + 0xd0 ]
setc r15b; spill CF x155 to reg (r15)
movzx rdx, byte [ rsp + 0x120 ]; load byte memx195 to register64
clc;
mov byte [ rsp + 0x178 ], r9b; spilling byte x112 to mem
mov r9, -0x1 ; moving imm to reg
adcx rdx, r9; loading flag
adcx r8, rbx
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbx, r9, r13; x263, x262<- x3 * arg1[1]
setc dl; spill CF x197 to reg (rdx)
mov [ rsp + 0x180 ], rbx; spilling x263 to mem
movzx rbx, byte [ rsp + 0x110 ]; load byte memx238 to register64
clc;
mov byte [ rsp + 0x188 ], r15b; spilling byte x155 to mem
mov r15, -0x1 ; moving imm to reg
adcx rbx, r15; loading flag
adcx r8, [ rsp + 0x88 ]
seto bl; spill OF x182 to reg (rbx)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r9, [ rsp + 0xe0 ]
setc r15b; spill CF x240 to reg (r15)
mov byte [ rsp + 0x190 ], dl; spilling byte x197 to mem
movzx rdx, byte [ rsp + 0x108 ]; load byte memx280 to register64
clc;
mov byte [ rsp + 0x198 ], bl; spilling byte x182 to mem
mov rbx, -0x1 ; moving imm to reg
adcx rdx, rbx; loading flag
adcx r8, r9
mov rdx, 0xffffffffffffffff ; moving imm to reg
mulx r9, rbx, rcx; x306, x305<- x279 * 0xffffffffffffffff
setc dl; spill CF x282 to reg (rdx)
clc;
adcx rbx, [ rsp + 0xf8 ]
mov [ rsp + 0x1a0 ], r9; spilling x306 to mem
mov r9b, dl; preserving value of x282 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov byte [ rsp + 0x1a8 ], r15b; spilling byte x240 to mem
mov byte [ rsp + 0x1b0 ], bpl; spilling byte x97 to mem
mulx r15, rbp, r12; x11, x10<- x7 * arg1[5]
setc dl; spill CF x310 to reg (rdx)
mov [ rsp + 0x1b8 ], r15; spilling x11 to mem
movzx r15, byte [ rsp + 0x128 ]; load byte memx323 to register64
clc;
mov byte [ rsp + 0x1c0 ], r9b; spilling byte x282 to mem
mov r9, -0x1 ; moving imm to reg
adcx r15, r9; loading flag
adcx r8, rbx
mov r15, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, r15; 0x6cfc5fd681c52056, swapping with x310, which is currently in rdx
mulx rbx, r9, r11; x38, x37<- x20 * 0x6cfc5fd681c52056
setc dl; spill CF x325 to reg (rdx)
mov [ rsp + 0x1c8 ], r8; spilling x324 to mem
movzx r8, byte [ rsp + 0x140 ]; load byte memx29 to register64
clc;
mov [ rsp + 0x1d0 ], rbx; spilling x38 to mem
mov rbx, -0x1 ; moving imm to reg
adcx r8, rbx; loading flag
adcx rbp, [ rsp + 0x100 ]
seto r8b; spill OF x267 to reg (r8)
movzx rbx, byte [ rsp + 0x148 ]; load byte memx56 to register64
mov byte [ rsp + 0x1d8 ], dl; spilling byte x325 to mem
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
adox rbx, rdx; loading flag
adox r9, [ rsp + 0x118 ]
setc bl; spill CF x31 to reg (rbx)
movzx rdx, byte [ rsp + 0x158 ]; load byte memx71 to register64
clc;
mov byte [ rsp + 0x1e0 ], r15b; spilling byte x310 to mem
mov r15, -0x1 ; moving imm to reg
adcx rdx, r15; loading flag
adcx rbp, r9
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r9, r15, rax; x83, x82<- x1 * arg1[4]
seto dl; spill OF x58 to reg (rdx)
mov [ rsp + 0x1e8 ], r9; spilling x83 to mem
movzx r9, byte [ rsp + 0x1b0 ]; load byte memx97 to register64
mov byte [ rsp + 0x1f0 ], bl; spilling byte x31 to mem
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r9, rbx; loading flag
adox r15, [ rsp + 0x138 ]
mov r9, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, r9; 0x7bc65c783158aea3, swapping with x58, which is currently in rdx
mov byte [ rsp + 0x1f8 ], r9b; spilling byte x58 to mem
mulx rbx, r9, r14; x126, x125<- x105 * 0x7bc65c783158aea3
setc dl; spill CF x73 to reg (rdx)
mov [ rsp + 0x200 ], rbx; spilling x126 to mem
movzx rbx, byte [ rsp + 0x178 ]; load byte memx112 to register64
clc;
mov byte [ rsp + 0x208 ], r8b; spilling byte x267 to mem
mov r8, -0x1 ; moving imm to reg
adcx rbx, r8; loading flag
adcx rbp, r15
setc bl; spill CF x114 to reg (rbx)
movzx r15, byte [ rsp + 0x170 ]; load byte memx140 to register64
clc;
adcx r15, r8; loading flag
adcx r9, [ rsp + 0x150 ]
seto r15b; spill OF x99 to reg (r15)
movzx r8, byte [ rsp + 0x188 ]; load byte memx155 to register64
mov byte [ rsp + 0x210 ], bl; spilling byte x114 to mem
mov rbx, -0x1 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbx, -0x1 ; moving imm to reg
adox r8, rbx; loading flag
adox rbp, r9
xchg rdx, r10; x2, swapping with x73, which is currently in rdx
mulx r8, r9, [ rsi + 0x18 ]; x172, x171<- x2 * arg1[3]
seto bl; spill OF x157 to reg (rbx)
mov [ rsp + 0x218 ], r8; spilling x172 to mem
movzx r8, byte [ rsp + 0x198 ]; load byte memx182 to register64
mov byte [ rsp + 0x220 ], r15b; spilling byte x99 to mem
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r15, -0x1 ; moving imm to reg
adox r8, r15; loading flag
adox r9, [ rsp + 0x168 ]
seto r8b; spill OF x184 to reg (r8)
movzx r15, byte [ rsp + 0x190 ]; load byte memx197 to register64
mov byte [ rsp + 0x228 ], bl; spilling byte x157 to mem
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, rbx; loading flag
adox rbp, r9
setc r15b; spill CF x142 to reg (r15)
movzx r9, byte [ rsp + 0x1a8 ]; load byte memx240 to register64
clc;
adcx r9, rbx; loading flag
adcx rbp, [ rsp + 0x60 ]
xchg rdx, r13; x3, swapping with x2, which is currently in rdx
mulx r9, rbx, [ rsi + 0x10 ]; x261, x260<- x3 * arg1[2]
mov [ rsp + 0x230 ], r9; spilling x261 to mem
setc r9b; spill CF x242 to reg (r9)
mov byte [ rsp + 0x238 ], r8b; spilling byte x184 to mem
movzx r8, byte [ rsp + 0x208 ]; load byte memx267 to register64
clc;
mov byte [ rsp + 0x240 ], r15b; spilling byte x142 to mem
mov r15, -0x1 ; moving imm to reg
adcx r8, r15; loading flag
adcx rbx, [ rsp + 0x180 ]
mov r8, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r8; 0xffffffffffffffff, swapping with x3, which is currently in rdx
mov byte [ rsp + 0x248 ], r9b; spilling byte x242 to mem
mulx r15, r9, rcx; x304, x303<- x279 * 0xffffffffffffffff
xchg rdx, r12; x7, swapping with 0xffffffffffffffff, which is currently in rdx
mulx rdx, r12, [ rsi + 0x30 ]; x9, x8<- x7 * arg1[6]
mov [ rsp + 0x250 ], rdx; spilling x9 to mem
setc dl; spill CF x269 to reg (rdx)
mov [ rsp + 0x258 ], r15; spilling x304 to mem
movzx r15, byte [ rsp + 0x1c0 ]; load byte memx282 to register64
clc;
mov byte [ rsp + 0x260 ], r10b; spilling byte x73 to mem
mov r10, -0x1 ; moving imm to reg
adcx r15, r10; loading flag
adcx rbp, rbx
setc r15b; spill CF x284 to reg (r15)
movzx rbx, byte [ rsp + 0x1e0 ]; load byte memx310 to register64
clc;
adcx rbx, r10; loading flag
adcx r9, [ rsp + 0x1a0 ]
seto bl; spill OF x199 to reg (rbx)
movzx r10, byte [ rsp + 0x1d8 ]; load byte memx325 to register64
mov byte [ rsp + 0x268 ], r15b; spilling byte x284 to mem
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r15, -0x1 ; moving imm to reg
adox r10, r15; loading flag
adox rbp, r9
mov r10, 0x2341f27177344 ; moving imm to reg
xchg rdx, r10; 0x2341f27177344, swapping with x269, which is currently in rdx
mulx r11, r9, r11; x36, x35<- x20 * 0x2341f27177344
setc r15b; spill CF x312 to reg (r15)
movzx rdx, byte [ rsp + 0x1f0 ]; load byte memx31 to register64
clc;
mov [ rsp + 0x270 ], rbp; spilling x326 to mem
mov rbp, -0x1 ; moving imm to reg
adcx rdx, rbp; loading flag
adcx r12, [ rsp + 0x1b8 ]
seto dl; spill OF x327 to reg (rdx)
movzx rbp, byte [ rsp + 0x1f8 ]; load byte memx58 to register64
mov [ rsp + 0x278 ], r11; spilling x36 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
adox rbp, r11; loading flag
adox r9, [ rsp + 0x1d0 ]
setc bpl; spill CF x33 to reg (rbp)
movzx r11, byte [ rsp + 0x260 ]; load byte memx73 to register64
clc;
mov byte [ rsp + 0x280 ], dl; spilling byte x327 to mem
mov rdx, -0x1 ; moving imm to reg
adcx r11, rdx; loading flag
adcx r12, r9
mov rdx, rax; x1 to rdx
mulx rax, r11, [ rsi + 0x28 ]; x81, x80<- x1 * arg1[5]
seto r9b; spill OF x60 to reg (r9)
mov [ rsp + 0x288 ], rax; spilling x81 to mem
movzx rax, byte [ rsp + 0x220 ]; load byte memx99 to register64
mov byte [ rsp + 0x290 ], bpl; spilling byte x33 to mem
mov rbp, 0x0 ; moving imm to reg
dec rbp; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rax, rbp; loading flag
adox r11, [ rsp + 0x1e8 ]
mov rax, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, r14; x105, swapping with x1, which is currently in rdx
mov byte [ rsp + 0x298 ], r9b; spilling byte x60 to mem
mulx rbp, r9, rax; x124, x123<- x105 * 0x6cfc5fd681c52056
seto al; spill OF x101 to reg (rax)
mov [ rsp + 0x2a0 ], rbp; spilling x124 to mem
movzx rbp, byte [ rsp + 0x240 ]; load byte memx142 to register64
mov byte [ rsp + 0x2a8 ], r15b; spilling byte x312 to mem
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbp, r15; loading flag
adox r9, [ rsp + 0x200 ]
setc bpl; spill CF x75 to reg (rbp)
movzx r15, byte [ rsp + 0x210 ]; load byte memx114 to register64
clc;
mov byte [ rsp + 0x2b0 ], al; spilling byte x101 to mem
mov rax, -0x1 ; moving imm to reg
adcx r15, rax; loading flag
adcx r12, r11
seto r15b; spill OF x144 to reg (r15)
movzx r11, byte [ rsp + 0x228 ]; load byte memx157 to register64
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rax, -0x1 ; moving imm to reg
adox r11, rax; loading flag
adox r12, r9
mov r11, rdx; preserving value of x105 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r9, rax, r13; x170, x169<- x2 * arg1[4]
seto dl; spill OF x159 to reg (rdx)
mov [ rsp + 0x2b8 ], r9; spilling x170 to mem
movzx r9, byte [ rsp + 0x238 ]; load byte memx184 to register64
mov byte [ rsp + 0x2c0 ], r15b; spilling byte x144 to mem
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r9, r15; loading flag
adox rax, [ rsp + 0x218 ]
seto r9b; spill OF x186 to reg (r9)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, r15; loading flag
adox r12, rax
seto bl; spill OF x201 to reg (rbx)
movzx rax, byte [ rsp + 0x248 ]; load byte memx242 to register64
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
adox rax, r15; loading flag
adox r12, [ rsp + 0x68 ]
xchg rdx, r8; x3, swapping with x159, which is currently in rdx
mulx rax, r15, [ rsi + 0x18 ]; x259, x258<- x3 * arg1[3]
mov [ rsp + 0x2c8 ], rax; spilling x259 to mem
setc al; spill CF x116 to reg (rax)
clc;
mov byte [ rsp + 0x2d0 ], bl; spilling byte x201 to mem
mov rbx, -0x1 ; moving imm to reg
movzx r10, r10b
adcx r10, rbx; loading flag
adcx r15, [ rsp + 0x230 ]
seto r10b; spill OF x244 to reg (r10)
movzx rbx, byte [ rsp + 0x268 ]; load byte memx284 to register64
mov byte [ rsp + 0x2d8 ], r8b; spilling byte x159 to mem
mov r8, -0x1 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r8, -0x1 ; moving imm to reg
adox rbx, r8; loading flag
adox r12, r15
mov rbx, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, rbx; 0xfdc1767ae2ffffff, swapping with x3, which is currently in rdx
mulx r15, r8, rcx; x302, x301<- x279 * 0xfdc1767ae2ffffff
setc dl; spill CF x271 to reg (rdx)
mov [ rsp + 0x2e0 ], r15; spilling x302 to mem
movzx r15, byte [ rsp + 0x2a8 ]; load byte memx312 to register64
clc;
mov byte [ rsp + 0x2e8 ], r10b; spilling byte x244 to mem
mov r10, -0x1 ; moving imm to reg
adcx r15, r10; loading flag
adcx r8, [ rsp + 0x258 ]
movzx r15, byte [ rsp + 0x290 ]; x34, copying x33 here, cause x33 is needed in a reg for other than x34, namely all: , x34, size: 1
mov r10, [ rsp + 0x250 ]; load m64 x9 to register64
lea r15, [ r15 + r10 ]; r8/64 + m8
setc r10b; spill CF x314 to reg (r10)
mov byte [ rsp + 0x2f0 ], dl; spilling byte x271 to mem
movzx rdx, byte [ rsp + 0x280 ]; load byte memx327 to register64
clc;
mov byte [ rsp + 0x2f8 ], r9b; spilling byte x186 to mem
mov r9, -0x1 ; moving imm to reg
adcx rdx, r9; loading flag
adcx r12, r8
movzx rdx, byte [ rsp + 0x298 ]; x61, copying x60 here, cause x60 is needed in a reg for other than x61, namely all: , x61, size: 1
mov r8, [ rsp + 0x278 ]; load m64 x36 to register64
lea rdx, [ rdx + r8 ]; r8/64 + m8
seto r8b; spill OF x286 to reg (r8)
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, r9; loading flag
adox r15, rdx
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mulx r14, rbp, r14; x79, x78<- x1 * arg1[6]
seto dl; spill OF x77 to reg (rdx)
movzx r9, byte [ rsp + 0x2b0 ]; load byte memx101 to register64
mov [ rsp + 0x300 ], r12; spilling x328 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r9, r12; loading flag
adox rbp, [ rsp + 0x288 ]
seto r9b; spill OF x103 to reg (r9)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
movzx rax, al
adox rax, r12; loading flag
adox r15, rbp
mov al, dl; preserving value of x77 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx rbp, r12, r13; x168, x167<- x2 * arg1[5]
mov rdx, 0x2341f27177344 ; moving imm to reg
mov [ rsp + 0x308 ], rbp; spilling x168 to mem
mulx r11, rbp, r11; x122, x121<- x105 * 0x2341f27177344
setc dl; spill CF x329 to reg (rdx)
mov byte [ rsp + 0x310 ], al; spilling byte x77 to mem
movzx rax, byte [ rsp + 0x2c0 ]; load byte memx144 to register64
clc;
mov [ rsp + 0x318 ], r11; spilling x122 to mem
mov r11, -0x1 ; moving imm to reg
adcx rax, r11; loading flag
adcx rbp, [ rsp + 0x2a0 ]
setc al; spill CF x146 to reg (rax)
movzx r11, byte [ rsp + 0x2f8 ]; load byte memx186 to register64
clc;
mov [ rsp + 0x320 ], r14; spilling x79 to mem
mov r14, -0x1 ; moving imm to reg
adcx r11, r14; loading flag
adcx r12, [ rsp + 0x2b8 ]
setc r11b; spill CF x188 to reg (r11)
movzx r14, byte [ rsp + 0x2d8 ]; load byte memx159 to register64
clc;
mov byte [ rsp + 0x328 ], al; spilling byte x146 to mem
mov rax, -0x1 ; moving imm to reg
adcx r14, rax; loading flag
adcx r15, rbp
seto r14b; spill OF x118 to reg (r14)
movzx rbp, byte [ rsp + 0x2d0 ]; load byte memx201 to register64
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rax, -0x1 ; moving imm to reg
adox rbp, rax; loading flag
adox r15, r12
seto bpl; spill OF x203 to reg (rbp)
movzx r12, byte [ rsp + 0x2e8 ]; load byte memx244 to register64
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rax, -0x1 ; moving imm to reg
adox r12, rax; loading flag
adox r15, [ rsp + 0x70 ]
xchg rdx, rbx; x3, swapping with x329, which is currently in rdx
mulx r12, rax, [ rsi + 0x20 ]; x257, x256<- x3 * arg1[4]
mov [ rsp + 0x330 ], r12; spilling x257 to mem
setc r12b; spill CF x161 to reg (r12)
mov byte [ rsp + 0x338 ], bpl; spilling byte x203 to mem
movzx rbp, byte [ rsp + 0x2f0 ]; load byte memx271 to register64
clc;
mov byte [ rsp + 0x340 ], r11b; spilling byte x188 to mem
mov r11, -0x1 ; moving imm to reg
adcx rbp, r11; loading flag
adcx rax, [ rsp + 0x2c8 ]
setc bpl; spill CF x273 to reg (rbp)
clc;
movzx r8, r8b
adcx r8, r11; loading flag
adcx r15, rax
mov r8, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, r8; 0x7bc65c783158aea3, swapping with x3, which is currently in rdx
mulx rax, r11, rcx; x300, x299<- x279 * 0x7bc65c783158aea3
setc dl; spill CF x288 to reg (rdx)
clc;
mov [ rsp + 0x348 ], rax; spilling x300 to mem
mov rax, -0x1 ; moving imm to reg
movzx r10, r10b
adcx r10, rax; loading flag
adcx r11, [ rsp + 0x2e0 ]
seto r10b; spill OF x246 to reg (r10)
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rax, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, rax; loading flag
adox r15, r11
movzx rbx, r9b; x104, copying x103 here, cause x103 is needed in a reg for other than x104, namely all: , x104, size: 1
mov r11, [ rsp + 0x320 ]; load m64 x79 to register64
lea rbx, [ rbx + r11 ]; r8/64 + m8
movzx r11, byte [ rsp + 0x328 ]; x147, copying x146 here, cause x146 is needed in a reg for other than x147, namely all: , x147, size: 1
mov r9, [ rsp + 0x318 ]; load m64 x122 to register64
lea r11, [ r11 + r9 ]; r8/64 + m8
setc r9b; spill CF x316 to reg (r9)
clc;
mov [ rsp + 0x350 ], r15; spilling x330 to mem
movzx r15, byte [ rsp + 0x310 ]; load byte memx77 to register64
movzx r14, r14b
adcx r14, rax; loading flag
adcx rbx, r15
seto r15b; spill OF x331 to reg (r15)
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, r14; loading flag
adox rbx, r11
mov r12b, dl; preserving value of x288 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mulx r13, r11, r13; x166, x165<- x2 * arg1[6]
setc dl; spill CF x120 to reg (rdx)
movzx rax, byte [ rsp + 0x340 ]; load byte memx188 to register64
clc;
adcx rax, r14; loading flag
adcx r11, [ rsp + 0x308 ]
seto al; spill OF x163 to reg (rax)
movzx r14, byte [ rsp + 0x338 ]; load byte memx203 to register64
mov [ rsp + 0x358 ], r13; spilling x166 to mem
mov r13, -0x1 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r13, -0x1 ; moving imm to reg
adox r14, r13; loading flag
adox rbx, r11
setc r14b; spill CF x190 to reg (r14)
clc;
movzx r10, r10b
adcx r10, r13; loading flag
adcx rbx, [ rsp + 0x80 ]
xchg rdx, r8; x3, swapping with x120, which is currently in rdx
mulx r10, r11, [ rsi + 0x28 ]; x255, x254<- x3 * arg1[5]
seto r13b; spill OF x205 to reg (r13)
mov [ rsp + 0x360 ], r10; spilling x255 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbp, bpl
adox rbp, r10; loading flag
adox r11, [ rsp + 0x330 ]
seto bpl; spill OF x275 to reg (rbp)
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r10, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, r10; loading flag
adox rbx, r11
mov r12, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, r12; 0x6cfc5fd681c52056, swapping with x3, which is currently in rdx
mulx r11, r10, rcx; x298, x297<- x279 * 0x6cfc5fd681c52056
setc dl; spill CF x248 to reg (rdx)
clc;
mov [ rsp + 0x368 ], r11; spilling x298 to mem
mov r11, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, r11; loading flag
adcx r10, [ rsp + 0x348 ]
seto r9b; spill OF x290 to reg (r9)
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r11, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, r11; loading flag
adox rbx, r10
movzx r15, al; x164, copying x163 here, cause x163 is needed in a reg for other than x164, namely all: , x164, size: 1
movzx r8, r8b
lea r15, [ r15 + r8 ]
movzx r8, r14b; x191, copying x190 here, cause x190 is needed in a reg for other than x191, namely all: , x191, size: 1
mov rax, [ rsp + 0x358 ]; load m64 x166 to register64
lea r8, [ r8 + rax ]; r8/64 + m8
setc al; spill CF x318 to reg (rax)
clc;
movzx r13, r13b
adcx r13, r11; loading flag
adcx r15, r8
setc r14b; spill CF x207 to reg (r14)
clc;
movzx rdx, dl
adcx rdx, r11; loading flag
adcx r15, [ rsp + 0x78 ]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mulx r12, r13, r12; x253, x252<- x3 * arg1[6]
seto dl; spill OF x333 to reg (rdx)
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r10, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, r10; loading flag
adox r13, [ rsp + 0x360 ]
setc bpl; spill CF x250 to reg (rbp)
clc;
movzx r9, r9b
adcx r9, r10; loading flag
adcx r15, r13
mov r9, 0x2341f27177344 ; moving imm to reg
xchg rdx, rcx; x279, swapping with x333, which is currently in rdx
mulx rdx, r8, r9; x296, x295<- x279 * 0x2341f27177344
setc r13b; spill CF x292 to reg (r13)
clc;
movzx rax, al
adcx rax, r10; loading flag
adcx r8, [ rsp + 0x368 ]
movzx rax, bpl; x251, copying x250 here, cause x250 is needed in a reg for other than x251, namely all: , x251, size: 1
movzx r14, r14b
lea rax, [ rax + r14 ]
setc r14b; spill CF x320 to reg (r14)
clc;
movzx rcx, cl
adcx rcx, r10; loading flag
adcx r15, r8
adox r12, r11
dec r11; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx r13, r13b
adox r13, r11; loading flag
adox rax, r12
movzx r10, r14b; x321, copying x320 here, cause x320 is needed in a reg for other than x321, namely all: , x321, size: 1
lea r10, [ r10 + rdx ]
adcx r10, rax
mov rcx, [ rsi + 0x20 ]; load m64 x4 to register64
seto bpl; spill OF x338 to reg (rbp)
adc bpl, 0x0
movzx rbp, bpl
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r13, r8, rcx; x352, x351<- x4 * arg1[0]
adox r8, [ rsp + 0x1c8 ]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mulx r14, r12, r8; x395, x394<- x366 * 0xffffffffffffffff
adcx r12, r8
mov r12, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx rax, r11, rcx; x350, x349<- x4 * arg1[1]
mov rdx, r12; 0xffffffffffffffff to rdx
mulx r12, r9, r8; x393, x392<- x366 * 0xffffffffffffffff
setc dl; spill CF x410 to reg (rdx)
clc;
adcx r11, r13
mov r13, [ rsp + 0x270 ]; x368, copying x326 here, cause x326 is needed in a reg for other than x368, namely all: , x368--x369, size: 1
adox r13, r11
setc r11b; spill CF x354 to reg (r11)
clc;
adcx r9, r14
seto r14b; spill OF x369 to reg (r14)
mov byte [ rsp + 0x370 ], bpl; spilling byte x338 to mem
mov rbp, -0x1 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
movzx rdx, dl
adox rdx, rbp; loading flag
adox r13, r9
mov rdx, rcx; x4 to rdx
mulx rcx, r9, [ rsi + 0x10 ]; x348, x347<- x4 * arg1[2]
mov rbp, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbp; 0xffffffffffffffff, swapping with x4, which is currently in rdx
mov [ rsp + 0x378 ], r13; spilling x411 to mem
mov [ rsp + 0x380 ], r10; spilling x336 to mem
mulx r13, r10, r8; x391, x390<- x366 * 0xffffffffffffffff
setc dl; spill CF x397 to reg (rdx)
clc;
mov [ rsp + 0x388 ], r15; spilling x334 to mem
mov r15, -0x1 ; moving imm to reg
movzx r11, r11b
adcx r11, r15; loading flag
adcx rax, r9
setc r11b; spill CF x356 to reg (r11)
clc;
movzx r14, r14b
adcx r14, r15; loading flag
adcx rax, [ rsp + 0x300 ]
setc r14b; spill CF x371 to reg (r14)
clc;
movzx rdx, dl
adcx rdx, r15; loading flag
adcx r12, r10
adox r12, rax
mov rdx, rbp; x4 to rdx
mulx rbp, r9, [ rsi + 0x18 ]; x346, x345<- x4 * arg1[3]
setc r10b; spill CF x399 to reg (r10)
clc;
movzx r11, r11b
adcx r11, r15; loading flag
adcx rcx, r9
mov r11, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, r8; x366, swapping with x4, which is currently in rdx
mulx rax, r9, r11; x389, x388<- x366 * 0xfdc1767ae2ffffff
setc r15b; spill CF x358 to reg (r15)
clc;
mov r11, -0x1 ; moving imm to reg
movzx r14, r14b
adcx r14, r11; loading flag
adcx rcx, [ rsp + 0x350 ]
setc r14b; spill CF x373 to reg (r14)
clc;
movzx r10, r10b
adcx r10, r11; loading flag
adcx r13, r9
adox r13, rcx
mov r10, rdx; preserving value of x366 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r9, rcx, r8; x344, x343<- x4 * arg1[4]
seto dl; spill OF x416 to reg (rdx)
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r11, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, r11; loading flag
adox rbp, rcx
seto r15b; spill OF x360 to reg (r15)
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rcx, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, rcx; loading flag
adox rbx, rbp
mov r14, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, r14; 0x7bc65c783158aea3, swapping with x416, which is currently in rdx
mulx rbp, r11, r10; x387, x386<- x366 * 0x7bc65c783158aea3
adcx r11, rax
setc al; spill CF x403 to reg (rax)
clc;
movzx r14, r14b
adcx r14, rcx; loading flag
adcx rbx, r11
mov r14, rdx; preserving value of 0x7bc65c783158aea3 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx r11, rcx, r8; x342, x341<- x4 * arg1[5]
seto dl; spill OF x375 to reg (rdx)
mov r14, -0x1 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r14, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, r14; loading flag
adox r9, rcx
setc r15b; spill CF x418 to reg (r15)
clc;
movzx rdx, dl
adcx rdx, r14; loading flag
adcx r9, [ rsp + 0x388 ]
mov rdx, 0x6cfc5fd681c52056 ; moving imm to reg
mulx rcx, r14, r10; x385, x384<- x366 * 0x6cfc5fd681c52056
xchg rdx, r8; x4, swapping with 0x6cfc5fd681c52056, which is currently in rdx
mulx rdx, r8, [ rsi + 0x30 ]; x340, x339<- x4 * arg1[6]
mov [ rsp + 0x390 ], rbx; spilling x417 to mem
setc bl; spill CF x377 to reg (rbx)
clc;
mov [ rsp + 0x398 ], r13; spilling x415 to mem
mov r13, -0x1 ; moving imm to reg
movzx rax, al
adcx rax, r13; loading flag
adcx rbp, r14
setc al; spill CF x405 to reg (rax)
clc;
movzx r15, r15b
adcx r15, r13; loading flag
adcx r9, rbp
mov r15, 0x2341f27177344 ; moving imm to reg
xchg rdx, r10; x366, swapping with x340, which is currently in rdx
mulx rdx, r14, r15; x383, x382<- x366 * 0x2341f27177344
adox r8, r11
setc r11b; spill CF x420 to reg (r11)
clc;
movzx rbx, bl
adcx rbx, r13; loading flag
adcx r8, [ rsp + 0x380 ]
seto bl; spill OF x364 to reg (rbx)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx rax, al
adox rax, rbp; loading flag
adox rcx, r14
seto al; spill OF x407 to reg (rax)
inc rbp; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov r13, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, r13; loading flag
adox r8, rcx
movzx r11, bl; x365, copying x364 here, cause x364 is needed in a reg for other than x365, namely all: , x365, size: 1
lea r11, [ r11 + r10 ]
movzx r10, byte [ rsp + 0x370 ]; x380, copying x338 here, cause x338 is needed in a reg for other than x380, namely all: , x380--x381, size: 1
adcx r10, r11
movzx r14, al; x408, copying x407 here, cause x407 is needed in a reg for other than x408, namely all: , x408, size: 1
lea r14, [ r14 + rdx ]
adox r14, r10
seto dl; spill OF x425 to reg (rdx)
adc dl, 0x0
movzx rdx, dl
mov rbx, [ rsi + 0x28 ]; load m64 x5 to register64
mov cl, dl; preserving value of x425 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx rax, r11, rbx; x439, x438<- x5 * arg1[0]
adox r11, [ rsp + 0x378 ]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mulx r10, rbp, r11; x482, x481<- x453 * 0xffffffffffffffff
mulx r13, r15, r11; x480, x479<- x453 * 0xffffffffffffffff
mov byte [ rsp + 0x3a0 ], cl; spilling byte x425 to mem
mov [ rsp + 0x3a8 ], r14; spilling x423 to mem
mulx rcx, r14, r11; x478, x477<- x453 * 0xffffffffffffffff
adcx r15, r10
adcx r14, r13
mov r10, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, r11; x453, swapping with 0xffffffffffffffff, which is currently in rdx
mulx r13, r11, r10; x476, x475<- x453 * 0xfdc1767ae2ffffff
adcx r11, rcx
mov rcx, 0x7bc65c783158aea3 ; moving imm to reg
mov [ rsp + 0x3b0 ], r8; spilling x421 to mem
mulx r10, r8, rcx; x474, x473<- x453 * 0x7bc65c783158aea3
adcx r8, r13
mov r13, 0x6cfc5fd681c52056 ; moving imm to reg
mov [ rsp + 0x3b8 ], r8; spilling x489 to mem
mulx rcx, r8, r13; x472, x471<- x453 * 0x6cfc5fd681c52056
adcx r8, r10
mov r10, 0x2341f27177344 ; moving imm to reg
mov [ rsp + 0x3c0 ], r8; spilling x491 to mem
mulx r13, r8, r10; x470, x469<- x453 * 0x2341f27177344
adcx r8, rcx
mov rcx, 0x0 ; moving imm to reg
adcx r13, rcx
clc;
adcx rbp, rdx
mov rdx, rbx; x5 to rdx
mulx rbx, rbp, [ rsi + 0x8 ]; x437, x436<- x5 * arg1[1]
seto r10b; spill OF x454 to reg (r10)
mov [ rsp + 0x3c8 ], r13; spilling x495 to mem
mov r13, -0x3 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbp, rax
setc al; spill CF x497 to reg (rax)
clc;
mov rcx, -0x1 ; moving imm to reg
movzx r10, r10b
adcx r10, rcx; loading flag
adcx r12, rbp
mulx r10, rbp, [ rsi + 0x10 ]; x435, x434<- x5 * arg1[2]
adox rbp, rbx
seto bl; spill OF x443 to reg (rbx)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rcx, -0x1 ; moving imm to reg
movzx rax, al
adox rax, rcx; loading flag
adox r12, r15
mov r15, [ rsp + 0x398 ]; x457, copying x415 here, cause x415 is needed in a reg for other than x457, namely all: , x457--x458, size: 1
adcx r15, rbp
mulx rax, rbp, [ rsi + 0x18 ]; x433, x432<- x5 * arg1[3]
adox r14, r15
seto r15b; spill OF x501 to reg (r15)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rcx, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, rcx; loading flag
adox r10, rbp
mov rbx, [ rsp + 0x390 ]; x459, copying x417 here, cause x417 is needed in a reg for other than x459, namely all: , x459--x460, size: 1
adcx rbx, r10
mulx rbp, r10, [ rsi + 0x20 ]; x431, x430<- x5 * arg1[4]
adox r10, rax
adcx r10, r9
setc r9b; spill CF x462 to reg (r9)
clc;
movzx r15, r15b
adcx r15, rcx; loading flag
adcx rbx, r11
mov r11, [ rsp + 0x3b8 ]; x504, copying x489 here, cause x489 is needed in a reg for other than x504, namely all: , x504--x505, size: 1
adcx r11, r10
mulx rax, r15, [ rsi + 0x28 ]; x429, x428<- x5 * arg1[5]
adox r15, rbp
seto bpl; spill OF x449 to reg (rbp)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r10, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, r10; loading flag
adox r15, [ rsp + 0x3b0 ]
mov r9, [ rsp + 0x3c0 ]; x506, copying x491 here, cause x491 is needed in a reg for other than x506, namely all: , x506--x507, size: 1
adcx r9, r15
mulx rdx, r15, [ rsi + 0x30 ]; x427, x426<- x5 * arg1[6]
setc cl; spill CF x507 to reg (rcx)
clc;
movzx rbp, bpl
adcx rbp, r10; loading flag
adcx rax, r15
mov rbp, [ rsp + 0x3a8 ]; x465, copying x423 here, cause x423 is needed in a reg for other than x465, namely all: , x465--x466, size: 1
adox rbp, rax
setc r15b; spill CF x451 to reg (r15)
clc;
movzx rcx, cl
adcx rcx, r10; loading flag
adcx rbp, r8
movzx r8, r15b; x452, copying x451 here, cause x451 is needed in a reg for other than x452, namely all: , x452, size: 1
lea r8, [ r8 + rdx ]
movzx rcx, byte [ rsp + 0x3a0 ]; x467, copying x425 here, cause x425 is needed in a reg for other than x467, namely all: , x467--x468, size: 1
adox rcx, r8
mov rdx, [ rsp + 0x3c8 ]; x510, copying x495 here, cause x495 is needed in a reg for other than x510, namely all: , x510--x511, size: 1
adcx rdx, rcx
mov rax, [ rsi + 0x30 ]; load m64 x6 to register64
seto r15b; spill OF x512 to reg (r15)
adc r15b, 0x0
movzx r15, r15b
xchg rdx, rax; x6, swapping with x510, which is currently in rdx
mulx r8, rcx, [ rsi + 0x0 ]; x526, x525<- x6 * arg1[0]
adox rcx, r12
mov r12, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rcx; x540, swapping with x6, which is currently in rdx
mulx r10, r13, r12; x569, x568<- x540 * 0xffffffffffffffff
adcx r13, rdx
xchg rdx, rcx; x6, swapping with x540, which is currently in rdx
mulx r13, r12, [ rsi + 0x8 ]; x524, x523<- x6 * arg1[1]
mov byte [ rsp + 0x3d0 ], r15b; spilling byte x512 to mem
setc r15b; spill CF x584 to reg (r15)
clc;
adcx r12, r8
mov r8, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r8; 0xffffffffffffffff, swapping with x6, which is currently in rdx
mov [ rsp + 0x3d8 ], rax; spilling x510 to mem
mov [ rsp + 0x3e0 ], rbp; spilling x508 to mem
mulx rax, rbp, rcx; x567, x566<- x540 * 0xffffffffffffffff
adox r12, r14
seto r14b; spill OF x543 to reg (r14)
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, r10
setc r10b; spill CF x528 to reg (r10)
clc;
movzx r15, r15b
adcx r15, rdx; loading flag
adcx r12, rbp
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r15, rbp, r8; x522, x521<- x6 * arg1[2]
setc dl; spill CF x586 to reg (rdx)
clc;
mov [ rsp + 0x3e8 ], r12; spilling x585 to mem
mov r12, -0x1 ; moving imm to reg
movzx r10, r10b
adcx r10, r12; loading flag
adcx r13, rbp
mov r10, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rcx; x540, swapping with x586, which is currently in rdx
mulx rbp, r12, r10; x565, x564<- x540 * 0xffffffffffffffff
adox r12, rax
seto al; spill OF x573 to reg (rax)
mov r10, -0x1 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r10, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, r10; loading flag
adox rbx, r13
setc r14b; spill CF x530 to reg (r14)
clc;
movzx rcx, cl
adcx rcx, r10; loading flag
adcx rbx, r12
xchg rdx, r8; x6, swapping with x540, which is currently in rdx
mulx rcx, r13, [ rsi + 0x18 ]; x520, x519<- x6 * arg1[3]
setc r12b; spill CF x588 to reg (r12)
clc;
movzx r14, r14b
adcx r14, r10; loading flag
adcx r15, r13
adox r15, r11
mov r11, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, r11; 0xfdc1767ae2ffffff, swapping with x6, which is currently in rdx
mulx r14, r13, r8; x563, x562<- x540 * 0xfdc1767ae2ffffff
seto r10b; spill OF x547 to reg (r10)
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rax, al
adox rax, rdx; loading flag
adox rbp, r13
seto al; spill OF x575 to reg (rax)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, r13; loading flag
adox r15, rbp
mov r12, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx rbp, r13, r11; x518, x517<- x6 * arg1[4]
adcx r13, rcx
seto dl; spill OF x590 to reg (rdx)
dec r12; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r10, r10b
adox r10, r12; loading flag
adox r9, r13
mov rcx, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, rcx; 0x7bc65c783158aea3, swapping with x590, which is currently in rdx
mulx r10, r13, r8; x561, x560<- x540 * 0x7bc65c783158aea3
seto r12b; spill OF x549 to reg (r12)
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
movzx rax, al
adox rax, rdx; loading flag
adox r14, r13
seto al; spill OF x577 to reg (rax)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r13; loading flag
adox r9, r14
mov rcx, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx r14, r13, r11; x516, x515<- x6 * arg1[5]
mov rdx, 0x6cfc5fd681c52056 ; moving imm to reg
mov [ rsp + 0x3f0 ], r9; spilling x591 to mem
mulx rcx, r9, r8; x559, x558<- x540 * 0x6cfc5fd681c52056
adcx r13, rbp
setc bpl; spill CF x536 to reg (rbp)
clc;
mov rdx, -0x1 ; moving imm to reg
movzx rax, al
adcx rax, rdx; loading flag
adcx r10, r9
mov rdx, r11; x6 to rdx
mulx rdx, r11, [ rsi + 0x30 ]; x514, x513<- x6 * arg1[6]
setc al; spill CF x579 to reg (rax)
clc;
mov r9, -0x1 ; moving imm to reg
movzx r12, r12b
adcx r12, r9; loading flag
adcx r13, [ rsp + 0x3e0 ]
adox r10, r13
setc r12b; spill CF x551 to reg (r12)
clc;
movzx rbp, bpl
adcx rbp, r9; loading flag
adcx r14, r11
setc bpl; spill CF x538 to reg (rbp)
clc;
movzx r12, r12b
adcx r12, r9; loading flag
adcx r14, [ rsp + 0x3d8 ]
mov r11, 0x2341f27177344 ; moving imm to reg
xchg rdx, r11; 0x2341f27177344, swapping with x514, which is currently in rdx
mulx r8, r13, r8; x557, x556<- x540 * 0x2341f27177344
movzx r12, bpl; x539, copying x538 here, cause x538 is needed in a reg for other than x539, namely all: , x539, size: 1
lea r12, [ r12 + r11 ]
setc r11b; spill CF x553 to reg (r11)
clc;
movzx rax, al
adcx rax, r9; loading flag
adcx rcx, r13
adox rcx, r14
mov rax, 0x0 ; moving imm to reg
adcx r8, rax
clc;
movzx rbp, byte [ rsp + 0x3d0 ]; load byte memx512 to register64
movzx r11, r11b
adcx r11, r9; loading flag
adcx r12, rbp
adox r8, r12
setc bpl; spill CF x555 to reg (rbp)
seto r14b; spill OF x598 to reg (r14)
mov r11, [ rsp + 0x3e8 ]; x600, copying x585 here, cause x585 is needed in a reg for other than x600, namely all: , x616, x600--x601, size: 2
mov r13, 0xffffffffffffffff ; moving imm to reg
sub r11, r13
movzx r12, r14b; x599, copying x598 here, cause x598 is needed in a reg for other than x599, namely all: , x599, size: 1
movzx rbp, bpl
lea r12, [ r12 + rbp ]
mov rbp, rbx; x602, copying x587 here, cause x587 is needed in a reg for other than x602, namely all: , x602--x603, x617, size: 2
sbb rbp, r13
mov r14, r15; x604, copying x589 here, cause x589 is needed in a reg for other than x604, namely all: , x618, x604--x605, size: 2
sbb r14, r13
mov rax, [ rsp + 0x3f0 ]; x606, copying x591 here, cause x591 is needed in a reg for other than x606, namely all: , x619, x606--x607, size: 2
mov r9, 0xfdc1767ae2ffffff ; moving imm to reg
sbb rax, r9
mov r13, r10; x608, copying x593 here, cause x593 is needed in a reg for other than x608, namely all: , x608--x609, x620, size: 2
mov rdx, 0x7bc65c783158aea3 ; moving imm to reg
sbb r13, rdx
mov rdx, rcx; x610, copying x595 here, cause x595 is needed in a reg for other than x610, namely all: , x610--x611, x621, size: 2
mov r9, 0x6cfc5fd681c52056 ; moving imm to reg
sbb rdx, r9
mov r9, r8; x612, copying x597 here, cause x597 is needed in a reg for other than x612, namely all: , x622, x612--x613, size: 2
mov [ rsp + 0x3f8 ], r11; spilling x600 to mem
mov r11, 0x2341f27177344 ; moving imm to reg
sbb r9, r11
sbb r12, 0x00000000
cmovc r13, r10; if CF, x620<- x593 (nzVar)
cmovc rbp, rbx; if CF, x617<- x587 (nzVar)
mov r12, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r12 + 0x20 ], r13; out1[4] = x620
mov [ r12 + 0x8 ], rbp; out1[1] = x617
cmovc r14, r15; if CF, x618<- x589 (nzVar)
cmovc r9, r8; if CF, x622<- x597 (nzVar)
cmovc rdx, rcx; if CF, x621<- x595 (nzVar)
mov [ r12 + 0x30 ], r9; out1[6] = x622
cmovc rax, [ rsp + 0x3f0 ]; if CF, x619<- x591 (nzVar)
mov [ r12 + 0x28 ], rdx; out1[5] = x621
mov [ r12 + 0x18 ], rax; out1[3] = x619
mov rbx, [ rsp + 0x3f8 ]; x616, copying x600 here, cause x600 is needed in a reg for other than x616, namely all: , x616, size: 1
cmovc rbx, [ rsp + 0x3e8 ]; if CF, x616<- x585 (nzVar)
mov [ r12 + 0x0 ], rbx; out1[0] = x616
mov [ r12 + 0x10 ], r14; out1[2] = x618
mov rbx, [ rsp + 0x400 ]; restoring from stack
mov rbp, [ rsp + 0x408 ]; restoring from stack
mov r12, [ rsp + 0x410 ]; restoring from stack
mov r13, [ rsp + 0x418 ]; restoring from stack
mov r14, [ rsp + 0x420 ]; restoring from stack
mov r15, [ rsp + 0x428 ]; restoring from stack
add rsp, 0x430 
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; clocked at 2200 MHz
; first cyclecount 329.8, best 316.0740740740741, lastGood 321.1111111111111
; seed 1206177160463392 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 45638 ms / 500 runs=> 91.276ms/run
; Time spent for assembling and measureing (initial batch_size=27, initial num_batches=101): 1223 ms
; Ratio (time for assembling + measure)/(total runtime for 500runs): 0.02679784390201148
; number reverted permutation/ tried permutation: 130 / 244 =53.279%
; number reverted decision/ tried decision: 128 / 257 =49.805%