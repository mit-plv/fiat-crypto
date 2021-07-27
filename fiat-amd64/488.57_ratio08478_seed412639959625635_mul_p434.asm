SECTION .text
	GLOBAL mul_p434
mul_p434:
sub rsp, 0x620 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x5f0 ], rbx; saving to stack
mov [ rsp + 0x5f8 ], rbp; saving to stack
mov [ rsp + 0x600 ], r12; saving to stack
mov [ rsp + 0x608 ], r13; saving to stack
mov [ rsp + 0x610 ], r14; saving to stack
mov [ rsp + 0x618 ], r15; saving to stack
mov rax, [ rsi + 0x10 ]; load m64 x2 to register64
mov r10, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x0 ]; saving arg2[0] in rdx.
mulx r11, rbx, rax; x178, x177<- x2 * arg2[0]
mov rdx, [ r10 + 0x8 ]; arg2[1] to rdx
mulx rbp, r12, rax; x176, x175<- x2 * arg2[1]
test al, al
adox r12, r11
mov rdx, rax; x2 to rdx
mulx rax, r13, [ r10 + 0x10 ]; x174, x173<- x2 * arg2[2]
mulx r14, r15, [ r10 + 0x18 ]; x172, x171<- x2 * arg2[3]
adox r13, rbp
adox r15, rax
mulx rcx, r8, [ r10 + 0x20 ]; x170, x169<- x2 * arg2[4]
adox r8, r14
mulx r9, r11, [ r10 + 0x28 ]; x168, x167<- x2 * arg2[5]
mulx rdx, rbp, [ r10 + 0x30 ]; x166, x165<- x2 * arg2[6]
adox r11, rcx
adox rbp, r9
mov rax, [ rsi + 0x0 ]; load m64 x7 to register64
mov r14, 0x0 ; moving imm to reg
adox rdx, r14
xchg rdx, rax; x7, swapping with x191, which is currently in rdx
mulx rcx, r9, [ r10 + 0x0 ]; x21, x20<- x7 * arg2[0]
mov r14, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r9; x20, swapping with x7, which is currently in rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov [ rsp + 0x8 ], rax; spilling x191 to mem
mulx rdi, rax, r14; x48, x47<- x20 * 0xffffffffffffffff
xchg rdx, r9; x7, swapping with x20, which is currently in rdx
mov [ rsp + 0x10 ], rbp; spilling x189 to mem
mulx r14, rbp, [ r10 + 0x8 ]; x19, x18<- x7 * arg2[1]
adcx rax, r9
mov rax, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r9; x20, swapping with x7, which is currently in rdx
mov [ rsp + 0x18 ], r11; spilling x187 to mem
mov [ rsp + 0x20 ], r8; spilling x185 to mem
mulx r11, r8, rax; x46, x45<- x20 * 0xffffffffffffffff
mov rax, -0x2 ; moving imm to reg
inc rax; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, rcx
seto cl; spill OF x23 to reg (rcx)
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r8, rdi
adcx r8, rbp
mov rdi, [ rsi + 0x8 ]; load m64 x1 to register64
mov rbp, rdx; preserving value of x20 into a new reg
mov rdx, [ r10 + 0x0 ]; saving arg2[0] in rdx.
mov [ rsp + 0x28 ], r15; spilling x183 to mem
mulx rax, r15, rdi; x91, x90<- x1 * arg2[0]
mov [ rsp + 0x30 ], r13; spilling x181 to mem
setc r13b; spill CF x65 to reg (r13)
clc;
adcx r15, r8
mov r8, 0xffffffffffffffff ; moving imm to reg
mov rdx, r15; x105 to rdx
mov [ rsp + 0x38 ], r12; spilling x179 to mem
mulx r15, r12, r8; x134, x133<- x105 * 0xffffffffffffffff
setc r8b; spill CF x106 to reg (r8)
clc;
adcx r12, rdx
mov r12, rdx; preserving value of x105 into a new reg
mov rdx, [ r10 + 0x10 ]; saving arg2[2] in rdx.
mov [ rsp + 0x40 ], rbx; spilling x177 to mem
mov [ rsp + 0x48 ], r15; spilling x134 to mem
mulx rbx, r15, r9; x17, x16<- x7 * arg2[2]
mov [ rsp + 0x50 ], rbx; spilling x17 to mem
setc bl; spill CF x149 to reg (rbx)
clc;
mov byte [ rsp + 0x58 ], r8b; spilling byte x106 to mem
mov r8, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, r8; loading flag
adcx r14, r15
mov rcx, 0xffffffffffffffff ; moving imm to reg
mov rdx, rbp; x20 to rdx
mulx rbp, r15, rcx; x44, x43<- x20 * 0xffffffffffffffff
adox r15, r11
seto r11b; spill OF x52 to reg (r11)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, r8; loading flag
adox r14, r15
xchg rdx, rdi; x1, swapping with x20, which is currently in rdx
mulx r13, r15, [ r10 + 0x8 ]; x89, x88<- x1 * arg2[1]
seto r8b; spill OF x67 to reg (r8)
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, rax
seto al; spill OF x93 to reg (rax)
movzx rcx, byte [ rsp + 0x58 ]; load byte memx106 to register64
mov [ rsp + 0x60 ], r13; spilling x89 to mem
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rcx, r13; loading flag
adox r14, r15
mov rcx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rcx; 0xffffffffffffffff, swapping with x1, which is currently in rdx
mulx r15, r13, r12; x132, x131<- x105 * 0xffffffffffffffff
seto dl; spill OF x108 to reg (rdx)
mov [ rsp + 0x68 ], r15; spilling x132 to mem
mov r15, -0x2 ; moving imm to reg
inc r15; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, [ rsp + 0x48 ]
seto r15b; spill OF x136 to reg (r15)
mov byte [ rsp + 0x70 ], dl; spilling byte x108 to mem
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, rdx; loading flag
adox r14, r13
seto bl; spill OF x151 to reg (rbx)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r14, [ rsp + 0x40 ]
mov r13, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r13; 0xffffffffffffffff, swapping with 0x0, which is currently in rdx
mov byte [ rsp + 0x78 ], bl; spilling byte x151 to mem
mulx r13, rbx, r14; x219, x218<- x192 * 0xffffffffffffffff
mov byte [ rsp + 0x80 ], r15b; spilling byte x136 to mem
mov byte [ rsp + 0x88 ], al; spilling byte x93 to mem
mulx r15, rax, r14; x221, x220<- x192 * 0xffffffffffffffff
mov byte [ rsp + 0x90 ], r8b; spilling byte x67 to mem
mov [ rsp + 0x98 ], rbp; spilling x44 to mem
mulx r8, rbp, r14; x217, x216<- x192 * 0xffffffffffffffff
setc dl; spill CF x25 to reg (rdx)
clc;
adcx rbx, r15
adcx rbp, r13
mov r13, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, r14; x192, swapping with x25, which is currently in rdx
mov [ rsp + 0xa0 ], rbp; spilling x224 to mem
mulx r15, rbp, r13; x215, x214<- x192 * 0xfdc1767ae2ffffff
mov r13, 0x7bc65c783158aea3 ; moving imm to reg
mov [ rsp + 0xa8 ], rbx; spilling x222 to mem
mov byte [ rsp + 0xb0 ], r11b; spilling byte x52 to mem
mulx rbx, r11, r13; x213, x212<- x192 * 0x7bc65c783158aea3
adcx rbp, r8
adcx r11, r15
mov r8, 0x2341f27177344 ; moving imm to reg
mulx r15, r13, r8; x209, x208<- x192 * 0x2341f27177344
mov r8, 0x6cfc5fd681c52056 ; moving imm to reg
mov [ rsp + 0xb8 ], r11; spilling x228 to mem
mov [ rsp + 0xc0 ], rbp; spilling x226 to mem
mulx r11, rbp, r8; x211, x210<- x192 * 0x6cfc5fd681c52056
adcx rbp, rbx
adcx r13, r11
mov rbx, [ rsi + 0x28 ]; load m64 x5 to register64
mov r11, 0x0 ; moving imm to reg
adcx r15, r11
xchg rdx, rbx; x5, swapping with x192, which is currently in rdx
mulx r11, r8, [ r10 + 0x0 ]; x439, x438<- x5 * arg2[0]
mov [ rsp + 0xc8 ], r8; spilling x438 to mem
mov [ rsp + 0xd0 ], r15; spilling x234 to mem
mulx r8, r15, [ r10 + 0x10 ]; x435, x434<- x5 * arg2[2]
mov [ rsp + 0xd8 ], r13; spilling x232 to mem
mov [ rsp + 0xe0 ], rbp; spilling x230 to mem
mulx r13, rbp, [ r10 + 0x8 ]; x437, x436<- x5 * arg2[1]
clc;
adcx rbp, r11
adcx r15, r13
mulx r11, r13, [ r10 + 0x18 ]; x433, x432<- x5 * arg2[3]
adcx r13, r8
mov [ rsp + 0xe8 ], r13; spilling x444 to mem
mulx r8, r13, [ r10 + 0x20 ]; x431, x430<- x5 * arg2[4]
mov [ rsp + 0xf0 ], r15; spilling x442 to mem
mov [ rsp + 0xf8 ], rbp; spilling x440 to mem
mulx r15, rbp, [ r10 + 0x28 ]; x429, x428<- x5 * arg2[5]
adcx r13, r11
adcx rbp, r8
mulx rdx, r11, [ r10 + 0x30 ]; x427, x426<- x5 * arg2[6]
adcx r11, r15
mov r8, 0x0 ; moving imm to reg
adcx rdx, r8
mov r15, [ rsi + 0x20 ]; load m64 x4 to register64
xchg rdx, r15; x4, swapping with x452, which is currently in rdx
mov [ rsp + 0x100 ], r15; spilling x452 to mem
mulx r8, r15, [ r10 + 0x8 ]; x350, x349<- x4 * arg2[1]
mov [ rsp + 0x108 ], r11; spilling x450 to mem
mov [ rsp + 0x110 ], rbp; spilling x448 to mem
mulx r11, rbp, [ r10 + 0x10 ]; x348, x347<- x4 * arg2[2]
mov [ rsp + 0x118 ], r13; spilling x446 to mem
mov byte [ rsp + 0x120 ], r14b; spilling byte x25 to mem
mulx r13, r14, [ r10 + 0x0 ]; x352, x351<- x4 * arg2[0]
clc;
adcx r15, r13
adcx rbp, r8
mulx r8, r13, [ r10 + 0x18 ]; x346, x345<- x4 * arg2[3]
adcx r13, r11
mov [ rsp + 0x128 ], r13; spilling x357 to mem
mulx r11, r13, [ r10 + 0x20 ]; x344, x343<- x4 * arg2[4]
adcx r13, r8
mov [ rsp + 0x130 ], r13; spilling x359 to mem
mulx r8, r13, [ r10 + 0x28 ]; x342, x341<- x4 * arg2[5]
mov [ rsp + 0x138 ], rbp; spilling x355 to mem
mulx rdx, rbp, [ r10 + 0x30 ]; x340, x339<- x4 * arg2[6]
adcx r13, r11
adcx rbp, r8
mov r11, 0x0 ; moving imm to reg
adcx rdx, r11
clc;
adcx rax, rbx
xchg rdx, r9; x7, swapping with x365, which is currently in rdx
mulx rax, rbx, [ r10 + 0x18 ]; x15, x14<- x7 * arg2[3]
setc r8b; spill CF x236 to reg (r8)
movzx r11, byte [ rsp + 0x120 ]; load byte memx25 to register64
clc;
mov [ rsp + 0x140 ], r9; spilling x365 to mem
mov r9, -0x1 ; moving imm to reg
adcx r11, r9; loading flag
adcx rbx, [ rsp + 0x50 ]
mov r11, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, rdi; x20, swapping with x7, which is currently in rdx
mov [ rsp + 0x148 ], rbp; spilling x363 to mem
mulx r9, rbp, r11; x42, x41<- x20 * 0xfdc1767ae2ffffff
seto r11b; spill OF x193 to reg (r11)
mov [ rsp + 0x150 ], r13; spilling x361 to mem
movzx r13, byte [ rsp + 0xb0 ]; load byte memx52 to register64
mov [ rsp + 0x158 ], r15; spilling x353 to mem
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r15, -0x1 ; moving imm to reg
adox r13, r15; loading flag
adox rbp, [ rsp + 0x98 ]
mov r13, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r12; x105, swapping with x20, which is currently in rdx
mov [ rsp + 0x160 ], r14; spilling x351 to mem
mulx r15, r14, r13; x130, x129<- x105 * 0xffffffffffffffff
seto r13b; spill OF x54 to reg (r13)
mov [ rsp + 0x168 ], r15; spilling x130 to mem
movzx r15, byte [ rsp + 0x90 ]; load byte memx67 to register64
mov [ rsp + 0x170 ], r9; spilling x42 to mem
mov r9, -0x1 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r9, -0x1 ; moving imm to reg
adox r15, r9; loading flag
adox rbx, rbp
xchg rdx, rcx; x1, swapping with x105, which is currently in rdx
mulx r15, rbp, [ r10 + 0x10 ]; x87, x86<- x1 * arg2[2]
setc r9b; spill CF x27 to reg (r9)
mov [ rsp + 0x178 ], r15; spilling x87 to mem
movzx r15, byte [ rsp + 0x88 ]; load byte memx93 to register64
clc;
mov byte [ rsp + 0x180 ], r13b; spilling byte x54 to mem
mov r13, -0x1 ; moving imm to reg
adcx r15, r13; loading flag
adcx rbp, [ rsp + 0x60 ]
setc r15b; spill CF x95 to reg (r15)
movzx r13, byte [ rsp + 0x70 ]; load byte memx108 to register64
clc;
mov [ rsp + 0x188 ], rax; spilling x15 to mem
mov rax, -0x1 ; moving imm to reg
adcx r13, rax; loading flag
adcx rbx, rbp
seto r13b; spill OF x69 to reg (r13)
movzx rbp, byte [ rsp + 0x80 ]; load byte memx136 to register64
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rax, -0x1 ; moving imm to reg
adox rbp, rax; loading flag
adox r14, [ rsp + 0x68 ]
seto bpl; spill OF x138 to reg (rbp)
movzx rax, byte [ rsp + 0x78 ]; load byte memx151 to register64
mov byte [ rsp + 0x190 ], r15b; spilling byte x95 to mem
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rax, r15; loading flag
adox rbx, r14
seto al; spill OF x153 to reg (rax)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, r14; loading flag
adox rbx, [ rsp + 0x38 ]
seto r11b; spill OF x195 to reg (r11)
dec r15; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx r8, r8b
adox r8, r15; loading flag
adox rbx, [ rsp + 0xa8 ]
mov r14, [ rsi + 0x18 ]; load m64 x3 to register64
mov r8, rdx; preserving value of x1 into a new reg
mov rdx, [ r10 + 0x0 ]; saving arg2[0] in rdx.
mov byte [ rsp + 0x198 ], r11b; spilling byte x195 to mem
mulx r15, r11, r14; x265, x264<- x3 * arg2[0]
mov [ rsp + 0x1a0 ], r15; spilling x265 to mem
setc r15b; spill CF x110 to reg (r15)
clc;
adcx r11, rbx
mov rbx, 0xffffffffffffffff ; moving imm to reg
mov rdx, rbx; 0xffffffffffffffff to rdx
mov byte [ rsp + 0x1a8 ], al; spilling byte x153 to mem
mulx rbx, rax, r11; x308, x307<- x279 * 0xffffffffffffffff
seto dl; spill OF x238 to reg (rdx)
mov [ rsp + 0x1b0 ], rbx; spilling x308 to mem
mov rbx, -0x2 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rax, r11
mov al, dl; preserving value of x238 into a new reg
mov rdx, [ r10 + 0x20 ]; saving arg2[4] in rdx.
mov byte [ rsp + 0x1b8 ], bpl; spilling byte x138 to mem
mulx rbx, rbp, rdi; x13, x12<- x7 * arg2[4]
mov [ rsp + 0x1c0 ], rbx; spilling x13 to mem
seto bl; spill OF x323 to reg (rbx)
mov byte [ rsp + 0x1c8 ], al; spilling byte x238 to mem
mov rax, 0x0 ; moving imm to reg
dec rax; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r9, r9b
adox r9, rax; loading flag
adox rbp, [ rsp + 0x188 ]
mov r9, 0x7bc65c783158aea3 ; moving imm to reg
mov rdx, r12; x20 to rdx
mulx r12, rax, r9; x40, x39<- x20 * 0x7bc65c783158aea3
seto r9b; spill OF x29 to reg (r9)
mov [ rsp + 0x1d0 ], r12; spilling x40 to mem
movzx r12, byte [ rsp + 0x180 ]; load byte memx54 to register64
mov byte [ rsp + 0x1d8 ], bl; spilling byte x323 to mem
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r12, rbx; loading flag
adox rax, [ rsp + 0x170 ]
seto r12b; spill OF x56 to reg (r12)
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, rbx; loading flag
adox rbp, rax
mov r13, rdx; preserving value of x20 into a new reg
mov rdx, [ r10 + 0x18 ]; saving arg2[3] in rdx.
mulx rax, rbx, r8; x85, x84<- x1 * arg2[3]
mov [ rsp + 0x1e0 ], rax; spilling x85 to mem
setc al; spill CF x280 to reg (rax)
mov byte [ rsp + 0x1e8 ], r12b; spilling byte x56 to mem
movzx r12, byte [ rsp + 0x190 ]; load byte memx95 to register64
clc;
mov byte [ rsp + 0x1f0 ], r9b; spilling byte x29 to mem
mov r9, -0x1 ; moving imm to reg
adcx r12, r9; loading flag
adcx rbx, [ rsp + 0x178 ]
seto r12b; spill OF x71 to reg (r12)
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, r9; loading flag
adox rbp, rbx
mov r15, 0xfdc1767ae2ffffff ; moving imm to reg
mov rdx, rcx; x105 to rdx
mulx rcx, rbx, r15; x128, x127<- x105 * 0xfdc1767ae2ffffff
setc r9b; spill CF x97 to reg (r9)
movzx r15, byte [ rsp + 0x1b8 ]; load byte memx138 to register64
clc;
mov [ rsp + 0x1f8 ], rcx; spilling x128 to mem
mov rcx, -0x1 ; moving imm to reg
adcx r15, rcx; loading flag
adcx rbx, [ rsp + 0x168 ]
seto r15b; spill OF x112 to reg (r15)
movzx rcx, byte [ rsp + 0x1a8 ]; load byte memx153 to register64
mov byte [ rsp + 0x200 ], r9b; spilling byte x97 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rcx, r9; loading flag
adox rbp, rbx
seto cl; spill OF x155 to reg (rcx)
movzx rbx, byte [ rsp + 0x198 ]; load byte memx195 to register64
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
adox rbx, r9; loading flag
adox rbp, [ rsp + 0x30 ]
setc bl; spill CF x140 to reg (rbx)
movzx r9, byte [ rsp + 0x1c8 ]; load byte memx238 to register64
clc;
mov byte [ rsp + 0x208 ], cl; spilling byte x155 to mem
mov rcx, -0x1 ; moving imm to reg
adcx r9, rcx; loading flag
adcx rbp, [ rsp + 0xa0 ]
mov r9, rdx; preserving value of x105 into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mov byte [ rsp + 0x210 ], bl; spilling byte x140 to mem
mulx rcx, rbx, r14; x263, x262<- x3 * arg2[1]
mov [ rsp + 0x218 ], rcx; spilling x263 to mem
setc cl; spill CF x240 to reg (rcx)
clc;
adcx rbx, [ rsp + 0x1a0 ]
mov byte [ rsp + 0x220 ], cl; spilling byte x240 to mem
mov rcx, 0xffffffffffffffff ; moving imm to reg
mov rdx, rcx; 0xffffffffffffffff to rdx
mov byte [ rsp + 0x228 ], r15b; spilling byte x112 to mem
mulx rcx, r15, r11; x306, x305<- x279 * 0xffffffffffffffff
setc dl; spill CF x267 to reg (rdx)
clc;
mov [ rsp + 0x230 ], rcx; spilling x306 to mem
mov rcx, -0x1 ; moving imm to reg
movzx rax, al
adcx rax, rcx; loading flag
adcx rbp, rbx
seto al; spill OF x197 to reg (rax)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r15, [ rsp + 0x1b0 ]
xchg rdx, rdi; x7, swapping with x267, which is currently in rdx
mulx rbx, rcx, [ r10 + 0x28 ]; x11, x10<- x7 * arg2[5]
mov [ rsp + 0x238 ], rbx; spilling x11 to mem
mov rbx, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, rbx; 0x6cfc5fd681c52056, swapping with x7, which is currently in rdx
mov byte [ rsp + 0x240 ], dil; spilling byte x267 to mem
mov byte [ rsp + 0x248 ], al; spilling byte x197 to mem
mulx rdi, rax, r13; x38, x37<- x20 * 0x6cfc5fd681c52056
seto dl; spill OF x310 to reg (rdx)
mov [ rsp + 0x250 ], rdi; spilling x38 to mem
movzx rdi, byte [ rsp + 0x1f0 ]; load byte memx29 to register64
mov byte [ rsp + 0x258 ], r12b; spilling byte x71 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
adox rdi, r12; loading flag
adox rcx, [ rsp + 0x1c0 ]
seto dil; spill OF x31 to reg (rdi)
movzx r12, byte [ rsp + 0x1d8 ]; load byte memx323 to register64
mov byte [ rsp + 0x260 ], dl; spilling byte x310 to mem
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
adox r12, rdx; loading flag
adox rbp, r15
setc r12b; spill CF x282 to reg (r12)
movzx r15, byte [ rsp + 0x1e8 ]; load byte memx56 to register64
clc;
adcx r15, rdx; loading flag
adcx rax, [ rsp + 0x1d0 ]
setc r15b; spill CF x58 to reg (r15)
movzx rdx, byte [ rsp + 0x258 ]; load byte memx71 to register64
clc;
mov [ rsp + 0x268 ], rbp; spilling x324 to mem
mov rbp, -0x1 ; moving imm to reg
adcx rdx, rbp; loading flag
adcx rcx, rax
mov rdx, r8; x1 to rdx
mulx r8, rax, [ r10 + 0x20 ]; x83, x82<- x1 * arg2[4]
setc bpl; spill CF x73 to reg (rbp)
mov [ rsp + 0x270 ], r8; spilling x83 to mem
movzx r8, byte [ rsp + 0x200 ]; load byte memx97 to register64
clc;
mov byte [ rsp + 0x278 ], dil; spilling byte x31 to mem
mov rdi, -0x1 ; moving imm to reg
adcx r8, rdi; loading flag
adcx rax, [ rsp + 0x1e0 ]
mov r8, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, r9; x105, swapping with x1, which is currently in rdx
mov byte [ rsp + 0x280 ], bpl; spilling byte x73 to mem
mulx rdi, rbp, r8; x126, x125<- x105 * 0x7bc65c783158aea3
setc r8b; spill CF x99 to reg (r8)
mov [ rsp + 0x288 ], rdi; spilling x126 to mem
movzx rdi, byte [ rsp + 0x228 ]; load byte memx112 to register64
clc;
mov byte [ rsp + 0x290 ], r15b; spilling byte x58 to mem
mov r15, -0x1 ; moving imm to reg
adcx rdi, r15; loading flag
adcx rcx, rax
seto dil; spill OF x325 to reg (rdi)
movzx rax, byte [ rsp + 0x210 ]; load byte memx140 to register64
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
adox rax, r15; loading flag
adox rbp, [ rsp + 0x1f8 ]
setc al; spill CF x114 to reg (rax)
movzx r15, byte [ rsp + 0x208 ]; load byte memx155 to register64
clc;
mov byte [ rsp + 0x298 ], r8b; spilling byte x99 to mem
mov r8, -0x1 ; moving imm to reg
adcx r15, r8; loading flag
adcx rcx, rbp
setc r15b; spill CF x157 to reg (r15)
movzx rbp, byte [ rsp + 0x248 ]; load byte memx197 to register64
clc;
adcx rbp, r8; loading flag
adcx rcx, [ rsp + 0x28 ]
xchg rdx, r14; x3, swapping with x105, which is currently in rdx
mulx rbp, r8, [ r10 + 0x10 ]; x261, x260<- x3 * arg2[2]
mov [ rsp + 0x2a0 ], rbp; spilling x261 to mem
setc bpl; spill CF x199 to reg (rbp)
mov byte [ rsp + 0x2a8 ], r15b; spilling byte x157 to mem
movzx r15, byte [ rsp + 0x240 ]; load byte memx267 to register64
clc;
mov byte [ rsp + 0x2b0 ], al; spilling byte x114 to mem
mov rax, -0x1 ; moving imm to reg
adcx r15, rax; loading flag
adcx r8, [ rsp + 0x218 ]
seto r15b; spill OF x142 to reg (r15)
movzx rax, byte [ rsp + 0x220 ]; load byte memx240 to register64
mov byte [ rsp + 0x2b8 ], bpl; spilling byte x199 to mem
mov rbp, 0x0 ; moving imm to reg
dec rbp; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rax, rbp; loading flag
adox rcx, [ rsp + 0xc0 ]
mov rax, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r11; x279, swapping with x3, which is currently in rdx
mov byte [ rsp + 0x2c0 ], r15b; spilling byte x142 to mem
mulx rbp, r15, rax; x304, x303<- x279 * 0xffffffffffffffff
setc al; spill CF x269 to reg (rax)
clc;
mov [ rsp + 0x2c8 ], rbp; spilling x304 to mem
mov rbp, -0x1 ; moving imm to reg
movzx r12, r12b
adcx r12, rbp; loading flag
adcx rcx, r8
seto r12b; spill OF x242 to reg (r12)
movzx r8, byte [ rsp + 0x260 ]; load byte memx310 to register64
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
adox r8, rbp; loading flag
adox r15, [ rsp + 0x230 ]
seto r8b; spill OF x312 to reg (r8)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx rdi, dil
adox rdi, rbp; loading flag
adox rcx, r15
xchg rdx, rbx; x7, swapping with x279, which is currently in rdx
mulx rdx, rdi, [ r10 + 0x30 ]; x9, x8<- x7 * arg2[6]
mov r15, 0x2341f27177344 ; moving imm to reg
xchg rdx, r13; x20, swapping with x9, which is currently in rdx
mulx rdx, rbp, r15; x36, x35<- x20 * 0x2341f27177344
setc r15b; spill CF x284 to reg (r15)
mov [ rsp + 0x2d0 ], rcx; spilling x326 to mem
movzx rcx, byte [ rsp + 0x290 ]; load byte memx58 to register64
clc;
mov [ rsp + 0x2d8 ], r13; spilling x9 to mem
mov r13, -0x1 ; moving imm to reg
adcx rcx, r13; loading flag
adcx rbp, [ rsp + 0x250 ]
setc cl; spill CF x60 to reg (rcx)
movzx r13, byte [ rsp + 0x278 ]; load byte memx31 to register64
clc;
mov [ rsp + 0x2e0 ], rdx; spilling x36 to mem
mov rdx, -0x1 ; moving imm to reg
adcx r13, rdx; loading flag
adcx rdi, [ rsp + 0x238 ]
setc r13b; spill CF x33 to reg (r13)
movzx rdx, byte [ rsp + 0x280 ]; load byte memx73 to register64
clc;
mov byte [ rsp + 0x2e8 ], cl; spilling byte x60 to mem
mov rcx, -0x1 ; moving imm to reg
adcx rdx, rcx; loading flag
adcx rdi, rbp
mov rdx, [ r10 + 0x28 ]; arg2[5] to rdx
mulx rbp, rcx, r9; x81, x80<- x1 * arg2[5]
mov [ rsp + 0x2f0 ], rbp; spilling x81 to mem
setc bpl; spill CF x75 to reg (rbp)
mov byte [ rsp + 0x2f8 ], r13b; spilling byte x33 to mem
movzx r13, byte [ rsp + 0x298 ]; load byte memx99 to register64
clc;
mov byte [ rsp + 0x300 ], r8b; spilling byte x312 to mem
mov r8, -0x1 ; moving imm to reg
adcx r13, r8; loading flag
adcx rcx, [ rsp + 0x270 ]
seto r13b; spill OF x327 to reg (r13)
movzx r8, byte [ rsp + 0x2b0 ]; load byte memx114 to register64
mov byte [ rsp + 0x308 ], bpl; spilling byte x75 to mem
mov rbp, -0x1 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
adox r8, rbp; loading flag
adox rdi, rcx
mov r8, 0x6cfc5fd681c52056 ; moving imm to reg
mov rdx, r8; 0x6cfc5fd681c52056 to rdx
mulx r8, rcx, r14; x124, x123<- x105 * 0x6cfc5fd681c52056
setc bpl; spill CF x101 to reg (rbp)
movzx rdx, byte [ rsp + 0x2c0 ]; load byte memx142 to register64
clc;
mov [ rsp + 0x310 ], r8; spilling x124 to mem
mov r8, -0x1 ; moving imm to reg
adcx rdx, r8; loading flag
adcx rcx, [ rsp + 0x288 ]
seto dl; spill OF x116 to reg (rdx)
movzx r8, byte [ rsp + 0x2a8 ]; load byte memx157 to register64
mov byte [ rsp + 0x318 ], bpl; spilling byte x101 to mem
mov rbp, -0x1 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
adox r8, rbp; loading flag
adox rdi, rcx
setc r8b; spill CF x144 to reg (r8)
movzx rcx, byte [ rsp + 0x2b8 ]; load byte memx199 to register64
clc;
adcx rcx, rbp; loading flag
adcx rdi, [ rsp + 0x20 ]
mov cl, dl; preserving value of x116 into a new reg
mov rdx, [ r10 + 0x18 ]; saving arg2[3] in rdx.
mov byte [ rsp + 0x320 ], r8b; spilling byte x144 to mem
mulx rbp, r8, r11; x259, x258<- x3 * arg2[3]
mov [ rsp + 0x328 ], rbp; spilling x259 to mem
setc bpl; spill CF x201 to reg (rbp)
clc;
mov byte [ rsp + 0x330 ], cl; spilling byte x116 to mem
mov rcx, -0x1 ; moving imm to reg
movzx rax, al
adcx rax, rcx; loading flag
adcx r8, [ rsp + 0x2a0 ]
seto al; spill OF x159 to reg (rax)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rcx, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, rcx; loading flag
adox rdi, [ rsp + 0xb8 ]
setc r12b; spill CF x271 to reg (r12)
clc;
movzx r15, r15b
adcx r15, rcx; loading flag
adcx rdi, r8
mov r15, 0xfdc1767ae2ffffff ; moving imm to reg
mov rdx, r15; 0xfdc1767ae2ffffff to rdx
mulx r15, r8, rbx; x302, x301<- x279 * 0xfdc1767ae2ffffff
seto cl; spill OF x244 to reg (rcx)
movzx rdx, byte [ rsp + 0x300 ]; load byte memx312 to register64
mov [ rsp + 0x338 ], r15; spilling x302 to mem
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r15, -0x1 ; moving imm to reg
adox rdx, r15; loading flag
adox r8, [ rsp + 0x2c8 ]
seto dl; spill OF x314 to reg (rdx)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, r15; loading flag
adox rdi, r8
movzx r13, byte [ rsp + 0x2e8 ]; x61, copying x60 here, cause x60 is needed in a reg for other than x61, namely all: , x61, size: 1
mov r8, [ rsp + 0x2e0 ]; load m64 x36 to register64
lea r13, [ r13 + r8 ]; r8/64 + m8
movzx r8, byte [ rsp + 0x2f8 ]; x34, copying x33 here, cause x33 is needed in a reg for other than x34, namely all: , x34, size: 1
mov r15, [ rsp + 0x2d8 ]; load m64 x9 to register64
lea r8, [ r8 + r15 ]; r8/64 + m8
seto r15b; spill OF x329 to reg (r15)
mov [ rsp + 0x340 ], rdi; spilling x328 to mem
movzx rdi, byte [ rsp + 0x308 ]; load byte memx75 to register64
mov byte [ rsp + 0x348 ], dl; spilling byte x314 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rdi, rdx; loading flag
adox r8, r13
mov rdx, [ r10 + 0x30 ]; arg2[6] to rdx
mulx r9, rdi, r9; x79, x78<- x1 * arg2[6]
seto r13b; spill OF x77 to reg (r13)
mov byte [ rsp + 0x350 ], r15b; spilling byte x329 to mem
movzx r15, byte [ rsp + 0x318 ]; load byte memx101 to register64
mov [ rsp + 0x358 ], r9; spilling x79 to mem
mov r9, -0x1 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r9, -0x1 ; moving imm to reg
adox r15, r9; loading flag
adox rdi, [ rsp + 0x2f0 ]
seto r15b; spill OF x103 to reg (r15)
movzx r9, byte [ rsp + 0x330 ]; load byte memx116 to register64
mov byte [ rsp + 0x360 ], r13b; spilling byte x77 to mem
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r9, r13; loading flag
adox r8, rdi
mov r9, 0x2341f27177344 ; moving imm to reg
mov rdx, r9; 0x2341f27177344 to rdx
mulx r14, r9, r14; x122, x121<- x105 * 0x2341f27177344
setc dil; spill CF x286 to reg (rdi)
movzx r13, byte [ rsp + 0x320 ]; load byte memx144 to register64
clc;
mov rdx, -0x1 ; moving imm to reg
adcx r13, rdx; loading flag
adcx r9, [ rsp + 0x310 ]
setc r13b; spill CF x146 to reg (r13)
clc;
movzx rax, al
adcx rax, rdx; loading flag
adcx r8, r9
mov rdx, r11; x3 to rdx
mulx r11, rax, [ r10 + 0x20 ]; x257, x256<- x3 * arg2[4]
seto r9b; spill OF x118 to reg (r9)
mov [ rsp + 0x368 ], r11; spilling x257 to mem
mov r11, 0x0 ; moving imm to reg
dec r11; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbp, bpl
adox rbp, r11; loading flag
adox r8, [ rsp + 0x18 ]
seto bpl; spill OF x203 to reg (rbp)
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r11, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r11; loading flag
adox r8, [ rsp + 0xe0 ]
seto cl; spill OF x246 to reg (rcx)
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r11, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, r11; loading flag
adox rax, [ rsp + 0x328 ]
seto r12b; spill OF x273 to reg (r12)
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r11, -0x1 ; moving imm to reg
movzx rdi, dil
adox rdi, r11; loading flag
adox r8, rax
mov rdi, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, rbx; x279, swapping with x3, which is currently in rdx
mulx rax, r11, rdi; x300, x299<- x279 * 0x7bc65c783158aea3
setc dil; spill CF x161 to reg (rdi)
mov [ rsp + 0x370 ], rax; spilling x300 to mem
movzx rax, byte [ rsp + 0x348 ]; load byte memx314 to register64
clc;
mov byte [ rsp + 0x378 ], cl; spilling byte x246 to mem
mov rcx, -0x1 ; moving imm to reg
adcx rax, rcx; loading flag
adcx r11, [ rsp + 0x338 ]
movzx rax, r15b; x104, copying x103 here, cause x103 is needed in a reg for other than x104, namely all: , x104, size: 1
mov rcx, [ rsp + 0x358 ]; load m64 x79 to register64
lea rax, [ rax + rcx ]; r8/64 + m8
setc cl; spill CF x316 to reg (rcx)
movzx r15, byte [ rsp + 0x350 ]; load byte memx329 to register64
clc;
mov byte [ rsp + 0x380 ], bpl; spilling byte x203 to mem
mov rbp, -0x1 ; moving imm to reg
adcx r15, rbp; loading flag
adcx r8, r11
movzx r15, r13b; x147, copying x146 here, cause x146 is needed in a reg for other than x147, namely all: , x147, size: 1
lea r15, [ r15 + r14 ]
setc r14b; spill CF x331 to reg (r14)
clc;
movzx r13, byte [ rsp + 0x360 ]; load byte memx77 to register64
movzx r9, r9b
adcx r9, rbp; loading flag
adcx rax, r13
mov r13, rdx; preserving value of x279 into a new reg
mov rdx, [ r10 + 0x28 ]; saving arg2[5] in rdx.
mulx r9, r11, rbx; x255, x254<- x3 * arg2[5]
setc bpl; spill CF x120 to reg (rbp)
clc;
mov [ rsp + 0x388 ], r8; spilling x330 to mem
mov r8, -0x1 ; moving imm to reg
movzx rdi, dil
adcx rdi, r8; loading flag
adcx rax, r15
seto dil; spill OF x288 to reg (rdi)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, r15; loading flag
adox r11, [ rsp + 0x368 ]
setc r12b; spill CF x163 to reg (r12)
movzx r8, byte [ rsp + 0x380 ]; load byte memx203 to register64
clc;
adcx r8, r15; loading flag
adcx rax, [ rsp + 0x10 ]
seto r8b; spill OF x275 to reg (r8)
movzx r15, byte [ rsp + 0x378 ]; load byte memx246 to register64
mov [ rsp + 0x390 ], r9; spilling x255 to mem
mov r9, -0x1 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r9, -0x1 ; moving imm to reg
adox r15, r9; loading flag
adox rax, [ rsp + 0xd8 ]
setc r15b; spill CF x205 to reg (r15)
clc;
movzx rdi, dil
adcx rdi, r9; loading flag
adcx rax, r11
mov rdi, 0x6cfc5fd681c52056 ; moving imm to reg
mov rdx, r13; x279 to rdx
mulx r13, r11, rdi; x298, x297<- x279 * 0x6cfc5fd681c52056
seto r9b; spill OF x248 to reg (r9)
mov rdi, -0x1 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdi, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, rdi; loading flag
adox r11, [ rsp + 0x370 ]
seto cl; spill OF x318 to reg (rcx)
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdi, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, rdi; loading flag
adox rax, r11
movzx r14, r12b; x164, copying x163 here, cause x163 is needed in a reg for other than x164, namely all: , x164, size: 1
movzx rbp, bpl
lea r14, [ r14 + rbp ]
setc bpl; spill CF x290 to reg (rbp)
clc;
movzx r15, r15b
adcx r15, rdi; loading flag
adcx r14, [ rsp + 0x8 ]
setc r12b; spill CF x207 to reg (r12)
clc;
movzx r9, r9b
adcx r9, rdi; loading flag
adcx r14, [ rsp + 0xd0 ]
mov r15, rdx; preserving value of x279 into a new reg
mov rdx, [ r10 + 0x30 ]; saving arg2[6] in rdx.
mulx rbx, r9, rbx; x253, x252<- x3 * arg2[6]
mov r11, 0x2341f27177344 ; moving imm to reg
mov rdx, r11; 0x2341f27177344 to rdx
mulx r15, r11, r15; x296, x295<- x279 * 0x2341f27177344
seto dil; spill OF x333 to reg (rdi)
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, rdx; loading flag
adox r9, [ rsp + 0x390 ]
seto r8b; spill OF x277 to reg (r8)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, rdx; loading flag
adox r14, r9
setc bpl; spill CF x250 to reg (rbp)
clc;
movzx rcx, cl
adcx rcx, rdx; loading flag
adcx r13, r11
setc cl; spill CF x320 to reg (rcx)
clc;
movzx rdi, dil
adcx rdi, rdx; loading flag
adcx r14, r13
movzx rdi, r8b; x278, copying x277 here, cause x277 is needed in a reg for other than x278, namely all: , x278, size: 1
lea rdi, [ rdi + rbx ]
movzx rbx, bpl; x251, copying x250 here, cause x250 is needed in a reg for other than x251, namely all: , x251, size: 1
movzx r12, r12b
lea rbx, [ rbx + r12 ]
movzx r12, cl; x321, copying x320 here, cause x320 is needed in a reg for other than x321, namely all: , x321, size: 1
lea r12, [ r12 + r15 ]
adox rdi, rbx
adcx r12, rdi
seto bpl; spill OF x338 to reg (rbp)
adc bpl, 0x0
movzx rbp, bpl
mov r15, [ rsp + 0x268 ]; load m64 x324 to register64
adox r15, [ rsp + 0x160 ]
mov r11, 0xffffffffffffffff ; moving imm to reg
mov rdx, r15; x366 to rdx
mulx r15, r9, r11; x395, x394<- x366 * 0xffffffffffffffff
adcx r9, rdx
mov r9, [ rsp + 0x158 ]; load m64 x353 to register64
mov r8, [ rsp + 0x2d0 ]; x368, copying x326 here, cause x326 is needed in a reg for other than x368, namely all: , x368--x369, size: 1
adox r8, r9
mulx r9, r13, r11; x393, x392<- x366 * 0xffffffffffffffff
setc cl; spill CF x410 to reg (rcx)
clc;
adcx r13, r15
setc bl; spill CF x397 to reg (rbx)
clc;
mov rdi, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, rdi; loading flag
adcx r8, r13
seto r15b; spill OF x369 to reg (r15)
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r8, [ rsp + 0xc8 ]
xchg rdx, r11; 0xffffffffffffffff, swapping with x366, which is currently in rdx
mulx rcx, r13, r8; x482, x481<- x453 * 0xffffffffffffffff
seto dl; spill OF x454 to reg (rdx)
mov byte [ rsp + 0x398 ], bpl; spilling byte x338 to mem
mov rbp, -0x3 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r13, r8
mov r13, [ rsp + 0x340 ]; load m64 x328 to register64
seto dil; spill OF x497 to reg (rdi)
mov rbp, -0x1 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, rbp; loading flag
adox r13, [ rsp + 0x138 ]
mov r15, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r15; 0xffffffffffffffff, swapping with x454, which is currently in rdx
mov [ rsp + 0x3a0 ], r12; spilling x336 to mem
mulx rbp, r12, r11; x391, x390<- x366 * 0xffffffffffffffff
seto dl; spill OF x371 to reg (rdx)
mov [ rsp + 0x3a8 ], r14; spilling x334 to mem
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbx, bl
adox rbx, r14; loading flag
adox r9, r12
adcx r9, r13
seto bl; spill OF x399 to reg (rbx)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, r13; loading flag
adox r9, [ rsp + 0xf8 ]
mov r15, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r8; x453, swapping with x371, which is currently in rdx
mulx r12, r14, r15; x480, x479<- x453 * 0xffffffffffffffff
mov r13, [ rsi + 0x30 ]; load m64 x6 to register64
setc r15b; spill CF x414 to reg (r15)
clc;
adcx r14, rcx
setc cl; spill CF x484 to reg (rcx)
clc;
mov [ rsp + 0x3b0 ], rax; spilling x332 to mem
mov rax, -0x1 ; moving imm to reg
movzx rdi, dil
adcx rdi, rax; loading flag
adcx r9, r14
mov rdi, rdx; preserving value of x453 into a new reg
mov rdx, [ r10 + 0x0 ]; saving arg2[0] in rdx.
mulx r14, rax, r13; x526, x525<- x6 * arg2[0]
mov [ rsp + 0x3b8 ], r14; spilling x526 to mem
setc r14b; spill CF x499 to reg (r14)
clc;
adcx rax, r9
mov r9, 0xffffffffffffffff ; moving imm to reg
mov rdx, rax; x540 to rdx
mov byte [ rsp + 0x3c0 ], r14b; spilling byte x499 to mem
mulx rax, r14, r9; x569, x568<- x540 * 0xffffffffffffffff
setc r9b; spill CF x541 to reg (r9)
clc;
adcx r14, rdx
mov r14, [ rsp + 0x128 ]; load m64 x357 to register64
mov [ rsp + 0x3c8 ], rax; spilling x569 to mem
setc al; spill CF x584 to reg (rax)
clc;
mov byte [ rsp + 0x3d0 ], r9b; spilling byte x541 to mem
mov r9, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, r9; loading flag
adcx r14, [ rsp + 0x388 ]
mov r8, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, r11; x366, swapping with x540, which is currently in rdx
mov byte [ rsp + 0x3d8 ], al; spilling byte x584 to mem
mulx r9, rax, r8; x389, x388<- x366 * 0xfdc1767ae2ffffff
setc r8b; spill CF x373 to reg (r8)
clc;
mov [ rsp + 0x3e0 ], r9; spilling x389 to mem
mov r9, -0x1 ; moving imm to reg
movzx rbx, bl
adcx rbx, r9; loading flag
adcx rbp, rax
setc bl; spill CF x401 to reg (rbx)
clc;
movzx r15, r15b
adcx r15, r9; loading flag
adcx r14, rbp
mov r15, [ rsp + 0xf0 ]; x457, copying x442 here, cause x442 is needed in a reg for other than x457, namely all: , x457--x458, size: 1
adox r15, r14
mov rax, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rax; 0xffffffffffffffff, swapping with x366, which is currently in rdx
mulx rbp, r14, rdi; x478, x477<- x453 * 0xffffffffffffffff
seto r9b; spill OF x458 to reg (r9)
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rcx, cl
adox rcx, rdx; loading flag
adox r12, r14
setc cl; spill CF x416 to reg (rcx)
movzx r14, byte [ rsp + 0x3c0 ]; load byte memx499 to register64
clc;
adcx r14, rdx; loading flag
adcx r15, r12
mov rdx, [ r10 + 0x8 ]; arg2[1] to rdx
mulx r14, r12, r13; x524, x523<- x6 * arg2[1]
mov [ rsp + 0x3e8 ], r14; spilling x524 to mem
setc r14b; spill CF x501 to reg (r14)
clc;
adcx r12, [ rsp + 0x3b8 ]
mov byte [ rsp + 0x3f0 ], r14b; spilling byte x501 to mem
setc r14b; spill CF x528 to reg (r14)
mov [ rsp + 0x3f8 ], rbp; spilling x478 to mem
movzx rbp, byte [ rsp + 0x3d0 ]; load byte memx541 to register64
clc;
mov byte [ rsp + 0x400 ], r9b; spilling byte x458 to mem
mov r9, -0x1 ; moving imm to reg
adcx rbp, r9; loading flag
adcx r15, r12
mov rbp, 0xffffffffffffffff ; moving imm to reg
mov rdx, r11; x540 to rdx
mulx r11, r12, rbp; x567, x566<- x540 * 0xffffffffffffffff
seto r9b; spill OF x486 to reg (r9)
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, [ rsp + 0x3c8 ]
seto bpl; spill OF x571 to reg (rbp)
mov [ rsp + 0x408 ], r11; spilling x567 to mem
movzx r11, byte [ rsp + 0x3d8 ]; load byte memx584 to register64
mov byte [ rsp + 0x410 ], r14b; spilling byte x528 to mem
mov r14, -0x1 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r14, -0x1 ; moving imm to reg
adox r11, r14; loading flag
adox r15, r12
setc r11b; spill CF x543 to reg (r11)
seto r12b; spill OF x586 to reg (r12)
mov r14, r15; x600, copying x585 here, cause x585 is needed in a reg for other than x600, namely all: , x616, x600--x601, size: 2
mov byte [ rsp + 0x418 ], bpl; spilling byte x571 to mem
mov rbp, 0xffffffffffffffff ; moving imm to reg
sub r14, rbp
mov rbp, [ rsp + 0x130 ]; load m64 x359 to register64
mov [ rsp + 0x420 ], r14; spilling x600 to mem
mov r14, -0x1 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r14, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, r14; loading flag
adox rbp, [ rsp + 0x3b0 ]
mov r8, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, rax; x366, swapping with x540, which is currently in rdx
mov byte [ rsp + 0x428 ], r12b; spilling byte x586 to mem
mulx r14, r12, r8; x387, x386<- x366 * 0x7bc65c783158aea3
setc r8b; spill CF x601 to reg (r8)
clc;
mov [ rsp + 0x430 ], r14; spilling x387 to mem
mov r14, -0x1 ; moving imm to reg
movzx rbx, bl
adcx rbx, r14; loading flag
adcx r12, [ rsp + 0x3e0 ]
setc bl; spill CF x403 to reg (rbx)
clc;
movzx rcx, cl
adcx rcx, r14; loading flag
adcx rbp, r12
mov rcx, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, rcx; 0xfdc1767ae2ffffff, swapping with x366, which is currently in rdx
mulx r12, r14, rdi; x476, x475<- x453 * 0xfdc1767ae2ffffff
setc dl; spill CF x418 to reg (rdx)
mov [ rsp + 0x438 ], r12; spilling x476 to mem
movzx r12, byte [ rsp + 0x400 ]; load byte memx458 to register64
clc;
mov byte [ rsp + 0x440 ], bl; spilling byte x403 to mem
mov rbx, -0x1 ; moving imm to reg
adcx r12, rbx; loading flag
adcx rbp, [ rsp + 0xe8 ]
seto r12b; spill OF x375 to reg (r12)
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, rbx; loading flag
adox r14, [ rsp + 0x3f8 ]
setc r9b; spill CF x460 to reg (r9)
movzx rbx, byte [ rsp + 0x3f0 ]; load byte memx501 to register64
clc;
mov byte [ rsp + 0x448 ], dl; spilling byte x418 to mem
mov rdx, -0x1 ; moving imm to reg
adcx rbx, rdx; loading flag
adcx rbp, r14
mov rdx, [ r10 + 0x10 ]; arg2[2] to rdx
mulx rbx, r14, r13; x522, x521<- x6 * arg2[2]
mov [ rsp + 0x450 ], rbx; spilling x522 to mem
setc bl; spill CF x503 to reg (rbx)
mov byte [ rsp + 0x458 ], r9b; spilling byte x460 to mem
movzx r9, byte [ rsp + 0x410 ]; load byte memx528 to register64
clc;
mov byte [ rsp + 0x460 ], r12b; spilling byte x375 to mem
mov r12, -0x1 ; moving imm to reg
adcx r9, r12; loading flag
adcx r14, [ rsp + 0x3e8 ]
setc r9b; spill CF x530 to reg (r9)
clc;
movzx r11, r11b
adcx r11, r12; loading flag
adcx rbp, r14
mov r11, 0xffffffffffffffff ; moving imm to reg
mov rdx, r11; 0xffffffffffffffff to rdx
mulx r11, r14, rax; x565, x564<- x540 * 0xffffffffffffffff
seto r12b; spill OF x488 to reg (r12)
movzx rdx, byte [ rsp + 0x418 ]; load byte memx571 to register64
mov [ rsp + 0x468 ], r11; spilling x565 to mem
mov r11, 0x0 ; moving imm to reg
dec r11; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rdx, r11; loading flag
adox r14, [ rsp + 0x408 ]
setc dl; spill CF x545 to reg (rdx)
movzx r11, byte [ rsp + 0x428 ]; load byte memx586 to register64
clc;
mov byte [ rsp + 0x470 ], r9b; spilling byte x530 to mem
mov r9, -0x1 ; moving imm to reg
adcx r11, r9; loading flag
adcx rbp, r14
setc r11b; spill CF x588 to reg (r11)
seto r14b; spill OF x573 to reg (r14)
movzx r9, r8b; x601, copying x601 here, cause x601 is needed in a reg for other than x601, namely all: , x602--x603, size: 1
add r9, -0x1
mov r8, rbp; x602, copying x587 here, cause x587 is needed in a reg for other than x602, namely all: , x602--x603, x617, size: 2
mov r9, 0xffffffffffffffff ; moving imm to reg
sbb r8, r9
mov r9, [ rsp + 0x3a8 ]; load m64 x334 to register64
mov [ rsp + 0x478 ], r8; spilling x602 to mem
movzx r8, byte [ rsp + 0x460 ]; load byte memx375 to register64
mov byte [ rsp + 0x480 ], r11b; spilling byte x588 to mem
mov r11, 0x0 ; moving imm to reg
dec r11; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r8, r11; loading flag
adox r9, [ rsp + 0x150 ]
mov r8, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, r8; 0x6cfc5fd681c52056, swapping with x545, which is currently in rdx
mov byte [ rsp + 0x488 ], r14b; spilling byte x573 to mem
mulx r11, r14, rcx; x385, x384<- x366 * 0x6cfc5fd681c52056
setc dl; spill CF x603 to reg (rdx)
mov [ rsp + 0x490 ], r11; spilling x385 to mem
movzx r11, byte [ rsp + 0x440 ]; load byte memx403 to register64
clc;
mov byte [ rsp + 0x498 ], r8b; spilling byte x545 to mem
mov r8, -0x1 ; moving imm to reg
adcx r11, r8; loading flag
adcx r14, [ rsp + 0x430 ]
setc r11b; spill CF x405 to reg (r11)
movzx r8, byte [ rsp + 0x448 ]; load byte memx418 to register64
clc;
mov byte [ rsp + 0x4a0 ], dl; spilling byte x603 to mem
mov rdx, -0x1 ; moving imm to reg
adcx r8, rdx; loading flag
adcx r9, r14
mov r8, 0x7bc65c783158aea3 ; moving imm to reg
mov rdx, r8; 0x7bc65c783158aea3 to rdx
mulx r8, r14, rdi; x474, x473<- x453 * 0x7bc65c783158aea3
setc dl; spill CF x420 to reg (rdx)
clc;
mov [ rsp + 0x4a8 ], r8; spilling x474 to mem
mov r8, -0x1 ; moving imm to reg
movzx r12, r12b
adcx r12, r8; loading flag
adcx r14, [ rsp + 0x438 ]
seto r12b; spill OF x377 to reg (r12)
movzx r8, byte [ rsp + 0x458 ]; load byte memx460 to register64
mov byte [ rsp + 0x4b0 ], dl; spilling byte x420 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r8, rdx; loading flag
adox r9, [ rsp + 0x118 ]
setc r8b; spill CF x490 to reg (r8)
clc;
movzx rbx, bl
adcx rbx, rdx; loading flag
adcx r9, r14
mov rdx, [ r10 + 0x18 ]; arg2[3] to rdx
mulx rbx, r14, r13; x520, x519<- x6 * arg2[3]
mov [ rsp + 0x4b8 ], rbx; spilling x520 to mem
seto bl; spill OF x462 to reg (rbx)
mov byte [ rsp + 0x4c0 ], r8b; spilling byte x490 to mem
movzx r8, byte [ rsp + 0x470 ]; load byte memx530 to register64
mov byte [ rsp + 0x4c8 ], r11b; spilling byte x405 to mem
mov r11, 0x0 ; moving imm to reg
dec r11; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r8, r11; loading flag
adox r14, [ rsp + 0x450 ]
mov r8, 0xfdc1767ae2ffffff ; moving imm to reg
mov rdx, rax; x540 to rdx
mulx rax, r11, r8; x563, x562<- x540 * 0xfdc1767ae2ffffff
setc r8b; spill CF x505 to reg (r8)
mov [ rsp + 0x4d0 ], rax; spilling x563 to mem
movzx rax, byte [ rsp + 0x498 ]; load byte memx545 to register64
clc;
mov byte [ rsp + 0x4d8 ], bl; spilling byte x462 to mem
mov rbx, -0x1 ; moving imm to reg
adcx rax, rbx; loading flag
adcx r9, r14
setc al; spill CF x547 to reg (rax)
movzx r14, byte [ rsp + 0x488 ]; load byte memx573 to register64
clc;
adcx r14, rbx; loading flag
adcx r11, [ rsp + 0x468 ]
setc r14b; spill CF x575 to reg (r14)
movzx rbx, byte [ rsp + 0x480 ]; load byte memx588 to register64
clc;
mov byte [ rsp + 0x4e0 ], al; spilling byte x547 to mem
mov rax, -0x1 ; moving imm to reg
adcx rbx, rax; loading flag
adcx r9, r11
setc bl; spill CF x590 to reg (rbx)
seto r11b; spill OF x532 to reg (r11)
movzx rax, byte [ rsp + 0x4a0 ]; x603, copying x603 here, cause x603 is needed in a reg for other than x603, namely all: , x604--x605, size: 1
add rax, -0x1
mov rax, r9; x604, copying x589 here, cause x589 is needed in a reg for other than x604, namely all: , x618, x604--x605, size: 2
mov byte [ rsp + 0x4e8 ], r14b; spilling byte x575 to mem
mov r14, 0xffffffffffffffff ; moving imm to reg
sbb rax, r14
mov r14, 0x2341f27177344 ; moving imm to reg
xchg rdx, rcx; x366, swapping with x540, which is currently in rdx
mov [ rsp + 0x4f0 ], rax; spilling x604 to mem
mulx rdx, rax, r14; x383, x382<- x366 * 0x2341f27177344
mov r14, [ rsp + 0x148 ]; load m64 x363 to register64
mov [ rsp + 0x4f8 ], rdx; spilling x383 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r12, r12b
adox r12, rdx; loading flag
adox r14, [ rsp + 0x3a0 ]
setc r12b; spill CF x605 to reg (r12)
movzx rdx, byte [ rsp + 0x4c8 ]; load byte memx405 to register64
clc;
mov byte [ rsp + 0x500 ], bl; spilling byte x590 to mem
mov rbx, -0x1 ; moving imm to reg
adcx rdx, rbx; loading flag
adcx rax, [ rsp + 0x490 ]
seto dl; spill OF x379 to reg (rdx)
movzx rbx, byte [ rsp + 0x4b0 ]; load byte memx420 to register64
mov byte [ rsp + 0x508 ], r12b; spilling byte x605 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbx, r12; loading flag
adox r14, rax
setc bl; spill CF x407 to reg (rbx)
movzx rax, byte [ rsp + 0x4d8 ]; load byte memx462 to register64
clc;
adcx rax, r12; loading flag
adcx r14, [ rsp + 0x110 ]
mov rax, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, rax; 0x6cfc5fd681c52056, swapping with x379, which is currently in rdx
mov byte [ rsp + 0x510 ], al; spilling byte x379 to mem
mulx r12, rax, rdi; x472, x471<- x453 * 0x6cfc5fd681c52056
xchg rdx, r13; x6, swapping with 0x6cfc5fd681c52056, which is currently in rdx
mov [ rsp + 0x518 ], r12; spilling x472 to mem
mulx r13, r12, [ r10 + 0x20 ]; x518, x517<- x6 * arg2[4]
mov [ rsp + 0x520 ], r13; spilling x518 to mem
setc r13b; spill CF x464 to reg (r13)
mov byte [ rsp + 0x528 ], bl; spilling byte x407 to mem
movzx rbx, byte [ rsp + 0x4c0 ]; load byte memx490 to register64
clc;
mov [ rsp + 0x530 ], r12; spilling x517 to mem
mov r12, -0x1 ; moving imm to reg
adcx rbx, r12; loading flag
adcx rax, [ rsp + 0x4a8 ]
seto bl; spill OF x422 to reg (rbx)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, r12; loading flag
adox r14, rax
mov r8, [ rsp + 0x530 ]; load m64 x517 to register64
seto al; spill OF x507 to reg (rax)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, r12; loading flag
adox r8, [ rsp + 0x4b8 ]
setc r11b; spill CF x492 to reg (r11)
movzx r12, byte [ rsp + 0x4e0 ]; load byte memx547 to register64
clc;
mov byte [ rsp + 0x538 ], al; spilling byte x507 to mem
mov rax, -0x1 ; moving imm to reg
adcx r12, rax; loading flag
adcx r14, r8
mov r12, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, r12; 0x7bc65c783158aea3, swapping with x6, which is currently in rdx
mulx r8, rax, rcx; x561, x560<- x540 * 0x7bc65c783158aea3
setc dl; spill CF x549 to reg (rdx)
mov [ rsp + 0x540 ], r8; spilling x561 to mem
movzx r8, byte [ rsp + 0x4e8 ]; load byte memx575 to register64
clc;
mov byte [ rsp + 0x548 ], r11b; spilling byte x492 to mem
mov r11, -0x1 ; moving imm to reg
adcx r8, r11; loading flag
adcx rax, [ rsp + 0x4d0 ]
setc r8b; spill CF x577 to reg (r8)
movzx r11, byte [ rsp + 0x500 ]; load byte memx590 to register64
clc;
mov byte [ rsp + 0x550 ], dl; spilling byte x549 to mem
mov rdx, -0x1 ; moving imm to reg
adcx r11, rdx; loading flag
adcx r14, rax
movzx r11, byte [ rsp + 0x528 ]; x408, copying x407 here, cause x407 is needed in a reg for other than x408, namely all: , x408, size: 1
mov rax, [ rsp + 0x4f8 ]; load m64 x383 to register64
lea r11, [ r11 + rax ]; r8/64 + m8
setc al; spill CF x592 to reg (rax)
seto dl; spill OF x534 to reg (rdx)
mov byte [ rsp + 0x558 ], r8b; spilling byte x577 to mem
movzx r8, byte [ rsp + 0x508 ]; x605, copying x605 here, cause x605 is needed in a reg for other than x605, namely all: , x606--x607, size: 1
add r8, -0x1
mov r8, r14; x606, copying x591 here, cause x591 is needed in a reg for other than x606, namely all: , x619, x606--x607, size: 2
mov byte [ rsp + 0x560 ], r13b; spilling byte x464 to mem
mov r13, 0xfdc1767ae2ffffff ; moving imm to reg
sbb r8, r13
movzx r13, byte [ rsp + 0x398 ]; load byte memx338 to register64
mov [ rsp + 0x568 ], r8; spilling x606 to mem
movzx r8, byte [ rsp + 0x510 ]; load byte memx379 to register64
mov byte [ rsp + 0x570 ], al; spilling byte x592 to mem
mov rax, -0x1 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rax, -0x1 ; moving imm to reg
adox r8, rax; loading flag
adox r13, [ rsp + 0x140 ]
mov r8, 0x2341f27177344 ; moving imm to reg
xchg rdx, r8; 0x2341f27177344, swapping with x534, which is currently in rdx
mulx rdi, rax, rdi; x470, x469<- x453 * 0x2341f27177344
seto dl; spill OF x381 to reg (rdx)
mov [ rsp + 0x578 ], rdi; spilling x470 to mem
mov rdi, 0x0 ; moving imm to reg
dec rdi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbx, bl
adox rbx, rdi; loading flag
adox r13, r11
setc bl; spill CF x607 to reg (rbx)
movzx r11, byte [ rsp + 0x560 ]; load byte memx464 to register64
clc;
adcx r11, rdi; loading flag
adcx r13, [ rsp + 0x108 ]
setc r11b; spill CF x466 to reg (r11)
movzx rdi, byte [ rsp + 0x548 ]; load byte memx492 to register64
clc;
mov byte [ rsp + 0x580 ], dl; spilling byte x381 to mem
mov rdx, -0x1 ; moving imm to reg
adcx rdi, rdx; loading flag
adcx rax, [ rsp + 0x518 ]
mov rdx, [ r10 + 0x28 ]; arg2[5] to rdx
mov byte [ rsp + 0x588 ], r11b; spilling byte x466 to mem
mulx rdi, r11, r12; x516, x515<- x6 * arg2[5]
mov [ rsp + 0x590 ], rdi; spilling x516 to mem
setc dil; spill CF x494 to reg (rdi)
clc;
mov byte [ rsp + 0x598 ], bl; spilling byte x607 to mem
mov rbx, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, rbx; loading flag
adcx r11, [ rsp + 0x520 ]
setc r8b; spill CF x536 to reg (r8)
movzx rbx, byte [ rsp + 0x538 ]; load byte memx507 to register64
clc;
mov byte [ rsp + 0x5a0 ], dil; spilling byte x494 to mem
mov rdi, -0x1 ; moving imm to reg
adcx rbx, rdi; loading flag
adcx r13, rax
mov rbx, 0x6cfc5fd681c52056 ; moving imm to reg
mov rdx, rcx; x540 to rdx
mulx rcx, rax, rbx; x559, x558<- x540 * 0x6cfc5fd681c52056
seto dil; spill OF x424 to reg (rdi)
movzx rbx, byte [ rsp + 0x558 ]; load byte memx577 to register64
mov [ rsp + 0x5a8 ], rcx; spilling x559 to mem
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbx, rcx; loading flag
adox rax, [ rsp + 0x540 ]
setc bl; spill CF x509 to reg (rbx)
movzx rcx, byte [ rsp + 0x550 ]; load byte memx549 to register64
clc;
mov byte [ rsp + 0x5b0 ], r8b; spilling byte x536 to mem
mov r8, -0x1 ; moving imm to reg
adcx rcx, r8; loading flag
adcx r13, r11
setc cl; spill CF x551 to reg (rcx)
movzx r11, byte [ rsp + 0x570 ]; load byte memx592 to register64
clc;
adcx r11, r8; loading flag
adcx r13, rax
setc r11b; spill CF x594 to reg (r11)
seto al; spill OF x579 to reg (rax)
movzx r8, byte [ rsp + 0x598 ]; x607, copying x607 here, cause x607 is needed in a reg for other than x607, namely all: , x608--x609, size: 1
add r8, -0x1
mov r8, r13; x608, copying x593 here, cause x593 is needed in a reg for other than x608, namely all: , x620, x608--x609, size: 2
mov byte [ rsp + 0x5b8 ], cl; spilling byte x551 to mem
mov rcx, 0x7bc65c783158aea3 ; moving imm to reg
sbb r8, rcx
movzx rcx, byte [ rsp + 0x5a0 ]; x495, copying x494 here, cause x494 is needed in a reg for other than x495, namely all: , x495, size: 1
mov [ rsp + 0x5c0 ], r8; spilling x608 to mem
mov r8, [ rsp + 0x578 ]; load m64 x470 to register64
lea rcx, [ rcx + r8 ]; r8/64 + m8
movzx r8, dil; x425, copying x424 here, cause x424 is needed in a reg for other than x425, namely all: , x425, size: 1
mov byte [ rsp + 0x5c8 ], r11b; spilling byte x594 to mem
movzx r11, byte [ rsp + 0x580 ]; load byte memx381 to register64
lea r8, [ r8 + r11 ]; r64+m8
movzx r11, byte [ rsp + 0x588 ]; load byte memx466 to register64
mov rdi, 0x0 ; moving imm to reg
dec rdi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r11, rdi; loading flag
adox r8, [ rsp + 0x100 ]
setc r11b; spill CF x609 to reg (r11)
clc;
movzx rbx, bl
adcx rbx, rdi; loading flag
adcx r8, rcx
xchg rdx, r12; x6, swapping with x540, which is currently in rdx
mulx rdx, rbx, [ r10 + 0x30 ]; x514, x513<- x6 * arg2[6]
seto cl; spill OF x468 to reg (rcx)
movzx rdi, byte [ rsp + 0x5b0 ]; load byte memx536 to register64
mov byte [ rsp + 0x5d0 ], r11b; spilling byte x609 to mem
mov r11, 0x0 ; moving imm to reg
dec r11; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rdi, r11; loading flag
adox rbx, [ rsp + 0x590 ]
seto dil; spill OF x538 to reg (rdi)
movzx r11, byte [ rsp + 0x5b8 ]; load byte memx551 to register64
mov byte [ rsp + 0x5d8 ], cl; spilling byte x468 to mem
mov rcx, -0x1 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rcx, -0x1 ; moving imm to reg
adox r11, rcx; loading flag
adox r8, rbx
mov r11, 0x2341f27177344 ; moving imm to reg
xchg rdx, r11; 0x2341f27177344, swapping with x514, which is currently in rdx
mulx r12, rbx, r12; x557, x556<- x540 * 0x2341f27177344
seto cl; spill OF x553 to reg (rcx)
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rax, al
adox rax, rdx; loading flag
adox rbx, [ rsp + 0x5a8 ]
setc al; spill CF x511 to reg (rax)
movzx rdx, byte [ rsp + 0x5c8 ]; load byte memx594 to register64
clc;
mov [ rsp + 0x5e0 ], r12; spilling x557 to mem
mov r12, -0x1 ; moving imm to reg
adcx rdx, r12; loading flag
adcx r8, rbx
movzx rdx, dil; x539, copying x538 here, cause x538 is needed in a reg for other than x539, namely all: , x539, size: 1
lea rdx, [ rdx + r11 ]
setc r11b; spill CF x596 to reg (r11)
seto dil; spill OF x581 to reg (rdi)
movzx rbx, byte [ rsp + 0x5d0 ]; x609, copying x609 here, cause x609 is needed in a reg for other than x609, namely all: , x610--x611, size: 1
add rbx, -0x1
mov rbx, r8; x610, copying x595 here, cause x595 is needed in a reg for other than x610, namely all: , x621, x610--x611, size: 2
mov r12, 0x6cfc5fd681c52056 ; moving imm to reg
sbb rbx, r12
movzx r12, al; x512, copying x511 here, cause x511 is needed in a reg for other than x512, namely all: , x512, size: 1
mov [ rsp + 0x5e8 ], rbx; spilling x610 to mem
movzx rbx, byte [ rsp + 0x5d8 ]; load byte memx468 to register64
lea r12, [ r12 + rbx ]; r64+m8
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rcx, cl
adox rcx, rbx; loading flag
adox r12, rdx
movzx rax, dil; x582, copying x581 here, cause x581 is needed in a reg for other than x582, namely all: , x582, size: 1
mov rcx, [ rsp + 0x5e0 ]; load m64 x557 to register64
lea rax, [ rax + rcx ]; r8/64 + m8
seto cl; spill OF x555 to reg (rcx)
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdi, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, rdi; loading flag
adox r12, rax
seto r11b; spill OF x598 to reg (r11)
mov rdx, r12; x612, copying x597 here, cause x597 is needed in a reg for other than x612, namely all: , x612--x613, x622, size: 2
mov rax, 0x2341f27177344 ; moving imm to reg
sbb rdx, rax
movzx rbx, r11b; x599, copying x598 here, cause x598 is needed in a reg for other than x599, namely all: , x599, size: 1
movzx rcx, cl
lea rbx, [ rbx + rcx ]
sbb rbx, 0x00000000
mov rbx, [ rsp + 0x4f0 ]; x618, copying x604 here, cause x604 is needed in a reg for other than x618, namely all: , x618, size: 1
cmovc rbx, r9; if CF, x618<- x589 (nzVar)
cmovc rdx, r12; if CF, x622<- x597 (nzVar)
mov r9, [ rsp + 0x420 ]; x616, copying x600 here, cause x600 is needed in a reg for other than x616, namely all: , x616, size: 1
cmovc r9, r15; if CF, x616<- x585 (nzVar)
mov r15, [ rsp + 0x5e8 ]; x621, copying x610 here, cause x610 is needed in a reg for other than x621, namely all: , x621, size: 1
cmovc r15, r8; if CF, x621<- x595 (nzVar)
mov r8, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r8 + 0x30 ], rdx; out1[6] = x622
mov rcx, [ rsp + 0x5c0 ]; x620, copying x608 here, cause x608 is needed in a reg for other than x620, namely all: , x620, size: 1
cmovc rcx, r13; if CF, x620<- x593 (nzVar)
mov [ r8 + 0x10 ], rbx; out1[2] = x618
mov r13, [ rsp + 0x478 ]; x617, copying x602 here, cause x602 is needed in a reg for other than x617, namely all: , x617, size: 1
cmovc r13, rbp; if CF, x617<- x587 (nzVar)
mov [ r8 + 0x8 ], r13; out1[1] = x617
mov [ r8 + 0x20 ], rcx; out1[4] = x620
mov rbp, [ rsp + 0x568 ]; x619, copying x606 here, cause x606 is needed in a reg for other than x619, namely all: , x619, size: 1
cmovc rbp, r14; if CF, x619<- x591 (nzVar)
mov [ r8 + 0x0 ], r9; out1[0] = x616
mov [ r8 + 0x18 ], rbp; out1[3] = x619
mov [ r8 + 0x28 ], r15; out1[5] = x621
mov rbx, [ rsp + 0x5f0 ]; restoring from stack
mov rbp, [ rsp + 0x5f8 ]; restoring from stack
mov r12, [ rsp + 0x600 ]; restoring from stack
mov r13, [ rsp + 0x608 ]; restoring from stack
mov r14, [ rsp + 0x610 ]; restoring from stack
mov r15, [ rsp + 0x618 ]; restoring from stack
add rsp, 0x620 
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; clocked at 2600 MHz
; first cyclecount 486.935, best 479.3478260869565, lastGood 488.5652173913044
; seed 412639959625635 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 83789 ms / 500 runs=> 167.578ms/run
; Time spent for assembling and measureing (initial batch_size=24, initial num_batches=101): 1708 ms
; Ratio (time for assembling + measure)/(total runtime for 500runs): 0.02038453734977145
; number reverted permutation/ tried permutation: 142 / 255 =55.686%
; number reverted decision/ tried decision: 151 / 246 =61.382%