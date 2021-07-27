SECTION .text
	GLOBAL square_p434
square_p434:
sub rsp, 0x620 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x5f0 ], rbx; saving to stack
mov [ rsp + 0x5f8 ], rbp; saving to stack
mov [ rsp + 0x600 ], r12; saving to stack
mov [ rsp + 0x608 ], r13; saving to stack
mov [ rsp + 0x610 ], r14; saving to stack
mov [ rsp + 0x618 ], r15; saving to stack
mov rax, [ rsi + 0x10 ]; load m64 x2 to register64
mov rdx, rax; x2 to rdx
mulx rax, r10, [ rsi + 0x10 ]; x174, x173<- x2 * arg1[2]
mulx r11, rbx, [ rsi + 0x18 ]; x172, x171<- x2 * arg1[3]
mulx rbp, r12, [ rsi + 0x28 ]; x168, x167<- x2 * arg1[5]
mulx r13, r14, [ rsi + 0x8 ]; x176, x175<- x2 * arg1[1]
mulx r15, rcx, [ rsi + 0x0 ]; x178, x177<- x2 * arg1[0]
mov r8, [ rsi + 0x28 ]; load m64 x5 to register64
xor r9, r9
adox r14, r15
adox r10, r13
mulx r13, r15, [ rsi + 0x20 ]; x170, x169<- x2 * arg1[4]
adox rbx, rax
mulx rdx, rax, [ rsi + 0x30 ]; x166, x165<- x2 * arg1[6]
adox r15, r11
adox r12, r13
xchg rdx, r8; x5, swapping with x166, which is currently in rdx
mulx r11, r13, [ rsi + 0x8 ]; x437, x436<- x5 * arg1[1]
adox rax, rbp
mulx rbp, r9, [ rsi + 0x28 ]; x429, x428<- x5 * arg1[5]
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov [ rsp + 0x8 ], rax; spilling x189 to mem
mulx rdi, rax, [ rsi + 0x0 ]; x439, x438<- x5 * arg1[0]
mov [ rsp + 0x10 ], rax; spilling x438 to mem
mov [ rsp + 0x18 ], r12; spilling x187 to mem
mulx rax, r12, [ rsi + 0x10 ]; x435, x434<- x5 * arg1[2]
mov [ rsp + 0x20 ], r15; spilling x185 to mem
mov r15, [ rsi + 0x0 ]; load m64 x7 to register64
adcx r13, rdi
mov [ rsp + 0x28 ], r13; spilling x440 to mem
mulx rdi, r13, [ rsi + 0x30 ]; x427, x426<- x5 * arg1[6]
adcx r12, r11
mov [ rsp + 0x30 ], r12; spilling x442 to mem
mulx r11, r12, [ rsi + 0x18 ]; x433, x432<- x5 * arg1[3]
mov [ rsp + 0x38 ], rbx; spilling x183 to mem
mov rbx, rdx; preserving value of x5 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x40 ], r10; spilling x181 to mem
mov [ rsp + 0x48 ], r14; spilling x179 to mem
mulx r10, r14, r15; x21, x20<- x7 * arg1[0]
mov rdx, rbx; x5 to rdx
mulx rdx, rbx, [ rsi + 0x20 ]; x431, x430<- x5 * arg1[4]
adcx r12, rax
adcx rbx, r11
mov rax, 0x0 ; moving imm to reg
adox r8, rax
mov r11, rdx; preserving value of x431 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x50 ], rbx; spilling x446 to mem
mulx rax, rbx, r15; x19, x18<- x7 * arg1[1]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x58 ], r12; spilling x444 to mem
mov [ rsp + 0x60 ], r8; spilling x191 to mem
mulx r12, r8, r14; x48, x47<- x20 * 0xffffffffffffffff
adcx r9, r11
mov r11, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x68 ], r9; spilling x448 to mem
mov [ rsp + 0x70 ], rcx; spilling x177 to mem
mulx r9, rcx, r15; x17, x16<- x7 * arg1[2]
adcx r13, rbp
mov rdx, r11; 0xffffffffffffffff to rdx
mulx r11, rbp, r14; x46, x45<- x20 * 0xffffffffffffffff
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, r14
mov r8, [ rsi + 0x8 ]; load m64 x1 to register64
mov rdx, 0x0 ; moving imm to reg
adcx rdi, rdx
clc;
adcx rbp, r12
mov r12, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x78 ], rdi; spilling x452 to mem
mov [ rsp + 0x80 ], r13; spilling x450 to mem
mulx rdi, r13, r8; x91, x90<- x1 * arg1[0]
setc dl; spill CF x50 to reg (rdx)
clc;
adcx rbx, r10
mov r10b, dl; preserving value of x50 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x88 ], r9; spilling x17 to mem
mulx r12, r9, r8; x89, x88<- x1 * arg1[1]
adcx rcx, rax
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x90 ], r12; spilling x89 to mem
mulx rax, r12, r14; x44, x43<- x20 * 0xffffffffffffffff
adox rbp, rbx
setc bl; spill CF x25 to reg (rbx)
clc;
adcx r13, rbp
mov [ rsp + 0x98 ], rax; spilling x44 to mem
mulx rbp, rax, r13; x132, x131<- x105 * 0xffffffffffffffff
seto dl; spill OF x65 to reg (rdx)
mov [ rsp + 0xa0 ], rbp; spilling x132 to mem
mov rbp, 0x0 ; moving imm to reg
dec rbp; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r10, r10b
adox r10, rbp; loading flag
adox r11, r12
mov r10, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r10; 0xffffffffffffffff, swapping with x65, which is currently in rdx
mulx r12, rbp, r13; x134, x133<- x105 * 0xffffffffffffffff
setc dl; spill CF x106 to reg (rdx)
clc;
adcx rax, r12
setc r12b; spill CF x136 to reg (r12)
clc;
adcx r9, rdi
seto dil; spill OF x52 to reg (rdi)
mov byte [ rsp + 0xa8 ], r12b; spilling byte x136 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r10, r10b
adox r10, r12; loading flag
adox rcx, r11
setc r10b; spill CF x93 to reg (r10)
clc;
adcx rbp, r13
seto bpl; spill OF x67 to reg (rbp)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r11, -0x1 ; moving imm to reg
movzx rdx, dl
adox rdx, r11; loading flag
adox rcx, r9
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r9, r12, r15; x15, x14<- x7 * arg1[3]
adcx rax, rcx
mov rdx, r8; x1 to rdx
mulx r8, rcx, [ rsi + 0x10 ]; x87, x86<- x1 * arg1[2]
mov r11, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, r11; 0xfdc1767ae2ffffff, swapping with x1, which is currently in rdx
mov [ rsp + 0xb0 ], r8; spilling x87 to mem
mov [ rsp + 0xb8 ], r9; spilling x15 to mem
mulx r8, r9, r14; x42, x41<- x20 * 0xfdc1767ae2ffffff
setc dl; spill CF x151 to reg (rdx)
clc;
mov [ rsp + 0xc0 ], r8; spilling x42 to mem
mov r8, -0x1 ; moving imm to reg
movzx rbx, bl
adcx rbx, r8; loading flag
adcx r12, [ rsp + 0x88 ]
setc bl; spill CF x27 to reg (rbx)
clc;
movzx rdi, dil
adcx rdi, r8; loading flag
adcx r9, [ rsp + 0x98 ]
mov rdi, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rdi; 0xffffffffffffffff, swapping with x151, which is currently in rdx
mov byte [ rsp + 0xc8 ], bl; spilling byte x27 to mem
mulx r8, rbx, r13; x130, x129<- x105 * 0xffffffffffffffff
mov rdx, [ rsi + 0x18 ]; load m64 x3 to register64
mov [ rsp + 0xd0 ], r8; spilling x130 to mem
setc r8b; spill CF x54 to reg (r8)
clc;
mov [ rsp + 0xd8 ], rdx; spilling x3 to mem
mov rdx, -0x1 ; moving imm to reg
movzx r10, r10b
adcx r10, rdx; loading flag
adcx rcx, [ rsp + 0x90 ]
setc r10b; spill CF x95 to reg (r10)
clc;
adcx rax, [ rsp + 0x70 ]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov byte [ rsp + 0xe0 ], r10b; spilling byte x95 to mem
mov byte [ rsp + 0xe8 ], r8b; spilling byte x54 to mem
mulx r10, r8, rax; x221, x220<- x192 * 0xffffffffffffffff
setc dl; spill CF x193 to reg (rdx)
clc;
mov [ rsp + 0xf0 ], r10; spilling x221 to mem
mov r10, -0x1 ; moving imm to reg
movzx rbp, bpl
adcx rbp, r10; loading flag
adcx r12, r9
setc bpl; spill CF x69 to reg (rbp)
movzx r9, byte [ rsp + 0xa8 ]; load byte memx136 to register64
clc;
adcx r9, r10; loading flag
adcx rbx, [ rsp + 0xa0 ]
adox rcx, r12
seto r9b; spill OF x110 to reg (r9)
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
movzx rdi, dil
adox rdi, r12; loading flag
adox rcx, rbx
mov dil, dl; preserving value of x193 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx rbx, r10, r15; x13, x12<- x7 * arg1[4]
seto dl; spill OF x153 to reg (rdx)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r8, rax
mov r8b, dl; preserving value of x153 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0xf8 ], rbx; spilling x13 to mem
mulx r12, rbx, [ rsp + 0xd8 ]; x265, x264<- x3 * arg1[0]
setc dl; spill CF x138 to reg (rdx)
clc;
mov [ rsp + 0x100 ], r12; spilling x265 to mem
mov r12, -0x1 ; moving imm to reg
movzx rdi, dil
adcx rdi, r12; loading flag
adcx rcx, [ rsp + 0x48 ]
mov rdi, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, rdi; 0x7bc65c783158aea3, swapping with x138, which is currently in rdx
mov byte [ rsp + 0x108 ], r8b; spilling byte x153 to mem
mulx r12, r8, r14; x40, x39<- x20 * 0x7bc65c783158aea3
setc dl; spill CF x195 to reg (rdx)
mov [ rsp + 0x110 ], r12; spilling x40 to mem
movzx r12, byte [ rsp + 0xc8 ]; load byte memx27 to register64
clc;
mov byte [ rsp + 0x118 ], dil; spilling byte x138 to mem
mov rdi, -0x1 ; moving imm to reg
adcx r12, rdi; loading flag
adcx r10, [ rsp + 0xb8 ]
mov r12, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rax; x192, swapping with x195, which is currently in rdx
mov byte [ rsp + 0x120 ], al; spilling byte x195 to mem
mulx rdi, rax, r12; x219, x218<- x192 * 0xffffffffffffffff
setc r12b; spill CF x29 to reg (r12)
clc;
adcx rax, [ rsp + 0xf0 ]
mov byte [ rsp + 0x128 ], r12b; spilling byte x29 to mem
setc r12b; spill CF x223 to reg (r12)
mov [ rsp + 0x130 ], rdi; spilling x219 to mem
movzx rdi, byte [ rsp + 0xe8 ]; load byte memx54 to register64
clc;
mov byte [ rsp + 0x138 ], r9b; spilling byte x110 to mem
mov r9, -0x1 ; moving imm to reg
adcx rdi, r9; loading flag
adcx r8, [ rsp + 0xc0 ]
mov rdi, rdx; preserving value of x192 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov byte [ rsp + 0x140 ], r12b; spilling byte x223 to mem
mulx r9, r12, r11; x85, x84<- x1 * arg1[3]
adox rax, rcx
seto dl; spill OF x238 to reg (rdx)
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, rax
mov rax, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbx; x279, swapping with x238, which is currently in rdx
mov byte [ rsp + 0x148 ], bl; spilling byte x238 to mem
mulx rcx, rbx, rax; x308, x307<- x279 * 0xffffffffffffffff
mov [ rsp + 0x150 ], rcx; spilling x308 to mem
mov [ rsp + 0x158 ], r9; spilling x85 to mem
mulx rcx, r9, rax; x306, x305<- x279 * 0xffffffffffffffff
setc al; spill CF x56 to reg (rax)
mov [ rsp + 0x160 ], rcx; spilling x306 to mem
movzx rcx, byte [ rsp + 0xe0 ]; load byte memx95 to register64
clc;
mov [ rsp + 0x168 ], r9; spilling x305 to mem
mov r9, -0x1 ; moving imm to reg
adcx rcx, r9; loading flag
adcx r12, [ rsp + 0xb0 ]
mov rcx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rcx; 0xffffffffffffffff, swapping with x279, which is currently in rdx
mov byte [ rsp + 0x170 ], al; spilling byte x56 to mem
mulx r9, rax, rdi; x217, x216<- x192 * 0xffffffffffffffff
mov rdx, [ rsi + 0x20 ]; load m64 x4 to register64
mov [ rsp + 0x178 ], r9; spilling x217 to mem
setc r9b; spill CF x97 to reg (r9)
clc;
mov [ rsp + 0x180 ], rdx; spilling x4 to mem
mov rdx, -0x1 ; moving imm to reg
movzx rbp, bpl
adcx rbp, rdx; loading flag
adcx r10, r8
mov rbp, 0xfdc1767ae2ffffff ; moving imm to reg
mov rdx, r13; x105 to rdx
mulx r13, r8, rbp; x128, x127<- x105 * 0xfdc1767ae2ffffff
setc bpl; spill CF x71 to reg (rbp)
clc;
adcx rbx, rcx
setc bl; spill CF x323 to reg (rbx)
mov [ rsp + 0x188 ], r13; spilling x128 to mem
movzx r13, byte [ rsp + 0x138 ]; load byte memx110 to register64
clc;
mov byte [ rsp + 0x190 ], bpl; spilling byte x71 to mem
mov rbp, -0x1 ; moving imm to reg
adcx r13, rbp; loading flag
adcx r10, r12
setc r13b; spill CF x112 to reg (r13)
movzx r12, byte [ rsp + 0x118 ]; load byte memx138 to register64
clc;
adcx r12, rbp; loading flag
adcx r8, [ rsp + 0xd0 ]
setc r12b; spill CF x140 to reg (r12)
movzx rbp, byte [ rsp + 0x140 ]; load byte memx223 to register64
clc;
mov byte [ rsp + 0x198 ], r13b; spilling byte x112 to mem
mov r13, -0x1 ; moving imm to reg
adcx rbp, r13; loading flag
adcx rax, [ rsp + 0x130 ]
mov rbp, rdx; preserving value of x105 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov byte [ rsp + 0x1a0 ], r12b; spilling byte x140 to mem
mulx r13, r12, r11; x83, x82<- x1 * arg1[4]
setc dl; spill CF x225 to reg (rdx)
clc;
mov [ rsp + 0x1a8 ], r13; spilling x83 to mem
mov r13, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, r13; loading flag
adcx r12, [ rsp + 0x158 ]
seto r9b; spill OF x280 to reg (r9)
movzx r13, byte [ rsp + 0x108 ]; load byte memx153 to register64
mov byte [ rsp + 0x1b0 ], dl; spilling byte x225 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r13, rdx; loading flag
adox r10, r8
mov r13, [ rsp + 0x150 ]; load m64 x308 to register64
setc r8b; spill CF x99 to reg (r8)
clc;
adcx r13, [ rsp + 0x168 ]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov byte [ rsp + 0x1b8 ], r8b; spilling byte x99 to mem
mov [ rsp + 0x1c0 ], r12; spilling x98 to mem
mulx r8, r12, [ rsp + 0x180 ]; x352, x351<- x4 * arg1[0]
setc dl; spill CF x310 to reg (rdx)
mov [ rsp + 0x1c8 ], r8; spilling x352 to mem
movzx r8, byte [ rsp + 0x120 ]; load byte memx195 to register64
clc;
mov [ rsp + 0x1d0 ], r12; spilling x351 to mem
mov r12, -0x1 ; moving imm to reg
adcx r8, r12; loading flag
adcx r10, [ rsp + 0x40 ]
mov r8b, dl; preserving value of x310 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x1d8 ], r13; spilling x309 to mem
mulx r12, r13, r15; x11, x10<- x7 * arg1[5]
seto dl; spill OF x155 to reg (rdx)
mov byte [ rsp + 0x1e0 ], r8b; spilling byte x310 to mem
movzx r8, byte [ rsp + 0x148 ]; load byte memx238 to register64
mov [ rsp + 0x1e8 ], r12; spilling x11 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
adox r8, r12; loading flag
adox r10, rax
mov r8b, dl; preserving value of x155 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx rax, r12, [ rsp + 0xd8 ]; x263, x262<- x3 * arg1[1]
setc dl; spill CF x197 to reg (rdx)
clc;
adcx r12, [ rsp + 0x100 ]
mov [ rsp + 0x1f0 ], rax; spilling x263 to mem
mov rax, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, r14; x20, swapping with x197, which is currently in rdx
mov byte [ rsp + 0x1f8 ], r14b; spilling byte x197 to mem
mov byte [ rsp + 0x200 ], r8b; spilling byte x155 to mem
mulx r14, r8, rax; x38, x37<- x20 * 0x6cfc5fd681c52056
setc al; spill CF x267 to reg (rax)
clc;
mov [ rsp + 0x208 ], r14; spilling x38 to mem
mov r14, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, r14; loading flag
adcx r10, r12
setc r9b; spill CF x282 to reg (r9)
clc;
movzx rbx, bl
adcx rbx, r14; loading flag
adcx r10, [ rsp + 0x1d8 ]
seto bl; spill OF x240 to reg (rbx)
movzx r12, byte [ rsp + 0x170 ]; load byte memx56 to register64
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
adox r12, r14; loading flag
adox r8, [ rsp + 0x110 ]
setc r12b; spill CF x325 to reg (r12)
clc;
adcx r10, [ rsp + 0x1d0 ]
mov r14, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, rbp; x105, swapping with x20, which is currently in rdx
mov byte [ rsp + 0x210 ], r12b; spilling byte x325 to mem
mov byte [ rsp + 0x218 ], r9b; spilling byte x282 to mem
mulx r12, r9, r14; x126, x125<- x105 * 0x7bc65c783158aea3
setc r14b; spill CF x367 to reg (r14)
mov [ rsp + 0x220 ], r12; spilling x126 to mem
movzx r12, byte [ rsp + 0x128 ]; load byte memx29 to register64
clc;
mov byte [ rsp + 0x228 ], al; spilling byte x267 to mem
mov rax, -0x1 ; moving imm to reg
adcx r12, rax; loading flag
adcx r13, [ rsp + 0xf8 ]
mov r12, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r12; 0xffffffffffffffff, swapping with x105, which is currently in rdx
mov byte [ rsp + 0x230 ], r14b; spilling byte x367 to mem
mulx rax, r14, r10; x395, x394<- x366 * 0xffffffffffffffff
setc dl; spill CF x31 to reg (rdx)
mov [ rsp + 0x238 ], rax; spilling x395 to mem
movzx rax, byte [ rsp + 0x190 ]; load byte memx71 to register64
clc;
mov byte [ rsp + 0x240 ], bl; spilling byte x240 to mem
mov rbx, -0x1 ; moving imm to reg
adcx rax, rbx; loading flag
adcx r13, r8
mov rax, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, rdi; x192, swapping with x31, which is currently in rdx
mulx r8, rbx, rax; x215, x214<- x192 * 0xfdc1767ae2ffffff
setc al; spill CF x73 to reg (rax)
clc;
adcx r14, r10
setc r14b; spill CF x410 to reg (r14)
mov [ rsp + 0x248 ], r8; spilling x215 to mem
movzx r8, byte [ rsp + 0x198 ]; load byte memx112 to register64
clc;
mov byte [ rsp + 0x250 ], al; spilling byte x73 to mem
mov rax, -0x1 ; moving imm to reg
adcx r8, rax; loading flag
adcx r13, [ rsp + 0x1c0 ]
mov r8, rdx; preserving value of x192 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov byte [ rsp + 0x258 ], r14b; spilling byte x410 to mem
mulx rax, r14, [ rsp + 0xd8 ]; x261, x260<- x3 * arg1[2]
setc dl; spill CF x114 to reg (rdx)
mov [ rsp + 0x260 ], rax; spilling x261 to mem
movzx rax, byte [ rsp + 0x1a0 ]; load byte memx140 to register64
clc;
mov [ rsp + 0x268 ], r14; spilling x260 to mem
mov r14, -0x1 ; moving imm to reg
adcx rax, r14; loading flag
adcx r9, [ rsp + 0x188 ]
seto al; spill OF x58 to reg (rax)
movzx r14, byte [ rsp + 0x1b0 ]; load byte memx225 to register64
mov byte [ rsp + 0x270 ], dl; spilling byte x114 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r14, rdx; loading flag
adox rbx, [ rsp + 0x178 ]
mov r14, 0x2341f27177344 ; moving imm to reg
mov rdx, rbp; x20 to rdx
mulx rdx, rbp, r14; x36, x35<- x20 * 0x2341f27177344
mov r14, rdx; preserving value of x36 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x278 ], rbp; spilling x35 to mem
mov byte [ rsp + 0x280 ], al; spilling byte x58 to mem
mulx rbp, rax, [ rsp + 0x180 ]; x350, x349<- x4 * arg1[1]
setc dl; spill CF x142 to reg (rdx)
mov [ rsp + 0x288 ], r14; spilling x36 to mem
movzx r14, byte [ rsp + 0x200 ]; load byte memx155 to register64
clc;
mov [ rsp + 0x290 ], rbp; spilling x350 to mem
mov rbp, -0x1 ; moving imm to reg
adcx r14, rbp; loading flag
adcx r13, r9
xchg rdx, r15; x7, swapping with x142, which is currently in rdx
mulx rdx, r14, [ rsi + 0x30 ]; x9, x8<- x7 * arg1[6]
seto r9b; spill OF x227 to reg (r9)
movzx rbp, byte [ rsp + 0x1f8 ]; load byte memx197 to register64
mov [ rsp + 0x298 ], rdx; spilling x9 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbp, rdx; loading flag
adox r13, [ rsp + 0x38 ]
mov rbp, 0xffffffffffffffff ; moving imm to reg
mov rdx, rbp; 0xffffffffffffffff to rdx
mov byte [ rsp + 0x2a0 ], r9b; spilling byte x227 to mem
mulx rbp, r9, rcx; x304, x303<- x279 * 0xffffffffffffffff
setc dl; spill CF x157 to reg (rdx)
mov byte [ rsp + 0x2a8 ], r15b; spilling byte x142 to mem
movzx r15, byte [ rsp + 0x240 ]; load byte memx240 to register64
clc;
mov [ rsp + 0x2b0 ], rbp; spilling x304 to mem
mov rbp, -0x1 ; moving imm to reg
adcx r15, rbp; loading flag
adcx r13, rbx
setc r15b; spill CF x242 to reg (r15)
clc;
movzx rdi, dil
adcx rdi, rbp; loading flag
adcx r14, [ rsp + 0x1e8 ]
mov rdi, [ rsp + 0x268 ]; load m64 x260 to register64
setc bl; spill CF x33 to reg (rbx)
movzx rbp, byte [ rsp + 0x228 ]; load byte memx267 to register64
clc;
mov byte [ rsp + 0x2b8 ], r15b; spilling byte x242 to mem
mov r15, -0x1 ; moving imm to reg
adcx rbp, r15; loading flag
adcx rdi, [ rsp + 0x1f0 ]
setc bpl; spill CF x269 to reg (rbp)
clc;
adcx rax, [ rsp + 0x1c8 ]
setc r15b; spill CF x354 to reg (r15)
mov byte [ rsp + 0x2c0 ], bpl; spilling byte x269 to mem
movzx rbp, byte [ rsp + 0x218 ]; load byte memx282 to register64
clc;
mov byte [ rsp + 0x2c8 ], bl; spilling byte x33 to mem
mov rbx, -0x1 ; moving imm to reg
adcx rbp, rbx; loading flag
adcx r13, rdi
mov rbp, [ rsp + 0x208 ]; load m64 x38 to register64
setc dil; spill CF x284 to reg (rdi)
movzx rbx, byte [ rsp + 0x280 ]; load byte memx58 to register64
clc;
mov byte [ rsp + 0x2d0 ], dl; spilling byte x157 to mem
mov rdx, -0x1 ; moving imm to reg
adcx rbx, rdx; loading flag
adcx rbp, [ rsp + 0x278 ]
setc bl; spill CF x60 to reg (rbx)
movzx rdx, byte [ rsp + 0x1e0 ]; load byte memx310 to register64
clc;
mov byte [ rsp + 0x2d8 ], dil; spilling byte x284 to mem
mov rdi, -0x1 ; moving imm to reg
adcx rdx, rdi; loading flag
adcx r9, [ rsp + 0x160 ]
setc dl; spill CF x312 to reg (rdx)
movzx rdi, byte [ rsp + 0x210 ]; load byte memx325 to register64
clc;
mov byte [ rsp + 0x2e0 ], bl; spilling byte x60 to mem
mov rbx, -0x1 ; moving imm to reg
adcx rdi, rbx; loading flag
adcx r13, r9
mov dil, dl; preserving value of x312 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx r9, rbx, r11; x81, x80<- x1 * arg1[5]
setc dl; spill CF x327 to reg (rdx)
mov [ rsp + 0x2e8 ], r9; spilling x81 to mem
movzx r9, byte [ rsp + 0x250 ]; load byte memx73 to register64
clc;
mov byte [ rsp + 0x2f0 ], r15b; spilling byte x354 to mem
mov r15, -0x1 ; moving imm to reg
adcx r9, r15; loading flag
adcx r14, rbp
mov r9, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r10; x366, swapping with x327, which is currently in rdx
mulx rbp, r15, r9; x393, x392<- x366 * 0xffffffffffffffff
seto r9b; spill OF x199 to reg (r9)
mov [ rsp + 0x2f8 ], rbp; spilling x393 to mem
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, [ rsp + 0x238 ]
setc bpl; spill CF x75 to reg (rbp)
mov byte [ rsp + 0x300 ], r10b; spilling byte x327 to mem
movzx r10, byte [ rsp + 0x230 ]; load byte memx367 to register64
clc;
mov byte [ rsp + 0x308 ], r9b; spilling byte x199 to mem
mov r9, -0x1 ; moving imm to reg
adcx r10, r9; loading flag
adcx r13, rax
setc r10b; spill CF x369 to reg (r10)
movzx rax, byte [ rsp + 0x258 ]; load byte memx410 to register64
clc;
adcx rax, r9; loading flag
adcx r13, r15
mov rax, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, rax; 0xfdc1767ae2ffffff, swapping with x366, which is currently in rdx
mulx r15, r9, rcx; x302, x301<- x279 * 0xfdc1767ae2ffffff
setc dl; spill CF x412 to reg (rdx)
clc;
mov [ rsp + 0x310 ], r13; spilling x411 to mem
mov r13, -0x1 ; moving imm to reg
movzx rdi, dil
adcx rdi, r13; loading flag
adcx r9, [ rsp + 0x2b0 ]
seto dil; spill OF x397 to reg (rdi)
movzx r13, byte [ rsp + 0x1b8 ]; load byte memx99 to register64
mov [ rsp + 0x318 ], r15; spilling x302 to mem
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r13, r15; loading flag
adox rbx, [ rsp + 0x1a8 ]
mov r13, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, r13; 0x7bc65c783158aea3, swapping with x412, which is currently in rdx
mov byte [ rsp + 0x320 ], bpl; spilling byte x75 to mem
mulx r15, rbp, r8; x213, x212<- x192 * 0x7bc65c783158aea3
seto dl; spill OF x101 to reg (rdx)
mov [ rsp + 0x328 ], r15; spilling x213 to mem
movzx r15, byte [ rsp + 0x270 ]; load byte memx114 to register64
mov byte [ rsp + 0x330 ], r13b; spilling byte x412 to mem
mov r13, -0x1 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r13, -0x1 ; moving imm to reg
adox r15, r13; loading flag
adox r14, rbx
mov r15, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, r15; 0x6cfc5fd681c52056, swapping with x101, which is currently in rdx
mulx rbx, r13, r12; x124, x123<- x105 * 0x6cfc5fd681c52056
setc dl; spill CF x314 to reg (rdx)
mov [ rsp + 0x338 ], rbx; spilling x124 to mem
movzx rbx, byte [ rsp + 0x2a8 ]; load byte memx142 to register64
clc;
mov byte [ rsp + 0x340 ], r15b; spilling byte x101 to mem
mov r15, -0x1 ; moving imm to reg
adcx rbx, r15; loading flag
adcx r13, [ rsp + 0x220 ]
mov bl, dl; preserving value of x314 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov byte [ rsp + 0x348 ], dil; spilling byte x397 to mem
mulx r15, rdi, [ rsp + 0x180 ]; x348, x347<- x4 * arg1[2]
seto dl; spill OF x116 to reg (rdx)
mov byte [ rsp + 0x350 ], bl; spilling byte x314 to mem
movzx rbx, byte [ rsp + 0x2f0 ]; load byte memx354 to register64
mov [ rsp + 0x358 ], r15; spilling x348 to mem
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbx, r15; loading flag
adox rdi, [ rsp + 0x290 ]
setc bl; spill CF x144 to reg (rbx)
movzx r15, byte [ rsp + 0x2d0 ]; load byte memx157 to register64
clc;
mov byte [ rsp + 0x360 ], dl; spilling byte x116 to mem
mov rdx, -0x1 ; moving imm to reg
adcx r15, rdx; loading flag
adcx r14, r13
seto r15b; spill OF x356 to reg (r15)
movzx r13, byte [ rsp + 0x308 ]; load byte memx199 to register64
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
adox r13, rdx; loading flag
adox r14, [ rsp + 0x20 ]
movzx r13, byte [ rsp + 0x2c8 ]; x34, copying x33 here, cause x33 is needed in a reg for other than x34, namely all: , x34, size: 1
mov rdx, [ rsp + 0x298 ]; load m64 x9 to register64
lea r13, [ r13 + rdx ]; r8/64 + m8
setc dl; spill CF x159 to reg (rdx)
mov byte [ rsp + 0x368 ], r15b; spilling byte x356 to mem
movzx r15, byte [ rsp + 0x2a0 ]; load byte memx227 to register64
clc;
mov byte [ rsp + 0x370 ], bl; spilling byte x144 to mem
mov rbx, -0x1 ; moving imm to reg
adcx r15, rbx; loading flag
adcx rbp, [ rsp + 0x248 ]
mov r15b, dl; preserving value of x159 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x378 ], r13; spilling x34 to mem
mulx rbx, r13, [ rsp + 0xd8 ]; x259, x258<- x3 * arg1[3]
seto dl; spill OF x201 to reg (rdx)
mov byte [ rsp + 0x380 ], r15b; spilling byte x159 to mem
movzx r15, byte [ rsp + 0x2c0 ]; load byte memx269 to register64
mov [ rsp + 0x388 ], rbx; spilling x259 to mem
mov rbx, -0x1 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbx, -0x1 ; moving imm to reg
adox r15, rbx; loading flag
adox r13, [ rsp + 0x260 ]
mov r15b, dl; preserving value of x201 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mulx r11, rbx, r11; x79, x78<- x1 * arg1[6]
seto dl; spill OF x271 to reg (rdx)
mov [ rsp + 0x390 ], r11; spilling x79 to mem
movzx r11, byte [ rsp + 0x2b8 ]; load byte memx242 to register64
mov byte [ rsp + 0x398 ], r15b; spilling byte x201 to mem
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r11, r15; loading flag
adox r14, rbp
setc r11b; spill CF x229 to reg (r11)
movzx rbp, byte [ rsp + 0x2d8 ]; load byte memx284 to register64
clc;
adcx rbp, r15; loading flag
adcx r14, r13
mov rbp, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbp; 0xffffffffffffffff, swapping with x271, which is currently in rdx
mulx r13, r15, rax; x391, x390<- x366 * 0xffffffffffffffff
seto dl; spill OF x244 to reg (rdx)
mov [ rsp + 0x3a0 ], r13; spilling x391 to mem
movzx r13, byte [ rsp + 0x300 ]; load byte memx327 to register64
mov byte [ rsp + 0x3a8 ], r11b; spilling byte x229 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
adox r13, r11; loading flag
adox r14, r9
mov r13, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, r13; 0x6cfc5fd681c52056, swapping with x244, which is currently in rdx
mulx r9, r11, r8; x211, x210<- x192 * 0x6cfc5fd681c52056
setc dl; spill CF x286 to reg (rdx)
clc;
mov [ rsp + 0x3b0 ], r9; spilling x211 to mem
mov r9, -0x1 ; moving imm to reg
movzx r10, r10b
adcx r10, r9; loading flag
adcx r14, rdi
setc r10b; spill CF x371 to reg (r10)
movzx rdi, byte [ rsp + 0x348 ]; load byte memx397 to register64
clc;
adcx rdi, r9; loading flag
adcx r15, [ rsp + 0x2f8 ]
mov dil, dl; preserving value of x286 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov byte [ rsp + 0x3b8 ], r10b; spilling byte x371 to mem
mulx r9, r10, [ rsp + 0xd8 ]; x257, x256<- x3 * arg1[4]
setc dl; spill CF x399 to reg (rdx)
mov [ rsp + 0x3c0 ], r9; spilling x257 to mem
movzx r9, byte [ rsp + 0x330 ]; load byte memx412 to register64
clc;
mov byte [ rsp + 0x3c8 ], dil; spilling byte x286 to mem
mov rdi, -0x1 ; moving imm to reg
adcx r9, rdi; loading flag
adcx r14, r15
movzx r9, byte [ rsp + 0x2e0 ]; x61, copying x60 here, cause x60 is needed in a reg for other than x61, namely all: , x61, size: 1
mov r15, [ rsp + 0x288 ]; load m64 x36 to register64
lea r9, [ r9 + r15 ]; r8/64 + m8
setc r15b; spill CF x414 to reg (r15)
clc;
movzx rbp, bpl
adcx rbp, rdi; loading flag
adcx r10, [ rsp + 0x388 ]
setc bpl; spill CF x273 to reg (rbp)
movzx rdi, byte [ rsp + 0x320 ]; load byte memx75 to register64
clc;
mov [ rsp + 0x3d0 ], r14; spilling x413 to mem
mov r14, -0x1 ; moving imm to reg
adcx rdi, r14; loading flag
adcx r9, [ rsp + 0x378 ]
mov dil, dl; preserving value of x399 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov byte [ rsp + 0x3d8 ], bpl; spilling byte x273 to mem
mulx r14, rbp, [ rsp + 0x180 ]; x346, x345<- x4 * arg1[3]
setc dl; spill CF x77 to reg (rdx)
mov [ rsp + 0x3e0 ], r14; spilling x346 to mem
movzx r14, byte [ rsp + 0x340 ]; load byte memx101 to register64
clc;
mov byte [ rsp + 0x3e8 ], r15b; spilling byte x414 to mem
mov r15, -0x1 ; moving imm to reg
adcx r14, r15; loading flag
adcx rbx, [ rsp + 0x2e8 ]
mov r14, 0x2341f27177344 ; moving imm to reg
xchg rdx, r12; x105, swapping with x77, which is currently in rdx
mulx rdx, r15, r14; x122, x121<- x105 * 0x2341f27177344
setc r14b; spill CF x103 to reg (r14)
mov byte [ rsp + 0x3f0 ], r12b; spilling byte x77 to mem
movzx r12, byte [ rsp + 0x360 ]; load byte memx116 to register64
clc;
mov byte [ rsp + 0x3f8 ], dil; spilling byte x399 to mem
mov rdi, -0x1 ; moving imm to reg
adcx r12, rdi; loading flag
adcx r9, rbx
setc r12b; spill CF x118 to reg (r12)
movzx rbx, byte [ rsp + 0x370 ]; load byte memx144 to register64
clc;
adcx rbx, rdi; loading flag
adcx r15, [ rsp + 0x338 ]
setc bl; spill CF x146 to reg (rbx)
movzx rdi, byte [ rsp + 0x380 ]; load byte memx159 to register64
clc;
mov byte [ rsp + 0x400 ], r12b; spilling byte x118 to mem
mov r12, -0x1 ; moving imm to reg
adcx rdi, r12; loading flag
adcx r9, r15
setc dil; spill CF x161 to reg (rdi)
movzx r15, byte [ rsp + 0x398 ]; load byte memx201 to register64
clc;
adcx r15, r12; loading flag
adcx r9, [ rsp + 0x18 ]
setc r15b; spill CF x203 to reg (r15)
movzx r12, byte [ rsp + 0x3a8 ]; load byte memx229 to register64
clc;
mov byte [ rsp + 0x408 ], dil; spilling byte x161 to mem
mov rdi, -0x1 ; moving imm to reg
adcx r12, rdi; loading flag
adcx r11, [ rsp + 0x328 ]
seto r12b; spill OF x329 to reg (r12)
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdi, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, rdi; loading flag
adox r9, r11
mov r13, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, r13; 0x7bc65c783158aea3, swapping with x122, which is currently in rdx
mulx r11, rdi, rcx; x300, x299<- x279 * 0x7bc65c783158aea3
seto dl; spill OF x246 to reg (rdx)
mov [ rsp + 0x410 ], r11; spilling x300 to mem
movzx r11, byte [ rsp + 0x368 ]; load byte memx356 to register64
mov byte [ rsp + 0x418 ], r15b; spilling byte x203 to mem
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r11, r15; loading flag
adox rbp, [ rsp + 0x358 ]
mov r11, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, r11; 0xfdc1767ae2ffffff, swapping with x246, which is currently in rdx
mov byte [ rsp + 0x420 ], r11b; spilling byte x246 to mem
mulx r15, r11, rax; x389, x388<- x366 * 0xfdc1767ae2ffffff
setc dl; spill CF x231 to reg (rdx)
mov [ rsp + 0x428 ], r15; spilling x389 to mem
movzx r15, byte [ rsp + 0x3c8 ]; load byte memx286 to register64
clc;
mov byte [ rsp + 0x430 ], r14b; spilling byte x103 to mem
mov r14, -0x1 ; moving imm to reg
adcx r15, r14; loading flag
adcx r9, r10
seto r15b; spill OF x358 to reg (r15)
movzx r10, byte [ rsp + 0x350 ]; load byte memx314 to register64
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
adox r10, r14; loading flag
adox rdi, [ rsp + 0x318 ]
seto r10b; spill OF x316 to reg (r10)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, r14; loading flag
adox r9, rdi
movzx r12, bl; x147, copying x146 here, cause x146 is needed in a reg for other than x147, namely all: , x147, size: 1
lea r12, [ r12 + r13 ]
setc r13b; spill CF x288 to reg (r13)
movzx rbx, byte [ rsp + 0x3b8 ]; load byte memx371 to register64
clc;
adcx rbx, r14; loading flag
adcx r9, rbp
mov rbx, 0x2341f27177344 ; moving imm to reg
xchg rdx, r8; x192, swapping with x231, which is currently in rdx
mulx rdx, rbp, rbx; x209, x208<- x192 * 0x2341f27177344
setc dil; spill CF x373 to reg (rdi)
movzx r14, byte [ rsp + 0x3f8 ]; load byte memx399 to register64
clc;
mov rbx, -0x1 ; moving imm to reg
adcx r14, rbx; loading flag
adcx r11, [ rsp + 0x3a0 ]
movzx r14, byte [ rsp + 0x430 ]; x104, copying x103 here, cause x103 is needed in a reg for other than x104, namely all: , x104, size: 1
mov rbx, [ rsp + 0x390 ]; load m64 x79 to register64
lea r14, [ r14 + rbx ]; r8/64 + m8
seto bl; spill OF x331 to reg (rbx)
mov [ rsp + 0x438 ], rdx; spilling x209 to mem
movzx rdx, byte [ rsp + 0x400 ]; load byte memx118 to register64
mov byte [ rsp + 0x440 ], dil; spilling byte x373 to mem
mov rdi, 0x0 ; moving imm to reg
dec rdi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
mov byte [ rsp + 0x448 ], r15b; spilling byte x358 to mem
movzx r15, byte [ rsp + 0x3f0 ]; load byte memx77 to register64
adox rdx, rdi; loading flag
adox r14, r15
setc r15b; spill CF x401 to reg (r15)
movzx rdx, byte [ rsp + 0x408 ]; load byte memx161 to register64
clc;
adcx rdx, rdi; loading flag
adcx r14, r12
mov rdx, 0x6cfc5fd681c52056 ; moving imm to reg
mulx r12, rdi, rcx; x298, x297<- x279 * 0x6cfc5fd681c52056
setc dl; spill CF x163 to reg (rdx)
clc;
mov [ rsp + 0x450 ], r12; spilling x298 to mem
mov r12, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, r12; loading flag
adcx rbp, [ rsp + 0x3b0 ]
setc r8b; spill CF x233 to reg (r8)
movzx r12, byte [ rsp + 0x3e8 ]; load byte memx414 to register64
clc;
mov byte [ rsp + 0x458 ], r15b; spilling byte x401 to mem
mov r15, -0x1 ; moving imm to reg
adcx r12, r15; loading flag
adcx r9, r11
setc r12b; spill CF x416 to reg (r12)
movzx r11, byte [ rsp + 0x418 ]; load byte memx203 to register64
clc;
adcx r11, r15; loading flag
adcx r14, [ rsp + 0x8 ]
seto r11b; spill OF x120 to reg (r11)
movzx r15, byte [ rsp + 0x420 ]; load byte memx246 to register64
mov [ rsp + 0x460 ], r9; spilling x415 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, r9; loading flag
adox r14, rbp
mov r15b, dl; preserving value of x163 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx rbp, r9, [ rsp + 0xd8 ]; x255, x254<- x3 * arg1[5]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov byte [ rsp + 0x468 ], r12b; spilling byte x416 to mem
mov [ rsp + 0x470 ], rbp; spilling x255 to mem
mulx r12, rbp, [ rsp + 0x180 ]; x344, x343<- x4 * arg1[4]
movzx rdx, r15b; x164, copying x163 here, cause x163 is needed in a reg for other than x164, namely all: , x164, size: 1
movzx r11, r11b
lea rdx, [ rdx + r11 ]
seto r11b; spill OF x248 to reg (r11)
movzx r15, byte [ rsp + 0x3d8 ]; load byte memx273 to register64
mov [ rsp + 0x478 ], r12; spilling x344 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, r12; loading flag
adox r9, [ rsp + 0x3c0 ]
seto r15b; spill OF x275 to reg (r15)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, r12; loading flag
adox r14, r9
mov r13, [ rsp + 0x60 ]; x206, copying x191 here, cause x191 is needed in a reg for other than x206, namely all: , x206--x207, size: 1
adcx r13, rdx
setc dl; spill CF x207 to reg (rdx)
clc;
movzx r10, r10b
adcx r10, r12; loading flag
adcx rdi, [ rsp + 0x410 ]
seto r10b; spill OF x290 to reg (r10)
movzx r9, byte [ rsp + 0x448 ]; load byte memx358 to register64
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
adox r9, r12; loading flag
adox rbp, [ rsp + 0x3e0 ]
seto r9b; spill OF x360 to reg (r9)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, r12; loading flag
adox r14, rdi
setc bl; spill CF x318 to reg (rbx)
movzx rdi, byte [ rsp + 0x440 ]; load byte memx373 to register64
clc;
adcx rdi, r12; loading flag
adcx r14, rbp
mov rdi, 0x2341f27177344 ; moving imm to reg
xchg rdx, rdi; 0x2341f27177344, swapping with x207, which is currently in rdx
mulx rbp, r12, rax; x383, x382<- x366 * 0x2341f27177344
mov rdx, 0x6cfc5fd681c52056 ; moving imm to reg
mov byte [ rsp + 0x480 ], dil; spilling byte x207 to mem
mov byte [ rsp + 0x488 ], r9b; spilling byte x360 to mem
mulx rdi, r9, rax; x385, x384<- x366 * 0x6cfc5fd681c52056
movzx rdx, r8b; x234, copying x233 here, cause x233 is needed in a reg for other than x234, namely all: , x234, size: 1
mov [ rsp + 0x490 ], rbp; spilling x383 to mem
mov rbp, [ rsp + 0x438 ]; load m64 x209 to register64
lea rdx, [ rdx + rbp ]; r8/64 + m8
mov rbp, 0x2341f27177344 ; moving imm to reg
xchg rdx, rbp; 0x2341f27177344, swapping with x234, which is currently in rdx
mulx rcx, r8, rcx; x296, x295<- x279 * 0x2341f27177344
mov [ rsp + 0x498 ], rcx; spilling x296 to mem
mov rcx, rdx; preserving value of 0x2341f27177344 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x4a0 ], r12; spilling x382 to mem
mov [ rsp + 0x4a8 ], rdi; spilling x385 to mem
mulx r12, rdi, [ rsp + 0x180 ]; x342, x341<- x4 * arg1[5]
setc dl; spill CF x375 to reg (rdx)
clc;
mov rcx, -0x1 ; moving imm to reg
movzx r11, r11b
adcx r11, rcx; loading flag
adcx r13, rbp
mov r11b, dl; preserving value of x375 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mulx rbp, rcx, [ rsp + 0xd8 ]; x253, x252<- x3 * arg1[6]
setc dl; spill CF x250 to reg (rdx)
clc;
mov byte [ rsp + 0x4b0 ], r11b; spilling byte x375 to mem
mov r11, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, r11; loading flag
adcx rcx, [ rsp + 0x470 ]
mov r15, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, r15; 0x7bc65c783158aea3, swapping with x250, which is currently in rdx
mulx rax, r11, rax; x387, x386<- x366 * 0x7bc65c783158aea3
seto dl; spill OF x333 to reg (rdx)
mov [ rsp + 0x4b8 ], r12; spilling x342 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
movzx r10, r10b
adox r10, r12; loading flag
adox r13, rcx
setc r10b; spill CF x277 to reg (r10)
movzx rcx, byte [ rsp + 0x458 ]; load byte memx401 to register64
clc;
adcx rcx, r12; loading flag
adcx r11, [ rsp + 0x428 ]
seto cl; spill OF x292 to reg (rcx)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, r12; loading flag
adox r8, [ rsp + 0x450 ]
movzx rbx, r10b; x278, copying x277 here, cause x277 is needed in a reg for other than x278, namely all: , x278, size: 1
lea rbx, [ rbx + rbp ]
mov rbp, [ rsi + 0x30 ]; load m64 x6 to register64
seto r10b; spill OF x320 to reg (r10)
movzx r12, byte [ rsp + 0x468 ]; load byte memx416 to register64
mov [ rsp + 0x4c0 ], rbp; spilling x6 to mem
mov rbp, 0x0 ; moving imm to reg
dec rbp; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r12, rbp; loading flag
adox r14, r11
adcx r9, rax
mov r12, [ rsp + 0x4a8 ]; load m64 x385 to register64
mov rax, [ rsp + 0x4a0 ]; x406, copying x382 here, cause x382 is needed in a reg for other than x406, namely all: , x406--x407, size: 1
adcx rax, r12
setc r12b; spill CF x407 to reg (r12)
clc;
movzx rdx, dl
adcx rdx, rbp; loading flag
adcx r13, r8
movzx rdx, r10b; x321, copying x320 here, cause x320 is needed in a reg for other than x321, namely all: , x321, size: 1
mov r11, [ rsp + 0x498 ]; load m64 x296 to register64
lea rdx, [ rdx + r11 ]; r8/64 + m8
movzx r11, r12b; x408, copying x407 here, cause x407 is needed in a reg for other than x408, namely all: , x408, size: 1
mov r8, [ rsp + 0x490 ]; load m64 x383 to register64
lea r11, [ r11 + r8 ]; r8/64 + m8
movzx r8, r15b; x251, copying x250 here, cause x250 is needed in a reg for other than x251, namely all: , x251, size: 1
movzx r10, byte [ rsp + 0x480 ]; load byte memx207 to register64
lea r8, [ r8 + r10 ]; r64+m8
setc r10b; spill CF x335 to reg (r10)
movzx r15, byte [ rsp + 0x488 ]; load byte memx360 to register64
clc;
adcx r15, rbp; loading flag
adcx rdi, [ rsp + 0x478 ]
mov r15, rdx; preserving value of x321 into a new reg
mov rdx, [ rsp + 0x180 ]; saving x4 in rdx.
mulx rdx, r12, [ rsi + 0x30 ]; x340, x339<- x4 * arg1[6]
setc bpl; spill CF x362 to reg (rbp)
clc;
mov [ rsp + 0x4c8 ], r14; spilling x417 to mem
mov r14, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, r14; loading flag
adcx r8, rbx
setc cl; spill CF x294 to reg (rcx)
clc;
movzx r10, r10b
adcx r10, r14; loading flag
adcx r8, r15
movzx rbx, cl; x338, copying x294 here, cause x294 is needed in a reg for other than x338, namely all: , x338, size: 1
mov r10, 0x0 ; moving imm to reg
adcx rbx, r10
clc;
movzx rbp, bpl
adcx rbp, r14; loading flag
adcx r12, [ rsp + 0x4b8 ]
setc r15b; spill CF x364 to reg (r15)
movzx rbp, byte [ rsp + 0x4b0 ]; load byte memx375 to register64
clc;
adcx rbp, r14; loading flag
adcx r13, rdi
adcx r12, r8
movzx rbp, r15b; x365, copying x364 here, cause x364 is needed in a reg for other than x365, namely all: , x365, size: 1
lea rbp, [ rbp + rdx ]
adox r9, r13
mov rdx, [ rsp + 0x4c0 ]; x6 to rdx
mulx rdi, rcx, [ rsi + 0x8 ]; x524, x523<- x6 * arg1[1]
adox rax, r12
adcx rbp, rbx
mov r8, [ rsp + 0x10 ]; load m64 x438 to register64
setc bl; spill CF x381 to reg (rbx)
clc;
adcx r8, [ rsp + 0x310 ]
mov r15, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r8; x453, swapping with x6, which is currently in rdx
mulx r13, r12, r15; x482, x481<- x453 * 0xffffffffffffffff
mov r10, [ rsp + 0x28 ]; load m64 x440 to register64
mov r14, [ rsp + 0x3d0 ]; x455, copying x413 here, cause x413 is needed in a reg for other than x455, namely all: , x455--x456, size: 1
adcx r14, r10
mov [ rsp + 0x4d0 ], rax; spilling x421 to mem
mulx r10, rax, r15; x478, x477<- x453 * 0xffffffffffffffff
adox r11, rbp
mov [ rsp + 0x4d8 ], r11; spilling x423 to mem
mulx rbp, r11, r15; x480, x479<- x453 * 0xffffffffffffffff
setc r15b; spill CF x456 to reg (r15)
clc;
adcx r11, r13
adcx rax, rbp
mov r13, rdx; preserving value of x453 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x4e0 ], rdi; spilling x524 to mem
mulx rbp, rdi, r8; x526, x525<- x6 * arg1[0]
mov rdx, [ rsp + 0x30 ]; load m64 x442 to register64
mov [ rsp + 0x4e8 ], r9; spilling x419 to mem
seto r9b; spill OF x424 to reg (r9)
mov [ rsp + 0x4f0 ], r10; spilling x478 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r15, r15b
adox r15, r10; loading flag
adox rdx, [ rsp + 0x460 ]
setc r15b; spill CF x486 to reg (r15)
clc;
adcx r12, r13
movzx r12, r9b; x425, copying x424 here, cause x424 is needed in a reg for other than x425, namely all: , x425, size: 1
movzx rbx, bl
lea r12, [ r12 + rbx ]
adcx r11, r14
seto bl; spill OF x458 to reg (rbx)
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rdi, r11
mov r14, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r14; 0xffffffffffffffff, swapping with x457, which is currently in rdx
mulx r9, r11, rdi; x567, x566<- x540 * 0xffffffffffffffff
adcx rax, r14
setc r14b; spill CF x501 to reg (r14)
clc;
adcx rcx, rbp
adox rcx, rax
mulx rbp, rax, rdi; x569, x568<- x540 * 0xffffffffffffffff
setc dl; spill CF x528 to reg (rdx)
clc;
adcx r11, rbp
setc bpl; spill CF x571 to reg (rbp)
clc;
adcx rax, rdi
adcx r11, rcx
mov rax, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, r13; x453, swapping with x528, which is currently in rdx
mulx rcx, r10, rax; x476, x475<- x453 * 0xfdc1767ae2ffffff
mov rax, rdx; preserving value of x453 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x4f8 ], r12; spilling x425 to mem
mov [ rsp + 0x500 ], rcx; spilling x476 to mem
mulx r12, rcx, r8; x522, x521<- x6 * arg1[2]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x508 ], r9; spilling x567 to mem
mov byte [ rsp + 0x510 ], bpl; spilling byte x571 to mem
mulx r9, rbp, rdi; x565, x564<- x540 * 0xffffffffffffffff
mov rdx, [ rsp + 0x58 ]; load m64 x444 to register64
mov [ rsp + 0x518 ], r9; spilling x565 to mem
setc r9b; spill CF x586 to reg (r9)
clc;
mov [ rsp + 0x520 ], rbp; spilling x564 to mem
mov rbp, -0x1 ; moving imm to reg
movzx rbx, bl
adcx rbx, rbp; loading flag
adcx rdx, [ rsp + 0x4c8 ]
setc bl; spill CF x460 to reg (rbx)
seto bpl; spill OF x543 to reg (rbp)
mov byte [ rsp + 0x528 ], r9b; spilling byte x586 to mem
mov r9, r11; x600, copying x585 here, cause x585 is needed in a reg for other than x600, namely all: , x616, x600--x601, size: 2
mov [ rsp + 0x530 ], rdx; spilling x459 to mem
mov rdx, 0xffffffffffffffff ; moving imm to reg
sub r9, rdx
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, rdx; loading flag
adox r10, [ rsp + 0x4f0 ]
mov r15, [ rsp + 0x50 ]; load m64 x446 to register64
setc dl; spill CF x601 to reg (rdx)
clc;
mov [ rsp + 0x538 ], r9; spilling x600 to mem
mov r9, -0x1 ; moving imm to reg
movzx rbx, bl
adcx rbx, r9; loading flag
adcx r15, [ rsp + 0x4e8 ]
xchg rdx, r8; x6, swapping with x601, which is currently in rdx
mulx rbx, r9, [ rsi + 0x18 ]; x520, x519<- x6 * arg1[3]
mov [ rsp + 0x540 ], rbx; spilling x520 to mem
setc bl; spill CF x462 to reg (rbx)
clc;
mov [ rsp + 0x548 ], r15; spilling x461 to mem
mov r15, -0x1 ; moving imm to reg
movzx r13, r13b
adcx r13, r15; loading flag
adcx rcx, [ rsp + 0x4e0 ]
adcx r9, r12
seto r13b; spill OF x488 to reg (r13)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, r12; loading flag
adox r10, [ rsp + 0x530 ]
mov r14, [ rsp + 0x520 ]; load m64 x564 to register64
setc r15b; spill CF x532 to reg (r15)
movzx r12, byte [ rsp + 0x510 ]; load byte memx571 to register64
clc;
mov byte [ rsp + 0x550 ], bl; spilling byte x462 to mem
mov rbx, -0x1 ; moving imm to reg
adcx r12, rbx; loading flag
adcx r14, [ rsp + 0x508 ]
seto r12b; spill OF x503 to reg (r12)
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, rbx; loading flag
adox r10, rcx
mov rbp, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, rbp; 0x6cfc5fd681c52056, swapping with x6, which is currently in rdx
mulx rcx, rbx, rax; x472, x471<- x453 * 0x6cfc5fd681c52056
setc dl; spill CF x573 to reg (rdx)
mov [ rsp + 0x558 ], rcx; spilling x472 to mem
movzx rcx, byte [ rsp + 0x528 ]; load byte memx586 to register64
clc;
mov byte [ rsp + 0x560 ], r15b; spilling byte x532 to mem
mov r15, -0x1 ; moving imm to reg
adcx rcx, r15; loading flag
adcx r10, r14
setc cl; spill CF x588 to reg (rcx)
seto r14b; spill OF x545 to reg (r14)
movzx r15, r8b; x601, copying x601 here, cause x601 is needed in a reg for other than x601, namely all: , x602--x603, size: 1
add r15, -0x1
mov r15, r10; x602, copying x587 here, cause x587 is needed in a reg for other than x602, namely all: , x617, x602--x603, size: 2
mov r8, 0xffffffffffffffff ; moving imm to reg
sbb r15, r8
mov r8, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, rdi; x540, swapping with x573, which is currently in rdx
mov [ rsp + 0x568 ], r15; spilling x602 to mem
mov byte [ rsp + 0x570 ], cl; spilling byte x588 to mem
mulx r15, rcx, r8; x563, x562<- x540 * 0xfdc1767ae2ffffff
mov r8, -0x1 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r8, -0x1 ; moving imm to reg
movzx rdi, dil
adox rdi, r8; loading flag
adox rcx, [ rsp + 0x518 ]
mov rdi, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, rdi; 0x7bc65c783158aea3, swapping with x540, which is currently in rdx
mov [ rsp + 0x578 ], rcx; spilling x574 to mem
mulx r8, rcx, rax; x474, x473<- x453 * 0x7bc65c783158aea3
mov [ rsp + 0x580 ], r9; spilling x531 to mem
mov byte [ rsp + 0x588 ], r14b; spilling byte x545 to mem
mulx r9, r14, rdi; x561, x560<- x540 * 0x7bc65c783158aea3
adox r14, r15
xchg rdx, rbp; x6, swapping with 0x7bc65c783158aea3, which is currently in rdx
mulx r15, rbp, [ rsi + 0x20 ]; x518, x517<- x6 * arg1[4]
mov [ rsp + 0x590 ], r9; spilling x561 to mem
setc r9b; spill CF x603 to reg (r9)
clc;
mov [ rsp + 0x598 ], r15; spilling x518 to mem
mov r15, -0x1 ; moving imm to reg
movzx r13, r13b
adcx r13, r15; loading flag
adcx rcx, [ rsp + 0x500 ]
adcx rbx, r8
setc r13b; spill CF x492 to reg (r13)
clc;
movzx r12, r12b
adcx r12, r15; loading flag
adcx rcx, [ rsp + 0x548 ]
seto r12b; spill OF x577 to reg (r12)
movzx r8, byte [ rsp + 0x588 ]; load byte memx545 to register64
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
adox r8, r15; loading flag
adox rcx, [ rsp + 0x580 ]
setc r8b; spill CF x505 to reg (r8)
movzx r15, byte [ rsp + 0x570 ]; load byte memx588 to register64
clc;
mov byte [ rsp + 0x5a0 ], r12b; spilling byte x577 to mem
mov r12, -0x1 ; moving imm to reg
adcx r15, r12; loading flag
adcx rcx, [ rsp + 0x578 ]
mov r15, [ rsp + 0x68 ]; load m64 x448 to register64
seto r12b; spill OF x547 to reg (r12)
mov [ rsp + 0x5a8 ], rcx; spilling x589 to mem
movzx rcx, byte [ rsp + 0x550 ]; load byte memx462 to register64
mov byte [ rsp + 0x5b0 ], r9b; spilling byte x603 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rcx, r9; loading flag
adox r15, [ rsp + 0x4d0 ]
mov rcx, 0x2341f27177344 ; moving imm to reg
xchg rdx, rcx; 0x2341f27177344, swapping with x6, which is currently in rdx
mulx rax, r9, rax; x470, x469<- x453 * 0x2341f27177344
mov rdx, [ rsp + 0x4d8 ]; load m64 x423 to register64
mov [ rsp + 0x5b8 ], r14; spilling x576 to mem
mov r14, [ rsp + 0x80 ]; x465, copying x450 here, cause x450 is needed in a reg for other than x465, namely all: , x465--x466, size: 1
adox r14, rdx
setc dl; spill CF x590 to reg (rdx)
clc;
mov [ rsp + 0x5c0 ], r14; spilling x465 to mem
mov r14, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, r14; loading flag
adcx r15, rbx
setc bl; spill CF x507 to reg (rbx)
movzx r8, byte [ rsp + 0x560 ]; load byte memx532 to register64
clc;
adcx r8, r14; loading flag
adcx rbp, [ rsp + 0x540 ]
setc r8b; spill CF x534 to reg (r8)
clc;
movzx r13, r13b
adcx r13, r14; loading flag
adcx r9, [ rsp + 0x558 ]
seto r13b; spill OF x466 to reg (r13)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, r14; loading flag
adox r15, rbp
mov r12, 0x0 ; moving imm to reg
adcx rax, r12
mov rbp, [ rsp + 0x78 ]; load m64 x452 to register64
clc;
movzx r13, r13b
adcx r13, r14; loading flag
adcx rbp, [ rsp + 0x4f8 ]
setc r13b; spill CF x468 to reg (r13)
clc;
movzx rdx, dl
adcx rdx, r14; loading flag
adcx r15, [ rsp + 0x5b8 ]
setc dl; spill CF x592 to reg (rdx)
seto r12b; spill OF x549 to reg (r12)
movzx r14, byte [ rsp + 0x5b0 ]; x603, copying x603 here, cause x603 is needed in a reg for other than x603, namely all: , x604--x605, size: 1
add r14, -0x1
mov r14, [ rsp + 0x5a8 ]; x604, copying x589 here, cause x589 is needed in a reg for other than x604, namely all: , x618, x604--x605, size: 2
mov byte [ rsp + 0x5c8 ], r13b; spilling byte x468 to mem
mov r13, 0xffffffffffffffff ; moving imm to reg
sbb r14, r13
mov r13, r15; x606, copying x591 here, cause x591 is needed in a reg for other than x606, namely all: , x606--x607, x619, size: 2
mov [ rsp + 0x5d0 ], r14; spilling x604 to mem
mov r14, 0xfdc1767ae2ffffff ; moving imm to reg
sbb r13, r14
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbx, bl
adox rbx, r14; loading flag
adox r9, [ rsp + 0x5c0 ]
mov bl, dl; preserving value of x592 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x5d8 ], r13; spilling x606 to mem
mulx r14, r13, rcx; x516, x515<- x6 * arg1[5]
seto dl; spill OF x509 to reg (rdx)
mov byte [ rsp + 0x5e0 ], bl; spilling byte x592 to mem
mov rbx, -0x1 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbx, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, rbx; loading flag
adox r13, [ rsp + 0x598 ]
setc r8b; spill CF x607 to reg (r8)
clc;
movzx r12, r12b
adcx r12, rbx; loading flag
adcx r9, r13
xchg rdx, rcx; x6, swapping with x509, which is currently in rdx
mulx rdx, r12, [ rsi + 0x30 ]; x514, x513<- x6 * arg1[6]
adox r12, r14
setc r14b; spill CF x551 to reg (r14)
clc;
movzx rcx, cl
adcx rcx, rbx; loading flag
adcx rbp, rax
mov rax, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, rdi; x540, swapping with x514, which is currently in rdx
mulx rcx, r13, rax; x559, x558<- x540 * 0x6cfc5fd681c52056
setc bl; spill CF x511 to reg (rbx)
movzx rax, byte [ rsp + 0x5a0 ]; load byte memx577 to register64
clc;
mov byte [ rsp + 0x5e8 ], r8b; spilling byte x607 to mem
mov r8, -0x1 ; moving imm to reg
adcx rax, r8; loading flag
adcx r13, [ rsp + 0x590 ]
mov rax, 0x0 ; moving imm to reg
adox rdi, rax
mov rax, 0x2341f27177344 ; moving imm to reg
mulx rdx, r8, rax; x557, x556<- x540 * 0x2341f27177344
adcx r8, rcx
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r14, r14b
adox r14, rcx; loading flag
adox rbp, r12
movzx r14, bl; x512, copying x511 here, cause x511 is needed in a reg for other than x512, namely all: , x512, size: 1
movzx r12, byte [ rsp + 0x5c8 ]; load byte memx468 to register64
lea r14, [ r14 + r12 ]; r64+m8
adox rdi, r14
seto r12b; spill OF x555 to reg (r12)
movzx rbx, byte [ rsp + 0x5e0 ]; load byte memx592 to register64
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
adox rbx, r14; loading flag
adox r9, r13
adox r8, rbp
setc bl; spill CF x581 to reg (rbx)
seto r13b; spill OF x596 to reg (r13)
movzx rbp, byte [ rsp + 0x5e8 ]; x607, copying x607 here, cause x607 is needed in a reg for other than x607, namely all: , x608--x609, size: 1
add rbp, -0x1
mov rbp, r9; x608, copying x593 here, cause x593 is needed in a reg for other than x608, namely all: , x608--x609, x620, size: 2
mov rcx, 0x7bc65c783158aea3 ; moving imm to reg
sbb rbp, rcx
movzx r14, bl; x582, copying x581 here, cause x581 is needed in a reg for other than x582, namely all: , x582, size: 1
lea r14, [ r14 + rdx ]
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r13, r13b
adox r13, rdx; loading flag
adox rdi, r14
movzx rbx, r12b; x599, copying x555 here, cause x555 is needed in a reg for other than x599, namely all: , x599, size: 1
mov r13, 0x0 ; moving imm to reg
adox rbx, r13
mov r12, r8; x610, copying x595 here, cause x595 is needed in a reg for other than x610, namely all: , x610--x611, x621, size: 2
mov r14, 0x6cfc5fd681c52056 ; moving imm to reg
sbb r12, r14
mov r13, rdi; x612, copying x597 here, cause x597 is needed in a reg for other than x612, namely all: , x612--x613, x622, size: 2
sbb r13, rax
sbb rbx, 0x00000000
cmovc rbp, r9; if CF, x620<- x593 (nzVar)
mov rbx, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rbx + 0x20 ], rbp; out1[4] = x620
cmovc r13, rdi; if CF, x622<- x597 (nzVar)
mov r9, [ rsp + 0x5d0 ]; x618, copying x604 here, cause x604 is needed in a reg for other than x618, namely all: , x618, size: 1
cmovc r9, [ rsp + 0x5a8 ]; if CF, x618<- x589 (nzVar)
cmovc r12, r8; if CF, x621<- x595 (nzVar)
mov [ rbx + 0x30 ], r13; out1[6] = x622
mov r8, [ rsp + 0x5d8 ]; x619, copying x606 here, cause x606 is needed in a reg for other than x619, namely all: , x619, size: 1
cmovc r8, r15; if CF, x619<- x591 (nzVar)
mov r15, [ rsp + 0x538 ]; x616, copying x600 here, cause x600 is needed in a reg for other than x616, namely all: , x616, size: 1
cmovc r15, r11; if CF, x616<- x585 (nzVar)
mov [ rbx + 0x0 ], r15; out1[0] = x616
mov [ rbx + 0x18 ], r8; out1[3] = x619
mov r11, [ rsp + 0x568 ]; x617, copying x602 here, cause x602 is needed in a reg for other than x617, namely all: , x617, size: 1
cmovc r11, r10; if CF, x617<- x587 (nzVar)
mov [ rbx + 0x8 ], r11; out1[1] = x617
mov [ rbx + 0x10 ], r9; out1[2] = x618
mov [ rbx + 0x28 ], r12; out1[5] = x621
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
; first cyclecount 464.405, best 416.48148148148147, lastGood 421.037037037037
; seed 3759678552496106 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 9769871 ms / 60000 runs=> 162.83118333333334ms/run
; Time spent for assembling and measureing (initial batch_size=27, initial num_batches=101): 185267 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.018963095827979715
; number reverted permutation/ tried permutation: 19410 / 29921 =64.871%
; number reverted decision/ tried decision: 18019 / 30080 =59.904%