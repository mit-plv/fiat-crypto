SECTION .text
	GLOBAL mul_p434
mul_p434:
sub rsp, 0x550 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x520 ], rbx; saving to stack
mov [ rsp + 0x528 ], rbp; saving to stack
mov [ rsp + 0x530 ], r12; saving to stack
mov [ rsp + 0x538 ], r13; saving to stack
mov [ rsp + 0x540 ], r14; saving to stack
mov [ rsp + 0x548 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x7 to register64
xchg rdx, rax; x7, swapping with arg2, which is currently in rdx
mulx r10, r11, [ rax + 0x0 ]; x21, x20<- x7 * arg2[0]
mov rbx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r11; x20, swapping with x7, which is currently in rdx
mulx rbp, r12, rbx; x48, x47<- x20 * 0xffffffffffffffff
test al, al
adox r12, rdx
xchg rdx, r11; x7, swapping with x20, which is currently in rdx
mulx r12, r13, [ rax + 0x8 ]; x19, x18<- x7 * arg2[1]
adcx r13, r10
xchg rdx, r11; x20, swapping with x7, which is currently in rdx
mulx r14, r15, rbx; x46, x45<- x20 * 0xffffffffffffffff
setc cl; spill CF x23 to reg (rcx)
clc;
adcx r15, rbp
adox r15, r13
mov r8, [ rsi + 0x8 ]; load m64 x1 to register64
xchg rdx, r8; x1, swapping with x20, which is currently in rdx
mulx r9, r10, [ rax + 0x0 ]; x91, x90<- x1 * arg2[0]
seto bpl; spill OF x65 to reg (rbp)
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r10, r15
xchg rdx, r10; x105, swapping with x1, which is currently in rdx
mulx r15, r13, rbx; x134, x133<- x105 * 0xffffffffffffffff
seto bl; spill OF x106 to reg (rbx)
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, rdx
xchg rdx, r11; x7, swapping with x105, which is currently in rdx
mulx r13, rdi, [ rax + 0x10 ]; x17, x16<- x7 * arg2[2]
mov [ rsp + 0x8 ], r13; spilling x17 to mem
setc r13b; spill CF x50 to reg (r13)
clc;
mov [ rsp + 0x10 ], r15; spilling x134 to mem
mov r15, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, r15; loading flag
adcx r12, rdi
mov rcx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rcx; 0xffffffffffffffff, swapping with x7, which is currently in rdx
mulx rdi, r15, r8; x44, x43<- x20 * 0xffffffffffffffff
seto dl; spill OF x149 to reg (rdx)
mov [ rsp + 0x18 ], rdi; spilling x44 to mem
mov rdi, 0x0 ; moving imm to reg
dec rdi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r13, r13b
adox r13, rdi; loading flag
adox r14, r15
seto r13b; spill OF x52 to reg (r13)
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, r15; loading flag
adox r12, r14
mov bpl, dl; preserving value of x149 into a new reg
mov rdx, [ rax + 0x8 ]; saving arg2[1] in rdx.
mulx r14, rdi, r10; x89, x88<- x1 * arg2[1]
setc r15b; spill CF x25 to reg (r15)
clc;
adcx rdi, r9
seto r9b; spill OF x67 to reg (r9)
mov [ rsp + 0x20 ], r14; spilling x89 to mem
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbx, bl
adox rbx, r14; loading flag
adox r12, rdi
mov rbx, 0xffffffffffffffff ; moving imm to reg
mov rdx, r11; x105 to rdx
mulx r11, rdi, rbx; x132, x131<- x105 * 0xffffffffffffffff
seto r14b; spill OF x108 to reg (r14)
mov rbx, -0x2 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rdi, [ rsp + 0x10 ]
seto bl; spill OF x136 to reg (rbx)
mov [ rsp + 0x28 ], r11; spilling x132 to mem
mov r11, 0x0 ; moving imm to reg
dec r11; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbp, bpl
adox rbp, r11; loading flag
adox r12, rdi
mov rbp, [ rsi + 0x10 ]; load m64 x2 to register64
xchg rdx, rbp; x2, swapping with x105, which is currently in rdx
mulx rdi, r11, [ rax + 0x0 ]; x178, x177<- x2 * arg2[0]
mov [ rsp + 0x30 ], rdi; spilling x178 to mem
setc dil; spill CF x93 to reg (rdi)
clc;
adcx r11, r12
mov r12, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r12; 0xffffffffffffffff, swapping with x2, which is currently in rdx
mov byte [ rsp + 0x38 ], bl; spilling byte x136 to mem
mov byte [ rsp + 0x40 ], r14b; spilling byte x108 to mem
mulx rbx, r14, r11; x221, x220<- x192 * 0xffffffffffffffff
setc dl; spill CF x193 to reg (rdx)
clc;
adcx r14, r11
mov r14, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, r8; x20, swapping with x193, which is currently in rdx
mov [ rsp + 0x48 ], rbx; spilling x221 to mem
mov byte [ rsp + 0x50 ], r8b; spilling byte x193 to mem
mulx rbx, r8, r14; x42, x41<- x20 * 0xfdc1767ae2ffffff
mov r14, rdx; preserving value of x20 into a new reg
mov rdx, [ rax + 0x18 ]; saving arg2[3] in rdx.
mov [ rsp + 0x58 ], rbx; spilling x42 to mem
mov byte [ rsp + 0x60 ], dil; spilling byte x93 to mem
mulx rbx, rdi, rcx; x15, x14<- x7 * arg2[3]
mov [ rsp + 0x68 ], rbx; spilling x15 to mem
seto bl; spill OF x151 to reg (rbx)
mov byte [ rsp + 0x70 ], r9b; spilling byte x67 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r15, r15b
adox r15, r9; loading flag
adox rdi, [ rsp + 0x8 ]
setc r15b; spill CF x236 to reg (r15)
clc;
movzx r13, r13b
adcx r13, r9; loading flag
adcx r8, [ rsp + 0x18 ]
mov rdx, r10; x1 to rdx
mulx r10, r13, [ rax + 0x10 ]; x87, x86<- x1 * arg2[2]
seto r9b; spill OF x27 to reg (r9)
mov [ rsp + 0x78 ], r10; spilling x87 to mem
movzx r10, byte [ rsp + 0x70 ]; load byte memx67 to register64
mov byte [ rsp + 0x80 ], r15b; spilling byte x236 to mem
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r10, r15; loading flag
adox rdi, r8
seto r10b; spill OF x69 to reg (r10)
movzx r8, byte [ rsp + 0x60 ]; load byte memx93 to register64
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
adox r8, r15; loading flag
adox r13, [ rsp + 0x20 ]
seto r8b; spill OF x95 to reg (r8)
movzx r15, byte [ rsp + 0x40 ]; load byte memx108 to register64
mov byte [ rsp + 0x88 ], r10b; spilling byte x69 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, r10; loading flag
adox rdi, r13
mov r15, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r15; 0xffffffffffffffff, swapping with x1, which is currently in rdx
mulx r13, r10, rbp; x130, x129<- x105 * 0xffffffffffffffff
seto dl; spill OF x110 to reg (rdx)
mov [ rsp + 0x90 ], r13; spilling x130 to mem
movzx r13, byte [ rsp + 0x38 ]; load byte memx136 to register64
mov byte [ rsp + 0x98 ], r8b; spilling byte x95 to mem
mov r8, -0x1 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r8, -0x1 ; moving imm to reg
adox r13, r8; loading flag
adox r10, [ rsp + 0x28 ]
mov r13b, dl; preserving value of x110 into a new reg
mov rdx, [ rax + 0x8 ]; saving arg2[1] in rdx.
mov byte [ rsp + 0xa0 ], r9b; spilling byte x27 to mem
mulx r8, r9, r12; x176, x175<- x2 * arg2[1]
mov [ rsp + 0xa8 ], r8; spilling x176 to mem
seto r8b; spill OF x138 to reg (r8)
mov byte [ rsp + 0xb0 ], r13b; spilling byte x110 to mem
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbx, bl
adox rbx, r13; loading flag
adox rdi, r10
setc bl; spill CF x54 to reg (rbx)
clc;
adcx r9, [ rsp + 0x30 ]
mov r10, 0xffffffffffffffff ; moving imm to reg
mov rdx, r10; 0xffffffffffffffff to rdx
mulx r10, r13, r11; x219, x218<- x192 * 0xffffffffffffffff
setc dl; spill CF x180 to reg (rdx)
mov [ rsp + 0xb8 ], r10; spilling x219 to mem
movzx r10, byte [ rsp + 0x50 ]; load byte memx193 to register64
clc;
mov byte [ rsp + 0xc0 ], r8b; spilling byte x138 to mem
mov r8, -0x1 ; moving imm to reg
adcx r10, r8; loading flag
adcx rdi, r9
setc r10b; spill CF x195 to reg (r10)
clc;
adcx r13, [ rsp + 0x48 ]
setc r9b; spill CF x223 to reg (r9)
movzx r8, byte [ rsp + 0x80 ]; load byte memx236 to register64
clc;
mov byte [ rsp + 0xc8 ], r10b; spilling byte x195 to mem
mov r10, -0x1 ; moving imm to reg
adcx r8, r10; loading flag
adcx rdi, r13
mov r8, [ rsi + 0x18 ]; load m64 x3 to register64
xchg rdx, r8; x3, swapping with x180, which is currently in rdx
mulx r13, r10, [ rax + 0x0 ]; x265, x264<- x3 * arg2[0]
mov [ rsp + 0xd0 ], r13; spilling x265 to mem
setc r13b; spill CF x238 to reg (r13)
clc;
adcx r10, rdi
mov rdi, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r10; x279, swapping with x3, which is currently in rdx
mov byte [ rsp + 0xd8 ], r13b; spilling byte x238 to mem
mov byte [ rsp + 0xe0 ], r9b; spilling byte x223 to mem
mulx r13, r9, rdi; x308, x307<- x279 * 0xffffffffffffffff
mov byte [ rsp + 0xe8 ], r8b; spilling byte x180 to mem
mov byte [ rsp + 0xf0 ], bl; spilling byte x54 to mem
mulx r8, rbx, rdi; x306, x305<- x279 * 0xffffffffffffffff
mov [ rsp + 0xf8 ], r9; spilling x307 to mem
mov [ rsp + 0x100 ], r8; spilling x306 to mem
mulx r9, r8, rdi; x304, x303<- x279 * 0xffffffffffffffff
setc dil; spill CF x280 to reg (rdi)
clc;
adcx rbx, r13
mov r13, 0xfdc1767ae2ffffff ; moving imm to reg
mov [ rsp + 0x108 ], rbx; spilling x309 to mem
mov byte [ rsp + 0x110 ], dil; spilling byte x280 to mem
mulx rbx, rdi, r13; x302, x301<- x279 * 0xfdc1767ae2ffffff
mov r13, [ rsp + 0x100 ]; x311, copying x306 here, cause x306 is needed in a reg for other than x311, namely all: , x311--x312, size: 1
adcx r13, r8
mov r8, 0x7bc65c783158aea3 ; moving imm to reg
mov [ rsp + 0x118 ], r13; spilling x311 to mem
mov [ rsp + 0x120 ], rbx; spilling x302 to mem
mulx r13, rbx, r8; x300, x299<- x279 * 0x7bc65c783158aea3
adcx rdi, r9
mov r9, [ rsp + 0x120 ]; x315, copying x302 here, cause x302 is needed in a reg for other than x315, namely all: , x315--x316, size: 1
adcx r9, rbx
mov rbx, 0x6cfc5fd681c52056 ; moving imm to reg
mov [ rsp + 0x128 ], r9; spilling x315 to mem
mulx r8, r9, rbx; x298, x297<- x279 * 0x6cfc5fd681c52056
adcx r9, r13
mov r13, 0x2341f27177344 ; moving imm to reg
mov [ rsp + 0x130 ], r9; spilling x317 to mem
mulx rbx, r9, r13; x296, x295<- x279 * 0x2341f27177344
adcx r9, r8
mov r8, 0x0 ; moving imm to reg
adcx rbx, r8
mov r8, [ rsi + 0x28 ]; load m64 x5 to register64
xchg rdx, r8; x5, swapping with x279, which is currently in rdx
mov [ rsp + 0x138 ], rbx; spilling x321 to mem
mulx r13, rbx, [ rax + 0x0 ]; x439, x438<- x5 * arg2[0]
mov [ rsp + 0x140 ], rbx; spilling x438 to mem
mov [ rsp + 0x148 ], r9; spilling x319 to mem
mulx rbx, r9, [ rax + 0x8 ]; x437, x436<- x5 * arg2[1]
clc;
adcx r9, r13
mov [ rsp + 0x150 ], r9; spilling x440 to mem
mulx r13, r9, [ rax + 0x10 ]; x435, x434<- x5 * arg2[2]
adcx r9, rbx
mov [ rsp + 0x158 ], r9; spilling x442 to mem
mulx rbx, r9, [ rax + 0x18 ]; x433, x432<- x5 * arg2[3]
adcx r9, r13
mov [ rsp + 0x160 ], r9; spilling x444 to mem
mulx r13, r9, [ rax + 0x20 ]; x431, x430<- x5 * arg2[4]
adcx r9, rbx
mov [ rsp + 0x168 ], r9; spilling x446 to mem
mulx rbx, r9, [ rax + 0x28 ]; x429, x428<- x5 * arg2[5]
adcx r9, r13
mulx rdx, r13, [ rax + 0x30 ]; x427, x426<- x5 * arg2[6]
adcx r13, rbx
mov rbx, 0x0 ; moving imm to reg
adcx rdx, rbx
clc;
adcx r8, [ rsp + 0xf8 ]
xchg rdx, rcx; x7, swapping with x452, which is currently in rdx
mulx r8, rbx, [ rax + 0x20 ]; x13, x12<- x7 * arg2[4]
mov [ rsp + 0x170 ], rcx; spilling x452 to mem
seto cl; spill OF x153 to reg (rcx)
mov [ rsp + 0x178 ], r13; spilling x450 to mem
movzx r13, byte [ rsp + 0xa0 ]; load byte memx27 to register64
mov [ rsp + 0x180 ], r9; spilling x448 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r13, r9; loading flag
adox rbx, [ rsp + 0x68 ]
mov r13, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, r14; x20, swapping with x7, which is currently in rdx
mov [ rsp + 0x188 ], rdi; spilling x313 to mem
mulx r9, rdi, r13; x40, x39<- x20 * 0x7bc65c783158aea3
xchg rdx, r15; x1, swapping with x20, which is currently in rdx
mov [ rsp + 0x190 ], r9; spilling x40 to mem
mulx r13, r9, [ rax + 0x18 ]; x85, x84<- x1 * arg2[3]
mov [ rsp + 0x198 ], r13; spilling x85 to mem
seto r13b; spill OF x29 to reg (r13)
mov [ rsp + 0x1a0 ], r8; spilling x13 to mem
movzx r8, byte [ rsp + 0xf0 ]; load byte memx54 to register64
mov byte [ rsp + 0x1a8 ], cl; spilling byte x153 to mem
mov rcx, -0x1 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rcx, -0x1 ; moving imm to reg
adox r8, rcx; loading flag
adox rdi, [ rsp + 0x58 ]
setc r8b; spill CF x323 to reg (r8)
movzx rcx, byte [ rsp + 0x98 ]; load byte memx95 to register64
clc;
mov byte [ rsp + 0x1b0 ], r13b; spilling byte x29 to mem
mov r13, -0x1 ; moving imm to reg
adcx rcx, r13; loading flag
adcx r9, [ rsp + 0x78 ]
seto cl; spill OF x56 to reg (rcx)
movzx r13, byte [ rsp + 0x88 ]; load byte memx69 to register64
mov byte [ rsp + 0x1b8 ], r8b; spilling byte x323 to mem
mov r8, 0x0 ; moving imm to reg
dec r8; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r13, r8; loading flag
adox rbx, rdi
setc r13b; spill CF x97 to reg (r13)
movzx rdi, byte [ rsp + 0xb0 ]; load byte memx110 to register64
clc;
adcx rdi, r8; loading flag
adcx rbx, r9
mov rdi, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, rdi; 0xfdc1767ae2ffffff, swapping with x1, which is currently in rdx
mulx r9, r8, rbp; x128, x127<- x105 * 0xfdc1767ae2ffffff
seto dl; spill OF x71 to reg (rdx)
mov [ rsp + 0x1c0 ], r9; spilling x128 to mem
movzx r9, byte [ rsp + 0xc0 ]; load byte memx138 to register64
mov byte [ rsp + 0x1c8 ], r13b; spilling byte x97 to mem
mov r13, -0x1 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r13, -0x1 ; moving imm to reg
adox r9, r13; loading flag
adox r8, [ rsp + 0x90 ]
seto r9b; spill OF x140 to reg (r9)
movzx r13, byte [ rsp + 0x1a8 ]; load byte memx153 to register64
mov byte [ rsp + 0x1d0 ], dl; spilling byte x71 to mem
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
adox r13, rdx; loading flag
adox rbx, r8
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx r13, r8, r12; x174, x173<- x2 * arg2[2]
mov [ rsp + 0x1d8 ], r13; spilling x174 to mem
seto r13b; spill OF x155 to reg (r13)
mov byte [ rsp + 0x1e0 ], r9b; spilling byte x140 to mem
movzx r9, byte [ rsp + 0xe8 ]; load byte memx180 to register64
mov byte [ rsp + 0x1e8 ], cl; spilling byte x56 to mem
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r9, rcx; loading flag
adox r8, [ rsp + 0xa8 ]
setc r9b; spill CF x112 to reg (r9)
movzx rcx, byte [ rsp + 0xc8 ]; load byte memx195 to register64
clc;
mov byte [ rsp + 0x1f0 ], r13b; spilling byte x155 to mem
mov r13, -0x1 ; moving imm to reg
adcx rcx, r13; loading flag
adcx rbx, r8
mov rcx, 0xffffffffffffffff ; moving imm to reg
mov rdx, r11; x192 to rdx
mulx r11, r8, rcx; x217, x216<- x192 * 0xffffffffffffffff
setc r13b; spill CF x197 to reg (r13)
movzx rcx, byte [ rsp + 0xe0 ]; load byte memx223 to register64
clc;
mov [ rsp + 0x1f8 ], r11; spilling x217 to mem
mov r11, -0x1 ; moving imm to reg
adcx rcx, r11; loading flag
adcx r8, [ rsp + 0xb8 ]
setc cl; spill CF x225 to reg (rcx)
movzx r11, byte [ rsp + 0xd8 ]; load byte memx238 to register64
clc;
mov byte [ rsp + 0x200 ], r13b; spilling byte x197 to mem
mov r13, -0x1 ; moving imm to reg
adcx r11, r13; loading flag
adcx rbx, r8
xchg rdx, r10; x3, swapping with x192, which is currently in rdx
mulx r11, r8, [ rax + 0x8 ]; x263, x262<- x3 * arg2[1]
seto r13b; spill OF x182 to reg (r13)
mov [ rsp + 0x208 ], r11; spilling x263 to mem
mov r11, -0x2 ; moving imm to reg
inc r11; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, [ rsp + 0xd0 ]
seto r11b; spill OF x267 to reg (r11)
mov byte [ rsp + 0x210 ], cl; spilling byte x225 to mem
movzx rcx, byte [ rsp + 0x110 ]; load byte memx280 to register64
mov byte [ rsp + 0x218 ], r13b; spilling byte x182 to mem
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rcx, r13; loading flag
adox rbx, r8
setc cl; spill CF x240 to reg (rcx)
movzx r8, byte [ rsp + 0x1b8 ]; load byte memx323 to register64
clc;
adcx r8, r13; loading flag
adcx rbx, [ rsp + 0x108 ]
mov r8, rdx; preserving value of x3 into a new reg
mov rdx, [ rax + 0x28 ]; saving arg2[5] in rdx.
mov [ rsp + 0x220 ], rbx; spilling x324 to mem
mulx r13, rbx, r14; x11, x10<- x7 * arg2[5]
mov [ rsp + 0x228 ], r13; spilling x11 to mem
seto r13b; spill OF x282 to reg (r13)
mov byte [ rsp + 0x230 ], r11b; spilling byte x267 to mem
movzx r11, byte [ rsp + 0x1b0 ]; load byte memx29 to register64
mov byte [ rsp + 0x238 ], cl; spilling byte x240 to mem
mov rcx, -0x1 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rcx, -0x1 ; moving imm to reg
adox r11, rcx; loading flag
adox rbx, [ rsp + 0x1a0 ]
mov r11, 0x6cfc5fd681c52056 ; moving imm to reg
mov rdx, r15; x20 to rdx
mulx r15, rcx, r11; x38, x37<- x20 * 0x6cfc5fd681c52056
setc r11b; spill CF x325 to reg (r11)
mov [ rsp + 0x240 ], r15; spilling x38 to mem
movzx r15, byte [ rsp + 0x1e8 ]; load byte memx56 to register64
clc;
mov byte [ rsp + 0x248 ], r13b; spilling byte x282 to mem
mov r13, -0x1 ; moving imm to reg
adcx r15, r13; loading flag
adcx rcx, [ rsp + 0x190 ]
seto r15b; spill OF x31 to reg (r15)
movzx r13, byte [ rsp + 0x1d0 ]; load byte memx71 to register64
mov byte [ rsp + 0x250 ], r11b; spilling byte x325 to mem
mov r11, 0x0 ; moving imm to reg
dec r11; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r13, r11; loading flag
adox rbx, rcx
mov r13, rdx; preserving value of x20 into a new reg
mov rdx, [ rax + 0x20 ]; saving arg2[4] in rdx.
mulx rcx, r11, rdi; x83, x82<- x1 * arg2[4]
mov [ rsp + 0x258 ], rcx; spilling x83 to mem
setc cl; spill CF x58 to reg (rcx)
mov byte [ rsp + 0x260 ], r15b; spilling byte x31 to mem
movzx r15, byte [ rsp + 0x1c8 ]; load byte memx97 to register64
clc;
mov [ rsp + 0x268 ], rbx; spilling x72 to mem
mov rbx, -0x1 ; moving imm to reg
adcx r15, rbx; loading flag
adcx r11, [ rsp + 0x198 ]
mov r15, 0x7bc65c783158aea3 ; moving imm to reg
mov rdx, rbp; x105 to rdx
mulx rbp, rbx, r15; x126, x125<- x105 * 0x7bc65c783158aea3
setc r15b; spill CF x99 to reg (r15)
clc;
mov [ rsp + 0x270 ], rbp; spilling x126 to mem
mov rbp, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, rbp; loading flag
adcx r11, [ rsp + 0x268 ]
seto r9b; spill OF x73 to reg (r9)
movzx rbp, byte [ rsp + 0x1e0 ]; load byte memx140 to register64
mov byte [ rsp + 0x278 ], r15b; spilling byte x99 to mem
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbp, r15; loading flag
adox rbx, [ rsp + 0x1c0 ]
setc bpl; spill CF x114 to reg (rbp)
movzx r15, byte [ rsp + 0x1f0 ]; load byte memx155 to register64
clc;
mov byte [ rsp + 0x280 ], r9b; spilling byte x73 to mem
mov r9, -0x1 ; moving imm to reg
adcx r15, r9; loading flag
adcx r11, rbx
mov r15, rdx; preserving value of x105 into a new reg
mov rdx, [ rax + 0x18 ]; saving arg2[3] in rdx.
mulx rbx, r9, r12; x172, x171<- x2 * arg2[3]
mov [ rsp + 0x288 ], rbx; spilling x172 to mem
seto bl; spill OF x142 to reg (rbx)
mov byte [ rsp + 0x290 ], bpl; spilling byte x114 to mem
movzx rbp, byte [ rsp + 0x218 ]; load byte memx182 to register64
mov byte [ rsp + 0x298 ], cl; spilling byte x58 to mem
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbp, rcx; loading flag
adox r9, [ rsp + 0x1d8 ]
seto bpl; spill OF x184 to reg (rbp)
movzx rcx, byte [ rsp + 0x200 ]; load byte memx197 to register64
mov byte [ rsp + 0x2a0 ], bl; spilling byte x142 to mem
mov rbx, -0x1 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbx, -0x1 ; moving imm to reg
adox rcx, rbx; loading flag
adox r11, r9
mov rcx, 0xfdc1767ae2ffffff ; moving imm to reg
mov rdx, rcx; 0xfdc1767ae2ffffff to rdx
mulx rcx, r9, r10; x215, x214<- x192 * 0xfdc1767ae2ffffff
seto bl; spill OF x199 to reg (rbx)
movzx rdx, byte [ rsp + 0x210 ]; load byte memx225 to register64
mov [ rsp + 0x2a8 ], rcx; spilling x215 to mem
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rdx, rcx; loading flag
adox r9, [ rsp + 0x1f8 ]
setc dl; spill CF x157 to reg (rdx)
movzx rcx, byte [ rsp + 0x238 ]; load byte memx240 to register64
clc;
mov byte [ rsp + 0x2b0 ], bl; spilling byte x199 to mem
mov rbx, -0x1 ; moving imm to reg
adcx rcx, rbx; loading flag
adcx r11, r9
mov cl, dl; preserving value of x157 into a new reg
mov rdx, [ rax + 0x10 ]; saving arg2[2] in rdx.
mulx r9, rbx, r8; x261, x260<- x3 * arg2[2]
mov [ rsp + 0x2b8 ], r9; spilling x261 to mem
setc r9b; spill CF x242 to reg (r9)
mov byte [ rsp + 0x2c0 ], bpl; spilling byte x184 to mem
movzx rbp, byte [ rsp + 0x230 ]; load byte memx267 to register64
clc;
mov byte [ rsp + 0x2c8 ], cl; spilling byte x157 to mem
mov rcx, -0x1 ; moving imm to reg
adcx rbp, rcx; loading flag
adcx rbx, [ rsp + 0x208 ]
setc bpl; spill CF x269 to reg (rbp)
movzx rcx, byte [ rsp + 0x248 ]; load byte memx282 to register64
clc;
mov byte [ rsp + 0x2d0 ], r9b; spilling byte x242 to mem
mov r9, -0x1 ; moving imm to reg
adcx rcx, r9; loading flag
adcx r11, rbx
setc cl; spill CF x284 to reg (rcx)
movzx rbx, byte [ rsp + 0x250 ]; load byte memx325 to register64
clc;
adcx rbx, r9; loading flag
adcx r11, [ rsp + 0x118 ]
mov rdx, r14; x7 to rdx
mulx rdx, r14, [ rax + 0x30 ]; x9, x8<- x7 * arg2[6]
mov rbx, 0x2341f27177344 ; moving imm to reg
xchg rdx, rbx; 0x2341f27177344, swapping with x9, which is currently in rdx
mulx r13, r9, r13; x36, x35<- x20 * 0x2341f27177344
setc dl; spill CF x327 to reg (rdx)
mov [ rsp + 0x2d8 ], r11; spilling x326 to mem
movzx r11, byte [ rsp + 0x260 ]; load byte memx31 to register64
clc;
mov [ rsp + 0x2e0 ], rbx; spilling x9 to mem
mov rbx, -0x1 ; moving imm to reg
adcx r11, rbx; loading flag
adcx r14, [ rsp + 0x228 ]
setc r11b; spill CF x33 to reg (r11)
movzx rbx, byte [ rsp + 0x298 ]; load byte memx58 to register64
clc;
mov [ rsp + 0x2e8 ], r13; spilling x36 to mem
mov r13, -0x1 ; moving imm to reg
adcx rbx, r13; loading flag
adcx r9, [ rsp + 0x240 ]
seto bl; spill OF x227 to reg (rbx)
movzx r13, byte [ rsp + 0x280 ]; load byte memx73 to register64
mov byte [ rsp + 0x2f0 ], r11b; spilling byte x33 to mem
mov r11, 0x0 ; moving imm to reg
dec r11; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r13, r11; loading flag
adox r14, r9
mov r13b, dl; preserving value of x327 into a new reg
mov rdx, [ rax + 0x28 ]; saving arg2[5] in rdx.
mulx r9, r11, rdi; x81, x80<- x1 * arg2[5]
mov [ rsp + 0x2f8 ], r9; spilling x81 to mem
seto r9b; spill OF x75 to reg (r9)
mov byte [ rsp + 0x300 ], r13b; spilling byte x327 to mem
movzx r13, byte [ rsp + 0x278 ]; load byte memx99 to register64
mov byte [ rsp + 0x308 ], cl; spilling byte x284 to mem
mov rcx, -0x1 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rcx, -0x1 ; moving imm to reg
adox r13, rcx; loading flag
adox r11, [ rsp + 0x258 ]
mov r13, 0x6cfc5fd681c52056 ; moving imm to reg
mov rdx, r13; 0x6cfc5fd681c52056 to rdx
mulx r13, rcx, r15; x124, x123<- x105 * 0x6cfc5fd681c52056
setc dl; spill CF x60 to reg (rdx)
mov [ rsp + 0x310 ], r13; spilling x124 to mem
movzx r13, byte [ rsp + 0x290 ]; load byte memx114 to register64
clc;
mov byte [ rsp + 0x318 ], r9b; spilling byte x75 to mem
mov r9, -0x1 ; moving imm to reg
adcx r13, r9; loading flag
adcx r14, r11
setc r13b; spill CF x116 to reg (r13)
movzx r11, byte [ rsp + 0x2a0 ]; load byte memx142 to register64
clc;
adcx r11, r9; loading flag
adcx rcx, [ rsp + 0x270 ]
setc r11b; spill CF x144 to reg (r11)
movzx r9, byte [ rsp + 0x2c8 ]; load byte memx157 to register64
clc;
mov byte [ rsp + 0x320 ], r13b; spilling byte x116 to mem
mov r13, -0x1 ; moving imm to reg
adcx r9, r13; loading flag
adcx r14, rcx
mov r9b, dl; preserving value of x60 into a new reg
mov rdx, [ rax + 0x20 ]; saving arg2[4] in rdx.
mulx rcx, r13, r12; x170, x169<- x2 * arg2[4]
mov [ rsp + 0x328 ], rcx; spilling x170 to mem
seto cl; spill OF x101 to reg (rcx)
mov byte [ rsp + 0x330 ], r11b; spilling byte x144 to mem
movzx r11, byte [ rsp + 0x2c0 ]; load byte memx184 to register64
mov byte [ rsp + 0x338 ], r9b; spilling byte x60 to mem
mov r9, -0x1 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r9, -0x1 ; moving imm to reg
adox r11, r9; loading flag
adox r13, [ rsp + 0x288 ]
mov r11, 0x7bc65c783158aea3 ; moving imm to reg
mov rdx, r11; 0x7bc65c783158aea3 to rdx
mulx r11, r9, r10; x213, x212<- x192 * 0x7bc65c783158aea3
seto dl; spill OF x186 to reg (rdx)
mov [ rsp + 0x340 ], r11; spilling x213 to mem
movzx r11, byte [ rsp + 0x2b0 ]; load byte memx199 to register64
mov byte [ rsp + 0x348 ], cl; spilling byte x101 to mem
mov rcx, -0x1 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rcx, -0x1 ; moving imm to reg
adox r11, rcx; loading flag
adox r14, r13
setc r11b; spill CF x159 to reg (r11)
clc;
movzx rbx, bl
adcx rbx, rcx; loading flag
adcx r9, [ rsp + 0x2a8 ]
seto bl; spill OF x201 to reg (rbx)
movzx r13, byte [ rsp + 0x2d0 ]; load byte memx242 to register64
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rcx, -0x1 ; moving imm to reg
adox r13, rcx; loading flag
adox r14, r9
xchg rdx, r8; x3, swapping with x186, which is currently in rdx
mulx r13, r9, [ rax + 0x18 ]; x259, x258<- x3 * arg2[3]
setc cl; spill CF x229 to reg (rcx)
clc;
mov [ rsp + 0x350 ], r13; spilling x259 to mem
mov r13, -0x1 ; moving imm to reg
movzx rbp, bpl
adcx rbp, r13; loading flag
adcx r9, [ rsp + 0x2b8 ]
setc bpl; spill CF x271 to reg (rbp)
movzx r13, byte [ rsp + 0x308 ]; load byte memx284 to register64
clc;
mov byte [ rsp + 0x358 ], cl; spilling byte x229 to mem
mov rcx, -0x1 ; moving imm to reg
adcx r13, rcx; loading flag
adcx r14, r9
setc r13b; spill CF x286 to reg (r13)
movzx r9, byte [ rsp + 0x300 ]; load byte memx327 to register64
clc;
adcx r9, rcx; loading flag
adcx r14, [ rsp + 0x188 ]
movzx r9, byte [ rsp + 0x338 ]; x61, copying x60 here, cause x60 is needed in a reg for other than x61, namely all: , x61, size: 1
mov rcx, [ rsp + 0x2e8 ]; load m64 x36 to register64
lea r9, [ r9 + rcx ]; r8/64 + m8
movzx rcx, byte [ rsp + 0x2f0 ]; x34, copying x33 here, cause x33 is needed in a reg for other than x34, namely all: , x34, size: 1
mov [ rsp + 0x360 ], r14; spilling x328 to mem
mov r14, [ rsp + 0x2e0 ]; load m64 x9 to register64
lea rcx, [ rcx + r14 ]; r8/64 + m8
seto r14b; spill OF x244 to reg (r14)
mov byte [ rsp + 0x368 ], r13b; spilling byte x286 to mem
movzx r13, byte [ rsp + 0x318 ]; load byte memx75 to register64
mov byte [ rsp + 0x370 ], bpl; spilling byte x271 to mem
mov rbp, 0x0 ; moving imm to reg
dec rbp; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r13, rbp; loading flag
adox rcx, r9
xchg rdx, rdi; x1, swapping with x3, which is currently in rdx
mulx rdx, r13, [ rax + 0x30 ]; x79, x78<- x1 * arg2[6]
seto r9b; spill OF x77 to reg (r9)
movzx rbp, byte [ rsp + 0x348 ]; load byte memx101 to register64
mov [ rsp + 0x378 ], rdx; spilling x79 to mem
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
adox rbp, rdx; loading flag
adox r13, [ rsp + 0x2f8 ]
setc bpl; spill CF x329 to reg (rbp)
movzx rdx, byte [ rsp + 0x320 ]; load byte memx116 to register64
clc;
mov byte [ rsp + 0x380 ], r9b; spilling byte x77 to mem
mov r9, -0x1 ; moving imm to reg
adcx rdx, r9; loading flag
adcx rcx, r13
mov rdx, 0x2341f27177344 ; moving imm to reg
mulx r15, r13, r15; x122, x121<- x105 * 0x2341f27177344
setc r9b; spill CF x118 to reg (r9)
movzx rdx, byte [ rsp + 0x330 ]; load byte memx144 to register64
clc;
mov [ rsp + 0x388 ], r15; spilling x122 to mem
mov r15, -0x1 ; moving imm to reg
adcx rdx, r15; loading flag
adcx r13, [ rsp + 0x310 ]
setc dl; spill CF x146 to reg (rdx)
clc;
movzx r11, r11b
adcx r11, r15; loading flag
adcx rcx, r13
mov r11b, dl; preserving value of x146 into a new reg
mov rdx, [ rax + 0x28 ]; saving arg2[5] in rdx.
mulx r13, r15, r12; x168, x167<- x2 * arg2[5]
mov [ rsp + 0x390 ], r13; spilling x168 to mem
setc r13b; spill CF x161 to reg (r13)
clc;
mov byte [ rsp + 0x398 ], r11b; spilling byte x146 to mem
mov r11, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, r11; loading flag
adcx r15, [ rsp + 0x328 ]
seto r8b; spill OF x103 to reg (r8)
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r11, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, r11; loading flag
adox rcx, r15
mov rbx, 0x6cfc5fd681c52056 ; moving imm to reg
mov rdx, r10; x192 to rdx
mulx r10, r15, rbx; x211, x210<- x192 * 0x6cfc5fd681c52056
setc r11b; spill CF x188 to reg (r11)
movzx rbx, byte [ rsp + 0x358 ]; load byte memx229 to register64
clc;
mov [ rsp + 0x3a0 ], r10; spilling x211 to mem
mov r10, -0x1 ; moving imm to reg
adcx rbx, r10; loading flag
adcx r15, [ rsp + 0x340 ]
setc bl; spill CF x231 to reg (rbx)
clc;
movzx r14, r14b
adcx r14, r10; loading flag
adcx rcx, r15
xchg rdx, rdi; x3, swapping with x192, which is currently in rdx
mulx r14, r15, [ rax + 0x20 ]; x257, x256<- x3 * arg2[4]
seto r10b; spill OF x203 to reg (r10)
mov [ rsp + 0x3a8 ], r14; spilling x257 to mem
movzx r14, byte [ rsp + 0x370 ]; load byte memx271 to register64
mov byte [ rsp + 0x3b0 ], bl; spilling byte x231 to mem
mov rbx, -0x1 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbx, -0x1 ; moving imm to reg
adox r14, rbx; loading flag
adox r15, [ rsp + 0x350 ]
setc r14b; spill CF x246 to reg (r14)
movzx rbx, byte [ rsp + 0x368 ]; load byte memx286 to register64
clc;
mov byte [ rsp + 0x3b8 ], r10b; spilling byte x203 to mem
mov r10, -0x1 ; moving imm to reg
adcx rbx, r10; loading flag
adcx rcx, r15
seto bl; spill OF x273 to reg (rbx)
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, r15; loading flag
adox rcx, [ rsp + 0x128 ]
movzx rbp, r8b; x104, copying x103 here, cause x103 is needed in a reg for other than x104, namely all: , x104, size: 1
mov r10, [ rsp + 0x378 ]; load m64 x79 to register64
lea rbp, [ rbp + r10 ]; r8/64 + m8
seto r10b; spill OF x331 to reg (r10)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
movzx r15, byte [ rsp + 0x380 ]; load byte memx77 to register64
movzx r9, r9b
adox r9, r8; loading flag
adox rbp, r15
movzx r15, byte [ rsp + 0x398 ]; x147, copying x146 here, cause x146 is needed in a reg for other than x147, namely all: , x147, size: 1
mov r9, [ rsp + 0x388 ]; load m64 x122 to register64
lea r15, [ r15 + r9 ]; r8/64 + m8
seto r9b; spill OF x120 to reg (r9)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, r8; loading flag
adox rbp, r15
xchg rdx, r12; x2, swapping with x3, which is currently in rdx
mulx rdx, r13, [ rax + 0x30 ]; x166, x165<- x2 * arg2[6]
seto r15b; spill OF x163 to reg (r15)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, r8; loading flag
adox r13, [ rsp + 0x390 ]
mov r11, 0x2341f27177344 ; moving imm to reg
xchg rdx, r11; 0x2341f27177344, swapping with x166, which is currently in rdx
mulx rdi, r8, rdi; x209, x208<- x192 * 0x2341f27177344
setc dl; spill CF x288 to reg (rdx)
mov [ rsp + 0x3c0 ], rcx; spilling x330 to mem
movzx rcx, byte [ rsp + 0x3b0 ]; load byte memx231 to register64
clc;
mov [ rsp + 0x3c8 ], rdi; spilling x209 to mem
mov rdi, -0x1 ; moving imm to reg
adcx rcx, rdi; loading flag
adcx r8, [ rsp + 0x3a0 ]
setc cl; spill CF x233 to reg (rcx)
movzx rdi, byte [ rsp + 0x3b8 ]; load byte memx203 to register64
clc;
mov byte [ rsp + 0x3d0 ], r9b; spilling byte x120 to mem
mov r9, -0x1 ; moving imm to reg
adcx rdi, r9; loading flag
adcx rbp, r13
xchg rdx, r12; x3, swapping with x288, which is currently in rdx
mulx rdi, r13, [ rax + 0x28 ]; x255, x254<- x3 * arg2[5]
setc r9b; spill CF x205 to reg (r9)
clc;
mov [ rsp + 0x3d8 ], rsi; spilling arg1 to mem
mov rsi, -0x1 ; moving imm to reg
movzx r14, r14b
adcx r14, rsi; loading flag
adcx rbp, r8
setc r14b; spill CF x248 to reg (r14)
clc;
movzx rbx, bl
adcx rbx, rsi; loading flag
adcx r13, [ rsp + 0x3a8 ]
setc bl; spill CF x275 to reg (rbx)
clc;
movzx r12, r12b
adcx r12, rsi; loading flag
adcx rbp, r13
setc r12b; spill CF x290 to reg (r12)
clc;
movzx r10, r10b
adcx r10, rsi; loading flag
adcx rbp, [ rsp + 0x130 ]
mov r10, 0x0 ; moving imm to reg
adox r11, r10
movzx r8, r15b; x164, copying x163 here, cause x163 is needed in a reg for other than x164, namely all: , x164, size: 1
movzx r13, byte [ rsp + 0x3d0 ]; load byte memx120 to register64
lea r8, [ r8 + r13 ]; r64+m8
inc rsi; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov r10, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, r10; loading flag
adox r8, r11
movzx r13, cl; x234, copying x233 here, cause x233 is needed in a reg for other than x234, namely all: , x234, size: 1
mov r15, [ rsp + 0x3c8 ]; load m64 x209 to register64
lea r13, [ r13 + r15 ]; r8/64 + m8
seto r15b; spill OF x207 to reg (r15)
dec rsi; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx r14, r14b
adox r14, rsi; loading flag
adox r8, r13
mulx rdx, r10, [ rax + 0x30 ]; x253, x252<- x3 * arg2[6]
seto cl; spill OF x250 to reg (rcx)
inc rsi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, r9; loading flag
adox rdi, r10
seto r14b; spill OF x277 to reg (r14)
dec rsi; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx r12, r12b
adox r12, rsi; loading flag
adox r8, rdi
mov r9, [ rsp + 0x148 ]; x334, copying x319 here, cause x319 is needed in a reg for other than x334, namely all: , x334--x335, size: 1
adcx r9, r8
movzx rbx, r14b; x278, copying x277 here, cause x277 is needed in a reg for other than x278, namely all: , x278, size: 1
lea rbx, [ rbx + rdx ]
movzx r12, cl; x251, copying x250 here, cause x250 is needed in a reg for other than x251, namely all: , x251, size: 1
movzx r15, r15b
lea r12, [ r12 + r15 ]
adox rbx, r12
mov r11, [ rsp + 0x138 ]; x336, copying x321 here, cause x321 is needed in a reg for other than x336, namely all: , x336--x337, size: 1
adcx r11, rbx
seto r15b; spill OF x338 to reg (r15)
adc r15b, 0x0
movzx r15, r15b
mov r13, [ rsp + 0x3d8 ]; load m64 arg1 to register64
mov rcx, [ r13 + 0x30 ]; load m64 x6 to register64
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx r10, rdi, rcx; x526, x525<- x6 * arg2[0]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx r14, r8, rcx; x524, x523<- x6 * arg2[1]
mov rdx, rcx; x6 to rdx
mulx rcx, r12, [ rax + 0x10 ]; x522, x521<- x6 * arg2[2]
adox r8, r10
mulx rbx, r10, [ rax + 0x18 ]; x520, x519<- x6 * arg2[3]
adox r12, r14
adox r10, rcx
mulx r14, rcx, [ rax + 0x20 ]; x518, x517<- x6 * arg2[4]
adox rcx, rbx
mulx rbx, rsi, [ rax + 0x28 ]; x516, x515<- x6 * arg2[5]
adox rsi, r14
mulx rdx, r14, [ rax + 0x30 ]; x514, x513<- x6 * arg2[6]
adox r14, rbx
mov rbx, 0x0 ; moving imm to reg
adox rdx, rbx
mov rbx, [ r13 + 0x20 ]; load m64 x4 to register64
mov [ rsp + 0x3e0 ], r14; spilling x537 to mem
mov r14, rdx; preserving value of x539 into a new reg
mov rdx, [ rax + 0x0 ]; saving arg2[0] in rdx.
mov [ rsp + 0x3e8 ], rsi; spilling x535 to mem
mov [ rsp + 0x3f0 ], rcx; spilling x533 to mem
mulx rsi, rcx, rbx; x352, x351<- x4 * arg2[0]
adcx rcx, [ rsp + 0x220 ]
mov [ rsp + 0x3f8 ], r14; spilling x539 to mem
mov r14, 0xffffffffffffffff ; moving imm to reg
mov rdx, rcx; x366 to rdx
mov [ rsp + 0x400 ], r10; spilling x531 to mem
mulx rcx, r10, r14; x395, x394<- x366 * 0xffffffffffffffff
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r10, rdx
mov r10, rdx; preserving value of x366 into a new reg
mov rdx, [ rax + 0x8 ]; saving arg2[1] in rdx.
mov [ rsp + 0x408 ], r12; spilling x529 to mem
mulx r14, r12, rbx; x350, x349<- x4 * arg2[1]
mov [ rsp + 0x410 ], r8; spilling x527 to mem
mov r8, 0xffffffffffffffff ; moving imm to reg
mov rdx, r10; x366 to rdx
mov [ rsp + 0x418 ], rdi; spilling x525 to mem
mulx r10, rdi, r8; x393, x392<- x366 * 0xffffffffffffffff
seto r8b; spill OF x410 to reg (r8)
mov byte [ rsp + 0x420 ], r15b; spilling byte x338 to mem
mov r15, -0x2 ; moving imm to reg
inc r15; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, rsi
setc sil; spill CF x367 to reg (rsi)
clc;
adcx rdi, rcx
setc cl; spill CF x397 to reg (rcx)
clc;
movzx rsi, sil
adcx rsi, r15; loading flag
adcx r12, [ rsp + 0x2d8 ]
setc sil; spill CF x369 to reg (rsi)
clc;
movzx r8, r8b
adcx r8, r15; loading flag
adcx r12, rdi
mov r8, rdx; preserving value of x366 into a new reg
mov rdx, [ rax + 0x10 ]; saving arg2[2] in rdx.
mulx rdi, r15, rbx; x348, x347<- x4 * arg2[2]
adox r15, r14
seto r14b; spill OF x356 to reg (r14)
mov [ rsp + 0x428 ], r12; spilling x411 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
movzx rsi, sil
adox rsi, r12; loading flag
adox r15, [ rsp + 0x360 ]
mov rsi, 0xffffffffffffffff ; moving imm to reg
mov rdx, r8; x366 to rdx
mulx r8, r12, rsi; x391, x390<- x366 * 0xffffffffffffffff
seto sil; spill OF x371 to reg (rsi)
mov [ rsp + 0x430 ], r11; spilling x336 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r11; loading flag
adox r10, r12
mov rcx, rdx; preserving value of x366 into a new reg
mov rdx, [ rax + 0x18 ]; saving arg2[3] in rdx.
mulx r12, r11, rbx; x346, x345<- x4 * arg2[3]
adcx r10, r15
setc r15b; spill CF x414 to reg (r15)
clc;
mov [ rsp + 0x438 ], r10; spilling x413 to mem
mov r10, -0x1 ; moving imm to reg
movzx r14, r14b
adcx r14, r10; loading flag
adcx rdi, r11
seto r14b; spill OF x399 to reg (r14)
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r11, -0x1 ; moving imm to reg
movzx rsi, sil
adox rsi, r11; loading flag
adox rdi, [ rsp + 0x3c0 ]
mov rsi, 0xfdc1767ae2ffffff ; moving imm to reg
mov rdx, rcx; x366 to rdx
mulx rcx, r10, rsi; x389, x388<- x366 * 0xfdc1767ae2ffffff
setc r11b; spill CF x358 to reg (r11)
clc;
mov rsi, -0x1 ; moving imm to reg
movzx r14, r14b
adcx r14, rsi; loading flag
adcx r8, r10
mov r14, rdx; preserving value of x366 into a new reg
mov rdx, [ rax + 0x20 ]; saving arg2[4] in rdx.
mulx r10, rsi, rbx; x344, x343<- x4 * arg2[4]
mov [ rsp + 0x440 ], r9; spilling x334 to mem
seto r9b; spill OF x373 to reg (r9)
mov [ rsp + 0x448 ], r10; spilling x344 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r15, r15b
adox r15, r10; loading flag
adox rdi, r8
seto r15b; spill OF x416 to reg (r15)
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, r8; loading flag
adox r12, rsi
mov r11, 0x7bc65c783158aea3 ; moving imm to reg
mov rdx, r14; x366 to rdx
mulx r14, rsi, r11; x387, x386<- x366 * 0x7bc65c783158aea3
seto r10b; spill OF x360 to reg (r10)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, r8; loading flag
adox rbp, r12
adcx rsi, rcx
setc r9b; spill CF x403 to reg (r9)
clc;
movzx r15, r15b
adcx r15, r8; loading flag
adcx rbp, rsi
xchg rdx, rbx; x4, swapping with x366, which is currently in rdx
mulx rcx, r15, [ rax + 0x28 ]; x342, x341<- x4 * arg2[5]
seto r12b; spill OF x375 to reg (r12)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rsi, -0x1 ; moving imm to reg
movzx r10, r10b
adox r10, rsi; loading flag
adox r15, [ rsp + 0x448 ]
setc r10b; spill CF x418 to reg (r10)
clc;
movzx r12, r12b
adcx r12, rsi; loading flag
adcx r15, [ rsp + 0x440 ]
mov r12, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, rbx; x366, swapping with x4, which is currently in rdx
mulx r8, rsi, r12; x385, x384<- x366 * 0x6cfc5fd681c52056
setc r11b; spill CF x377 to reg (r11)
clc;
mov r12, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, r12; loading flag
adcx r14, rsi
setc r9b; spill CF x405 to reg (r9)
clc;
movzx r10, r10b
adcx r10, r12; loading flag
adcx r15, r14
mov r10, rdx; preserving value of x366 into a new reg
mov rdx, [ rax + 0x30 ]; saving arg2[6] in rdx.
mulx rbx, rsi, rbx; x340, x339<- x4 * arg2[6]
adox rsi, rcx
setc cl; spill CF x420 to reg (rcx)
clc;
movzx r11, r11b
adcx r11, r12; loading flag
adcx rsi, [ rsp + 0x430 ]
mov r11, 0x2341f27177344 ; moving imm to reg
mov rdx, r10; x366 to rdx
mulx rdx, r10, r11; x383, x382<- x366 * 0x2341f27177344
seto r14b; spill OF x364 to reg (r14)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, r12; loading flag
adox r8, r10
setc r9b; spill CF x379 to reg (r9)
clc;
movzx rcx, cl
adcx rcx, r12; loading flag
adcx rsi, r8
movzx rcx, r14b; x365, copying x364 here, cause x364 is needed in a reg for other than x365, namely all: , x365, size: 1
lea rcx, [ rcx + rbx ]
seto bl; spill OF x407 to reg (rbx)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
movzx r10, byte [ rsp + 0x420 ]; load byte memx338 to register64
movzx r9, r9b
adox r9, r14; loading flag
adox rcx, r10
movzx r10, bl; x408, copying x407 here, cause x407 is needed in a reg for other than x408, namely all: , x408, size: 1
lea r10, [ r10 + rdx ]
adcx r10, rcx
seto r9b; spill OF x425 to reg (r9)
adc r9b, 0x0
movzx r9, r9b
mov rdx, [ rsp + 0x140 ]; load m64 x438 to register64
adox rdx, [ rsp + 0x428 ]
mov r8, 0xffffffffffffffff ; moving imm to reg
mulx rbx, rcx, r8; x482, x481<- x453 * 0xffffffffffffffff
adcx rcx, rdx
mulx rcx, r12, r8; x480, x479<- x453 * 0xffffffffffffffff
mov r14, [ rsp + 0x150 ]; load m64 x440 to register64
mov r11, [ rsp + 0x438 ]; x455, copying x413 here, cause x413 is needed in a reg for other than x455, namely all: , x455--x456, size: 1
adox r11, r14
seto r14b; spill OF x456 to reg (r14)
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, rbx
adcx r12, r11
setc bl; spill CF x499 to reg (rbx)
clc;
adcx r12, [ rsp + 0x418 ]
mov r11, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r11; 0xffffffffffffffff, swapping with x453, which is currently in rdx
mov byte [ rsp + 0x450 ], r9b; spilling byte x425 to mem
mulx r8, r9, r12; x569, x568<- x540 * 0xffffffffffffffff
seto dl; spill OF x484 to reg (rdx)
mov [ rsp + 0x458 ], r10; spilling x423 to mem
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r9, r12
setc r9b; spill CF x541 to reg (r9)
clc;
movzx r14, r14b
adcx r14, r10; loading flag
adcx rdi, [ rsp + 0x158 ]
mov r14, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r14; 0xffffffffffffffff, swapping with x484, which is currently in rdx
mov [ rsp + 0x460 ], rsi; spilling x421 to mem
mulx r10, rsi, r11; x478, x477<- x453 * 0xffffffffffffffff
setc dl; spill CF x458 to reg (rdx)
clc;
mov [ rsp + 0x468 ], r15; spilling x419 to mem
mov r15, -0x1 ; moving imm to reg
movzx r14, r14b
adcx r14, r15; loading flag
adcx rcx, rsi
seto r14b; spill OF x584 to reg (r14)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rsi, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, rsi; loading flag
adox rdi, rcx
mov rbx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r12; x540, swapping with x458, which is currently in rdx
mulx rcx, r15, rbx; x567, x566<- x540 * 0xffffffffffffffff
seto sil; spill OF x501 to reg (rsi)
mov rbx, -0x1 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbx, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, rbx; loading flag
adox rdi, [ rsp + 0x410 ]
setc r9b; spill CF x486 to reg (r9)
clc;
adcx r15, r8
seto r8b; spill OF x543 to reg (r8)
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, rbx; loading flag
adox rdi, r15
setc r14b; spill CF x571 to reg (r14)
clc;
movzx r12, r12b
adcx r12, rbx; loading flag
adcx rbp, [ rsp + 0x160 ]
setc r12b; spill CF x460 to reg (r12)
seto r15b; spill OF x586 to reg (r15)
mov rbx, rdi; x600, copying x585 here, cause x585 is needed in a reg for other than x600, namely all: , x616, x600--x601, size: 2
mov [ rsp + 0x470 ], rcx; spilling x567 to mem
mov rcx, 0xffffffffffffffff ; moving imm to reg
sub rbx, rcx
mov rcx, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, r11; x453, swapping with x540, which is currently in rdx
mov [ rsp + 0x478 ], rbx; spilling x600 to mem
mov byte [ rsp + 0x480 ], r12b; spilling byte x460 to mem
mulx rbx, r12, rcx; x476, x475<- x453 * 0xfdc1767ae2ffffff
mov rcx, -0x1 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rcx, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, rcx; loading flag
adox r10, r12
seto r9b; spill OF x488 to reg (r9)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
movzx rsi, sil
adox rsi, r12; loading flag
adox rbp, r10
mov rsi, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rsi; 0xffffffffffffffff, swapping with x453, which is currently in rdx
mulx r10, rcx, r11; x565, x564<- x540 * 0xffffffffffffffff
seto r12b; spill OF x503 to reg (r12)
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r8, r8b
adox r8, rdx; loading flag
adox rbp, [ rsp + 0x408 ]
seto r8b; spill OF x545 to reg (r8)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, rdx; loading flag
adox rcx, [ rsp + 0x470 ]
seto r14b; spill OF x573 to reg (r14)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, rdx; loading flag
adox rbp, rcx
seto r15b; spill OF x588 to reg (r15)
mov rcx, rbp; x602, copying x587 here, cause x587 is needed in a reg for other than x602, namely all: , x602--x603, x617, size: 2
mov rdx, 0xffffffffffffffff ; moving imm to reg
sbb rcx, rdx
mov rdx, [ rsp + 0x168 ]; load m64 x446 to register64
mov [ rsp + 0x488 ], rcx; spilling x602 to mem
movzx rcx, byte [ rsp + 0x480 ]; load byte memx460 to register64
mov byte [ rsp + 0x490 ], r15b; spilling byte x588 to mem
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rcx, r15; loading flag
adox rdx, [ rsp + 0x468 ]
mov rcx, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, rcx; 0x7bc65c783158aea3, swapping with x461, which is currently in rdx
mov [ rsp + 0x498 ], r10; spilling x565 to mem
mulx r15, r10, rsi; x474, x473<- x453 * 0x7bc65c783158aea3
seto dl; spill OF x462 to reg (rdx)
mov [ rsp + 0x4a0 ], r15; spilling x474 to mem
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r15, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, r15; loading flag
adox rbx, r10
setc r9b; spill CF x603 to reg (r9)
clc;
movzx r12, r12b
adcx r12, r15; loading flag
adcx rcx, rbx
mov r12, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, r11; x540, swapping with x462, which is currently in rdx
mulx r10, rbx, r12; x563, x562<- x540 * 0xfdc1767ae2ffffff
seto r15b; spill OF x490 to reg (r15)
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, r12; loading flag
adox rcx, [ rsp + 0x400 ]
setc r8b; spill CF x505 to reg (r8)
clc;
movzx r14, r14b
adcx r14, r12; loading flag
adcx rbx, [ rsp + 0x498 ]
seto r14b; spill OF x547 to reg (r14)
movzx r12, byte [ rsp + 0x490 ]; load byte memx588 to register64
mov [ rsp + 0x4a8 ], r10; spilling x563 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r12, r10; loading flag
adox rcx, rbx
setc r12b; spill CF x575 to reg (r12)
seto bl; spill OF x590 to reg (rbx)
movzx r10, r9b; x603, copying x603 here, cause x603 is needed in a reg for other than x603, namely all: , x604--x605, size: 1
add r10, -0x1
mov r10, rcx; x604, copying x589 here, cause x589 is needed in a reg for other than x604, namely all: , x618, x604--x605, size: 2
mov r9, 0xffffffffffffffff ; moving imm to reg
sbb r10, r9
mov r9, [ rsp + 0x180 ]; load m64 x448 to register64
mov [ rsp + 0x4b0 ], r10; spilling x604 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r11, r11b
adox r11, r10; loading flag
adox r9, [ rsp + 0x460 ]
mov r11, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, r11; 0x6cfc5fd681c52056, swapping with x540, which is currently in rdx
mov byte [ rsp + 0x4b8 ], bl; spilling byte x590 to mem
mulx r10, rbx, rsi; x472, x471<- x453 * 0x6cfc5fd681c52056
seto dl; spill OF x464 to reg (rdx)
mov [ rsp + 0x4c0 ], r10; spilling x472 to mem
mov r10, -0x1 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r10, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, r10; loading flag
adox rbx, [ rsp + 0x4a0 ]
setc r15b; spill CF x605 to reg (r15)
clc;
movzx r8, r8b
adcx r8, r10; loading flag
adcx r9, rbx
seto r8b; spill OF x492 to reg (r8)
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, rbx; loading flag
adox r9, [ rsp + 0x3f0 ]
mov r14, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, r14; 0x7bc65c783158aea3, swapping with x464, which is currently in rdx
mulx r10, rbx, r11; x561, x560<- x540 * 0x7bc65c783158aea3
setc dl; spill CF x507 to reg (rdx)
clc;
mov [ rsp + 0x4c8 ], r10; spilling x561 to mem
mov r10, -0x1 ; moving imm to reg
movzx r12, r12b
adcx r12, r10; loading flag
adcx rbx, [ rsp + 0x4a8 ]
seto r12b; spill OF x549 to reg (r12)
movzx r10, byte [ rsp + 0x4b8 ]; load byte memx590 to register64
mov byte [ rsp + 0x4d0 ], dl; spilling byte x507 to mem
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
adox r10, rdx; loading flag
adox r9, rbx
mov r10, [ rsp + 0x178 ]; load m64 x450 to register64
seto bl; spill OF x592 to reg (rbx)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, rdx; loading flag
adox r10, [ rsp + 0x458 ]
setc r14b; spill CF x577 to reg (r14)
seto dl; spill OF x466 to reg (rdx)
mov byte [ rsp + 0x4d8 ], bl; spilling byte x592 to mem
movzx rbx, r15b; x605, copying x605 here, cause x605 is needed in a reg for other than x605, namely all: , x606--x607, size: 1
add rbx, -0x1
mov rbx, r9; x606, copying x591 here, cause x591 is needed in a reg for other than x606, namely all: , x606--x607, x619, size: 2
mov r15, 0xfdc1767ae2ffffff ; moving imm to reg
sbb rbx, r15
mov r15, 0x2341f27177344 ; moving imm to reg
xchg rdx, r15; 0x2341f27177344, swapping with x466, which is currently in rdx
mov [ rsp + 0x4e0 ], rbx; spilling x606 to mem
mulx rsi, rbx, rsi; x470, x469<- x453 * 0x2341f27177344
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r8, r8b
adox r8, rdx; loading flag
adox rbx, [ rsp + 0x4c0 ]
setc r8b; spill CF x607 to reg (r8)
movzx rdx, byte [ rsp + 0x4d0 ]; load byte memx507 to register64
clc;
mov byte [ rsp + 0x4e8 ], r15b; spilling byte x466 to mem
mov r15, -0x1 ; moving imm to reg
adcx rdx, r15; loading flag
adcx r10, rbx
mov rdx, 0x6cfc5fd681c52056 ; moving imm to reg
mulx rbx, r15, r11; x559, x558<- x540 * 0x6cfc5fd681c52056
seto dl; spill OF x494 to reg (rdx)
mov [ rsp + 0x4f0 ], rbx; spilling x559 to mem
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r12, r12b
adox r12, rbx; loading flag
adox r10, [ rsp + 0x3e8 ]
seto r12b; spill OF x551 to reg (r12)
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, rbx; loading flag
adox r15, [ rsp + 0x4c8 ]
seto r14b; spill OF x579 to reg (r14)
movzx rbx, byte [ rsp + 0x4d8 ]; load byte memx592 to register64
mov byte [ rsp + 0x4f8 ], r12b; spilling byte x551 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbx, r12; loading flag
adox r10, r15
movzx rbx, dl; x495, copying x494 here, cause x494 is needed in a reg for other than x495, namely all: , x495, size: 1
lea rbx, [ rbx + rsi ]
movzx rsi, byte [ rsp + 0x450 ]; load byte memx425 to register64
seto dl; spill OF x594 to reg (rdx)
movzx r15, byte [ rsp + 0x4e8 ]; load byte memx466 to register64
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
adox r15, r12; loading flag
adox rsi, [ rsp + 0x170 ]
setc r15b; spill CF x509 to reg (r15)
seto r12b; spill OF x468 to reg (r12)
mov byte [ rsp + 0x500 ], dl; spilling byte x594 to mem
movzx rdx, r8b; x607, copying x607 here, cause x607 is needed in a reg for other than x607, namely all: , x608--x609, size: 1
add rdx, -0x1
mov r8, r10; x608, copying x593 here, cause x593 is needed in a reg for other than x608, namely all: , x620, x608--x609, size: 2
mov byte [ rsp + 0x508 ], r14b; spilling byte x579 to mem
mov r14, 0x7bc65c783158aea3 ; moving imm to reg
sbb r8, r14
mov r14, -0x1 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r14, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, r14; loading flag
adox rsi, rbx
setc r15b; spill CF x609 to reg (r15)
movzx rbx, byte [ rsp + 0x4f8 ]; load byte memx551 to register64
clc;
adcx rbx, r14; loading flag
adcx rsi, [ rsp + 0x3e0 ]
mov rbx, 0x2341f27177344 ; moving imm to reg
mov rdx, rbx; 0x2341f27177344 to rdx
mulx r11, rbx, r11; x557, x556<- x540 * 0x2341f27177344
setc r14b; spill CF x553 to reg (r14)
movzx rdx, byte [ rsp + 0x508 ]; load byte memx579 to register64
clc;
mov [ rsp + 0x510 ], r8; spilling x608 to mem
mov r8, -0x1 ; moving imm to reg
adcx rdx, r8; loading flag
adcx rbx, [ rsp + 0x4f0 ]
setc dl; spill CF x581 to reg (rdx)
movzx r8, byte [ rsp + 0x500 ]; load byte memx594 to register64
clc;
mov [ rsp + 0x518 ], r11; spilling x557 to mem
mov r11, -0x1 ; moving imm to reg
adcx r8, r11; loading flag
adcx rsi, rbx
setc r8b; spill CF x596 to reg (r8)
seto bl; spill OF x511 to reg (rbx)
movzx r11, r15b; x609, copying x609 here, cause x609 is needed in a reg for other than x609, namely all: , x610--x611, size: 1
add r11, -0x1
mov r11, rsi; x610, copying x595 here, cause x595 is needed in a reg for other than x610, namely all: , x610--x611, x621, size: 2
mov r15, 0x6cfc5fd681c52056 ; moving imm to reg
sbb r11, r15
movzx r15, bl; x512, copying x511 here, cause x511 is needed in a reg for other than x512, namely all: , x512, size: 1
movzx r12, r12b
lea r15, [ r15 + r12 ]
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbx, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, rbx; loading flag
adox r15, [ rsp + 0x3f8 ]
movzx r14, dl; x582, copying x581 here, cause x581 is needed in a reg for other than x582, namely all: , x582, size: 1
mov r12, [ rsp + 0x518 ]; load m64 x557 to register64
lea r14, [ r14 + r12 ]; r8/64 + m8
seto r12b; spill OF x555 to reg (r12)
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, rdx; loading flag
adox r15, r14
seto r8b; spill OF x598 to reg (r8)
mov r14, r15; x612, copying x597 here, cause x597 is needed in a reg for other than x612, namely all: , x612--x613, x622, size: 2
mov rbx, 0x2341f27177344 ; moving imm to reg
sbb r14, rbx
movzx rdx, r8b; x599, copying x598 here, cause x598 is needed in a reg for other than x599, namely all: , x599, size: 1
movzx r12, r12b
lea rdx, [ rdx + r12 ]
sbb rdx, 0x00000000
mov r12, [ rsp + 0x4e0 ]; x619, copying x606 here, cause x606 is needed in a reg for other than x619, namely all: , x619, size: 1
cmovc r12, r9; if CF, x619<- x591 (nzVar)
mov r9, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r9 + 0x18 ], r12; out1[3] = x619
mov r8, [ rsp + 0x4b0 ]; x618, copying x604 here, cause x604 is needed in a reg for other than x618, namely all: , x618, size: 1
cmovc r8, rcx; if CF, x618<- x589 (nzVar)
cmovc r14, r15; if CF, x622<- x597 (nzVar)
mov [ r9 + 0x10 ], r8; out1[2] = x618
mov rcx, [ rsp + 0x478 ]; x616, copying x600 here, cause x600 is needed in a reg for other than x616, namely all: , x616, size: 1
cmovc rcx, rdi; if CF, x616<- x585 (nzVar)
mov [ r9 + 0x30 ], r14; out1[6] = x622
mov [ r9 + 0x0 ], rcx; out1[0] = x616
cmovc r11, rsi; if CF, x621<- x595 (nzVar)
mov rdi, [ rsp + 0x510 ]; x620, copying x608 here, cause x608 is needed in a reg for other than x620, namely all: , x620, size: 1
cmovc rdi, r10; if CF, x620<- x593 (nzVar)
mov r10, [ rsp + 0x488 ]; x617, copying x602 here, cause x602 is needed in a reg for other than x617, namely all: , x617, size: 1
cmovc r10, rbp; if CF, x617<- x587 (nzVar)
mov [ r9 + 0x28 ], r11; out1[5] = x621
mov [ r9 + 0x8 ], r10; out1[1] = x617
mov [ r9 + 0x20 ], rdi; out1[4] = x620
mov rbx, [ rsp + 0x520 ]; restoring from stack
mov rbp, [ rsp + 0x528 ]; restoring from stack
mov r12, [ rsp + 0x530 ]; restoring from stack
mov r13, [ rsp + 0x538 ]; restoring from stack
mov r14, [ rsp + 0x540 ]; restoring from stack
mov r15, [ rsp + 0x548 ]; restoring from stack
add rsp, 0x550 
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; clocked at 4478 MHz
; first cyclecount 422.41, best 421.6, lastGood 477.1304347826087
; seed 971834780550536 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 53356 ms / 500 runs=> 106.712ms/run
; Time spent for assembling and measureing (initial batch_size=23, initial num_batches=101): 1070 ms
; Ratio (time for assembling + measure)/(total runtime for 500runs): 0.020053977059749605
; number reverted permutation/ tried permutation: 159 / 227 =70.044%
; number reverted decision/ tried decision: 177 / 274 =64.599%