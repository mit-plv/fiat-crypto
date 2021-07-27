SECTION .text
	GLOBAL mul_p434
mul_p434:
sub rsp, 0x890 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x860 ], rbx; saving to stack
mov [ rsp + 0x868 ], rbp; saving to stack
mov [ rsp + 0x870 ], r12; saving to stack
mov [ rsp + 0x878 ], r13; saving to stack
mov [ rsp + 0x880 ], r14; saving to stack
mov [ rsp + 0x888 ], r15; saving to stack
mov rax, [ rsi + 0x28 ]; load m64 x5 to register64
xchg rdx, rax; x5, swapping with arg2, which is currently in rdx
mulx r10, r11, [ rax + 0x0 ]; x439, x438<- x5 * arg2[0]
mulx rbx, rbp, [ rax + 0x10 ]; x435, x434<- x5 * arg2[2]
mulx r12, r13, [ rax + 0x8 ]; x437, x436<- x5 * arg2[1]
add r13, r10; could be done better, if r0 has been u8 as well
adcx rbp, r12
mulx r14, r15, [ rax + 0x18 ]; x433, x432<- x5 * arg2[3]
mulx rcx, r8, [ rax + 0x20 ]; x431, x430<- x5 * arg2[4]
adcx r15, rbx
adcx r8, r14
mulx r9, r10, [ rax + 0x28 ]; x429, x428<- x5 * arg2[5]
mulx rdx, rbx, [ rax + 0x30 ]; x427, x426<- x5 * arg2[6]
adcx r10, rcx
adcx rbx, r9
adc rdx, 0x0
mov r12, [ rsi + 0x0 ]; load m64 x7 to register64
xchg rdx, r12; x7, swapping with x452, which is currently in rdx
mulx r14, rcx, [ rax + 0x0 ]; x21, x20<- x7 * arg2[0]
mov r9, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rcx; x20, swapping with x7, which is currently in rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov [ rsp + 0x8 ], r12; spilling x452 to mem
mulx rdi, r12, r9; x48, x47<- x20 * 0xffffffffffffffff
mov r9, rdx; preserving value of x20 into a new reg
mov rdx, [ rax + 0x8 ]; saving arg2[1] in rdx.
mov [ rsp + 0x10 ], rbx; spilling x450 to mem
mov [ rsp + 0x18 ], r10; spilling x448 to mem
mulx rbx, r10, rcx; x19, x18<- x7 * arg2[1]
add r12, r9; could be done better, if r0 has been u8 as well
mov r12, 0xffffffffffffffff ; moving imm to reg
mov rdx, r9; x20 to rdx
mov [ rsp + 0x20 ], r8; spilling x446 to mem
mulx r9, r8, r12; x46, x45<- x20 * 0xffffffffffffffff
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r10, r14
seto r14b; spill OF x23 to reg (r14)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r8, rdi
adcx r8, r10
mov rdi, [ rsi + 0x8 ]; load m64 x1 to register64
xchg rdx, rdi; x1, swapping with x20, which is currently in rdx
mulx r10, r12, [ rax + 0x0 ]; x91, x90<- x1 * arg2[0]
mov [ rsp + 0x28 ], r15; spilling x444 to mem
seto r15b; spill OF x50 to reg (r15)
mov [ rsp + 0x30 ], rbp; spilling x442 to mem
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, r8
mov r8, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r12; x105, swapping with x1, which is currently in rdx
mov [ rsp + 0x38 ], r13; spilling x440 to mem
mulx rbp, r13, r8; x134, x133<- x105 * 0xffffffffffffffff
seto r8b; spill OF x106 to reg (r8)
mov [ rsp + 0x40 ], r11; spilling x438 to mem
mov r11, -0x2 ; moving imm to reg
inc r11; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, rdx
xchg rdx, rcx; x7, swapping with x105, which is currently in rdx
mulx r13, r11, [ rax + 0x10 ]; x17, x16<- x7 * arg2[2]
mov [ rsp + 0x48 ], r13; spilling x17 to mem
seto r13b; spill OF x149 to reg (r13)
mov [ rsp + 0x50 ], rbp; spilling x134 to mem
mov rbp, 0x0 ; moving imm to reg
dec rbp; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r14, r14b
adox r14, rbp; loading flag
adox rbx, r11
mov r14, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r14; 0xffffffffffffffff, swapping with x7, which is currently in rdx
mulx r11, rbp, rdi; x44, x43<- x20 * 0xffffffffffffffff
setc dl; spill CF x65 to reg (rdx)
clc;
mov [ rsp + 0x58 ], r11; spilling x44 to mem
mov r11, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, r11; loading flag
adcx r9, rbp
setc r15b; spill CF x52 to reg (r15)
clc;
movzx rdx, dl
adcx rdx, r11; loading flag
adcx rbx, r9
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx rbp, r9, r12; x89, x88<- x1 * arg2[1]
mov r11, 0xffffffffffffffff ; moving imm to reg
mov rdx, rcx; x105 to rdx
mov [ rsp + 0x60 ], rbp; spilling x89 to mem
mulx rcx, rbp, r11; x132, x131<- x105 * 0xffffffffffffffff
setc r11b; spill CF x67 to reg (r11)
clc;
adcx r9, r10
seto r10b; spill OF x25 to reg (r10)
mov [ rsp + 0x68 ], rcx; spilling x132 to mem
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r8, r8b
adox r8, rcx; loading flag
adox rbx, r9
seto r8b; spill OF x108 to reg (r8)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rbp, [ rsp + 0x50 ]
seto r9b; spill OF x136 to reg (r9)
dec rcx; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r13, r13b
adox r13, rcx; loading flag
adox rbx, rbp
mov r13, [ rsi + 0x10 ]; load m64 x2 to register64
xchg rdx, r13; x2, swapping with x105, which is currently in rdx
mulx rbp, rcx, [ rax + 0x0 ]; x178, x177<- x2 * arg2[0]
mov [ rsp + 0x70 ], rbp; spilling x178 to mem
setc bpl; spill CF x93 to reg (rbp)
clc;
adcx rcx, rbx
mov rbx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rcx; x192, swapping with x2, which is currently in rdx
mov byte [ rsp + 0x78 ], r9b; spilling byte x136 to mem
mov byte [ rsp + 0x80 ], r8b; spilling byte x108 to mem
mulx r9, r8, rbx; x221, x220<- x192 * 0xffffffffffffffff
seto bl; spill OF x151 to reg (rbx)
mov [ rsp + 0x88 ], r9; spilling x221 to mem
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, rdx
mov r8, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, r8; 0xfdc1767ae2ffffff, swapping with x192, which is currently in rdx
mov byte [ rsp + 0x90 ], bl; spilling byte x151 to mem
mulx r9, rbx, rdi; x42, x41<- x20 * 0xfdc1767ae2ffffff
mov [ rsp + 0x98 ], r9; spilling x42 to mem
mov r9, rdx; preserving value of 0xfdc1767ae2ffffff into a new reg
mov rdx, [ rax + 0x18 ]; saving arg2[3] in rdx.
mov byte [ rsp + 0xa0 ], r11b; spilling byte x67 to mem
mov byte [ rsp + 0xa8 ], bpl; spilling byte x93 to mem
mulx r11, rbp, r14; x15, x14<- x7 * arg2[3]
mov rdx, r12; x1 to rdx
mulx r12, r9, [ rax + 0x10 ]; x87, x86<- x1 * arg2[2]
mov [ rsp + 0xb0 ], r12; spilling x87 to mem
setc r12b; spill CF x193 to reg (r12)
clc;
mov [ rsp + 0xb8 ], r11; spilling x15 to mem
mov r11, -0x1 ; moving imm to reg
movzx r10, r10b
adcx r10, r11; loading flag
adcx rbp, [ rsp + 0x48 ]
setc r10b; spill CF x27 to reg (r10)
clc;
movzx r15, r15b
adcx r15, r11; loading flag
adcx rbx, [ rsp + 0x58 ]
setc r15b; spill CF x54 to reg (r15)
movzx r11, byte [ rsp + 0xa8 ]; load byte memx93 to register64
clc;
mov byte [ rsp + 0xc0 ], r10b; spilling byte x27 to mem
mov r10, -0x1 ; moving imm to reg
adcx r11, r10; loading flag
adcx r9, [ rsp + 0x60 ]
setc r11b; spill CF x95 to reg (r11)
movzx r10, byte [ rsp + 0xa0 ]; load byte memx67 to register64
clc;
mov byte [ rsp + 0xc8 ], r15b; spilling byte x54 to mem
mov r15, -0x1 ; moving imm to reg
adcx r10, r15; loading flag
adcx rbp, rbx
seto r10b; spill OF x236 to reg (r10)
movzx rbx, byte [ rsp + 0x80 ]; load byte memx108 to register64
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
adox rbx, r15; loading flag
adox rbp, r9
mov rbx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbx; 0xffffffffffffffff, swapping with x1, which is currently in rdx
mulx r9, r15, r13; x130, x129<- x105 * 0xffffffffffffffff
seto dl; spill OF x110 to reg (rdx)
mov [ rsp + 0xd0 ], r9; spilling x130 to mem
movzx r9, byte [ rsp + 0x78 ]; load byte memx136 to register64
mov byte [ rsp + 0xd8 ], r11b; spilling byte x95 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
adox r9, r11; loading flag
adox r15, [ rsp + 0x68 ]
mov r9b, dl; preserving value of x110 into a new reg
mov rdx, [ rax + 0x8 ]; saving arg2[1] in rdx.
mov byte [ rsp + 0xe0 ], r10b; spilling byte x236 to mem
mulx r11, r10, rcx; x176, x175<- x2 * arg2[1]
mov [ rsp + 0xe8 ], r11; spilling x176 to mem
seto r11b; spill OF x138 to reg (r11)
mov byte [ rsp + 0xf0 ], r9b; spilling byte x110 to mem
movzx r9, byte [ rsp + 0x90 ]; load byte memx151 to register64
mov byte [ rsp + 0xf8 ], r12b; spilling byte x193 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r9, r12; loading flag
adox rbp, r15
seto r9b; spill OF x153 to reg (r9)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r10, [ rsp + 0x70 ]
setc r15b; spill CF x69 to reg (r15)
movzx r12, byte [ rsp + 0xf8 ]; load byte memx193 to register64
clc;
mov byte [ rsp + 0x100 ], r9b; spilling byte x153 to mem
mov r9, -0x1 ; moving imm to reg
adcx r12, r9; loading flag
adcx rbp, r10
mov r12, 0xffffffffffffffff ; moving imm to reg
mov rdx, r12; 0xffffffffffffffff to rdx
mulx r12, r10, r8; x219, x218<- x192 * 0xffffffffffffffff
seto r9b; spill OF x180 to reg (r9)
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r10, [ rsp + 0x88 ]
seto dl; spill OF x223 to reg (rdx)
mov [ rsp + 0x108 ], r12; spilling x219 to mem
movzx r12, byte [ rsp + 0xe0 ]; load byte memx236 to register64
mov byte [ rsp + 0x110 ], r9b; spilling byte x180 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r12, r9; loading flag
adox rbp, r10
mov r12, [ rsi + 0x18 ]; load m64 x3 to register64
xchg rdx, r12; x3, swapping with x223, which is currently in rdx
mulx r10, r9, [ rax + 0x0 ]; x265, x264<- x3 * arg2[0]
mov [ rsp + 0x118 ], r10; spilling x265 to mem
setc r10b; spill CF x195 to reg (r10)
clc;
adcx r9, rbp
mov rbp, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r9; x279, swapping with x3, which is currently in rdx
mov byte [ rsp + 0x120 ], r12b; spilling byte x223 to mem
mov byte [ rsp + 0x128 ], r10b; spilling byte x195 to mem
mulx r12, r10, rbp; x308, x307<- x279 * 0xffffffffffffffff
mov byte [ rsp + 0x130 ], r11b; spilling byte x138 to mem
mov byte [ rsp + 0x138 ], r15b; spilling byte x69 to mem
mulx r11, r15, rbp; x306, x305<- x279 * 0xffffffffffffffff
setc bpl; spill CF x280 to reg (rbp)
clc;
adcx r15, r12
mov r12, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x140 ], r15; spilling x309 to mem
mov byte [ rsp + 0x148 ], bpl; spilling byte x280 to mem
mulx r15, rbp, r12; x304, x303<- x279 * 0xffffffffffffffff
adcx rbp, r11
mov r11, 0x7bc65c783158aea3 ; moving imm to reg
mov [ rsp + 0x150 ], rbp; spilling x311 to mem
mulx r12, rbp, r11; x300, x299<- x279 * 0x7bc65c783158aea3
mov r11, 0xfdc1767ae2ffffff ; moving imm to reg
mov [ rsp + 0x158 ], r10; spilling x307 to mem
mov [ rsp + 0x160 ], r12; spilling x300 to mem
mulx r10, r12, r11; x302, x301<- x279 * 0xfdc1767ae2ffffff
adcx r12, r15
adcx rbp, r10
mov r15, 0x6cfc5fd681c52056 ; moving imm to reg
mulx r10, r11, r15; x298, x297<- x279 * 0x6cfc5fd681c52056
mov r15, [ rsp + 0x160 ]; x317, copying x300 here, cause x300 is needed in a reg for other than x317, namely all: , x317--x318, size: 1
adcx r15, r11
mov r11, 0x2341f27177344 ; moving imm to reg
mov [ rsp + 0x168 ], r15; spilling x317 to mem
mov [ rsp + 0x170 ], rbp; spilling x315 to mem
mulx r15, rbp, r11; x296, x295<- x279 * 0x2341f27177344
adcx rbp, r10
xchg rdx, r14; x7, swapping with x279, which is currently in rdx
mulx r10, r11, [ rax + 0x20 ]; x13, x12<- x7 * arg2[4]
mov [ rsp + 0x178 ], rbp; spilling x319 to mem
mov rbp, 0x0 ; moving imm to reg
adcx r15, rbp
clc;
adcx r14, [ rsp + 0x158 ]
seto r14b; spill OF x238 to reg (r14)
movzx rbp, byte [ rsp + 0xc0 ]; load byte memx27 to register64
mov [ rsp + 0x180 ], r15; spilling x321 to mem
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbp, r15; loading flag
adox r11, [ rsp + 0xb8 ]
mov rbp, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, rdi; x20, swapping with x7, which is currently in rdx
mov [ rsp + 0x188 ], r12; spilling x313 to mem
mulx r15, r12, rbp; x40, x39<- x20 * 0x7bc65c783158aea3
seto bpl; spill OF x29 to reg (rbp)
mov [ rsp + 0x190 ], r15; spilling x40 to mem
movzx r15, byte [ rsp + 0xc8 ]; load byte memx54 to register64
mov [ rsp + 0x198 ], r10; spilling x13 to mem
mov r10, -0x1 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r10, -0x1 ; moving imm to reg
adox r15, r10; loading flag
adox r12, [ rsp + 0x98 ]
mov r15, rdx; preserving value of x20 into a new reg
mov rdx, [ rax + 0x18 ]; saving arg2[3] in rdx.
mov byte [ rsp + 0x1a0 ], bpl; spilling byte x29 to mem
mulx r10, rbp, rbx; x85, x84<- x1 * arg2[3]
mov [ rsp + 0x1a8 ], r10; spilling x85 to mem
setc r10b; spill CF x323 to reg (r10)
mov byte [ rsp + 0x1b0 ], r14b; spilling byte x238 to mem
movzx r14, byte [ rsp + 0x138 ]; load byte memx69 to register64
clc;
mov [ rsp + 0x1b8 ], rbp; spilling x84 to mem
mov rbp, -0x1 ; moving imm to reg
adcx r14, rbp; loading flag
adcx r11, r12
mov r14, [ rsp + 0x1b8 ]; load m64 x84 to register64
seto r12b; spill OF x56 to reg (r12)
movzx rbp, byte [ rsp + 0xd8 ]; load byte memx95 to register64
mov byte [ rsp + 0x1c0 ], r10b; spilling byte x323 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbp, r10; loading flag
adox r14, [ rsp + 0xb0 ]
setc bpl; spill CF x71 to reg (rbp)
movzx r10, byte [ rsp + 0xf0 ]; load byte memx110 to register64
clc;
mov byte [ rsp + 0x1c8 ], r12b; spilling byte x56 to mem
mov r12, -0x1 ; moving imm to reg
adcx r10, r12; loading flag
adcx r11, r14
mov r10, 0xfdc1767ae2ffffff ; moving imm to reg
mov rdx, r13; x105 to rdx
mulx r13, r14, r10; x128, x127<- x105 * 0xfdc1767ae2ffffff
seto r12b; spill OF x97 to reg (r12)
movzx r10, byte [ rsp + 0x130 ]; load byte memx138 to register64
mov [ rsp + 0x1d0 ], r13; spilling x128 to mem
mov r13, -0x1 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r13, -0x1 ; moving imm to reg
adox r10, r13; loading flag
adox r14, [ rsp + 0xd0 ]
seto r10b; spill OF x140 to reg (r10)
movzx r13, byte [ rsp + 0x100 ]; load byte memx153 to register64
mov byte [ rsp + 0x1d8 ], r12b; spilling byte x97 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
adox r13, r12; loading flag
adox r11, r14
xchg rdx, rcx; x2, swapping with x105, which is currently in rdx
mulx r13, r14, [ rax + 0x10 ]; x174, x173<- x2 * arg2[2]
seto r12b; spill OF x155 to reg (r12)
mov [ rsp + 0x1e0 ], r13; spilling x174 to mem
movzx r13, byte [ rsp + 0x110 ]; load byte memx180 to register64
mov byte [ rsp + 0x1e8 ], r10b; spilling byte x140 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r13, r10; loading flag
adox r14, [ rsp + 0xe8 ]
setc r13b; spill CF x112 to reg (r13)
movzx r10, byte [ rsp + 0x128 ]; load byte memx195 to register64
clc;
mov byte [ rsp + 0x1f0 ], r12b; spilling byte x155 to mem
mov r12, -0x1 ; moving imm to reg
adcx r10, r12; loading flag
adcx r11, r14
mov r10, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r8; x192, swapping with x2, which is currently in rdx
mulx r14, r12, r10; x217, x216<- x192 * 0xffffffffffffffff
setc r10b; spill CF x197 to reg (r10)
mov [ rsp + 0x1f8 ], r14; spilling x217 to mem
movzx r14, byte [ rsp + 0x120 ]; load byte memx223 to register64
clc;
mov byte [ rsp + 0x200 ], r13b; spilling byte x112 to mem
mov r13, -0x1 ; moving imm to reg
adcx r14, r13; loading flag
adcx r12, [ rsp + 0x108 ]
seto r14b; spill OF x182 to reg (r14)
movzx r13, byte [ rsp + 0x1b0 ]; load byte memx238 to register64
mov byte [ rsp + 0x208 ], r10b; spilling byte x197 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r13, r10; loading flag
adox r11, r12
xchg rdx, r9; x3, swapping with x192, which is currently in rdx
mulx r13, r12, [ rax + 0x8 ]; x263, x262<- x3 * arg2[1]
mov r10, [ rsi + 0x20 ]; load m64 x4 to register64
mov [ rsp + 0x210 ], r13; spilling x263 to mem
setc r13b; spill CF x225 to reg (r13)
clc;
adcx r12, [ rsp + 0x118 ]
mov byte [ rsp + 0x218 ], r13b; spilling byte x225 to mem
setc r13b; spill CF x267 to reg (r13)
mov byte [ rsp + 0x220 ], r14b; spilling byte x182 to mem
movzx r14, byte [ rsp + 0x148 ]; load byte memx280 to register64
clc;
mov byte [ rsp + 0x228 ], bpl; spilling byte x71 to mem
mov rbp, -0x1 ; moving imm to reg
adcx r14, rbp; loading flag
adcx r11, r12
xchg rdx, r10; x4, swapping with x3, which is currently in rdx
mulx r14, r12, [ rax + 0x0 ]; x352, x351<- x4 * arg2[0]
setc bpl; spill CF x282 to reg (rbp)
mov [ rsp + 0x230 ], r14; spilling x352 to mem
movzx r14, byte [ rsp + 0x1c0 ]; load byte memx323 to register64
clc;
mov byte [ rsp + 0x238 ], r13b; spilling byte x267 to mem
mov r13, -0x1 ; moving imm to reg
adcx r14, r13; loading flag
adcx r11, [ rsp + 0x140 ]
seto r14b; spill OF x240 to reg (r14)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r12, r11
mov r11, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r12; x366, swapping with x4, which is currently in rdx
mov byte [ rsp + 0x240 ], bpl; spilling byte x282 to mem
mulx r13, rbp, r11; x395, x394<- x366 * 0xffffffffffffffff
seto r11b; spill OF x367 to reg (r11)
mov [ rsp + 0x248 ], r13; spilling x395 to mem
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, rdx
mov rbp, rdx; preserving value of x366 into a new reg
mov rdx, [ rax + 0x28 ]; saving arg2[5] in rdx.
mov byte [ rsp + 0x250 ], r11b; spilling byte x367 to mem
mulx r13, r11, rdi; x11, x10<- x7 * arg2[5]
mov [ rsp + 0x258 ], r13; spilling x11 to mem
seto r13b; spill OF x410 to reg (r13)
mov byte [ rsp + 0x260 ], r14b; spilling byte x240 to mem
movzx r14, byte [ rsp + 0x1a0 ]; load byte memx29 to register64
mov [ rsp + 0x268 ], rbp; spilling x366 to mem
mov rbp, -0x1 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
adox r14, rbp; loading flag
adox r11, [ rsp + 0x198 ]
mov r14, 0x6cfc5fd681c52056 ; moving imm to reg
mov rdx, r14; 0x6cfc5fd681c52056 to rdx
mulx r14, rbp, r15; x38, x37<- x20 * 0x6cfc5fd681c52056
setc dl; spill CF x325 to reg (rdx)
mov [ rsp + 0x270 ], r14; spilling x38 to mem
movzx r14, byte [ rsp + 0x1c8 ]; load byte memx56 to register64
clc;
mov byte [ rsp + 0x278 ], r13b; spilling byte x410 to mem
mov r13, -0x1 ; moving imm to reg
adcx r14, r13; loading flag
adcx rbp, [ rsp + 0x190 ]
seto r14b; spill OF x31 to reg (r14)
movzx r13, byte [ rsp + 0x228 ]; load byte memx71 to register64
mov byte [ rsp + 0x280 ], dl; spilling byte x325 to mem
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
adox r13, rdx; loading flag
adox r11, rbp
mov rdx, rbx; x1 to rdx
mulx rbx, r13, [ rax + 0x20 ]; x83, x82<- x1 * arg2[4]
setc bpl; spill CF x58 to reg (rbp)
mov [ rsp + 0x288 ], rbx; spilling x83 to mem
movzx rbx, byte [ rsp + 0x1d8 ]; load byte memx97 to register64
clc;
mov byte [ rsp + 0x290 ], r14b; spilling byte x31 to mem
mov r14, -0x1 ; moving imm to reg
adcx rbx, r14; loading flag
adcx r13, [ rsp + 0x1a8 ]
mov rbx, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, rcx; x105, swapping with x1, which is currently in rdx
mov byte [ rsp + 0x298 ], bpl; spilling byte x58 to mem
mulx r14, rbp, rbx; x126, x125<- x105 * 0x7bc65c783158aea3
setc bl; spill CF x99 to reg (rbx)
mov [ rsp + 0x2a0 ], r14; spilling x126 to mem
movzx r14, byte [ rsp + 0x200 ]; load byte memx112 to register64
clc;
mov [ rsp + 0x2a8 ], rbp; spilling x125 to mem
mov rbp, -0x1 ; moving imm to reg
adcx r14, rbp; loading flag
adcx r11, r13
mov r14, [ rsp + 0x1d0 ]; load m64 x128 to register64
setc r13b; spill CF x114 to reg (r13)
movzx rbp, byte [ rsp + 0x1e8 ]; load byte memx140 to register64
clc;
mov byte [ rsp + 0x2b0 ], bl; spilling byte x99 to mem
mov rbx, -0x1 ; moving imm to reg
adcx rbp, rbx; loading flag
adcx r14, [ rsp + 0x2a8 ]
mov rbp, rdx; preserving value of x105 into a new reg
mov rdx, [ rax + 0x18 ]; saving arg2[3] in rdx.
mov byte [ rsp + 0x2b8 ], r13b; spilling byte x114 to mem
mulx rbx, r13, r8; x172, x171<- x2 * arg2[3]
mov [ rsp + 0x2c0 ], rbx; spilling x172 to mem
seto bl; spill OF x73 to reg (rbx)
mov [ rsp + 0x2c8 ], r13; spilling x171 to mem
movzx r13, byte [ rsp + 0x1f0 ]; load byte memx155 to register64
mov [ rsp + 0x2d0 ], r12; spilling x4 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r13, r12; loading flag
adox r11, r14
mov r13, [ rsp + 0x2c8 ]; load m64 x171 to register64
setc r14b; spill CF x142 to reg (r14)
movzx r12, byte [ rsp + 0x220 ]; load byte memx182 to register64
clc;
mov byte [ rsp + 0x2d8 ], bl; spilling byte x73 to mem
mov rbx, -0x1 ; moving imm to reg
adcx r12, rbx; loading flag
adcx r13, [ rsp + 0x1e0 ]
seto r12b; spill OF x157 to reg (r12)
movzx rbx, byte [ rsp + 0x208 ]; load byte memx197 to register64
mov byte [ rsp + 0x2e0 ], r14b; spilling byte x142 to mem
mov r14, -0x1 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r14, -0x1 ; moving imm to reg
adox rbx, r14; loading flag
adox r11, r13
mov rbx, 0xfdc1767ae2ffffff ; moving imm to reg
mov rdx, rbx; 0xfdc1767ae2ffffff to rdx
mulx rbx, r13, r9; x215, x214<- x192 * 0xfdc1767ae2ffffff
seto r14b; spill OF x199 to reg (r14)
movzx rdx, byte [ rsp + 0x218 ]; load byte memx225 to register64
mov [ rsp + 0x2e8 ], rbx; spilling x215 to mem
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rdx, rbx; loading flag
adox r13, [ rsp + 0x1f8 ]
seto dl; spill OF x227 to reg (rdx)
movzx rbx, byte [ rsp + 0x260 ]; load byte memx240 to register64
mov byte [ rsp + 0x2f0 ], r14b; spilling byte x199 to mem
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbx, r14; loading flag
adox r11, r13
mov bl, dl; preserving value of x227 into a new reg
mov rdx, [ rax + 0x10 ]; saving arg2[2] in rdx.
mulx r13, r14, r10; x261, x260<- x3 * arg2[2]
mov [ rsp + 0x2f8 ], r13; spilling x261 to mem
setc r13b; spill CF x184 to reg (r13)
mov byte [ rsp + 0x300 ], bl; spilling byte x227 to mem
movzx rbx, byte [ rsp + 0x238 ]; load byte memx267 to register64
clc;
mov byte [ rsp + 0x308 ], r12b; spilling byte x157 to mem
mov r12, -0x1 ; moving imm to reg
adcx rbx, r12; loading flag
adcx r14, [ rsp + 0x210 ]
seto bl; spill OF x242 to reg (rbx)
movzx r12, byte [ rsp + 0x240 ]; load byte memx282 to register64
mov byte [ rsp + 0x310 ], r13b; spilling byte x184 to mem
mov r13, -0x1 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r13, -0x1 ; moving imm to reg
adox r12, r13; loading flag
adox r11, r14
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx r12, r14, [ rsp + 0x2d0 ]; x350, x349<- x4 * arg2[1]
seto r13b; spill OF x284 to reg (r13)
mov [ rsp + 0x318 ], r12; spilling x350 to mem
movzx r12, byte [ rsp + 0x280 ]; load byte memx325 to register64
mov byte [ rsp + 0x320 ], bl; spilling byte x242 to mem
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r12, rbx; loading flag
adox r11, [ rsp + 0x150 ]
mov r12, 0xffffffffffffffff ; moving imm to reg
mov rdx, r12; 0xffffffffffffffff to rdx
mulx r12, rbx, [ rsp + 0x268 ]; x393, x392<- x366 * 0xffffffffffffffff
setc dl; spill CF x269 to reg (rdx)
clc;
adcx rbx, [ rsp + 0x248 ]
mov [ rsp + 0x328 ], r12; spilling x393 to mem
setc r12b; spill CF x397 to reg (r12)
clc;
adcx r14, [ rsp + 0x230 ]
mov byte [ rsp + 0x330 ], r12b; spilling byte x397 to mem
setc r12b; spill CF x354 to reg (r12)
mov byte [ rsp + 0x338 ], r13b; spilling byte x284 to mem
movzx r13, byte [ rsp + 0x250 ]; load byte memx367 to register64
clc;
mov byte [ rsp + 0x340 ], dl; spilling byte x269 to mem
mov rdx, -0x1 ; moving imm to reg
adcx r13, rdx; loading flag
adcx r11, r14
seto r13b; spill OF x327 to reg (r13)
movzx r14, byte [ rsp + 0x278 ]; load byte memx410 to register64
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
adox r14, rdx; loading flag
adox r11, rbx
seto r14b; spill OF x412 to reg (r14)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r11, [ rsp + 0x40 ]
mov rbx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbx; 0xffffffffffffffff, swapping with 0x0, which is currently in rdx
mov byte [ rsp + 0x348 ], r14b; spilling byte x412 to mem
mulx rbx, r14, r11; x482, x481<- x453 * 0xffffffffffffffff
seto dl; spill OF x454 to reg (rdx)
mov [ rsp + 0x350 ], rbx; spilling x482 to mem
mov rbx, -0x2 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, r11
mov r14b, dl; preserving value of x454 into a new reg
mov rdx, [ rax + 0x30 ]; saving arg2[6] in rdx.
mulx rdi, rbx, rdi; x9, x8<- x7 * arg2[6]
mov [ rsp + 0x358 ], rdi; spilling x9 to mem
seto dil; spill OF x497 to reg (rdi)
mov byte [ rsp + 0x360 ], r14b; spilling byte x454 to mem
movzx r14, byte [ rsp + 0x290 ]; load byte memx31 to register64
mov byte [ rsp + 0x368 ], r12b; spilling byte x354 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r14, r12; loading flag
adox rbx, [ rsp + 0x258 ]
mov r14, 0x2341f27177344 ; moving imm to reg
mov rdx, r15; x20 to rdx
mulx rdx, r15, r14; x36, x35<- x20 * 0x2341f27177344
mov r12, rdx; preserving value of x36 into a new reg
mov rdx, [ rax + 0x28 ]; saving arg2[5] in rdx.
mov byte [ rsp + 0x370 ], dil; spilling byte x497 to mem
mulx r14, rdi, rcx; x81, x80<- x1 * arg2[5]
mov [ rsp + 0x378 ], r14; spilling x81 to mem
seto r14b; spill OF x33 to reg (r14)
mov [ rsp + 0x380 ], r12; spilling x36 to mem
movzx r12, byte [ rsp + 0x298 ]; load byte memx58 to register64
mov byte [ rsp + 0x388 ], r13b; spilling byte x327 to mem
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r12, r13; loading flag
adox r15, [ rsp + 0x270 ]
seto r12b; spill OF x60 to reg (r12)
movzx r13, byte [ rsp + 0x2d8 ]; load byte memx73 to register64
mov byte [ rsp + 0x390 ], r14b; spilling byte x33 to mem
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r13, r14; loading flag
adox rbx, r15
setc r13b; spill CF x369 to reg (r13)
movzx r15, byte [ rsp + 0x2b0 ]; load byte memx99 to register64
clc;
adcx r15, r14; loading flag
adcx rdi, [ rsp + 0x288 ]
seto r15b; spill OF x75 to reg (r15)
movzx r14, byte [ rsp + 0x2b8 ]; load byte memx114 to register64
mov byte [ rsp + 0x398 ], r12b; spilling byte x60 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r14, r12; loading flag
adox rbx, rdi
mov r14, 0x6cfc5fd681c52056 ; moving imm to reg
mov rdx, rbp; x105 to rdx
mulx rbp, rdi, r14; x124, x123<- x105 * 0x6cfc5fd681c52056
seto r12b; spill OF x116 to reg (r12)
movzx r14, byte [ rsp + 0x2e0 ]; load byte memx142 to register64
mov [ rsp + 0x3a0 ], rbp; spilling x124 to mem
mov rbp, 0x0 ; moving imm to reg
dec rbp; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r14, rbp; loading flag
adox rdi, [ rsp + 0x2a0 ]
setc r14b; spill CF x101 to reg (r14)
movzx rbp, byte [ rsp + 0x308 ]; load byte memx157 to register64
clc;
mov byte [ rsp + 0x3a8 ], r12b; spilling byte x116 to mem
mov r12, -0x1 ; moving imm to reg
adcx rbp, r12; loading flag
adcx rbx, rdi
xchg rdx, r8; x2, swapping with x105, which is currently in rdx
mulx rbp, rdi, [ rax + 0x20 ]; x170, x169<- x2 * arg2[4]
seto r12b; spill OF x144 to reg (r12)
mov [ rsp + 0x3b0 ], rbp; spilling x170 to mem
movzx rbp, byte [ rsp + 0x310 ]; load byte memx184 to register64
mov byte [ rsp + 0x3b8 ], r14b; spilling byte x101 to mem
mov r14, -0x1 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r14, -0x1 ; moving imm to reg
adox rbp, r14; loading flag
adox rdi, [ rsp + 0x2c0 ]
setc bpl; spill CF x159 to reg (rbp)
movzx r14, byte [ rsp + 0x2f0 ]; load byte memx199 to register64
clc;
mov byte [ rsp + 0x3c0 ], r12b; spilling byte x144 to mem
mov r12, -0x1 ; moving imm to reg
adcx r14, r12; loading flag
adcx rbx, rdi
mov r14, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, r14; 0x7bc65c783158aea3, swapping with x2, which is currently in rdx
mulx rdi, r12, r9; x213, x212<- x192 * 0x7bc65c783158aea3
setc dl; spill CF x201 to reg (rdx)
mov [ rsp + 0x3c8 ], rdi; spilling x213 to mem
movzx rdi, byte [ rsp + 0x300 ]; load byte memx227 to register64
clc;
mov byte [ rsp + 0x3d0 ], bpl; spilling byte x159 to mem
mov rbp, -0x1 ; moving imm to reg
adcx rdi, rbp; loading flag
adcx r12, [ rsp + 0x2e8 ]
setc dil; spill CF x229 to reg (rdi)
movzx rbp, byte [ rsp + 0x320 ]; load byte memx242 to register64
clc;
mov byte [ rsp + 0x3d8 ], dl; spilling byte x201 to mem
mov rdx, -0x1 ; moving imm to reg
adcx rbp, rdx; loading flag
adcx rbx, r12
mov rdx, r10; x3 to rdx
mulx r10, rbp, [ rax + 0x18 ]; x259, x258<- x3 * arg2[3]
seto r12b; spill OF x186 to reg (r12)
mov [ rsp + 0x3e0 ], r10; spilling x259 to mem
movzx r10, byte [ rsp + 0x340 ]; load byte memx269 to register64
mov byte [ rsp + 0x3e8 ], dil; spilling byte x229 to mem
mov rdi, 0x0 ; moving imm to reg
dec rdi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r10, rdi; loading flag
adox rbp, [ rsp + 0x2f8 ]
setc r10b; spill CF x244 to reg (r10)
movzx rdi, byte [ rsp + 0x338 ]; load byte memx284 to register64
clc;
mov byte [ rsp + 0x3f0 ], r12b; spilling byte x186 to mem
mov r12, -0x1 ; moving imm to reg
adcx rdi, r12; loading flag
adcx rbx, rbp
setc dil; spill CF x286 to reg (rdi)
movzx rbp, byte [ rsp + 0x388 ]; load byte memx327 to register64
clc;
adcx rbp, r12; loading flag
adcx rbx, [ rsp + 0x188 ]
mov rbp, rdx; preserving value of x3 into a new reg
mov rdx, [ rsp + 0x2d0 ]; saving x4 in rdx.
mov byte [ rsp + 0x3f8 ], dil; spilling byte x286 to mem
mulx r12, rdi, [ rax + 0x10 ]; x348, x347<- x4 * arg2[2]
mov [ rsp + 0x400 ], r12; spilling x348 to mem
seto r12b; spill OF x271 to reg (r12)
mov byte [ rsp + 0x408 ], r10b; spilling byte x244 to mem
movzx r10, byte [ rsp + 0x368 ]; load byte memx354 to register64
mov byte [ rsp + 0x410 ], r15b; spilling byte x75 to mem
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r10, r15; loading flag
adox rdi, [ rsp + 0x318 ]
mov r10, 0xffffffffffffffff ; moving imm to reg
mov r15, rdx; preserving value of x4 into a new reg
mov rdx, [ rsp + 0x268 ]; saving x366 in rdx.
mov byte [ rsp + 0x418 ], r12b; spilling byte x271 to mem
mov [ rsp + 0x420 ], rdi; spilling x355 to mem
mulx r12, rdi, r10; x391, x390<- x366 * 0xffffffffffffffff
setc r10b; spill CF x329 to reg (r10)
clc;
mov [ rsp + 0x428 ], r12; spilling x391 to mem
mov r12, -0x1 ; moving imm to reg
movzx r13, r13b
adcx r13, r12; loading flag
adcx rbx, [ rsp + 0x420 ]
setc r13b; spill CF x371 to reg (r13)
movzx r12, byte [ rsp + 0x330 ]; load byte memx397 to register64
clc;
mov byte [ rsp + 0x430 ], r10b; spilling byte x329 to mem
mov r10, -0x1 ; moving imm to reg
adcx r12, r10; loading flag
adcx rdi, [ rsp + 0x328 ]
setc r12b; spill CF x399 to reg (r12)
movzx r10, byte [ rsp + 0x348 ]; load byte memx412 to register64
clc;
mov byte [ rsp + 0x438 ], r13b; spilling byte x371 to mem
mov r13, -0x1 ; moving imm to reg
adcx r10, r13; loading flag
adcx rbx, rdi
seto r10b; spill OF x356 to reg (r10)
movzx rdi, byte [ rsp + 0x360 ]; load byte memx454 to register64
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
adox rdi, r13; loading flag
adox rbx, [ rsp + 0x38 ]
mov rdi, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rdi; 0xffffffffffffffff, swapping with x366, which is currently in rdx
mov byte [ rsp + 0x440 ], r12b; spilling byte x399 to mem
mulx r13, r12, r11; x480, x479<- x453 * 0xffffffffffffffff
seto dl; spill OF x456 to reg (rdx)
mov [ rsp + 0x448 ], r13; spilling x480 to mem
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, [ rsp + 0x350 ]
seto r13b; spill OF x484 to reg (r13)
mov byte [ rsp + 0x450 ], dl; spilling byte x456 to mem
movzx rdx, byte [ rsp + 0x370 ]; load byte memx497 to register64
mov byte [ rsp + 0x458 ], r10b; spilling byte x356 to mem
mov r10, -0x1 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r10, -0x1 ; moving imm to reg
adox rdx, r10; loading flag
adox rbx, r12
mov rdx, [ rsi + 0x30 ]; load m64 x6 to register64
mulx r12, r10, [ rax + 0x0 ]; x526, x525<- x6 * arg2[0]
mov [ rsp + 0x460 ], r12; spilling x526 to mem
setc r12b; spill CF x414 to reg (r12)
clc;
adcx r10, rbx
mov rbx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbx; 0xffffffffffffffff, swapping with x6, which is currently in rdx
mov byte [ rsp + 0x468 ], r13b; spilling byte x484 to mem
mov byte [ rsp + 0x470 ], r12b; spilling byte x414 to mem
mulx r13, r12, r10; x569, x568<- x540 * 0xffffffffffffffff
setc dl; spill CF x541 to reg (rdx)
clc;
adcx r12, r10
movzx r12, byte [ rsp + 0x390 ]; x34, copying x33 here, cause x33 is needed in a reg for other than x34, namely all: , x34, size: 1
mov byte [ rsp + 0x478 ], dl; spilling byte x541 to mem
mov rdx, [ rsp + 0x358 ]; load m64 x9 to register64
lea r12, [ r12 + rdx ]; r8/64 + m8
movzx rdx, byte [ rsp + 0x398 ]; x61, copying x60 here, cause x60 is needed in a reg for other than x61, namely all: , x61, size: 1
mov [ rsp + 0x480 ], r13; spilling x569 to mem
mov r13, [ rsp + 0x380 ]; load m64 x36 to register64
lea rdx, [ rdx + r13 ]; r8/64 + m8
seto r13b; spill OF x499 to reg (r13)
mov [ rsp + 0x488 ], r10; spilling x540 to mem
movzx r10, byte [ rsp + 0x410 ]; load byte memx75 to register64
mov [ rsp + 0x490 ], rbx; spilling x6 to mem
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r10, rbx; loading flag
adox r12, rdx
mov rdx, rcx; x1 to rdx
mulx rdx, rcx, [ rax + 0x30 ]; x79, x78<- x1 * arg2[6]
setc r10b; spill CF x584 to reg (r10)
movzx rbx, byte [ rsp + 0x3b8 ]; load byte memx101 to register64
clc;
mov [ rsp + 0x498 ], rdx; spilling x79 to mem
mov rdx, -0x1 ; moving imm to reg
adcx rbx, rdx; loading flag
adcx rcx, [ rsp + 0x378 ]
setc bl; spill CF x103 to reg (rbx)
movzx rdx, byte [ rsp + 0x3a8 ]; load byte memx116 to register64
clc;
mov byte [ rsp + 0x4a0 ], r10b; spilling byte x584 to mem
mov r10, -0x1 ; moving imm to reg
adcx rdx, r10; loading flag
adcx r12, rcx
mov rdx, 0x2341f27177344 ; moving imm to reg
mulx r8, rcx, r8; x122, x121<- x105 * 0x2341f27177344
setc r10b; spill CF x118 to reg (r10)
movzx rdx, byte [ rsp + 0x3c0 ]; load byte memx144 to register64
clc;
mov [ rsp + 0x4a8 ], r8; spilling x122 to mem
mov r8, -0x1 ; moving imm to reg
adcx rdx, r8; loading flag
adcx rcx, [ rsp + 0x3a0 ]
setc dl; spill CF x146 to reg (rdx)
movzx r8, byte [ rsp + 0x3d0 ]; load byte memx159 to register64
clc;
mov byte [ rsp + 0x4b0 ], r10b; spilling byte x118 to mem
mov r10, -0x1 ; moving imm to reg
adcx r8, r10; loading flag
adcx r12, rcx
xchg rdx, r14; x2, swapping with x146, which is currently in rdx
mulx r8, rcx, [ rax + 0x28 ]; x168, x167<- x2 * arg2[5]
setc r10b; spill CF x161 to reg (r10)
mov [ rsp + 0x4b8 ], r8; spilling x168 to mem
movzx r8, byte [ rsp + 0x3f0 ]; load byte memx186 to register64
clc;
mov byte [ rsp + 0x4c0 ], r14b; spilling byte x146 to mem
mov r14, -0x1 ; moving imm to reg
adcx r8, r14; loading flag
adcx rcx, [ rsp + 0x3b0 ]
setc r8b; spill CF x188 to reg (r8)
movzx r14, byte [ rsp + 0x3d8 ]; load byte memx201 to register64
clc;
mov byte [ rsp + 0x4c8 ], r10b; spilling byte x161 to mem
mov r10, -0x1 ; moving imm to reg
adcx r14, r10; loading flag
adcx r12, rcx
mov r14, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, r14; 0x6cfc5fd681c52056, swapping with x2, which is currently in rdx
mulx rcx, r10, r9; x211, x210<- x192 * 0x6cfc5fd681c52056
setc dl; spill CF x203 to reg (rdx)
mov [ rsp + 0x4d0 ], rcx; spilling x211 to mem
movzx rcx, byte [ rsp + 0x3e8 ]; load byte memx229 to register64
clc;
mov byte [ rsp + 0x4d8 ], r8b; spilling byte x188 to mem
mov r8, -0x1 ; moving imm to reg
adcx rcx, r8; loading flag
adcx r10, [ rsp + 0x3c8 ]
mov cl, dl; preserving value of x203 into a new reg
mov rdx, [ rax + 0x20 ]; saving arg2[4] in rdx.
mov byte [ rsp + 0x4e0 ], bl; spilling byte x103 to mem
mulx r8, rbx, rbp; x257, x256<- x3 * arg2[4]
mov [ rsp + 0x4e8 ], r8; spilling x257 to mem
seto r8b; spill OF x77 to reg (r8)
mov byte [ rsp + 0x4f0 ], cl; spilling byte x203 to mem
movzx rcx, byte [ rsp + 0x418 ]; load byte memx271 to register64
mov byte [ rsp + 0x4f8 ], r13b; spilling byte x499 to mem
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rcx, r13; loading flag
adox rbx, [ rsp + 0x3e0 ]
seto cl; spill OF x273 to reg (rcx)
movzx r13, byte [ rsp + 0x408 ]; load byte memx244 to register64
mov byte [ rsp + 0x500 ], r8b; spilling byte x77 to mem
mov r8, 0x0 ; moving imm to reg
dec r8; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r13, r8; loading flag
adox r12, r10
setc r13b; spill CF x231 to reg (r13)
movzx r10, byte [ rsp + 0x3f8 ]; load byte memx286 to register64
clc;
adcx r10, r8; loading flag
adcx r12, rbx
setc r10b; spill CF x288 to reg (r10)
movzx rbx, byte [ rsp + 0x430 ]; load byte memx329 to register64
clc;
adcx rbx, r8; loading flag
adcx r12, [ rsp + 0x170 ]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mulx rbx, r8, r15; x346, x345<- x4 * arg2[3]
mov [ rsp + 0x508 ], rbx; spilling x346 to mem
seto bl; spill OF x246 to reg (rbx)
mov byte [ rsp + 0x510 ], r10b; spilling byte x288 to mem
movzx r10, byte [ rsp + 0x458 ]; load byte memx356 to register64
mov byte [ rsp + 0x518 ], cl; spilling byte x273 to mem
mov rcx, -0x1 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rcx, -0x1 ; moving imm to reg
adox r10, rcx; loading flag
adox r8, [ rsp + 0x400 ]
setc r10b; spill CF x331 to reg (r10)
movzx rcx, byte [ rsp + 0x438 ]; load byte memx371 to register64
clc;
mov byte [ rsp + 0x520 ], bl; spilling byte x246 to mem
mov rbx, -0x1 ; moving imm to reg
adcx rcx, rbx; loading flag
adcx r12, r8
mov rcx, 0xfdc1767ae2ffffff ; moving imm to reg
mov rdx, rcx; 0xfdc1767ae2ffffff to rdx
mulx rcx, r8, rdi; x389, x388<- x366 * 0xfdc1767ae2ffffff
setc bl; spill CF x373 to reg (rbx)
movzx rdx, byte [ rsp + 0x440 ]; load byte memx399 to register64
clc;
mov [ rsp + 0x528 ], rcx; spilling x389 to mem
mov rcx, -0x1 ; moving imm to reg
adcx rdx, rcx; loading flag
adcx r8, [ rsp + 0x428 ]
seto dl; spill OF x358 to reg (rdx)
movzx rcx, byte [ rsp + 0x470 ]; load byte memx414 to register64
mov byte [ rsp + 0x530 ], bl; spilling byte x373 to mem
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rcx, rbx; loading flag
adox r12, r8
setc cl; spill CF x401 to reg (rcx)
movzx r8, byte [ rsp + 0x450 ]; load byte memx456 to register64
clc;
adcx r8, rbx; loading flag
adcx r12, [ rsp + 0x30 ]
mov r8, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r11; x453, swapping with x358, which is currently in rdx
mov byte [ rsp + 0x538 ], cl; spilling byte x401 to mem
mulx rbx, rcx, r8; x478, x477<- x453 * 0xffffffffffffffff
setc r8b; spill CF x458 to reg (r8)
mov [ rsp + 0x540 ], rbx; spilling x478 to mem
movzx rbx, byte [ rsp + 0x468 ]; load byte memx484 to register64
clc;
mov byte [ rsp + 0x548 ], r10b; spilling byte x331 to mem
mov r10, -0x1 ; moving imm to reg
adcx rbx, r10; loading flag
adcx rcx, [ rsp + 0x448 ]
setc bl; spill CF x486 to reg (rbx)
movzx r10, byte [ rsp + 0x4f8 ]; load byte memx499 to register64
clc;
mov byte [ rsp + 0x550 ], r8b; spilling byte x458 to mem
mov r8, -0x1 ; moving imm to reg
adcx r10, r8; loading flag
adcx r12, rcx
mov r10, rdx; preserving value of x453 into a new reg
mov rdx, [ rsp + 0x490 ]; saving x6 in rdx.
mulx rcx, r8, [ rax + 0x8 ]; x524, x523<- x6 * arg2[1]
mov [ rsp + 0x558 ], rcx; spilling x524 to mem
setc cl; spill CF x501 to reg (rcx)
clc;
adcx r8, [ rsp + 0x460 ]
mov byte [ rsp + 0x560 ], cl; spilling byte x501 to mem
mov rcx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rcx; 0xffffffffffffffff, swapping with x6, which is currently in rdx
mov byte [ rsp + 0x568 ], bl; spilling byte x486 to mem
mov byte [ rsp + 0x570 ], r11b; spilling byte x358 to mem
mulx rbx, r11, [ rsp + 0x488 ]; x567, x566<- x540 * 0xffffffffffffffff
setc dl; spill CF x528 to reg (rdx)
clc;
adcx r11, [ rsp + 0x480 ]
mov [ rsp + 0x578 ], rbx; spilling x567 to mem
setc bl; spill CF x571 to reg (rbx)
mov byte [ rsp + 0x580 ], dl; spilling byte x528 to mem
movzx rdx, byte [ rsp + 0x478 ]; load byte memx541 to register64
clc;
mov byte [ rsp + 0x588 ], r13b; spilling byte x231 to mem
mov r13, -0x1 ; moving imm to reg
adcx rdx, r13; loading flag
adcx r12, r8
setc dl; spill CF x543 to reg (rdx)
movzx r8, byte [ rsp + 0x4a0 ]; load byte memx584 to register64
clc;
adcx r8, r13; loading flag
adcx r12, r11
setc r8b; spill CF x586 to reg (r8)
seto r11b; spill OF x416 to reg (r11)
mov r13, r12; x600, copying x585 here, cause x585 is needed in a reg for other than x600, namely all: , x616, x600--x601, size: 2
mov byte [ rsp + 0x590 ], bl; spilling byte x571 to mem
mov rbx, 0xffffffffffffffff ; moving imm to reg
sub r13, rbx
movzx rbx, byte [ rsp + 0x4e0 ]; x104, copying x103 here, cause x103 is needed in a reg for other than x104, namely all: , x104, size: 1
mov [ rsp + 0x598 ], r13; spilling x600 to mem
mov r13, [ rsp + 0x498 ]; load m64 x79 to register64
lea rbx, [ rbx + r13 ]; r8/64 + m8
movzx r13, byte [ rsp + 0x4b0 ]; load byte memx118 to register64
mov byte [ rsp + 0x5a0 ], r8b; spilling byte x586 to mem
mov r8, 0x0 ; moving imm to reg
dec r8; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
mov byte [ rsp + 0x5a8 ], dl; spilling byte x543 to mem
movzx rdx, byte [ rsp + 0x500 ]; load byte memx77 to register64
adox r13, r8; loading flag
adox rbx, rdx
movzx rdx, byte [ rsp + 0x4c0 ]; x147, copying x146 here, cause x146 is needed in a reg for other than x147, namely all: , x147, size: 1
mov r13, [ rsp + 0x4a8 ]; load m64 x122 to register64
lea rdx, [ rdx + r13 ]; r8/64 + m8
seto r13b; spill OF x120 to reg (r13)
movzx r8, byte [ rsp + 0x4c8 ]; load byte memx161 to register64
mov byte [ rsp + 0x5b0 ], r11b; spilling byte x416 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
adox r8, r11; loading flag
adox rbx, rdx
mov rdx, r14; x2 to rdx
mulx rdx, r14, [ rax + 0x30 ]; x166, x165<- x2 * arg2[6]
seto r8b; spill OF x163 to reg (r8)
movzx r11, byte [ rsp + 0x4d8 ]; load byte memx188 to register64
mov [ rsp + 0x5b8 ], rdx; spilling x166 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r11, rdx; loading flag
adox r14, [ rsp + 0x4b8 ]
setc r11b; spill CF x601 to reg (r11)
movzx rdx, byte [ rsp + 0x4f0 ]; load byte memx203 to register64
clc;
mov byte [ rsp + 0x5c0 ], r13b; spilling byte x120 to mem
mov r13, -0x1 ; moving imm to reg
adcx rdx, r13; loading flag
adcx rbx, r14
mov rdx, 0x2341f27177344 ; moving imm to reg
mulx r9, r14, r9; x209, x208<- x192 * 0x2341f27177344
setc r13b; spill CF x205 to reg (r13)
movzx rdx, byte [ rsp + 0x588 ]; load byte memx231 to register64
clc;
mov [ rsp + 0x5c8 ], r9; spilling x209 to mem
mov r9, -0x1 ; moving imm to reg
adcx rdx, r9; loading flag
adcx r14, [ rsp + 0x4d0 ]
setc dl; spill CF x233 to reg (rdx)
movzx r9, byte [ rsp + 0x520 ]; load byte memx246 to register64
clc;
mov byte [ rsp + 0x5d0 ], r13b; spilling byte x205 to mem
mov r13, -0x1 ; moving imm to reg
adcx r9, r13; loading flag
adcx rbx, r14
mov r9b, dl; preserving value of x233 into a new reg
mov rdx, [ rax + 0x28 ]; saving arg2[5] in rdx.
mulx r14, r13, rbp; x255, x254<- x3 * arg2[5]
mov [ rsp + 0x5d8 ], r14; spilling x255 to mem
setc r14b; spill CF x248 to reg (r14)
mov byte [ rsp + 0x5e0 ], r9b; spilling byte x233 to mem
movzx r9, byte [ rsp + 0x518 ]; load byte memx273 to register64
clc;
mov byte [ rsp + 0x5e8 ], r8b; spilling byte x163 to mem
mov r8, -0x1 ; moving imm to reg
adcx r9, r8; loading flag
adcx r13, [ rsp + 0x4e8 ]
mov rdx, r15; x4 to rdx
mulx r15, r9, [ rax + 0x20 ]; x344, x343<- x4 * arg2[4]
seto r8b; spill OF x190 to reg (r8)
mov [ rsp + 0x5f0 ], r15; spilling x344 to mem
movzx r15, byte [ rsp + 0x510 ]; load byte memx288 to register64
mov byte [ rsp + 0x5f8 ], r14b; spilling byte x248 to mem
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, r14; loading flag
adox rbx, r13
setc r15b; spill CF x275 to reg (r15)
movzx r13, byte [ rsp + 0x570 ]; load byte memx358 to register64
clc;
adcx r13, r14; loading flag
adcx r9, [ rsp + 0x508 ]
seto r13b; spill OF x290 to reg (r13)
movzx r14, byte [ rsp + 0x548 ]; load byte memx331 to register64
mov byte [ rsp + 0x600 ], r15b; spilling byte x275 to mem
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r14, r15; loading flag
adox rbx, [ rsp + 0x168 ]
mov r14, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, r14; 0x7bc65c783158aea3, swapping with x4, which is currently in rdx
mov byte [ rsp + 0x608 ], r13b; spilling byte x290 to mem
mulx r15, r13, rdi; x387, x386<- x366 * 0x7bc65c783158aea3
seto dl; spill OF x333 to reg (rdx)
mov [ rsp + 0x610 ], r15; spilling x387 to mem
movzx r15, byte [ rsp + 0x530 ]; load byte memx373 to register64
mov byte [ rsp + 0x618 ], r8b; spilling byte x190 to mem
mov r8, 0x0 ; moving imm to reg
dec r8; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, r8; loading flag
adox rbx, r9
seto r15b; spill OF x375 to reg (r15)
movzx r9, byte [ rsp + 0x538 ]; load byte memx401 to register64
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
adox r9, r8; loading flag
adox r13, [ rsp + 0x528 ]
setc r9b; spill CF x360 to reg (r9)
movzx r8, byte [ rsp + 0x5b0 ]; load byte memx416 to register64
clc;
mov byte [ rsp + 0x620 ], r15b; spilling byte x375 to mem
mov r15, -0x1 ; moving imm to reg
adcx r8, r15; loading flag
adcx rbx, r13
setc r8b; spill CF x418 to reg (r8)
movzx r13, byte [ rsp + 0x550 ]; load byte memx458 to register64
clc;
adcx r13, r15; loading flag
adcx rbx, [ rsp + 0x28 ]
mov r13, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, r10; x453, swapping with x333, which is currently in rdx
mov byte [ rsp + 0x628 ], r8b; spilling byte x418 to mem
mulx r15, r8, r13; x476, x475<- x453 * 0xfdc1767ae2ffffff
seto r13b; spill OF x403 to reg (r13)
mov [ rsp + 0x630 ], r15; spilling x476 to mem
movzx r15, byte [ rsp + 0x568 ]; load byte memx486 to register64
mov byte [ rsp + 0x638 ], r9b; spilling byte x360 to mem
mov r9, -0x1 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r9, -0x1 ; moving imm to reg
adox r15, r9; loading flag
adox r8, [ rsp + 0x540 ]
mov r15, rdx; preserving value of x453 into a new reg
mov rdx, [ rax + 0x10 ]; saving arg2[2] in rdx.
mov byte [ rsp + 0x640 ], r13b; spilling byte x403 to mem
mulx r9, r13, rcx; x522, x521<- x6 * arg2[2]
mov [ rsp + 0x648 ], r9; spilling x522 to mem
seto r9b; spill OF x488 to reg (r9)
mov byte [ rsp + 0x650 ], r10b; spilling byte x333 to mem
movzx r10, byte [ rsp + 0x560 ]; load byte memx501 to register64
mov byte [ rsp + 0x658 ], r11b; spilling byte x601 to mem
mov r11, 0x0 ; moving imm to reg
dec r11; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r10, r11; loading flag
adox rbx, r8
setc r10b; spill CF x460 to reg (r10)
movzx r8, byte [ rsp + 0x580 ]; load byte memx528 to register64
clc;
adcx r8, r11; loading flag
adcx r13, [ rsp + 0x558 ]
mov r8, 0xffffffffffffffff ; moving imm to reg
mov rdx, [ rsp + 0x488 ]; x540 to rdx
mov byte [ rsp + 0x660 ], r10b; spilling byte x460 to mem
mulx r11, r10, r8; x565, x564<- x540 * 0xffffffffffffffff
setc r8b; spill CF x530 to reg (r8)
mov [ rsp + 0x668 ], r11; spilling x565 to mem
movzx r11, byte [ rsp + 0x5a8 ]; load byte memx543 to register64
clc;
mov byte [ rsp + 0x670 ], r9b; spilling byte x488 to mem
mov r9, -0x1 ; moving imm to reg
adcx r11, r9; loading flag
adcx rbx, r13
setc r11b; spill CF x545 to reg (r11)
movzx r13, byte [ rsp + 0x590 ]; load byte memx571 to register64
clc;
adcx r13, r9; loading flag
adcx r10, [ rsp + 0x578 ]
setc r13b; spill CF x573 to reg (r13)
movzx r9, byte [ rsp + 0x5a0 ]; load byte memx586 to register64
clc;
mov byte [ rsp + 0x678 ], r11b; spilling byte x545 to mem
mov r11, -0x1 ; moving imm to reg
adcx r9, r11; loading flag
adcx rbx, r10
setc r9b; spill CF x588 to reg (r9)
seto r10b; spill OF x503 to reg (r10)
movzx r11, byte [ rsp + 0x658 ]; x601, copying x601 here, cause x601 is needed in a reg for other than x601, namely all: , x602--x603, size: 1
add r11, -0x1
mov r11, rbx; x602, copying x587 here, cause x587 is needed in a reg for other than x602, namely all: , x617, x602--x603, size: 2
mov byte [ rsp + 0x680 ], r13b; spilling byte x573 to mem
mov r13, 0xffffffffffffffff ; moving imm to reg
sbb r11, r13
movzx r13, byte [ rsp + 0x5e8 ]; x164, copying x163 here, cause x163 is needed in a reg for other than x164, namely all: , x164, size: 1
mov [ rsp + 0x688 ], r11; spilling x602 to mem
movzx r11, byte [ rsp + 0x5c0 ]; load byte memx120 to register64
lea r13, [ r13 + r11 ]; r64+m8
movzx r11, byte [ rsp + 0x618 ]; x191, copying x190 here, cause x190 is needed in a reg for other than x191, namely all: , x191, size: 1
mov byte [ rsp + 0x690 ], r9b; spilling byte x588 to mem
mov r9, [ rsp + 0x5b8 ]; load m64 x166 to register64
lea r11, [ r11 + r9 ]; r8/64 + m8
movzx r9, byte [ rsp + 0x5d0 ]; load byte memx205 to register64
mov byte [ rsp + 0x698 ], r8b; spilling byte x530 to mem
mov r8, -0x1 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r8, -0x1 ; moving imm to reg
adox r9, r8; loading flag
adox r13, r11
movzx r9, byte [ rsp + 0x5e0 ]; x234, copying x233 here, cause x233 is needed in a reg for other than x234, namely all: , x234, size: 1
mov r11, [ rsp + 0x5c8 ]; load m64 x209 to register64
lea r9, [ r9 + r11 ]; r8/64 + m8
seto r11b; spill OF x207 to reg (r11)
movzx r8, byte [ rsp + 0x5f8 ]; load byte memx248 to register64
mov byte [ rsp + 0x6a0 ], r10b; spilling byte x503 to mem
mov r10, -0x1 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r10, -0x1 ; moving imm to reg
adox r8, r10; loading flag
adox r13, r9
mov r8, rdx; preserving value of x540 into a new reg
mov rdx, [ rax + 0x30 ]; saving arg2[6] in rdx.
mulx rbp, r9, rbp; x253, x252<- x3 * arg2[6]
seto r10b; spill OF x250 to reg (r10)
mov [ rsp + 0x6a8 ], rbp; spilling x253 to mem
movzx rbp, byte [ rsp + 0x600 ]; load byte memx275 to register64
mov byte [ rsp + 0x6b0 ], r11b; spilling byte x207 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
adox rbp, r11; loading flag
adox r9, [ rsp + 0x5d8 ]
seto bpl; spill OF x277 to reg (rbp)
movzx r11, byte [ rsp + 0x608 ]; load byte memx290 to register64
mov byte [ rsp + 0x6b8 ], r10b; spilling byte x250 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r11, r10; loading flag
adox r13, r9
mov rdx, r14; x4 to rdx
mulx r14, r11, [ rax + 0x28 ]; x342, x341<- x4 * arg2[5]
seto r9b; spill OF x292 to reg (r9)
movzx r10, byte [ rsp + 0x650 ]; load byte memx333 to register64
mov [ rsp + 0x6c0 ], r14; spilling x342 to mem
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r10, r14; loading flag
adox r13, [ rsp + 0x178 ]
seto r10b; spill OF x335 to reg (r10)
movzx r14, byte [ rsp + 0x638 ]; load byte memx360 to register64
mov byte [ rsp + 0x6c8 ], r9b; spilling byte x292 to mem
mov r9, -0x1 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r9, -0x1 ; moving imm to reg
adox r14, r9; loading flag
adox r11, [ rsp + 0x5f0 ]
seto r14b; spill OF x362 to reg (r14)
movzx r9, byte [ rsp + 0x620 ]; load byte memx375 to register64
mov byte [ rsp + 0x6d0 ], r10b; spilling byte x335 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r9, r10; loading flag
adox r13, r11
mov r9, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, rdi; x366, swapping with x4, which is currently in rdx
mulx r11, r10, r9; x385, x384<- x366 * 0x6cfc5fd681c52056
seto r9b; spill OF x377 to reg (r9)
mov [ rsp + 0x6d8 ], r11; spilling x385 to mem
movzx r11, byte [ rsp + 0x640 ]; load byte memx403 to register64
mov byte [ rsp + 0x6e0 ], r14b; spilling byte x362 to mem
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r11, r14; loading flag
adox r10, [ rsp + 0x610 ]
setc r11b; spill CF x603 to reg (r11)
movzx r14, byte [ rsp + 0x628 ]; load byte memx418 to register64
clc;
mov byte [ rsp + 0x6e8 ], r9b; spilling byte x377 to mem
mov r9, -0x1 ; moving imm to reg
adcx r14, r9; loading flag
adcx r13, r10
mov r14, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, r14; 0x7bc65c783158aea3, swapping with x366, which is currently in rdx
mulx r10, r9, r15; x474, x473<- x453 * 0x7bc65c783158aea3
seto dl; spill OF x405 to reg (rdx)
mov [ rsp + 0x6f0 ], r10; spilling x474 to mem
movzx r10, byte [ rsp + 0x670 ]; load byte memx488 to register64
mov byte [ rsp + 0x6f8 ], bpl; spilling byte x277 to mem
mov rbp, -0x1 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
adox r10, rbp; loading flag
adox r9, [ rsp + 0x630 ]
seto r10b; spill OF x490 to reg (r10)
movzx rbp, byte [ rsp + 0x660 ]; load byte memx460 to register64
mov byte [ rsp + 0x700 ], dl; spilling byte x405 to mem
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
adox rbp, rdx; loading flag
adox r13, [ rsp + 0x20 ]
seto bpl; spill OF x462 to reg (rbp)
movzx rdx, byte [ rsp + 0x6a0 ]; load byte memx503 to register64
mov byte [ rsp + 0x708 ], r10b; spilling byte x490 to mem
mov r10, -0x1 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r10, -0x1 ; moving imm to reg
adox rdx, r10; loading flag
adox r13, r9
mov rdx, rcx; x6 to rdx
mulx rcx, r9, [ rax + 0x18 ]; x520, x519<- x6 * arg2[3]
setc r10b; spill CF x420 to reg (r10)
mov [ rsp + 0x710 ], rcx; spilling x520 to mem
movzx rcx, byte [ rsp + 0x698 ]; load byte memx530 to register64
clc;
mov byte [ rsp + 0x718 ], bpl; spilling byte x462 to mem
mov rbp, -0x1 ; moving imm to reg
adcx rcx, rbp; loading flag
adcx r9, [ rsp + 0x648 ]
seto cl; spill OF x505 to reg (rcx)
movzx rbp, byte [ rsp + 0x678 ]; load byte memx545 to register64
mov byte [ rsp + 0x720 ], r10b; spilling byte x420 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbp, r10; loading flag
adox r13, r9
mov rbp, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, rbp; 0xfdc1767ae2ffffff, swapping with x6, which is currently in rdx
mulx r9, r10, r8; x563, x562<- x540 * 0xfdc1767ae2ffffff
seto dl; spill OF x547 to reg (rdx)
mov [ rsp + 0x728 ], r9; spilling x563 to mem
movzx r9, byte [ rsp + 0x680 ]; load byte memx573 to register64
mov byte [ rsp + 0x730 ], cl; spilling byte x505 to mem
mov rcx, -0x1 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rcx, -0x1 ; moving imm to reg
adox r9, rcx; loading flag
adox r10, [ rsp + 0x668 ]
setc r9b; spill CF x532 to reg (r9)
movzx rcx, byte [ rsp + 0x690 ]; load byte memx588 to register64
clc;
mov byte [ rsp + 0x738 ], dl; spilling byte x547 to mem
mov rdx, -0x1 ; moving imm to reg
adcx rcx, rdx; loading flag
adcx r13, r10
setc cl; spill CF x590 to reg (rcx)
seto r10b; spill OF x575 to reg (r10)
movzx rdx, r11b; x603, copying x603 here, cause x603 is needed in a reg for other than x603, namely all: , x604--x605, size: 1
add rdx, -0x1
mov r11, r13; x604, copying x589 here, cause x589 is needed in a reg for other than x604, namely all: , x618, x604--x605, size: 2
mov byte [ rsp + 0x740 ], r9b; spilling byte x532 to mem
mov r9, 0xffffffffffffffff ; moving imm to reg
sbb r11, r9
movzx r9, byte [ rsp + 0x6b8 ]; x251, copying x250 here, cause x250 is needed in a reg for other than x251, namely all: , x251, size: 1
mov [ rsp + 0x748 ], r11; spilling x604 to mem
movzx r11, byte [ rsp + 0x6b0 ]; load byte memx207 to register64
lea r9, [ r9 + r11 ]; r64+m8
movzx r11, byte [ rsp + 0x6f8 ]; x278, copying x277 here, cause x277 is needed in a reg for other than x278, namely all: , x278, size: 1
mov byte [ rsp + 0x750 ], cl; spilling byte x590 to mem
mov rcx, [ rsp + 0x6a8 ]; load m64 x253 to register64
lea r11, [ r11 + rcx ]; r8/64 + m8
movzx rcx, byte [ rsp + 0x6c8 ]; load byte memx292 to register64
mov byte [ rsp + 0x758 ], r10b; spilling byte x575 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rcx, r10; loading flag
adox r9, r11
setc cl; spill CF x605 to reg (rcx)
movzx r11, byte [ rsp + 0x6d0 ]; load byte memx335 to register64
clc;
adcx r11, r10; loading flag
adcx r9, [ rsp + 0x180 ]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mulx rdi, r11, rdi; x340, x339<- x4 * arg2[6]
mov r10, 0x2341f27177344 ; moving imm to reg
mov rdx, r10; 0x2341f27177344 to rdx
mulx r14, r10, r14; x383, x382<- x366 * 0x2341f27177344
seto dl; spill OF x294 to reg (rdx)
mov [ rsp + 0x760 ], r14; spilling x383 to mem
movzx r14, byte [ rsp + 0x6e0 ]; load byte memx362 to register64
mov [ rsp + 0x768 ], rdi; spilling x340 to mem
mov rdi, -0x1 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdi, -0x1 ; moving imm to reg
adox r14, rdi; loading flag
adox r11, [ rsp + 0x6c0 ]
setc r14b; spill CF x337 to reg (r14)
movzx rdi, byte [ rsp + 0x6e8 ]; load byte memx377 to register64
clc;
mov byte [ rsp + 0x770 ], dl; spilling byte x294 to mem
mov rdx, -0x1 ; moving imm to reg
adcx rdi, rdx; loading flag
adcx r9, r11
seto dil; spill OF x364 to reg (rdi)
movzx r11, byte [ rsp + 0x700 ]; load byte memx405 to register64
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
adox r11, rdx; loading flag
adox r10, [ rsp + 0x6d8 ]
setc r11b; spill CF x379 to reg (r11)
movzx rdx, byte [ rsp + 0x720 ]; load byte memx420 to register64
clc;
mov byte [ rsp + 0x778 ], dil; spilling byte x364 to mem
mov rdi, -0x1 ; moving imm to reg
adcx rdx, rdi; loading flag
adcx r9, r10
mov rdx, 0x6cfc5fd681c52056 ; moving imm to reg
mulx r10, rdi, r15; x472, x471<- x453 * 0x6cfc5fd681c52056
seto dl; spill OF x407 to reg (rdx)
mov [ rsp + 0x780 ], r10; spilling x472 to mem
movzx r10, byte [ rsp + 0x718 ]; load byte memx462 to register64
mov byte [ rsp + 0x788 ], r11b; spilling byte x379 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
adox r10, r11; loading flag
adox r9, [ rsp + 0x18 ]
seto r10b; spill OF x464 to reg (r10)
movzx r11, byte [ rsp + 0x708 ]; load byte memx490 to register64
mov byte [ rsp + 0x790 ], dl; spilling byte x407 to mem
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
adox r11, rdx; loading flag
adox rdi, [ rsp + 0x6f0 ]
seto r11b; spill OF x492 to reg (r11)
movzx rdx, byte [ rsp + 0x730 ]; load byte memx505 to register64
mov byte [ rsp + 0x798 ], r10b; spilling byte x464 to mem
mov r10, -0x1 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r10, -0x1 ; moving imm to reg
adox rdx, r10; loading flag
adox r9, rdi
mov rdx, rbp; x6 to rdx
mulx rbp, rdi, [ rax + 0x20 ]; x518, x517<- x6 * arg2[4]
seto r10b; spill OF x507 to reg (r10)
mov [ rsp + 0x7a0 ], rbp; spilling x518 to mem
movzx rbp, byte [ rsp + 0x740 ]; load byte memx532 to register64
mov byte [ rsp + 0x7a8 ], r11b; spilling byte x492 to mem
mov r11, 0x0 ; moving imm to reg
dec r11; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbp, r11; loading flag
adox rdi, [ rsp + 0x710 ]
seto bpl; spill OF x534 to reg (rbp)
movzx r11, byte [ rsp + 0x738 ]; load byte memx547 to register64
mov byte [ rsp + 0x7b0 ], r10b; spilling byte x507 to mem
mov r10, -0x1 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r10, -0x1 ; moving imm to reg
adox r11, r10; loading flag
adox r9, rdi
mov r11, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, r11; 0x7bc65c783158aea3, swapping with x6, which is currently in rdx
mulx rdi, r10, r8; x561, x560<- x540 * 0x7bc65c783158aea3
seto dl; spill OF x549 to reg (rdx)
mov [ rsp + 0x7b8 ], rdi; spilling x561 to mem
movzx rdi, byte [ rsp + 0x758 ]; load byte memx575 to register64
mov byte [ rsp + 0x7c0 ], bpl; spilling byte x534 to mem
mov rbp, 0x0 ; moving imm to reg
dec rbp; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rdi, rbp; loading flag
adox r10, [ rsp + 0x728 ]
setc dil; spill CF x422 to reg (rdi)
movzx rbp, byte [ rsp + 0x750 ]; load byte memx590 to register64
clc;
mov byte [ rsp + 0x7c8 ], dl; spilling byte x549 to mem
mov rdx, -0x1 ; moving imm to reg
adcx rbp, rdx; loading flag
adcx r9, r10
setc bpl; spill CF x592 to reg (rbp)
seto r10b; spill OF x577 to reg (r10)
movzx rdx, cl; x605, copying x605 here, cause x605 is needed in a reg for other than x605, namely all: , x606--x607, size: 1
add rdx, -0x1
mov rcx, r9; x606, copying x591 here, cause x591 is needed in a reg for other than x606, namely all: , x606--x607, x619, size: 2
mov byte [ rsp + 0x7d0 ], dil; spilling byte x422 to mem
mov rdi, 0xfdc1767ae2ffffff ; moving imm to reg
sbb rcx, rdi
movzx rdi, r14b; x338, copying x337 here, cause x337 is needed in a reg for other than x338, namely all: , x338, size: 1
mov [ rsp + 0x7d8 ], rcx; spilling x606 to mem
movzx rcx, byte [ rsp + 0x770 ]; load byte memx294 to register64
lea rdi, [ rdi + rcx ]; r64+m8
movzx rcx, byte [ rsp + 0x778 ]; x365, copying x364 here, cause x364 is needed in a reg for other than x365, namely all: , x365, size: 1
mov r14, [ rsp + 0x768 ]; load m64 x340 to register64
lea rcx, [ rcx + r14 ]; r8/64 + m8
movzx r14, byte [ rsp + 0x788 ]; load byte memx379 to register64
mov byte [ rsp + 0x7e0 ], bpl; spilling byte x592 to mem
mov rbp, -0x1 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
adox r14, rbp; loading flag
adox rdi, rcx
movzx r14, byte [ rsp + 0x790 ]; x408, copying x407 here, cause x407 is needed in a reg for other than x408, namely all: , x408, size: 1
mov rcx, [ rsp + 0x760 ]; load m64 x383 to register64
lea r14, [ r14 + rcx ]; r8/64 + m8
seto cl; spill OF x381 to reg (rcx)
movzx rbp, byte [ rsp + 0x7d0 ]; load byte memx422 to register64
mov byte [ rsp + 0x7e8 ], r10b; spilling byte x577 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbp, r10; loading flag
adox rdi, r14
mov rbp, 0x2341f27177344 ; moving imm to reg
mov rdx, rbp; 0x2341f27177344 to rdx
mulx r15, rbp, r15; x470, x469<- x453 * 0x2341f27177344
setc r14b; spill CF x607 to reg (r14)
movzx r10, byte [ rsp + 0x798 ]; load byte memx464 to register64
clc;
mov rdx, -0x1 ; moving imm to reg
adcx r10, rdx; loading flag
adcx rdi, [ rsp + 0x10 ]
setc r10b; spill CF x466 to reg (r10)
movzx rdx, byte [ rsp + 0x7a8 ]; load byte memx492 to register64
clc;
mov byte [ rsp + 0x7f0 ], r14b; spilling byte x607 to mem
mov r14, -0x1 ; moving imm to reg
adcx rdx, r14; loading flag
adcx rbp, [ rsp + 0x780 ]
setc dl; spill CF x494 to reg (rdx)
movzx r14, byte [ rsp + 0x7b0 ]; load byte memx507 to register64
clc;
mov [ rsp + 0x7f8 ], r15; spilling x470 to mem
mov r15, -0x1 ; moving imm to reg
adcx r14, r15; loading flag
adcx rdi, rbp
mov r14b, dl; preserving value of x494 into a new reg
mov rdx, [ rax + 0x28 ]; saving arg2[5] in rdx.
mulx rbp, r15, r11; x516, x515<- x6 * arg2[5]
mov [ rsp + 0x800 ], rbp; spilling x516 to mem
setc bpl; spill CF x509 to reg (rbp)
mov byte [ rsp + 0x808 ], r14b; spilling byte x494 to mem
movzx r14, byte [ rsp + 0x7c0 ]; load byte memx534 to register64
clc;
mov byte [ rsp + 0x810 ], r10b; spilling byte x466 to mem
mov r10, -0x1 ; moving imm to reg
adcx r14, r10; loading flag
adcx r15, [ rsp + 0x7a0 ]
setc r14b; spill CF x536 to reg (r14)
movzx r10, byte [ rsp + 0x7c8 ]; load byte memx549 to register64
clc;
mov byte [ rsp + 0x818 ], bpl; spilling byte x509 to mem
mov rbp, -0x1 ; moving imm to reg
adcx r10, rbp; loading flag
adcx rdi, r15
movzx r10, cl; x425, copying x381 here, cause x381 is needed in a reg for other than x425, namely all: , x425, size: 1
mov r15, 0x0 ; moving imm to reg
adox r10, r15
mov rcx, 0x6cfc5fd681c52056 ; moving imm to reg
mov rdx, r8; x540 to rdx
mulx r8, r15, rcx; x559, x558<- x540 * 0x6cfc5fd681c52056
movzx rbp, byte [ rsp + 0x7e8 ]; load byte memx577 to register64
mov rcx, -0x1 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rcx, -0x1 ; moving imm to reg
adox rbp, rcx; loading flag
adox r15, [ rsp + 0x7b8 ]
seto bpl; spill OF x579 to reg (rbp)
movzx rcx, byte [ rsp + 0x7e0 ]; load byte memx592 to register64
mov [ rsp + 0x820 ], r8; spilling x559 to mem
mov r8, -0x1 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r8, -0x1 ; moving imm to reg
adox rcx, r8; loading flag
adox rdi, r15
seto cl; spill OF x594 to reg (rcx)
movzx r15, byte [ rsp + 0x810 ]; load byte memx466 to register64
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
adox r15, r8; loading flag
adox r10, [ rsp + 0x8 ]
movzx r15, byte [ rsp + 0x808 ]; x495, copying x494 here, cause x494 is needed in a reg for other than x495, namely all: , x495, size: 1
mov r8, [ rsp + 0x7f8 ]; load m64 x470 to register64
lea r15, [ r15 + r8 ]; r8/64 + m8
setc r8b; spill CF x551 to reg (r8)
mov byte [ rsp + 0x828 ], cl; spilling byte x594 to mem
seto cl; spill OF x468 to reg (rcx)
mov byte [ rsp + 0x830 ], bpl; spilling byte x579 to mem
movzx rbp, byte [ rsp + 0x7f0 ]; x607, copying x607 here, cause x607 is needed in a reg for other than x607, namely all: , x608--x609, size: 1
add rbp, -0x1
mov rbp, rdi; x608, copying x593 here, cause x593 is needed in a reg for other than x608, namely all: , x608--x609, x620, size: 2
mov byte [ rsp + 0x838 ], r14b; spilling byte x536 to mem
mov r14, 0x7bc65c783158aea3 ; moving imm to reg
sbb rbp, r14
movzx r14, byte [ rsp + 0x818 ]; load byte memx509 to register64
mov [ rsp + 0x840 ], rbp; spilling x608 to mem
mov rbp, -0x1 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
adox r14, rbp; loading flag
adox r10, r15
xchg rdx, r11; x6, swapping with x540, which is currently in rdx
mulx rdx, r14, [ rax + 0x30 ]; x514, x513<- x6 * arg2[6]
seto r15b; spill OF x511 to reg (r15)
movzx rbp, byte [ rsp + 0x838 ]; load byte memx536 to register64
mov [ rsp + 0x848 ], rdx; spilling x514 to mem
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
adox rbp, rdx; loading flag
adox r14, [ rsp + 0x800 ]
seto bpl; spill OF x538 to reg (rbp)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, rdx; loading flag
adox r10, r14
mov r8, 0x2341f27177344 ; moving imm to reg
mov rdx, r11; x540 to rdx
mulx rdx, r11, r8; x557, x556<- x540 * 0x2341f27177344
setc r14b; spill CF x609 to reg (r14)
movzx r8, byte [ rsp + 0x830 ]; load byte memx579 to register64
clc;
mov [ rsp + 0x850 ], rdx; spilling x557 to mem
mov rdx, -0x1 ; moving imm to reg
adcx r8, rdx; loading flag
adcx r11, [ rsp + 0x820 ]
seto r8b; spill OF x553 to reg (r8)
movzx rdx, byte [ rsp + 0x828 ]; load byte memx594 to register64
mov byte [ rsp + 0x858 ], bpl; spilling byte x538 to mem
mov rbp, 0x0 ; moving imm to reg
dec rbp; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rdx, rbp; loading flag
adox r10, r11
setc dl; spill CF x581 to reg (rdx)
seto r11b; spill OF x596 to reg (r11)
movzx rbp, r14b; x609, copying x609 here, cause x609 is needed in a reg for other than x609, namely all: , x610--x611, size: 1
add rbp, -0x1
mov rbp, r10; x610, copying x595 here, cause x595 is needed in a reg for other than x610, namely all: , x621, x610--x611, size: 2
mov r14, 0x6cfc5fd681c52056 ; moving imm to reg
sbb rbp, r14
movzx r14, r15b; x512, copying x511 here, cause x511 is needed in a reg for other than x512, namely all: , x512, size: 1
movzx rcx, cl
lea r14, [ r14 + rcx ]
movzx rcx, byte [ rsp + 0x858 ]; x539, copying x538 here, cause x538 is needed in a reg for other than x539, namely all: , x539, size: 1
mov r15, [ rsp + 0x848 ]; load m64 x514 to register64
lea rcx, [ rcx + r15 ]; r8/64 + m8
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r8, r8b
adox r8, r15; loading flag
adox r14, rcx
movzx r8, dl; x582, copying x581 here, cause x581 is needed in a reg for other than x582, namely all: , x582, size: 1
mov rcx, [ rsp + 0x850 ]; load m64 x557 to register64
lea r8, [ r8 + rcx ]; r8/64 + m8
setc cl; spill CF x611 to reg (rcx)
clc;
movzx r11, r11b
adcx r11, r15; loading flag
adcx r14, r8
seto dl; spill OF x599 to reg (rdx)
adc dl, 0x0
movzx rdx, dl
movzx r11, cl; x611, copying x611 here, cause x611 is needed in a reg for other than x611, namely all: , x612--x613, size: 1
add r11, -0x1
mov r11, r14; x612, copying x597 here, cause x597 is needed in a reg for other than x612, namely all: , x612--x613, x622, size: 2
mov rcx, 0x2341f27177344 ; moving imm to reg
sbb r11, rcx
movzx r8, dl; _, copying x599 here, cause x599 is needed in a reg for other than _, namely all: , _--x615, size: 1
sbb r8, 0x00000000
mov r8, [ rsp + 0x748 ]; x618, copying x604 here, cause x604 is needed in a reg for other than x618, namely all: , x618, size: 1
cmovc r8, r13; if CF, x618<- x589 (nzVar)
mov r13, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r13 + 0x10 ], r8; out1[2] = x618
cmovc r11, r14; if CF, x622<- x597 (nzVar)
mov r14, [ rsp + 0x688 ]; x617, copying x602 here, cause x602 is needed in a reg for other than x617, namely all: , x617, size: 1
cmovc r14, rbx; if CF, x617<- x587 (nzVar)
mov [ r13 + 0x30 ], r11; out1[6] = x622
cmovc rbp, r10; if CF, x621<- x595 (nzVar)
mov rbx, [ rsp + 0x7d8 ]; x619, copying x606 here, cause x606 is needed in a reg for other than x619, namely all: , x619, size: 1
cmovc rbx, r9; if CF, x619<- x591 (nzVar)
mov r9, [ rsp + 0x598 ]; x616, copying x600 here, cause x600 is needed in a reg for other than x616, namely all: , x616, size: 1
cmovc r9, r12; if CF, x616<- x585 (nzVar)
mov [ r13 + 0x0 ], r9; out1[0] = x616
mov [ r13 + 0x18 ], rbx; out1[3] = x619
mov r12, [ rsp + 0x840 ]; x620, copying x608 here, cause x608 is needed in a reg for other than x620, namely all: , x620, size: 1
cmovc r12, rdi; if CF, x620<- x593 (nzVar)
mov [ r13 + 0x8 ], r14; out1[1] = x617
mov [ r13 + 0x28 ], rbp; out1[5] = x621
mov [ r13 + 0x20 ], r12; out1[4] = x620
mov rbx, [ rsp + 0x860 ]; restoring from stack
mov rbp, [ rsp + 0x868 ]; restoring from stack
mov r12, [ rsp + 0x870 ]; restoring from stack
mov r13, [ rsp + 0x878 ]; restoring from stack
mov r14, [ rsp + 0x880 ]; restoring from stack
mov r15, [ rsp + 0x888 ]; restoring from stack
add rsp, 0x890 
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; clocked at 2200 MHz
; first cyclecount 396.015, best 394.91, lastGood 414
; seed 4297472400993309 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 74876 ms / 500 runs=> 149.752ms/run
; Time spent for assembling and measureing (initial batch_size=17, initial num_batches=101): 1304 ms
; Ratio (time for assembling + measure)/(total runtime for 500runs): 0.01741546022757626
; number reverted permutation/ tried permutation: 150 / 250 =60.000%
; number reverted decision/ tried decision: 137 / 251 =54.582%