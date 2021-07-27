SECTION .text
	GLOBAL mul_p434
mul_p434:
sub rsp, 0x4b0 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x480 ], rbx; saving to stack
mov [ rsp + 0x488 ], rbp; saving to stack
mov [ rsp + 0x490 ], r12; saving to stack
mov [ rsp + 0x498 ], r13; saving to stack
mov [ rsp + 0x4a0 ], r14; saving to stack
mov [ rsp + 0x4a8 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x7 to register64
xchg rdx, rax; x7, swapping with arg2, which is currently in rdx
mulx r10, r11, [ rax + 0x0 ]; x21, x20<- x7 * arg2[0]
mov rbx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbx; 0xffffffffffffffff, swapping with x7, which is currently in rdx
mulx rbp, r12, r11; x48, x47<- x20 * 0xffffffffffffffff
xor r13, r13
adox r12, r11
mov r12, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ rax + 0x8 ]; saving arg2[1] in rdx.
mulx r14, r15, rbx; x19, x18<- x7 * arg2[1]
adcx r15, r10
mov rdx, r12; 0xffffffffffffffff to rdx
mulx r12, rcx, r11; x46, x45<- x20 * 0xffffffffffffffff
setc r8b; spill CF x23 to reg (r8)
clc;
adcx rcx, rbp
adox rcx, r15
mov r9, [ rsi + 0x8 ]; load m64 x1 to register64
mov r10, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ rax + 0x0 ]; saving arg2[0] in rdx.
mulx rbp, r15, r9; x91, x90<- x1 * arg2[0]
seto r10b; spill OF x65 to reg (r10)
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov rdi, -0x3 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r15, rcx
mov rcx, 0xffffffffffffffff ; moving imm to reg
mov rdx, r15; x105 to rdx
mulx r15, r13, rcx; x134, x133<- x105 * 0xffffffffffffffff
mov [ rsp + 0x8 ], rbp; spilling x91 to mem
mulx rdi, rbp, rcx; x132, x131<- x105 * 0xffffffffffffffff
seto cl; spill OF x106 to reg (rcx)
mov byte [ rsp + 0x10 ], r10b; spilling byte x65 to mem
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, r15
mov r15, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x18 ], rbp; spilling x135 to mem
mulx r10, rbp, r15; x130, x129<- x105 * 0xffffffffffffffff
adox rbp, rdi
mov rdi, 0xfdc1767ae2ffffff ; moving imm to reg
mov [ rsp + 0x20 ], rbp; spilling x137 to mem
mulx r15, rbp, rdi; x128, x127<- x105 * 0xfdc1767ae2ffffff
adox rbp, r10
mov r10, 0x7bc65c783158aea3 ; moving imm to reg
mov [ rsp + 0x28 ], rbp; spilling x139 to mem
mulx rdi, rbp, r10; x126, x125<- x105 * 0x7bc65c783158aea3
adox rbp, r15
mov r15, 0x6cfc5fd681c52056 ; moving imm to reg
mov [ rsp + 0x30 ], rbp; spilling x141 to mem
mulx r10, rbp, r15; x124, x123<- x105 * 0x6cfc5fd681c52056
adox rbp, rdi
mov rdi, 0x2341f27177344 ; moving imm to reg
mov [ rsp + 0x38 ], rbp; spilling x143 to mem
mulx r15, rbp, rdi; x122, x121<- x105 * 0x2341f27177344
adox rbp, r10
mov r10, [ rsi + 0x10 ]; load m64 x2 to register64
mov rdi, 0x0 ; moving imm to reg
adox r15, rdi
xchg rdx, r10; x2, swapping with x105, which is currently in rdx
mov [ rsp + 0x40 ], r15; spilling x147 to mem
mulx rdi, r15, [ rax + 0x0 ]; x178, x177<- x2 * arg2[0]
mov [ rsp + 0x48 ], rbp; spilling x145 to mem
mov [ rsp + 0x50 ], r15; spilling x177 to mem
mulx rbp, r15, [ rax + 0x8 ]; x176, x175<- x2 * arg2[1]
mov byte [ rsp + 0x58 ], cl; spilling byte x106 to mem
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, rdi
mulx rdi, rcx, [ rax + 0x10 ]; x174, x173<- x2 * arg2[2]
mov [ rsp + 0x60 ], r15; spilling x179 to mem
mov [ rsp + 0x68 ], r9; spilling x1 to mem
mulx r15, r9, [ rax + 0x18 ]; x172, x171<- x2 * arg2[3]
adox rcx, rbp
mov [ rsp + 0x70 ], rcx; spilling x181 to mem
mulx rbp, rcx, [ rax + 0x20 ]; x170, x169<- x2 * arg2[4]
adox r9, rdi
mov [ rsp + 0x78 ], r9; spilling x183 to mem
mulx rdi, r9, [ rax + 0x28 ]; x168, x167<- x2 * arg2[5]
adox rcx, r15
adox r9, rbp
mulx rdx, r15, [ rax + 0x30 ]; x166, x165<- x2 * arg2[6]
adox r15, rdi
seto bpl; spill OF x190 to reg (rbp)
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, r10
movzx r13, bpl; x191, copying x190 here, cause x190 is needed in a reg for other than x191, namely all: , x191, size: 1
lea r13, [ r13 + rdx ]
mov rdx, rbx; x7 to rdx
mulx rbx, r10, [ rax + 0x10 ]; x17, x16<- x7 * arg2[2]
mov rbp, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r11; x20, swapping with x7, which is currently in rdx
mov [ rsp + 0x80 ], r13; spilling x191 to mem
mulx rdi, r13, rbp; x44, x43<- x20 * 0xffffffffffffffff
setc bpl; spill CF x50 to reg (rbp)
clc;
mov [ rsp + 0x88 ], r15; spilling x189 to mem
mov r15, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, r15; loading flag
adcx r14, r10
setc r8b; spill CF x25 to reg (r8)
clc;
movzx rbp, bpl
adcx rbp, r15; loading flag
adcx r12, r13
mov rbp, rdx; preserving value of x20 into a new reg
mov rdx, [ rax + 0x8 ]; saving arg2[1] in rdx.
mulx r10, r13, [ rsp + 0x68 ]; x89, x88<- x1 * arg2[1]
seto r15b; spill OF x149 to reg (r15)
mov [ rsp + 0x90 ], r9; spilling x187 to mem
movzx r9, byte [ rsp + 0x10 ]; load byte memx65 to register64
mov [ rsp + 0x98 ], rcx; spilling x185 to mem
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r9, rcx; loading flag
adox r14, r12
setc r9b; spill CF x52 to reg (r9)
clc;
adcx r13, [ rsp + 0x8 ]
seto r12b; spill OF x67 to reg (r12)
movzx rcx, byte [ rsp + 0x58 ]; load byte memx106 to register64
mov [ rsp + 0xa0 ], r10; spilling x89 to mem
mov r10, -0x1 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r10, -0x1 ; moving imm to reg
adox rcx, r10; loading flag
adox r14, r13
setc cl; spill CF x93 to reg (rcx)
clc;
movzx r15, r15b
adcx r15, r10; loading flag
adcx r14, [ rsp + 0x18 ]
seto r15b; spill OF x108 to reg (r15)
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r14, [ rsp + 0x50 ]
mov r13, 0xffffffffffffffff ; moving imm to reg
mov rdx, r14; x192 to rdx
mulx r14, r10, r13; x221, x220<- x192 * 0xffffffffffffffff
seto r13b; spill OF x193 to reg (r13)
mov [ rsp + 0xa8 ], r14; spilling x221 to mem
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r10, rdx
mov r10, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, r10; 0xfdc1767ae2ffffff, swapping with x192, which is currently in rdx
mov byte [ rsp + 0xb0 ], r13b; spilling byte x193 to mem
mulx r14, r13, rbp; x42, x41<- x20 * 0xfdc1767ae2ffffff
mov [ rsp + 0xb8 ], r14; spilling x42 to mem
mov r14, rdx; preserving value of 0xfdc1767ae2ffffff into a new reg
mov rdx, [ rax + 0x18 ]; saving arg2[3] in rdx.
mov byte [ rsp + 0xc0 ], r15b; spilling byte x108 to mem
mov byte [ rsp + 0xc8 ], cl; spilling byte x93 to mem
mulx r15, rcx, r11; x15, x14<- x7 * arg2[3]
setc r14b; spill CF x151 to reg (r14)
clc;
mov [ rsp + 0xd0 ], r15; spilling x15 to mem
mov r15, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, r15; loading flag
adcx rdi, r13
setc r9b; spill CF x54 to reg (r9)
clc;
movzx r8, r8b
adcx r8, r15; loading flag
adcx rbx, rcx
setc r8b; spill CF x27 to reg (r8)
clc;
movzx r12, r12b
adcx r12, r15; loading flag
adcx rbx, rdi
mov rdx, [ rsp + 0x68 ]; x1 to rdx
mulx r12, r13, [ rax + 0x10 ]; x87, x86<- x1 * arg2[2]
setc cl; spill CF x69 to reg (rcx)
movzx rdi, byte [ rsp + 0xc8 ]; load byte memx93 to register64
clc;
adcx rdi, r15; loading flag
adcx r13, [ rsp + 0xa0 ]
seto dil; spill OF x236 to reg (rdi)
movzx r15, byte [ rsp + 0xc0 ]; load byte memx108 to register64
mov [ rsp + 0xd8 ], r12; spilling x87 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, r12; loading flag
adox rbx, r13
setc r15b; spill CF x95 to reg (r15)
clc;
movzx r14, r14b
adcx r14, r12; loading flag
adcx rbx, [ rsp + 0x20 ]
seto r14b; spill OF x110 to reg (r14)
movzx r13, byte [ rsp + 0xb0 ]; load byte memx193 to register64
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
adox r13, r12; loading flag
adox rbx, [ rsp + 0x60 ]
mov r13, [ rsi + 0x18 ]; load m64 x3 to register64
mov r12, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r10; x192, swapping with x1, which is currently in rdx
mov byte [ rsp + 0xe0 ], r14b; spilling byte x110 to mem
mov byte [ rsp + 0xe8 ], r15b; spilling byte x95 to mem
mulx r14, r15, r12; x219, x218<- x192 * 0xffffffffffffffff
seto r12b; spill OF x195 to reg (r12)
mov [ rsp + 0xf0 ], r14; spilling x219 to mem
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, [ rsp + 0xa8 ]
setc r14b; spill CF x153 to reg (r14)
clc;
mov byte [ rsp + 0xf8 ], r12b; spilling byte x195 to mem
mov r12, -0x1 ; moving imm to reg
movzx rdi, dil
adcx rdi, r12; loading flag
adcx rbx, r15
xchg rdx, r13; x3, swapping with x192, which is currently in rdx
mulx rdi, r15, [ rax + 0x0 ]; x265, x264<- x3 * arg2[0]
seto r12b; spill OF x223 to reg (r12)
mov [ rsp + 0x100 ], rdi; spilling x265 to mem
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, rbx
mov rbx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbx; 0xffffffffffffffff, swapping with x3, which is currently in rdx
mov byte [ rsp + 0x108 ], r12b; spilling byte x223 to mem
mulx rdi, r12, r15; x308, x307<- x279 * 0xffffffffffffffff
seto dl; spill OF x280 to reg (rdx)
mov [ rsp + 0x110 ], rdi; spilling x308 to mem
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, r15
xchg rdx, r11; x7, swapping with x280, which is currently in rdx
mulx r12, rdi, [ rax + 0x20 ]; x13, x12<- x7 * arg2[4]
mov [ rsp + 0x118 ], r12; spilling x13 to mem
mov r12, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, rbp; x20, swapping with x7, which is currently in rdx
mov byte [ rsp + 0x120 ], r11b; spilling byte x280 to mem
mov byte [ rsp + 0x128 ], r14b; spilling byte x153 to mem
mulx r11, r14, r12; x40, x39<- x20 * 0x7bc65c783158aea3
seto r12b; spill OF x323 to reg (r12)
mov [ rsp + 0x130 ], r11; spilling x40 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, r11; loading flag
adox r14, [ rsp + 0xb8 ]
setc r9b; spill CF x238 to reg (r9)
clc;
movzx r8, r8b
adcx r8, r11; loading flag
adcx rdi, [ rsp + 0xd0 ]
seto r8b; spill OF x56 to reg (r8)
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r11, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r11; loading flag
adox rdi, r14
xchg rdx, r10; x1, swapping with x20, which is currently in rdx
mulx rcx, r14, [ rax + 0x18 ]; x85, x84<- x1 * arg2[3]
setc r11b; spill CF x29 to reg (r11)
mov [ rsp + 0x138 ], rcx; spilling x85 to mem
movzx rcx, byte [ rsp + 0xe8 ]; load byte memx95 to register64
clc;
mov byte [ rsp + 0x140 ], r8b; spilling byte x56 to mem
mov r8, -0x1 ; moving imm to reg
adcx rcx, r8; loading flag
adcx r14, [ rsp + 0xd8 ]
seto cl; spill OF x71 to reg (rcx)
movzx r8, byte [ rsp + 0xe0 ]; load byte memx110 to register64
mov byte [ rsp + 0x148 ], r11b; spilling byte x29 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
adox r8, r11; loading flag
adox rdi, r14
setc r8b; spill CF x97 to reg (r8)
movzx r14, byte [ rsp + 0x128 ]; load byte memx153 to register64
clc;
adcx r14, r11; loading flag
adcx rdi, [ rsp + 0x28 ]
mov r14, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r14; 0xffffffffffffffff, swapping with x1, which is currently in rdx
mov byte [ rsp + 0x150 ], r8b; spilling byte x97 to mem
mulx r11, r8, r13; x217, x216<- x192 * 0xffffffffffffffff
setc dl; spill CF x155 to reg (rdx)
mov [ rsp + 0x158 ], r11; spilling x217 to mem
movzx r11, byte [ rsp + 0xf8 ]; load byte memx195 to register64
clc;
mov byte [ rsp + 0x160 ], cl; spilling byte x71 to mem
mov rcx, -0x1 ; moving imm to reg
adcx r11, rcx; loading flag
adcx rdi, [ rsp + 0x70 ]
seto r11b; spill OF x112 to reg (r11)
movzx rcx, byte [ rsp + 0x108 ]; load byte memx223 to register64
mov byte [ rsp + 0x168 ], dl; spilling byte x155 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rcx, rdx; loading flag
adox r8, [ rsp + 0xf0 ]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov byte [ rsp + 0x170 ], r11b; spilling byte x112 to mem
mulx rcx, r11, rbx; x263, x262<- x3 * arg2[1]
mov [ rsp + 0x178 ], rcx; spilling x263 to mem
setc cl; spill CF x197 to reg (rcx)
clc;
mov byte [ rsp + 0x180 ], r12b; spilling byte x323 to mem
mov r12, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, r12; loading flag
adcx rdi, r8
setc r9b; spill CF x240 to reg (r9)
clc;
adcx r11, [ rsp + 0x100 ]
setc r8b; spill CF x267 to reg (r8)
movzx r12, byte [ rsp + 0x120 ]; load byte memx280 to register64
clc;
mov byte [ rsp + 0x188 ], r9b; spilling byte x240 to mem
mov r9, -0x1 ; moving imm to reg
adcx r12, r9; loading flag
adcx rdi, r11
mov r12, 0xffffffffffffffff ; moving imm to reg
mov rdx, r12; 0xffffffffffffffff to rdx
mulx r12, r11, r15; x306, x305<- x279 * 0xffffffffffffffff
setc r9b; spill CF x282 to reg (r9)
clc;
adcx r11, [ rsp + 0x110 ]
setc dl; spill CF x310 to reg (rdx)
mov [ rsp + 0x190 ], r12; spilling x306 to mem
movzx r12, byte [ rsp + 0x180 ]; load byte memx323 to register64
clc;
mov byte [ rsp + 0x198 ], r9b; spilling byte x282 to mem
mov r9, -0x1 ; moving imm to reg
adcx r12, r9; loading flag
adcx rdi, r11
mov r12b, dl; preserving value of x310 into a new reg
mov rdx, [ rax + 0x28 ]; saving arg2[5] in rdx.
mulx r11, r9, rbp; x11, x10<- x7 * arg2[5]
mov [ rsp + 0x1a0 ], rdi; spilling x324 to mem
mov rdi, 0x6cfc5fd681c52056 ; moving imm to reg
mov rdx, rdi; 0x6cfc5fd681c52056 to rdx
mov [ rsp + 0x1a8 ], r11; spilling x11 to mem
mov byte [ rsp + 0x1b0 ], r12b; spilling byte x310 to mem
mulx r11, r12, r10; x38, x37<- x20 * 0x6cfc5fd681c52056
setc dl; spill CF x325 to reg (rdx)
mov [ rsp + 0x1b8 ], r11; spilling x38 to mem
movzx r11, byte [ rsp + 0x148 ]; load byte memx29 to register64
clc;
mov byte [ rsp + 0x1c0 ], r8b; spilling byte x267 to mem
mov r8, -0x1 ; moving imm to reg
adcx r11, r8; loading flag
adcx r9, [ rsp + 0x118 ]
seto r11b; spill OF x225 to reg (r11)
movzx r8, byte [ rsp + 0x140 ]; load byte memx56 to register64
mov byte [ rsp + 0x1c8 ], dl; spilling byte x325 to mem
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
adox r8, rdx; loading flag
adox r12, [ rsp + 0x130 ]
seto r8b; spill OF x58 to reg (r8)
movzx rdx, byte [ rsp + 0x160 ]; load byte memx71 to register64
mov byte [ rsp + 0x1d0 ], r11b; spilling byte x225 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
adox rdx, r11; loading flag
adox r9, r12
mov rdx, r14; x1 to rdx
mulx r14, r12, [ rax + 0x20 ]; x83, x82<- x1 * arg2[4]
seto r11b; spill OF x73 to reg (r11)
mov [ rsp + 0x1d8 ], r14; spilling x83 to mem
movzx r14, byte [ rsp + 0x150 ]; load byte memx97 to register64
mov byte [ rsp + 0x1e0 ], r8b; spilling byte x58 to mem
mov r8, -0x1 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r8, -0x1 ; moving imm to reg
adox r14, r8; loading flag
adox r12, [ rsp + 0x138 ]
setc r14b; spill CF x31 to reg (r14)
movzx r8, byte [ rsp + 0x170 ]; load byte memx112 to register64
clc;
mov byte [ rsp + 0x1e8 ], r11b; spilling byte x73 to mem
mov r11, -0x1 ; moving imm to reg
adcx r8, r11; loading flag
adcx r9, r12
setc r8b; spill CF x114 to reg (r8)
movzx r12, byte [ rsp + 0x168 ]; load byte memx155 to register64
clc;
adcx r12, r11; loading flag
adcx r9, [ rsp + 0x30 ]
seto r12b; spill OF x99 to reg (r12)
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r11, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r11; loading flag
adox r9, [ rsp + 0x78 ]
mov rcx, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, rcx; 0xfdc1767ae2ffffff, swapping with x1, which is currently in rdx
mov byte [ rsp + 0x1f0 ], r8b; spilling byte x114 to mem
mulx r11, r8, r13; x215, x214<- x192 * 0xfdc1767ae2ffffff
seto dl; spill OF x199 to reg (rdx)
mov [ rsp + 0x1f8 ], r11; spilling x215 to mem
movzx r11, byte [ rsp + 0x1d0 ]; load byte memx225 to register64
mov byte [ rsp + 0x200 ], r12b; spilling byte x99 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r11, r12; loading flag
adox r8, [ rsp + 0x158 ]
xchg rdx, rbx; x3, swapping with x199, which is currently in rdx
mulx r11, r12, [ rax + 0x10 ]; x261, x260<- x3 * arg2[2]
mov [ rsp + 0x208 ], r11; spilling x261 to mem
seto r11b; spill OF x227 to reg (r11)
mov byte [ rsp + 0x210 ], bl; spilling byte x199 to mem
movzx rbx, byte [ rsp + 0x188 ]; load byte memx240 to register64
mov byte [ rsp + 0x218 ], r14b; spilling byte x31 to mem
mov r14, -0x1 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r14, -0x1 ; moving imm to reg
adox rbx, r14; loading flag
adox r9, r8
setc bl; spill CF x157 to reg (rbx)
movzx r8, byte [ rsp + 0x1c0 ]; load byte memx267 to register64
clc;
adcx r8, r14; loading flag
adcx r12, [ rsp + 0x178 ]
mov r8, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r15; x279, swapping with x3, which is currently in rdx
mov byte [ rsp + 0x220 ], r11b; spilling byte x227 to mem
mulx r14, r11, r8; x304, x303<- x279 * 0xffffffffffffffff
setc r8b; spill CF x269 to reg (r8)
mov [ rsp + 0x228 ], r14; spilling x304 to mem
movzx r14, byte [ rsp + 0x198 ]; load byte memx282 to register64
clc;
mov byte [ rsp + 0x230 ], bl; spilling byte x157 to mem
mov rbx, -0x1 ; moving imm to reg
adcx r14, rbx; loading flag
adcx r9, r12
seto r14b; spill OF x242 to reg (r14)
movzx r12, byte [ rsp + 0x1b0 ]; load byte memx310 to register64
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
adox r12, rbx; loading flag
adox r11, [ rsp + 0x190 ]
setc r12b; spill CF x284 to reg (r12)
movzx rbx, byte [ rsp + 0x1c8 ]; load byte memx325 to register64
clc;
mov byte [ rsp + 0x238 ], r8b; spilling byte x269 to mem
mov r8, -0x1 ; moving imm to reg
adcx rbx, r8; loading flag
adcx r9, r11
xchg rdx, rbp; x7, swapping with x279, which is currently in rdx
mulx rdx, rbx, [ rax + 0x30 ]; x9, x8<- x7 * arg2[6]
seto r11b; spill OF x312 to reg (r11)
movzx r8, byte [ rsp + 0x218 ]; load byte memx31 to register64
mov [ rsp + 0x240 ], r9; spilling x326 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r8, r9; loading flag
adox rbx, [ rsp + 0x1a8 ]
mov r8, 0x2341f27177344 ; moving imm to reg
xchg rdx, r8; 0x2341f27177344, swapping with x9, which is currently in rdx
mulx r10, r9, r10; x36, x35<- x20 * 0x2341f27177344
seto dl; spill OF x33 to reg (rdx)
mov [ rsp + 0x248 ], r10; spilling x36 to mem
movzx r10, byte [ rsp + 0x1e0 ]; load byte memx58 to register64
mov [ rsp + 0x250 ], r8; spilling x9 to mem
mov r8, -0x1 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r8, -0x1 ; moving imm to reg
adox r10, r8; loading flag
adox r9, [ rsp + 0x1b8 ]
mov r10b, dl; preserving value of x33 into a new reg
mov rdx, [ rax + 0x28 ]; saving arg2[5] in rdx.
mov byte [ rsp + 0x258 ], r11b; spilling byte x312 to mem
mulx r8, r11, rcx; x81, x80<- x1 * arg2[5]
mov [ rsp + 0x260 ], r8; spilling x81 to mem
seto r8b; spill OF x60 to reg (r8)
mov byte [ rsp + 0x268 ], r10b; spilling byte x33 to mem
movzx r10, byte [ rsp + 0x1e8 ]; load byte memx73 to register64
mov byte [ rsp + 0x270 ], r12b; spilling byte x284 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
adox r10, r12; loading flag
adox rbx, r9
setc r10b; spill CF x327 to reg (r10)
movzx r9, byte [ rsp + 0x200 ]; load byte memx99 to register64
clc;
adcx r9, r12; loading flag
adcx r11, [ rsp + 0x1d8 ]
setc r9b; spill CF x101 to reg (r9)
movzx r12, byte [ rsp + 0x1f0 ]; load byte memx114 to register64
clc;
mov byte [ rsp + 0x278 ], r8b; spilling byte x60 to mem
mov r8, -0x1 ; moving imm to reg
adcx r12, r8; loading flag
adcx rbx, r11
mov r12, 0x7bc65c783158aea3 ; moving imm to reg
mov rdx, r12; 0x7bc65c783158aea3 to rdx
mulx r12, r11, r13; x213, x212<- x192 * 0x7bc65c783158aea3
seto r8b; spill OF x75 to reg (r8)
movzx rdx, byte [ rsp + 0x230 ]; load byte memx157 to register64
mov [ rsp + 0x280 ], r12; spilling x213 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rdx, r12; loading flag
adox rbx, [ rsp + 0x38 ]
setc dl; spill CF x116 to reg (rdx)
movzx r12, byte [ rsp + 0x210 ]; load byte memx199 to register64
clc;
mov byte [ rsp + 0x288 ], r8b; spilling byte x75 to mem
mov r8, -0x1 ; moving imm to reg
adcx r12, r8; loading flag
adcx rbx, [ rsp + 0x98 ]
seto r12b; spill OF x159 to reg (r12)
movzx r8, byte [ rsp + 0x220 ]; load byte memx227 to register64
mov byte [ rsp + 0x290 ], dl; spilling byte x116 to mem
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
adox r8, rdx; loading flag
adox r11, [ rsp + 0x1f8 ]
seto r8b; spill OF x229 to reg (r8)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, rdx; loading flag
adox rbx, r11
mov rdx, r15; x3 to rdx
mulx r15, r14, [ rax + 0x18 ]; x259, x258<- x3 * arg2[3]
seto r11b; spill OF x244 to reg (r11)
mov [ rsp + 0x298 ], r15; spilling x259 to mem
movzx r15, byte [ rsp + 0x238 ]; load byte memx269 to register64
mov byte [ rsp + 0x2a0 ], r8b; spilling byte x229 to mem
mov r8, 0x0 ; moving imm to reg
dec r8; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, r8; loading flag
adox r14, [ rsp + 0x208 ]
setc r15b; spill CF x201 to reg (r15)
movzx r8, byte [ rsp + 0x270 ]; load byte memx284 to register64
clc;
mov byte [ rsp + 0x2a8 ], r11b; spilling byte x244 to mem
mov r11, -0x1 ; moving imm to reg
adcx r8, r11; loading flag
adcx rbx, r14
mov r8, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, r8; 0xfdc1767ae2ffffff, swapping with x3, which is currently in rdx
mulx r14, r11, rbp; x302, x301<- x279 * 0xfdc1767ae2ffffff
setc dl; spill CF x286 to reg (rdx)
mov [ rsp + 0x2b0 ], r14; spilling x302 to mem
movzx r14, byte [ rsp + 0x258 ]; load byte memx312 to register64
clc;
mov byte [ rsp + 0x2b8 ], r15b; spilling byte x201 to mem
mov r15, -0x1 ; moving imm to reg
adcx r14, r15; loading flag
adcx r11, [ rsp + 0x228 ]
movzx r14, byte [ rsp + 0x268 ]; x34, copying x33 here, cause x33 is needed in a reg for other than x34, namely all: , x34, size: 1
mov r15, [ rsp + 0x250 ]; load m64 x9 to register64
lea r14, [ r14 + r15 ]; r8/64 + m8
seto r15b; spill OF x271 to reg (r15)
mov byte [ rsp + 0x2c0 ], dl; spilling byte x286 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r10, r10b
adox r10, rdx; loading flag
adox rbx, r11
movzx r10, byte [ rsp + 0x278 ]; x61, copying x60 here, cause x60 is needed in a reg for other than x61, namely all: , x61, size: 1
mov r11, [ rsp + 0x248 ]; load m64 x36 to register64
lea r10, [ r10 + r11 ]; r8/64 + m8
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mulx rcx, r11, rcx; x79, x78<- x1 * arg2[6]
mov [ rsp + 0x2c8 ], rbx; spilling x328 to mem
seto bl; spill OF x329 to reg (rbx)
mov [ rsp + 0x2d0 ], rcx; spilling x79 to mem
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r9, r9b
adox r9, rcx; loading flag
adox r11, [ rsp + 0x260 ]
seto r9b; spill OF x103 to reg (r9)
movzx rcx, byte [ rsp + 0x288 ]; load byte memx75 to register64
mov byte [ rsp + 0x2d8 ], bl; spilling byte x329 to mem
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rcx, rbx; loading flag
adox r14, r10
seto cl; spill OF x77 to reg (rcx)
movzx r10, byte [ rsp + 0x290 ]; load byte memx116 to register64
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
adox r10, rbx; loading flag
adox r14, r11
setc r10b; spill CF x314 to reg (r10)
clc;
movzx r12, r12b
adcx r12, rbx; loading flag
adcx r14, [ rsp + 0x48 ]
mov r12, 0x6cfc5fd681c52056 ; moving imm to reg
mov rdx, r12; 0x6cfc5fd681c52056 to rdx
mulx r12, r11, r13; x211, x210<- x192 * 0x6cfc5fd681c52056
setc bl; spill CF x161 to reg (rbx)
movzx rdx, byte [ rsp + 0x2b8 ]; load byte memx201 to register64
clc;
mov [ rsp + 0x2e0 ], r12; spilling x211 to mem
mov r12, -0x1 ; moving imm to reg
adcx rdx, r12; loading flag
adcx r14, [ rsp + 0x90 ]
setc dl; spill CF x203 to reg (rdx)
movzx r12, byte [ rsp + 0x2a0 ]; load byte memx229 to register64
clc;
mov byte [ rsp + 0x2e8 ], bl; spilling byte x161 to mem
mov rbx, -0x1 ; moving imm to reg
adcx r12, rbx; loading flag
adcx r11, [ rsp + 0x280 ]
setc r12b; spill CF x231 to reg (r12)
movzx rbx, byte [ rsp + 0x2a8 ]; load byte memx244 to register64
clc;
mov byte [ rsp + 0x2f0 ], dl; spilling byte x203 to mem
mov rdx, -0x1 ; moving imm to reg
adcx rbx, rdx; loading flag
adcx r14, r11
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx rbx, r11, r8; x257, x256<- x3 * arg2[4]
mov [ rsp + 0x2f8 ], rbx; spilling x257 to mem
mov rbx, 0x7bc65c783158aea3 ; moving imm to reg
mov rdx, rbp; x279 to rdx
mov byte [ rsp + 0x300 ], r12b; spilling byte x231 to mem
mulx rbp, r12, rbx; x300, x299<- x279 * 0x7bc65c783158aea3
seto bl; spill OF x118 to reg (rbx)
mov [ rsp + 0x308 ], rbp; spilling x300 to mem
mov rbp, 0x0 ; moving imm to reg
dec rbp; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r15, r15b
adox r15, rbp; loading flag
adox r11, [ rsp + 0x298 ]
setc r15b; spill CF x246 to reg (r15)
clc;
movzx r10, r10b
adcx r10, rbp; loading flag
adcx r12, [ rsp + 0x2b0 ]
setc r10b; spill CF x316 to reg (r10)
movzx rbp, byte [ rsp + 0x2c0 ]; load byte memx286 to register64
clc;
mov byte [ rsp + 0x310 ], r15b; spilling byte x246 to mem
mov r15, -0x1 ; moving imm to reg
adcx rbp, r15; loading flag
adcx r14, r11
movzx rbp, r9b; x104, copying x103 here, cause x103 is needed in a reg for other than x104, namely all: , x104, size: 1
mov r11, [ rsp + 0x2d0 ]; load m64 x79 to register64
lea rbp, [ rbp + r11 ]; r8/64 + m8
seto r11b; spill OF x273 to reg (r11)
movzx r9, byte [ rsp + 0x2d8 ]; load byte memx329 to register64
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
adox r9, r15; loading flag
adox r14, r12
seto r9b; spill OF x331 to reg (r9)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
movzx rcx, cl
movzx rbx, bl
adox rbx, r12; loading flag
adox rbp, rcx
seto cl; spill OF x120 to reg (rcx)
movzx rbx, byte [ rsp + 0x2e8 ]; load byte memx161 to register64
inc r12; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov r15, -0x1 ; moving imm to reg
adox rbx, r15; loading flag
adox rbp, [ rsp + 0x40 ]
seto bl; spill OF x163 to reg (rbx)
movzx r12, byte [ rsp + 0x2f0 ]; load byte memx203 to register64
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
adox r12, r15; loading flag
adox rbp, [ rsp + 0x88 ]
mov r12, 0x2341f27177344 ; moving imm to reg
xchg rdx, r12; 0x2341f27177344, swapping with x279, which is currently in rdx
mulx r13, r15, r13; x209, x208<- x192 * 0x2341f27177344
seto dl; spill OF x205 to reg (rdx)
mov [ rsp + 0x318 ], r14; spilling x330 to mem
movzx r14, byte [ rsp + 0x300 ]; load byte memx231 to register64
mov [ rsp + 0x320 ], r13; spilling x209 to mem
mov r13, -0x1 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r13, -0x1 ; moving imm to reg
adox r14, r13; loading flag
adox r15, [ rsp + 0x2e0 ]
seto r14b; spill OF x233 to reg (r14)
movzx r13, byte [ rsp + 0x310 ]; load byte memx246 to register64
mov byte [ rsp + 0x328 ], r9b; spilling byte x331 to mem
mov r9, -0x1 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r9, -0x1 ; moving imm to reg
adox r13, r9; loading flag
adox rbp, r15
mov r13b, dl; preserving value of x205 into a new reg
mov rdx, [ rax + 0x28 ]; saving arg2[5] in rdx.
mulx r15, r9, r8; x255, x254<- x3 * arg2[5]
mov [ rsp + 0x330 ], r15; spilling x255 to mem
setc r15b; spill CF x288 to reg (r15)
clc;
mov byte [ rsp + 0x338 ], r14b; spilling byte x233 to mem
mov r14, -0x1 ; moving imm to reg
movzx r11, r11b
adcx r11, r14; loading flag
adcx r9, [ rsp + 0x2f8 ]
seto r11b; spill OF x248 to reg (r11)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, r14; loading flag
adox rbp, r9
mov r15, 0x6cfc5fd681c52056 ; moving imm to reg
mov rdx, r15; 0x6cfc5fd681c52056 to rdx
mulx r15, r9, r12; x298, x297<- x279 * 0x6cfc5fd681c52056
movzx r14, bl; x164, copying x163 here, cause x163 is needed in a reg for other than x164, namely all: , x164, size: 1
movzx rcx, cl
lea r14, [ r14 + rcx ]
seto cl; spill OF x290 to reg (rcx)
mov rbx, -0x1 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbx, -0x1 ; moving imm to reg
movzx r10, r10b
adox r10, rbx; loading flag
adox r9, [ rsp + 0x308 ]
seto r10b; spill OF x318 to reg (r10)
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, rbx; loading flag
adox r14, [ rsp + 0x80 ]
seto r13b; spill OF x207 to reg (r13)
movzx rbx, byte [ rsp + 0x328 ]; load byte memx331 to register64
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbx, rdx; loading flag
adox rbp, r9
movzx rbx, byte [ rsp + 0x338 ]; x234, copying x233 here, cause x233 is needed in a reg for other than x234, namely all: , x234, size: 1
mov r9, [ rsp + 0x320 ]; load m64 x209 to register64
lea rbx, [ rbx + r9 ]; r8/64 + m8
mov rdx, r8; x3 to rdx
mulx rdx, r8, [ rax + 0x30 ]; x253, x252<- x3 * arg2[6]
setc r9b; spill CF x275 to reg (r9)
clc;
mov [ rsp + 0x340 ], rbp; spilling x332 to mem
mov rbp, -0x1 ; moving imm to reg
movzx r11, r11b
adcx r11, rbp; loading flag
adcx r14, rbx
setc r11b; spill CF x250 to reg (r11)
clc;
movzx r9, r9b
adcx r9, rbp; loading flag
adcx r8, [ rsp + 0x330 ]
seto r9b; spill OF x333 to reg (r9)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, rbx; loading flag
adox r14, r8
mov rcx, 0x2341f27177344 ; moving imm to reg
xchg rdx, r12; x279, swapping with x253, which is currently in rdx
mulx rdx, r8, rcx; x296, x295<- x279 * 0x2341f27177344
setc bpl; spill CF x277 to reg (rbp)
clc;
movzx r10, r10b
adcx r10, rbx; loading flag
adcx r15, r8
setc r10b; spill CF x320 to reg (r10)
clc;
movzx r9, r9b
adcx r9, rbx; loading flag
adcx r14, r15
movzx r9, bpl; x278, copying x277 here, cause x277 is needed in a reg for other than x278, namely all: , x278, size: 1
lea r9, [ r9 + r12 ]
movzx r12, r11b; x251, copying x250 here, cause x250 is needed in a reg for other than x251, namely all: , x251, size: 1
movzx r13, r13b
lea r12, [ r12 + r13 ]
adox r9, r12
movzx r13, r10b; x321, copying x320 here, cause x320 is needed in a reg for other than x321, namely all: , x321, size: 1
lea r13, [ r13 + rdx ]
adcx r13, r9
seto r11b; spill OF x338 to reg (r11)
adc r11b, 0x0
movzx r11, r11b
mov rbp, [ rsi + 0x20 ]; load m64 x4 to register64
mov rdx, rbp; x4 to rdx
mulx rbp, r8, [ rax + 0x0 ]; x352, x351<- x4 * arg2[0]
adox r8, [ rsp + 0x1a0 ]
mov r15, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r8; x366, swapping with x4, which is currently in rdx
mulx r10, r12, r15; x395, x394<- x366 * 0xffffffffffffffff
adcx r12, rdx
mov r12, rdx; preserving value of x366 into a new reg
mov rdx, [ rax + 0x8 ]; saving arg2[1] in rdx.
mulx r9, rbx, r8; x350, x349<- x4 * arg2[1]
setc cl; spill CF x410 to reg (rcx)
clc;
adcx rbx, rbp
mov rdx, r12; x366 to rdx
mulx r12, rbp, r15; x393, x392<- x366 * 0xffffffffffffffff
xchg rdx, r8; x4, swapping with x366, which is currently in rdx
mov byte [ rsp + 0x348 ], r11b; spilling byte x338 to mem
mulx r15, r11, [ rax + 0x10 ]; x348, x347<- x4 * arg2[2]
mov [ rsp + 0x350 ], r13; spilling x336 to mem
mov r13, [ rsp + 0x240 ]; x368, copying x326 here, cause x326 is needed in a reg for other than x368, namely all: , x368--x369, size: 1
adox r13, rbx
setc bl; spill CF x354 to reg (rbx)
clc;
adcx rbp, r10
seto r10b; spill OF x369 to reg (r10)
mov [ rsp + 0x358 ], r14; spilling x334 to mem
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rcx, cl
adox rcx, r14; loading flag
adox r13, rbp
setc cl; spill CF x397 to reg (rcx)
clc;
movzx rbx, bl
adcx rbx, r14; loading flag
adcx r9, r11
setc bl; spill CF x356 to reg (rbx)
clc;
movzx r10, r10b
adcx r10, r14; loading flag
adcx r9, [ rsp + 0x2c8 ]
mov r11, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r8; x366, swapping with x4, which is currently in rdx
mulx r10, rbp, r11; x391, x390<- x366 * 0xffffffffffffffff
seto r14b; spill OF x412 to reg (r14)
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r11; loading flag
adox r12, rbp
seto cl; spill OF x399 to reg (rcx)
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, rbp; loading flag
adox r9, r12
mov r14, rdx; preserving value of x366 into a new reg
mov rdx, [ rax + 0x18 ]; saving arg2[3] in rdx.
mulx r12, r11, r8; x346, x345<- x4 * arg2[3]
seto bpl; spill OF x414 to reg (rbp)
mov [ rsp + 0x360 ], r9; spilling x413 to mem
mov r9, -0x1 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r9, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, r9; loading flag
adox r15, r11
mov rbx, 0xfdc1767ae2ffffff ; moving imm to reg
mov rdx, r14; x366 to rdx
mulx r14, r11, rbx; x389, x388<- x366 * 0xfdc1767ae2ffffff
mov r9, [ rsp + 0x318 ]; x372, copying x330 here, cause x330 is needed in a reg for other than x372, namely all: , x372--x373, size: 1
adcx r9, r15
seto r15b; spill OF x358 to reg (r15)
mov rbx, -0x1 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbx, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, rbx; loading flag
adox r10, r11
setc cl; spill CF x373 to reg (rcx)
clc;
movzx rbp, bpl
adcx rbp, rbx; loading flag
adcx r9, r10
mov rbp, rdx; preserving value of x366 into a new reg
mov rdx, [ rax + 0x20 ]; saving arg2[4] in rdx.
mulx r11, r10, r8; x344, x343<- x4 * arg2[4]
seto bl; spill OF x401 to reg (rbx)
mov [ rsp + 0x368 ], r9; spilling x415 to mem
mov r9, -0x1 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r9, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, r9; loading flag
adox r12, r10
setc r15b; spill CF x416 to reg (r15)
clc;
movzx rcx, cl
adcx rcx, r9; loading flag
adcx r12, [ rsp + 0x340 ]
mov rcx, 0x7bc65c783158aea3 ; moving imm to reg
mov rdx, rcx; 0x7bc65c783158aea3 to rdx
mulx rcx, r10, rbp; x387, x386<- x366 * 0x7bc65c783158aea3
setc r9b; spill CF x375 to reg (r9)
clc;
mov rdx, -0x1 ; moving imm to reg
movzx rbx, bl
adcx rbx, rdx; loading flag
adcx r14, r10
setc bl; spill CF x403 to reg (rbx)
clc;
movzx r15, r15b
adcx r15, rdx; loading flag
adcx r12, r14
mov rdx, r8; x4 to rdx
mulx r8, r15, [ rax + 0x28 ]; x342, x341<- x4 * arg2[5]
mov r10, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, r10; 0x6cfc5fd681c52056, swapping with x4, which is currently in rdx
mov [ rsp + 0x370 ], r12; spilling x417 to mem
mulx r14, r12, rbp; x385, x384<- x366 * 0x6cfc5fd681c52056
adox r15, r11
setc r11b; spill CF x418 to reg (r11)
clc;
mov rdx, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, rdx; loading flag
adcx r15, [ rsp + 0x358 ]
seto r9b; spill OF x362 to reg (r9)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, rdx; loading flag
adox rcx, r12
seto bl; spill OF x405 to reg (rbx)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, r12; loading flag
adox r15, rcx
mov r11, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rax + 0x30 ]; saving arg2[6] in rdx.
mulx r10, rcx, r10; x340, x339<- x4 * arg2[6]
seto r11b; spill OF x420 to reg (r11)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, r12; loading flag
adox r8, rcx
mov r9, 0x2341f27177344 ; moving imm to reg
mov rdx, r9; 0x2341f27177344 to rdx
mulx rbp, r9, rbp; x383, x382<- x366 * 0x2341f27177344
mov rcx, [ rsp + 0x350 ]; x378, copying x336 here, cause x336 is needed in a reg for other than x378, namely all: , x378--x379, size: 1
adcx rcx, r8
mov r8, 0x0 ; moving imm to reg
adox r10, r8
dec r8; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx rbx, bl
adox rbx, r8; loading flag
adox r14, r9
mov r12, 0x0 ; moving imm to reg
adox rbp, r12
inc r8; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov r12, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, r12; loading flag
adox rcx, r14
movzx rbx, byte [ rsp + 0x348 ]; x380, copying x338 here, cause x338 is needed in a reg for other than x380, namely all: , x380--x381, size: 1
adcx rbx, r10
adox rbp, rbx
mov r11, [ rsi + 0x28 ]; load m64 x5 to register64
seto r9b; spill OF x425 to reg (r9)
adc r9b, 0x0
movzx r9, r9b
mov r10, rdx; preserving value of 0x2341f27177344 into a new reg
mov rdx, [ rax + 0x0 ]; saving arg2[0] in rdx.
mulx r14, rbx, r11; x439, x438<- x5 * arg2[0]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mulx r8, r12, r11; x433, x432<- x5 * arg2[3]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov byte [ rsp + 0x378 ], r9b; spilling byte x425 to mem
mulx r10, r9, r11; x437, x436<- x5 * arg2[1]
adox r9, r14
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x380 ], rbp; spilling x423 to mem
mulx r14, rbp, r11; x435, x434<- x5 * arg2[2]
adox rbp, r10
adox r12, r14
mov rdx, r11; x5 to rdx
mulx r11, r10, [ rax + 0x28 ]; x429, x428<- x5 * arg2[5]
mov [ rsp + 0x388 ], rcx; spilling x421 to mem
mulx r14, rcx, [ rax + 0x20 ]; x431, x430<- x5 * arg2[4]
adox rcx, r8
adox r10, r14
mulx rdx, r8, [ rax + 0x30 ]; x427, x426<- x5 * arg2[6]
adcx rbx, r13
adox r8, r11
mov r13, 0x0 ; moving imm to reg
adox rdx, r13
mov r11, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r11; 0xffffffffffffffff, swapping with x452, which is currently in rdx
mulx r14, r13, rbx; x482, x481<- x453 * 0xffffffffffffffff
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, rbx
mov r13, 0xffffffffffffffff ; moving imm to reg
mov rdx, rbx; x453 to rdx
mov [ rsp + 0x390 ], r11; spilling x452 to mem
mulx rbx, r11, r13; x480, x479<- x453 * 0xffffffffffffffff
mov r13, [ rsp + 0x360 ]; x455, copying x413 here, cause x413 is needed in a reg for other than x455, namely all: , x455--x456, size: 1
adcx r13, r9
setc r9b; spill CF x456 to reg (r9)
clc;
adcx r11, r14
mov r14, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x398 ], r8; spilling x450 to mem
mov [ rsp + 0x3a0 ], r10; spilling x448 to mem
mulx r8, r10, r14; x478, x477<- x453 * 0xffffffffffffffff
adox r11, r13
setc r13b; spill CF x484 to reg (r13)
clc;
mov r14, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, r14; loading flag
adcx rbp, [ rsp + 0x368 ]
seto r9b; spill OF x499 to reg (r9)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, r14; loading flag
adox rbx, r10
setc r13b; spill CF x458 to reg (r13)
clc;
movzx r9, r9b
adcx r9, r14; loading flag
adcx rbp, rbx
seto r10b; spill OF x486 to reg (r10)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, r9; loading flag
adox r12, [ rsp + 0x370 ]
mov r13, 0xfdc1767ae2ffffff ; moving imm to reg
mulx rbx, r14, r13; x476, x475<- x453 * 0xfdc1767ae2ffffff
seto r9b; spill OF x460 to reg (r9)
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r10, r10b
adox r10, r13; loading flag
adox r8, r14
adcx r8, r12
setc r10b; spill CF x503 to reg (r10)
clc;
movzx r9, r9b
adcx r9, r13; loading flag
adcx r15, rcx
mov rcx, 0x7bc65c783158aea3 ; moving imm to reg
mulx r12, r9, rcx; x474, x473<- x453 * 0x7bc65c783158aea3
adox r9, rbx
setc bl; spill CF x462 to reg (rbx)
clc;
movzx r10, r10b
adcx r10, r13; loading flag
adcx r15, r9
mov r14, [ rsp + 0x388 ]; load m64 x421 to register64
seto r10b; spill OF x490 to reg (r10)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, r9; loading flag
adox r14, [ rsp + 0x3a0 ]
mov rbx, 0x6cfc5fd681c52056 ; moving imm to reg
mulx r13, r9, rbx; x472, x471<- x453 * 0x6cfc5fd681c52056
setc bl; spill CF x505 to reg (rbx)
clc;
mov rcx, -0x1 ; moving imm to reg
movzx r10, r10b
adcx r10, rcx; loading flag
adcx r12, r9
mov r10, 0x2341f27177344 ; moving imm to reg
mulx rdx, r9, r10; x470, x469<- x453 * 0x2341f27177344
mov rcx, [ rsp + 0x398 ]; load m64 x450 to register64
mov r10, [ rsp + 0x380 ]; x465, copying x423 here, cause x423 is needed in a reg for other than x465, namely all: , x465--x466, size: 1
adox r10, rcx
setc cl; spill CF x492 to reg (rcx)
clc;
mov [ rsp + 0x3a8 ], r15; spilling x504 to mem
mov r15, -0x1 ; moving imm to reg
movzx rbx, bl
adcx rbx, r15; loading flag
adcx r14, r12
setc bl; spill CF x507 to reg (rbx)
clc;
movzx rcx, cl
adcx rcx, r15; loading flag
adcx r13, r9
seto r12b; spill OF x466 to reg (r12)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rcx, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, rcx; loading flag
adox r10, r13
movzx r9, byte [ rsp + 0x378 ]; load byte memx425 to register64
seto bl; spill OF x509 to reg (rbx)
inc rcx; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov r15, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, r15; loading flag
adox r9, [ rsp + 0x390 ]
adcx rdx, rcx
clc;
movzx rbx, bl
adcx rbx, r15; loading flag
adcx r9, rdx
seto r12b; spill OF x512 to reg (r12)
adc r12b, 0x0
movzx r12, r12b
mov r13, [ rsi + 0x30 ]; load m64 x6 to register64
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx rbx, rcx, r13; x526, x525<- x6 * arg2[0]
adox rcx, r11
mov r11, 0xffffffffffffffff ; moving imm to reg
mov rdx, r11; 0xffffffffffffffff to rdx
mulx r11, r15, rcx; x569, x568<- x540 * 0xffffffffffffffff
adcx r15, rcx
mov r15, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ rax + 0x8 ]; saving arg2[1] in rdx.
mov byte [ rsp + 0x3b0 ], r12b; spilling byte x512 to mem
mov [ rsp + 0x3b8 ], r9; spilling x510 to mem
mulx r12, r9, r13; x524, x523<- x6 * arg2[1]
seto r15b; spill OF x541 to reg (r15)
mov [ rsp + 0x3c0 ], r10; spilling x508 to mem
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r9, rbx
mov rbx, 0xffffffffffffffff ; moving imm to reg
mov rdx, rcx; x540 to rdx
mulx rcx, r10, rbx; x567, x566<- x540 * 0xffffffffffffffff
setc bl; spill CF x584 to reg (rbx)
clc;
mov [ rsp + 0x3c8 ], r14; spilling x506 to mem
mov r14, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, r14; loading flag
adcx rbp, r9
seto r15b; spill OF x528 to reg (r15)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r10, r11
seto r11b; spill OF x571 to reg (r11)
dec r14; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx rbx, bl
adox rbx, r14; loading flag
adox rbp, r10
setc bl; spill CF x543 to reg (rbx)
seto r9b; spill OF x586 to reg (r9)
mov r10, rbp; x600, copying x585 here, cause x585 is needed in a reg for other than x600, namely all: , x600--x601, x616, size: 2
mov r14, 0xffffffffffffffff ; moving imm to reg
sub r10, r14
mov r14, rdx; preserving value of x540 into a new reg
mov rdx, [ rax + 0x10 ]; saving arg2[2] in rdx.
mov [ rsp + 0x3d0 ], r10; spilling x600 to mem
mov byte [ rsp + 0x3d8 ], r9b; spilling byte x586 to mem
mulx r10, r9, r13; x522, x521<- x6 * arg2[2]
mov [ rsp + 0x3e0 ], r10; spilling x522 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r15, r15b
adox r15, r10; loading flag
adox r12, r9
seto r15b; spill OF x530 to reg (r15)
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, r9; loading flag
adox r8, r12
mov rbx, 0xffffffffffffffff ; moving imm to reg
mov rdx, r14; x540 to rdx
mulx r14, r12, rbx; x565, x564<- x540 * 0xffffffffffffffff
setc r10b; spill CF x601 to reg (r10)
clc;
movzx r11, r11b
adcx r11, r9; loading flag
adcx rcx, r12
seto r11b; spill OF x545 to reg (r11)
movzx r12, byte [ rsp + 0x3d8 ]; load byte memx586 to register64
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
adox r12, r9; loading flag
adox r8, rcx
mov r12, rdx; preserving value of x540 into a new reg
mov rdx, [ rax + 0x18 ]; saving arg2[3] in rdx.
mulx rcx, r9, r13; x520, x519<- x6 * arg2[3]
mov [ rsp + 0x3e8 ], rcx; spilling x520 to mem
setc cl; spill CF x573 to reg (rcx)
mov byte [ rsp + 0x3f0 ], r11b; spilling byte x545 to mem
seto r11b; spill OF x588 to reg (r11)
mov [ rsp + 0x3f8 ], r14; spilling x565 to mem
movzx r14, r10b; x601, copying x601 here, cause x601 is needed in a reg for other than x601, namely all: , x602--x603, size: 1
add r14, -0x1
mov r10, r8; x602, copying x587 here, cause x587 is needed in a reg for other than x602, namely all: , x617, x602--x603, size: 2
sbb r10, rbx
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r15, r15b
adox r15, r14; loading flag
adox r9, [ rsp + 0x3e0 ]
mov r15, 0xfdc1767ae2ffffff ; moving imm to reg
mov rdx, r12; x540 to rdx
mulx r12, r14, r15; x563, x562<- x540 * 0xfdc1767ae2ffffff
setc r15b; spill CF x603 to reg (r15)
clc;
mov rbx, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, rbx; loading flag
adcx r14, [ rsp + 0x3f8 ]
seto cl; spill OF x532 to reg (rcx)
movzx rbx, byte [ rsp + 0x3f0 ]; load byte memx545 to register64
mov [ rsp + 0x400 ], r10; spilling x602 to mem
mov r10, -0x1 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r10, -0x1 ; moving imm to reg
adox rbx, r10; loading flag
adox r9, [ rsp + 0x3a8 ]
setc bl; spill CF x575 to reg (rbx)
clc;
movzx r11, r11b
adcx r11, r10; loading flag
adcx r9, r14
setc r11b; spill CF x590 to reg (r11)
seto r14b; spill OF x547 to reg (r14)
movzx r10, r15b; x603, copying x603 here, cause x603 is needed in a reg for other than x603, namely all: , x604--x605, size: 1
add r10, -0x1
mov r10, r9; x604, copying x589 here, cause x589 is needed in a reg for other than x604, namely all: , x618, x604--x605, size: 2
mov r15, 0xffffffffffffffff ; moving imm to reg
sbb r10, r15
mov r15, rdx; preserving value of x540 into a new reg
mov rdx, [ rax + 0x20 ]; saving arg2[4] in rdx.
mov [ rsp + 0x408 ], r10; spilling x604 to mem
mov byte [ rsp + 0x410 ], r11b; spilling byte x590 to mem
mulx r10, r11, r13; x518, x517<- x6 * arg2[4]
mov [ rsp + 0x418 ], r10; spilling x518 to mem
mov r10, -0x1 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r10, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r10; loading flag
adox r11, [ rsp + 0x3e8 ]
setc cl; spill CF x605 to reg (rcx)
clc;
movzx r14, r14b
adcx r14, r10; loading flag
adcx r11, [ rsp + 0x3c8 ]
mov r14, 0x7bc65c783158aea3 ; moving imm to reg
mov rdx, r15; x540 to rdx
mulx r15, r10, r14; x561, x560<- x540 * 0x7bc65c783158aea3
setc r14b; spill CF x549 to reg (r14)
clc;
mov [ rsp + 0x420 ], r15; spilling x561 to mem
mov r15, -0x1 ; moving imm to reg
movzx rbx, bl
adcx rbx, r15; loading flag
adcx r12, r10
setc bl; spill CF x577 to reg (rbx)
movzx r10, byte [ rsp + 0x410 ]; load byte memx590 to register64
clc;
adcx r10, r15; loading flag
adcx r11, r12
xchg rdx, r13; x6, swapping with x540, which is currently in rdx
mulx r10, r12, [ rax + 0x28 ]; x516, x515<- x6 * arg2[5]
setc r15b; spill CF x592 to reg (r15)
mov [ rsp + 0x428 ], r10; spilling x516 to mem
seto r10b; spill OF x534 to reg (r10)
mov byte [ rsp + 0x430 ], bl; spilling byte x577 to mem
movzx rbx, cl; x605, copying x605 here, cause x605 is needed in a reg for other than x605, namely all: , x606--x607, size: 1
add rbx, -0x1
mov rbx, r11; x606, copying x591 here, cause x591 is needed in a reg for other than x606, namely all: , x606--x607, x619, size: 2
mov rcx, 0xfdc1767ae2ffffff ; moving imm to reg
sbb rbx, rcx
mov rcx, -0x1 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rcx, -0x1 ; moving imm to reg
movzx r10, r10b
adox r10, rcx; loading flag
adox r12, [ rsp + 0x418 ]
mov r10, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, r10; 0x6cfc5fd681c52056, swapping with x6, which is currently in rdx
mov [ rsp + 0x438 ], rbx; spilling x606 to mem
mulx rcx, rbx, r13; x559, x558<- x540 * 0x6cfc5fd681c52056
setc dl; spill CF x607 to reg (rdx)
clc;
mov [ rsp + 0x440 ], rcx; spilling x559 to mem
mov rcx, -0x1 ; moving imm to reg
movzx r14, r14b
adcx r14, rcx; loading flag
adcx r12, [ rsp + 0x3c0 ]
seto r14b; spill OF x536 to reg (r14)
movzx rcx, byte [ rsp + 0x430 ]; load byte memx577 to register64
mov byte [ rsp + 0x448 ], dl; spilling byte x607 to mem
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
adox rcx, rdx; loading flag
adox rbx, [ rsp + 0x420 ]
setc cl; spill CF x551 to reg (rcx)
clc;
movzx r15, r15b
adcx r15, rdx; loading flag
adcx r12, rbx
setc r15b; spill CF x594 to reg (r15)
seto bl; spill OF x579 to reg (rbx)
movzx rdx, byte [ rsp + 0x448 ]; x607, copying x607 here, cause x607 is needed in a reg for other than x607, namely all: , x608--x609, size: 1
add rdx, -0x1
mov byte [ rsp + 0x450 ], cl; spilling byte x551 to mem
mov rcx, r12; x608, copying x593 here, cause x593 is needed in a reg for other than x608, namely all: , x608--x609, x620, size: 2
mov byte [ rsp + 0x458 ], r14b; spilling byte x536 to mem
mov r14, 0x7bc65c783158aea3 ; moving imm to reg
sbb rcx, r14
mov rdx, r10; x6 to rdx
mulx rdx, r10, [ rax + 0x30 ]; x514, x513<- x6 * arg2[6]
movzx r14, byte [ rsp + 0x458 ]; load byte memx536 to register64
mov [ rsp + 0x460 ], rcx; spilling x608 to mem
mov rcx, -0x1 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rcx, -0x1 ; moving imm to reg
adox r14, rcx; loading flag
adox r10, [ rsp + 0x428 ]
seto r14b; spill OF x538 to reg (r14)
movzx rcx, byte [ rsp + 0x450 ]; load byte memx551 to register64
mov [ rsp + 0x468 ], rdx; spilling x514 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rcx, rdx; loading flag
adox r10, [ rsp + 0x3b8 ]
mov rcx, 0x2341f27177344 ; moving imm to reg
mov rdx, r13; x540 to rdx
mulx rdx, r13, rcx; x557, x556<- x540 * 0x2341f27177344
seto cl; spill OF x553 to reg (rcx)
mov [ rsp + 0x470 ], rdx; spilling x557 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbx, bl
adox rbx, rdx; loading flag
adox r13, [ rsp + 0x440 ]
seto bl; spill OF x581 to reg (rbx)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, rdx; loading flag
adox r10, r13
movzx r15, r14b; x539, copying x538 here, cause x538 is needed in a reg for other than x539, namely all: , x539, size: 1
mov r13, [ rsp + 0x468 ]; load m64 x514 to register64
lea r15, [ r15 + r13 ]; r8/64 + m8
seto r13b; spill OF x596 to reg (r13)
mov r14, r10; x610, copying x595 here, cause x595 is needed in a reg for other than x610, namely all: , x621, x610--x611, size: 2
mov rdx, 0x6cfc5fd681c52056 ; moving imm to reg
sbb r14, rdx
movzx rdx, bl; x582, copying x581 here, cause x581 is needed in a reg for other than x582, namely all: , x582, size: 1
mov [ rsp + 0x478 ], r14; spilling x610 to mem
mov r14, [ rsp + 0x470 ]; load m64 x557 to register64
lea rdx, [ rdx + r14 ]; r8/64 + m8
mov r14, -0x1 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbx, -0x1 ; moving imm to reg
movzx r14, byte [ rsp + 0x3b0 ]; load byte memx512 to register64
movzx rcx, cl
adox rcx, rbx; loading flag
adox r15, r14
seto r14b; spill OF x555 to reg (r14)
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rcx, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, rcx; loading flag
adox r15, rdx
seto r13b; spill OF x598 to reg (r13)
mov rdx, r15; x612, copying x597 here, cause x597 is needed in a reg for other than x612, namely all: , x612--x613, x622, size: 2
mov rbx, 0x2341f27177344 ; moving imm to reg
sbb rdx, rbx
movzx rcx, r13b; x599, copying x598 here, cause x598 is needed in a reg for other than x599, namely all: , x599, size: 1
movzx r14, r14b
lea rcx, [ rcx + r14 ]
sbb rcx, 0x00000000
mov rcx, [ rsp + 0x478 ]; x621, copying x610 here, cause x610 is needed in a reg for other than x621, namely all: , x621, size: 1
cmovc rcx, r10; if CF, x621<- x595 (nzVar)
mov r10, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r10 + 0x28 ], rcx; out1[5] = x621
mov r14, [ rsp + 0x408 ]; x618, copying x604 here, cause x604 is needed in a reg for other than x618, namely all: , x618, size: 1
cmovc r14, r9; if CF, x618<- x589 (nzVar)
mov r9, [ rsp + 0x400 ]; x617, copying x602 here, cause x602 is needed in a reg for other than x617, namely all: , x617, size: 1
cmovc r9, r8; if CF, x617<- x587 (nzVar)
mov r8, [ rsp + 0x3d0 ]; x616, copying x600 here, cause x600 is needed in a reg for other than x616, namely all: , x616, size: 1
cmovc r8, rbp; if CF, x616<- x585 (nzVar)
mov [ r10 + 0x8 ], r9; out1[1] = x617
mov [ r10 + 0x0 ], r8; out1[0] = x616
mov rbp, [ rsp + 0x438 ]; x619, copying x606 here, cause x606 is needed in a reg for other than x619, namely all: , x619, size: 1
cmovc rbp, r11; if CF, x619<- x591 (nzVar)
cmovc rdx, r15; if CF, x622<- x597 (nzVar)
mov [ r10 + 0x18 ], rbp; out1[3] = x619
mov r11, [ rsp + 0x460 ]; x620, copying x608 here, cause x608 is needed in a reg for other than x620, namely all: , x620, size: 1
cmovc r11, r12; if CF, x620<- x593 (nzVar)
mov [ r10 + 0x10 ], r14; out1[2] = x618
mov [ r10 + 0x30 ], rdx; out1[6] = x622
mov [ r10 + 0x20 ], r11; out1[4] = x620
mov rbx, [ rsp + 0x480 ]; restoring from stack
mov rbp, [ rsp + 0x488 ]; restoring from stack
mov r12, [ rsp + 0x490 ]; restoring from stack
mov r13, [ rsp + 0x498 ]; restoring from stack
mov r14, [ rsp + 0x4a0 ]; restoring from stack
mov r15, [ rsp + 0x4a8 ]; restoring from stack
add rsp, 0x4b0 
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; clocked at 3600 MHz
; first cyclecount 346.145, best 342.36, lastGood 394.4230769230769
; seed 2529639215636402 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 37037 ms / 500 runs=> 74.074ms/run
; Time spent for assembling and measureing (initial batch_size=27, initial num_batches=101): 971 ms
; Ratio (time for assembling + measure)/(total runtime for 500runs): 0.026217026217026217
; number reverted permutation/ tried permutation: 139 / 255 =54.510%
; number reverted decision/ tried decision: 113 / 246 =45.935%