SECTION .text
	GLOBAL mul_p434
mul_p434:
sub rsp, 0x7c8 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x798 ], rbx; saving to stack
mov [ rsp + 0x7a0 ], rbp; saving to stack
mov [ rsp + 0x7a8 ], r12; saving to stack
mov [ rsp + 0x7b0 ], r13; saving to stack
mov [ rsp + 0x7b8 ], r14; saving to stack
mov [ rsp + 0x7c0 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x7 to register64
mov r10, [ rsi + 0x30 ]; load m64 x6 to register64
mov r11, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x0 ]; saving arg2[0] in rdx.
mulx rbx, rbp, rax; x21, x20<- x7 * arg2[0]
mov r12, 0xffffffffffffffff ; moving imm to reg
mov rdx, rbp; x20 to rdx
mulx rbp, r13, r12; x48, x47<- x20 * 0xffffffffffffffff
xchg rdx, rax; x7, swapping with x20, which is currently in rdx
mulx r14, r15, [ r11 + 0x8 ]; x19, x18<- x7 * arg2[1]
test al, al
adox r13, rax
adcx r15, rbx
xchg rdx, rax; x20, swapping with x7, which is currently in rdx
mulx r13, rcx, r12; x46, x45<- x20 * 0xffffffffffffffff
seto r8b; spill OF x63 to reg (r8)
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rcx, rbp
seto bl; spill OF x50 to reg (rbx)
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, rbp; loading flag
adox r15, rcx
mov r8, [ rsi + 0x8 ]; load m64 x1 to register64
mov rcx, rdx; preserving value of x20 into a new reg
mov rdx, [ r11 + 0x0 ]; saving arg2[0] in rdx.
mulx r9, rbp, r8; x91, x90<- x1 * arg2[0]
seto r12b; spill OF x65 to reg (r12)
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, r15
mov r15, 0xffffffffffffffff ; moving imm to reg
mov rdx, rbp; x105 to rdx
mulx rbp, rdi, r15; x134, x133<- x105 * 0xffffffffffffffff
mov r15, rdx; preserving value of x105 into a new reg
mov rdx, [ r11 + 0x10 ]; saving arg2[2] in rdx.
mov [ rsp + 0x8 ], r10; spilling x6 to mem
mov [ rsp + 0x10 ], rbp; spilling x134 to mem
mulx r10, rbp, rax; x17, x16<- x7 * arg2[2]
mov [ rsp + 0x18 ], r10; spilling x17 to mem
seto r10b; spill OF x106 to reg (r10)
mov [ rsp + 0x20 ], r9; spilling x91 to mem
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rdi, r15
adcx rbp, r14
mov r14, 0xffffffffffffffff ; moving imm to reg
mov rdx, rcx; x20 to rdx
mulx rcx, r9, r14; x44, x43<- x20 * 0xffffffffffffffff
seto r14b; spill OF x149 to reg (r14)
mov [ rsp + 0x28 ], rcx; spilling x44 to mem
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbx, bl
adox rbx, rcx; loading flag
adox r13, r9
seto bl; spill OF x52 to reg (rbx)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, r9; loading flag
adox rbp, r13
mov r12, rdx; preserving value of x20 into a new reg
mov rdx, [ r11 + 0x8 ]; saving arg2[1] in rdx.
mulx r13, rcx, r8; x89, x88<- x1 * arg2[1]
setc r9b; spill CF x25 to reg (r9)
clc;
adcx rcx, [ rsp + 0x20 ]
mov [ rsp + 0x30 ], r13; spilling x89 to mem
setc r13b; spill CF x93 to reg (r13)
clc;
mov byte [ rsp + 0x38 ], bl; spilling byte x52 to mem
mov rbx, -0x1 ; moving imm to reg
movzx r10, r10b
adcx r10, rbx; loading flag
adcx rbp, rcx
mov r10, 0xffffffffffffffff ; moving imm to reg
mov rdx, r10; 0xffffffffffffffff to rdx
mulx r10, rcx, r15; x132, x131<- x105 * 0xffffffffffffffff
seto bl; spill OF x67 to reg (rbx)
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rcx, [ rsp + 0x10 ]
seto dl; spill OF x136 to reg (rdx)
mov [ rsp + 0x40 ], r10; spilling x132 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r14, r14b
adox r14, r10; loading flag
adox rbp, rcx
mov r14, [ rsi + 0x10 ]; load m64 x2 to register64
mov cl, dl; preserving value of x136 into a new reg
mov rdx, [ r11 + 0x0 ]; saving arg2[0] in rdx.
mov byte [ rsp + 0x48 ], r13b; spilling byte x93 to mem
mulx r10, r13, r14; x178, x177<- x2 * arg2[0]
mov [ rsp + 0x50 ], r10; spilling x178 to mem
seto r10b; spill OF x151 to reg (r10)
mov byte [ rsp + 0x58 ], cl; spilling byte x136 to mem
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, rbp
mov rbp, 0xffffffffffffffff ; moving imm to reg
mov rdx, rbp; 0xffffffffffffffff to rdx
mulx rbp, rcx, r13; x221, x220<- x192 * 0xffffffffffffffff
xchg rdx, rax; x7, swapping with 0xffffffffffffffff, which is currently in rdx
mov [ rsp + 0x60 ], rbp; spilling x221 to mem
mulx rax, rbp, [ r11 + 0x18 ]; x15, x14<- x7 * arg2[3]
mov [ rsp + 0x68 ], rax; spilling x15 to mem
seto al; spill OF x193 to reg (rax)
mov byte [ rsp + 0x70 ], r10b; spilling byte x151 to mem
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rcx, r13
seto cl; spill OF x236 to reg (rcx)
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r10, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, r10; loading flag
adox rbp, [ rsp + 0x18 ]
mov r9, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, r9; 0xfdc1767ae2ffffff, swapping with x7, which is currently in rdx
mov byte [ rsp + 0x78 ], cl; spilling byte x236 to mem
mulx r10, rcx, r12; x42, x41<- x20 * 0xfdc1767ae2ffffff
setc dl; spill CF x108 to reg (rdx)
mov [ rsp + 0x80 ], r10; spilling x42 to mem
movzx r10, byte [ rsp + 0x38 ]; load byte memx52 to register64
clc;
mov byte [ rsp + 0x88 ], al; spilling byte x193 to mem
mov rax, -0x1 ; moving imm to reg
adcx r10, rax; loading flag
adcx rcx, [ rsp + 0x28 ]
setc r10b; spill CF x54 to reg (r10)
clc;
movzx rbx, bl
adcx rbx, rax; loading flag
adcx rbp, rcx
xchg rdx, r8; x1, swapping with x108, which is currently in rdx
mulx rbx, rcx, [ r11 + 0x10 ]; x87, x86<- x1 * arg2[2]
seto al; spill OF x27 to reg (rax)
mov [ rsp + 0x90 ], rbx; spilling x87 to mem
movzx rbx, byte [ rsp + 0x48 ]; load byte memx93 to register64
mov byte [ rsp + 0x98 ], r10b; spilling byte x54 to mem
mov r10, -0x1 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r10, -0x1 ; moving imm to reg
adox rbx, r10; loading flag
adox rcx, [ rsp + 0x30 ]
seto bl; spill OF x95 to reg (rbx)
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r10, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, r10; loading flag
adox rbp, rcx
mov r8, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r8; 0xffffffffffffffff, swapping with x1, which is currently in rdx
mulx rcx, r10, r15; x130, x129<- x105 * 0xffffffffffffffff
setc dl; spill CF x69 to reg (rdx)
mov [ rsp + 0xa0 ], rcx; spilling x130 to mem
movzx rcx, byte [ rsp + 0x58 ]; load byte memx136 to register64
clc;
mov byte [ rsp + 0xa8 ], bl; spilling byte x95 to mem
mov rbx, -0x1 ; moving imm to reg
adcx rcx, rbx; loading flag
adcx r10, [ rsp + 0x40 ]
seto cl; spill OF x110 to reg (rcx)
movzx rbx, byte [ rsp + 0x70 ]; load byte memx151 to register64
mov byte [ rsp + 0xb0 ], dl; spilling byte x69 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbx, rdx; loading flag
adox rbp, r10
mov rdx, [ r11 + 0x8 ]; arg2[1] to rdx
mulx rbx, r10, r14; x176, x175<- x2 * arg2[1]
mov [ rsp + 0xb8 ], rbx; spilling x176 to mem
setc bl; spill CF x138 to reg (rbx)
clc;
adcx r10, [ rsp + 0x50 ]
mov byte [ rsp + 0xc0 ], bl; spilling byte x138 to mem
seto bl; spill OF x153 to reg (rbx)
mov byte [ rsp + 0xc8 ], cl; spilling byte x110 to mem
movzx rcx, byte [ rsp + 0x88 ]; load byte memx193 to register64
mov byte [ rsp + 0xd0 ], al; spilling byte x27 to mem
mov rax, -0x1 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rax, -0x1 ; moving imm to reg
adox rcx, rax; loading flag
adox rbp, r10
mov rcx, 0xffffffffffffffff ; moving imm to reg
mov rdx, rcx; 0xffffffffffffffff to rdx
mulx rcx, r10, r13; x219, x218<- x192 * 0xffffffffffffffff
setc al; spill CF x180 to reg (rax)
clc;
adcx r10, [ rsp + 0x60 ]
setc dl; spill CF x223 to reg (rdx)
mov [ rsp + 0xd8 ], rcx; spilling x219 to mem
movzx rcx, byte [ rsp + 0x78 ]; load byte memx236 to register64
clc;
mov byte [ rsp + 0xe0 ], al; spilling byte x180 to mem
mov rax, -0x1 ; moving imm to reg
adcx rcx, rax; loading flag
adcx rbp, r10
mov rcx, [ rsi + 0x18 ]; load m64 x3 to register64
mov r10b, dl; preserving value of x223 into a new reg
mov rdx, [ r11 + 0x0 ]; saving arg2[0] in rdx.
mov byte [ rsp + 0xe8 ], bl; spilling byte x153 to mem
mulx rax, rbx, rcx; x265, x264<- x3 * arg2[0]
mov [ rsp + 0xf0 ], rax; spilling x265 to mem
setc al; spill CF x238 to reg (rax)
clc;
adcx rbx, rbp
mov rbp, 0xffffffffffffffff ; moving imm to reg
mov rdx, rbp; 0xffffffffffffffff to rdx
mov byte [ rsp + 0xf8 ], al; spilling byte x238 to mem
mulx rbp, rax, rbx; x308, x307<- x279 * 0xffffffffffffffff
seto dl; spill OF x195 to reg (rdx)
mov [ rsp + 0x100 ], rbp; spilling x308 to mem
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rax, rbx
xchg rdx, r9; x7, swapping with x195, which is currently in rdx
mulx rax, rbp, [ r11 + 0x20 ]; x13, x12<- x7 * arg2[4]
mov [ rsp + 0x108 ], rax; spilling x13 to mem
seto al; spill OF x323 to reg (rax)
mov byte [ rsp + 0x110 ], r10b; spilling byte x223 to mem
movzx r10, byte [ rsp + 0xd0 ]; load byte memx27 to register64
mov byte [ rsp + 0x118 ], r9b; spilling byte x195 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r10, r9; loading flag
adox rbp, [ rsp + 0x68 ]
mov r10, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, r12; x20, swapping with x7, which is currently in rdx
mov byte [ rsp + 0x120 ], al; spilling byte x323 to mem
mulx r9, rax, r10; x40, x39<- x20 * 0x7bc65c783158aea3
setc r10b; spill CF x280 to reg (r10)
mov [ rsp + 0x128 ], r9; spilling x40 to mem
movzx r9, byte [ rsp + 0x98 ]; load byte memx54 to register64
clc;
mov [ rsp + 0x130 ], rbp; spilling x28 to mem
mov rbp, -0x1 ; moving imm to reg
adcx r9, rbp; loading flag
adcx rax, [ rsp + 0x80 ]
seto r9b; spill OF x29 to reg (r9)
movzx rbp, byte [ rsp + 0xb0 ]; load byte memx69 to register64
mov byte [ rsp + 0x138 ], r10b; spilling byte x280 to mem
mov r10, -0x1 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r10, -0x1 ; moving imm to reg
adox rbp, r10; loading flag
adox rax, [ rsp + 0x130 ]
mov rbp, rdx; preserving value of x20 into a new reg
mov rdx, [ r11 + 0x18 ]; saving arg2[3] in rdx.
mov byte [ rsp + 0x140 ], r9b; spilling byte x29 to mem
mulx r10, r9, r8; x85, x84<- x1 * arg2[3]
mov [ rsp + 0x148 ], r10; spilling x85 to mem
setc r10b; spill CF x56 to reg (r10)
mov [ rsp + 0x150 ], rax; spilling x70 to mem
movzx rax, byte [ rsp + 0xa8 ]; load byte memx95 to register64
clc;
mov [ rsp + 0x158 ], rbx; spilling x279 to mem
mov rbx, -0x1 ; moving imm to reg
adcx rax, rbx; loading flag
adcx r9, [ rsp + 0x90 ]
setc al; spill CF x97 to reg (rax)
movzx rbx, byte [ rsp + 0xc8 ]; load byte memx110 to register64
clc;
mov byte [ rsp + 0x160 ], r10b; spilling byte x56 to mem
mov r10, -0x1 ; moving imm to reg
adcx rbx, r10; loading flag
adcx r9, [ rsp + 0x150 ]
mov rbx, 0xfdc1767ae2ffffff ; moving imm to reg
mov rdx, r15; x105 to rdx
mulx r15, r10, rbx; x128, x127<- x105 * 0xfdc1767ae2ffffff
setc bl; spill CF x112 to reg (rbx)
mov [ rsp + 0x168 ], r15; spilling x128 to mem
movzx r15, byte [ rsp + 0xc0 ]; load byte memx138 to register64
clc;
mov byte [ rsp + 0x170 ], al; spilling byte x97 to mem
mov rax, -0x1 ; moving imm to reg
adcx r15, rax; loading flag
adcx r10, [ rsp + 0xa0 ]
seto r15b; spill OF x71 to reg (r15)
movzx rax, byte [ rsp + 0xe8 ]; load byte memx153 to register64
mov byte [ rsp + 0x178 ], bl; spilling byte x112 to mem
mov rbx, -0x1 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbx, -0x1 ; moving imm to reg
adox rax, rbx; loading flag
adox r9, r10
xchg rdx, r14; x2, swapping with x105, which is currently in rdx
mulx rax, r10, [ r11 + 0x10 ]; x174, x173<- x2 * arg2[2]
setc bl; spill CF x140 to reg (rbx)
mov [ rsp + 0x180 ], rax; spilling x174 to mem
movzx rax, byte [ rsp + 0xe0 ]; load byte memx180 to register64
clc;
mov byte [ rsp + 0x188 ], r15b; spilling byte x71 to mem
mov r15, -0x1 ; moving imm to reg
adcx rax, r15; loading flag
adcx r10, [ rsp + 0xb8 ]
seto al; spill OF x155 to reg (rax)
movzx r15, byte [ rsp + 0x118 ]; load byte memx195 to register64
mov byte [ rsp + 0x190 ], bl; spilling byte x140 to mem
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, rbx; loading flag
adox r9, r10
mov r15, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r15; 0xffffffffffffffff, swapping with x2, which is currently in rdx
mulx r10, rbx, r13; x217, x216<- x192 * 0xffffffffffffffff
seto dl; spill OF x197 to reg (rdx)
mov [ rsp + 0x198 ], r10; spilling x217 to mem
movzx r10, byte [ rsp + 0x110 ]; load byte memx223 to register64
mov byte [ rsp + 0x1a0 ], al; spilling byte x155 to mem
mov rax, -0x1 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rax, -0x1 ; moving imm to reg
adox r10, rax; loading flag
adox rbx, [ rsp + 0xd8 ]
seto r10b; spill OF x225 to reg (r10)
movzx rax, byte [ rsp + 0xf8 ]; load byte memx238 to register64
mov byte [ rsp + 0x1a8 ], dl; spilling byte x197 to mem
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
adox rax, rdx; loading flag
adox r9, rbx
mov rdx, rcx; x3 to rdx
mulx rcx, rax, [ r11 + 0x8 ]; x263, x262<- x3 * arg2[1]
setc bl; spill CF x182 to reg (rbx)
clc;
adcx rax, [ rsp + 0xf0 ]
mov [ rsp + 0x1b0 ], rcx; spilling x263 to mem
seto cl; spill OF x240 to reg (rcx)
mov byte [ rsp + 0x1b8 ], r10b; spilling byte x225 to mem
movzx r10, byte [ rsp + 0x138 ]; load byte memx280 to register64
mov byte [ rsp + 0x1c0 ], bl; spilling byte x182 to mem
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r10, rbx; loading flag
adox r9, rax
mov r10, 0xffffffffffffffff ; moving imm to reg
mov rax, rdx; preserving value of x3 into a new reg
mov rdx, [ rsp + 0x158 ]; saving x279 in rdx.
mov byte [ rsp + 0x1c8 ], cl; spilling byte x240 to mem
mulx rbx, rcx, r10; x306, x305<- x279 * 0xffffffffffffffff
seto r10b; spill OF x282 to reg (r10)
mov [ rsp + 0x1d0 ], rbx; spilling x306 to mem
mov rbx, -0x2 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rcx, [ rsp + 0x100 ]
setc bl; spill CF x267 to reg (rbx)
mov byte [ rsp + 0x1d8 ], r10b; spilling byte x282 to mem
movzx r10, byte [ rsp + 0x120 ]; load byte memx323 to register64
clc;
mov [ rsp + 0x158 ], rdx; spilling x279 to mem
mov rdx, -0x1 ; moving imm to reg
adcx r10, rdx; loading flag
adcx r9, rcx
mov r10, [ rsi + 0x20 ]; load m64 x4 to register64
mov rdx, r10; x4 to rdx
mulx r10, rcx, [ r11 + 0x0 ]; x352, x351<- x4 * arg2[0]
mov [ rsp + 0x1e0 ], r10; spilling x352 to mem
setc r10b; spill CF x325 to reg (r10)
clc;
adcx rcx, r9
mov r9, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r9; 0xffffffffffffffff, swapping with x4, which is currently in rdx
mov byte [ rsp + 0x1e8 ], r10b; spilling byte x325 to mem
mov byte [ rsp + 0x1f0 ], bl; spilling byte x267 to mem
mulx r10, rbx, rcx; x395, x394<- x366 * 0xffffffffffffffff
seto dl; spill OF x310 to reg (rdx)
mov [ rsp + 0x1f8 ], r10; spilling x395 to mem
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, rcx
mov bl, dl; preserving value of x310 into a new reg
mov rdx, [ r11 + 0x28 ]; saving arg2[5] in rdx.
mov [ rsp + 0x200 ], rcx; spilling x366 to mem
mulx r10, rcx, r12; x11, x10<- x7 * arg2[5]
mov [ rsp + 0x208 ], r10; spilling x11 to mem
seto r10b; spill OF x410 to reg (r10)
mov byte [ rsp + 0x210 ], bl; spilling byte x310 to mem
movzx rbx, byte [ rsp + 0x140 ]; load byte memx29 to register64
mov [ rsp + 0x218 ], r9; spilling x4 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbx, r9; loading flag
adox rcx, [ rsp + 0x108 ]
mov rbx, 0x6cfc5fd681c52056 ; moving imm to reg
mov rdx, rbx; 0x6cfc5fd681c52056 to rdx
mulx rbx, r9, rbp; x38, x37<- x20 * 0x6cfc5fd681c52056
setc dl; spill CF x367 to reg (rdx)
mov [ rsp + 0x220 ], rbx; spilling x38 to mem
movzx rbx, byte [ rsp + 0x160 ]; load byte memx56 to register64
clc;
mov byte [ rsp + 0x228 ], r10b; spilling byte x410 to mem
mov r10, -0x1 ; moving imm to reg
adcx rbx, r10; loading flag
adcx r9, [ rsp + 0x128 ]
seto bl; spill OF x31 to reg (rbx)
movzx r10, byte [ rsp + 0x188 ]; load byte memx71 to register64
mov byte [ rsp + 0x230 ], dl; spilling byte x367 to mem
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
adox r10, rdx; loading flag
adox rcx, r9
mov rdx, r8; x1 to rdx
mulx r8, r10, [ r11 + 0x20 ]; x83, x82<- x1 * arg2[4]
setc r9b; spill CF x58 to reg (r9)
mov [ rsp + 0x238 ], r8; spilling x83 to mem
movzx r8, byte [ rsp + 0x170 ]; load byte memx97 to register64
clc;
mov byte [ rsp + 0x240 ], bl; spilling byte x31 to mem
mov rbx, -0x1 ; moving imm to reg
adcx r8, rbx; loading flag
adcx r10, [ rsp + 0x148 ]
setc r8b; spill CF x99 to reg (r8)
movzx rbx, byte [ rsp + 0x178 ]; load byte memx112 to register64
clc;
mov byte [ rsp + 0x248 ], r9b; spilling byte x58 to mem
mov r9, -0x1 ; moving imm to reg
adcx rbx, r9; loading flag
adcx rcx, r10
mov rbx, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, r14; x105, swapping with x1, which is currently in rdx
mulx r10, r9, rbx; x126, x125<- x105 * 0x7bc65c783158aea3
seto bl; spill OF x73 to reg (rbx)
mov [ rsp + 0x250 ], r10; spilling x126 to mem
movzx r10, byte [ rsp + 0x190 ]; load byte memx140 to register64
mov byte [ rsp + 0x258 ], r8b; spilling byte x99 to mem
mov r8, 0x0 ; moving imm to reg
dec r8; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r10, r8; loading flag
adox r9, [ rsp + 0x168 ]
seto r10b; spill OF x142 to reg (r10)
movzx r8, byte [ rsp + 0x1a0 ]; load byte memx155 to register64
mov byte [ rsp + 0x260 ], bl; spilling byte x73 to mem
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r8, rbx; loading flag
adox rcx, r9
xchg rdx, r15; x2, swapping with x105, which is currently in rdx
mulx r8, r9, [ r11 + 0x18 ]; x172, x171<- x2 * arg2[3]
setc bl; spill CF x114 to reg (rbx)
mov [ rsp + 0x268 ], r8; spilling x172 to mem
movzx r8, byte [ rsp + 0x1c0 ]; load byte memx182 to register64
clc;
mov byte [ rsp + 0x270 ], r10b; spilling byte x142 to mem
mov r10, -0x1 ; moving imm to reg
adcx r8, r10; loading flag
adcx r9, [ rsp + 0x180 ]
seto r8b; spill OF x157 to reg (r8)
movzx r10, byte [ rsp + 0x1a8 ]; load byte memx197 to register64
mov byte [ rsp + 0x278 ], bl; spilling byte x114 to mem
mov rbx, -0x1 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbx, -0x1 ; moving imm to reg
adox r10, rbx; loading flag
adox rcx, r9
mov r10, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, r10; 0xfdc1767ae2ffffff, swapping with x2, which is currently in rdx
mulx r9, rbx, r13; x215, x214<- x192 * 0xfdc1767ae2ffffff
setc dl; spill CF x184 to reg (rdx)
mov [ rsp + 0x280 ], r9; spilling x215 to mem
movzx r9, byte [ rsp + 0x1b8 ]; load byte memx225 to register64
clc;
mov byte [ rsp + 0x288 ], r8b; spilling byte x157 to mem
mov r8, -0x1 ; moving imm to reg
adcx r9, r8; loading flag
adcx rbx, [ rsp + 0x198 ]
seto r9b; spill OF x199 to reg (r9)
movzx r8, byte [ rsp + 0x1c8 ]; load byte memx240 to register64
mov byte [ rsp + 0x290 ], dl; spilling byte x184 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r8, rdx; loading flag
adox rcx, rbx
mov rdx, rax; x3 to rdx
mulx rax, r8, [ r11 + 0x10 ]; x261, x260<- x3 * arg2[2]
seto bl; spill OF x242 to reg (rbx)
mov [ rsp + 0x298 ], rax; spilling x261 to mem
movzx rax, byte [ rsp + 0x1f0 ]; load byte memx267 to register64
mov byte [ rsp + 0x2a0 ], r9b; spilling byte x199 to mem
mov r9, -0x1 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r9, -0x1 ; moving imm to reg
adox rax, r9; loading flag
adox r8, [ rsp + 0x1b0 ]
setc al; spill CF x227 to reg (rax)
movzx r9, byte [ rsp + 0x1d8 ]; load byte memx282 to register64
clc;
mov byte [ rsp + 0x2a8 ], bl; spilling byte x242 to mem
mov rbx, -0x1 ; moving imm to reg
adcx r9, rbx; loading flag
adcx rcx, r8
mov r9, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r9; 0xffffffffffffffff, swapping with x3, which is currently in rdx
mulx r8, rbx, [ rsp + 0x158 ]; x304, x303<- x279 * 0xffffffffffffffff
setc dl; spill CF x284 to reg (rdx)
mov [ rsp + 0x2b0 ], r8; spilling x304 to mem
movzx r8, byte [ rsp + 0x210 ]; load byte memx310 to register64
clc;
mov byte [ rsp + 0x2b8 ], al; spilling byte x227 to mem
mov rax, -0x1 ; moving imm to reg
adcx r8, rax; loading flag
adcx rbx, [ rsp + 0x1d0 ]
setc r8b; spill CF x312 to reg (r8)
movzx rax, byte [ rsp + 0x1e8 ]; load byte memx325 to register64
clc;
mov byte [ rsp + 0x2c0 ], dl; spilling byte x284 to mem
mov rdx, -0x1 ; moving imm to reg
adcx rax, rdx; loading flag
adcx rcx, rbx
mov rdx, [ rsp + 0x218 ]; x4 to rdx
mulx rax, rbx, [ r11 + 0x8 ]; x350, x349<- x4 * arg2[1]
mov [ rsp + 0x2c8 ], rax; spilling x350 to mem
setc al; spill CF x327 to reg (rax)
clc;
adcx rbx, [ rsp + 0x1e0 ]
mov byte [ rsp + 0x2d0 ], al; spilling byte x327 to mem
seto al; spill OF x269 to reg (rax)
mov byte [ rsp + 0x2d8 ], r8b; spilling byte x312 to mem
movzx r8, byte [ rsp + 0x230 ]; load byte memx367 to register64
mov [ rsp + 0x218 ], rdx; spilling x4 to mem
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
adox r8, rdx; loading flag
adox rcx, rbx
mov r8, 0xffffffffffffffff ; moving imm to reg
mov rdx, [ rsp + 0x200 ]; x366 to rdx
mov byte [ rsp + 0x2e0 ], al; spilling byte x269 to mem
mulx rbx, rax, r8; x393, x392<- x366 * 0xffffffffffffffff
setc r8b; spill CF x354 to reg (r8)
clc;
adcx rax, [ rsp + 0x1f8 ]
mov [ rsp + 0x2e8 ], rbx; spilling x393 to mem
seto bl; spill OF x369 to reg (rbx)
mov byte [ rsp + 0x2f0 ], r8b; spilling byte x354 to mem
movzx r8, byte [ rsp + 0x228 ]; load byte memx410 to register64
mov [ rsp + 0x200 ], rdx; spilling x366 to mem
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
adox r8, rdx; loading flag
adox rcx, rax
mov r8, [ rsi + 0x28 ]; load m64 x5 to register64
mov rdx, [ r11 + 0x0 ]; arg2[0] to rdx
mov byte [ rsp + 0x2f8 ], bl; spilling byte x369 to mem
mulx rax, rbx, r8; x439, x438<- x5 * arg2[0]
mov [ rsp + 0x300 ], rax; spilling x439 to mem
seto al; spill OF x412 to reg (rax)
mov [ rsp + 0x308 ], r8; spilling x5 to mem
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, rcx
mov rcx, 0xffffffffffffffff ; moving imm to reg
mov rdx, rbx; x453 to rdx
mulx rbx, r8, rcx; x482, x481<- x453 * 0xffffffffffffffff
mov rcx, rdx; preserving value of x453 into a new reg
mov rdx, [ r11 + 0x30 ]; saving arg2[6] in rdx.
mov [ rsp + 0x310 ], rbx; spilling x482 to mem
mulx r12, rbx, r12; x9, x8<- x7 * arg2[6]
mov [ rsp + 0x318 ], r12; spilling x9 to mem
seto r12b; spill OF x454 to reg (r12)
mov byte [ rsp + 0x320 ], al; spilling byte x412 to mem
mov rax, -0x2 ; moving imm to reg
inc rax; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, rcx
setc r8b; spill CF x397 to reg (r8)
movzx rax, byte [ rsp + 0x240 ]; load byte memx31 to register64
clc;
mov byte [ rsp + 0x328 ], r12b; spilling byte x454 to mem
mov r12, -0x1 ; moving imm to reg
adcx rax, r12; loading flag
adcx rbx, [ rsp + 0x208 ]
mov rax, 0x2341f27177344 ; moving imm to reg
mov rdx, rbp; x20 to rdx
mulx rdx, rbp, rax; x36, x35<- x20 * 0x2341f27177344
seto r12b; spill OF x497 to reg (r12)
movzx rax, byte [ rsp + 0x248 ]; load byte memx58 to register64
mov [ rsp + 0x330 ], rdx; spilling x36 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rax, rdx; loading flag
adox rbp, [ rsp + 0x220 ]
setc al; spill CF x33 to reg (rax)
movzx rdx, byte [ rsp + 0x260 ]; load byte memx73 to register64
clc;
mov byte [ rsp + 0x338 ], r12b; spilling byte x497 to mem
mov r12, -0x1 ; moving imm to reg
adcx rdx, r12; loading flag
adcx rbx, rbp
mov rdx, r14; x1 to rdx
mulx r14, rbp, [ r11 + 0x28 ]; x81, x80<- x1 * arg2[5]
seto r12b; spill OF x60 to reg (r12)
mov [ rsp + 0x340 ], r14; spilling x81 to mem
movzx r14, byte [ rsp + 0x258 ]; load byte memx99 to register64
mov byte [ rsp + 0x348 ], al; spilling byte x33 to mem
mov rax, -0x1 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rax, -0x1 ; moving imm to reg
adox r14, rax; loading flag
adox rbp, [ rsp + 0x238 ]
mov r14, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, r15; x105, swapping with x1, which is currently in rdx
mov byte [ rsp + 0x350 ], r12b; spilling byte x60 to mem
mulx rax, r12, r14; x124, x123<- x105 * 0x6cfc5fd681c52056
seto r14b; spill OF x101 to reg (r14)
mov [ rsp + 0x358 ], rax; spilling x124 to mem
movzx rax, byte [ rsp + 0x278 ]; load byte memx114 to register64
mov byte [ rsp + 0x360 ], r8b; spilling byte x397 to mem
mov r8, 0x0 ; moving imm to reg
dec r8; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rax, r8; loading flag
adox rbx, rbp
setc al; spill CF x75 to reg (rax)
movzx rbp, byte [ rsp + 0x270 ]; load byte memx142 to register64
clc;
adcx rbp, r8; loading flag
adcx r12, [ rsp + 0x250 ]
seto bpl; spill OF x116 to reg (rbp)
movzx r8, byte [ rsp + 0x288 ]; load byte memx157 to register64
mov byte [ rsp + 0x368 ], r14b; spilling byte x101 to mem
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r8, r14; loading flag
adox rbx, r12
mov r8, rdx; preserving value of x105 into a new reg
mov rdx, [ r11 + 0x20 ]; saving arg2[4] in rdx.
mulx r12, r14, r10; x170, x169<- x2 * arg2[4]
mov [ rsp + 0x370 ], r12; spilling x170 to mem
setc r12b; spill CF x144 to reg (r12)
mov byte [ rsp + 0x378 ], bpl; spilling byte x116 to mem
movzx rbp, byte [ rsp + 0x290 ]; load byte memx184 to register64
clc;
mov byte [ rsp + 0x380 ], al; spilling byte x75 to mem
mov rax, -0x1 ; moving imm to reg
adcx rbp, rax; loading flag
adcx r14, [ rsp + 0x268 ]
seto bpl; spill OF x159 to reg (rbp)
movzx rax, byte [ rsp + 0x2a0 ]; load byte memx199 to register64
mov byte [ rsp + 0x388 ], r12b; spilling byte x144 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
adox rax, r12; loading flag
adox rbx, r14
mov rax, 0x7bc65c783158aea3 ; moving imm to reg
mov rdx, r13; x192 to rdx
mulx r13, r14, rax; x213, x212<- x192 * 0x7bc65c783158aea3
seto r12b; spill OF x201 to reg (r12)
movzx rax, byte [ rsp + 0x2b8 ]; load byte memx227 to register64
mov [ rsp + 0x390 ], r13; spilling x213 to mem
mov r13, -0x1 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r13, -0x1 ; moving imm to reg
adox rax, r13; loading flag
adox r14, [ rsp + 0x280 ]
seto al; spill OF x229 to reg (rax)
movzx r13, byte [ rsp + 0x2a8 ]; load byte memx242 to register64
mov byte [ rsp + 0x398 ], r12b; spilling byte x201 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r13, r12; loading flag
adox rbx, r14
xchg rdx, r9; x3, swapping with x192, which is currently in rdx
mulx r13, r14, [ r11 + 0x18 ]; x259, x258<- x3 * arg2[3]
setc r12b; spill CF x186 to reg (r12)
mov [ rsp + 0x3a0 ], r13; spilling x259 to mem
movzx r13, byte [ rsp + 0x2e0 ]; load byte memx269 to register64
clc;
mov byte [ rsp + 0x3a8 ], al; spilling byte x229 to mem
mov rax, -0x1 ; moving imm to reg
adcx r13, rax; loading flag
adcx r14, [ rsp + 0x298 ]
setc r13b; spill CF x271 to reg (r13)
movzx rax, byte [ rsp + 0x2c0 ]; load byte memx284 to register64
clc;
mov byte [ rsp + 0x3b0 ], r12b; spilling byte x186 to mem
mov r12, -0x1 ; moving imm to reg
adcx rax, r12; loading flag
adcx rbx, r14
mov rax, 0xfdc1767ae2ffffff ; moving imm to reg
mov r14, rdx; preserving value of x3 into a new reg
mov rdx, [ rsp + 0x158 ]; saving x279 in rdx.
mov byte [ rsp + 0x3b8 ], r13b; spilling byte x271 to mem
mulx r12, r13, rax; x302, x301<- x279 * 0xfdc1767ae2ffffff
seto al; spill OF x244 to reg (rax)
mov [ rsp + 0x3c0 ], r12; spilling x302 to mem
movzx r12, byte [ rsp + 0x2d8 ]; load byte memx312 to register64
mov byte [ rsp + 0x3c8 ], bpl; spilling byte x159 to mem
mov rbp, 0x0 ; moving imm to reg
dec rbp; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r12, rbp; loading flag
adox r13, [ rsp + 0x2b0 ]
seto r12b; spill OF x314 to reg (r12)
movzx rbp, byte [ rsp + 0x2d0 ]; load byte memx327 to register64
mov byte [ rsp + 0x3d0 ], al; spilling byte x244 to mem
mov rax, 0x0 ; moving imm to reg
dec rax; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbp, rax; loading flag
adox rbx, r13
mov rbp, rdx; preserving value of x279 into a new reg
mov rdx, [ r11 + 0x10 ]; saving arg2[2] in rdx.
mulx r13, rax, [ rsp + 0x218 ]; x348, x347<- x4 * arg2[2]
mov [ rsp + 0x3d8 ], r13; spilling x348 to mem
seto r13b; spill OF x329 to reg (r13)
mov byte [ rsp + 0x3e0 ], r12b; spilling byte x314 to mem
movzx r12, byte [ rsp + 0x2f0 ]; load byte memx354 to register64
mov [ rsp + 0x3e8 ], rbx; spilling x328 to mem
mov rbx, -0x1 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbx, -0x1 ; moving imm to reg
adox r12, rbx; loading flag
adox rax, [ rsp + 0x2c8 ]
seto r12b; spill OF x356 to reg (r12)
movzx rbx, byte [ rsp + 0x2f8 ]; load byte memx369 to register64
mov byte [ rsp + 0x3f0 ], r13b; spilling byte x329 to mem
mov r13, -0x1 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r13, -0x1 ; moving imm to reg
adox rbx, r13; loading flag
adox rax, [ rsp + 0x3e8 ]
mov rbx, 0xffffffffffffffff ; moving imm to reg
mov rdx, rbx; 0xffffffffffffffff to rdx
mulx rbx, r13, [ rsp + 0x200 ]; x391, x390<- x366 * 0xffffffffffffffff
seto dl; spill OF x371 to reg (rdx)
mov [ rsp + 0x3f8 ], rbx; spilling x391 to mem
movzx rbx, byte [ rsp + 0x360 ]; load byte memx397 to register64
mov byte [ rsp + 0x400 ], r12b; spilling byte x356 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbx, r12; loading flag
adox r13, [ rsp + 0x2e8 ]
setc bl; spill CF x286 to reg (rbx)
movzx r12, byte [ rsp + 0x320 ]; load byte memx412 to register64
clc;
mov byte [ rsp + 0x408 ], dl; spilling byte x371 to mem
mov rdx, -0x1 ; moving imm to reg
adcx r12, rdx; loading flag
adcx rax, r13
mov rdx, [ r11 + 0x8 ]; arg2[1] to rdx
mulx r12, r13, [ rsp + 0x308 ]; x437, x436<- x5 * arg2[1]
mov [ rsp + 0x410 ], r12; spilling x437 to mem
setc r12b; spill CF x414 to reg (r12)
clc;
adcx r13, [ rsp + 0x300 ]
mov byte [ rsp + 0x418 ], r12b; spilling byte x414 to mem
setc r12b; spill CF x441 to reg (r12)
mov byte [ rsp + 0x420 ], bl; spilling byte x286 to mem
movzx rbx, byte [ rsp + 0x328 ]; load byte memx454 to register64
clc;
mov [ rsp + 0x428 ], rcx; spilling x453 to mem
mov rcx, -0x1 ; moving imm to reg
adcx rbx, rcx; loading flag
adcx rax, r13
mov rbx, 0xffffffffffffffff ; moving imm to reg
mov rdx, rbx; 0xffffffffffffffff to rdx
mulx rbx, r13, [ rsp + 0x428 ]; x480, x479<- x453 * 0xffffffffffffffff
seto cl; spill OF x399 to reg (rcx)
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, [ rsp + 0x310 ]
seto dl; spill OF x484 to reg (rdx)
mov [ rsp + 0x430 ], rbx; spilling x480 to mem
movzx rbx, byte [ rsp + 0x338 ]; load byte memx497 to register64
mov byte [ rsp + 0x438 ], r12b; spilling byte x441 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
adox rbx, r12; loading flag
adox rax, r13
mov bl, dl; preserving value of x484 into a new reg
mov rdx, [ r11 + 0x0 ]; saving arg2[0] in rdx.
mulx r13, r12, [ rsp + 0x8 ]; x526, x525<- x6 * arg2[0]
mov [ rsp + 0x440 ], r13; spilling x526 to mem
setc r13b; spill CF x456 to reg (r13)
clc;
adcx r12, rax
mov rax, 0xffffffffffffffff ; moving imm to reg
mov rdx, rax; 0xffffffffffffffff to rdx
mov byte [ rsp + 0x448 ], bl; spilling byte x484 to mem
mulx rax, rbx, r12; x569, x568<- x540 * 0xffffffffffffffff
mov byte [ rsp + 0x450 ], r13b; spilling byte x456 to mem
mov [ rsp + 0x458 ], rbx; spilling x568 to mem
mulx r13, rbx, r12; x567, x566<- x540 * 0xffffffffffffffff
seto dl; spill OF x499 to reg (rdx)
mov byte [ rsp + 0x460 ], cl; spilling byte x399 to mem
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, rax
mov rax, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r12; x540, swapping with x499, which is currently in rdx
mov [ rsp + 0x468 ], rbx; spilling x570 to mem
mulx rcx, rbx, rax; x565, x564<- x540 * 0xffffffffffffffff
adox rbx, r13
mov r13, 0xfdc1767ae2ffffff ; moving imm to reg
mov [ rsp + 0x470 ], rbx; spilling x572 to mem
mulx rax, rbx, r13; x563, x562<- x540 * 0xfdc1767ae2ffffff
adox rbx, rcx
mov rcx, 0x7bc65c783158aea3 ; moving imm to reg
mov [ rsp + 0x478 ], rbx; spilling x574 to mem
mulx r13, rbx, rcx; x561, x560<- x540 * 0x7bc65c783158aea3
adox rbx, rax
mov rax, 0x6cfc5fd681c52056 ; moving imm to reg
mov [ rsp + 0x480 ], rbx; spilling x576 to mem
mulx rcx, rbx, rax; x559, x558<- x540 * 0x6cfc5fd681c52056
adox rbx, r13
mov r13, 0x2341f27177344 ; moving imm to reg
mov [ rsp + 0x488 ], rbx; spilling x578 to mem
mulx rax, rbx, r13; x557, x556<- x540 * 0x2341f27177344
adox rbx, rcx
mov rcx, 0x0 ; moving imm to reg
adox rax, rcx
movzx rcx, byte [ rsp + 0x350 ]; x61, copying x60 here, cause x60 is needed in a reg for other than x61, namely all: , x61, size: 1
mov r13, [ rsp + 0x330 ]; load m64 x36 to register64
lea rcx, [ rcx + r13 ]; r8/64 + m8
mov r13, 0x2341f27177344 ; moving imm to reg
xchg rdx, r8; x105, swapping with x540, which is currently in rdx
mov [ rsp + 0x490 ], rax; spilling x582 to mem
mulx rdx, rax, r13; x122, x121<- x105 * 0x2341f27177344
movzx r13, byte [ rsp + 0x348 ]; x34, copying x33 here, cause x33 is needed in a reg for other than x34, namely all: , x34, size: 1
mov [ rsp + 0x498 ], rbx; spilling x580 to mem
mov rbx, [ rsp + 0x318 ]; load m64 x9 to register64
lea r13, [ r13 + rbx ]; r8/64 + m8
movzx rbx, byte [ rsp + 0x388 ]; load byte memx144 to register64
mov byte [ rsp + 0x4a0 ], r12b; spilling byte x499 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbx, r12; loading flag
adox rax, [ rsp + 0x358 ]
mov rbx, 0x0 ; moving imm to reg
adox rdx, rbx
xchg rdx, r15; x1, swapping with x147, which is currently in rdx
mulx rdx, rbx, [ r11 + 0x30 ]; x79, x78<- x1 * arg2[6]
movzx r12, byte [ rsp + 0x380 ]; load byte memx75 to register64
mov [ rsp + 0x4a8 ], r15; spilling x147 to mem
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r15, -0x1 ; moving imm to reg
adox r12, r15; loading flag
adox r13, rcx
seto r12b; spill OF x77 to reg (r12)
movzx rcx, byte [ rsp + 0x368 ]; load byte memx101 to register64
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
adox rcx, r15; loading flag
adox rbx, [ rsp + 0x340 ]
seto cl; spill OF x103 to reg (rcx)
movzx r15, byte [ rsp + 0x378 ]; load byte memx116 to register64
mov byte [ rsp + 0x4b0 ], r12b; spilling byte x77 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, r12; loading flag
adox r13, rbx
xchg rdx, r10; x2, swapping with x79, which is currently in rdx
mulx r15, rbx, [ r11 + 0x28 ]; x168, x167<- x2 * arg2[5]
seto r12b; spill OF x118 to reg (r12)
mov [ rsp + 0x4b8 ], r15; spilling x168 to mem
movzx r15, byte [ rsp + 0x3c8 ]; load byte memx159 to register64
mov [ rsp + 0x4c0 ], r10; spilling x79 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, r10; loading flag
adox r13, rax
setc r15b; spill CF x541 to reg (r15)
movzx rax, byte [ rsp + 0x3b0 ]; load byte memx186 to register64
clc;
adcx rax, r10; loading flag
adcx rbx, [ rsp + 0x370 ]
setc al; spill CF x188 to reg (rax)
movzx r10, byte [ rsp + 0x398 ]; load byte memx201 to register64
clc;
mov byte [ rsp + 0x4c8 ], r15b; spilling byte x541 to mem
mov r15, -0x1 ; moving imm to reg
adcx r10, r15; loading flag
adcx r13, rbx
mov r10, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, r9; x192, swapping with x2, which is currently in rdx
mulx rbx, r15, r10; x211, x210<- x192 * 0x6cfc5fd681c52056
seto r10b; spill OF x161 to reg (r10)
mov [ rsp + 0x4d0 ], rbx; spilling x211 to mem
movzx rbx, byte [ rsp + 0x3a8 ]; load byte memx229 to register64
mov byte [ rsp + 0x4d8 ], al; spilling byte x188 to mem
mov rax, -0x1 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rax, -0x1 ; moving imm to reg
adox rbx, rax; loading flag
adox r15, [ rsp + 0x390 ]
seto bl; spill OF x231 to reg (rbx)
movzx rax, byte [ rsp + 0x3d0 ]; load byte memx244 to register64
mov byte [ rsp + 0x4e0 ], r10b; spilling byte x161 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rax, r10; loading flag
adox r13, r15
mov rax, rdx; preserving value of x192 into a new reg
mov rdx, [ r11 + 0x20 ]; saving arg2[4] in rdx.
mulx r15, r10, r14; x257, x256<- x3 * arg2[4]
mov [ rsp + 0x4e8 ], r15; spilling x257 to mem
seto r15b; spill OF x246 to reg (r15)
mov byte [ rsp + 0x4f0 ], bl; spilling byte x231 to mem
movzx rbx, byte [ rsp + 0x3b8 ]; load byte memx271 to register64
mov byte [ rsp + 0x4f8 ], r12b; spilling byte x118 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
adox rbx, r12; loading flag
adox r10, [ rsp + 0x3a0 ]
mov rbx, 0x7bc65c783158aea3 ; moving imm to reg
mov rdx, rbx; 0x7bc65c783158aea3 to rdx
mulx rbx, r12, rbp; x300, x299<- x279 * 0x7bc65c783158aea3
setc dl; spill CF x203 to reg (rdx)
mov [ rsp + 0x500 ], rbx; spilling x300 to mem
movzx rbx, byte [ rsp + 0x3e0 ]; load byte memx314 to register64
clc;
mov byte [ rsp + 0x508 ], r15b; spilling byte x246 to mem
mov r15, -0x1 ; moving imm to reg
adcx rbx, r15; loading flag
adcx r12, [ rsp + 0x3c0 ]
setc bl; spill CF x316 to reg (rbx)
movzx r15, byte [ rsp + 0x420 ]; load byte memx286 to register64
clc;
mov byte [ rsp + 0x510 ], dl; spilling byte x203 to mem
mov rdx, -0x1 ; moving imm to reg
adcx r15, rdx; loading flag
adcx r13, r10
setc r15b; spill CF x288 to reg (r15)
movzx r10, byte [ rsp + 0x3f0 ]; load byte memx329 to register64
clc;
adcx r10, rdx; loading flag
adcx r13, r12
mov rdx, [ rsp + 0x218 ]; x4 to rdx
mulx r10, r12, [ r11 + 0x18 ]; x346, x345<- x4 * arg2[3]
mov [ rsp + 0x518 ], r10; spilling x346 to mem
setc r10b; spill CF x331 to reg (r10)
mov byte [ rsp + 0x520 ], bl; spilling byte x316 to mem
movzx rbx, byte [ rsp + 0x400 ]; load byte memx356 to register64
clc;
mov byte [ rsp + 0x528 ], r15b; spilling byte x288 to mem
mov r15, -0x1 ; moving imm to reg
adcx rbx, r15; loading flag
adcx r12, [ rsp + 0x3d8 ]
setc bl; spill CF x358 to reg (rbx)
movzx r15, byte [ rsp + 0x408 ]; load byte memx371 to register64
clc;
mov byte [ rsp + 0x530 ], r10b; spilling byte x331 to mem
mov r10, -0x1 ; moving imm to reg
adcx r15, r10; loading flag
adcx r13, r12
mov r15, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, r15; 0xfdc1767ae2ffffff, swapping with x4, which is currently in rdx
mulx r12, r10, [ rsp + 0x200 ]; x389, x388<- x366 * 0xfdc1767ae2ffffff
seto dl; spill OF x273 to reg (rdx)
mov [ rsp + 0x538 ], r12; spilling x389 to mem
movzx r12, byte [ rsp + 0x460 ]; load byte memx399 to register64
mov byte [ rsp + 0x540 ], bl; spilling byte x358 to mem
mov rbx, -0x1 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbx, -0x1 ; moving imm to reg
adox r12, rbx; loading flag
adox r10, [ rsp + 0x3f8 ]
movzx r12, cl; x104, copying x103 here, cause x103 is needed in a reg for other than x104, namely all: , x104, size: 1
mov rbx, [ rsp + 0x4c0 ]; load m64 x79 to register64
lea r12, [ r12 + rbx ]; r8/64 + m8
seto bl; spill OF x401 to reg (rbx)
movzx rcx, byte [ rsp + 0x418 ]; load byte memx414 to register64
mov byte [ rsp + 0x548 ], dl; spilling byte x273 to mem
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
adox rcx, rdx; loading flag
adox r13, r10
seto cl; spill OF x416 to reg (rcx)
movzx r10, byte [ rsp + 0x4f8 ]; load byte memx118 to register64
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
mov [ rsp + 0x550 ], r13; spilling x415 to mem
movzx r13, byte [ rsp + 0x4b0 ]; load byte memx77 to register64
adox r10, rdx; loading flag
adox r12, r13
setc r13b; spill CF x373 to reg (r13)
movzx r10, byte [ rsp + 0x4e0 ]; load byte memx161 to register64
clc;
adcx r10, rdx; loading flag
adcx r12, [ rsp + 0x4a8 ]
mov rdx, [ r11 + 0x30 ]; arg2[6] to rdx
mulx r9, r10, r9; x166, x165<- x2 * arg2[6]
mov [ rsp + 0x558 ], r9; spilling x166 to mem
setc r9b; spill CF x163 to reg (r9)
mov byte [ rsp + 0x560 ], cl; spilling byte x416 to mem
movzx rcx, byte [ rsp + 0x4d8 ]; load byte memx188 to register64
clc;
mov byte [ rsp + 0x568 ], bl; spilling byte x401 to mem
mov rbx, -0x1 ; moving imm to reg
adcx rcx, rbx; loading flag
adcx r10, [ rsp + 0x4b8 ]
setc cl; spill CF x190 to reg (rcx)
movzx rbx, byte [ rsp + 0x510 ]; load byte memx203 to register64
clc;
mov byte [ rsp + 0x570 ], r9b; spilling byte x163 to mem
mov r9, -0x1 ; moving imm to reg
adcx rbx, r9; loading flag
adcx r12, r10
mov rbx, 0x2341f27177344 ; moving imm to reg
mov rdx, rax; x192 to rdx
mulx rdx, rax, rbx; x209, x208<- x192 * 0x2341f27177344
seto r10b; spill OF x120 to reg (r10)
movzx r9, byte [ rsp + 0x4f0 ]; load byte memx231 to register64
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r9, rbx; loading flag
adox rax, [ rsp + 0x4d0 ]
setc r9b; spill CF x205 to reg (r9)
movzx rbx, byte [ rsp + 0x508 ]; load byte memx246 to register64
clc;
mov [ rsp + 0x578 ], rdx; spilling x209 to mem
mov rdx, -0x1 ; moving imm to reg
adcx rbx, rdx; loading flag
adcx r12, rax
mov rdx, r14; x3 to rdx
mulx r14, rbx, [ r11 + 0x28 ]; x255, x254<- x3 * arg2[5]
setc al; spill CF x248 to reg (rax)
mov [ rsp + 0x580 ], r14; spilling x255 to mem
movzx r14, byte [ rsp + 0x548 ]; load byte memx273 to register64
clc;
mov byte [ rsp + 0x588 ], r9b; spilling byte x205 to mem
mov r9, -0x1 ; moving imm to reg
adcx r14, r9; loading flag
adcx rbx, [ rsp + 0x4e8 ]
seto r14b; spill OF x233 to reg (r14)
movzx r9, byte [ rsp + 0x528 ]; load byte memx288 to register64
mov byte [ rsp + 0x590 ], al; spilling byte x248 to mem
mov rax, -0x1 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rax, -0x1 ; moving imm to reg
adox r9, rax; loading flag
adox r12, rbx
mov r9, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, rbp; x279, swapping with x3, which is currently in rdx
mulx rbx, rax, r9; x298, x297<- x279 * 0x6cfc5fd681c52056
seto r9b; spill OF x290 to reg (r9)
mov [ rsp + 0x598 ], rbx; spilling x298 to mem
movzx rbx, byte [ rsp + 0x520 ]; load byte memx316 to register64
mov byte [ rsp + 0x5a0 ], r14b; spilling byte x233 to mem
mov r14, -0x1 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r14, -0x1 ; moving imm to reg
adox rbx, r14; loading flag
adox rax, [ rsp + 0x500 ]
seto bl; spill OF x318 to reg (rbx)
movzx r14, byte [ rsp + 0x530 ]; load byte memx331 to register64
mov byte [ rsp + 0x5a8 ], r9b; spilling byte x290 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r14, r9; loading flag
adox r12, rax
mov r14, rdx; preserving value of x279 into a new reg
mov rdx, [ r11 + 0x20 ]; saving arg2[4] in rdx.
mulx rax, r9, r15; x344, x343<- x4 * arg2[4]
mov [ rsp + 0x5b0 ], rax; spilling x344 to mem
seto al; spill OF x333 to reg (rax)
mov byte [ rsp + 0x5b8 ], bl; spilling byte x318 to mem
movzx rbx, byte [ rsp + 0x540 ]; load byte memx358 to register64
mov byte [ rsp + 0x5c0 ], cl; spilling byte x190 to mem
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbx, rcx; loading flag
adox r9, [ rsp + 0x518 ]
seto bl; spill OF x360 to reg (rbx)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rcx, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, rcx; loading flag
adox r12, r9
mov r13, 0x7bc65c783158aea3 ; moving imm to reg
mov rdx, r13; 0x7bc65c783158aea3 to rdx
mulx r13, r9, [ rsp + 0x200 ]; x387, x386<- x366 * 0x7bc65c783158aea3
seto cl; spill OF x375 to reg (rcx)
movzx rdx, byte [ rsp + 0x568 ]; load byte memx401 to register64
mov [ rsp + 0x5c8 ], r13; spilling x387 to mem
mov r13, -0x1 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r13, -0x1 ; moving imm to reg
adox rdx, r13; loading flag
adox r9, [ rsp + 0x538 ]
movzx rdx, r10b; x164, copying x120 here, cause x120 is needed in a reg for other than x164, namely all: , x164, size: 1
movzx r13, byte [ rsp + 0x570 ]; load byte memx163 to register64
lea rdx, [ rdx + r13 ]; r64+m8
seto r10b; spill OF x403 to reg (r10)
movzx r13, byte [ rsp + 0x560 ]; load byte memx416 to register64
mov byte [ rsp + 0x5d0 ], cl; spilling byte x375 to mem
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r13, rcx; loading flag
adox r12, r9
movzx r13, byte [ rsp + 0x5c0 ]; x191, copying x190 here, cause x190 is needed in a reg for other than x191, namely all: , x191, size: 1
mov r9, [ rsp + 0x558 ]; load m64 x166 to register64
lea r13, [ r13 + r9 ]; r8/64 + m8
movzx r9, byte [ rsp + 0x5a0 ]; x234, copying x233 here, cause x233 is needed in a reg for other than x234, namely all: , x234, size: 1
mov rcx, [ rsp + 0x578 ]; load m64 x209 to register64
lea r9, [ r9 + rcx ]; r8/64 + m8
setc cl; spill CF x275 to reg (rcx)
mov [ rsp + 0x5d8 ], r12; spilling x417 to mem
movzx r12, byte [ rsp + 0x588 ]; load byte memx205 to register64
clc;
mov byte [ rsp + 0x5e0 ], r10b; spilling byte x403 to mem
mov r10, -0x1 ; moving imm to reg
adcx r12, r10; loading flag
adcx rdx, r13
mov r12, rdx; preserving value of x206 into a new reg
mov rdx, [ r11 + 0x30 ]; saving arg2[6] in rdx.
mulx rbp, r13, rbp; x253, x252<- x3 * arg2[6]
setc r10b; spill CF x207 to reg (r10)
mov [ rsp + 0x5e8 ], rbp; spilling x253 to mem
movzx rbp, byte [ rsp + 0x590 ]; load byte memx248 to register64
clc;
mov byte [ rsp + 0x5f0 ], bl; spilling byte x360 to mem
mov rbx, -0x1 ; moving imm to reg
adcx rbp, rbx; loading flag
adcx r12, r9
setc bpl; spill CF x250 to reg (rbp)
clc;
movzx rcx, cl
adcx rcx, rbx; loading flag
adcx r13, [ rsp + 0x580 ]
setc cl; spill CF x277 to reg (rcx)
movzx r9, byte [ rsp + 0x5a8 ]; load byte memx290 to register64
clc;
adcx r9, rbx; loading flag
adcx r12, r13
mov r9, 0x2341f27177344 ; moving imm to reg
mov rdx, r9; 0x2341f27177344 to rdx
mulx r14, r9, r14; x296, x295<- x279 * 0x2341f27177344
seto r13b; spill OF x418 to reg (r13)
movzx rbx, byte [ rsp + 0x5b8 ]; load byte memx318 to register64
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbx, rdx; loading flag
adox r9, [ rsp + 0x598 ]
seto bl; spill OF x320 to reg (rbx)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
movzx rax, al
adox rax, rdx; loading flag
adox r12, r9
mov rdx, r15; x4 to rdx
mulx r15, rax, [ r11 + 0x28 ]; x342, x341<- x4 * arg2[5]
setc r9b; spill CF x292 to reg (r9)
mov [ rsp + 0x5f8 ], r15; spilling x342 to mem
movzx r15, byte [ rsp + 0x5f0 ]; load byte memx360 to register64
clc;
mov [ rsp + 0x600 ], r14; spilling x296 to mem
mov r14, -0x1 ; moving imm to reg
adcx r15, r14; loading flag
adcx rax, [ rsp + 0x5b0 ]
seto r15b; spill OF x335 to reg (r15)
movzx r14, byte [ rsp + 0x5d0 ]; load byte memx375 to register64
mov byte [ rsp + 0x608 ], r9b; spilling byte x292 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r14, r9; loading flag
adox r12, rax
mov r14, 0x6cfc5fd681c52056 ; moving imm to reg
mov rax, rdx; preserving value of x4 into a new reg
mov rdx, [ rsp + 0x200 ]; saving x366 in rdx.
mov byte [ rsp + 0x610 ], r15b; spilling byte x335 to mem
mulx r9, r15, r14; x385, x384<- x366 * 0x6cfc5fd681c52056
seto r14b; spill OF x377 to reg (r14)
mov [ rsp + 0x618 ], r9; spilling x385 to mem
movzx r9, byte [ rsp + 0x5e0 ]; load byte memx403 to register64
mov byte [ rsp + 0x620 ], bl; spilling byte x320 to mem
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r9, rbx; loading flag
adox r15, [ rsp + 0x5c8 ]
seto r9b; spill OF x405 to reg (r9)
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, rbx; loading flag
adox r12, r15
movzx r13, bpl; x251, copying x250 here, cause x250 is needed in a reg for other than x251, namely all: , x251, size: 1
movzx r10, r10b
lea r13, [ r13 + r10 ]
movzx r10, cl; x278, copying x277 here, cause x277 is needed in a reg for other than x278, namely all: , x278, size: 1
mov rbp, [ rsp + 0x5e8 ]; load m64 x253 to register64
lea r10, [ r10 + rbp ]; r8/64 + m8
movzx rbp, byte [ rsp + 0x620 ]; x321, copying x320 here, cause x320 is needed in a reg for other than x321, namely all: , x321, size: 1
mov rcx, [ rsp + 0x600 ]; load m64 x296 to register64
lea rbp, [ rbp + rcx ]; r8/64 + m8
seto cl; spill OF x420 to reg (rcx)
movzx r15, byte [ rsp + 0x608 ]; load byte memx292 to register64
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
adox r15, rbx; loading flag
adox r13, r10
seto r15b; spill OF x294 to reg (r15)
movzx r10, byte [ rsp + 0x610 ]; load byte memx335 to register64
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
adox r10, rbx; loading flag
adox r13, rbp
xchg rdx, rax; x4, swapping with x366, which is currently in rdx
mulx rdx, r10, [ r11 + 0x30 ]; x340, x339<- x4 * arg2[6]
mov rbp, [ rsp + 0x5f8 ]; x363, copying x342 here, cause x342 is needed in a reg for other than x363, namely all: , x363--x364, size: 1
adcx rbp, r10
mov r10, 0x2341f27177344 ; moving imm to reg
xchg rdx, rax; x366, swapping with x340, which is currently in rdx
mulx rdx, rbx, r10; x383, x382<- x366 * 0x2341f27177344
seto r10b; spill OF x337 to reg (r10)
mov [ rsp + 0x628 ], r12; spilling x419 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, r12; loading flag
adox r13, rbp
seto r14b; spill OF x379 to reg (r14)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, rbp; loading flag
adox rbx, [ rsp + 0x618 ]
seto r9b; spill OF x407 to reg (r9)
dec r12; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx rcx, cl
adox rcx, r12; loading flag
adox r13, rbx
mov rbp, 0x0 ; moving imm to reg
adcx rax, rbp
movzx rcx, r10b; x338, copying x337 here, cause x337 is needed in a reg for other than x338, namely all: , x338, size: 1
movzx r15, r15b
lea rcx, [ rcx + r15 ]
clc;
movzx r14, r14b
adcx r14, r12; loading flag
adcx rcx, rax
movzx r15, r9b; x408, copying x407 here, cause x407 is needed in a reg for other than x408, namely all: , x408, size: 1
lea r15, [ r15 + rdx ]
adox r15, rcx
seto r10b; spill OF x425 to reg (r10)
adc r10b, 0x0
movzx r10, r10b
adox r8, [ rsp + 0x458 ]
mov rdx, [ rsp + 0x308 ]; x5 to rdx
mulx r8, r14, [ r11 + 0x10 ]; x435, x434<- x5 * arg2[2]
movzx rbx, byte [ rsp + 0x438 ]; load byte memx441 to register64
adcx rbx, r12; loading flag
adcx r14, [ rsp + 0x410 ]
mov rbx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbx; 0xffffffffffffffff, swapping with x5, which is currently in rdx
mulx r9, rax, [ rsp + 0x428 ]; x478, x477<- x453 * 0xffffffffffffffff
setc cl; spill CF x443 to reg (rcx)
movzx rbp, byte [ rsp + 0x450 ]; load byte memx456 to register64
clc;
adcx rbp, r12; loading flag
adcx r14, [ rsp + 0x550 ]
setc bpl; spill CF x458 to reg (rbp)
movzx r12, byte [ rsp + 0x448 ]; load byte memx484 to register64
clc;
mov rdx, -0x1 ; moving imm to reg
adcx r12, rdx; loading flag
adcx rax, [ rsp + 0x430 ]
setc r12b; spill CF x486 to reg (r12)
movzx rdx, byte [ rsp + 0x4a0 ]; load byte memx499 to register64
clc;
mov byte [ rsp + 0x630 ], r10b; spilling byte x425 to mem
mov r10, -0x1 ; moving imm to reg
adcx rdx, r10; loading flag
adcx r14, rax
mov rdx, [ rsp + 0x8 ]; x6 to rdx
mulx rax, r10, [ r11 + 0x8 ]; x524, x523<- x6 * arg2[1]
mov [ rsp + 0x638 ], r15; spilling x423 to mem
seto r15b; spill OF x584 to reg (r15)
mov [ rsp + 0x640 ], r13; spilling x421 to mem
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r10, [ rsp + 0x440 ]
setc r13b; spill CF x501 to reg (r13)
mov [ rsp + 0x648 ], rax; spilling x524 to mem
movzx rax, byte [ rsp + 0x4c8 ]; load byte memx541 to register64
clc;
mov [ rsp + 0x650 ], r9; spilling x478 to mem
mov r9, -0x1 ; moving imm to reg
adcx rax, r9; loading flag
adcx r14, r10
seto al; spill OF x528 to reg (rax)
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r10, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, r10; loading flag
adox r14, [ rsp + 0x468 ]
setc r15b; spill CF x543 to reg (r15)
seto r10b; spill OF x586 to reg (r10)
mov byte [ rsp + 0x658 ], al; spilling byte x528 to mem
mov rax, r14; x600, copying x585 here, cause x585 is needed in a reg for other than x600, namely all: , x616, x600--x601, size: 2
mov byte [ rsp + 0x660 ], r13b; spilling byte x501 to mem
mov r13, 0xffffffffffffffff ; moving imm to reg
sub rax, r13
mov r9, rdx; preserving value of x6 into a new reg
mov rdx, [ r11 + 0x18 ]; saving arg2[3] in rdx.
mov [ rsp + 0x668 ], rax; spilling x600 to mem
mulx r13, rax, rbx; x433, x432<- x5 * arg2[3]
mov [ rsp + 0x670 ], r13; spilling x433 to mem
mov r13, -0x1 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r13, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r13; loading flag
adox r8, rax
setc cl; spill CF x601 to reg (rcx)
clc;
movzx rbp, bpl
adcx rbp, r13; loading flag
adcx r8, [ rsp + 0x5d8 ]
mov rbp, 0xfdc1767ae2ffffff ; moving imm to reg
mov rdx, [ rsp + 0x428 ]; x453 to rdx
mulx rax, r13, rbp; x476, x475<- x453 * 0xfdc1767ae2ffffff
seto bpl; spill OF x445 to reg (rbp)
mov [ rsp + 0x678 ], rax; spilling x476 to mem
mov rax, -0x1 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rax, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, rax; loading flag
adox r13, [ rsp + 0x650 ]
xchg rdx, r9; x6, swapping with x453, which is currently in rdx
mulx r12, rax, [ r11 + 0x10 ]; x522, x521<- x6 * arg2[2]
mov [ rsp + 0x680 ], r12; spilling x522 to mem
seto r12b; spill OF x488 to reg (r12)
mov byte [ rsp + 0x688 ], bpl; spilling byte x445 to mem
movzx rbp, byte [ rsp + 0x660 ]; load byte memx501 to register64
mov byte [ rsp + 0x690 ], cl; spilling byte x601 to mem
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbp, rcx; loading flag
adox r8, r13
setc bpl; spill CF x460 to reg (rbp)
movzx r13, byte [ rsp + 0x658 ]; load byte memx528 to register64
clc;
adcx r13, rcx; loading flag
adcx rax, [ rsp + 0x648 ]
setc r13b; spill CF x530 to reg (r13)
clc;
movzx r15, r15b
adcx r15, rcx; loading flag
adcx r8, rax
setc r15b; spill CF x545 to reg (r15)
clc;
movzx r10, r10b
adcx r10, rcx; loading flag
adcx r8, [ rsp + 0x470 ]
xchg rdx, rbx; x5, swapping with x6, which is currently in rdx
mulx r10, rax, [ r11 + 0x20 ]; x431, x430<- x5 * arg2[4]
setc cl; spill CF x588 to reg (rcx)
mov [ rsp + 0x698 ], r10; spilling x431 to mem
seto r10b; spill OF x503 to reg (r10)
mov byte [ rsp + 0x6a0 ], r15b; spilling byte x545 to mem
movzx r15, byte [ rsp + 0x690 ]; x601, copying x601 here, cause x601 is needed in a reg for other than x601, namely all: , x602--x603, size: 1
add r15, -0x1
mov r15, r8; x602, copying x587 here, cause x587 is needed in a reg for other than x602, namely all: , x617, x602--x603, size: 2
mov byte [ rsp + 0x6a8 ], r13b; spilling byte x530 to mem
mov r13, 0xffffffffffffffff ; moving imm to reg
sbb r15, r13
movzx r13, byte [ rsp + 0x688 ]; load byte memx445 to register64
mov [ rsp + 0x6b0 ], r15; spilling x602 to mem
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r15, -0x1 ; moving imm to reg
adox r13, r15; loading flag
adox rax, [ rsp + 0x670 ]
seto r13b; spill OF x447 to reg (r13)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, r15; loading flag
adox rax, [ rsp + 0x628 ]
mov rbp, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, rbp; 0x7bc65c783158aea3, swapping with x5, which is currently in rdx
mov byte [ rsp + 0x6b8 ], r13b; spilling byte x447 to mem
mulx r15, r13, r9; x474, x473<- x453 * 0x7bc65c783158aea3
seto dl; spill OF x462 to reg (rdx)
mov [ rsp + 0x6c0 ], r15; spilling x474 to mem
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r15, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, r15; loading flag
adox r13, [ rsp + 0x678 ]
seto r12b; spill OF x490 to reg (r12)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
movzx r10, r10b
adox r10, r15; loading flag
adox rax, r13
mov r10b, dl; preserving value of x462 into a new reg
mov rdx, [ r11 + 0x18 ]; saving arg2[3] in rdx.
mulx r13, r15, rbx; x520, x519<- x6 * arg2[3]
mov [ rsp + 0x6c8 ], r13; spilling x520 to mem
seto r13b; spill OF x505 to reg (r13)
mov byte [ rsp + 0x6d0 ], r12b; spilling byte x490 to mem
movzx r12, byte [ rsp + 0x6a8 ]; load byte memx530 to register64
mov byte [ rsp + 0x6d8 ], r10b; spilling byte x462 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r12, r10; loading flag
adox r15, [ rsp + 0x680 ]
setc r12b; spill CF x603 to reg (r12)
movzx r10, byte [ rsp + 0x6a0 ]; load byte memx545 to register64
clc;
mov byte [ rsp + 0x6e0 ], r13b; spilling byte x505 to mem
mov r13, -0x1 ; moving imm to reg
adcx r10, r13; loading flag
adcx rax, r15
seto r10b; spill OF x532 to reg (r10)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r15; loading flag
adox rax, [ rsp + 0x478 ]
setc cl; spill CF x547 to reg (rcx)
seto r13b; spill OF x590 to reg (r13)
movzx r15, r12b; x603, copying x603 here, cause x603 is needed in a reg for other than x603, namely all: , x604--x605, size: 1
add r15, -0x1
mov r12, rax; x604, copying x589 here, cause x589 is needed in a reg for other than x604, namely all: , x604--x605, x618, size: 2
mov r15, 0xffffffffffffffff ; moving imm to reg
sbb r12, r15
mov rdx, rbp; x5 to rdx
mulx rbp, r15, [ r11 + 0x28 ]; x429, x428<- x5 * arg2[5]
mov [ rsp + 0x6e8 ], r12; spilling x604 to mem
movzx r12, byte [ rsp + 0x6b8 ]; load byte memx447 to register64
mov [ rsp + 0x6f0 ], rbp; spilling x429 to mem
mov rbp, 0x0 ; moving imm to reg
dec rbp; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r12, rbp; loading flag
adox r15, [ rsp + 0x698 ]
seto r12b; spill OF x449 to reg (r12)
movzx rbp, byte [ rsp + 0x6d8 ]; load byte memx462 to register64
mov byte [ rsp + 0x6f8 ], r13b; spilling byte x590 to mem
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbp, r13; loading flag
adox r15, [ rsp + 0x640 ]
mov rbp, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, rbp; 0x6cfc5fd681c52056, swapping with x5, which is currently in rdx
mov byte [ rsp + 0x700 ], r12b; spilling byte x449 to mem
mulx r13, r12, r9; x472, x471<- x453 * 0x6cfc5fd681c52056
seto dl; spill OF x464 to reg (rdx)
mov [ rsp + 0x708 ], r13; spilling x472 to mem
movzx r13, byte [ rsp + 0x6d0 ]; load byte memx490 to register64
mov byte [ rsp + 0x710 ], cl; spilling byte x547 to mem
mov rcx, -0x1 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rcx, -0x1 ; moving imm to reg
adox r13, rcx; loading flag
adox r12, [ rsp + 0x6c0 ]
xchg rdx, rbx; x6, swapping with x464, which is currently in rdx
mulx r13, rcx, [ r11 + 0x20 ]; x518, x517<- x6 * arg2[4]
mov [ rsp + 0x718 ], r13; spilling x518 to mem
seto r13b; spill OF x492 to reg (r13)
mov byte [ rsp + 0x720 ], bl; spilling byte x464 to mem
movzx rbx, byte [ rsp + 0x6e0 ]; load byte memx505 to register64
mov [ rsp + 0x728 ], rcx; spilling x517 to mem
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbx, rcx; loading flag
adox r15, r12
mov rbx, [ rsp + 0x728 ]; load m64 x517 to register64
setc r12b; spill CF x605 to reg (r12)
clc;
movzx r10, r10b
adcx r10, rcx; loading flag
adcx rbx, [ rsp + 0x6c8 ]
seto r10b; spill OF x507 to reg (r10)
movzx rcx, byte [ rsp + 0x710 ]; load byte memx547 to register64
mov byte [ rsp + 0x730 ], r13b; spilling byte x492 to mem
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rcx, r13; loading flag
adox r15, rbx
seto cl; spill OF x549 to reg (rcx)
movzx rbx, byte [ rsp + 0x6f8 ]; load byte memx590 to register64
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
adox rbx, r13; loading flag
adox r15, [ rsp + 0x480 ]
setc bl; spill CF x534 to reg (rbx)
seto r13b; spill OF x592 to reg (r13)
mov byte [ rsp + 0x738 ], cl; spilling byte x549 to mem
movzx rcx, r12b; x605, copying x605 here, cause x605 is needed in a reg for other than x605, namely all: , x606--x607, size: 1
add rcx, -0x1
mov r12, r15; x606, copying x591 here, cause x591 is needed in a reg for other than x606, namely all: , x606--x607, x619, size: 2
mov rcx, 0xfdc1767ae2ffffff ; moving imm to reg
sbb r12, rcx
xchg rdx, rbp; x5, swapping with x6, which is currently in rdx
mulx rdx, rcx, [ r11 + 0x30 ]; x427, x426<- x5 * arg2[6]
mov [ rsp + 0x740 ], r12; spilling x606 to mem
movzx r12, byte [ rsp + 0x700 ]; load byte memx449 to register64
mov [ rsp + 0x748 ], rdx; spilling x427 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r12, rdx; loading flag
adox rcx, [ rsp + 0x6f0 ]
seto r12b; spill OF x451 to reg (r12)
movzx rdx, byte [ rsp + 0x720 ]; load byte memx464 to register64
mov byte [ rsp + 0x750 ], r13b; spilling byte x592 to mem
mov r13, -0x1 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r13, -0x1 ; moving imm to reg
adox rdx, r13; loading flag
adox rcx, [ rsp + 0x638 ]
mov rdx, 0x2341f27177344 ; moving imm to reg
mulx r9, r13, r9; x470, x469<- x453 * 0x2341f27177344
seto dl; spill OF x466 to reg (rdx)
mov [ rsp + 0x758 ], r9; spilling x470 to mem
movzx r9, byte [ rsp + 0x730 ]; load byte memx492 to register64
mov byte [ rsp + 0x760 ], r12b; spilling byte x451 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
adox r9, r12; loading flag
adox r13, [ rsp + 0x708 ]
setc r9b; spill CF x607 to reg (r9)
clc;
movzx r10, r10b
adcx r10, r12; loading flag
adcx rcx, r13
xchg rdx, rbp; x6, swapping with x466, which is currently in rdx
mulx r10, r13, [ r11 + 0x28 ]; x516, x515<- x6 * arg2[5]
setc r12b; spill CF x509 to reg (r12)
clc;
mov [ rsp + 0x768 ], r10; spilling x516 to mem
mov r10, -0x1 ; moving imm to reg
movzx rbx, bl
adcx rbx, r10; loading flag
adcx r13, [ rsp + 0x718 ]
setc bl; spill CF x536 to reg (rbx)
movzx r10, byte [ rsp + 0x738 ]; load byte memx549 to register64
clc;
mov byte [ rsp + 0x770 ], r12b; spilling byte x509 to mem
mov r12, -0x1 ; moving imm to reg
adcx r10, r12; loading flag
adcx rcx, r13
seto r10b; spill OF x494 to reg (r10)
movzx r13, byte [ rsp + 0x750 ]; load byte memx592 to register64
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
adox r13, r12; loading flag
adox rcx, [ rsp + 0x488 ]
setc r13b; spill CF x551 to reg (r13)
seto r12b; spill OF x594 to reg (r12)
mov byte [ rsp + 0x778 ], bl; spilling byte x536 to mem
movzx rbx, r9b; x607, copying x607 here, cause x607 is needed in a reg for other than x607, namely all: , x608--x609, size: 1
add rbx, -0x1
mov rbx, rcx; x608, copying x593 here, cause x593 is needed in a reg for other than x608, namely all: , x620, x608--x609, size: 2
mov r9, 0x7bc65c783158aea3 ; moving imm to reg
sbb rbx, r9
movzx r9, byte [ rsp + 0x760 ]; x452, copying x451 here, cause x451 is needed in a reg for other than x452, namely all: , x452, size: 1
mov [ rsp + 0x780 ], rsi; spilling arg1 to mem
mov rsi, [ rsp + 0x748 ]; load m64 x427 to register64
lea r9, [ r9 + rsi ]; r8/64 + m8
mov rsi, 0x0 ; moving imm to reg
dec rsi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
mov [ rsp + 0x788 ], rbx; spilling x608 to mem
movzx rbx, byte [ rsp + 0x630 ]; load byte memx425 to register64
movzx rbp, bpl
adox rbp, rsi; loading flag
adox r9, rbx
movzx rbx, r10b; x495, copying x494 here, cause x494 is needed in a reg for other than x495, namely all: , x495, size: 1
mov rbp, [ rsp + 0x758 ]; load m64 x470 to register64
lea rbx, [ rbx + rbp ]; r8/64 + m8
setc bpl; spill CF x609 to reg (rbp)
movzx r10, byte [ rsp + 0x770 ]; load byte memx509 to register64
clc;
adcx r10, rsi; loading flag
adcx r9, rbx
mulx rdx, r10, [ r11 + 0x30 ]; x514, x513<- x6 * arg2[6]
seto bl; spill OF x468 to reg (rbx)
movzx rsi, byte [ rsp + 0x778 ]; load byte memx536 to register64
mov byte [ rsp + 0x790 ], bpl; spilling byte x609 to mem
mov rbp, -0x1 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
adox rsi, rbp; loading flag
adox r10, [ rsp + 0x768 ]
setc sil; spill CF x511 to reg (rsi)
clc;
movzx r13, r13b
adcx r13, rbp; loading flag
adcx r9, r10
setc r13b; spill CF x553 to reg (r13)
clc;
movzx r12, r12b
adcx r12, rbp; loading flag
adcx r9, [ rsp + 0x498 ]
movzx r12, sil; x512, copying x511 here, cause x511 is needed in a reg for other than x512, namely all: , x512, size: 1
movzx rbx, bl
lea r12, [ r12 + rbx ]
mov rbx, 0x0 ; moving imm to reg
adox rdx, rbx
setc sil; spill CF x596 to reg (rsi)
movzx r10, byte [ rsp + 0x790 ]; x609, copying x609 here, cause x609 is needed in a reg for other than x609, namely all: , x610--x611, size: 1
add r10, -0x1
mov r10, r9; x610, copying x595 here, cause x595 is needed in a reg for other than x610, namely all: , x610--x611, x621, size: 2
mov rbx, 0x6cfc5fd681c52056 ; moving imm to reg
sbb r10, rbx
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, rbp; loading flag
adox r12, rdx
seto r13b; spill OF x555 to reg (r13)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
movzx rsi, sil
adox rsi, rdx; loading flag
adox r12, [ rsp + 0x490 ]
movzx rsi, r13b; x599, copying x555 here, cause x555 is needed in a reg for other than x599, namely all: , x599, size: 1
adox rsi, rbp
mov r13, r12; x612, copying x597 here, cause x597 is needed in a reg for other than x612, namely all: , x612--x613, x622, size: 2
mov rbp, 0x2341f27177344 ; moving imm to reg
sbb r13, rbp
sbb rsi, 0x00000000
mov rdx, [ rsp + 0x6b0 ]; x617, copying x602 here, cause x602 is needed in a reg for other than x617, namely all: , x617, size: 1
cmovc rdx, r8; if CF, x617<- x587 (nzVar)
mov r8, [ rsp + 0x788 ]; x620, copying x608 here, cause x608 is needed in a reg for other than x620, namely all: , x620, size: 1
cmovc r8, rcx; if CF, x620<- x593 (nzVar)
mov rcx, [ rsp + 0x668 ]; x616, copying x600 here, cause x600 is needed in a reg for other than x616, namely all: , x616, size: 1
cmovc rcx, r14; if CF, x616<- x585 (nzVar)
mov r14, [ rsp + 0x6e8 ]; x618, copying x604 here, cause x604 is needed in a reg for other than x618, namely all: , x618, size: 1
cmovc r14, rax; if CF, x618<- x589 (nzVar)
mov rax, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rax + 0x0 ], rcx; out1[0] = x616
cmovc r13, r12; if CF, x622<- x597 (nzVar)
mov [ rax + 0x8 ], rdx; out1[1] = x617
mov [ rax + 0x30 ], r13; out1[6] = x622
mov [ rax + 0x20 ], r8; out1[4] = x620
cmovc r10, r9; if CF, x621<- x595 (nzVar)
mov r9, [ rsp + 0x740 ]; x619, copying x606 here, cause x606 is needed in a reg for other than x619, namely all: , x619, size: 1
cmovc r9, r15; if CF, x619<- x591 (nzVar)
mov [ rax + 0x28 ], r10; out1[5] = x621
mov [ rax + 0x10 ], r14; out1[2] = x618
mov [ rax + 0x18 ], r9; out1[3] = x619
mov rbx, [ rsp + 0x798 ]; restoring from stack
mov rbp, [ rsp + 0x7a0 ]; restoring from stack
mov r12, [ rsp + 0x7a8 ]; restoring from stack
mov r13, [ rsp + 0x7b0 ]; restoring from stack
mov r14, [ rsp + 0x7b8 ]; restoring from stack
mov r15, [ rsp + 0x7c0 ]; restoring from stack
add rsp, 0x7c8 
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; clocked at 2200 MHz
; first cyclecount 643.34, best 637.5555555555555, lastGood 658.6666666666666
; seed 2655622732133814 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 89186 ms / 500 runs=> 178.372ms/run
; Time spent for assembling and measureing (initial batch_size=10, initial num_batches=101): 2167 ms
; Ratio (time for assembling + measure)/(total runtime for 500runs): 0.02429753548763259
; number reverted permutation/ tried permutation: 204 / 250 =81.600%
; number reverted decision/ tried decision: 172 / 251 =68.526%