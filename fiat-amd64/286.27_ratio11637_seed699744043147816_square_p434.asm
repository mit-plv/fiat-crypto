SECTION .text
	GLOBAL square_p434
square_p434:
sub rsp, 0x640 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x610 ], rbx; saving to stack
mov [ rsp + 0x618 ], rbp; saving to stack
mov [ rsp + 0x620 ], r12; saving to stack
mov [ rsp + 0x628 ], r13; saving to stack
mov [ rsp + 0x630 ], r14; saving to stack
mov [ rsp + 0x638 ], r15; saving to stack
mov rax, [ rsi + 0x8 ]; load m64 x1 to register64
mov r10, [ rsi + 0x0 ]; load m64 x7 to register64
mov rdx, r10; x7 to rdx
mulx r10, r11, [ rsi + 0x8 ]; x19, x18<- x7 * arg1[1]
mulx rbx, rbp, [ rsi + 0x0 ]; x21, x20<- x7 * arg1[0]
mov r12, rdx; preserving value of x7 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r13, r14, rax; x91, x90<- x1 * arg1[0]
mov r15, 0xffffffffffffffff ; moving imm to reg
mov rdx, rbp; x20 to rdx
mulx rbp, rcx, r15; x48, x47<- x20 * 0xffffffffffffffff
test al, al
adox r11, rbx
mulx r8, r9, r15; x46, x45<- x20 * 0xffffffffffffffff
adcx r9, rbp
xchg rdx, r12; x7, swapping with x20, which is currently in rdx
mulx rbx, rbp, [ rsi + 0x10 ]; x17, x16<- x7 * arg1[2]
xchg rdx, r15; 0xffffffffffffffff, swapping with x7, which is currently in rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov [ rsp + 0x8 ], rbx; spilling x17 to mem
mulx rdi, rbx, r12; x44, x43<- x20 * 0xffffffffffffffff
setc dl; spill CF x50 to reg (rdx)
clc;
adcx rcx, r12
adcx r9, r11
setc cl; spill CF x65 to reg (rcx)
clc;
mov r11, -0x1 ; moving imm to reg
movzx rdx, dl
adcx rdx, r11; loading flag
adcx r8, rbx
setc dl; spill CF x52 to reg (rdx)
clc;
adcx r14, r9
xchg rdx, rax; x1, swapping with x52, which is currently in rdx
mulx rbx, r9, [ rsi + 0x8 ]; x89, x88<- x1 * arg1[1]
mov r11, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r11; 0xffffffffffffffff, swapping with x1, which is currently in rdx
mov [ rsp + 0x10 ], rdi; spilling x44 to mem
mov byte [ rsp + 0x18 ], al; spilling byte x52 to mem
mulx rdi, rax, r14; x134, x133<- x105 * 0xffffffffffffffff
adox rbp, r10
seto r10b; spill OF x25 to reg (r10)
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rax, r14
seto al; spill OF x149 to reg (rax)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, rdx; loading flag
adox rbp, r8
mov rcx, [ rsi + 0x10 ]; load m64 x2 to register64
setc r8b; spill CF x106 to reg (r8)
clc;
adcx r9, r13
seto r13b; spill OF x67 to reg (r13)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, rdx; loading flag
adox rbp, r9
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r8, r9, rcx; x178, x177<- x2 * arg1[0]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x20 ], r8; spilling x178 to mem
mov byte [ rsp + 0x28 ], r13b; spilling byte x67 to mem
mulx r8, r13, r14; x132, x131<- x105 * 0xffffffffffffffff
setc dl; spill CF x93 to reg (rdx)
clc;
adcx r13, rdi
setc dil; spill CF x136 to reg (rdi)
clc;
mov [ rsp + 0x30 ], r8; spilling x132 to mem
mov r8, -0x1 ; moving imm to reg
movzx rax, al
adcx rax, r8; loading flag
adcx rbp, r13
mov al, dl; preserving value of x93 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r13, r8, r11; x87, x86<- x1 * arg1[2]
setc dl; spill CF x151 to reg (rdx)
clc;
adcx r9, rbp
mov rbp, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbp; 0xffffffffffffffff, swapping with x151, which is currently in rdx
mov [ rsp + 0x38 ], r13; spilling x87 to mem
mov byte [ rsp + 0x40 ], bpl; spilling byte x151 to mem
mulx r13, rbp, r9; x219, x218<- x192 * 0xffffffffffffffff
mov rdx, 0x6cfc5fd681c52056 ; moving imm to reg
mov byte [ rsp + 0x48 ], dil; spilling byte x136 to mem
mov byte [ rsp + 0x50 ], r10b; spilling byte x25 to mem
mulx rdi, r10, r9; x211, x210<- x192 * 0x6cfc5fd681c52056
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x58 ], rdi; spilling x211 to mem
mov [ rsp + 0x60 ], r15; spilling x7 to mem
mulx rdi, r15, r9; x221, x220<- x192 * 0xffffffffffffffff
mov [ rsp + 0x68 ], r15; spilling x220 to mem
mov [ rsp + 0x70 ], r10; spilling x210 to mem
mulx r15, r10, r9; x217, x216<- x192 * 0xffffffffffffffff
mov rdx, 0xfdc1767ae2ffffff ; moving imm to reg
mov [ rsp + 0x78 ], r12; spilling x20 to mem
mov [ rsp + 0x80 ], r15; spilling x217 to mem
mulx r12, r15, r9; x215, x214<- x192 * 0xfdc1767ae2ffffff
mov rdx, 0x7bc65c783158aea3 ; moving imm to reg
mov [ rsp + 0x88 ], r12; spilling x215 to mem
mov [ rsp + 0x90 ], r15; spilling x214 to mem
mulx r12, r15, r9; x213, x212<- x192 * 0x7bc65c783158aea3
seto dl; spill OF x108 to reg (rdx)
mov [ rsp + 0x98 ], r12; spilling x213 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
movzx rax, al
adox rax, r12; loading flag
adox rbx, r8
setc al; spill CF x193 to reg (rax)
clc;
adcx rbp, rdi
adcx r10, r13
mov r8, 0x2341f27177344 ; moving imm to reg
xchg rdx, r8; 0x2341f27177344, swapping with x108, which is currently in rdx
mulx r13, rdi, r9; x209, x208<- x192 * 0x2341f27177344
mov r12, [ rsp + 0x90 ]; load m64 x214 to register64
mov rdx, [ rsp + 0x80 ]; x226, copying x217 here, cause x217 is needed in a reg for other than x226, namely all: , x226--x227, size: 1
adcx rdx, r12
mov r12, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, r12; 0xfdc1767ae2ffffff, swapping with x226, which is currently in rdx
mov [ rsp + 0xa0 ], r12; spilling x226 to mem
mov [ rsp + 0xa8 ], r10; spilling x224 to mem
mulx r12, r10, [ rsp + 0x78 ]; x42, x41<- x20 * 0xfdc1767ae2ffffff
mov rdx, [ rsp + 0x88 ]; x228, copying x215 here, cause x215 is needed in a reg for other than x228, namely all: , x228--x229, size: 1
adcx rdx, r15
mov r15, [ rsp + 0x70 ]; load m64 x210 to register64
mov [ rsp + 0xb0 ], rdx; spilling x228 to mem
mov rdx, [ rsp + 0x98 ]; x230, copying x213 here, cause x213 is needed in a reg for other than x230, namely all: , x230--x231, size: 1
adcx rdx, r15
mov r15, rdx; preserving value of x230 into a new reg
mov rdx, [ rsp + 0x60 ]; saving x7 in rdx.
mov [ rsp + 0xb8 ], r12; spilling x42 to mem
mov [ rsp + 0xc0 ], rbp; spilling x222 to mem
mulx r12, rbp, [ rsi + 0x18 ]; x15, x14<- x7 * arg1[3]
mov [ rsp + 0xc8 ], r15; spilling x230 to mem
mov r15, [ rsp + 0x58 ]; x232, copying x211 here, cause x211 is needed in a reg for other than x232, namely all: , x232--x233, size: 1
adcx r15, rdi
seto dil; spill OF x95 to reg (rdi)
mov [ rsp + 0xd0 ], r15; spilling x232 to mem
movzx r15, byte [ rsp + 0x50 ]; load byte memx25 to register64
mov [ rsp + 0xd8 ], r12; spilling x15 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
adox r15, r12; loading flag
adox rbp, [ rsp + 0x8 ]
seto r15b; spill OF x27 to reg (r15)
movzx r12, byte [ rsp + 0x18 ]; load byte memx52 to register64
mov byte [ rsp + 0xe0 ], dil; spilling byte x95 to mem
mov rdi, -0x1 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdi, -0x1 ; moving imm to reg
adox r12, rdi; loading flag
adox r10, [ rsp + 0x10 ]
mov r12, [ rsi + 0x18 ]; load m64 x3 to register64
seto dil; spill OF x54 to reg (rdi)
mov byte [ rsp + 0xe8 ], r15b; spilling byte x27 to mem
movzx r15, byte [ rsp + 0x28 ]; load byte memx67 to register64
mov [ rsp + 0xf0 ], r12; spilling x3 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
adox r15, r12; loading flag
adox rbp, r10
mov r15, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r15; 0xffffffffffffffff, swapping with x7, which is currently in rdx
mulx r10, r12, r14; x130, x129<- x105 * 0xffffffffffffffff
seto dl; spill OF x69 to reg (rdx)
mov [ rsp + 0xf8 ], r10; spilling x130 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r8, r8b
adox r8, r10; loading flag
adox rbp, rbx
mov r8, 0x0 ; moving imm to reg
adcx r13, r8
movzx rbx, byte [ rsp + 0x48 ]; load byte memx136 to register64
clc;
adcx rbx, r10; loading flag
adcx r12, [ rsp + 0x30 ]
xchg rdx, rcx; x2, swapping with x69, which is currently in rdx
mulx rbx, r8, [ rsi + 0x8 ]; x176, x175<- x2 * arg1[1]
xchg rdx, r15; x7, swapping with x2, which is currently in rdx
mov [ rsp + 0x100 ], r13; spilling x234 to mem
mulx r10, r13, [ rsi + 0x20 ]; x13, x12<- x7 * arg1[4]
mov [ rsp + 0x108 ], r10; spilling x13 to mem
seto r10b; spill OF x110 to reg (r10)
mov byte [ rsp + 0x110 ], cl; spilling byte x69 to mem
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, [ rsp + 0x20 ]
seto cl; spill OF x180 to reg (rcx)
mov byte [ rsp + 0x118 ], r10b; spilling byte x110 to mem
movzx r10, byte [ rsp + 0x40 ]; load byte memx151 to register64
mov byte [ rsp + 0x120 ], dil; spilling byte x54 to mem
mov rdi, 0x0 ; moving imm to reg
dec rdi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r10, rdi; loading flag
adox rbp, r12
setc r10b; spill CF x138 to reg (r10)
clc;
movzx rax, al
adcx rax, rdi; loading flag
adcx rbp, r8
setc al; spill CF x195 to reg (rax)
clc;
adcx r9, [ rsp + 0x68 ]
mov r9, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, r9; 0xfdc1767ae2ffffff, swapping with x7, which is currently in rdx
mulx r12, r8, r14; x128, x127<- x105 * 0xfdc1767ae2ffffff
mov rdi, [ rsp + 0xc0 ]; x237, copying x222 here, cause x222 is needed in a reg for other than x237, namely all: , x237--x238, size: 1
adcx rdi, rbp
mov rbp, rdx; preserving value of 0xfdc1767ae2ffffff into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x128 ], r12; spilling x128 to mem
mov byte [ rsp + 0x130 ], al; spilling byte x195 to mem
mulx r12, rax, [ rsp + 0xf0 ]; x265, x264<- x3 * arg1[0]
mov rdx, 0x7bc65c783158aea3 ; moving imm to reg
mov [ rsp + 0x138 ], r12; spilling x265 to mem
mulx rbp, r12, [ rsp + 0x78 ]; x40, x39<- x20 * 0x7bc65c783158aea3
xchg rdx, r15; x2, swapping with 0x7bc65c783158aea3, which is currently in rdx
mov [ rsp + 0x140 ], rbp; spilling x40 to mem
mulx r15, rbp, [ rsi + 0x10 ]; x174, x173<- x2 * arg1[2]
mov [ rsp + 0x148 ], r15; spilling x174 to mem
setc r15b; spill CF x238 to reg (r15)
mov [ rsp + 0x150 ], r8; spilling x127 to mem
movzx r8, byte [ rsp + 0xe8 ]; load byte memx27 to register64
clc;
mov byte [ rsp + 0x158 ], r10b; spilling byte x138 to mem
mov r10, -0x1 ; moving imm to reg
adcx r8, r10; loading flag
adcx r13, [ rsp + 0xd8 ]
setc r8b; spill CF x29 to reg (r8)
clc;
movzx rcx, cl
adcx rcx, r10; loading flag
adcx rbx, rbp
xchg rdx, r11; x1, swapping with x2, which is currently in rdx
mulx rcx, rbp, [ rsi + 0x18 ]; x85, x84<- x1 * arg1[3]
setc r10b; spill CF x182 to reg (r10)
mov byte [ rsp + 0x160 ], r8b; spilling byte x29 to mem
movzx r8, byte [ rsp + 0x120 ]; load byte memx54 to register64
clc;
mov [ rsp + 0x168 ], rcx; spilling x85 to mem
mov rcx, -0x1 ; moving imm to reg
adcx r8, rcx; loading flag
adcx r12, [ rsp + 0xb8 ]
mov r8, [ rsi + 0x20 ]; load m64 x4 to register64
setc cl; spill CF x56 to reg (rcx)
clc;
adcx rax, rdi
setc dil; spill CF x280 to reg (rdi)
mov byte [ rsp + 0x170 ], r10b; spilling byte x182 to mem
movzx r10, byte [ rsp + 0x110 ]; load byte memx69 to register64
clc;
mov byte [ rsp + 0x178 ], cl; spilling byte x56 to mem
mov rcx, -0x1 ; moving imm to reg
adcx r10, rcx; loading flag
adcx r13, r12
setc r10b; spill CF x71 to reg (r10)
movzx r12, byte [ rsp + 0xe0 ]; load byte memx95 to register64
clc;
adcx r12, rcx; loading flag
adcx rbp, [ rsp + 0x38 ]
mov r12, [ rsp + 0x150 ]; load m64 x127 to register64
setc cl; spill CF x97 to reg (rcx)
mov byte [ rsp + 0x180 ], r10b; spilling byte x71 to mem
movzx r10, byte [ rsp + 0x158 ]; load byte memx138 to register64
clc;
mov byte [ rsp + 0x188 ], dil; spilling byte x280 to mem
mov rdi, -0x1 ; moving imm to reg
adcx r10, rdi; loading flag
adcx r12, [ rsp + 0xf8 ]
setc r10b; spill CF x140 to reg (r10)
movzx rdi, byte [ rsp + 0x118 ]; load byte memx110 to register64
clc;
mov byte [ rsp + 0x190 ], cl; spilling byte x97 to mem
mov rcx, -0x1 ; moving imm to reg
adcx rdi, rcx; loading flag
adcx r13, rbp
mov rdi, rdx; preserving value of x1 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx rbp, rcx, [ rsp + 0xf0 ]; x263, x262<- x3 * arg1[1]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x198 ], rbp; spilling x263 to mem
mov byte [ rsp + 0x1a0 ], r10b; spilling byte x140 to mem
mulx rbp, r10, rax; x306, x305<- x279 * 0xffffffffffffffff
adox r12, r13
mov [ rsp + 0x1a8 ], rbp; spilling x306 to mem
mulx r13, rbp, rax; x308, x307<- x279 * 0xffffffffffffffff
setc dl; spill CF x112 to reg (rdx)
mov [ rsp + 0x1b0 ], r8; spilling x4 to mem
movzx r8, byte [ rsp + 0x130 ]; load byte memx195 to register64
clc;
mov [ rsp + 0x1b8 ], rbp; spilling x307 to mem
mov rbp, -0x1 ; moving imm to reg
adcx r8, rbp; loading flag
adcx r12, rbx
seto r8b; spill OF x155 to reg (r8)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rcx, [ rsp + 0x138 ]
seto bl; spill OF x267 to reg (rbx)
dec rbp; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r15, r15b
adox r15, rbp; loading flag
adox r12, [ rsp + 0xa8 ]
setc r15b; spill CF x197 to reg (r15)
clc;
adcx r10, r13
mov r13b, dl; preserving value of x112 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov byte [ rsp + 0x1c0 ], bl; spilling byte x267 to mem
mulx rbp, rbx, r9; x11, x10<- x7 * arg1[5]
mov rdx, 0x6cfc5fd681c52056 ; moving imm to reg
mov [ rsp + 0x1c8 ], rbp; spilling x11 to mem
mov byte [ rsp + 0x1d0 ], r15b; spilling byte x197 to mem
mulx rbp, r15, [ rsp + 0x78 ]; x38, x37<- x20 * 0x6cfc5fd681c52056
mov rdx, rax; _, copying x279 here, cause x279 is needed in a reg for other than _, namely all: , x301--x302, _--x323, x303--x304, x297--x298, x295--x296, x299--x300, size: 6
mov [ rsp + 0x1d8 ], rbp; spilling x38 to mem
setc bpl; spill CF x310 to reg (rbp)
clc;
adcx rdx, [ rsp + 0x1b8 ]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov byte [ rsp + 0x1e0 ], bpl; spilling byte x310 to mem
mov byte [ rsp + 0x1e8 ], r8b; spilling byte x155 to mem
mulx rbp, r8, [ rsp + 0x1b0 ]; x352, x351<- x4 * arg1[0]
setc dl; spill CF x323 to reg (rdx)
mov [ rsp + 0x1f0 ], rbp; spilling x352 to mem
movzx rbp, byte [ rsp + 0x188 ]; load byte memx280 to register64
clc;
mov byte [ rsp + 0x1f8 ], r13b; spilling byte x112 to mem
mov r13, -0x1 ; moving imm to reg
adcx rbp, r13; loading flag
adcx r12, rcx
setc bpl; spill CF x282 to reg (rbp)
movzx rcx, byte [ rsp + 0x178 ]; load byte memx56 to register64
clc;
adcx rcx, r13; loading flag
adcx r15, [ rsp + 0x140 ]
seto cl; spill OF x240 to reg (rcx)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
movzx rdx, dl
adox rdx, r13; loading flag
adox r12, r10
setc r10b; spill CF x58 to reg (r10)
clc;
adcx r8, r12
mov rdx, 0xffffffffffffffff ; moving imm to reg
mulx r12, r13, r8; x395, x394<- x366 * 0xffffffffffffffff
mov rdx, 0x7bc65c783158aea3 ; moving imm to reg
mov byte [ rsp + 0x200 ], r10b; spilling byte x58 to mem
mov [ rsp + 0x208 ], r12; spilling x395 to mem
mulx r10, r12, r14; x126, x125<- x105 * 0x7bc65c783158aea3
setc dl; spill CF x367 to reg (rdx)
clc;
adcx r13, r8
xchg rdx, rdi; x1, swapping with x367, which is currently in rdx
mov [ rsp + 0x210 ], r10; spilling x126 to mem
mulx r13, r10, [ rsi + 0x20 ]; x83, x82<- x1 * arg1[4]
mov [ rsp + 0x218 ], r13; spilling x83 to mem
mov r13, rdx; preserving value of x1 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov byte [ rsp + 0x220 ], dil; spilling byte x367 to mem
mov byte [ rsp + 0x228 ], bpl; spilling byte x282 to mem
mulx rdi, rbp, r11; x172, x171<- x2 * arg1[3]
seto dl; spill OF x325 to reg (rdx)
mov [ rsp + 0x230 ], rdi; spilling x172 to mem
movzx rdi, byte [ rsp + 0x190 ]; load byte memx97 to register64
mov byte [ rsp + 0x238 ], cl; spilling byte x240 to mem
mov rcx, -0x1 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rcx, -0x1 ; moving imm to reg
adox rdi, rcx; loading flag
adox r10, [ rsp + 0x168 ]
setc dil; spill CF x410 to reg (rdi)
movzx rcx, byte [ rsp + 0x160 ]; load byte memx29 to register64
clc;
mov byte [ rsp + 0x240 ], dl; spilling byte x325 to mem
mov rdx, -0x1 ; moving imm to reg
adcx rcx, rdx; loading flag
adcx rbx, [ rsp + 0x108 ]
setc cl; spill CF x31 to reg (rcx)
movzx rdx, byte [ rsp + 0x180 ]; load byte memx71 to register64
clc;
mov byte [ rsp + 0x248 ], dil; spilling byte x410 to mem
mov rdi, -0x1 ; moving imm to reg
adcx rdx, rdi; loading flag
adcx rbx, r15
mov rdx, 0xffffffffffffffff ; moving imm to reg
mulx r15, rdi, rax; x304, x303<- x279 * 0xffffffffffffffff
setc dl; spill CF x73 to reg (rdx)
mov [ rsp + 0x250 ], r15; spilling x304 to mem
movzx r15, byte [ rsp + 0x1a0 ]; load byte memx140 to register64
clc;
mov byte [ rsp + 0x258 ], cl; spilling byte x31 to mem
mov rcx, -0x1 ; moving imm to reg
adcx r15, rcx; loading flag
adcx r12, [ rsp + 0x128 ]
mov r15, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r8; x366, swapping with x73, which is currently in rdx
mov byte [ rsp + 0x260 ], r8b; spilling byte x73 to mem
mulx rcx, r8, r15; x393, x392<- x366 * 0xffffffffffffffff
seto r15b; spill OF x99 to reg (r15)
mov [ rsp + 0x268 ], rcx; spilling x393 to mem
movzx rcx, byte [ rsp + 0x1f8 ]; load byte memx112 to register64
mov [ rsp + 0x270 ], r8; spilling x392 to mem
mov r8, 0x0 ; moving imm to reg
dec r8; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rcx, r8; loading flag
adox rbx, r10
setc cl; spill CF x142 to reg (rcx)
movzx r10, byte [ rsp + 0x1e8 ]; load byte memx155 to register64
clc;
adcx r10, r8; loading flag
adcx rbx, r12
setc r10b; spill CF x157 to reg (r10)
movzx r12, byte [ rsp + 0x170 ]; load byte memx182 to register64
clc;
adcx r12, r8; loading flag
adcx rbp, [ rsp + 0x148 ]
mov r12, rdx; preserving value of x366 into a new reg
mov rdx, [ rsp + 0xf0 ]; saving x3 in rdx.
mov byte [ rsp + 0x278 ], r10b; spilling byte x157 to mem
mulx r8, r10, [ rsi + 0x10 ]; x261, x260<- x3 * arg1[2]
mov [ rsp + 0x280 ], r8; spilling x261 to mem
setc r8b; spill CF x184 to reg (r8)
mov byte [ rsp + 0x288 ], cl; spilling byte x142 to mem
movzx rcx, byte [ rsp + 0x1d0 ]; load byte memx197 to register64
clc;
mov byte [ rsp + 0x290 ], r15b; spilling byte x99 to mem
mov r15, -0x1 ; moving imm to reg
adcx rcx, r15; loading flag
adcx rbx, rbp
setc cl; spill CF x199 to reg (rcx)
movzx rbp, byte [ rsp + 0x1e0 ]; load byte memx310 to register64
clc;
adcx rbp, r15; loading flag
adcx rdi, [ rsp + 0x1a8 ]
setc bpl; spill CF x312 to reg (rbp)
movzx r15, byte [ rsp + 0x238 ]; load byte memx240 to register64
clc;
mov byte [ rsp + 0x298 ], cl; spilling byte x199 to mem
mov rcx, -0x1 ; moving imm to reg
adcx r15, rcx; loading flag
adcx rbx, [ rsp + 0xa0 ]
setc r15b; spill CF x242 to reg (r15)
movzx rcx, byte [ rsp + 0x1c0 ]; load byte memx267 to register64
clc;
mov byte [ rsp + 0x2a0 ], bpl; spilling byte x312 to mem
mov rbp, -0x1 ; moving imm to reg
adcx rcx, rbp; loading flag
adcx r10, [ rsp + 0x198 ]
seto cl; spill OF x114 to reg (rcx)
movzx rbp, byte [ rsp + 0x228 ]; load byte memx282 to register64
mov byte [ rsp + 0x2a8 ], r15b; spilling byte x242 to mem
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbp, r15; loading flag
adox rbx, r10
mov rbp, rdx; preserving value of x3 into a new reg
mov rdx, [ rsp + 0x1b0 ]; saving x4 in rdx.
mulx r10, r15, [ rsi + 0x8 ]; x350, x349<- x4 * arg1[1]
mov [ rsp + 0x2b0 ], r10; spilling x350 to mem
mov r10, rdx; preserving value of x4 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov byte [ rsp + 0x2b8 ], cl; spilling byte x114 to mem
mov byte [ rsp + 0x2c0 ], r8b; spilling byte x184 to mem
mulx rcx, r8, r11; x170, x169<- x2 * arg1[4]
seto dl; spill OF x284 to reg (rdx)
mov [ rsp + 0x2c8 ], rcx; spilling x170 to mem
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, [ rsp + 0x1f0 ]
setc cl; spill CF x269 to reg (rcx)
mov byte [ rsp + 0x2d0 ], dl; spilling byte x284 to mem
movzx rdx, byte [ rsp + 0x240 ]; load byte memx325 to register64
clc;
mov [ rsp + 0x2d8 ], r8; spilling x169 to mem
mov r8, -0x1 ; moving imm to reg
adcx rdx, r8; loading flag
adcx rbx, rdi
mov rdx, [ rsp + 0x270 ]; load m64 x392 to register64
setc dil; spill CF x327 to reg (rdi)
clc;
adcx rdx, [ rsp + 0x208 ]
setc r8b; spill CF x397 to reg (r8)
mov byte [ rsp + 0x2e0 ], dil; spilling byte x327 to mem
movzx rdi, byte [ rsp + 0x220 ]; load byte memx367 to register64
clc;
mov byte [ rsp + 0x2e8 ], cl; spilling byte x269 to mem
mov rcx, -0x1 ; moving imm to reg
adcx rdi, rcx; loading flag
adcx rbx, r15
mov rdi, 0x2341f27177344 ; moving imm to reg
xchg rdx, rdi; 0x2341f27177344, swapping with x396, which is currently in rdx
mulx r15, rcx, [ rsp + 0x78 ]; x36, x35<- x20 * 0x2341f27177344
mov byte [ rsp + 0x2f0 ], r8b; spilling byte x397 to mem
mov r8, rdx; preserving value of 0x2341f27177344 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x2f8 ], r15; spilling x36 to mem
mov [ rsp + 0x300 ], rcx; spilling x35 to mem
mulx r15, rcx, r13; x81, x80<- x1 * arg1[5]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x308 ], r15; spilling x81 to mem
mulx r8, r15, r12; x391, x390<- x366 * 0xffffffffffffffff
seto dl; spill OF x354 to reg (rdx)
mov [ rsp + 0x310 ], r8; spilling x391 to mem
movzx r8, byte [ rsp + 0x248 ]; load byte memx410 to register64
mov [ rsp + 0x318 ], r15; spilling x390 to mem
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r8, r15; loading flag
adox rbx, rdi
setc r8b; spill CF x369 to reg (r8)
movzx rdi, byte [ rsp + 0x290 ]; load byte memx99 to register64
clc;
adcx rdi, r15; loading flag
adcx rcx, [ rsp + 0x218 ]
mov rdi, [ rsp + 0x1d8 ]; load m64 x38 to register64
setc r15b; spill CF x101 to reg (r15)
mov [ rsp + 0x320 ], rbx; spilling x411 to mem
movzx rbx, byte [ rsp + 0x200 ]; load byte memx58 to register64
clc;
mov byte [ rsp + 0x328 ], r8b; spilling byte x369 to mem
mov r8, -0x1 ; moving imm to reg
adcx rbx, r8; loading flag
adcx rdi, [ rsp + 0x300 ]
mov bl, dl; preserving value of x354 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mulx r9, r8, r9; x9, x8<- x7 * arg1[6]
mov rdx, [ rsp + 0x2d8 ]; load m64 x169 to register64
mov byte [ rsp + 0x330 ], r15b; spilling byte x101 to mem
setc r15b; spill CF x60 to reg (r15)
mov [ rsp + 0x338 ], r9; spilling x9 to mem
movzx r9, byte [ rsp + 0x2c0 ]; load byte memx184 to register64
clc;
mov byte [ rsp + 0x340 ], bl; spilling byte x354 to mem
mov rbx, -0x1 ; moving imm to reg
adcx r9, rbx; loading flag
adcx rdx, [ rsp + 0x230 ]
mov r9, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, r9; 0x6cfc5fd681c52056, swapping with x185, which is currently in rdx
mov byte [ rsp + 0x348 ], r15b; spilling byte x60 to mem
mulx rbx, r15, r14; x124, x123<- x105 * 0x6cfc5fd681c52056
setc dl; spill CF x186 to reg (rdx)
mov [ rsp + 0x350 ], rbx; spilling x124 to mem
movzx rbx, byte [ rsp + 0x258 ]; load byte memx31 to register64
clc;
mov [ rsp + 0x358 ], r9; spilling x185 to mem
mov r9, -0x1 ; moving imm to reg
adcx rbx, r9; loading flag
adcx r8, [ rsp + 0x1c8 ]
seto bl; spill OF x412 to reg (rbx)
movzx r9, byte [ rsp + 0x288 ]; load byte memx142 to register64
mov byte [ rsp + 0x360 ], dl; spilling byte x186 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r9, rdx; loading flag
adox r15, [ rsp + 0x210 ]
setc r9b; spill CF x33 to reg (r9)
movzx rdx, byte [ rsp + 0x260 ]; load byte memx73 to register64
clc;
mov byte [ rsp + 0x368 ], bl; spilling byte x412 to mem
mov rbx, -0x1 ; moving imm to reg
adcx rdx, rbx; loading flag
adcx r8, rdi
setc dl; spill CF x75 to reg (rdx)
movzx rdi, byte [ rsp + 0x2b8 ]; load byte memx114 to register64
clc;
adcx rdi, rbx; loading flag
adcx r8, rcx
setc dil; spill CF x116 to reg (rdi)
movzx rcx, byte [ rsp + 0x278 ]; load byte memx157 to register64
clc;
adcx rcx, rbx; loading flag
adcx r8, r15
mov cl, dl; preserving value of x75 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx r15, rbx, rbp; x259, x258<- x3 * arg1[3]
seto dl; spill OF x144 to reg (rdx)
mov byte [ rsp + 0x370 ], dil; spilling byte x116 to mem
movzx rdi, byte [ rsp + 0x298 ]; load byte memx199 to register64
mov byte [ rsp + 0x378 ], cl; spilling byte x75 to mem
mov rcx, -0x1 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rcx, -0x1 ; moving imm to reg
adox rdi, rcx; loading flag
adox r8, [ rsp + 0x358 ]
setc dil; spill CF x159 to reg (rdi)
movzx rcx, byte [ rsp + 0x2a8 ]; load byte memx242 to register64
clc;
mov byte [ rsp + 0x380 ], dl; spilling byte x144 to mem
mov rdx, -0x1 ; moving imm to reg
adcx rcx, rdx; loading flag
adcx r8, [ rsp + 0xb0 ]
mov rcx, 0xfdc1767ae2ffffff ; moving imm to reg
mov rdx, rcx; 0xfdc1767ae2ffffff to rdx
mov byte [ rsp + 0x388 ], dil; spilling byte x159 to mem
mulx rcx, rdi, rax; x302, x301<- x279 * 0xfdc1767ae2ffffff
setc dl; spill CF x244 to reg (rdx)
mov [ rsp + 0x390 ], rcx; spilling x302 to mem
movzx rcx, byte [ rsp + 0x2e8 ]; load byte memx269 to register64
clc;
mov [ rsp + 0x398 ], r15; spilling x259 to mem
mov r15, -0x1 ; moving imm to reg
adcx rcx, r15; loading flag
adcx rbx, [ rsp + 0x280 ]
seto cl; spill OF x201 to reg (rcx)
movzx r15, byte [ rsp + 0x2d0 ]; load byte memx284 to register64
mov byte [ rsp + 0x3a0 ], dl; spilling byte x244 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, rdx; loading flag
adox r8, rbx
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r15, rbx, r10; x348, x347<- x4 * arg1[2]
mov rdx, 0x2341f27177344 ; moving imm to reg
mov [ rsp + 0x3a8 ], r15; spilling x348 to mem
mulx r14, r15, r14; x122, x121<- x105 * 0x2341f27177344
seto dl; spill OF x286 to reg (rdx)
mov [ rsp + 0x3b0 ], r14; spilling x122 to mem
movzx r14, byte [ rsp + 0x2a0 ]; load byte memx312 to register64
mov byte [ rsp + 0x3b8 ], cl; spilling byte x201 to mem
mov rcx, -0x1 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rcx, -0x1 ; moving imm to reg
adox r14, rcx; loading flag
adox rdi, [ rsp + 0x250 ]
xchg rdx, rbp; x3, swapping with x286, which is currently in rdx
mulx r14, rcx, [ rsi + 0x20 ]; x257, x256<- x3 * arg1[4]
mov [ rsp + 0x3c0 ], r14; spilling x257 to mem
seto r14b; spill OF x314 to reg (r14)
mov byte [ rsp + 0x3c8 ], bpl; spilling byte x286 to mem
movzx rbp, byte [ rsp + 0x340 ]; load byte memx354 to register64
mov [ rsp + 0x3d0 ], r15; spilling x121 to mem
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbp, r15; loading flag
adox rbx, [ rsp + 0x2b0 ]
seto bpl; spill OF x356 to reg (rbp)
movzx r15, byte [ rsp + 0x2e0 ]; load byte memx327 to register64
mov byte [ rsp + 0x3d8 ], r14b; spilling byte x314 to mem
mov r14, -0x1 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r14, -0x1 ; moving imm to reg
adox r15, r14; loading flag
adox r8, rdi
movzx r15, r9b; x34, copying x33 here, cause x33 is needed in a reg for other than x34, namely all: , x34, size: 1
mov rdi, [ rsp + 0x338 ]; load m64 x9 to register64
lea r15, [ r15 + rdi ]; r8/64 + m8
movzx rdi, byte [ rsp + 0x348 ]; x61, copying x60 here, cause x60 is needed in a reg for other than x61, namely all: , x61, size: 1
mov r9, [ rsp + 0x2f8 ]; load m64 x36 to register64
lea rdi, [ rdi + r9 ]; r8/64 + m8
mov r9, [ rsp + 0x268 ]; load m64 x393 to register64
seto r14b; spill OF x329 to reg (r14)
mov byte [ rsp + 0x3e0 ], bpl; spilling byte x356 to mem
movzx rbp, byte [ rsp + 0x2f0 ]; load byte memx397 to register64
mov [ rsp + 0x3e8 ], rdi; spilling x61 to mem
mov rdi, 0x0 ; moving imm to reg
dec rdi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbp, rdi; loading flag
adox r9, [ rsp + 0x318 ]
mov rbp, rdx; preserving value of x3 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mulx r13, rdi, r13; x79, x78<- x1 * arg1[6]
seto dl; spill OF x399 to reg (rdx)
mov byte [ rsp + 0x3f0 ], r14b; spilling byte x329 to mem
movzx r14, byte [ rsp + 0x330 ]; load byte memx101 to register64
mov [ rsp + 0x3f8 ], r13; spilling x79 to mem
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r14, r13; loading flag
adox rdi, [ rsp + 0x308 ]
mov r14, [ rsp + 0x398 ]; x272, copying x259 here, cause x259 is needed in a reg for other than x272, namely all: , x272--x273, size: 1
adcx r14, rcx
setc cl; spill CF x273 to reg (rcx)
movzx r13, byte [ rsp + 0x328 ]; load byte memx369 to register64
clc;
mov byte [ rsp + 0x400 ], dl; spilling byte x399 to mem
mov rdx, -0x1 ; moving imm to reg
adcx r13, rdx; loading flag
adcx r8, rbx
seto r13b; spill OF x103 to reg (r13)
movzx rbx, byte [ rsp + 0x378 ]; load byte memx75 to register64
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
adox rbx, rdx; loading flag
adox r15, [ rsp + 0x3e8 ]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov byte [ rsp + 0x408 ], cl; spilling byte x273 to mem
mulx rbx, rcx, r11; x168, x167<- x2 * arg1[5]
setc dl; spill CF x371 to reg (rdx)
mov byte [ rsp + 0x410 ], r13b; spilling byte x103 to mem
movzx r13, byte [ rsp + 0x368 ]; load byte memx412 to register64
clc;
mov [ rsp + 0x418 ], r14; spilling x272 to mem
mov r14, -0x1 ; moving imm to reg
adcx r13, r14; loading flag
adcx r8, r9
mov r13, [ rsp + 0x350 ]; load m64 x124 to register64
seto r9b; spill OF x77 to reg (r9)
movzx r14, byte [ rsp + 0x380 ]; load byte memx144 to register64
mov [ rsp + 0x420 ], r8; spilling x413 to mem
mov r8, 0x0 ; moving imm to reg
dec r8; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r14, r8; loading flag
adox r13, [ rsp + 0x3d0 ]
setc r14b; spill CF x414 to reg (r14)
movzx r8, byte [ rsp + 0x360 ]; load byte memx186 to register64
clc;
mov byte [ rsp + 0x428 ], dl; spilling byte x371 to mem
mov rdx, -0x1 ; moving imm to reg
adcx r8, rdx; loading flag
adcx rcx, [ rsp + 0x2c8 ]
mov r8, 0xfdc1767ae2ffffff ; moving imm to reg
mov rdx, r12; x366 to rdx
mov byte [ rsp + 0x430 ], r14b; spilling byte x414 to mem
mulx r12, r14, r8; x389, x388<- x366 * 0xfdc1767ae2ffffff
seto r8b; spill OF x146 to reg (r8)
mov [ rsp + 0x438 ], r12; spilling x389 to mem
movzx r12, byte [ rsp + 0x370 ]; load byte memx116 to register64
mov byte [ rsp + 0x440 ], r9b; spilling byte x77 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r12, r9; loading flag
adox r15, rdi
seto r12b; spill OF x118 to reg (r12)
movzx rdi, byte [ rsp + 0x388 ]; load byte memx159 to register64
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
adox rdi, r9; loading flag
adox r15, r13
mov rdi, rdx; preserving value of x366 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mulx r11, r13, r11; x166, x165<- x2 * arg1[6]
setc dl; spill CF x188 to reg (rdx)
movzx r9, byte [ rsp + 0x3b8 ]; load byte memx201 to register64
clc;
mov [ rsp + 0x448 ], r11; spilling x166 to mem
mov r11, -0x1 ; moving imm to reg
adcx r9, r11; loading flag
adcx r15, rcx
movzx r9, r8b; x147, copying x146 here, cause x146 is needed in a reg for other than x147, namely all: , x147, size: 1
mov rcx, [ rsp + 0x3b0 ]; load m64 x122 to register64
lea r9, [ r9 + rcx ]; r8/64 + m8
seto cl; spill OF x161 to reg (rcx)
movzx r8, byte [ rsp + 0x3a0 ]; load byte memx244 to register64
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r11, -0x1 ; moving imm to reg
adox r8, r11; loading flag
adox r15, [ rsp + 0xc8 ]
seto r8b; spill OF x246 to reg (r8)
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r11, -0x1 ; moving imm to reg
movzx rdx, dl
adox rdx, r11; loading flag
adox rbx, r13
mov rdx, 0x7bc65c783158aea3 ; moving imm to reg
mulx r13, r11, rax; x300, x299<- x279 * 0x7bc65c783158aea3
setc dl; spill CF x203 to reg (rdx)
mov [ rsp + 0x450 ], r13; spilling x300 to mem
movzx r13, byte [ rsp + 0x3c8 ]; load byte memx286 to register64
clc;
mov byte [ rsp + 0x458 ], r8b; spilling byte x246 to mem
mov r8, -0x1 ; moving imm to reg
adcx r13, r8; loading flag
adcx r15, [ rsp + 0x418 ]
setc r13b; spill CF x288 to reg (r13)
movzx r8, byte [ rsp + 0x3d8 ]; load byte memx314 to register64
clc;
mov [ rsp + 0x460 ], rbx; spilling x189 to mem
mov rbx, -0x1 ; moving imm to reg
adcx r8, rbx; loading flag
adcx r11, [ rsp + 0x390 ]
movzx r8, byte [ rsp + 0x410 ]; x104, copying x103 here, cause x103 is needed in a reg for other than x104, namely all: , x104, size: 1
mov rbx, [ rsp + 0x3f8 ]; load m64 x79 to register64
lea r8, [ r8 + rbx ]; r8/64 + m8
setc bl; spill CF x316 to reg (rbx)
mov byte [ rsp + 0x468 ], r13b; spilling byte x288 to mem
movzx r13, byte [ rsp + 0x400 ]; load byte memx399 to register64
clc;
mov byte [ rsp + 0x470 ], dl; spilling byte x203 to mem
mov rdx, -0x1 ; moving imm to reg
adcx r13, rdx; loading flag
adcx r14, [ rsp + 0x310 ]
setc r13b; spill CF x401 to reg (r13)
movzx rdx, byte [ rsp + 0x3f0 ]; load byte memx329 to register64
clc;
mov byte [ rsp + 0x478 ], bl; spilling byte x316 to mem
mov rbx, -0x1 ; moving imm to reg
adcx rdx, rbx; loading flag
adcx r15, r11
mov rdx, r10; x4 to rdx
mulx r10, r11, [ rsi + 0x18 ]; x346, x345<- x4 * arg1[3]
setc bl; spill CF x331 to reg (rbx)
clc;
mov byte [ rsp + 0x480 ], r13b; spilling byte x401 to mem
mov r13, -0x1 ; moving imm to reg
mov [ rsp + 0x488 ], r14; spilling x400 to mem
movzx r14, byte [ rsp + 0x440 ]; load byte memx77 to register64
movzx r12, r12b
adcx r12, r13; loading flag
adcx r8, r14
setc r14b; spill CF x120 to reg (r14)
clc;
movzx rcx, cl
adcx rcx, r13; loading flag
adcx r8, r9
setc r12b; spill CF x163 to reg (r12)
movzx rcx, byte [ rsp + 0x3e0 ]; load byte memx356 to register64
clc;
adcx rcx, r13; loading flag
adcx r11, [ rsp + 0x3a8 ]
mov rcx, rdx; preserving value of x4 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx r9, r13, rbp; x255, x254<- x3 * arg1[5]
setc dl; spill CF x358 to reg (rdx)
mov byte [ rsp + 0x490 ], bl; spilling byte x331 to mem
movzx rbx, byte [ rsp + 0x428 ]; load byte memx371 to register64
clc;
mov byte [ rsp + 0x498 ], r14b; spilling byte x120 to mem
mov r14, -0x1 ; moving imm to reg
adcx rbx, r14; loading flag
adcx r15, r11
xchg rdx, rcx; x4, swapping with x358, which is currently in rdx
mulx rbx, r11, [ rsi + 0x20 ]; x344, x343<- x4 * arg1[4]
seto r14b; spill OF x190 to reg (r14)
mov [ rsp + 0x4a0 ], rbx; spilling x344 to mem
movzx rbx, byte [ rsp + 0x470 ]; load byte memx203 to register64
mov byte [ rsp + 0x4a8 ], r12b; spilling byte x163 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
adox rbx, r12; loading flag
adox r8, [ rsp + 0x460 ]
seto bl; spill OF x205 to reg (rbx)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r12; loading flag
adox r10, r11
mov rcx, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, rax; x279, swapping with x4, which is currently in rdx
mulx r11, r12, rcx; x298, x297<- x279 * 0x6cfc5fd681c52056
seto cl; spill OF x360 to reg (rcx)
mov [ rsp + 0x4b0 ], r10; spilling x359 to mem
movzx r10, byte [ rsp + 0x458 ]; load byte memx246 to register64
mov byte [ rsp + 0x4b8 ], bl; spilling byte x205 to mem
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r10, rbx; loading flag
adox r8, [ rsp + 0xd0 ]
setc r10b; spill CF x373 to reg (r10)
movzx rbx, byte [ rsp + 0x408 ]; load byte memx273 to register64
clc;
mov byte [ rsp + 0x4c0 ], cl; spilling byte x360 to mem
mov rcx, -0x1 ; moving imm to reg
adcx rbx, rcx; loading flag
adcx r13, [ rsp + 0x3c0 ]
mov rbx, rdx; preserving value of x279 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mulx rbp, rcx, rbp; x253, x252<- x3 * arg1[6]
adcx rcx, r9
mov rdx, 0x7bc65c783158aea3 ; moving imm to reg
mov byte [ rsp + 0x4c8 ], r10b; spilling byte x373 to mem
mulx r9, r10, rdi; x387, x386<- x366 * 0x7bc65c783158aea3
setc dl; spill CF x277 to reg (rdx)
mov [ rsp + 0x4d0 ], r9; spilling x387 to mem
movzx r9, byte [ rsp + 0x468 ]; load byte memx288 to register64
clc;
mov [ rsp + 0x4d8 ], r10; spilling x386 to mem
mov r10, -0x1 ; moving imm to reg
adcx r9, r10; loading flag
adcx r8, r13
seto r9b; spill OF x248 to reg (r9)
movzx r13, byte [ rsp + 0x430 ]; load byte memx414 to register64
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r10, -0x1 ; moving imm to reg
adox r13, r10; loading flag
adox r15, [ rsp + 0x488 ]
setc r13b; spill CF x290 to reg (r13)
movzx r10, byte [ rsp + 0x478 ]; load byte memx316 to register64
clc;
mov [ rsp + 0x4e0 ], r15; spilling x415 to mem
mov r15, -0x1 ; moving imm to reg
adcx r10, r15; loading flag
adcx r12, [ rsp + 0x450 ]
movzx r10, byte [ rsp + 0x4a8 ]; x164, copying x163 here, cause x163 is needed in a reg for other than x164, namely all: , x164, size: 1
movzx r15, byte [ rsp + 0x498 ]; load byte memx120 to register64
lea r10, [ r10 + r15 ]; r64+m8
mov r15, 0x2341f27177344 ; moving imm to reg
xchg rdx, rbx; x279, swapping with x277, which is currently in rdx
mov [ rsp + 0x4e8 ], rbp; spilling x253 to mem
mulx rdx, rbp, r15; x296, x295<- x279 * 0x2341f27177344
setc r15b; spill CF x318 to reg (r15)
mov [ rsp + 0x4f0 ], rdx; spilling x296 to mem
movzx rdx, byte [ rsp + 0x490 ]; load byte memx331 to register64
clc;
mov byte [ rsp + 0x4f8 ], bl; spilling byte x277 to mem
mov rbx, -0x1 ; moving imm to reg
adcx rdx, rbx; loading flag
adcx r8, r12
seto dl; spill OF x416 to reg (rdx)
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, r12; loading flag
adox r11, rbp
movzx r15, r14b; x191, copying x190 here, cause x190 is needed in a reg for other than x191, namely all: , x191, size: 1
mov rbp, [ rsp + 0x448 ]; load m64 x166 to register64
lea r15, [ r15 + rbp ]; r8/64 + m8
seto bpl; spill OF x320 to reg (rbp)
movzx r14, byte [ rsp + 0x4b8 ]; load byte memx205 to register64
inc r12; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov rbx, -0x1 ; moving imm to reg
adox r14, rbx; loading flag
adox r10, r15
setc r14b; spill CF x333 to reg (r14)
clc;
movzx r9, r9b
adcx r9, rbx; loading flag
adcx r10, [ rsp + 0x100 ]
setc r9b; spill CF x250 to reg (r9)
clc;
movzx r13, r13b
adcx r13, rbx; loading flag
adcx r10, rcx
movzx rcx, byte [ rsp + 0x4f8 ]; x278, copying x277 here, cause x277 is needed in a reg for other than x278, namely all: , x278, size: 1
mov r13, [ rsp + 0x4e8 ]; load m64 x253 to register64
lea rcx, [ rcx + r13 ]; r8/64 + m8
seto r13b; spill OF x207 to reg (r13)
movzx r15, byte [ rsp + 0x4c8 ]; load byte memx373 to register64
inc rbx; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov r12, -0x1 ; moving imm to reg
adox r15, r12; loading flag
adox r8, [ rsp + 0x4b0 ]
mov r15, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, rdi; x366, swapping with x416, which is currently in rdx
mulx rbx, r12, r15; x385, x384<- x366 * 0x6cfc5fd681c52056
movzx r15, r9b; x251, copying x250 here, cause x250 is needed in a reg for other than x251, namely all: , x251, size: 1
movzx r13, r13b
lea r15, [ r15 + r13 ]
adcx rcx, r15
mov r13, [ rsp + 0x4d8 ]; load m64 x386 to register64
seto r9b; spill OF x375 to reg (r9)
movzx r15, byte [ rsp + 0x480 ]; load byte memx401 to register64
mov [ rsp + 0x500 ], rbx; spilling x385 to mem
mov rbx, -0x1 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbx, -0x1 ; moving imm to reg
adox r15, rbx; loading flag
adox r13, [ rsp + 0x438 ]
seto r15b; spill OF x403 to reg (r15)
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
movzx rdi, dil
adox rdi, rbx; loading flag
adox r8, r13
movzx rdi, bpl; x321, copying x320 here, cause x320 is needed in a reg for other than x321, namely all: , x321, size: 1
mov r13, [ rsp + 0x4f0 ]; load m64 x296 to register64
lea rdi, [ rdi + r13 ]; r8/64 + m8
setc r13b; spill CF x294 to reg (r13)
clc;
movzx r14, r14b
adcx r14, rbx; loading flag
adcx r10, r11
xchg rdx, rax; x4, swapping with x366, which is currently in rdx
mulx r14, r11, [ rsi + 0x28 ]; x342, x341<- x4 * arg1[5]
seto bpl; spill OF x418 to reg (rbp)
movzx rbx, byte [ rsp + 0x4c0 ]; load byte memx360 to register64
mov [ rsp + 0x508 ], r8; spilling x417 to mem
mov r8, 0x0 ; moving imm to reg
dec r8; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbx, r8; loading flag
adox r11, [ rsp + 0x4a0 ]
adcx rdi, rcx
setc bl; spill CF x337 to reg (rbx)
clc;
movzx r15, r15b
adcx r15, r8; loading flag
adcx r12, [ rsp + 0x4d0 ]
mulx rdx, rcx, [ rsi + 0x30 ]; x340, x339<- x4 * arg1[6]
adox rcx, r14
mov r15, 0x2341f27177344 ; moving imm to reg
xchg rdx, rax; x366, swapping with x340, which is currently in rdx
mulx rdx, r14, r15; x383, x382<- x366 * 0x2341f27177344
mov r8, [ rsi + 0x28 ]; load m64 x5 to register64
mov r15, 0x0 ; moving imm to reg
adox rax, r15
movzx r15, bl; x338, copying x337 here, cause x337 is needed in a reg for other than x338, namely all: , x338, size: 1
movzx r13, r13b
lea r15, [ r15 + r13 ]
mov r13, -0x1 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbx, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, rbx; loading flag
adox r10, r11
adox rcx, rdi
mov r9, [ rsp + 0x500 ]; x406, copying x385 here, cause x385 is needed in a reg for other than x406, namely all: , x406--x407, size: 1
adcx r9, r14
setc r11b; spill CF x407 to reg (r11)
clc;
movzx rbp, bpl
adcx rbp, rbx; loading flag
adcx r10, r12
xchg rdx, r8; x5, swapping with x383, which is currently in rdx
mulx rbp, rdi, [ rsi + 0x0 ]; x439, x438<- x5 * arg1[0]
adcx r9, rcx
movzx r12, r11b; x408, copying x407 here, cause x407 is needed in a reg for other than x408, namely all: , x408, size: 1
lea r12, [ r12 + r8 ]
mulx r8, r14, [ rsi + 0x8 ]; x437, x436<- x5 * arg1[1]
setc cl; spill CF x422 to reg (rcx)
clc;
adcx rdi, [ rsp + 0x320 ]
adox rax, r15
seto r15b; spill OF x381 to reg (r15)
inc rbx; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov r13, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r13; loading flag
adox rax, r12
mulx r11, rcx, [ rsi + 0x10 ]; x435, x434<- x5 * arg1[2]
mov r12, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r12; 0xffffffffffffffff, swapping with x5, which is currently in rdx
mulx rbx, r13, rdi; x480, x479<- x453 * 0xffffffffffffffff
mov rdx, 0xfdc1767ae2ffffff ; moving imm to reg
mov [ rsp + 0x510 ], rax; spilling x423 to mem
mov [ rsp + 0x518 ], r9; spilling x421 to mem
mulx rax, r9, rdi; x476, x475<- x453 * 0xfdc1767ae2ffffff
seto dl; spill OF x424 to reg (rdx)
mov [ rsp + 0x520 ], r10; spilling x419 to mem
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, rbp
mov rbp, [ rsp + 0x420 ]; x455, copying x413 here, cause x413 is needed in a reg for other than x455, namely all: , x455--x456, size: 1
adcx rbp, r14
mov r14, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r14; 0xffffffffffffffff, swapping with x424, which is currently in rdx
mov [ rsp + 0x528 ], rbp; spilling x455 to mem
mulx r10, rbp, rdi; x482, x481<- x453 * 0xffffffffffffffff
adox rcx, r8
movzx r8, r14b; x425, copying x424 here, cause x424 is needed in a reg for other than x425, namely all: , x425, size: 1
movzx r15, r15b
lea r8, [ r8 + r15 ]
mulx r15, r14, rdi; x478, x477<- x453 * 0xffffffffffffffff
setc dl; spill CF x456 to reg (rdx)
clc;
adcx rbp, rdi
seto bpl; spill OF x443 to reg (rbp)
mov [ rsp + 0x530 ], r8; spilling x425 to mem
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, r10
adox r14, rbx
adox r9, r15
mov bl, dl; preserving value of x456 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx r10, r15, r12; x433, x432<- x5 * arg1[3]
setc dl; spill CF x497 to reg (rdx)
clc;
movzx rbp, bpl
adcx rbp, r8; loading flag
adcx r11, r15
mov bpl, dl; preserving value of x497 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r15, r8, r12; x431, x430<- x5 * arg1[4]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x538 ], r15; spilling x431 to mem
mov [ rsp + 0x540 ], r9; spilling x487 to mem
mulx r15, r9, r12; x429, x428<- x5 * arg1[5]
mov rdx, 0x7bc65c783158aea3 ; moving imm to reg
mov [ rsp + 0x548 ], r15; spilling x429 to mem
mov [ rsp + 0x550 ], r9; spilling x428 to mem
mulx r15, r9, rdi; x474, x473<- x453 * 0x7bc65c783158aea3
xchg rdx, r12; x5, swapping with 0x7bc65c783158aea3, which is currently in rdx
mulx rdx, r12, [ rsi + 0x30 ]; x427, x426<- x5 * arg1[6]
adox r9, rax
adcx r8, r10
setc al; spill CF x447 to reg (rax)
clc;
mov r10, -0x1 ; moving imm to reg
movzx rbp, bpl
adcx rbp, r10; loading flag
adcx r13, [ rsp + 0x528 ]
setc bpl; spill CF x499 to reg (rbp)
clc;
movzx rbx, bl
adcx rbx, r10; loading flag
adcx rcx, [ rsp + 0x4e0 ]
mov rbx, 0x2341f27177344 ; moving imm to reg
xchg rdx, rdi; x453, swapping with x427, which is currently in rdx
mov [ rsp + 0x558 ], r13; spilling x498 to mem
mulx r10, r13, rbx; x470, x469<- x453 * 0x2341f27177344
mov rbx, 0x6cfc5fd681c52056 ; moving imm to reg
mov [ rsp + 0x560 ], r10; spilling x470 to mem
mulx rdx, r10, rbx; x472, x471<- x453 * 0x6cfc5fd681c52056
mov rbx, [ rsp + 0x508 ]; x459, copying x417 here, cause x417 is needed in a reg for other than x459, namely all: , x459--x460, size: 1
adcx rbx, r11
setc r11b; spill CF x460 to reg (r11)
clc;
mov [ rsp + 0x568 ], rdi; spilling x427 to mem
mov rdi, -0x1 ; moving imm to reg
movzx rbp, bpl
adcx rbp, rdi; loading flag
adcx rcx, r14
adox r10, r15
adox r13, rdx
mov r14, [ rsi + 0x30 ]; load m64 x6 to register64
setc r15b; spill CF x501 to reg (r15)
clc;
movzx r11, r11b
adcx r11, rdi; loading flag
adcx r8, [ rsp + 0x520 ]
setc bpl; spill CF x462 to reg (rbp)
clc;
movzx r15, r15b
adcx r15, rdi; loading flag
adcx rbx, [ rsp + 0x540 ]
mov rdx, r14; x6 to rdx
mulx r14, r11, [ rsi + 0x8 ]; x524, x523<- x6 * arg1[1]
mov r15, [ rsp + 0x538 ]; load m64 x431 to register64
seto dil; spill OF x494 to reg (rdi)
mov [ rsp + 0x570 ], rbx; spilling x502 to mem
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rax, al
adox rax, rbx; loading flag
adox r15, [ rsp + 0x550 ]
adcx r9, r8
mov rax, [ rsp + 0x548 ]; x450, copying x429 here, cause x429 is needed in a reg for other than x450, namely all: , x450--x451, size: 1
adox rax, r12
mov r12, [ rsp + 0x568 ]; x452, copying x427 here, cause x427 is needed in a reg for other than x452, namely all: , x452, size: 1
mov r8, 0x0 ; moving imm to reg
adox r12, r8
inc rbx; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov r8, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, r8; loading flag
adox r15, [ rsp + 0x518 ]
mov rbp, [ rsp + 0x510 ]; x465, copying x423 here, cause x423 is needed in a reg for other than x465, namely all: , x465--x466, size: 1
adox rbp, rax
adcx r10, r15
mov rax, [ rsp + 0x530 ]; x467, copying x425 here, cause x425 is needed in a reg for other than x467, namely all: , x467--x468, size: 1
adox rax, r12
adcx r13, rbp
movzx r12, dil; x495, copying x494 here, cause x494 is needed in a reg for other than x495, namely all: , x495, size: 1
mov r15, [ rsp + 0x560 ]; load m64 x470 to register64
lea r12, [ r12 + r15 ]; r8/64 + m8
mulx r15, rdi, [ rsi + 0x0 ]; x526, x525<- x6 * arg1[0]
adcx r12, rax
mulx rbp, rax, [ rsi + 0x10 ]; x522, x521<- x6 * arg1[2]
setc r8b; spill CF x511 to reg (r8)
clc;
adcx rdi, [ rsp + 0x558 ]
mov rbx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rdi; x540, swapping with x6, which is currently in rdx
mov [ rsp + 0x578 ], r12; spilling x510 to mem
mov [ rsp + 0x580 ], r13; spilling x508 to mem
mulx r12, r13, rbx; x565, x564<- x540 * 0xffffffffffffffff
movzx rbx, r8b; x512, copying x511 here, cause x511 is needed in a reg for other than x512, namely all: , x512, size: 1
mov [ rsp + 0x588 ], r12; spilling x565 to mem
mov r12, 0x0 ; moving imm to reg
adox rbx, r12
mov r8, 0xfdc1767ae2ffffff ; moving imm to reg
mov [ rsp + 0x590 ], rbx; spilling x512 to mem
mulx r12, rbx, r8; x563, x562<- x540 * 0xfdc1767ae2ffffff
mov r8, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x598 ], r12; spilling x563 to mem
mov [ rsp + 0x5a0 ], rbx; spilling x562 to mem
mulx r12, rbx, r8; x569, x568<- x540 * 0xffffffffffffffff
mov [ rsp + 0x5a8 ], r10; spilling x506 to mem
mov [ rsp + 0x5b0 ], r9; spilling x504 to mem
mulx r10, r9, r8; x567, x566<- x540 * 0xffffffffffffffff
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, r15
adox rax, r14
adcx r11, rcx
seto cl; spill OF x530 to reg (rcx)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rbx, rdx
mov rbx, 0x7bc65c783158aea3 ; moving imm to reg
mulx r14, r15, rbx; x561, x560<- x540 * 0x7bc65c783158aea3
mov r8, [ rsp + 0x570 ]; x544, copying x502 here, cause x502 is needed in a reg for other than x544, namely all: , x544--x545, size: 1
adcx r8, rax
setc al; spill CF x545 to reg (rax)
clc;
adcx r9, r12
xchg rdx, rdi; x6, swapping with x540, which is currently in rdx
mulx r12, rbx, [ rsi + 0x30 ]; x514, x513<- x6 * arg1[6]
adcx r13, r10
mov [ rsp + 0x5b8 ], r12; spilling x514 to mem
mulx r10, r12, [ rsi + 0x18 ]; x520, x519<- x6 * arg1[3]
adox r9, r11
adox r13, r8
setc r11b; spill CF x573 to reg (r11)
clc;
mov r8, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, r8; loading flag
adcx rbp, r12
setc cl; spill CF x532 to reg (rcx)
seto r12b; spill OF x588 to reg (r12)
mov r8, r9; x600, copying x585 here, cause x585 is needed in a reg for other than x600, namely all: , x600--x601, x616, size: 2
mov [ rsp + 0x5c0 ], rbx; spilling x513 to mem
mov rbx, 0xffffffffffffffff ; moving imm to reg
sub r8, rbx
mov rbx, -0x1 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbx, -0x1 ; moving imm to reg
movzx rax, al
adox rax, rbx; loading flag
adox rbp, [ rsp + 0x5b0 ]
mulx rax, rbx, [ rsi + 0x20 ]; x518, x517<- x6 * arg1[4]
mov [ rsp + 0x5c8 ], r8; spilling x600 to mem
mulx rdx, r8, [ rsi + 0x28 ]; x516, x515<- x6 * arg1[5]
mov [ rsp + 0x5d0 ], rdx; spilling x516 to mem
setc dl; spill CF x601 to reg (rdx)
clc;
mov [ rsp + 0x5d8 ], r14; spilling x561 to mem
mov r14, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, r14; loading flag
adcx r10, rbx
mov rcx, [ rsp + 0x5a8 ]; x548, copying x506 here, cause x506 is needed in a reg for other than x548, namely all: , x548--x549, size: 1
adox rcx, r10
mov rbx, [ rsp + 0x5a0 ]; load m64 x562 to register64
setc r10b; spill CF x534 to reg (r10)
clc;
movzx r11, r11b
adcx r11, r14; loading flag
adcx rbx, [ rsp + 0x588 ]
mov r11, [ rsp + 0x598 ]; x576, copying x563 here, cause x563 is needed in a reg for other than x576, namely all: , x576--x577, size: 1
adcx r11, r15
setc r15b; spill CF x577 to reg (r15)
clc;
movzx r12, r12b
adcx r12, r14; loading flag
adcx rbp, rbx
mov r12, 0x2341f27177344 ; moving imm to reg
xchg rdx, rdi; x540, swapping with x601, which is currently in rdx
mulx rbx, r14, r12; x557, x556<- x540 * 0x2341f27177344
setc r12b; spill CF x590 to reg (r12)
mov [ rsp + 0x5e0 ], rbx; spilling x557 to mem
seto bl; spill OF x549 to reg (rbx)
mov [ rsp + 0x5e8 ], r14; spilling x556 to mem
movzx r14, dil; x601, copying x601 here, cause x601 is needed in a reg for other than x601, namely all: , x602--x603, size: 1
add r14, -0x1
mov r14, r13; x602, copying x587 here, cause x587 is needed in a reg for other than x602, namely all: , x602--x603, x617, size: 2
mov [ rsp + 0x5f0 ], r11; spilling x576 to mem
mov r11, 0xffffffffffffffff ; moving imm to reg
sbb r14, r11
mov [ rsp + 0x5f8 ], r14; spilling x602 to mem
mov r14, rbp; x604, copying x589 here, cause x589 is needed in a reg for other than x604, namely all: , x604--x605, x618, size: 2
sbb r14, r11
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
movzx r10, r10b
adox r10, r11; loading flag
adox rax, r8
mov r8, 0x6cfc5fd681c52056 ; moving imm to reg
mulx rdx, r10, r8; x559, x558<- x540 * 0x6cfc5fd681c52056
setc r11b; spill CF x605 to reg (r11)
clc;
mov r8, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, r8; loading flag
adcx r10, [ rsp + 0x5d8 ]
setc r15b; spill CF x579 to reg (r15)
clc;
movzx r12, r12b
adcx r12, r8; loading flag
adcx rcx, [ rsp + 0x5f0 ]
mov r12, [ rsp + 0x5d0 ]; load m64 x516 to register64
mov r8, [ rsp + 0x5c0 ]; x537, copying x513 here, cause x513 is needed in a reg for other than x537, namely all: , x537--x538, size: 1
adox r8, r12
mov r12, [ rsp + 0x5b8 ]; x539, copying x514 here, cause x514 is needed in a reg for other than x539, namely all: , x539, size: 1
mov [ rsp + 0x600 ], r14; spilling x604 to mem
mov r14, 0x0 ; moving imm to reg
adox r12, r14
dec r14; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r15, r15b
adox r15, r14; loading flag
adox rdx, [ rsp + 0x5e8 ]
setc r15b; spill CF x592 to reg (r15)
seto r14b; spill OF x581 to reg (r14)
mov [ rsp + 0x608 ], rdx; spilling x580 to mem
movzx rdx, r11b; x605, copying x605 here, cause x605 is needed in a reg for other than x605, namely all: , x606--x607, size: 1
add rdx, -0x1
mov r11, rcx; x606, copying x591 here, cause x591 is needed in a reg for other than x606, namely all: , x619, x606--x607, size: 2
mov rdx, 0xfdc1767ae2ffffff ; moving imm to reg
sbb r11, rdx
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, rdx; loading flag
adox rax, [ rsp + 0x580 ]
mov rbx, [ rsp + 0x578 ]; x552, copying x510 here, cause x510 is needed in a reg for other than x552, namely all: , x552--x553, size: 1
adox rbx, r8
mov r8, [ rsp + 0x590 ]; x554, copying x512 here, cause x512 is needed in a reg for other than x554, namely all: , x554--x555, size: 1
adox r8, r12
setc r12b; spill CF x607 to reg (r12)
clc;
movzx r15, r15b
adcx r15, rdx; loading flag
adcx rax, r10
movzx r10, r14b; x582, copying x581 here, cause x581 is needed in a reg for other than x582, namely all: , x582, size: 1
mov r15, [ rsp + 0x5e0 ]; load m64 x557 to register64
lea r10, [ r10 + r15 ]; r8/64 + m8
mov r15, [ rsp + 0x608 ]; x595, copying x580 here, cause x580 is needed in a reg for other than x595, namely all: , x595--x596, size: 1
adcx r15, rbx
adcx r10, r8
setc r14b; spill CF x598 to reg (r14)
seto bl; spill OF x555 to reg (rbx)
movzx r8, r12b; x607, copying x607 here, cause x607 is needed in a reg for other than x607, namely all: , x608--x609, size: 1
add r8, -0x1
mov r12, rax; x608, copying x593 here, cause x593 is needed in a reg for other than x608, namely all: , x608--x609, x620, size: 2
mov r8, 0x7bc65c783158aea3 ; moving imm to reg
sbb r12, r8
movzx rdx, r14b; x599, copying x598 here, cause x598 is needed in a reg for other than x599, namely all: , x599, size: 1
movzx rbx, bl
lea rdx, [ rdx + rbx ]
mov rbx, r15; x610, copying x595 here, cause x595 is needed in a reg for other than x610, namely all: , x621, x610--x611, size: 2
mov r14, 0x6cfc5fd681c52056 ; moving imm to reg
sbb rbx, r14
mov r8, r10; x612, copying x597 here, cause x597 is needed in a reg for other than x612, namely all: , x622, x612--x613, size: 2
mov r14, 0x2341f27177344 ; moving imm to reg
sbb r8, r14
sbb rdx, 0x00000000
cmovc r12, rax; if CF, x620<- x593 (nzVar)
mov rdx, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rdx + 0x20 ], r12; out1[4] = x620
mov rax, [ rsp + 0x5f8 ]; x617, copying x602 here, cause x602 is needed in a reg for other than x617, namely all: , x617, size: 1
cmovc rax, r13; if CF, x617<- x587 (nzVar)
cmovc r11, rcx; if CF, x619<- x591 (nzVar)
cmovc rbx, r15; if CF, x621<- x595 (nzVar)
mov r13, [ rsp + 0x5c8 ]; x616, copying x600 here, cause x600 is needed in a reg for other than x616, namely all: , x616, size: 1
cmovc r13, r9; if CF, x616<- x585 (nzVar)
mov [ rdx + 0x8 ], rax; out1[1] = x617
mov [ rdx + 0x18 ], r11; out1[3] = x619
mov r9, [ rsp + 0x600 ]; x618, copying x604 here, cause x604 is needed in a reg for other than x618, namely all: , x618, size: 1
cmovc r9, rbp; if CF, x618<- x589 (nzVar)
cmovc r8, r10; if CF, x622<- x597 (nzVar)
mov [ rdx + 0x28 ], rbx; out1[5] = x621
mov [ rdx + 0x0 ], r13; out1[0] = x616
mov [ rdx + 0x10 ], r9; out1[2] = x618
mov [ rdx + 0x30 ], r8; out1[6] = x622
mov rbx, [ rsp + 0x610 ]; restoring from stack
mov rbp, [ rsp + 0x618 ]; restoring from stack
mov r12, [ rsp + 0x620 ]; restoring from stack
mov r13, [ rsp + 0x628 ]; restoring from stack
mov r14, [ rsp + 0x630 ]; restoring from stack
mov r15, [ rsp + 0x638 ]; restoring from stack
add rsp, 0x640 
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; clocked at 2200 MHz
; first cyclecount 321.67, best 280.41379310344826, lastGood 286.26666666666665
; seed 699744043147816 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5442407 ms / 60000 runs=> 90.70678333333333ms/run
; Time spent for assembling and measureing (initial batch_size=30, initial num_batches=101): 138767 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.025497358062342636
; number reverted permutation/ tried permutation: 18034 / 29927 =60.260%
; number reverted decision/ tried decision: 17086 / 30074 =56.813%