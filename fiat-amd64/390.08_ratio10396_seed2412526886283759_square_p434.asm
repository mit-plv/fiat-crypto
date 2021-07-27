SECTION .text
	GLOBAL square_p434
square_p434:
sub rsp, 0x568 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x538 ], rbx; saving to stack
mov [ rsp + 0x540 ], rbp; saving to stack
mov [ rsp + 0x548 ], r12; saving to stack
mov [ rsp + 0x550 ], r13; saving to stack
mov [ rsp + 0x558 ], r14; saving to stack
mov [ rsp + 0x560 ], r15; saving to stack
mov rax, [ rsi + 0x10 ]; load m64 x2 to register64
mov rdx, rax; x2 to rdx
mulx rax, r10, [ rsi + 0x0 ]; x178, x177<- x2 * arg1[0]
mulx r11, rbx, [ rsi + 0x10 ]; x174, x173<- x2 * arg1[2]
mulx rbp, r12, [ rsi + 0x30 ]; x166, x165<- x2 * arg1[6]
mulx r13, r14, [ rsi + 0x8 ]; x176, x175<- x2 * arg1[1]
mov r15, [ rsi + 0x0 ]; load m64 x7 to register64
mulx rcx, r8, [ rsi + 0x28 ]; x168, x167<- x2 * arg1[5]
xor r9, r9
adox r14, rax
adox rbx, r13
mulx rax, r13, [ rsi + 0x18 ]; x172, x171<- x2 * arg1[3]
adox r13, r11
mov r11, [ rsi + 0x20 ]; load m64 x4 to register64
mulx rdx, r9, [ rsi + 0x20 ]; x170, x169<- x2 * arg1[4]
adox r9, rax
adox r8, rdx
mov rdx, r15; x7 to rdx
mulx r15, rax, [ rsi + 0x0 ]; x21, x20<- x7 * arg1[0]
adox r12, rcx
mov rcx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rax; x20, swapping with x7, which is currently in rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov [ rsp + 0x8 ], r12; spilling x189 to mem
mulx rdi, r12, rcx; x46, x45<- x20 * 0xffffffffffffffff
mov rcx, 0x0 ; moving imm to reg
adox rbp, rcx
mov rcx, 0xfdc1767ae2ffffff ; moving imm to reg
mov [ rsp + 0x10 ], rbp; spilling x191 to mem
mov [ rsp + 0x18 ], r8; spilling x187 to mem
mulx rbp, r8, rcx; x42, x41<- x20 * 0xfdc1767ae2ffffff
mov rcx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x20 ], r9; spilling x185 to mem
mov [ rsp + 0x28 ], r13; spilling x183 to mem
mulx r9, r13, rcx; x48, x47<- x20 * 0xffffffffffffffff
mov [ rsp + 0x30 ], rbx; spilling x181 to mem
mov [ rsp + 0x38 ], r14; spilling x179 to mem
mulx rbx, r14, rcx; x44, x43<- x20 * 0xffffffffffffffff
mov rcx, 0x6cfc5fd681c52056 ; moving imm to reg
mov [ rsp + 0x40 ], r10; spilling x177 to mem
mov [ rsp + 0x48 ], r15; spilling x21 to mem
mulx r10, r15, rcx; x38, x37<- x20 * 0x6cfc5fd681c52056
adcx r12, r9
adcx r14, rdi
adcx r8, rbx
mov rdi, 0x7bc65c783158aea3 ; moving imm to reg
mulx r9, rbx, rdi; x40, x39<- x20 * 0x7bc65c783158aea3
mov rdi, rdx; preserving value of x20 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x50 ], r8; spilling x53 to mem
mulx rcx, r8, rax; x19, x18<- x7 * arg1[1]
adcx rbx, rbp
mov rdx, 0x2341f27177344 ; moving imm to reg
mov [ rsp + 0x58 ], rbx; spilling x55 to mem
mulx rbp, rbx, rdi; x36, x35<- x20 * 0x2341f27177344
xchg rdx, r11; x4, swapping with 0x2341f27177344, which is currently in rdx
mov [ rsp + 0x60 ], r14; spilling x51 to mem
mulx r11, r14, [ rsi + 0x8 ]; x350, x349<- x4 * arg1[1]
mov [ rsp + 0x68 ], r12; spilling x49 to mem
mov r12, [ rsi + 0x8 ]; load m64 x1 to register64
mov [ rsp + 0x70 ], r12; spilling x1 to mem
mov [ rsp + 0x78 ], rcx; spilling x19 to mem
mulx r12, rcx, [ rsi + 0x10 ]; x348, x347<- x4 * arg1[2]
adcx r15, r9
mov [ rsp + 0x80 ], r15; spilling x57 to mem
mulx r9, r15, [ rsi + 0x0 ]; x352, x351<- x4 * arg1[0]
mov [ rsp + 0x88 ], r15; spilling x351 to mem
mov [ rsp + 0x90 ], r12; spilling x348 to mem
mulx r15, r12, [ rsi + 0x18 ]; x346, x345<- x4 * arg1[3]
adcx rbx, r10
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, r9
mov r9, 0x0 ; moving imm to reg
adcx rbp, r9
mulx r9, r10, [ rsi + 0x28 ]; x342, x341<- x4 * arg1[5]
adox rcx, r11
clc;
adcx r13, rdi
setc r13b; spill CF x63 to reg (r13)
clc;
adcx r8, [ rsp + 0x48 ]
mulx rdi, r11, [ rsi + 0x20 ]; x344, x343<- x4 * arg1[4]
mov [ rsp + 0x98 ], rcx; spilling x355 to mem
mulx rdx, rcx, [ rsi + 0x30 ]; x340, x339<- x4 * arg1[6]
mov [ rsp + 0xa0 ], r14; spilling x353 to mem
mov r14, rdx; preserving value of x340 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0xa8 ], rbp; spilling x61 to mem
mov [ rsp + 0xb0 ], rbx; spilling x59 to mem
mulx rbp, rbx, rax; x17, x16<- x7 * arg1[2]
mov rdx, [ rsp + 0x90 ]; x357, copying x348 here, cause x348 is needed in a reg for other than x357, namely all: , x357--x358, size: 1
adox rdx, r12
adox r11, r15
adox r10, rdi
mov r15, [ rsp + 0x78 ]; x24, copying x19 here, cause x19 is needed in a reg for other than x24, namely all: , x24--x25, size: 1
adcx r15, rbx
seto r12b; spill OF x362 to reg (r12)
mov rdi, 0x0 ; moving imm to reg
dec rdi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r13, r13b
adox r13, rdi; loading flag
adox r8, [ rsp + 0x68 ]
mov r13, [ rsp + 0x60 ]; x66, copying x51 here, cause x51 is needed in a reg for other than x66, namely all: , x66--x67, size: 1
adox r13, r15
mov rbx, rdx; preserving value of x357 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r15, rdi, [ rsp + 0x70 ]; x87, x86<- x1 * arg1[2]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0xb8 ], r10; spilling x361 to mem
mov [ rsp + 0xc0 ], r11; spilling x359 to mem
mulx r10, r11, [ rsp + 0x70 ]; x91, x90<- x1 * arg1[0]
setc dl; spill CF x25 to reg (rdx)
clc;
mov [ rsp + 0xc8 ], rbx; spilling x357 to mem
mov rbx, -0x1 ; moving imm to reg
movzx r12, r12b
adcx r12, rbx; loading flag
adcx r9, rcx
seto cl; spill OF x67 to reg (rcx)
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r11, r8
mov r12b, dl; preserving value of x25 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r8, rbx, [ rsp + 0x70 ]; x89, x88<- x1 * arg1[1]
setc dl; spill CF x364 to reg (rdx)
clc;
adcx rbx, r10
movzx r10, dl; x365, copying x364 here, cause x364 is needed in a reg for other than x365, namely all: , x365, size: 1
lea r10, [ r10 + r14 ]
mov r14, 0xffffffffffffffff ; moving imm to reg
mov rdx, r11; x105 to rdx
mov [ rsp + 0xd0 ], r10; spilling x365 to mem
mulx r11, r10, r14; x134, x133<- x105 * 0xffffffffffffffff
adox rbx, r13
mov [ rsp + 0xd8 ], r9; spilling x363 to mem
mulx r13, r9, r14; x132, x131<- x105 * 0xffffffffffffffff
adcx rdi, r8
setc r8b; spill CF x95 to reg (r8)
clc;
adcx r9, r11
setc r11b; spill CF x136 to reg (r11)
clc;
adcx r10, rdx
mov [ rsp + 0xe0 ], r15; spilling x87 to mem
mulx r10, r15, r14; x130, x129<- x105 * 0xffffffffffffffff
mov r14, rdx; preserving value of x105 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0xe8 ], r10; spilling x130 to mem
mov byte [ rsp + 0xf0 ], r8b; spilling byte x95 to mem
mulx r10, r8, rax; x15, x14<- x7 * arg1[3]
adcx r9, rbx
setc dl; spill CF x151 to reg (rdx)
clc;
mov rbx, -0x1 ; moving imm to reg
movzx r12, r12b
adcx r12, rbx; loading flag
adcx rbp, r8
setc r12b; spill CF x27 to reg (r12)
clc;
movzx rcx, cl
adcx rcx, rbx; loading flag
adcx rbp, [ rsp + 0x50 ]
seto cl; spill OF x108 to reg (rcx)
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r9, [ rsp + 0x40 ]
mov r8, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r9; x192, swapping with x151, which is currently in rdx
mov [ rsp + 0xf8 ], r10; spilling x15 to mem
mulx rbx, r10, r8; x221, x220<- x192 * 0xffffffffffffffff
seto r8b; spill OF x193 to reg (r8)
mov byte [ rsp + 0x100 ], r12b; spilling byte x27 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, r12; loading flag
adox r13, r15
mov r11, 0xffffffffffffffff ; moving imm to reg
mulx r15, r12, r11; x219, x218<- x192 * 0xffffffffffffffff
mov r11, [ rsi + 0x18 ]; load m64 x3 to register64
mov [ rsp + 0x108 ], r15; spilling x219 to mem
seto r15b; spill OF x138 to reg (r15)
mov [ rsp + 0x110 ], r11; spilling x3 to mem
mov r11, -0x2 ; moving imm to reg
inc r11; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, rbx
seto bl; spill OF x223 to reg (rbx)
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r10, rdx
setc r10b; spill CF x69 to reg (r10)
clc;
mov r11, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, r11; loading flag
adcx rbp, rdi
setc cl; spill CF x110 to reg (rcx)
clc;
movzx r9, r9b
adcx r9, r11; loading flag
adcx rbp, r13
setc dil; spill CF x153 to reg (rdi)
clc;
movzx r8, r8b
adcx r8, r11; loading flag
adcx rbp, [ rsp + 0x38 ]
adox r12, rbp
mov r9, rdx; preserving value of x192 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r8, r13, [ rsp + 0x110 ]; x265, x264<- x3 * arg1[0]
setc dl; spill CF x195 to reg (rdx)
clc;
adcx r13, r12
mov rbp, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, r13; x279, swapping with x195, which is currently in rdx
mulx r12, r11, rbp; x298, x297<- x279 * 0x6cfc5fd681c52056
mov rbp, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x118 ], r8; spilling x265 to mem
mov byte [ rsp + 0x120 ], r13b; spilling byte x195 to mem
mulx r8, r13, rbp; x308, x307<- x279 * 0xffffffffffffffff
mov rbp, 0x7bc65c783158aea3 ; moving imm to reg
mov [ rsp + 0x128 ], r13; spilling x307 to mem
mov byte [ rsp + 0x130 ], dil; spilling byte x153 to mem
mulx r13, rdi, rbp; x300, x299<- x279 * 0x7bc65c783158aea3
mov rbp, 0xffffffffffffffff ; moving imm to reg
mov byte [ rsp + 0x138 ], cl; spilling byte x110 to mem
mov byte [ rsp + 0x140 ], r10b; spilling byte x69 to mem
mulx rcx, r10, rbp; x306, x305<- x279 * 0xffffffffffffffff
setc bpl; spill CF x280 to reg (rbp)
clc;
adcx r10, r8
mov r8, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x148 ], r10; spilling x309 to mem
mov byte [ rsp + 0x150 ], bpl; spilling byte x280 to mem
mulx r10, rbp, r8; x304, x303<- x279 * 0xffffffffffffffff
mov r8, 0xfdc1767ae2ffffff ; moving imm to reg
mov byte [ rsp + 0x158 ], r15b; spilling byte x138 to mem
mov byte [ rsp + 0x160 ], bl; spilling byte x223 to mem
mulx r15, rbx, r8; x302, x301<- x279 * 0xfdc1767ae2ffffff
adcx rbp, rcx
adcx rbx, r10
mov rcx, rdx; preserving value of x279 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx r10, r8, [ rsp + 0x70 ]; x85, x84<- x1 * arg1[3]
adcx rdi, r15
mov rdx, 0x2341f27177344 ; moving imm to reg
mov [ rsp + 0x168 ], rdi; spilling x315 to mem
mulx r15, rdi, rcx; x296, x295<- x279 * 0x2341f27177344
adcx r11, r13
adcx rdi, r12
mov r12, rdx; preserving value of 0x2341f27177344 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x170 ], rdi; spilling x319 to mem
mulx r13, rdi, rax; x13, x12<- x7 * arg1[4]
mov rdx, 0xfdc1767ae2ffffff ; moving imm to reg
mov [ rsp + 0x178 ], r11; spilling x317 to mem
mulx r12, r11, r14; x128, x127<- x105 * 0xfdc1767ae2ffffff
mov rdx, 0x0 ; moving imm to reg
adcx r15, rdx
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x180 ], r15; spilling x321 to mem
mov [ rsp + 0x188 ], rbx; spilling x313 to mem
mulx r15, rbx, r9; x217, x216<- x192 * 0xffffffffffffffff
mov [ rsp + 0x190 ], rbp; spilling x311 to mem
mov rbp, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x198 ], r15; spilling x217 to mem
mov [ rsp + 0x1a0 ], r12; spilling x128 to mem
mulx r15, r12, [ rsp + 0x70 ]; x83, x82<- x1 * arg1[4]
movzx rdx, byte [ rsp + 0x100 ]; load byte memx27 to register64
clc;
mov rbp, -0x1 ; moving imm to reg
adcx rdx, rbp; loading flag
adcx rdi, [ rsp + 0xf8 ]
setc dl; spill CF x29 to reg (rdx)
movzx rbp, byte [ rsp + 0x160 ]; load byte memx223 to register64
clc;
mov [ rsp + 0x1a8 ], r15; spilling x83 to mem
mov r15, -0x1 ; moving imm to reg
adcx rbp, r15; loading flag
adcx rbx, [ rsp + 0x108 ]
setc bpl; spill CF x225 to reg (rbp)
movzx r15, byte [ rsp + 0xf0 ]; load byte memx95 to register64
clc;
mov [ rsp + 0x1b0 ], rbx; spilling x224 to mem
mov rbx, -0x1 ; moving imm to reg
adcx r15, rbx; loading flag
adcx r8, [ rsp + 0xe0 ]
seto r15b; spill OF x238 to reg (r15)
movzx rbx, byte [ rsp + 0x158 ]; load byte memx138 to register64
mov byte [ rsp + 0x1b8 ], bpl; spilling byte x225 to mem
mov rbp, -0x1 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
adox rbx, rbp; loading flag
adox r11, [ rsp + 0xe8 ]
setc bl; spill CF x97 to reg (rbx)
movzx rbp, byte [ rsp + 0x140 ]; load byte memx69 to register64
clc;
mov byte [ rsp + 0x1c0 ], r15b; spilling byte x238 to mem
mov r15, -0x1 ; moving imm to reg
adcx rbp, r15; loading flag
adcx rdi, [ rsp + 0x58 ]
setc bpl; spill CF x71 to reg (rbp)
movzx r15, byte [ rsp + 0x138 ]; load byte memx110 to register64
clc;
mov [ rsp + 0x1c8 ], r13; spilling x13 to mem
mov r13, -0x1 ; moving imm to reg
adcx r15, r13; loading flag
adcx rdi, r8
setc r15b; spill CF x112 to reg (r15)
movzx r8, byte [ rsp + 0x130 ]; load byte memx153 to register64
clc;
adcx r8, r13; loading flag
adcx rdi, r11
xchg rdx, rax; x7, swapping with x29, which is currently in rdx
mulx r8, r11, [ rsi + 0x28 ]; x11, x10<- x7 * arg1[5]
setc r13b; spill CF x155 to reg (r13)
clc;
mov [ rsp + 0x1d0 ], r8; spilling x11 to mem
mov r8, -0x1 ; moving imm to reg
movzx rbx, bl
adcx rbx, r8; loading flag
adcx r10, r12
setc r12b; spill CF x99 to reg (r12)
clc;
movzx rax, al
adcx rax, r8; loading flag
adcx r11, [ rsp + 0x1c8 ]
setc al; spill CF x31 to reg (rax)
movzx rbx, byte [ rsp + 0x120 ]; load byte memx195 to register64
clc;
adcx rbx, r8; loading flag
adcx rdi, [ rsp + 0x30 ]
mov rbx, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, rbx; 0x7bc65c783158aea3, swapping with x7, which is currently in rdx
mov byte [ rsp + 0x1d8 ], r12b; spilling byte x99 to mem
mulx r8, r12, r14; x126, x125<- x105 * 0x7bc65c783158aea3
mov rdx, 0x6cfc5fd681c52056 ; moving imm to reg
mov [ rsp + 0x1e0 ], r8; spilling x126 to mem
mov byte [ rsp + 0x1e8 ], al; spilling byte x31 to mem
mulx r8, rax, r14; x124, x123<- x105 * 0x6cfc5fd681c52056
mov rdx, 0xfdc1767ae2ffffff ; moving imm to reg
mov [ rsp + 0x1f0 ], r8; spilling x124 to mem
mov [ rsp + 0x1f8 ], rax; spilling x123 to mem
mulx r8, rax, r9; x215, x214<- x192 * 0xfdc1767ae2ffffff
mov rdx, [ rsp + 0x1a0 ]; x141, copying x128 here, cause x128 is needed in a reg for other than x141, namely all: , x141--x142, size: 1
adox rdx, r12
seto r12b; spill OF x142 to reg (r12)
mov [ rsp + 0x200 ], r8; spilling x215 to mem
mov r8, 0x0 ; moving imm to reg
dec r8; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbp, bpl
adox rbp, r8; loading flag
adox r11, [ rsp + 0x80 ]
mov rbp, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, r9; x192, swapping with x141, which is currently in rdx
mov byte [ rsp + 0x208 ], r12b; spilling byte x142 to mem
mulx r8, r12, rbp; x213, x212<- x192 * 0x7bc65c783158aea3
xchg rdx, rbx; x7, swapping with x192, which is currently in rdx
mulx rdx, rbp, [ rsi + 0x30 ]; x9, x8<- x7 * arg1[6]
mov [ rsp + 0x210 ], r8; spilling x213 to mem
setc r8b; spill CF x197 to reg (r8)
mov [ rsp + 0x218 ], r12; spilling x212 to mem
movzx r12, byte [ rsp + 0x1b8 ]; load byte memx225 to register64
clc;
mov [ rsp + 0x220 ], rdx; spilling x9 to mem
mov rdx, -0x1 ; moving imm to reg
adcx r12, rdx; loading flag
adcx rax, [ rsp + 0x198 ]
setc r12b; spill CF x227 to reg (r12)
clc;
movzx r15, r15b
adcx r15, rdx; loading flag
adcx r11, r10
setc r15b; spill CF x114 to reg (r15)
clc;
movzx r13, r13b
adcx r13, rdx; loading flag
adcx r11, r9
seto r13b; spill OF x73 to reg (r13)
movzx r10, byte [ rsp + 0x1c0 ]; load byte memx238 to register64
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
adox r10, r9; loading flag
adox rdi, [ rsp + 0x1b0 ]
setc r10b; spill CF x157 to reg (r10)
clc;
movzx r8, r8b
adcx r8, r9; loading flag
adcx r11, [ rsp + 0x28 ]
adox rax, r11
seto r8b; spill OF x242 to reg (r8)
movzx r11, byte [ rsp + 0x1e8 ]; load byte memx31 to register64
dec rdx; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
adox r11, rdx; loading flag
adox rbp, [ rsp + 0x1d0 ]
mov rdx, [ rsp + 0x70 ]; x1 to rdx
mulx r9, r11, [ rsi + 0x28 ]; x81, x80<- x1 * arg1[5]
mov [ rsp + 0x228 ], rax; spilling x241 to mem
seto al; spill OF x33 to reg (rax)
mov [ rsp + 0x230 ], rdi; spilling x239 to mem
mov rdi, 0x0 ; moving imm to reg
dec rdi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r13, r13b
adox r13, rdi; loading flag
adox rbp, [ rsp + 0xb0 ]
mov r13, [ rsp + 0x1f8 ]; load m64 x123 to register64
setc dil; spill CF x199 to reg (rdi)
mov byte [ rsp + 0x238 ], r8b; spilling byte x242 to mem
movzx r8, byte [ rsp + 0x208 ]; load byte memx142 to register64
clc;
mov byte [ rsp + 0x240 ], r12b; spilling byte x227 to mem
mov r12, -0x1 ; moving imm to reg
adcx r8, r12; loading flag
adcx r13, [ rsp + 0x1e0 ]
setc r8b; spill CF x144 to reg (r8)
movzx r12, byte [ rsp + 0x1d8 ]; load byte memx99 to register64
clc;
mov byte [ rsp + 0x248 ], dil; spilling byte x199 to mem
mov rdi, -0x1 ; moving imm to reg
adcx r12, rdi; loading flag
adcx r11, [ rsp + 0x1a8 ]
setc r12b; spill CF x101 to reg (r12)
clc;
movzx r15, r15b
adcx r15, rdi; loading flag
adcx rbp, r11
mulx rdx, r15, [ rsi + 0x30 ]; x79, x78<- x1 * arg1[6]
setc r11b; spill CF x116 to reg (r11)
clc;
movzx r10, r10b
adcx r10, rdi; loading flag
adcx rbp, r13
setc r10b; spill CF x159 to reg (r10)
clc;
movzx r12, r12b
adcx r12, rdi; loading flag
adcx r9, r15
mov r13, 0x2341f27177344 ; moving imm to reg
xchg rdx, r14; x105, swapping with x79, which is currently in rdx
mulx rdx, r12, r13; x122, x121<- x105 * 0x2341f27177344
movzx r15, al; x34, copying x33 here, cause x33 is needed in a reg for other than x34, namely all: , x34, size: 1
mov rdi, [ rsp + 0x220 ]; load m64 x9 to register64
lea r15, [ r15 + rdi ]; r8/64 + m8
setc dil; spill CF x103 to reg (rdi)
movzx rax, byte [ rsp + 0x248 ]; load byte memx199 to register64
clc;
mov r13, -0x1 ; moving imm to reg
adcx rax, r13; loading flag
adcx rbp, [ rsp + 0x20 ]
mov rax, [ rsp + 0xa8 ]; x76, copying x61 here, cause x61 is needed in a reg for other than x76, namely all: , x76--x77, size: 1
adox rax, r15
setc r15b; spill CF x201 to reg (r15)
clc;
movzx r8, r8b
adcx r8, r13; loading flag
adcx r12, [ rsp + 0x1f0 ]
setc r8b; spill CF x146 to reg (r8)
clc;
movzx r11, r11b
adcx r11, r13; loading flag
adcx rax, r9
mov r11, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, rbx; x192, swapping with x122, which is currently in rdx
mulx r9, r13, r11; x211, x210<- x192 * 0x6cfc5fd681c52056
movzx r11, dil; x104, copying x103 here, cause x103 is needed in a reg for other than x104, namely all: , x104, size: 1
lea r11, [ r11 + r14 ]
setc r14b; spill CF x118 to reg (r14)
clc;
mov rdi, -0x1 ; moving imm to reg
movzx r10, r10b
adcx r10, rdi; loading flag
adcx rax, r12
movzx r10, r8b; x147, copying x146 here, cause x146 is needed in a reg for other than x147, namely all: , x147, size: 1
lea r10, [ r10 + rbx ]
mov rbx, [ rsp + 0x200 ]; load m64 x215 to register64
setc r12b; spill CF x161 to reg (r12)
movzx r8, byte [ rsp + 0x240 ]; load byte memx227 to register64
clc;
adcx r8, rdi; loading flag
adcx rbx, [ rsp + 0x218 ]
mov r8, [ rsp + 0x210 ]; x230, copying x213 here, cause x213 is needed in a reg for other than x230, namely all: , x230--x231, size: 1
adcx r8, r13
mov r13, 0x2341f27177344 ; moving imm to reg
mulx rdx, rdi, r13; x209, x208<- x192 * 0x2341f27177344
movzx r13, r14b; x119, copying x118 here, cause x118 is needed in a reg for other than x119, namely all: , x119--x120, size: 1
adox r13, r11
adcx rdi, r9
seto r14b; spill OF x120 to reg (r14)
mov r9, -0x1 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, r11; loading flag
adox rax, [ rsp + 0x18 ]
adcx rdx, r9
clc;
movzx r12, r12b
adcx r12, r11; loading flag
adcx r13, r10
movzx r15, r14b; x164, copying x120 here, cause x120 is needed in a reg for other than x164, namely all: , x164, size: 1
adcx r15, r9
mov r12, [ rsp + 0x8 ]; x204, copying x189 here, cause x189 is needed in a reg for other than x204, namely all: , x204--x205, size: 1
adox r12, r13
movzx r10, byte [ rsp + 0x238 ]; load byte memx242 to register64
clc;
adcx r10, r11; loading flag
adcx rbp, rbx
adcx r8, rax
adcx rdi, r12
mov r10, [ rsp + 0x10 ]; x206, copying x191 here, cause x191 is needed in a reg for other than x206, namely all: , x206--x207, size: 1
adox r10, r15
mov rbx, rdx; preserving value of x234 into a new reg
mov rdx, [ rsp + 0x110 ]; saving x3 in rdx.
mulx r14, rax, [ rsi + 0x8 ]; x263, x262<- x3 * arg1[1]
adcx rbx, r10
setc r13b; spill CF x250 to reg (r13)
clc;
adcx rax, [ rsp + 0x118 ]
mulx r15, r12, [ rsi + 0x10 ]; x261, x260<- x3 * arg1[2]
adcx r12, r14
setc r10b; spill CF x269 to reg (r10)
movzx r14, byte [ rsp + 0x150 ]; load byte memx280 to register64
clc;
adcx r14, r11; loading flag
adcx rax, [ rsp + 0x230 ]
mov r14, [ rsp + 0x228 ]; x283, copying x241 here, cause x241 is needed in a reg for other than x283, namely all: , x283--x284, size: 1
adcx r14, r12
setc r12b; spill CF x284 to reg (r12)
clc;
adcx rcx, [ rsp + 0x128 ]
mov rcx, [ rsi + 0x28 ]; load m64 x5 to register64
movzx r9, r13b; x251, copying x250 here, cause x250 is needed in a reg for other than x251, namely all: , x251, size: 1
mov r11, 0x0 ; moving imm to reg
adox r9, r11
xchg rdx, rcx; x5, swapping with x3, which is currently in rdx
mulx r13, r11, [ rsi + 0x0 ]; x439, x438<- x5 * arg1[0]
mov [ rsp + 0x250 ], r9; spilling x251 to mem
mov r9, [ rsp + 0x148 ]; x324, copying x309 here, cause x309 is needed in a reg for other than x324, namely all: , x324--x325, size: 1
adcx r9, rax
mov rax, [ rsp + 0x190 ]; x326, copying x311 here, cause x311 is needed in a reg for other than x326, namely all: , x326--x327, size: 1
adcx rax, r14
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r9, [ rsp + 0x88 ]
mov r14, rdx; preserving value of x5 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x258 ], rbx; spilling x249 to mem
mov [ rsp + 0x260 ], rdi; spilling x247 to mem
mulx rbx, rdi, rcx; x259, x258<- x3 * arg1[3]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x268 ], r8; spilling x245 to mem
mov [ rsp + 0x270 ], rbx; spilling x259 to mem
mulx r8, rbx, r9; x395, x394<- x366 * 0xffffffffffffffff
seto dl; spill OF x367 to reg (rdx)
mov [ rsp + 0x278 ], r13; spilling x439 to mem
mov r13, -0x1 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r13, -0x1 ; moving imm to reg
movzx r10, r10b
adox r10, r13; loading flag
adox r15, rdi
mov r10, [ rsi + 0x30 ]; load m64 x6 to register64
setc dil; spill CF x327 to reg (rdi)
clc;
adcx rbx, r9
seto bl; spill OF x271 to reg (rbx)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
movzx rdx, dl
adox rdx, r13; loading flag
adox rax, [ rsp + 0xa0 ]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov byte [ rsp + 0x280 ], bl; spilling byte x271 to mem
mulx r13, rbx, r9; x391, x390<- x366 * 0xffffffffffffffff
mov [ rsp + 0x288 ], r13; spilling x391 to mem
mov [ rsp + 0x290 ], r10; spilling x6 to mem
mulx r13, r10, r9; x393, x392<- x366 * 0xffffffffffffffff
seto dl; spill OF x369 to reg (rdx)
mov [ rsp + 0x298 ], r11; spilling x438 to mem
mov r11, -0x2 ; moving imm to reg
inc r11; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r10, r8
adox rbx, r13
seto r8b; spill OF x399 to reg (r8)
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, r13; loading flag
adox rbp, r15
xchg rdx, r14; x5, swapping with x369, which is currently in rdx
mulx r12, r15, [ rsi + 0x8 ]; x437, x436<- x5 * arg1[1]
setc r11b; spill CF x410 to reg (r11)
clc;
movzx rdi, dil
adcx rdi, r13; loading flag
adcx rbp, [ rsp + 0x188 ]
seto dil; spill OF x286 to reg (rdi)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, r13; loading flag
adox rax, r10
setc r11b; spill CF x329 to reg (r11)
clc;
adcx rax, [ rsp + 0x298 ]
mov r10, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r10; 0xffffffffffffffff, swapping with x5, which is currently in rdx
mov byte [ rsp + 0x2a0 ], r8b; spilling byte x399 to mem
mulx r13, r8, rax; x482, x481<- x453 * 0xffffffffffffffff
mov [ rsp + 0x2a8 ], r12; spilling x437 to mem
mov byte [ rsp + 0x2b0 ], r11b; spilling byte x329 to mem
mulx r12, r11, rax; x480, x479<- x453 * 0xffffffffffffffff
setc dl; spill CF x454 to reg (rdx)
clc;
mov [ rsp + 0x2b8 ], r12; spilling x480 to mem
mov r12, -0x1 ; moving imm to reg
movzx r14, r14b
adcx r14, r12; loading flag
adcx rbp, [ rsp + 0x98 ]
seto r14b; spill OF x412 to reg (r14)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r8, rax
mov r8b, dl; preserving value of x454 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov byte [ rsp + 0x2c0 ], dil; spilling byte x286 to mem
mulx r12, rdi, [ rsp + 0x290 ]; x526, x525<- x6 * arg1[0]
setc dl; spill CF x371 to reg (rdx)
clc;
adcx r15, [ rsp + 0x278 ]
mov [ rsp + 0x2c8 ], r12; spilling x526 to mem
setc r12b; spill CF x441 to reg (r12)
clc;
mov byte [ rsp + 0x2d0 ], dl; spilling byte x371 to mem
mov rdx, -0x1 ; moving imm to reg
movzx r14, r14b
adcx r14, rdx; loading flag
adcx rbp, rbx
setc bl; spill CF x414 to reg (rbx)
clc;
adcx r11, r13
seto r14b; spill OF x497 to reg (r14)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, r13; loading flag
adox rbp, r15
seto r8b; spill OF x456 to reg (r8)
dec rdx; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx r14, r14b
adox r14, rdx; loading flag
adox rbp, r11
setc r13b; spill CF x484 to reg (r13)
clc;
adcx rdi, rbp
mov r14, 0xffffffffffffffff ; moving imm to reg
mov rdx, r14; 0xffffffffffffffff to rdx
mulx r14, r15, rdi; x567, x566<- x540 * 0xffffffffffffffff
mov r11, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, rdi; x540, swapping with 0xffffffffffffffff, which is currently in rdx
mulx rbp, rdi, r11; x559, x558<- x540 * 0x6cfc5fd681c52056
mov r11, 0xffffffffffffffff ; moving imm to reg
mov byte [ rsp + 0x2d8 ], r13b; spilling byte x484 to mem
mov byte [ rsp + 0x2e0 ], r8b; spilling byte x456 to mem
mulx r13, r8, r11; x569, x568<- x540 * 0xffffffffffffffff
mov byte [ rsp + 0x2e8 ], bl; spilling byte x414 to mem
mov byte [ rsp + 0x2f0 ], r12b; spilling byte x441 to mem
mulx rbx, r12, r11; x565, x564<- x540 * 0xffffffffffffffff
setc r11b; spill CF x541 to reg (r11)
clc;
adcx r15, r13
mov r13, 0x2341f27177344 ; moving imm to reg
mov [ rsp + 0x2f8 ], r15; spilling x570 to mem
mov byte [ rsp + 0x300 ], r11b; spilling byte x541 to mem
mulx r15, r11, r13; x557, x556<- x540 * 0x2341f27177344
mov r13, 0xfdc1767ae2ffffff ; moving imm to reg
mov [ rsp + 0x308 ], r15; spilling x557 to mem
mov [ rsp + 0x310 ], r8; spilling x568 to mem
mulx r15, r8, r13; x563, x562<- x540 * 0xfdc1767ae2ffffff
adcx r12, r14
adcx r8, rbx
mov r14, rdx; preserving value of x540 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx rbx, r13, r10; x435, x434<- x5 * arg1[2]
mov rdx, 0x7bc65c783158aea3 ; moving imm to reg
mov [ rsp + 0x318 ], r8; spilling x574 to mem
mov [ rsp + 0x320 ], r12; spilling x572 to mem
mulx r8, r12, r14; x561, x560<- x540 * 0x7bc65c783158aea3
adcx r12, r15
adcx rdi, r8
mov r15, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, r15; 0xfdc1767ae2ffffff, swapping with 0x7bc65c783158aea3, which is currently in rdx
mulx r8, r15, r9; x389, x388<- x366 * 0xfdc1767ae2ffffff
adcx r11, rbp
setc bpl; spill CF x581 to reg (rbp)
clc;
adcx r14, [ rsp + 0x310 ]
mov r14, rdx; preserving value of 0xfdc1767ae2ffffff into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x328 ], r11; spilling x580 to mem
mov [ rsp + 0x330 ], rdi; spilling x578 to mem
mulx r11, rdi, rcx; x257, x256<- x3 * arg1[4]
setc dl; spill CF x584 to reg (rdx)
movzx r14, byte [ rsp + 0x280 ]; load byte memx271 to register64
clc;
mov [ rsp + 0x338 ], r12; spilling x576 to mem
mov r12, -0x1 ; moving imm to reg
adcx r14, r12; loading flag
adcx rdi, [ rsp + 0x270 ]
setc r14b; spill CF x273 to reg (r14)
movzx r12, byte [ rsp + 0x2c0 ]; load byte memx286 to register64
clc;
mov [ rsp + 0x340 ], r8; spilling x389 to mem
mov r8, -0x1 ; moving imm to reg
adcx r12, r8; loading flag
adcx rdi, [ rsp + 0x268 ]
setc r12b; spill CF x288 to reg (r12)
movzx r8, byte [ rsp + 0x2b0 ]; load byte memx329 to register64
clc;
mov [ rsp + 0x348 ], rbx; spilling x435 to mem
mov rbx, -0x1 ; moving imm to reg
adcx r8, rbx; loading flag
adcx rdi, [ rsp + 0x168 ]
seto r8b; spill OF x499 to reg (r8)
movzx rbx, byte [ rsp + 0x2f0 ]; load byte memx441 to register64
mov byte [ rsp + 0x350 ], r12b; spilling byte x288 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbx, r12; loading flag
adox r13, [ rsp + 0x2a8 ]
movzx rbx, bpl; x582, copying x581 here, cause x581 is needed in a reg for other than x582, namely all: , x582, size: 1
mov r12, [ rsp + 0x308 ]; load m64 x557 to register64
lea rbx, [ rbx + r12 ]; r8/64 + m8
seto r12b; spill OF x443 to reg (r12)
movzx rbp, byte [ rsp + 0x2a0 ]; load byte memx399 to register64
mov [ rsp + 0x358 ], rbx; spilling x582 to mem
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbp, rbx; loading flag
adox r15, [ rsp + 0x288 ]
setc bpl; spill CF x331 to reg (rbp)
movzx rbx, byte [ rsp + 0x2d0 ]; load byte memx371 to register64
clc;
mov byte [ rsp + 0x360 ], r12b; spilling byte x443 to mem
mov r12, -0x1 ; moving imm to reg
adcx rbx, r12; loading flag
adcx rdi, [ rsp + 0xc8 ]
setc bl; spill CF x373 to reg (rbx)
movzx r12, byte [ rsp + 0x2e8 ]; load byte memx414 to register64
clc;
mov byte [ rsp + 0x368 ], bpl; spilling byte x331 to mem
mov rbp, -0x1 ; moving imm to reg
adcx r12, rbp; loading flag
adcx rdi, r15
mov r12b, dl; preserving value of x584 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r15, rbp, [ rsp + 0x290 ]; x524, x523<- x6 * arg1[1]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov byte [ rsp + 0x370 ], bl; spilling byte x373 to mem
mov [ rsp + 0x378 ], r15; spilling x524 to mem
mulx rbx, r15, rax; x478, x477<- x453 * 0xffffffffffffffff
setc dl; spill CF x416 to reg (rdx)
mov [ rsp + 0x380 ], rbx; spilling x478 to mem
movzx rbx, byte [ rsp + 0x2e0 ]; load byte memx456 to register64
clc;
mov byte [ rsp + 0x388 ], r12b; spilling byte x584 to mem
mov r12, -0x1 ; moving imm to reg
adcx rbx, r12; loading flag
adcx rdi, r13
seto bl; spill OF x401 to reg (rbx)
movzx r13, byte [ rsp + 0x2d8 ]; load byte memx484 to register64
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
adox r13, r12; loading flag
adox r15, [ rsp + 0x2b8 ]
xchg rdx, rcx; x3, swapping with x416, which is currently in rdx
mulx r13, r12, [ rsi + 0x28 ]; x255, x254<- x3 * arg1[5]
mov [ rsp + 0x390 ], r13; spilling x255 to mem
setc r13b; spill CF x458 to reg (r13)
clc;
adcx rbp, [ rsp + 0x2c8 ]
mov byte [ rsp + 0x398 ], r13b; spilling byte x458 to mem
seto r13b; spill OF x486 to reg (r13)
mov byte [ rsp + 0x3a0 ], cl; spilling byte x416 to mem
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r8, r8b
adox r8, rcx; loading flag
adox rdi, r15
setc r8b; spill CF x528 to reg (r8)
clc;
movzx r14, r14b
adcx r14, rcx; loading flag
adcx r11, r12
setc r14b; spill CF x275 to reg (r14)
movzx r15, byte [ rsp + 0x300 ]; load byte memx541 to register64
clc;
adcx r15, rcx; loading flag
adcx rdi, rbp
seto r15b; spill OF x501 to reg (r15)
movzx r12, byte [ rsp + 0x388 ]; load byte memx584 to register64
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
adox r12, rbp; loading flag
adox rdi, [ rsp + 0x2f8 ]
setc r12b; spill CF x543 to reg (r12)
seto bpl; spill OF x586 to reg (rbp)
mov byte [ rsp + 0x3a8 ], r14b; spilling byte x275 to mem
mov r14, rdi; x600, copying x585 here, cause x585 is needed in a reg for other than x600, namely all: , x600--x601, x616, size: 2
mov byte [ rsp + 0x3b0 ], r15b; spilling byte x501 to mem
mov r15, 0xffffffffffffffff ; moving imm to reg
sub r14, r15
mov rcx, rdx; preserving value of x3 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x3b8 ], r14; spilling x600 to mem
mulx r15, r14, [ rsp + 0x290 ]; x522, x521<- x6 * arg1[2]
mov rdx, 0xfdc1767ae2ffffff ; moving imm to reg
mov [ rsp + 0x3c0 ], r15; spilling x522 to mem
mov byte [ rsp + 0x3c8 ], bpl; spilling byte x586 to mem
mulx r15, rbp, rax; x476, x475<- x453 * 0xfdc1767ae2ffffff
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r13, r13b
adox r13, rdx; loading flag
adox rbp, [ rsp + 0x380 ]
mov rdx, r10; x5 to rdx
mulx r10, r13, [ rsi + 0x18 ]; x433, x432<- x5 * arg1[3]
mov [ rsp + 0x3d0 ], r15; spilling x476 to mem
seto r15b; spill OF x488 to reg (r15)
mov [ rsp + 0x3d8 ], r10; spilling x433 to mem
mov r10, -0x1 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r10, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, r10; loading flag
adox r14, [ rsp + 0x378 ]
seto r8b; spill OF x530 to reg (r8)
movzx r10, byte [ rsp + 0x350 ]; load byte memx288 to register64
mov byte [ rsp + 0x3e0 ], r15b; spilling byte x488 to mem
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r10, r15; loading flag
adox r11, [ rsp + 0x260 ]
setc r10b; spill CF x601 to reg (r10)
movzx r15, byte [ rsp + 0x368 ]; load byte memx331 to register64
clc;
mov byte [ rsp + 0x3e8 ], r8b; spilling byte x530 to mem
mov r8, -0x1 ; moving imm to reg
adcx r15, r8; loading flag
adcx r11, [ rsp + 0x178 ]
setc r15b; spill CF x333 to reg (r15)
movzx r8, byte [ rsp + 0x360 ]; load byte memx443 to register64
clc;
mov byte [ rsp + 0x3f0 ], r10b; spilling byte x601 to mem
mov r10, -0x1 ; moving imm to reg
adcx r8, r10; loading flag
adcx r13, [ rsp + 0x348 ]
mov r8, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, r8; 0x7bc65c783158aea3, swapping with x5, which is currently in rdx
mov byte [ rsp + 0x3f8 ], r15b; spilling byte x333 to mem
mulx r10, r15, r9; x387, x386<- x366 * 0x7bc65c783158aea3
setc dl; spill CF x445 to reg (rdx)
clc;
mov [ rsp + 0x400 ], r10; spilling x387 to mem
mov r10, -0x1 ; moving imm to reg
movzx rbx, bl
adcx rbx, r10; loading flag
adcx r15, [ rsp + 0x340 ]
mov bl, dl; preserving value of x445 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mulx rcx, r10, rcx; x253, x252<- x3 * arg1[6]
setc dl; spill CF x403 to reg (rdx)
mov byte [ rsp + 0x408 ], bl; spilling byte x445 to mem
movzx rbx, byte [ rsp + 0x370 ]; load byte memx373 to register64
clc;
mov [ rsp + 0x410 ], rcx; spilling x253 to mem
mov rcx, -0x1 ; moving imm to reg
adcx rbx, rcx; loading flag
adcx r11, [ rsp + 0xc0 ]
setc bl; spill CF x375 to reg (rbx)
movzx rcx, byte [ rsp + 0x3a0 ]; load byte memx416 to register64
clc;
mov byte [ rsp + 0x418 ], dl; spilling byte x403 to mem
mov rdx, -0x1 ; moving imm to reg
adcx rcx, rdx; loading flag
adcx r11, r15
setc cl; spill CF x418 to reg (rcx)
movzx r15, byte [ rsp + 0x398 ]; load byte memx458 to register64
clc;
adcx r15, rdx; loading flag
adcx r11, r13
seto r15b; spill OF x290 to reg (r15)
movzx r13, byte [ rsp + 0x3b0 ]; load byte memx501 to register64
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
adox r13, rdx; loading flag
adox r11, rbp
setc r13b; spill CF x460 to reg (r13)
clc;
movzx r12, r12b
adcx r12, rdx; loading flag
adcx r11, r14
seto r12b; spill OF x503 to reg (r12)
movzx rbp, byte [ rsp + 0x3a8 ]; load byte memx275 to register64
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
adox rbp, r14; loading flag
adox r10, [ rsp + 0x390 ]
setc bpl; spill CF x545 to reg (rbp)
clc;
movzx r15, r15b
adcx r15, r14; loading flag
adcx r10, [ rsp + 0x258 ]
setc r15b; spill CF x292 to reg (r15)
movzx rdx, byte [ rsp + 0x3c8 ]; load byte memx586 to register64
clc;
adcx rdx, r14; loading flag
adcx r11, [ rsp + 0x320 ]
setc dl; spill CF x588 to reg (rdx)
movzx r14, byte [ rsp + 0x3f8 ]; load byte memx333 to register64
clc;
mov byte [ rsp + 0x420 ], bpl; spilling byte x545 to mem
mov rbp, -0x1 ; moving imm to reg
adcx r14, rbp; loading flag
adcx r10, [ rsp + 0x170 ]
mov r14, [ rsp + 0x410 ]; x278, copying x253 here, cause x253 is needed in a reg for other than x278, namely all: , x278, size: 1
mov rbp, 0x0 ; moving imm to reg
adox r14, rbp
dec rbp; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx rbx, bl
adox rbx, rbp; loading flag
adox r10, [ rsp + 0xb8 ]
mov bl, dl; preserving value of x588 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov byte [ rsp + 0x428 ], r12b; spilling byte x503 to mem
mulx rbp, r12, [ rsp + 0x290 ]; x520, x519<- x6 * arg1[3]
mov rdx, 0x6cfc5fd681c52056 ; moving imm to reg
mov [ rsp + 0x430 ], rbp; spilling x520 to mem
mov byte [ rsp + 0x438 ], bl; spilling byte x588 to mem
mulx rbp, rbx, r9; x385, x384<- x366 * 0x6cfc5fd681c52056
xchg rdx, r8; x5, swapping with 0x6cfc5fd681c52056, which is currently in rdx
mov [ rsp + 0x440 ], rbp; spilling x385 to mem
mulx r8, rbp, [ rsi + 0x20 ]; x431, x430<- x5 * arg1[4]
mov byte [ rsp + 0x448 ], r13b; spilling byte x460 to mem
setc r13b; spill CF x335 to reg (r13)
mov [ rsp + 0x450 ], r8; spilling x431 to mem
movzx r8, byte [ rsp + 0x3e8 ]; load byte memx530 to register64
clc;
mov [ rsp + 0x458 ], r11; spilling x587 to mem
mov r11, -0x1 ; moving imm to reg
adcx r8, r11; loading flag
adcx r12, [ rsp + 0x3c0 ]
setc r8b; spill CF x532 to reg (r8)
movzx r11, byte [ rsp + 0x408 ]; load byte memx445 to register64
clc;
mov [ rsp + 0x460 ], r12; spilling x531 to mem
mov r12, -0x1 ; moving imm to reg
adcx r11, r12; loading flag
adcx rbp, [ rsp + 0x3d8 ]
mov r11, 0x2341f27177344 ; moving imm to reg
xchg rdx, r9; x366, swapping with x5, which is currently in rdx
mulx rdx, r12, r11; x383, x382<- x366 * 0x2341f27177344
setc r11b; spill CF x447 to reg (r11)
mov byte [ rsp + 0x468 ], r8b; spilling byte x532 to mem
movzx r8, byte [ rsp + 0x418 ]; load byte memx403 to register64
clc;
mov [ rsp + 0x470 ], rdx; spilling x383 to mem
mov rdx, -0x1 ; moving imm to reg
adcx r8, rdx; loading flag
adcx rbx, [ rsp + 0x400 ]
setc r8b; spill CF x405 to reg (r8)
clc;
movzx rcx, cl
adcx rcx, rdx; loading flag
adcx r10, rbx
setc cl; spill CF x420 to reg (rcx)
clc;
movzx r15, r15b
adcx r15, rdx; loading flag
adcx r14, [ rsp + 0x250 ]
setc r15b; spill CF x294 to reg (r15)
seto bl; spill OF x377 to reg (rbx)
movzx rdx, byte [ rsp + 0x3f0 ]; x601, copying x601 here, cause x601 is needed in a reg for other than x601, namely all: , x602--x603, size: 1
add rdx, -0x1
mov rdx, [ rsp + 0x458 ]; x602, copying x587 here, cause x587 is needed in a reg for other than x602, namely all: , x617, x602--x603, size: 2
mov byte [ rsp + 0x478 ], cl; spilling byte x420 to mem
mov rcx, 0xffffffffffffffff ; moving imm to reg
sbb rdx, rcx
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r13, r13b
adox r13, rcx; loading flag
adox r14, [ rsp + 0x180 ]
xchg rdx, r9; x5, swapping with x602, which is currently in rdx
mulx r13, rcx, [ rsi + 0x28 ]; x429, x428<- x5 * arg1[5]
mov [ rsp + 0x480 ], r9; spilling x602 to mem
setc r9b; spill CF x603 to reg (r9)
clc;
mov [ rsp + 0x488 ], r13; spilling x429 to mem
mov r13, -0x1 ; moving imm to reg
movzx r11, r11b
adcx r11, r13; loading flag
adcx rcx, [ rsp + 0x450 ]
mov r11, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, rax; x453, swapping with x5, which is currently in rdx
mov [ rsp + 0x490 ], rcx; spilling x448 to mem
mulx r13, rcx, r11; x472, x471<- x453 * 0x6cfc5fd681c52056
mov r11, 0x7bc65c783158aea3 ; moving imm to reg
mov [ rsp + 0x498 ], r13; spilling x472 to mem
mov [ rsp + 0x4a0 ], r14; spilling x336 to mem
mulx r13, r14, r11; x474, x473<- x453 * 0x7bc65c783158aea3
setc r11b; spill CF x449 to reg (r11)
mov byte [ rsp + 0x4a8 ], bl; spilling byte x377 to mem
movzx rbx, byte [ rsp + 0x448 ]; load byte memx460 to register64
clc;
mov byte [ rsp + 0x4b0 ], r9b; spilling byte x603 to mem
mov r9, -0x1 ; moving imm to reg
adcx rbx, r9; loading flag
adcx r10, rbp
movzx rbx, r15b; x338, copying x294 here, cause x294 is needed in a reg for other than x338, namely all: , x338, size: 1
mov rbp, 0x0 ; moving imm to reg
adox rbx, rbp
movzx r15, byte [ rsp + 0x3e0 ]; load byte memx488 to register64
dec rbp; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
adox r15, rbp; loading flag
adox r14, [ rsp + 0x3d0 ]
setc r9b; spill CF x462 to reg (r9)
movzx r15, byte [ rsp + 0x428 ]; load byte memx503 to register64
clc;
adcx r15, rbp; loading flag
adcx r10, r14
setc r15b; spill CF x505 to reg (r15)
clc;
movzx r8, r8b
adcx r8, rbp; loading flag
adcx r12, [ rsp + 0x440 ]
mov r8, [ rsp + 0x470 ]; x408, copying x383 here, cause x383 is needed in a reg for other than x408, namely all: , x408, size: 1
mov r14, 0x0 ; moving imm to reg
adcx r8, r14
movzx r14, byte [ rsp + 0x420 ]; load byte memx545 to register64
clc;
adcx r14, rbp; loading flag
adcx r10, [ rsp + 0x460 ]
adox rcx, r13
seto r14b; spill OF x492 to reg (r14)
movzx r13, byte [ rsp + 0x438 ]; load byte memx588 to register64
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
adox r13, rbp; loading flag
adox r10, [ rsp + 0x318 ]
setc r13b; spill CF x547 to reg (r13)
seto bpl; spill OF x590 to reg (rbp)
mov [ rsp + 0x4b8 ], r8; spilling x408 to mem
movzx r8, byte [ rsp + 0x4b0 ]; x603, copying x603 here, cause x603 is needed in a reg for other than x603, namely all: , x604--x605, size: 1
add r8, -0x1
mov r8, r10; x604, copying x589 here, cause x589 is needed in a reg for other than x604, namely all: , x618, x604--x605, size: 2
mov byte [ rsp + 0x4c0 ], r11b; spilling byte x449 to mem
mov r11, 0xffffffffffffffff ; moving imm to reg
sbb r8, r11
mov r11, rdx; preserving value of x453 into a new reg
mov rdx, [ rsp + 0x290 ]; saving x6 in rdx.
mov [ rsp + 0x4c8 ], r8; spilling x604 to mem
mov byte [ rsp + 0x4d0 ], bpl; spilling byte x590 to mem
mulx r8, rbp, [ rsi + 0x20 ]; x518, x517<- x6 * arg1[4]
mov [ rsp + 0x4d8 ], r8; spilling x518 to mem
mov r8, [ rsp + 0x4a0 ]; load m64 x336 to register64
mov [ rsp + 0x4e0 ], rbx; spilling x338 to mem
movzx rbx, byte [ rsp + 0x4a8 ]; load byte memx377 to register64
mov byte [ rsp + 0x4e8 ], r13b; spilling byte x547 to mem
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbx, r13; loading flag
adox r8, [ rsp + 0xd8 ]
mov rbx, 0x2341f27177344 ; moving imm to reg
xchg rdx, r11; x453, swapping with x6, which is currently in rdx
mulx rdx, r13, rbx; x470, x469<- x453 * 0x2341f27177344
setc bl; spill CF x605 to reg (rbx)
mov [ rsp + 0x4f0 ], rdx; spilling x470 to mem
movzx rdx, byte [ rsp + 0x478 ]; load byte memx420 to register64
clc;
mov [ rsp + 0x4f8 ], rbp; spilling x517 to mem
mov rbp, -0x1 ; moving imm to reg
adcx rdx, rbp; loading flag
adcx r8, r12
seto dl; spill OF x379 to reg (rdx)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, r12; loading flag
adox r13, [ rsp + 0x498 ]
setc r14b; spill CF x422 to reg (r14)
clc;
movzx r9, r9b
adcx r9, r12; loading flag
adcx r8, [ rsp + 0x490 ]
seto r9b; spill OF x494 to reg (r9)
inc r12; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, rbp; loading flag
adox r8, rcx
mov r15, [ rsp + 0x4f8 ]; load m64 x517 to register64
seto cl; spill OF x507 to reg (rcx)
movzx r12, byte [ rsp + 0x468 ]; load byte memx532 to register64
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
adox r12, rbp; loading flag
adox r15, [ rsp + 0x430 ]
setc r12b; spill CF x464 to reg (r12)
movzx rbp, byte [ rsp + 0x4e8 ]; load byte memx547 to register64
clc;
mov byte [ rsp + 0x500 ], r9b; spilling byte x494 to mem
mov r9, -0x1 ; moving imm to reg
adcx rbp, r9; loading flag
adcx r8, r15
mov rbp, [ rsp + 0xd0 ]; load m64 x365 to register64
setc r15b; spill CF x549 to reg (r15)
clc;
movzx rdx, dl
adcx rdx, r9; loading flag
adcx rbp, [ rsp + 0x4e0 ]
setc dl; spill CF x381 to reg (rdx)
movzx r9, byte [ rsp + 0x4d0 ]; load byte memx590 to register64
clc;
mov byte [ rsp + 0x508 ], r15b; spilling byte x549 to mem
mov r15, -0x1 ; moving imm to reg
adcx r9, r15; loading flag
adcx r8, [ rsp + 0x338 ]
mov r9b, dl; preserving value of x381 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mulx rax, r15, rax; x427, x426<- x5 * arg1[6]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x510 ], r13; spilling x493 to mem
mov byte [ rsp + 0x518 ], cl; spilling byte x507 to mem
mulx r13, rcx, r11; x516, x515<- x6 * arg1[5]
setc dl; spill CF x592 to reg (rdx)
mov [ rsp + 0x520 ], r13; spilling x516 to mem
movzx r13, byte [ rsp + 0x4c0 ]; load byte memx449 to register64
clc;
mov byte [ rsp + 0x528 ], r9b; spilling byte x381 to mem
mov r9, -0x1 ; moving imm to reg
adcx r13, r9; loading flag
adcx r15, [ rsp + 0x488 ]
mov r13, 0x0 ; moving imm to reg
adcx rax, r13
mov r13, [ rsp + 0x4d8 ]; x535, copying x518 here, cause x518 is needed in a reg for other than x535, namely all: , x535--x536, size: 1
adox r13, rcx
clc;
movzx r14, r14b
adcx r14, r9; loading flag
adcx rbp, [ rsp + 0x4b8 ]
setc r14b; spill CF x424 to reg (r14)
seto cl; spill OF x536 to reg (rcx)
movzx r9, bl; x605, copying x605 here, cause x605 is needed in a reg for other than x605, namely all: , x606--x607, size: 1
add r9, -0x1
mov rbx, r8; x606, copying x591 here, cause x591 is needed in a reg for other than x606, namely all: , x619, x606--x607, size: 2
mov r9, 0xfdc1767ae2ffffff ; moving imm to reg
sbb rbx, r9
mov r9b, dl; preserving value of x592 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0x530 ], rbx; spilling x606 to mem
mulx r11, rbx, r11; x514, x513<- x6 * arg1[6]
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, rdx; loading flag
adox rbp, r15
movzx r12, r14b; x425, copying x424 here, cause x424 is needed in a reg for other than x425, namely all: , x425, size: 1
movzx r15, byte [ rsp + 0x528 ]; load byte memx381 to register64
lea r12, [ r12 + r15 ]; r64+m8
setc r15b; spill CF x607 to reg (r15)
movzx r14, byte [ rsp + 0x518 ]; load byte memx507 to register64
clc;
adcx r14, rdx; loading flag
adcx rbp, [ rsp + 0x510 ]
movzx r14, byte [ rsp + 0x500 ]; x495, copying x494 here, cause x494 is needed in a reg for other than x495, namely all: , x495, size: 1
mov rdx, [ rsp + 0x4f0 ]; load m64 x470 to register64
lea r14, [ r14 + rdx ]; r8/64 + m8
adox rax, r12
seto dl; spill OF x468 to reg (rdx)
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rcx, cl
adox rcx, r12; loading flag
adox rbx, [ rsp + 0x520 ]
adcx r14, rax
mov rcx, 0x0 ; moving imm to reg
adox r11, rcx
movzx rax, byte [ rsp + 0x508 ]; load byte memx549 to register64
dec rcx; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
adox rax, rcx; loading flag
adox rbp, r13
adox rbx, r14
movzx r12, dl; x512, copying x468 here, cause x468 is needed in a reg for other than x512, namely all: , x512, size: 1
mov rax, 0x0 ; moving imm to reg
adcx r12, rax
clc;
movzx r9, r9b
adcx r9, rcx; loading flag
adcx rbp, [ rsp + 0x330 ]
adox r11, r12
mov r9, [ rsp + 0x328 ]; x595, copying x580 here, cause x580 is needed in a reg for other than x595, namely all: , x595--x596, size: 1
adcx r9, rbx
mov r13, [ rsp + 0x358 ]; x597, copying x582 here, cause x582 is needed in a reg for other than x597, namely all: , x597--x598, size: 1
adcx r13, r11
setc dl; spill CF x598 to reg (rdx)
seto r14b; spill OF x555 to reg (r14)
movzx rbx, r15b; x607, copying x607 here, cause x607 is needed in a reg for other than x607, namely all: , x608--x609, size: 1
add rbx, -0x1
mov rbx, rbp; x608, copying x593 here, cause x593 is needed in a reg for other than x608, namely all: , x608--x609, x620, size: 2
mov r15, 0x7bc65c783158aea3 ; moving imm to reg
sbb rbx, r15
movzx r12, dl; x599, copying x598 here, cause x598 is needed in a reg for other than x599, namely all: , x599, size: 1
movzx r14, r14b
lea r12, [ r12 + r14 ]
mov r14, r9; x610, copying x595 here, cause x595 is needed in a reg for other than x610, namely all: , x621, x610--x611, size: 2
mov r11, 0x6cfc5fd681c52056 ; moving imm to reg
sbb r14, r11
mov rdx, r13; x612, copying x597 here, cause x597 is needed in a reg for other than x612, namely all: , x612--x613, x622, size: 2
mov rax, 0x2341f27177344 ; moving imm to reg
sbb rdx, rax
sbb r12, 0x00000000
cmovc rdx, r13; if CF, x622<- x597 (nzVar)
cmovc r14, r9; if CF, x621<- x595 (nzVar)
mov r12, [ rsp + 0x530 ]; x619, copying x606 here, cause x606 is needed in a reg for other than x619, namely all: , x619, size: 1
cmovc r12, r8; if CF, x619<- x591 (nzVar)
mov r8, [ rsp + 0x4c8 ]; x618, copying x604 here, cause x604 is needed in a reg for other than x618, namely all: , x618, size: 1
cmovc r8, r10; if CF, x618<- x589 (nzVar)
mov r10, [ rsp + 0x3b8 ]; x616, copying x600 here, cause x600 is needed in a reg for other than x616, namely all: , x616, size: 1
cmovc r10, rdi; if CF, x616<- x585 (nzVar)
mov rdi, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rdi + 0x10 ], r8; out1[2] = x618
cmovc rbx, rbp; if CF, x620<- x593 (nzVar)
mov [ rdi + 0x28 ], r14; out1[5] = x621
mov rbp, [ rsp + 0x480 ]; x617, copying x602 here, cause x602 is needed in a reg for other than x617, namely all: , x617, size: 1
cmovc rbp, [ rsp + 0x458 ]; if CF, x617<- x587 (nzVar)
mov [ rdi + 0x30 ], rdx; out1[6] = x622
mov [ rdi + 0x20 ], rbx; out1[4] = x620
mov [ rdi + 0x0 ], r10; out1[0] = x616
mov [ rdi + 0x8 ], rbp; out1[1] = x617
mov [ rdi + 0x18 ], r12; out1[3] = x619
mov rbx, [ rsp + 0x538 ]; restoring from stack
mov rbp, [ rsp + 0x540 ]; restoring from stack
mov r12, [ rsp + 0x548 ]; restoring from stack
mov r13, [ rsp + 0x550 ]; restoring from stack
mov r14, [ rsp + 0x558 ]; restoring from stack
mov r15, [ rsp + 0x560 ]; restoring from stack
add rsp, 0x568 
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; clocked at 4800 MHz
; first cyclecount 681.85, best 386.8, lastGood 390.08
; seed 2412526886283759 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 6440623 ms / 60000 runs=> 107.34371666666667ms/run
; Time spent for assembling and measureing (initial batch_size=25, initial num_batches=101): 114887 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.017837870653196128
; number reverted permutation/ tried permutation: 18693 / 29897 =62.525%
; number reverted decision/ tried decision: 17520 / 30104 =58.198%