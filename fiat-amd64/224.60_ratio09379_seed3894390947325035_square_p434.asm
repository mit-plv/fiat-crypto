SECTION .text
	GLOBAL square_p434
square_p434:
sub rsp, 0x650 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x620 ], rbx; saving to stack
mov [ rsp + 0x628 ], rbp; saving to stack
mov [ rsp + 0x630 ], r12; saving to stack
mov [ rsp + 0x638 ], r13; saving to stack
mov [ rsp + 0x640 ], r14; saving to stack
mov [ rsp + 0x648 ], r15; saving to stack
mov rax, [ rsi + 0x18 ]; load m64 x3 to register64
mov rdx, rax; x3 to rdx
mulx rax, r10, [ rsi + 0x8 ]; x263, x262<- x3 * arg1[1]
mulx r11, rbx, [ rsi + 0x28 ]; x255, x254<- x3 * arg1[5]
mulx rbp, r12, [ rsi + 0x30 ]; x253, x252<- x3 * arg1[6]
mulx r13, r14, [ rsi + 0x0 ]; x265, x264<- x3 * arg1[0]
mulx r15, rcx, [ rsi + 0x20 ]; x257, x256<- x3 * arg1[4]
mulx r8, r9, [ rsi + 0x10 ]; x261, x260<- x3 * arg1[2]
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx rdx, rdi, [ rsi + 0x18 ]; x259, x258<- x3 * arg1[3]
test al, al
adox r10, r13
adox r9, rax
mov rax, [ rsi + 0x30 ]; load m64 x6 to register64
adox rdi, r8
adox rcx, rdx
mov rdx, rax; x6 to rdx
mulx rax, r13, [ rsi + 0x8 ]; x524, x523<- x6 * arg1[1]
adox rbx, r15
mulx r15, r8, [ rsi + 0x0 ]; x526, x525<- x6 * arg1[0]
mov [ rsp + 0x8 ], rbx; spilling x274 to mem
mov [ rsp + 0x10 ], rcx; spilling x272 to mem
mulx rbx, rcx, [ rsi + 0x20 ]; x518, x517<- x6 * arg1[4]
mov [ rsp + 0x18 ], r8; spilling x525 to mem
mov [ rsp + 0x20 ], rdi; spilling x270 to mem
mulx r8, rdi, [ rsi + 0x10 ]; x522, x521<- x6 * arg1[2]
adox r12, r11
mov [ rsp + 0x28 ], r12; spilling x276 to mem
mulx r11, r12, [ rsi + 0x18 ]; x520, x519<- x6 * arg1[3]
mov [ rsp + 0x30 ], r9; spilling x268 to mem
mov r9, [ rsi + 0x0 ]; load m64 x7 to register64
adcx r13, r15
mov r15, 0x0 ; moving imm to reg
adox rbp, r15
mov [ rsp + 0x38 ], rbp; spilling x278 to mem
mulx r15, rbp, [ rsi + 0x30 ]; x514, x513<- x6 * arg1[6]
adcx rdi, rax
adcx r12, r8
adcx rcx, r11
mulx rdx, rax, [ rsi + 0x28 ]; x516, x515<- x6 * arg1[5]
adcx rax, rbx
mov rbx, rdx; preserving value of x516 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r8, r11, r9; x21, x20<- x7 * arg1[0]
adcx rbp, rbx
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x40 ], rbp; spilling x537 to mem
mulx rbx, rbp, r11; x46, x45<- x20 * 0xffffffffffffffff
mov rdx, [ rsi + 0x20 ]; load m64 x4 to register64
mov [ rsp + 0x48 ], rax; spilling x535 to mem
mov rax, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r11; x20, swapping with x4, which is currently in rdx
mov [ rsp + 0x50 ], rcx; spilling x533 to mem
mov [ rsp + 0x58 ], r12; spilling x531 to mem
mulx rcx, r12, rax; x48, x47<- x20 * 0xffffffffffffffff
adc r15, 0x0
xchg rdx, r9; x7, swapping with x20, which is currently in rdx
mov [ rsp + 0x60 ], r15; spilling x539 to mem
mulx rax, r15, [ rsi + 0x8 ]; x19, x18<- x7 * arg1[1]
add rbp, rcx; could be done better, if r0 has been u8 as well
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, r9
mov r12, [ rsi + 0x8 ]; load m64 x1 to register64
setc cl; spill CF x50 to reg (rcx)
clc;
adcx r15, r8
adox rbp, r15
mulx r8, r15, [ rsi + 0x10 ]; x17, x16<- x7 * arg1[2]
mov [ rsp + 0x68 ], rdi; spilling x529 to mem
mov rdi, rdx; preserving value of x7 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x70 ], r13; spilling x527 to mem
mov [ rsp + 0x78 ], r10; spilling x266 to mem
mulx r13, r10, r12; x91, x90<- x1 * arg1[0]
adcx r15, rax
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x80 ], r11; spilling x4 to mem
mulx rax, r11, r9; x44, x43<- x20 * 0xffffffffffffffff
setc dl; spill CF x25 to reg (rdx)
clc;
adcx r10, rbp
mov rbp, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbp; 0xffffffffffffffff, swapping with x25, which is currently in rdx
mov [ rsp + 0x88 ], r14; spilling x264 to mem
mov [ rsp + 0x90 ], r8; spilling x17 to mem
mulx r14, r8, r10; x134, x133<- x105 * 0xffffffffffffffff
mov byte [ rsp + 0x98 ], bpl; spilling byte x25 to mem
mov [ rsp + 0xa0 ], rax; spilling x44 to mem
mulx rbp, rax, r10; x132, x131<- x105 * 0xffffffffffffffff
setc dl; spill CF x106 to reg (rdx)
clc;
adcx r8, r10
xchg rdx, r12; x1, swapping with x106, which is currently in rdx
mov [ rsp + 0xa8 ], rbp; spilling x132 to mem
mulx r8, rbp, [ rsi + 0x8 ]; x89, x88<- x1 * arg1[1]
mov [ rsp + 0xb0 ], r8; spilling x89 to mem
setc r8b; spill CF x149 to reg (r8)
clc;
adcx rbp, r13
setc r13b; spill CF x93 to reg (r13)
clc;
mov byte [ rsp + 0xb8 ], r8b; spilling byte x149 to mem
mov r8, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, r8; loading flag
adcx rbx, r11
adox rbx, r15
setc cl; spill CF x52 to reg (rcx)
clc;
adcx rax, r14
mov r15, rdx; preserving value of x1 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx r11, r14, rdi; x15, x14<- x7 * arg1[3]
mov rdx, 0xfdc1767ae2ffffff ; moving imm to reg
mov [ rsp + 0xc0 ], r11; spilling x15 to mem
mulx r8, r11, r9; x42, x41<- x20 * 0xfdc1767ae2ffffff
setc dl; spill CF x136 to reg (rdx)
clc;
mov [ rsp + 0xc8 ], r8; spilling x42 to mem
mov r8, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, r8; loading flag
adcx r11, [ rsp + 0xa0 ]
seto cl; spill OF x67 to reg (rcx)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, r8; loading flag
adox rbx, rbp
mov r12b, dl; preserving value of x136 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx rbp, r8, r15; x87, x86<- x1 * arg1[2]
setc dl; spill CF x54 to reg (rdx)
mov [ rsp + 0xd0 ], rbp; spilling x87 to mem
movzx rbp, byte [ rsp + 0x98 ]; load byte memx25 to register64
clc;
mov byte [ rsp + 0xd8 ], r12b; spilling byte x136 to mem
mov r12, -0x1 ; moving imm to reg
adcx rbp, r12; loading flag
adcx r14, [ rsp + 0x90 ]
setc bpl; spill CF x27 to reg (rbp)
clc;
movzx rcx, cl
adcx rcx, r12; loading flag
adcx r14, r11
setc cl; spill CF x69 to reg (rcx)
clc;
movzx r13, r13b
adcx r13, r12; loading flag
adcx r8, [ rsp + 0xb0 ]
setc r13b; spill CF x95 to reg (r13)
movzx r11, byte [ rsp + 0xb8 ]; load byte memx149 to register64
clc;
adcx r11, r12; loading flag
adcx rbx, rax
adox r8, r14
mov r11b, dl; preserving value of x54 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx rax, r14, r15; x85, x84<- x1 * arg1[3]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0xe0 ], rbx; spilling x150 to mem
mulx r12, rbx, r10; x130, x129<- x105 * 0xffffffffffffffff
seto dl; spill OF x110 to reg (rdx)
mov [ rsp + 0xe8 ], rax; spilling x85 to mem
movzx rax, byte [ rsp + 0xd8 ]; load byte memx136 to register64
mov [ rsp + 0xf0 ], r12; spilling x130 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
adox rax, r12; loading flag
adox rbx, [ rsp + 0xa8 ]
adcx rbx, r8
mov al, dl; preserving value of x110 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r8, r12, rdi; x13, x12<- x7 * arg1[4]
seto dl; spill OF x138 to reg (rdx)
mov [ rsp + 0xf8 ], rbx; spilling x152 to mem
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbp, bpl
adox rbp, rbx; loading flag
adox r12, [ rsp + 0xc0 ]
seto bpl; spill OF x29 to reg (rbp)
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, rbx; loading flag
adox r14, [ rsp + 0xd0 ]
mov r13, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, r13; 0x7bc65c783158aea3, swapping with x138, which is currently in rdx
mov [ rsp + 0x100 ], r14; spilling x96 to mem
mulx rbx, r14, r9; x40, x39<- x20 * 0x7bc65c783158aea3
setc dl; spill CF x153 to reg (rdx)
clc;
mov byte [ rsp + 0x108 ], al; spilling byte x110 to mem
mov rax, -0x1 ; moving imm to reg
movzx r11, r11b
adcx r11, rax; loading flag
adcx r14, [ rsp + 0xc8 ]
seto r11b; spill OF x97 to reg (r11)
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rax, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, rax; loading flag
adox r12, r14
mov cl, dl; preserving value of x153 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx r14, rax, rdi; x11, x10<- x7 * arg1[5]
mov rdx, 0x6cfc5fd681c52056 ; moving imm to reg
mov [ rsp + 0x110 ], r14; spilling x11 to mem
mov byte [ rsp + 0x118 ], r11b; spilling byte x97 to mem
mulx r14, r11, r9; x38, x37<- x20 * 0x6cfc5fd681c52056
mov rdx, 0xfdc1767ae2ffffff ; moving imm to reg
mov [ rsp + 0x120 ], r14; spilling x38 to mem
mov byte [ rsp + 0x128 ], cl; spilling byte x153 to mem
mulx r14, rcx, r10; x128, x127<- x105 * 0xfdc1767ae2ffffff
adcx r11, rbx
setc bl; spill CF x58 to reg (rbx)
clc;
mov rdx, -0x1 ; moving imm to reg
movzx r13, r13b
adcx r13, rdx; loading flag
adcx rcx, [ rsp + 0xf0 ]
seto r13b; spill OF x71 to reg (r13)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, rdx; loading flag
adox r8, rax
seto bpl; spill OF x31 to reg (rbp)
movzx rax, byte [ rsp + 0x108 ]; load byte memx110 to register64
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
adox rax, rdx; loading flag
adox r12, [ rsp + 0x100 ]
seto al; spill OF x112 to reg (rax)
movzx rdx, byte [ rsp + 0x128 ]; load byte memx153 to register64
mov byte [ rsp + 0x130 ], bpl; spilling byte x31 to mem
mov rbp, 0x0 ; moving imm to reg
dec rbp; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rdx, rbp; loading flag
adox r12, rcx
mov rdx, 0x7bc65c783158aea3 ; moving imm to reg
mulx rcx, rbp, r10; x126, x125<- x105 * 0x7bc65c783158aea3
adcx rbp, r14
setc r14b; spill CF x142 to reg (r14)
clc;
mov rdx, -0x1 ; moving imm to reg
movzx r13, r13b
adcx r13, rdx; loading flag
adcx r8, r11
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r13, r11, r15; x83, x82<- x1 * arg1[4]
setc dl; spill CF x73 to reg (rdx)
mov [ rsp + 0x138 ], r12; spilling x154 to mem
movzx r12, byte [ rsp + 0x118 ]; load byte memx97 to register64
clc;
mov [ rsp + 0x140 ], r13; spilling x83 to mem
mov r13, -0x1 ; moving imm to reg
adcx r12, r13; loading flag
adcx r11, [ rsp + 0xe8 ]
setc r12b; spill CF x99 to reg (r12)
clc;
movzx rax, al
adcx rax, r13; loading flag
adcx r8, r11
adox rbp, r8
mov al, dl; preserving value of x73 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mulx rdi, r11, rdi; x9, x8<- x7 * arg1[6]
mov rdx, 0x6cfc5fd681c52056 ; moving imm to reg
mulx r8, r13, r10; x124, x123<- x105 * 0x6cfc5fd681c52056
mov rdx, 0x2341f27177344 ; moving imm to reg
mov [ rsp + 0x148 ], rbp; spilling x156 to mem
mulx r9, rbp, r9; x36, x35<- x20 * 0x2341f27177344
setc dl; spill CF x114 to reg (rdx)
clc;
mov [ rsp + 0x150 ], r8; spilling x124 to mem
mov r8, -0x1 ; moving imm to reg
movzx rbx, bl
adcx rbx, r8; loading flag
adcx rbp, [ rsp + 0x120 ]
seto bl; spill OF x157 to reg (rbx)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, r8; loading flag
adox rcx, r13
mov r14b, dl; preserving value of x114 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx r13, r8, r15; x81, x80<- x1 * arg1[5]
setc dl; spill CF x60 to reg (rdx)
mov [ rsp + 0x158 ], rcx; spilling x143 to mem
movzx rcx, byte [ rsp + 0x130 ]; load byte memx31 to register64
clc;
mov byte [ rsp + 0x160 ], bl; spilling byte x157 to mem
mov rbx, -0x1 ; moving imm to reg
adcx rcx, rbx; loading flag
adcx r11, [ rsp + 0x110 ]
mov rcx, 0x0 ; moving imm to reg
adcx rdi, rcx
clc;
movzx rax, al
adcx rax, rbx; loading flag
adcx r11, rbp
setc al; spill CF x75 to reg (rax)
clc;
movzx r12, r12b
adcx r12, rbx; loading flag
adcx r8, [ rsp + 0x140 ]
mov r12b, dl; preserving value of x60 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mulx r15, rbp, r15; x79, x78<- x1 * arg1[6]
adcx rbp, r13
mov rdx, [ rsi + 0x10 ]; load m64 x2 to register64
adcx r15, rcx
movzx r13, r12b; x61, copying x60 here, cause x60 is needed in a reg for other than x61, namely all: , x61, size: 1
lea r13, [ r13 + r9 ]
mov r9, 0x2341f27177344 ; moving imm to reg
xchg rdx, r9; 0x2341f27177344, swapping with x2, which is currently in rdx
mulx r10, r12, r10; x122, x121<- x105 * 0x2341f27177344
clc;
movzx r14, r14b
adcx r14, rbx; loading flag
adcx r11, r8
mov r14, [ rsp + 0x150 ]; x145, copying x124 here, cause x124 is needed in a reg for other than x145, namely all: , x145--x146, size: 1
adox r14, r12
adox r10, rcx
inc rbx; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov rcx, -0x1 ; moving imm to reg
movzx rax, al
adox rax, rcx; loading flag
adox rdi, r13
adcx rbp, rdi
setc al; spill CF x118 to reg (rax)
movzx r8, byte [ rsp + 0x160 ]; load byte memx157 to register64
clc;
adcx r8, rcx; loading flag
adcx r11, [ rsp + 0x158 ]
adcx r14, rbp
xchg rdx, r9; x2, swapping with 0x2341f27177344, which is currently in rdx
mulx r8, r13, [ rsi + 0x0 ]; x178, x177<- x2 * arg1[0]
movzx r12, al; x119, copying x118 here, cause x118 is needed in a reg for other than x119, namely all: , x119--x120, size: 1
adox r12, r15
adcx r10, r12
setc r15b; spill CF x163 to reg (r15)
clc;
adcx r13, [ rsp + 0xe0 ]
movzx rdi, r15b; x164, copying x163 here, cause x163 is needed in a reg for other than x164, namely all: , x164, size: 1
adox rdi, rbx
mov rax, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r13; x192, swapping with x2, which is currently in rdx
mulx rbp, r12, rax; x221, x220<- x192 * 0xffffffffffffffff
xchg rdx, r13; x2, swapping with x192, which is currently in rdx
mulx r15, rbx, [ rsi + 0x8 ]; x176, x175<- x2 * arg1[1]
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rbx, r8
xchg rdx, r13; x192, swapping with x2, which is currently in rdx
mulx r8, rcx, rax; x219, x218<- x192 * 0xffffffffffffffff
mov r9, [ rsp + 0xf8 ]; x194, copying x152 here, cause x152 is needed in a reg for other than x194, namely all: , x194--x195, size: 1
adcx r9, rbx
setc bl; spill CF x195 to reg (rbx)
clc;
adcx rcx, rbp
setc bpl; spill CF x223 to reg (rbp)
clc;
adcx r12, rdx
adcx rcx, r9
setc r12b; spill CF x238 to reg (r12)
clc;
adcx rcx, [ rsp + 0x88 ]
xchg rdx, rcx; x279, swapping with x192, which is currently in rdx
mov [ rsp + 0x168 ], rdi; spilling x164 to mem
mulx r9, rdi, rax; x306, x305<- x279 * 0xffffffffffffffff
mov [ rsp + 0x170 ], r10; spilling x162 to mem
mov [ rsp + 0x178 ], r14; spilling x160 to mem
mulx r10, r14, rax; x308, x307<- x279 * 0xffffffffffffffff
mov rax, 0xfdc1767ae2ffffff ; moving imm to reg
mov [ rsp + 0x180 ], r11; spilling x158 to mem
mov [ rsp + 0x188 ], r14; spilling x307 to mem
mulx r11, r14, rax; x302, x301<- x279 * 0xfdc1767ae2ffffff
setc al; spill CF x280 to reg (rax)
clc;
adcx rdi, r10
mov r10, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x190 ], rdi; spilling x309 to mem
mov byte [ rsp + 0x198 ], al; spilling byte x280 to mem
mulx rdi, rax, r10; x304, x303<- x279 * 0xffffffffffffffff
adcx rax, r9
mov r9, 0x7bc65c783158aea3 ; moving imm to reg
mov [ rsp + 0x1a0 ], rax; spilling x311 to mem
mulx r10, rax, r9; x300, x299<- x279 * 0x7bc65c783158aea3
adcx r14, rdi
adcx rax, r11
mov r11, 0x6cfc5fd681c52056 ; moving imm to reg
mulx rdi, r9, r11; x298, x297<- x279 * 0x6cfc5fd681c52056
adcx r9, r10
mov r10, 0x2341f27177344 ; moving imm to reg
mov [ rsp + 0x1a8 ], r9; spilling x317 to mem
mulx r11, r9, r10; x296, x295<- x279 * 0x2341f27177344
mov r10, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rcx; x192, swapping with x279, which is currently in rdx
mov [ rsp + 0x1b0 ], rax; spilling x315 to mem
mov [ rsp + 0x1b8 ], r14; spilling x313 to mem
mulx rax, r14, r10; x217, x216<- x192 * 0xffffffffffffffff
xchg rdx, r13; x2, swapping with x192, which is currently in rdx
mov [ rsp + 0x1c0 ], rax; spilling x217 to mem
mulx r10, rax, [ rsi + 0x10 ]; x174, x173<- x2 * arg1[2]
adox rax, r15
seto r15b; spill OF x182 to reg (r15)
mov [ rsp + 0x1c8 ], r10; spilling x174 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbx, bl
adox rbx, r10; loading flag
adox rax, [ rsp + 0x138 ]
adcx r9, rdi
mov rbx, 0x0 ; moving imm to reg
adcx r11, rbx
clc;
movzx rbp, bpl
adcx rbp, r10; loading flag
adcx r8, r14
setc bpl; spill CF x225 to reg (rbp)
clc;
movzx r12, r12b
adcx r12, r10; loading flag
adcx rax, r8
seto r12b; spill OF x197 to reg (r12)
mov rdi, -0x3 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rcx, [ rsp + 0x188 ]
mov rcx, rdx; preserving value of x2 into a new reg
mov rdx, [ rsp + 0x80 ]; saving x4 in rdx.
mulx r14, r8, [ rsi + 0x0 ]; x352, x351<- x4 * arg1[0]
mov rbx, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, r13; x192, swapping with x4, which is currently in rdx
mulx rdi, r10, rbx; x215, x214<- x192 * 0xfdc1767ae2ffffff
setc bl; spill CF x240 to reg (rbx)
mov [ rsp + 0x1d0 ], r11; spilling x321 to mem
movzx r11, byte [ rsp + 0x198 ]; load byte memx280 to register64
clc;
mov [ rsp + 0x1d8 ], r9; spilling x319 to mem
mov r9, -0x1 ; moving imm to reg
adcx r11, r9; loading flag
adcx rax, [ rsp + 0x78 ]
mov r11, [ rsp + 0x190 ]; x324, copying x309 here, cause x309 is needed in a reg for other than x324, namely all: , x324--x325, size: 1
adox r11, rax
setc al; spill CF x282 to reg (rax)
clc;
adcx r8, r11
mov r11, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r8; x366, swapping with x192, which is currently in rdx
mov [ rsp + 0x1e0 ], rdi; spilling x215 to mem
mulx r9, rdi, r11; x395, x394<- x366 * 0xffffffffffffffff
setc r11b; spill CF x367 to reg (r11)
clc;
mov [ rsp + 0x1e8 ], r9; spilling x395 to mem
mov r9, -0x1 ; moving imm to reg
movzx rbp, bpl
adcx rbp, r9; loading flag
adcx r10, [ rsp + 0x1c0 ]
seto bpl; spill OF x325 to reg (rbp)
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rdi, rdx
mov r9, rdx; preserving value of x366 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov byte [ rsp + 0x1f0 ], r11b; spilling byte x367 to mem
mov byte [ rsp + 0x1f8 ], bpl; spilling byte x325 to mem
mulx r11, rbp, r13; x350, x349<- x4 * arg1[1]
mov rdx, rcx; x2 to rdx
mov [ rsp + 0x200 ], r11; spilling x350 to mem
mulx rcx, r11, [ rsi + 0x18 ]; x172, x171<- x2 * arg1[3]
mov [ rsp + 0x208 ], rcx; spilling x172 to mem
seto cl; spill OF x410 to reg (rcx)
mov byte [ rsp + 0x210 ], al; spilling byte x282 to mem
mov rax, -0x1 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rax, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, rax; loading flag
adox r11, [ rsp + 0x1c8 ]
setc r15b; spill CF x227 to reg (r15)
clc;
movzx r12, r12b
adcx r12, rax; loading flag
adcx r11, [ rsp + 0x148 ]
setc r12b; spill CF x199 to reg (r12)
clc;
movzx rbx, bl
adcx rbx, rax; loading flag
adcx r11, r10
setc bl; spill CF x242 to reg (rbx)
clc;
adcx rbp, r14
setc r14b; spill CF x354 to reg (r14)
movzx r10, byte [ rsp + 0x210 ]; load byte memx282 to register64
clc;
adcx r10, rax; loading flag
adcx r11, [ rsp + 0x30 ]
setc r10b; spill CF x284 to reg (r10)
movzx rax, byte [ rsp + 0x1f8 ]; load byte memx325 to register64
clc;
mov byte [ rsp + 0x218 ], r14b; spilling byte x354 to mem
mov r14, -0x1 ; moving imm to reg
adcx rax, r14; loading flag
adcx r11, [ rsp + 0x1a0 ]
mov rax, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r9; x366, swapping with x2, which is currently in rdx
mov byte [ rsp + 0x220 ], r10b; spilling byte x284 to mem
mulx r14, r10, rax; x393, x392<- x366 * 0xffffffffffffffff
setc al; spill CF x327 to reg (rax)
clc;
adcx r10, [ rsp + 0x1e8 ]
mov [ rsp + 0x228 ], r14; spilling x393 to mem
setc r14b; spill CF x397 to reg (r14)
mov byte [ rsp + 0x230 ], al; spilling byte x327 to mem
movzx rax, byte [ rsp + 0x1f0 ]; load byte memx367 to register64
clc;
mov byte [ rsp + 0x238 ], bl; spilling byte x242 to mem
mov rbx, -0x1 ; moving imm to reg
adcx rax, rbx; loading flag
adcx r11, rbp
mov rax, [ rsi + 0x28 ]; load m64 x5 to register64
mov rbp, rdx; preserving value of x366 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov byte [ rsp + 0x240 ], r14b; spilling byte x397 to mem
mulx rbx, r14, r9; x170, x169<- x2 * arg1[4]
mov rdx, 0x7bc65c783158aea3 ; moving imm to reg
mov [ rsp + 0x248 ], rbx; spilling x170 to mem
mov byte [ rsp + 0x250 ], r15b; spilling byte x227 to mem
mulx rbx, r15, r8; x213, x212<- x192 * 0x7bc65c783158aea3
xchg rdx, rax; x5, swapping with 0x7bc65c783158aea3, which is currently in rdx
mov [ rsp + 0x258 ], rbx; spilling x213 to mem
mulx rax, rbx, [ rsi + 0x8 ]; x437, x436<- x5 * arg1[1]
mov [ rsp + 0x260 ], rax; spilling x437 to mem
mov rax, [ rsp + 0x208 ]; x185, copying x172 here, cause x172 is needed in a reg for other than x185, namely all: , x185--x186, size: 1
adox rax, r14
setc r14b; spill CF x369 to reg (r14)
clc;
mov [ rsp + 0x268 ], rbx; spilling x436 to mem
mov rbx, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, rbx; loading flag
adcx r11, r10
setc cl; spill CF x412 to reg (rcx)
clc;
movzx r12, r12b
adcx r12, rbx; loading flag
adcx rax, [ rsp + 0x180 ]
mulx r12, r10, [ rsi + 0x0 ]; x439, x438<- x5 * arg1[0]
seto bl; spill OF x186 to reg (rbx)
mov [ rsp + 0x270 ], r12; spilling x439 to mem
movzx r12, byte [ rsp + 0x250 ]; load byte memx227 to register64
mov byte [ rsp + 0x278 ], cl; spilling byte x412 to mem
mov rcx, -0x1 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rcx, -0x1 ; moving imm to reg
adox r12, rcx; loading flag
adox r15, [ rsp + 0x1e0 ]
seto r12b; spill OF x229 to reg (r12)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r10, r11
mov r11, rdx; preserving value of x5 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov byte [ rsp + 0x280 ], r12b; spilling byte x229 to mem
mulx rcx, r12, r13; x348, x347<- x4 * arg1[2]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x288 ], rcx; spilling x348 to mem
mov byte [ rsp + 0x290 ], bl; spilling byte x186 to mem
mulx rcx, rbx, r10; x482, x481<- x453 * 0xffffffffffffffff
seto dl; spill OF x454 to reg (rdx)
mov [ rsp + 0x298 ], rcx; spilling x482 to mem
movzx rcx, byte [ rsp + 0x238 ]; load byte memx242 to register64
mov byte [ rsp + 0x2a0 ], r14b; spilling byte x369 to mem
mov r14, -0x1 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r14, -0x1 ; moving imm to reg
adox rcx, r14; loading flag
adox rax, r15
seto cl; spill OF x244 to reg (rcx)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rbx, r10
seto bl; spill OF x497 to reg (rbx)
movzx r15, byte [ rsp + 0x218 ]; load byte memx354 to register64
dec r14; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
adox r15, r14; loading flag
adox r12, [ rsp + 0x200 ]
setc r15b; spill CF x201 to reg (r15)
movzx r14, byte [ rsp + 0x220 ]; load byte memx284 to register64
clc;
mov byte [ rsp + 0x2a8 ], cl; spilling byte x244 to mem
mov rcx, -0x1 ; moving imm to reg
adcx r14, rcx; loading flag
adcx rax, [ rsp + 0x20 ]
setc r14b; spill CF x286 to reg (r14)
movzx rcx, byte [ rsp + 0x230 ]; load byte memx327 to register64
clc;
mov byte [ rsp + 0x2b0 ], r15b; spilling byte x201 to mem
mov r15, -0x1 ; moving imm to reg
adcx rcx, r15; loading flag
adcx rax, [ rsp + 0x1b8 ]
setc cl; spill CF x329 to reg (rcx)
movzx r15, byte [ rsp + 0x2a0 ]; load byte memx369 to register64
clc;
mov byte [ rsp + 0x2b8 ], r14b; spilling byte x286 to mem
mov r14, -0x1 ; moving imm to reg
adcx r15, r14; loading flag
adcx rax, r12
mov r15, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r15; 0xffffffffffffffff, swapping with x454, which is currently in rdx
mulx r12, r14, rbp; x391, x390<- x366 * 0xffffffffffffffff
seto dl; spill OF x356 to reg (rdx)
mov byte [ rsp + 0x2c0 ], cl; spilling byte x329 to mem
movzx rcx, byte [ rsp + 0x240 ]; load byte memx397 to register64
mov [ rsp + 0x2c8 ], r12; spilling x391 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rcx, r12; loading flag
adox r14, [ rsp + 0x228 ]
setc cl; spill CF x371 to reg (rcx)
movzx r12, byte [ rsp + 0x278 ]; load byte memx412 to register64
clc;
mov byte [ rsp + 0x2d0 ], dl; spilling byte x356 to mem
mov rdx, -0x1 ; moving imm to reg
adcx r12, rdx; loading flag
adcx rax, r14
mov r12, 0x6cfc5fd681c52056 ; moving imm to reg
mov rdx, r8; x192 to rdx
mulx r8, r14, r12; x211, x210<- x192 * 0x6cfc5fd681c52056
mov r12, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r10; x453, swapping with x192, which is currently in rdx
mov [ rsp + 0x2d8 ], r8; spilling x211 to mem
mov byte [ rsp + 0x2e0 ], cl; spilling byte x371 to mem
mulx r8, rcx, r12; x480, x479<- x453 * 0xffffffffffffffff
setc r12b; spill CF x414 to reg (r12)
clc;
adcx rcx, [ rsp + 0x298 ]
mov [ rsp + 0x2e8 ], r8; spilling x480 to mem
mov r8, [ rsp + 0x270 ]; load m64 x439 to register64
mov byte [ rsp + 0x2f0 ], r12b; spilling byte x414 to mem
setc r12b; spill CF x484 to reg (r12)
clc;
adcx r8, [ rsp + 0x268 ]
mov byte [ rsp + 0x2f8 ], r12b; spilling byte x484 to mem
seto r12b; spill OF x399 to reg (r12)
mov [ rsp + 0x300 ], r14; spilling x210 to mem
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r15, r15b
adox r15, r14; loading flag
adox rax, r8
xchg rdx, r9; x2, swapping with x453, which is currently in rdx
mulx r15, r8, [ rsi + 0x28 ]; x168, x167<- x2 * arg1[5]
seto r14b; spill OF x456 to reg (r14)
mov [ rsp + 0x308 ], r15; spilling x168 to mem
movzx r15, byte [ rsp + 0x290 ]; load byte memx186 to register64
mov byte [ rsp + 0x310 ], r12b; spilling byte x399 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, r12; loading flag
adox r8, [ rsp + 0x248 ]
seto r15b; spill OF x188 to reg (r15)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, r12; loading flag
adox rax, rcx
setc bl; spill CF x441 to reg (rbx)
movzx rcx, byte [ rsp + 0x2b0 ]; load byte memx201 to register64
clc;
adcx rcx, r12; loading flag
adcx r8, [ rsp + 0x178 ]
setc cl; spill CF x203 to reg (rcx)
clc;
adcx rax, [ rsp + 0x18 ]
mov r12, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r12; 0xffffffffffffffff, swapping with x2, which is currently in rdx
mov byte [ rsp + 0x318 ], cl; spilling byte x203 to mem
mov byte [ rsp + 0x320 ], r14b; spilling byte x456 to mem
mulx rcx, r14, rax; x569, x568<- x540 * 0xffffffffffffffff
mov rdx, 0xfdc1767ae2ffffff ; moving imm to reg
mov [ rsp + 0x328 ], rcx; spilling x569 to mem
mov byte [ rsp + 0x330 ], bl; spilling byte x441 to mem
mulx rcx, rbx, rbp; x389, x388<- x366 * 0xfdc1767ae2ffffff
setc dl; spill CF x541 to reg (rdx)
mov [ rsp + 0x338 ], rcx; spilling x389 to mem
movzx rcx, byte [ rsp + 0x310 ]; load byte memx399 to register64
clc;
mov byte [ rsp + 0x340 ], r15b; spilling byte x188 to mem
mov r15, -0x1 ; moving imm to reg
adcx rcx, r15; loading flag
adcx rbx, [ rsp + 0x2c8 ]
setc cl; spill CF x401 to reg (rcx)
clc;
adcx r14, rax
mov r14, [ rsp + 0x300 ]; load m64 x210 to register64
seto r15b; spill OF x499 to reg (r15)
mov byte [ rsp + 0x348 ], cl; spilling byte x401 to mem
movzx rcx, byte [ rsp + 0x280 ]; load byte memx229 to register64
mov byte [ rsp + 0x350 ], dl; spilling byte x541 to mem
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
adox rcx, rdx; loading flag
adox r14, [ rsp + 0x258 ]
setc cl; spill CF x584 to reg (rcx)
movzx rdx, byte [ rsp + 0x2a8 ]; load byte memx244 to register64
clc;
mov byte [ rsp + 0x358 ], r15b; spilling byte x499 to mem
mov r15, -0x1 ; moving imm to reg
adcx rdx, r15; loading flag
adcx r8, r14
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r14, r15, r13; x346, x345<- x4 * arg1[3]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x360 ], r14; spilling x346 to mem
mulx r12, r14, r12; x166, x165<- x2 * arg1[6]
setc dl; spill CF x246 to reg (rdx)
mov [ rsp + 0x368 ], r12; spilling x166 to mem
movzx r12, byte [ rsp + 0x2d0 ]; load byte memx356 to register64
clc;
mov byte [ rsp + 0x370 ], cl; spilling byte x584 to mem
mov rcx, -0x1 ; moving imm to reg
adcx r12, rcx; loading flag
adcx r15, [ rsp + 0x288 ]
setc r12b; spill CF x358 to reg (r12)
movzx rcx, byte [ rsp + 0x2b8 ]; load byte memx286 to register64
clc;
mov byte [ rsp + 0x378 ], dl; spilling byte x246 to mem
mov rdx, -0x1 ; moving imm to reg
adcx rcx, rdx; loading flag
adcx r8, [ rsp + 0x10 ]
setc cl; spill CF x288 to reg (rcx)
movzx rdx, byte [ rsp + 0x2c0 ]; load byte memx329 to register64
clc;
mov byte [ rsp + 0x380 ], r12b; spilling byte x358 to mem
mov r12, -0x1 ; moving imm to reg
adcx rdx, r12; loading flag
adcx r8, [ rsp + 0x1b0 ]
mov rdx, r11; x5 to rdx
mulx r11, r12, [ rsi + 0x10 ]; x435, x434<- x5 * arg1[2]
mov [ rsp + 0x388 ], r11; spilling x435 to mem
seto r11b; spill OF x231 to reg (r11)
mov byte [ rsp + 0x390 ], cl; spilling byte x288 to mem
movzx rcx, byte [ rsp + 0x2e0 ]; load byte memx371 to register64
mov [ rsp + 0x398 ], r12; spilling x434 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
adox rcx, r12; loading flag
adox r8, r15
setc cl; spill CF x331 to reg (rcx)
movzx r15, byte [ rsp + 0x340 ]; load byte memx188 to register64
clc;
adcx r15, r12; loading flag
adcx r14, [ rsp + 0x308 ]
setc r15b; spill CF x190 to reg (r15)
movzx r12, byte [ rsp + 0x2f0 ]; load byte memx414 to register64
clc;
mov byte [ rsp + 0x3a0 ], cl; spilling byte x331 to mem
mov rcx, -0x1 ; moving imm to reg
adcx r12, rcx; loading flag
adcx r8, rbx
mov r12, [ rsp + 0x398 ]; load m64 x434 to register64
setc bl; spill CF x416 to reg (rbx)
movzx rcx, byte [ rsp + 0x330 ]; load byte memx441 to register64
clc;
mov byte [ rsp + 0x3a8 ], r15b; spilling byte x190 to mem
mov r15, -0x1 ; moving imm to reg
adcx rcx, r15; loading flag
adcx r12, [ rsp + 0x260 ]
mov rcx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r9; x453, swapping with x5, which is currently in rdx
mov byte [ rsp + 0x3b0 ], bl; spilling byte x416 to mem
mulx r15, rbx, rcx; x478, x477<- x453 * 0xffffffffffffffff
setc cl; spill CF x443 to reg (rcx)
mov [ rsp + 0x3b8 ], r15; spilling x478 to mem
movzx r15, byte [ rsp + 0x320 ]; load byte memx456 to register64
clc;
mov byte [ rsp + 0x3c0 ], r11b; spilling byte x231 to mem
mov r11, -0x1 ; moving imm to reg
adcx r15, r11; loading flag
adcx r8, r12
setc r15b; spill CF x458 to reg (r15)
movzx r12, byte [ rsp + 0x2f8 ]; load byte memx484 to register64
clc;
adcx r12, r11; loading flag
adcx rbx, [ rsp + 0x2e8 ]
setc r12b; spill CF x486 to reg (r12)
movzx r11, byte [ rsp + 0x358 ]; load byte memx499 to register64
clc;
mov byte [ rsp + 0x3c8 ], r15b; spilling byte x458 to mem
mov r15, -0x1 ; moving imm to reg
adcx r11, r15; loading flag
adcx r8, rbx
setc r11b; spill CF x501 to reg (r11)
movzx rbx, byte [ rsp + 0x350 ]; load byte memx541 to register64
clc;
adcx rbx, r15; loading flag
adcx r8, [ rsp + 0x70 ]
mov rbx, 0x2341f27177344 ; moving imm to reg
xchg rdx, rbx; 0x2341f27177344, swapping with x453, which is currently in rdx
mulx r10, r15, r10; x209, x208<- x192 * 0x2341f27177344
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x3d0 ], r10; spilling x209 to mem
mov byte [ rsp + 0x3d8 ], r11b; spilling byte x501 to mem
mulx r10, r11, rax; x567, x566<- x540 * 0xffffffffffffffff
setc dl; spill CF x543 to reg (rdx)
mov [ rsp + 0x3e0 ], r10; spilling x567 to mem
movzx r10, byte [ rsp + 0x318 ]; load byte memx203 to register64
clc;
mov byte [ rsp + 0x3e8 ], r12b; spilling byte x486 to mem
mov r12, -0x1 ; moving imm to reg
adcx r10, r12; loading flag
adcx r14, [ rsp + 0x170 ]
setc r10b; spill CF x205 to reg (r10)
clc;
adcx r11, [ rsp + 0x328 ]
setc r12b; spill CF x571 to reg (r12)
mov byte [ rsp + 0x3f0 ], r10b; spilling byte x205 to mem
movzx r10, byte [ rsp + 0x370 ]; load byte memx584 to register64
clc;
mov byte [ rsp + 0x3f8 ], dl; spilling byte x543 to mem
mov rdx, -0x1 ; moving imm to reg
adcx r10, rdx; loading flag
adcx r8, r11
setc r10b; spill CF x586 to reg (r10)
movzx r11, byte [ rsp + 0x3c0 ]; load byte memx231 to register64
clc;
adcx r11, rdx; loading flag
adcx r15, [ rsp + 0x2d8 ]
setc r11b; spill CF x233 to reg (r11)
movzx rdx, byte [ rsp + 0x378 ]; load byte memx246 to register64
clc;
mov byte [ rsp + 0x400 ], r10b; spilling byte x586 to mem
mov r10, -0x1 ; moving imm to reg
adcx rdx, r10; loading flag
adcx r14, r15
setc dl; spill CF x248 to reg (rdx)
movzx r15, byte [ rsp + 0x390 ]; load byte memx288 to register64
clc;
adcx r15, r10; loading flag
adcx r14, [ rsp + 0x8 ]
setc r15b; spill CF x290 to reg (r15)
movzx r10, byte [ rsp + 0x3a0 ]; load byte memx331 to register64
clc;
mov byte [ rsp + 0x408 ], dl; spilling byte x248 to mem
mov rdx, -0x1 ; moving imm to reg
adcx r10, rdx; loading flag
adcx r14, [ rsp + 0x1a8 ]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov byte [ rsp + 0x410 ], r15b; spilling byte x290 to mem
mulx r10, r15, r13; x344, x343<- x4 * arg1[4]
setc dl; spill CF x333 to reg (rdx)
mov [ rsp + 0x418 ], r10; spilling x344 to mem
movzx r10, byte [ rsp + 0x380 ]; load byte memx358 to register64
clc;
mov byte [ rsp + 0x420 ], r11b; spilling byte x233 to mem
mov r11, -0x1 ; moving imm to reg
adcx r10, r11; loading flag
adcx r15, [ rsp + 0x360 ]
setc r10b; spill CF x360 to reg (r10)
seto r11b; spill OF x373 to reg (r11)
mov byte [ rsp + 0x428 ], dl; spilling byte x333 to mem
mov rdx, r8; x600, copying x585 here, cause x585 is needed in a reg for other than x600, namely all: , x600--x601, x616, size: 2
mov byte [ rsp + 0x430 ], r12b; spilling byte x571 to mem
mov r12, 0xffffffffffffffff ; moving imm to reg
sub rdx, r12
xchg rdx, r9; x5, swapping with x600, which is currently in rdx
mov [ rsp + 0x438 ], r9; spilling x600 to mem
mulx r12, r9, [ rsi + 0x18 ]; x433, x432<- x5 * arg1[3]
mov byte [ rsp + 0x440 ], r10b; spilling byte x360 to mem
mov r10, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, r10; 0x7bc65c783158aea3, swapping with x5, which is currently in rdx
mov [ rsp + 0x448 ], r12; spilling x433 to mem
mov [ rsp + 0x450 ], r15; spilling x359 to mem
mulx r12, r15, rbp; x387, x386<- x366 * 0x7bc65c783158aea3
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, rdx; loading flag
adox r9, [ rsp + 0x388 ]
setc cl; spill CF x601 to reg (rcx)
clc;
movzx r11, r11b
adcx r11, rdx; loading flag
adcx r14, [ rsp + 0x450 ]
seto r11b; spill OF x445 to reg (r11)
movzx rdx, byte [ rsp + 0x348 ]; load byte memx401 to register64
mov byte [ rsp + 0x458 ], cl; spilling byte x601 to mem
mov rcx, -0x1 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rcx, -0x1 ; moving imm to reg
adox rdx, rcx; loading flag
adox r15, [ rsp + 0x338 ]
mov rdx, 0xfdc1767ae2ffffff ; moving imm to reg
mov byte [ rsp + 0x460 ], r11b; spilling byte x445 to mem
mulx rcx, r11, rbx; x476, x475<- x453 * 0xfdc1767ae2ffffff
setc dl; spill CF x375 to reg (rdx)
mov [ rsp + 0x468 ], rcx; spilling x476 to mem
movzx rcx, byte [ rsp + 0x3b0 ]; load byte memx416 to register64
clc;
mov [ rsp + 0x470 ], r12; spilling x387 to mem
mov r12, -0x1 ; moving imm to reg
adcx rcx, r12; loading flag
adcx r14, r15
setc cl; spill CF x418 to reg (rcx)
movzx r15, byte [ rsp + 0x3e8 ]; load byte memx486 to register64
clc;
adcx r15, r12; loading flag
adcx r11, [ rsp + 0x3b8 ]
mov r15, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, rbp; x366, swapping with x375, which is currently in rdx
mov byte [ rsp + 0x478 ], cl; spilling byte x418 to mem
mulx r12, rcx, r15; x385, x384<- x366 * 0x6cfc5fd681c52056
setc r15b; spill CF x488 to reg (r15)
mov [ rsp + 0x480 ], r12; spilling x385 to mem
movzx r12, byte [ rsp + 0x3c8 ]; load byte memx458 to register64
clc;
mov byte [ rsp + 0x488 ], bpl; spilling byte x375 to mem
mov rbp, -0x1 ; moving imm to reg
adcx r12, rbp; loading flag
adcx r14, r9
setc r12b; spill CF x460 to reg (r12)
movzx r9, byte [ rsp + 0x3d8 ]; load byte memx501 to register64
clc;
adcx r9, rbp; loading flag
adcx r14, r11
mov r9, [ rsp + 0x470 ]; x404, copying x387 here, cause x387 is needed in a reg for other than x404, namely all: , x404--x405, size: 1
adox r9, rcx
movzx r11, byte [ rsp + 0x3a8 ]; x191, copying x190 here, cause x190 is needed in a reg for other than x191, namely all: , x191, size: 1
mov rcx, [ rsp + 0x368 ]; load m64 x166 to register64
lea r11, [ r11 + rcx ]; r8/64 + m8
mov rcx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rcx; 0xffffffffffffffff, swapping with x366, which is currently in rdx
mov byte [ rsp + 0x490 ], r15b; spilling byte x488 to mem
mulx rbp, r15, rax; x565, x564<- x540 * 0xffffffffffffffff
setc dl; spill CF x503 to reg (rdx)
mov [ rsp + 0x498 ], rbp; spilling x565 to mem
movzx rbp, byte [ rsp + 0x3f8 ]; load byte memx543 to register64
clc;
mov byte [ rsp + 0x4a0 ], r12b; spilling byte x460 to mem
mov r12, -0x1 ; moving imm to reg
adcx rbp, r12; loading flag
adcx r14, [ rsp + 0x68 ]
setc bpl; spill CF x545 to reg (rbp)
movzx r12, byte [ rsp + 0x430 ]; load byte memx571 to register64
clc;
mov byte [ rsp + 0x4a8 ], dl; spilling byte x503 to mem
mov rdx, -0x1 ; moving imm to reg
adcx r12, rdx; loading flag
adcx r15, [ rsp + 0x3e0 ]
movzx r12, byte [ rsp + 0x420 ]; x234, copying x233 here, cause x233 is needed in a reg for other than x234, namely all: , x234, size: 1
mov rdx, [ rsp + 0x3d0 ]; load m64 x209 to register64
lea r12, [ r12 + rdx ]; r8/64 + m8
setc dl; spill CF x573 to reg (rdx)
mov byte [ rsp + 0x4b0 ], bpl; spilling byte x545 to mem
movzx rbp, byte [ rsp + 0x3f0 ]; load byte memx205 to register64
clc;
mov [ rsp + 0x4b8 ], r9; spilling x404 to mem
mov r9, -0x1 ; moving imm to reg
adcx rbp, r9; loading flag
adcx r11, [ rsp + 0x168 ]
mov bpl, dl; preserving value of x573 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x4c0 ], r15; spilling x572 to mem
mulx r9, r15, r10; x431, x430<- x5 * arg1[4]
setc dl; spill CF x207 to reg (rdx)
mov [ rsp + 0x4c8 ], r9; spilling x431 to mem
movzx r9, byte [ rsp + 0x408 ]; load byte memx248 to register64
clc;
mov byte [ rsp + 0x4d0 ], bpl; spilling byte x573 to mem
mov rbp, -0x1 ; moving imm to reg
adcx r9, rbp; loading flag
adcx r11, r12
setc r9b; spill CF x250 to reg (r9)
movzx r12, byte [ rsp + 0x460 ]; load byte memx445 to register64
clc;
adcx r12, rbp; loading flag
adcx r15, [ rsp + 0x448 ]
setc r12b; spill CF x447 to reg (r12)
movzx rbp, byte [ rsp + 0x410 ]; load byte memx290 to register64
clc;
mov byte [ rsp + 0x4d8 ], dl; spilling byte x207 to mem
mov rdx, -0x1 ; moving imm to reg
adcx rbp, rdx; loading flag
adcx r11, [ rsp + 0x28 ]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov byte [ rsp + 0x4e0 ], r12b; spilling byte x447 to mem
mulx rbp, r12, r13; x342, x341<- x4 * arg1[5]
mov rdx, 0xfdc1767ae2ffffff ; moving imm to reg
mov byte [ rsp + 0x4e8 ], r9b; spilling byte x250 to mem
mov [ rsp + 0x4f0 ], rbp; spilling x342 to mem
mulx r9, rbp, rax; x563, x562<- x540 * 0xfdc1767ae2ffffff
seto dl; spill OF x405 to reg (rdx)
mov [ rsp + 0x4f8 ], r9; spilling x563 to mem
movzx r9, byte [ rsp + 0x440 ]; load byte memx360 to register64
mov [ rsp + 0x500 ], rbp; spilling x562 to mem
mov rbp, 0x0 ; moving imm to reg
dec rbp; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r9, rbp; loading flag
adox r12, [ rsp + 0x418 ]
seto r9b; spill OF x362 to reg (r9)
movzx rbp, byte [ rsp + 0x400 ]; load byte memx586 to register64
mov byte [ rsp + 0x508 ], dl; spilling byte x405 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbp, rdx; loading flag
adox r14, [ rsp + 0x4c0 ]
setc bpl; spill CF x292 to reg (rbp)
movzx rdx, byte [ rsp + 0x428 ]; load byte memx333 to register64
clc;
mov byte [ rsp + 0x510 ], r9b; spilling byte x362 to mem
mov r9, -0x1 ; moving imm to reg
adcx rdx, r9; loading flag
adcx r11, [ rsp + 0x1d8 ]
setc dl; spill CF x335 to reg (rdx)
movzx r9, byte [ rsp + 0x488 ]; load byte memx375 to register64
clc;
mov byte [ rsp + 0x518 ], bpl; spilling byte x292 to mem
mov rbp, -0x1 ; moving imm to reg
adcx r9, rbp; loading flag
adcx r11, r12
mov r9, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, r9; 0x7bc65c783158aea3, swapping with x335, which is currently in rdx
mulx r12, rbp, rbx; x474, x473<- x453 * 0x7bc65c783158aea3
setc dl; spill CF x377 to reg (rdx)
mov byte [ rsp + 0x520 ], r9b; spilling byte x335 to mem
movzx r9, byte [ rsp + 0x478 ]; load byte memx418 to register64
clc;
mov [ rsp + 0x528 ], r12; spilling x474 to mem
mov r12, -0x1 ; moving imm to reg
adcx r9, r12; loading flag
adcx r11, [ rsp + 0x4b8 ]
setc r9b; spill CF x420 to reg (r9)
movzx r12, byte [ rsp + 0x4a0 ]; load byte memx460 to register64
clc;
mov byte [ rsp + 0x530 ], dl; spilling byte x377 to mem
mov rdx, -0x1 ; moving imm to reg
adcx r12, rdx; loading flag
adcx r11, r15
seto r12b; spill OF x588 to reg (r12)
movzx r15, byte [ rsp + 0x490 ]; load byte memx488 to register64
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
adox r15, rdx; loading flag
adox rbp, [ rsp + 0x468 ]
setc r15b; spill CF x462 to reg (r15)
seto dl; spill OF x490 to reg (rdx)
mov byte [ rsp + 0x538 ], r9b; spilling byte x420 to mem
movzx r9, byte [ rsp + 0x458 ]; x601, copying x601 here, cause x601 is needed in a reg for other than x601, namely all: , x602--x603, size: 1
add r9, -0x1
mov r9, r14; x602, copying x587 here, cause x587 is needed in a reg for other than x602, namely all: , x602--x603, x617, size: 2
mov byte [ rsp + 0x540 ], r12b; spilling byte x588 to mem
mov r12, 0xffffffffffffffff ; moving imm to reg
sbb r9, r12
movzx r12, byte [ rsp + 0x4a8 ]; load byte memx503 to register64
mov [ rsp + 0x548 ], r9; spilling x602 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r12, r9; loading flag
adox r11, rbp
xchg rdx, r13; x4, swapping with x490, which is currently in rdx
mulx rdx, r12, [ rsi + 0x30 ]; x340, x339<- x4 * arg1[6]
seto bpl; spill OF x505 to reg (rbp)
movzx r9, byte [ rsp + 0x510 ]; load byte memx362 to register64
mov byte [ rsp + 0x550 ], r15b; spilling byte x462 to mem
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r15, -0x1 ; moving imm to reg
adox r9, r15; loading flag
adox r12, [ rsp + 0x4f0 ]
mov r9, [ rsp + 0x500 ]; load m64 x562 to register64
seto r15b; spill OF x364 to reg (r15)
mov byte [ rsp + 0x558 ], bpl; spilling byte x505 to mem
movzx rbp, byte [ rsp + 0x4d0 ]; load byte memx573 to register64
mov [ rsp + 0x560 ], rdx; spilling x340 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbp, rdx; loading flag
adox r9, [ rsp + 0x498 ]
movzx rbp, byte [ rsp + 0x4e8 ]; x251, copying x250 here, cause x250 is needed in a reg for other than x251, namely all: , x251, size: 1
movzx rdx, byte [ rsp + 0x4d8 ]; load byte memx207 to register64
lea rbp, [ rbp + rdx ]; r64+m8
seto dl; spill OF x575 to reg (rdx)
mov byte [ rsp + 0x568 ], r15b; spilling byte x364 to mem
movzx r15, byte [ rsp + 0x4b0 ]; load byte memx545 to register64
mov [ rsp + 0x570 ], r12; spilling x363 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, r12; loading flag
adox r11, [ rsp + 0x58 ]
setc r15b; spill CF x603 to reg (r15)
movzx r12, byte [ rsp + 0x540 ]; load byte memx588 to register64
clc;
mov byte [ rsp + 0x578 ], dl; spilling byte x575 to mem
mov rdx, -0x1 ; moving imm to reg
adcx r12, rdx; loading flag
adcx r11, r9
mov r12, 0x2341f27177344 ; moving imm to reg
mov rdx, r12; 0x2341f27177344 to rdx
mulx rcx, r12, rcx; x383, x382<- x366 * 0x2341f27177344
setc r9b; spill CF x590 to reg (r9)
seto dl; spill OF x547 to reg (rdx)
mov [ rsp + 0x580 ], rcx; spilling x383 to mem
movzx rcx, r15b; x603, copying x603 here, cause x603 is needed in a reg for other than x603, namely all: , x604--x605, size: 1
add rcx, -0x1
mov r15, r11; x604, copying x589 here, cause x589 is needed in a reg for other than x604, namely all: , x604--x605, x618, size: 2
mov rcx, 0xffffffffffffffff ; moving imm to reg
sbb r15, rcx
movzx rcx, byte [ rsp + 0x518 ]; load byte memx292 to register64
mov [ rsp + 0x588 ], r15; spilling x604 to mem
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rcx, r15; loading flag
adox rbp, [ rsp + 0x38 ]
xchg rdx, r10; x5, swapping with x547, which is currently in rdx
mulx rcx, r15, [ rsi + 0x28 ]; x429, x428<- x5 * arg1[5]
mov byte [ rsp + 0x590 ], r9b; spilling byte x590 to mem
setc r9b; spill CF x605 to reg (r9)
mov [ rsp + 0x598 ], rcx; spilling x429 to mem
movzx rcx, byte [ rsp + 0x508 ]; load byte memx405 to register64
clc;
mov byte [ rsp + 0x5a0 ], r10b; spilling byte x547 to mem
mov r10, -0x1 ; moving imm to reg
adcx rcx, r10; loading flag
adcx r12, [ rsp + 0x480 ]
mov rcx, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, rcx; 0x6cfc5fd681c52056, swapping with x5, which is currently in rdx
mov byte [ rsp + 0x5a8 ], r9b; spilling byte x605 to mem
mulx r10, r9, rbx; x472, x471<- x453 * 0x6cfc5fd681c52056
setc dl; spill CF x407 to reg (rdx)
clc;
mov [ rsp + 0x5b0 ], r15; spilling x428 to mem
mov r15, -0x1 ; moving imm to reg
movzx r13, r13b
adcx r13, r15; loading flag
adcx r9, [ rsp + 0x528 ]
setc r13b; spill CF x492 to reg (r13)
movzx r15, byte [ rsp + 0x520 ]; load byte memx335 to register64
clc;
mov [ rsp + 0x5b8 ], r9; spilling x491 to mem
mov r9, -0x1 ; moving imm to reg
adcx r15, r9; loading flag
adcx rbp, [ rsp + 0x1d0 ]
mov r15, 0x2341f27177344 ; moving imm to reg
xchg rdx, r15; 0x2341f27177344, swapping with x407, which is currently in rdx
mulx rbx, r9, rbx; x470, x469<- x453 * 0x2341f27177344
seto dl; spill OF x338 to reg (rdx)
adc dl, 0x0
movzx rdx, dl
add r13b, 0xFF; load flag from rm/8 into CF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
setc r13b; since that has deps, resore it whereever it was
adcx r10, r9
movzx r13, r15b; x408, copying x407 here, cause x407 is needed in a reg for other than x408, namely all: , x408, size: 1
adox r13, [ rsp + 0x580 ]
movzx r15, byte [ rsp + 0x530 ]; load byte memx377 to register64
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, r9; loading flag
adox rbp, [ rsp + 0x570 ]
setc r15b; spill CF x494 to reg (r15)
movzx r9, byte [ rsp + 0x538 ]; load byte memx420 to register64
clc;
mov [ rsp + 0x5c0 ], rbx; spilling x470 to mem
mov rbx, -0x1 ; moving imm to reg
adcx r9, rbx; loading flag
adcx rbp, r12
movzx r9, byte [ rsp + 0x568 ]; x365, copying x364 here, cause x364 is needed in a reg for other than x365, namely all: , x365, size: 1
mov r12, [ rsp + 0x560 ]; load m64 x340 to register64
lea r9, [ r9 + r12 ]; r8/64 + m8
mov r12, [ rsp + 0x5b0 ]; load m64 x428 to register64
setc bl; spill CF x422 to reg (rbx)
mov byte [ rsp + 0x5c8 ], r15b; spilling byte x494 to mem
movzx r15, byte [ rsp + 0x4e0 ]; load byte memx447 to register64
clc;
mov [ rsp + 0x5d0 ], r10; spilling x493 to mem
mov r10, -0x1 ; moving imm to reg
adcx r15, r10; loading flag
adcx r12, [ rsp + 0x4c8 ]
movzx r15, dl; x380, copying x338 here, cause x338 is needed in a reg for other than x380, namely all: , x380--x381, size: 1
adox r15, r9
mov rdx, 0x7bc65c783158aea3 ; moving imm to reg
mulx r9, r10, rax; x561, x560<- x540 * 0x7bc65c783158aea3
setc dl; spill CF x449 to reg (rdx)
mov [ rsp + 0x5d8 ], r9; spilling x561 to mem
movzx r9, byte [ rsp + 0x550 ]; load byte memx462 to register64
clc;
mov [ rsp + 0x5e0 ], r13; spilling x408 to mem
mov r13, -0x1 ; moving imm to reg
adcx r9, r13; loading flag
adcx rbp, r12
setc r9b; spill CF x464 to reg (r9)
movzx r12, byte [ rsp + 0x578 ]; load byte memx575 to register64
clc;
adcx r12, r13; loading flag
adcx r10, [ rsp + 0x4f8 ]
setc r12b; spill CF x577 to reg (r12)
movzx r13, byte [ rsp + 0x558 ]; load byte memx505 to register64
clc;
mov byte [ rsp + 0x5e8 ], r9b; spilling byte x464 to mem
mov r9, -0x1 ; moving imm to reg
adcx r13, r9; loading flag
adcx rbp, [ rsp + 0x5b8 ]
setc r13b; spill CF x507 to reg (r13)
movzx r9, byte [ rsp + 0x5a0 ]; load byte memx547 to register64
clc;
mov byte [ rsp + 0x5f0 ], r12b; spilling byte x577 to mem
mov r12, -0x1 ; moving imm to reg
adcx r9, r12; loading flag
adcx rbp, [ rsp + 0x50 ]
setc r9b; spill CF x549 to reg (r9)
clc;
movzx rbx, bl
adcx rbx, r12; loading flag
adcx r15, [ rsp + 0x5e0 ]
xchg rdx, rcx; x5, swapping with x449, which is currently in rdx
mulx rdx, rbx, [ rsi + 0x30 ]; x427, x426<- x5 * arg1[6]
seto r12b; spill OF x425 to reg (r12)
adc r12b, 0x0
movzx r12, r12b
add cl, 0xFF; load flag from rm/8 into CF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
setc cl; since that has deps, resore it whereever it was
adcx rbx, [ rsp + 0x598 ]
adc rdx, 0x0
add byte [ rsp + 0x590 ], 0xFF; load flag from rm/8 into CF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
setc [ rsp + 0x590 ]; since that has deps, resore it whereever it was
adcx rbp, r10
movzx rcx, byte [ rsp + 0x5e8 ]; load byte memx464 to register64
mov r10, -0x1 ; moving imm to reg
adox rcx, r10; loading flag
adox r15, rbx
setc cl; spill CF x592 to reg (rcx)
seto bl; spill OF x466 to reg (rbx)
movzx r10, byte [ rsp + 0x5a8 ]; x605, copying x605 here, cause x605 is needed in a reg for other than x605, namely all: , x606--x607, size: 1
add r10, -0x1
mov r10, rbp; x606, copying x591 here, cause x591 is needed in a reg for other than x606, namely all: , x606--x607, x619, size: 2
mov byte [ rsp + 0x5f8 ], r9b; spilling byte x549 to mem
mov r9, 0xfdc1767ae2ffffff ; moving imm to reg
sbb r10, r9
mov r9, -0x1 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r9, -0x1 ; moving imm to reg
movzx r12, r12b
movzx rbx, bl
adox rbx, r9; loading flag
adox rdx, r12
mov r12, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, rax; x540, swapping with x467, which is currently in rdx
mulx rbx, r9, r12; x559, x558<- x540 * 0x6cfc5fd681c52056
setc r12b; spill CF x607 to reg (r12)
mov [ rsp + 0x600 ], r10; spilling x606 to mem
movzx r10, byte [ rsp + 0x5f0 ]; load byte memx577 to register64
clc;
mov [ rsp + 0x608 ], rbx; spilling x559 to mem
mov rbx, -0x1 ; moving imm to reg
adcx r10, rbx; loading flag
adcx r9, [ rsp + 0x5d8 ]
setc r10b; spill CF x579 to reg (r10)
clc;
movzx r13, r13b
adcx r13, rbx; loading flag
adcx r15, [ rsp + 0x5d0 ]
seto r13b; spill OF x468 to reg (r13)
movzx rbx, byte [ rsp + 0x5f8 ]; load byte memx549 to register64
mov byte [ rsp + 0x610 ], r10b; spilling byte x579 to mem
mov r10, -0x1 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r10, -0x1 ; moving imm to reg
adox rbx, r10; loading flag
adox r15, [ rsp + 0x48 ]
seto bl; spill OF x551 to reg (rbx)
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r10, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r10; loading flag
adox r15, r9
movzx rcx, byte [ rsp + 0x5c8 ]; x495, copying x494 here, cause x494 is needed in a reg for other than x495, namely all: , x495, size: 1
mov r9, [ rsp + 0x5c0 ]; load m64 x470 to register64
lea rcx, [ rcx + r9 ]; r8/64 + m8
adcx rcx, rax
mov r9, 0x2341f27177344 ; moving imm to reg
mulx rdx, rax, r9; x557, x556<- x540 * 0x2341f27177344
movzx r10, r13b; x512, copying x468 here, cause x468 is needed in a reg for other than x512, namely all: , x512, size: 1
mov r9, 0x0 ; moving imm to reg
adcx r10, r9
seto r13b; spill OF x594 to reg (r13)
movzx r9, r12b; x607, copying x607 here, cause x607 is needed in a reg for other than x607, namely all: , x608--x609, size: 1
add r9, -0x1
mov r12, r15; x608, copying x593 here, cause x593 is needed in a reg for other than x608, namely all: , x608--x609, x620, size: 2
mov r9, 0x7bc65c783158aea3 ; moving imm to reg
sbb r12, r9
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbx, bl
adox rbx, r9; loading flag
adox rcx, [ rsp + 0x40 ]
setc bl; spill CF x609 to reg (rbx)
movzx r9, byte [ rsp + 0x610 ]; load byte memx579 to register64
clc;
mov [ rsp + 0x618 ], r12; spilling x608 to mem
mov r12, -0x1 ; moving imm to reg
adcx r9, r12; loading flag
adcx rax, [ rsp + 0x608 ]
mov r9, [ rsp + 0x60 ]; x554, copying x539 here, cause x539 is needed in a reg for other than x554, namely all: , x554--x555, size: 1
adox r9, r10
setc r10b; spill CF x581 to reg (r10)
clc;
movzx r13, r13b
adcx r13, r12; loading flag
adcx rcx, rax
movzx r13, r10b; x582, copying x581 here, cause x581 is needed in a reg for other than x582, namely all: , x582, size: 1
lea r13, [ r13 + rdx ]
adcx r13, r9
setc dl; spill CF x598 to reg (rdx)
seto al; spill OF x555 to reg (rax)
movzx r10, bl; x609, copying x609 here, cause x609 is needed in a reg for other than x609, namely all: , x610--x611, size: 1
add r10, -0x1
mov r10, rcx; x610, copying x595 here, cause x595 is needed in a reg for other than x610, namely all: , x621, x610--x611, size: 2
mov rbx, 0x6cfc5fd681c52056 ; moving imm to reg
sbb r10, rbx
movzx r9, dl; x599, copying x598 here, cause x598 is needed in a reg for other than x599, namely all: , x599, size: 1
movzx rax, al
lea r9, [ r9 + rax ]
mov rax, r13; x612, copying x597 here, cause x597 is needed in a reg for other than x612, namely all: , x612--x613, x622, size: 2
mov rdx, 0x2341f27177344 ; moving imm to reg
sbb rax, rdx
sbb r9, 0x00000000
cmovc r10, rcx; if CF, x621<- x595 (nzVar)
mov r9, [ rsp + 0x618 ]; x620, copying x608 here, cause x608 is needed in a reg for other than x620, namely all: , x620, size: 1
cmovc r9, r15; if CF, x620<- x593 (nzVar)
mov r15, [ rsp + 0x548 ]; x617, copying x602 here, cause x602 is needed in a reg for other than x617, namely all: , x617, size: 1
cmovc r15, r14; if CF, x617<- x587 (nzVar)
mov r14, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r14 + 0x8 ], r15; out1[1] = x617
mov rcx, [ rsp + 0x438 ]; x616, copying x600 here, cause x600 is needed in a reg for other than x616, namely all: , x616, size: 1
cmovc rcx, r8; if CF, x616<- x585 (nzVar)
mov r8, [ rsp + 0x600 ]; x619, copying x606 here, cause x606 is needed in a reg for other than x619, namely all: , x619, size: 1
cmovc r8, rbp; if CF, x619<- x591 (nzVar)
mov [ r14 + 0x28 ], r10; out1[5] = x621
mov [ r14 + 0x0 ], rcx; out1[0] = x616
mov [ r14 + 0x18 ], r8; out1[3] = x619
cmovc rax, r13; if CF, x622<- x597 (nzVar)
mov [ r14 + 0x20 ], r9; out1[4] = x620
mov rbp, [ rsp + 0x588 ]; x618, copying x604 here, cause x604 is needed in a reg for other than x618, namely all: , x618, size: 1
cmovc rbp, r11; if CF, x618<- x589 (nzVar)
mov [ r14 + 0x10 ], rbp; out1[2] = x618
mov [ r14 + 0x30 ], rax; out1[6] = x622
mov rbx, [ rsp + 0x620 ]; restoring from stack
mov rbp, [ rsp + 0x628 ]; restoring from stack
mov r12, [ rsp + 0x630 ]; restoring from stack
mov r13, [ rsp + 0x638 ]; restoring from stack
mov r14, [ rsp + 0x640 ]; restoring from stack
mov r15, [ rsp + 0x648 ]; restoring from stack
add rsp, 0x650 
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; clocked at 1600 MHz
; first cyclecount 267.7925, best 217.63829787234042, lastGood 224.59574468085106
; seed 3894390947325035 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 8583129 ms / 60000 runs=> 143.05215ms/run
; Time spent for assembling and measureing (initial batch_size=47, initial num_batches=101): 210108 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.02447918468894036
; number reverted permutation/ tried permutation: 23506 / 30185 =77.873%
; number reverted decision/ tried decision: 20218 / 29816 =67.809%