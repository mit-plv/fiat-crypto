SECTION .text
	GLOBAL square_p434
square_p434:
sub rsp, 0x440 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x410 ], rbx; saving to stack
mov [ rsp + 0x418 ], rbp; saving to stack
mov [ rsp + 0x420 ], r12; saving to stack
mov [ rsp + 0x428 ], r13; saving to stack
mov [ rsp + 0x430 ], r14; saving to stack
mov [ rsp + 0x438 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x7 to register64
mov rdx, rax; x7 to rdx
mulx rax, r10, [ rsi + 0x0 ]; x21, x20<- x7 * arg1[0]
mov r11, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r11; 0xffffffffffffffff, swapping with x7, which is currently in rdx
mulx rbx, rbp, r10; x48, x47<- x20 * 0xffffffffffffffff
xchg rdx, r11; x7, swapping with 0xffffffffffffffff, which is currently in rdx
mulx r12, r13, [ rsi + 0x8 ]; x19, x18<- x7 * arg1[1]
test al, al
adox rbp, r10
mov rbp, [ rsi + 0x8 ]; load m64 x1 to register64
xchg rdx, r11; 0xffffffffffffffff, swapping with x7, which is currently in rdx
mulx r14, r15, r10; x46, x45<- x20 * 0xffffffffffffffff
xchg rdx, rbp; x1, swapping with 0xffffffffffffffff, which is currently in rdx
mulx rcx, r8, [ rsi + 0x0 ]; x91, x90<- x1 * arg1[0]
adcx r13, rax
setc r9b; spill CF x23 to reg (r9)
clc;
adcx r15, rbx
adox r15, r13
setc al; spill CF x50 to reg (rax)
clc;
adcx r8, r15
xchg rdx, r8; x105, swapping with x1, which is currently in rdx
mulx rbx, r13, rbp; x134, x133<- x105 * 0xffffffffffffffff
setc r15b; spill CF x106 to reg (r15)
clc;
adcx r13, rdx
mov r13, rdx; preserving value of x105 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx rbp, rdi, r11; x17, x16<- x7 * arg1[2]
seto dl; spill OF x65 to reg (rdx)
mov [ rsp + 0x8 ], rbp; spilling x17 to mem
mov rbp, 0x0 ; moving imm to reg
dec rbp; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r9, r9b
adox r9, rbp; loading flag
adox r12, rdi
mov r9, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r9; 0xffffffffffffffff, swapping with x65, which is currently in rdx
mulx rdi, rbp, r10; x44, x43<- x20 * 0xffffffffffffffff
setc dl; spill CF x149 to reg (rdx)
clc;
mov [ rsp + 0x10 ], rdi; spilling x44 to mem
mov rdi, -0x1 ; moving imm to reg
movzx rax, al
adcx rax, rdi; loading flag
adcx r14, rbp
seto al; spill OF x25 to reg (rax)
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, rbp; loading flag
adox r12, r14
xchg rdx, r8; x1, swapping with x149, which is currently in rdx
mulx r9, r14, [ rsi + 0x8 ]; x89, x88<- x1 * arg1[1]
setc bpl; spill CF x52 to reg (rbp)
clc;
adcx r14, rcx
setc cl; spill CF x93 to reg (rcx)
clc;
mov rdi, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, rdi; loading flag
adcx r12, r14
mov r15, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r13; x105, swapping with x1, which is currently in rdx
mulx r14, rdi, r15; x132, x131<- x105 * 0xffffffffffffffff
setc r15b; spill CF x108 to reg (r15)
clc;
adcx rdi, rbx
setc bl; spill CF x136 to reg (rbx)
clc;
mov [ rsp + 0x18 ], r14; spilling x132 to mem
mov r14, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, r14; loading flag
adcx r12, rdi
mov r8, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, r10; x20, swapping with x105, which is currently in rdx
mulx rdi, r14, r8; x42, x41<- x20 * 0xfdc1767ae2ffffff
xchg rdx, r11; x7, swapping with x20, which is currently in rdx
mov [ rsp + 0x20 ], r12; spilling x150 to mem
mulx r8, r12, [ rsi + 0x18 ]; x15, x14<- x7 * arg1[3]
mov [ rsp + 0x28 ], rdi; spilling x42 to mem
seto dil; spill OF x67 to reg (rdi)
mov [ rsp + 0x30 ], r8; spilling x15 to mem
mov r8, -0x1 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r8, -0x1 ; moving imm to reg
movzx rax, al
adox rax, r8; loading flag
adox r12, [ rsp + 0x8 ]
seto al; spill OF x27 to reg (rax)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, r8; loading flag
adox r14, [ rsp + 0x10 ]
xchg rdx, r13; x1, swapping with x7, which is currently in rdx
mulx rbp, r8, [ rsi + 0x10 ]; x87, x86<- x1 * arg1[2]
mov [ rsp + 0x38 ], rbp; spilling x87 to mem
seto bpl; spill OF x54 to reg (rbp)
mov byte [ rsp + 0x40 ], al; spilling byte x27 to mem
mov rax, 0x0 ; moving imm to reg
dec rax; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rdi, dil
adox rdi, rax; loading flag
adox r12, r14
setc dil; spill CF x151 to reg (rdi)
clc;
movzx rcx, cl
adcx rcx, rax; loading flag
adcx r9, r8
setc cl; spill CF x95 to reg (rcx)
clc;
movzx r15, r15b
adcx r15, rax; loading flag
adcx r12, r9
mov r15, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r10; x105, swapping with x1, which is currently in rdx
mulx r14, r8, r15; x130, x129<- x105 * 0xffffffffffffffff
setc r9b; spill CF x110 to reg (r9)
clc;
movzx rbx, bl
adcx rbx, rax; loading flag
adcx r8, [ rsp + 0x18 ]
mov rbx, rdx; preserving value of x105 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx rax, r15, r13; x13, x12<- x7 * arg1[4]
setc dl; spill CF x138 to reg (rdx)
clc;
mov [ rsp + 0x48 ], rax; spilling x13 to mem
mov rax, -0x1 ; moving imm to reg
movzx rdi, dil
adcx rdi, rax; loading flag
adcx r12, r8
setc dil; spill CF x153 to reg (rdi)
movzx r8, byte [ rsp + 0x40 ]; load byte memx27 to register64
clc;
adcx r8, rax; loading flag
adcx r15, [ rsp + 0x30 ]
mov r8, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, r8; 0x7bc65c783158aea3, swapping with x138, which is currently in rdx
mov [ rsp + 0x50 ], r12; spilling x152 to mem
mulx rax, r12, r11; x40, x39<- x20 * 0x7bc65c783158aea3
seto dl; spill OF x69 to reg (rdx)
mov [ rsp + 0x58 ], rax; spilling x40 to mem
mov rax, 0x0 ; moving imm to reg
dec rax; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbp, bpl
adox rbp, rax; loading flag
adox r12, [ rsp + 0x28 ]
seto bpl; spill OF x56 to reg (rbp)
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rax, -0x1 ; moving imm to reg
movzx rdx, dl
adox rdx, rax; loading flag
adox r15, r12
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r12, rax, r10; x85, x84<- x1 * arg1[3]
setc dl; spill CF x29 to reg (rdx)
clc;
mov [ rsp + 0x60 ], r12; spilling x85 to mem
mov r12, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, r12; loading flag
adcx rax, [ rsp + 0x38 ]
seto cl; spill OF x71 to reg (rcx)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, r12; loading flag
adox r15, rax
mov r9, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, rbx; x105, swapping with x29, which is currently in rdx
mulx rax, r12, r9; x128, x127<- x105 * 0xfdc1767ae2ffffff
setc r9b; spill CF x97 to reg (r9)
clc;
mov [ rsp + 0x68 ], rax; spilling x128 to mem
mov rax, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, rax; loading flag
adcx r14, r12
mov r8, rdx; preserving value of x105 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx r12, rax, r13; x11, x10<- x7 * arg1[5]
seto dl; spill OF x112 to reg (rdx)
mov [ rsp + 0x70 ], r12; spilling x11 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rdi, dil
adox rdi, r12; loading flag
adox r15, r14
mov rdi, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, rdi; 0x6cfc5fd681c52056, swapping with x112, which is currently in rdx
mulx r14, r12, r11; x38, x37<- x20 * 0x6cfc5fd681c52056
setc dl; spill CF x140 to reg (rdx)
clc;
mov [ rsp + 0x78 ], r15; spilling x154 to mem
mov r15, -0x1 ; moving imm to reg
movzx rbx, bl
adcx rbx, r15; loading flag
adcx rax, [ rsp + 0x48 ]
xchg rdx, r10; x1, swapping with x140, which is currently in rdx
mulx rbx, r15, [ rsi + 0x20 ]; x83, x82<- x1 * arg1[4]
mov [ rsp + 0x80 ], rbx; spilling x83 to mem
setc bl; spill CF x31 to reg (rbx)
clc;
mov [ rsp + 0x88 ], r14; spilling x38 to mem
mov r14, -0x1 ; moving imm to reg
movzx rbp, bpl
adcx rbp, r14; loading flag
adcx r12, [ rsp + 0x58 ]
setc bpl; spill CF x58 to reg (rbp)
clc;
movzx rcx, cl
adcx rcx, r14; loading flag
adcx rax, r12
mov rcx, rdx; preserving value of x1 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mulx r13, r12, r13; x9, x8<- x7 * arg1[6]
setc dl; spill CF x73 to reg (rdx)
clc;
movzx r9, r9b
adcx r9, r14; loading flag
adcx r15, [ rsp + 0x60 ]
seto r9b; spill OF x155 to reg (r9)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
movzx rdi, dil
adox rdi, r14; loading flag
adox rax, r15
mov rdi, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, rdi; 0x7bc65c783158aea3, swapping with x73, which is currently in rdx
mulx r15, r14, r8; x126, x125<- x105 * 0x7bc65c783158aea3
setc dl; spill CF x99 to reg (rdx)
clc;
mov [ rsp + 0x90 ], r13; spilling x9 to mem
mov r13, -0x1 ; moving imm to reg
movzx r10, r10b
adcx r10, r13; loading flag
adcx r14, [ rsp + 0x68 ]
seto r10b; spill OF x114 to reg (r10)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, r13; loading flag
adox rax, r14
seto r9b; spill OF x157 to reg (r9)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, r14; loading flag
adox r12, [ rsp + 0x70 ]
mov rbx, 0x2341f27177344 ; moving imm to reg
xchg rdx, r11; x20, swapping with x99, which is currently in rdx
mulx rdx, r13, rbx; x36, x35<- x20 * 0x2341f27177344
seto r14b; spill OF x33 to reg (r14)
mov rbx, -0x1 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbx, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, rbx; loading flag
adox r13, [ rsp + 0x88 ]
seto bpl; spill OF x60 to reg (rbp)
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
movzx rdi, dil
adox rdi, rbx; loading flag
adox r12, r13
mov rdi, rdx; preserving value of x36 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx r13, rbx, rcx; x81, x80<- x1 * arg1[5]
setc dl; spill CF x142 to reg (rdx)
clc;
mov [ rsp + 0x98 ], rax; spilling x156 to mem
mov rax, -0x1 ; moving imm to reg
movzx r11, r11b
adcx r11, rax; loading flag
adcx rbx, [ rsp + 0x80 ]
setc r11b; spill CF x101 to reg (r11)
clc;
movzx r10, r10b
adcx r10, rax; loading flag
adcx r12, rbx
mov r10, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, r10; 0x6cfc5fd681c52056, swapping with x142, which is currently in rdx
mulx rbx, rax, r8; x124, x123<- x105 * 0x6cfc5fd681c52056
setc dl; spill CF x116 to reg (rdx)
clc;
mov [ rsp + 0xa0 ], r13; spilling x81 to mem
mov r13, -0x1 ; moving imm to reg
movzx r10, r10b
adcx r10, r13; loading flag
adcx r15, rax
movzx r10, r14b; x34, copying x33 here, cause x33 is needed in a reg for other than x34, namely all: , x34, size: 1
mov rax, [ rsp + 0x90 ]; load m64 x9 to register64
lea r10, [ r10 + rax ]; r8/64 + m8
setc al; spill CF x144 to reg (rax)
clc;
movzx r9, r9b
adcx r9, r13; loading flag
adcx r12, r15
movzx r9, bpl; x61, copying x60 here, cause x60 is needed in a reg for other than x61, namely all: , x61, size: 1
lea r9, [ r9 + rdi ]
mov r14, 0x2341f27177344 ; moving imm to reg
xchg rdx, r14; 0x2341f27177344, swapping with x116, which is currently in rdx
mulx r8, rdi, r8; x122, x121<- x105 * 0x2341f27177344
xchg rdx, rcx; x1, swapping with 0x2341f27177344, which is currently in rdx
mulx rdx, rbp, [ rsi + 0x30 ]; x79, x78<- x1 * arg1[6]
setc r15b; spill CF x159 to reg (r15)
clc;
movzx rax, al
adcx rax, r13; loading flag
adcx rbx, rdi
adox r9, r10
mov rax, [ rsi + 0x10 ]; load m64 x2 to register64
setc r10b; spill CF x146 to reg (r10)
clc;
movzx r11, r11b
adcx r11, r13; loading flag
adcx rbp, [ rsp + 0xa0 ]
setc r11b; spill CF x103 to reg (r11)
clc;
movzx r14, r14b
adcx r14, r13; loading flag
adcx r9, rbp
seto r14b; spill OF x77 to reg (r14)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdi, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, rdi; loading flag
adox r9, rbx
movzx r15, r11b; x104, copying x103 here, cause x103 is needed in a reg for other than x104, namely all: , x104, size: 1
lea r15, [ r15 + rdx ]
movzx rdx, r14b; x119, copying x77 here, cause x77 is needed in a reg for other than x119, namely all: , x119--x120, size: 1
adcx rdx, r15
movzx rbx, r10b; x147, copying x146 here, cause x146 is needed in a reg for other than x147, namely all: , x147, size: 1
lea rbx, [ rbx + r8 ]
adox rbx, rdx
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r8, r10, rax; x178, x177<- x2 * arg1[0]
setc dl; spill CF x120 to reg (rdx)
clc;
adcx r10, [ rsp + 0x20 ]
movzx r14, dl; x164, copying x120 here, cause x120 is needed in a reg for other than x164, namely all: , x164, size: 1
adox r14, r13
mov rbp, 0xffffffffffffffff ; moving imm to reg
mov rdx, r10; x192 to rdx
mulx r10, r11, rbp; x221, x220<- x192 * 0xffffffffffffffff
mov r15, rdx; preserving value of x192 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r13, rdi, rax; x176, x175<- x2 * arg1[1]
mov rdx, r15; x192 to rdx
mulx r15, rcx, rbp; x219, x218<- x192 * 0xffffffffffffffff
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, rdx
mov r11, [ rsi + 0x18 ]; load m64 x3 to register64
setc bpl; spill CF x193 to reg (rbp)
clc;
adcx rdi, r8
setc r8b; spill CF x180 to reg (r8)
clc;
adcx rcx, r10
setc r10b; spill CF x223 to reg (r10)
clc;
mov [ rsp + 0xa8 ], r14; spilling x164 to mem
mov r14, -0x1 ; moving imm to reg
movzx rbp, bpl
adcx rbp, r14; loading flag
adcx rdi, [ rsp + 0x50 ]
xchg rdx, r11; x3, swapping with x192, which is currently in rdx
mulx rbp, r14, [ rsi + 0x0 ]; x265, x264<- x3 * arg1[0]
adox rcx, rdi
setc dil; spill CF x195 to reg (rdi)
clc;
adcx r14, rcx
mov rcx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rcx; 0xffffffffffffffff, swapping with x3, which is currently in rdx
mov [ rsp + 0xb0 ], rbx; spilling x162 to mem
mov [ rsp + 0xb8 ], r9; spilling x160 to mem
mulx rbx, r9, r14; x308, x307<- x279 * 0xffffffffffffffff
mov [ rsp + 0xc0 ], r12; spilling x158 to mem
mov [ rsp + 0xc8 ], rbp; spilling x265 to mem
mulx r12, rbp, r14; x306, x305<- x279 * 0xffffffffffffffff
mov byte [ rsp + 0xd0 ], dil; spilling byte x195 to mem
mov [ rsp + 0xd8 ], r15; spilling x219 to mem
mulx rdi, r15, r14; x304, x303<- x279 * 0xffffffffffffffff
setc dl; spill CF x280 to reg (rdx)
clc;
adcx rbp, rbx
mov rbx, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, rbx; 0xfdc1767ae2ffffff, swapping with x280, which is currently in rdx
mov [ rsp + 0xe0 ], rbp; spilling x309 to mem
mov byte [ rsp + 0xe8 ], bl; spilling byte x280 to mem
mulx rbp, rbx, r14; x302, x301<- x279 * 0xfdc1767ae2ffffff
adcx r15, r12
mov r12, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, r14; x279, swapping with 0xfdc1767ae2ffffff, which is currently in rdx
mov [ rsp + 0xf0 ], r15; spilling x311 to mem
mulx r14, r15, r12; x300, x299<- x279 * 0x7bc65c783158aea3
adcx rbx, rdi
adcx r15, rbp
mov rdi, 0x2341f27177344 ; moving imm to reg
mulx rbp, r12, rdi; x296, x295<- x279 * 0x2341f27177344
mov rdi, 0x6cfc5fd681c52056 ; moving imm to reg
mov [ rsp + 0xf8 ], r15; spilling x315 to mem
mov [ rsp + 0x100 ], rbx; spilling x313 to mem
mulx r15, rbx, rdi; x298, x297<- x279 * 0x6cfc5fd681c52056
adcx rbx, r14
adcx r12, r15
mov r14, 0x0 ; moving imm to reg
adcx rbp, r14
clc;
adcx r9, rdx
mov rdx, rax; x2 to rdx
mulx rax, r9, [ rsi + 0x10 ]; x174, x173<- x2 * arg1[2]
seto r15b; spill OF x238 to reg (r15)
dec r14; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r8, r8b
adox r8, r14; loading flag
adox r13, r9
mov r8, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r11; x192, swapping with x2, which is currently in rdx
mulx r9, r14, r8; x217, x216<- x192 * 0xffffffffffffffff
setc r8b; spill CF x323 to reg (r8)
clc;
mov rdi, -0x1 ; moving imm to reg
movzx r10, r10b
adcx r10, rdi; loading flag
adcx r14, [ rsp + 0xd8 ]
mov r10, rdx; preserving value of x192 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x108 ], rbp; spilling x321 to mem
mulx rdi, rbp, rcx; x263, x262<- x3 * arg1[1]
setc dl; spill CF x225 to reg (rdx)
mov [ rsp + 0x110 ], r12; spilling x319 to mem
movzx r12, byte [ rsp + 0xd0 ]; load byte memx195 to register64
clc;
mov [ rsp + 0x118 ], rbx; spilling x317 to mem
mov rbx, -0x1 ; moving imm to reg
adcx r12, rbx; loading flag
adcx r13, [ rsp + 0x78 ]
seto r12b; spill OF x182 to reg (r12)
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, rbx; loading flag
adox r13, r14
seto r15b; spill OF x240 to reg (r15)
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rbp, [ rsp + 0xc8 ]
setc r14b; spill CF x197 to reg (r14)
movzx rbx, byte [ rsp + 0xe8 ]; load byte memx280 to register64
clc;
mov [ rsp + 0x120 ], rdi; spilling x263 to mem
mov rdi, -0x1 ; moving imm to reg
adcx rbx, rdi; loading flag
adcx r13, rbp
setc bl; spill CF x282 to reg (rbx)
clc;
movzx r8, r8b
adcx r8, rdi; loading flag
adcx r13, [ rsp + 0xe0 ]
mov r8, [ rsi + 0x20 ]; load m64 x4 to register64
mov bpl, dl; preserving value of x225 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov byte [ rsp + 0x128 ], bl; spilling byte x282 to mem
mulx rdi, rbx, r8; x352, x351<- x4 * arg1[0]
setc dl; spill CF x325 to reg (rdx)
clc;
adcx rbx, r13
xchg rdx, r11; x2, swapping with x325, which is currently in rdx
mov [ rsp + 0x130 ], rdi; spilling x352 to mem
mulx r13, rdi, [ rsi + 0x18 ]; x172, x171<- x2 * arg1[3]
mov [ rsp + 0x138 ], r13; spilling x172 to mem
mov r13, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbx; x366, swapping with x2, which is currently in rdx
mov byte [ rsp + 0x140 ], r11b; spilling byte x325 to mem
mov byte [ rsp + 0x148 ], r15b; spilling byte x240 to mem
mulx r11, r15, r13; x395, x394<- x366 * 0xffffffffffffffff
seto r13b; spill OF x267 to reg (r13)
mov [ rsp + 0x150 ], r11; spilling x395 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, r11; loading flag
adox rax, rdi
mov r12, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, r10; x192, swapping with x366, which is currently in rdx
mulx rdi, r11, r12; x215, x214<- x192 * 0xfdc1767ae2ffffff
setc r12b; spill CF x367 to reg (r12)
clc;
mov [ rsp + 0x158 ], rdi; spilling x215 to mem
mov rdi, -0x1 ; moving imm to reg
movzx rbp, bpl
adcx rbp, rdi; loading flag
adcx r9, r11
setc bpl; spill CF x227 to reg (rbp)
clc;
adcx r15, r10
setc r15b; spill CF x410 to reg (r15)
clc;
movzx r14, r14b
adcx r14, rdi; loading flag
adcx rax, [ rsp + 0x98 ]
setc r14b; spill CF x199 to reg (r14)
movzx r11, byte [ rsp + 0x148 ]; load byte memx240 to register64
clc;
adcx r11, rdi; loading flag
adcx rax, r9
mov r11, rdx; preserving value of x192 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r9, rdi, rcx; x261, x260<- x3 * arg1[2]
seto dl; spill OF x184 to reg (rdx)
mov [ rsp + 0x160 ], r9; spilling x261 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r13, r13b
adox r13, r9; loading flag
adox rdi, [ rsp + 0x120 ]
setc r13b; spill CF x242 to reg (r13)
movzx r9, byte [ rsp + 0x128 ]; load byte memx282 to register64
clc;
mov byte [ rsp + 0x168 ], bpl; spilling byte x227 to mem
mov rbp, -0x1 ; moving imm to reg
adcx r9, rbp; loading flag
adcx rax, rdi
setc r9b; spill CF x284 to reg (r9)
movzx rdi, byte [ rsp + 0x140 ]; load byte memx325 to register64
clc;
adcx rdi, rbp; loading flag
adcx rax, [ rsp + 0xf0 ]
mov dil, dl; preserving value of x184 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov byte [ rsp + 0x170 ], r9b; spilling byte x284 to mem
mulx rbp, r9, r8; x350, x349<- x4 * arg1[1]
setc dl; spill CF x327 to reg (rdx)
clc;
adcx r9, [ rsp + 0x130 ]
mov byte [ rsp + 0x178 ], dl; spilling byte x327 to mem
seto dl; spill OF x269 to reg (rdx)
mov [ rsp + 0x180 ], rbp; spilling x350 to mem
mov rbp, 0x0 ; moving imm to reg
dec rbp; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r12, r12b
adox r12, rbp; loading flag
adox rax, r9
mov r12, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r12; 0xffffffffffffffff, swapping with x269, which is currently in rdx
mulx r9, rbp, r10; x393, x392<- x366 * 0xffffffffffffffff
setc dl; spill CF x354 to reg (rdx)
clc;
adcx rbp, [ rsp + 0x150 ]
mov [ rsp + 0x188 ], r9; spilling x393 to mem
setc r9b; spill CF x397 to reg (r9)
clc;
mov byte [ rsp + 0x190 ], dl; spilling byte x354 to mem
mov rdx, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, rdx; loading flag
adcx rax, rbp
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r15, rbp, rbx; x170, x169<- x2 * arg1[4]
setc dl; spill CF x412 to reg (rdx)
clc;
mov [ rsp + 0x198 ], rax; spilling x411 to mem
mov rax, -0x1 ; moving imm to reg
movzx rdi, dil
adcx rdi, rax; loading flag
adcx rbp, [ rsp + 0x138 ]
setc dil; spill CF x186 to reg (rdi)
clc;
movzx r14, r14b
adcx r14, rax; loading flag
adcx rbp, [ rsp + 0xc0 ]
mov r14, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, r14; 0x7bc65c783158aea3, swapping with x412, which is currently in rdx
mov [ rsp + 0x1a0 ], r15; spilling x170 to mem
mulx rax, r15, r11; x213, x212<- x192 * 0x7bc65c783158aea3
seto dl; spill OF x369 to reg (rdx)
mov [ rsp + 0x1a8 ], rax; spilling x213 to mem
movzx rax, byte [ rsp + 0x168 ]; load byte memx227 to register64
mov byte [ rsp + 0x1b0 ], dil; spilling byte x186 to mem
mov rdi, 0x0 ; moving imm to reg
dec rdi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rax, rdi; loading flag
adox r15, [ rsp + 0x158 ]
setc al; spill CF x201 to reg (rax)
clc;
movzx r13, r13b
adcx r13, rdi; loading flag
adcx rbp, r15
xchg rdx, rcx; x3, swapping with x369, which is currently in rdx
mulx r13, r15, [ rsi + 0x18 ]; x259, x258<- x3 * arg1[3]
seto dil; spill OF x229 to reg (rdi)
mov [ rsp + 0x1b8 ], r13; spilling x259 to mem
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r12, r12b
adox r12, r13; loading flag
adox r15, [ rsp + 0x160 ]
setc r12b; spill CF x244 to reg (r12)
movzx r13, byte [ rsp + 0x170 ]; load byte memx284 to register64
clc;
mov byte [ rsp + 0x1c0 ], dil; spilling byte x229 to mem
mov rdi, -0x1 ; moving imm to reg
adcx r13, rdi; loading flag
adcx rbp, r15
mov r13, rdx; preserving value of x3 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r15, rdi, r8; x348, x347<- x4 * arg1[2]
seto dl; spill OF x271 to reg (rdx)
mov [ rsp + 0x1c8 ], r15; spilling x348 to mem
movzx r15, byte [ rsp + 0x190 ]; load byte memx354 to register64
mov byte [ rsp + 0x1d0 ], r12b; spilling byte x244 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
adox r15, r12; loading flag
adox rdi, [ rsp + 0x180 ]
seto r15b; spill OF x356 to reg (r15)
movzx r12, byte [ rsp + 0x178 ]; load byte memx327 to register64
mov byte [ rsp + 0x1d8 ], dl; spilling byte x271 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r12, rdx; loading flag
adox rbp, [ rsp + 0x100 ]
seto r12b; spill OF x329 to reg (r12)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, rdx; loading flag
adox rbp, rdi
mov rcx, 0xffffffffffffffff ; moving imm to reg
mov rdx, r10; x366 to rdx
mulx r10, rdi, rcx; x391, x390<- x366 * 0xffffffffffffffff
seto cl; spill OF x371 to reg (rcx)
mov [ rsp + 0x1e0 ], r10; spilling x391 to mem
mov r10, -0x1 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r10, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, r10; loading flag
adox rdi, [ rsp + 0x188 ]
setc r9b; spill CF x286 to reg (r9)
clc;
movzx r14, r14b
adcx r14, r10; loading flag
adcx rbp, rdi
xchg rdx, rbx; x2, swapping with x366, which is currently in rdx
mulx r14, rdi, [ rsi + 0x28 ]; x168, x167<- x2 * arg1[5]
seto r10b; spill OF x399 to reg (r10)
mov [ rsp + 0x1e8 ], rbp; spilling x413 to mem
movzx rbp, byte [ rsp + 0x1b0 ]; load byte memx186 to register64
mov [ rsp + 0x1f0 ], r14; spilling x168 to mem
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbp, r14; loading flag
adox rdi, [ rsp + 0x1a0 ]
mov rbp, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, r11; x192, swapping with x2, which is currently in rdx
mov byte [ rsp + 0x1f8 ], r10b; spilling byte x399 to mem
mulx r14, r10, rbp; x211, x210<- x192 * 0x6cfc5fd681c52056
seto bpl; spill OF x188 to reg (rbp)
mov [ rsp + 0x200 ], r14; spilling x211 to mem
mov r14, -0x1 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r14, -0x1 ; moving imm to reg
movzx rax, al
adox rax, r14; loading flag
adox rdi, [ rsp + 0xb8 ]
setc al; spill CF x414 to reg (rax)
movzx r14, byte [ rsp + 0x1c0 ]; load byte memx229 to register64
clc;
mov byte [ rsp + 0x208 ], bpl; spilling byte x188 to mem
mov rbp, -0x1 ; moving imm to reg
adcx r14, rbp; loading flag
adcx r10, [ rsp + 0x1a8 ]
setc r14b; spill CF x231 to reg (r14)
movzx rbp, byte [ rsp + 0x1d0 ]; load byte memx244 to register64
clc;
mov byte [ rsp + 0x210 ], al; spilling byte x414 to mem
mov rax, -0x1 ; moving imm to reg
adcx rbp, rax; loading flag
adcx rdi, r10
mov rbp, rdx; preserving value of x192 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r10, rax, r13; x257, x256<- x3 * arg1[4]
seto dl; spill OF x203 to reg (rdx)
mov [ rsp + 0x218 ], r10; spilling x257 to mem
movzx r10, byte [ rsp + 0x1d8 ]; load byte memx271 to register64
mov byte [ rsp + 0x220 ], r14b; spilling byte x231 to mem
mov r14, -0x1 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r14, -0x1 ; moving imm to reg
adox r10, r14; loading flag
adox rax, [ rsp + 0x1b8 ]
seto r10b; spill OF x273 to reg (r10)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, r14; loading flag
adox rdi, rax
xchg rdx, r8; x4, swapping with x203, which is currently in rdx
mulx r9, rax, [ rsi + 0x18 ]; x346, x345<- x4 * arg1[3]
seto r14b; spill OF x288 to reg (r14)
mov [ rsp + 0x228 ], r9; spilling x346 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r15, r15b
adox r15, r9; loading flag
adox rax, [ rsp + 0x1c8 ]
seto r15b; spill OF x358 to reg (r15)
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, r9; loading flag
adox rdi, [ rsp + 0xf8 ]
setc r12b; spill CF x246 to reg (r12)
clc;
movzx rcx, cl
adcx rcx, r9; loading flag
adcx rdi, rax
mov rcx, 0x2341f27177344 ; moving imm to reg
xchg rdx, rcx; 0x2341f27177344, swapping with x4, which is currently in rdx
mulx rbp, rax, rbp; x209, x208<- x192 * 0x2341f27177344
mov r9, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, rbx; x366, swapping with 0x2341f27177344, which is currently in rdx
mov [ rsp + 0x230 ], rbp; spilling x209 to mem
mulx rbx, rbp, r9; x389, x388<- x366 * 0xfdc1767ae2ffffff
mov r9, rdx; preserving value of x366 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0x238 ], rbx; spilling x389 to mem
mulx r11, rbx, r11; x166, x165<- x2 * arg1[6]
seto dl; spill OF x331 to reg (rdx)
mov [ rsp + 0x240 ], r11; spilling x166 to mem
movzx r11, byte [ rsp + 0x1f8 ]; load byte memx399 to register64
mov byte [ rsp + 0x248 ], r15b; spilling byte x358 to mem
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r11, r15; loading flag
adox rbp, [ rsp + 0x1e0 ]
seto r11b; spill OF x401 to reg (r11)
movzx r15, byte [ rsp + 0x210 ]; load byte memx414 to register64
mov byte [ rsp + 0x250 ], dl; spilling byte x331 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, rdx; loading flag
adox rdi, rbp
setc r15b; spill CF x373 to reg (r15)
movzx rbp, byte [ rsp + 0x208 ]; load byte memx188 to register64
clc;
adcx rbp, rdx; loading flag
adcx rbx, [ rsp + 0x1f0 ]
setc bpl; spill CF x190 to reg (rbp)
movzx rdx, byte [ rsp + 0x220 ]; load byte memx231 to register64
clc;
mov [ rsp + 0x258 ], rdi; spilling x415 to mem
mov rdi, -0x1 ; moving imm to reg
adcx rdx, rdi; loading flag
adcx rax, [ rsp + 0x200 ]
setc dl; spill CF x233 to reg (rdx)
clc;
movzx r8, r8b
adcx r8, rdi; loading flag
adcx rbx, [ rsp + 0xb0 ]
setc r8b; spill CF x205 to reg (r8)
clc;
movzx r12, r12b
adcx r12, rdi; loading flag
adcx rbx, rax
mov r12b, dl; preserving value of x233 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx rax, rdi, r13; x255, x254<- x3 * arg1[5]
setc dl; spill CF x248 to reg (rdx)
clc;
mov [ rsp + 0x260 ], rax; spilling x255 to mem
mov rax, -0x1 ; moving imm to reg
movzx r10, r10b
adcx r10, rax; loading flag
adcx rdi, [ rsp + 0x218 ]
mov r10b, dl; preserving value of x248 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov byte [ rsp + 0x268 ], r12b; spilling byte x233 to mem
mulx rax, r12, rcx; x344, x343<- x4 * arg1[4]
setc dl; spill CF x275 to reg (rdx)
clc;
mov byte [ rsp + 0x270 ], r10b; spilling byte x248 to mem
mov r10, -0x1 ; moving imm to reg
movzx r14, r14b
adcx r14, r10; loading flag
adcx rbx, rdi
seto r14b; spill OF x416 to reg (r14)
movzx rdi, byte [ rsp + 0x250 ]; load byte memx331 to register64
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r10, -0x1 ; moving imm to reg
adox rdi, r10; loading flag
adox rbx, [ rsp + 0x118 ]
mov rdi, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, rdi; 0x7bc65c783158aea3, swapping with x275, which is currently in rdx
mov byte [ rsp + 0x278 ], dil; spilling byte x275 to mem
mulx r10, rdi, r9; x387, x386<- x366 * 0x7bc65c783158aea3
setc dl; spill CF x290 to reg (rdx)
mov [ rsp + 0x280 ], r10; spilling x387 to mem
movzx r10, byte [ rsp + 0x248 ]; load byte memx358 to register64
clc;
mov [ rsp + 0x288 ], rax; spilling x344 to mem
mov rax, -0x1 ; moving imm to reg
adcx r10, rax; loading flag
adcx r12, [ rsp + 0x228 ]
movzx r10, bpl; x191, copying x190 here, cause x190 is needed in a reg for other than x191, namely all: , x191, size: 1
mov rax, [ rsp + 0x240 ]; load m64 x166 to register64
lea r10, [ r10 + rax ]; r8/64 + m8
setc al; spill CF x360 to reg (rax)
clc;
mov rbp, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, rbp; loading flag
adcx r10, [ rsp + 0xa8 ]
setc r8b; spill CF x207 to reg (r8)
clc;
movzx r11, r11b
adcx r11, rbp; loading flag
adcx rdi, [ rsp + 0x238 ]
xchg rdx, r13; x3, swapping with x290, which is currently in rdx
mulx rdx, r11, [ rsi + 0x30 ]; x253, x252<- x3 * arg1[6]
seto bpl; spill OF x333 to reg (rbp)
mov [ rsp + 0x290 ], rdx; spilling x253 to mem
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, rdx; loading flag
adox rbx, r12
setc r15b; spill CF x403 to reg (r15)
clc;
movzx r14, r14b
adcx r14, rdx; loading flag
adcx rbx, rdi
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mulx r14, r12, rcx; x342, x341<- x4 * arg1[5]
setc dl; spill CF x418 to reg (rdx)
clc;
mov rdi, -0x1 ; moving imm to reg
movzx rax, al
adcx rax, rdi; loading flag
adcx r12, [ rsp + 0x288 ]
movzx rax, byte [ rsp + 0x268 ]; x234, copying x233 here, cause x233 is needed in a reg for other than x234, namely all: , x234, size: 1
mov rdi, [ rsp + 0x230 ]; load m64 x209 to register64
lea rax, [ rax + rdi ]; r8/64 + m8
seto dil; spill OF x375 to reg (rdi)
mov [ rsp + 0x298 ], rbx; spilling x417 to mem
movzx rbx, byte [ rsp + 0x270 ]; load byte memx248 to register64
mov [ rsp + 0x2a0 ], r14; spilling x342 to mem
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbx, r14; loading flag
adox r10, rax
seto bl; spill OF x250 to reg (rbx)
movzx rax, byte [ rsp + 0x278 ]; load byte memx275 to register64
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
adox rax, r14; loading flag
adox r11, [ rsp + 0x260 ]
seto al; spill OF x277 to reg (rax)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, r14; loading flag
adox r10, r11
seto r13b; spill OF x292 to reg (r13)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r11, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, r11; loading flag
adox r10, [ rsp + 0x110 ]
setc bpl; spill CF x362 to reg (rbp)
clc;
movzx rdi, dil
adcx rdi, r11; loading flag
adcx r10, r12
mov rdi, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, rdi; 0x6cfc5fd681c52056, swapping with x418, which is currently in rdx
mulx r12, r14, r9; x385, x384<- x366 * 0x6cfc5fd681c52056
seto r11b; spill OF x335 to reg (r11)
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, rdx; loading flag
adox r14, [ rsp + 0x280 ]
movzx r15, bl; x251, copying x250 here, cause x250 is needed in a reg for other than x251, namely all: , x251, size: 1
movzx r8, r8b
lea r15, [ r15 + r8 ]
movzx r8, al; x278, copying x277 here, cause x277 is needed in a reg for other than x278, namely all: , x278, size: 1
mov rbx, [ rsp + 0x290 ]; load m64 x253 to register64
lea r8, [ r8 + rbx ]; r8/64 + m8
setc bl; spill CF x377 to reg (rbx)
clc;
movzx rdi, dil
adcx rdi, rdx; loading flag
adcx r10, r14
seto dil; spill OF x405 to reg (rdi)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rax, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, rax; loading flag
adox r15, r8
seto r13b; spill OF x294 to reg (r13)
inc rax; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, rdx; loading flag
adox r15, [ rsp + 0x108 ]
movzx r11, r13b; x338, copying x294 here, cause x294 is needed in a reg for other than x338, namely all: , x338, size: 1
adox r11, rax
mov rdx, rcx; x4 to rdx
mulx rdx, rcx, [ rsi + 0x30 ]; x340, x339<- x4 * arg1[6]
mov r14, 0x2341f27177344 ; moving imm to reg
xchg rdx, r14; 0x2341f27177344, swapping with x340, which is currently in rdx
mulx r9, r8, r9; x383, x382<- x366 * 0x2341f27177344
dec rax; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx rbp, bpl
adox rbp, rax; loading flag
adox rcx, [ rsp + 0x2a0 ]
seto bpl; spill OF x364 to reg (rbp)
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
movzx rdi, dil
adox rdi, r13; loading flag
adox r12, r8
mov rdi, [ rsi + 0x28 ]; load m64 x5 to register64
movzx r8, bpl; x365, copying x364 here, cause x364 is needed in a reg for other than x365, namely all: , x365, size: 1
lea r8, [ r8 + r14 ]
setc r14b; spill CF x420 to reg (r14)
clc;
movzx rbx, bl
adcx rbx, r13; loading flag
adcx r15, rcx
adcx r8, r11
seto bl; spill OF x407 to reg (rbx)
dec rax; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx r14, r14b
adox r14, rax; loading flag
adox r15, r12
movzx r13, bl; x408, copying x407 here, cause x407 is needed in a reg for other than x408, namely all: , x408, size: 1
lea r13, [ r13 + r9 ]
adox r13, r8
seto r14b; spill OF x425 to reg (r14)
adc r14b, 0x0
movzx r14, r14b
xchg rdx, rdi; x5, swapping with 0x2341f27177344, which is currently in rdx
mulx r11, r9, [ rsi + 0x0 ]; x439, x438<- x5 * arg1[0]
adox r9, [ rsp + 0x198 ]
mov rcx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r9; x453, swapping with x5, which is currently in rdx
mulx rbp, r12, rcx; x478, x477<- x453 * 0xffffffffffffffff
mulx rbx, r8, rcx; x482, x481<- x453 * 0xffffffffffffffff
mulx rax, rdi, rcx; x480, x479<- x453 * 0xffffffffffffffff
mov rcx, 0xfdc1767ae2ffffff ; moving imm to reg
mov byte [ rsp + 0x2a8 ], r14b; spilling byte x425 to mem
mov [ rsp + 0x2b0 ], r13; spilling x423 to mem
mulx r14, r13, rcx; x476, x475<- x453 * 0xfdc1767ae2ffffff
adcx rdi, rbx
adcx r12, rax
mov rbx, 0x2341f27177344 ; moving imm to reg
mulx rax, rcx, rbx; x470, x469<- x453 * 0x2341f27177344
adcx r13, rbp
mov rbp, 0x7bc65c783158aea3 ; moving imm to reg
mov [ rsp + 0x2b8 ], r15; spilling x421 to mem
mulx rbx, r15, rbp; x474, x473<- x453 * 0x7bc65c783158aea3
mov rbp, 0x6cfc5fd681c52056 ; moving imm to reg
mov [ rsp + 0x2c0 ], r10; spilling x419 to mem
mov [ rsp + 0x2c8 ], r13; spilling x487 to mem
mulx r10, r13, rbp; x472, x471<- x453 * 0x6cfc5fd681c52056
adcx r15, r14
adcx r13, rbx
mov r14, [ rsi + 0x30 ]; load m64 x6 to register64
seto bl; spill OF x454 to reg (rbx)
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, rdx
adcx rcx, r10
mov rdx, r9; x5 to rdx
mulx r8, r9, [ rsi + 0x8 ]; x437, x436<- x5 * arg1[1]
xchg rdx, r14; x6, swapping with x5, which is currently in rdx
mulx r10, rbp, [ rsi + 0x0 ]; x526, x525<- x6 * arg1[0]
mov [ rsp + 0x2d0 ], rcx; spilling x493 to mem
mov rcx, 0x0 ; moving imm to reg
adcx rax, rcx
clc;
adcx r9, r11
setc r11b; spill CF x441 to reg (r11)
clc;
mov rcx, -0x1 ; moving imm to reg
movzx rbx, bl
adcx rbx, rcx; loading flag
adcx r9, [ rsp + 0x1e8 ]
adox rdi, r9
mov rbx, rdx; preserving value of x6 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r9, rcx, r14; x435, x434<- x5 * arg1[2]
setc dl; spill CF x456 to reg (rdx)
clc;
mov [ rsp + 0x2d8 ], rax; spilling x495 to mem
mov rax, -0x1 ; moving imm to reg
movzx r11, r11b
adcx r11, rax; loading flag
adcx r8, rcx
setc r11b; spill CF x443 to reg (r11)
clc;
movzx rdx, dl
adcx rdx, rax; loading flag
adcx r8, [ rsp + 0x258 ]
setc dl; spill CF x458 to reg (rdx)
clc;
adcx rbp, rdi
adox r12, r8
mov rdi, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rdi; 0xffffffffffffffff, swapping with x458, which is currently in rdx
mulx rcx, r8, rbp; x569, x568<- x540 * 0xffffffffffffffff
mov [ rsp + 0x2e0 ], r13; spilling x491 to mem
mulx rax, r13, rbp; x567, x566<- x540 * 0xffffffffffffffff
mov [ rsp + 0x2e8 ], r15; spilling x489 to mem
mov r15, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x2f0 ], rax; spilling x567 to mem
mov byte [ rsp + 0x2f8 ], dil; spilling byte x458 to mem
mulx rax, rdi, rbx; x524, x523<- x6 * arg1[1]
setc dl; spill CF x541 to reg (rdx)
clc;
adcx rdi, r10
setc r10b; spill CF x528 to reg (r10)
clc;
adcx r8, rbp
mov r8b, dl; preserving value of x541 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x300 ], rax; spilling x524 to mem
mulx r15, rax, r14; x433, x432<- x5 * arg1[3]
setc dl; spill CF x584 to reg (rdx)
clc;
adcx r13, rcx
seto cl; spill OF x501 to reg (rcx)
mov [ rsp + 0x308 ], r15; spilling x433 to mem
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r11, r11b
adox r11, r15; loading flag
adox r9, rax
setc r11b; spill CF x571 to reg (r11)
clc;
movzx r8, r8b
adcx r8, r15; loading flag
adcx r12, rdi
setc r8b; spill CF x543 to reg (r8)
clc;
movzx rdx, dl
adcx rdx, r15; loading flag
adcx r12, r13
seto dil; spill OF x445 to reg (rdi)
movzx rdx, byte [ rsp + 0x2f8 ]; load byte memx458 to register64
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rax, -0x1 ; moving imm to reg
adox rdx, rax; loading flag
adox r9, [ rsp + 0x298 ]
setc dl; spill CF x586 to reg (rdx)
clc;
movzx rcx, cl
adcx rcx, rax; loading flag
adcx r9, [ rsp + 0x2c8 ]
xchg rdx, rbx; x6, swapping with x586, which is currently in rdx
mulx rcx, r13, [ rsi + 0x10 ]; x522, x521<- x6 * arg1[2]
setc al; spill CF x503 to reg (rax)
mov [ rsp + 0x310 ], rcx; spilling x522 to mem
seto cl; spill OF x460 to reg (rcx)
mov byte [ rsp + 0x318 ], dil; spilling byte x445 to mem
mov rdi, r12; x600, copying x585 here, cause x585 is needed in a reg for other than x600, namely all: , x600--x601, x616, size: 2
mov byte [ rsp + 0x320 ], bl; spilling byte x586 to mem
mov rbx, 0xffffffffffffffff ; moving imm to reg
sub rdi, rbx
dec r15; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r10, r10b
adox r10, r15; loading flag
adox r13, [ rsp + 0x300 ]
setc r10b; spill CF x601 to reg (r10)
clc;
movzx r8, r8b
adcx r8, r15; loading flag
adcx r9, r13
xchg rdx, rbp; x540, swapping with x6, which is currently in rdx
mulx r8, r13, rbx; x565, x564<- x540 * 0xffffffffffffffff
seto r15b; spill OF x530 to reg (r15)
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r11, r11b
adox r11, rbx; loading flag
adox r13, [ rsp + 0x2f0 ]
setc r11b; spill CF x545 to reg (r11)
movzx rbx, byte [ rsp + 0x320 ]; load byte memx586 to register64
clc;
mov [ rsp + 0x328 ], rdi; spilling x600 to mem
mov rdi, -0x1 ; moving imm to reg
adcx rbx, rdi; loading flag
adcx r9, r13
setc bl; spill CF x588 to reg (rbx)
seto r13b; spill OF x573 to reg (r13)
movzx rdi, r10b; x601, copying x601 here, cause x601 is needed in a reg for other than x601, namely all: , x602--x603, size: 1
add rdi, -0x1
mov r10, r9; x602, copying x587 here, cause x587 is needed in a reg for other than x602, namely all: , x602--x603, x617, size: 2
mov byte [ rsp + 0x330 ], r11b; spilling byte x545 to mem
mov r11, 0xffffffffffffffff ; moving imm to reg
sbb r10, r11
mov r11, rdx; preserving value of x540 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x338 ], r10; spilling x602 to mem
mov byte [ rsp + 0x340 ], bl; spilling byte x588 to mem
mulx r10, rbx, r14; x431, x430<- x5 * arg1[4]
movzx rdx, byte [ rsp + 0x318 ]; load byte memx445 to register64
mov [ rsp + 0x348 ], r10; spilling x431 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rdx, r10; loading flag
adox rbx, [ rsp + 0x308 ]
setc dl; spill CF x603 to reg (rdx)
clc;
movzx rcx, cl
adcx rcx, r10; loading flag
adcx rbx, [ rsp + 0x2c0 ]
xchg rdx, rbp; x6, swapping with x603, which is currently in rdx
mulx rcx, r10, [ rsi + 0x18 ]; x520, x519<- x6 * arg1[3]
mov [ rsp + 0x350 ], rcx; spilling x520 to mem
seto cl; spill OF x447 to reg (rcx)
mov byte [ rsp + 0x358 ], bpl; spilling byte x603 to mem
mov rbp, -0x1 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
movzx rax, al
adox rax, rbp; loading flag
adox rbx, [ rsp + 0x2e8 ]
setc al; spill CF x462 to reg (rax)
clc;
movzx r15, r15b
adcx r15, rbp; loading flag
adcx r10, [ rsp + 0x310 ]
mov r15, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, r15; 0xfdc1767ae2ffffff, swapping with x6, which is currently in rdx
mov byte [ rsp + 0x360 ], al; spilling byte x462 to mem
mulx rbp, rax, r11; x563, x562<- x540 * 0xfdc1767ae2ffffff
setc dl; spill CF x532 to reg (rdx)
clc;
mov [ rsp + 0x368 ], rbp; spilling x563 to mem
mov rbp, -0x1 ; moving imm to reg
movzx r13, r13b
adcx r13, rbp; loading flag
adcx r8, rax
seto r13b; spill OF x505 to reg (r13)
movzx rax, byte [ rsp + 0x330 ]; load byte memx545 to register64
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
adox rax, rbp; loading flag
adox rbx, r10
xchg rdx, r14; x5, swapping with x532, which is currently in rdx
mulx rax, r10, [ rsi + 0x28 ]; x429, x428<- x5 * arg1[5]
seto bpl; spill OF x547 to reg (rbp)
mov [ rsp + 0x370 ], rax; spilling x429 to mem
movzx rax, byte [ rsp + 0x340 ]; load byte memx588 to register64
mov byte [ rsp + 0x378 ], r13b; spilling byte x505 to mem
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rax, r13; loading flag
adox rbx, r8
seto al; spill OF x590 to reg (rax)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r8; loading flag
adox r10, [ rsp + 0x348 ]
setc cl; spill CF x575 to reg (rcx)
seto r13b; spill OF x449 to reg (r13)
movzx r8, byte [ rsp + 0x358 ]; x603, copying x603 here, cause x603 is needed in a reg for other than x603, namely all: , x604--x605, size: 1
add r8, -0x1
mov r8, rbx; x604, copying x589 here, cause x589 is needed in a reg for other than x604, namely all: , x618, x604--x605, size: 2
mov byte [ rsp + 0x380 ], al; spilling byte x590 to mem
mov rax, 0xffffffffffffffff ; moving imm to reg
sbb r8, rax
movzx rax, byte [ rsp + 0x360 ]; load byte memx462 to register64
mov [ rsp + 0x388 ], r8; spilling x604 to mem
mov r8, 0x0 ; moving imm to reg
dec r8; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rax, r8; loading flag
adox r10, [ rsp + 0x2b8 ]
mov rax, rdx; preserving value of x5 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov byte [ rsp + 0x390 ], r13b; spilling byte x449 to mem
mulx r8, r13, r15; x518, x517<- x6 * arg1[4]
setc dl; spill CF x605 to reg (rdx)
clc;
mov [ rsp + 0x398 ], r8; spilling x518 to mem
mov r8, -0x1 ; moving imm to reg
movzx r14, r14b
adcx r14, r8; loading flag
adcx r13, [ rsp + 0x350 ]
setc r14b; spill CF x534 to reg (r14)
movzx r8, byte [ rsp + 0x378 ]; load byte memx505 to register64
clc;
mov byte [ rsp + 0x3a0 ], dl; spilling byte x605 to mem
mov rdx, -0x1 ; moving imm to reg
adcx r8, rdx; loading flag
adcx r10, [ rsp + 0x2e0 ]
mov r8, 0x7bc65c783158aea3 ; moving imm to reg
mov rdx, r11; x540 to rdx
mov byte [ rsp + 0x3a8 ], r14b; spilling byte x534 to mem
mulx r11, r14, r8; x561, x560<- x540 * 0x7bc65c783158aea3
setc r8b; spill CF x507 to reg (r8)
clc;
mov [ rsp + 0x3b0 ], r11; spilling x561 to mem
mov r11, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, r11; loading flag
adcx r14, [ rsp + 0x368 ]
setc cl; spill CF x577 to reg (rcx)
clc;
movzx rbp, bpl
adcx rbp, r11; loading flag
adcx r10, r13
setc bpl; spill CF x549 to reg (rbp)
movzx r13, byte [ rsp + 0x380 ]; load byte memx590 to register64
clc;
adcx r13, r11; loading flag
adcx r10, r14
setc r13b; spill CF x592 to reg (r13)
seto r14b; spill OF x464 to reg (r14)
movzx r11, byte [ rsp + 0x3a0 ]; x605, copying x605 here, cause x605 is needed in a reg for other than x605, namely all: , x606--x607, size: 1
add r11, -0x1
mov r11, r10; x606, copying x591 here, cause x591 is needed in a reg for other than x606, namely all: , x606--x607, x619, size: 2
mov byte [ rsp + 0x3b8 ], bpl; spilling byte x549 to mem
mov rbp, 0xfdc1767ae2ffffff ; moving imm to reg
sbb r11, rbp
xchg rdx, r15; x6, swapping with x540, which is currently in rdx
mov [ rsp + 0x3c0 ], r11; spilling x606 to mem
mulx rbp, r11, [ rsi + 0x28 ]; x516, x515<- x6 * arg1[5]
xchg rdx, rax; x5, swapping with x6, which is currently in rdx
mov [ rsp + 0x3c8 ], rbp; spilling x516 to mem
mulx rdx, rbp, [ rsi + 0x30 ]; x427, x426<- x5 * arg1[6]
mov byte [ rsp + 0x3d0 ], r13b; spilling byte x592 to mem
movzx r13, byte [ rsp + 0x390 ]; load byte memx449 to register64
mov byte [ rsp + 0x3d8 ], cl; spilling byte x577 to mem
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r13, rcx; loading flag
adox rbp, [ rsp + 0x370 ]
setc r13b; spill CF x607 to reg (r13)
clc;
movzx r14, r14b
adcx r14, rcx; loading flag
adcx rbp, [ rsp + 0x2b0 ]
setc r14b; spill CF x466 to reg (r14)
clc;
movzx r8, r8b
adcx r8, rcx; loading flag
adcx rbp, [ rsp + 0x2d0 ]
mov r8, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, r8; 0x6cfc5fd681c52056, swapping with x427, which is currently in rdx
mov byte [ rsp + 0x3e0 ], r13b; spilling byte x607 to mem
mulx rcx, r13, r15; x559, x558<- x540 * 0x6cfc5fd681c52056
mov rdx, 0x0 ; moving imm to reg
adox r8, rdx
dec rdx; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
mov [ rsp + 0x3e8 ], rcx; spilling x559 to mem
movzx rcx, byte [ rsp + 0x2a8 ]; load byte memx425 to register64
movzx r14, r14b
adox r14, rdx; loading flag
adox r8, rcx
mov rcx, [ rsp + 0x2d8 ]; x510, copying x495 here, cause x495 is needed in a reg for other than x510, namely all: , x510--x511, size: 1
adcx rcx, r8
setc r14b; spill CF x511 to reg (r14)
movzx r8, byte [ rsp + 0x3a8 ]; load byte memx534 to register64
clc;
adcx r8, rdx; loading flag
adcx r11, [ rsp + 0x398 ]
setc r8b; spill CF x536 to reg (r8)
movzx rdx, byte [ rsp + 0x3d8 ]; load byte memx577 to register64
clc;
mov [ rsp + 0x3f0 ], rcx; spilling x510 to mem
mov rcx, -0x1 ; moving imm to reg
adcx rdx, rcx; loading flag
adcx r13, [ rsp + 0x3b0 ]
seto dl; spill OF x468 to reg (rdx)
movzx rcx, byte [ rsp + 0x3b8 ]; load byte memx549 to register64
mov byte [ rsp + 0x3f8 ], r8b; spilling byte x536 to mem
mov r8, 0x0 ; moving imm to reg
dec r8; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rcx, r8; loading flag
adox rbp, r11
setc cl; spill CF x579 to reg (rcx)
movzx r11, byte [ rsp + 0x3d0 ]; load byte memx592 to register64
clc;
adcx r11, r8; loading flag
adcx rbp, r13
xchg rdx, rax; x6, swapping with x468, which is currently in rdx
mulx rdx, r11, [ rsi + 0x30 ]; x514, x513<- x6 * arg1[6]
movzx r13, r14b; x512, copying x511 here, cause x511 is needed in a reg for other than x512, namely all: , x512, size: 1
movzx rax, al
lea r13, [ r13 + rax ]
setc al; spill CF x594 to reg (rax)
movzx r14, byte [ rsp + 0x3f8 ]; load byte memx536 to register64
clc;
adcx r14, r8; loading flag
adcx r11, [ rsp + 0x3c8 ]
mov r14, [ rsp + 0x3f0 ]; x552, copying x510 here, cause x510 is needed in a reg for other than x552, namely all: , x552--x553, size: 1
adox r14, r11
setc r11b; spill CF x538 to reg (r11)
seto r8b; spill OF x553 to reg (r8)
mov [ rsp + 0x400 ], r13; spilling x512 to mem
movzx r13, byte [ rsp + 0x3e0 ]; x607, copying x607 here, cause x607 is needed in a reg for other than x607, namely all: , x608--x609, size: 1
add r13, -0x1
mov r13, rbp; x608, copying x593 here, cause x593 is needed in a reg for other than x608, namely all: , x620, x608--x609, size: 2
mov [ rsp + 0x408 ], r14; spilling x552 to mem
mov r14, 0x7bc65c783158aea3 ; moving imm to reg
sbb r13, r14
movzx r14, r11b; x539, copying x538 here, cause x538 is needed in a reg for other than x539, namely all: , x539, size: 1
lea r14, [ r14 + rdx ]
mov rdx, 0x2341f27177344 ; moving imm to reg
mulx r15, r11, r15; x557, x556<- x540 * 0x2341f27177344
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, rdx; loading flag
adox r11, [ rsp + 0x3e8 ]
setc cl; spill CF x609 to reg (rcx)
clc;
movzx rax, al
adcx rax, rdx; loading flag
adcx r11, [ rsp + 0x408 ]
mov rax, 0x0 ; moving imm to reg
adox r15, rax
inc rdx; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov rax, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, rax; loading flag
adox r14, [ rsp + 0x400 ]
adcx r15, r14
setc r8b; spill CF x598 to reg (r8)
seto r14b; spill OF x555 to reg (r14)
movzx rdx, cl; x609, copying x609 here, cause x609 is needed in a reg for other than x609, namely all: , x610--x611, size: 1
add rdx, -0x1
mov rdx, r11; x610, copying x595 here, cause x595 is needed in a reg for other than x610, namely all: , x610--x611, x621, size: 2
mov rcx, 0x6cfc5fd681c52056 ; moving imm to reg
sbb rdx, rcx
movzx rax, r8b; x599, copying x598 here, cause x598 is needed in a reg for other than x599, namely all: , x599, size: 1
movzx r14, r14b
lea rax, [ rax + r14 ]
mov r14, r15; x612, copying x597 here, cause x597 is needed in a reg for other than x612, namely all: , x612--x613, x622, size: 2
mov r8, 0x2341f27177344 ; moving imm to reg
sbb r14, r8
sbb rax, 0x00000000
mov rax, [ rsp + 0x388 ]; x618, copying x604 here, cause x604 is needed in a reg for other than x618, namely all: , x618, size: 1
cmovc rax, rbx; if CF, x618<- x589 (nzVar)
mov rbx, [ rsp + 0x328 ]; x616, copying x600 here, cause x600 is needed in a reg for other than x616, namely all: , x616, size: 1
cmovc rbx, r12; if CF, x616<- x585 (nzVar)
cmovc r14, r15; if CF, x622<- x597 (nzVar)
mov r12, [ rsp + 0x338 ]; x617, copying x602 here, cause x602 is needed in a reg for other than x617, namely all: , x617, size: 1
cmovc r12, r9; if CF, x617<- x587 (nzVar)
mov r9, [ rsp + 0x3c0 ]; x619, copying x606 here, cause x606 is needed in a reg for other than x619, namely all: , x619, size: 1
cmovc r9, r10; if CF, x619<- x591 (nzVar)
mov r10, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r10 + 0x18 ], r9; out1[3] = x619
cmovc rdx, r11; if CF, x621<- x595 (nzVar)
mov [ r10 + 0x28 ], rdx; out1[5] = x621
mov [ r10 + 0x8 ], r12; out1[1] = x617
mov [ r10 + 0x10 ], rax; out1[2] = x618
cmovc r13, rbp; if CF, x620<- x593 (nzVar)
mov [ r10 + 0x30 ], r14; out1[6] = x622
mov [ r10 + 0x20 ], r13; out1[4] = x620
mov [ r10 + 0x0 ], rbx; out1[0] = x616
mov rbx, [ rsp + 0x410 ]; restoring from stack
mov rbp, [ rsp + 0x418 ]; restoring from stack
mov r12, [ rsp + 0x420 ]; restoring from stack
mov r13, [ rsp + 0x428 ]; restoring from stack
mov r14, [ rsp + 0x430 ]; restoring from stack
mov r15, [ rsp + 0x438 ]; restoring from stack
add rsp, 0x440 
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; clocked at 2200 MHz
; first cyclecount 504.07, best 463.23809523809524, lastGood 486.76190476190476
; seed 2513671278159213 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 6982149 ms / 60000 runs=> 116.36915ms/run
; Time spent for assembling and measureing (initial batch_size=21, initial num_batches=101): 216805 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.031051328179905642
; number reverted permutation/ tried permutation: 25881 / 29935 =86.457%
; number reverted decision/ tried decision: 22485 / 30066 =74.785%