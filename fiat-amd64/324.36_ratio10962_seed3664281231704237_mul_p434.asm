SECTION .text
	GLOBAL mul_p434
mul_p434:
sub rsp, 0x730 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x700 ], rbx; saving to stack
mov [ rsp + 0x708 ], rbp; saving to stack
mov [ rsp + 0x710 ], r12; saving to stack
mov [ rsp + 0x718 ], r13; saving to stack
mov [ rsp + 0x720 ], r14; saving to stack
mov [ rsp + 0x728 ], r15; saving to stack
mov rax, [ rsi + 0x28 ]; load m64 x5 to register64
mov r10, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x0 ]; saving arg2[0] in rdx.
mulx r11, rbx, rax; x439, x438<- x5 * arg2[0]
mov rbp, [ rsi + 0x20 ]; load m64 x4 to register64
mov rdx, [ r10 + 0x8 ]; arg2[1] to rdx
mulx r12, r13, rax; x437, x436<- x5 * arg2[1]
add r13, r11; could be done better, if r0 has been u8 as well
mov rdx, rax; x5 to rdx
mulx rax, r14, [ r10 + 0x10 ]; x435, x434<- x5 * arg2[2]
adcx r14, r12
mulx r15, rcx, [ r10 + 0x18 ]; x433, x432<- x5 * arg2[3]
mulx r8, r9, [ r10 + 0x20 ]; x431, x430<- x5 * arg2[4]
mulx r11, r12, [ r10 + 0x28 ]; x429, x428<- x5 * arg2[5]
adcx rcx, rax
adcx r9, r15
mulx rdx, rax, [ r10 + 0x30 ]; x427, x426<- x5 * arg2[6]
adcx r12, r8
adcx rax, r11
adc rdx, 0x0
mov r15, [ rsi + 0x0 ]; load m64 x7 to register64
xchg rdx, r15; x7, swapping with x452, which is currently in rdx
mulx r8, r11, [ r10 + 0x0 ]; x21, x20<- x7 * arg2[0]
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov rdi, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rdi; 0xffffffffffffffff, swapping with x7, which is currently in rdx
mov [ rsp + 0x8 ], r15; spilling x452 to mem
mov [ rsp + 0x10 ], rax; spilling x450 to mem
mulx r15, rax, r11; x48, x47<- x20 * 0xffffffffffffffff
xor rdx, rdx
adox rax, r11
mov rax, rdx; preserving value of 0x0 into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mov [ rsp + 0x18 ], r12; spilling x448 to mem
mov [ rsp + 0x20 ], r9; spilling x446 to mem
mulx r12, r9, rdi; x19, x18<- x7 * arg2[1]
adcx r9, r8
mov r8, 0xffffffffffffffff ; moving imm to reg
mov rdx, r8; 0xffffffffffffffff to rdx
mulx r8, rax, r11; x46, x45<- x20 * 0xffffffffffffffff
setc dl; spill CF x23 to reg (rdx)
clc;
adcx rax, r15
mov r15, [ rsi + 0x8 ]; load m64 x1 to register64
adox rax, r9
mov r9b, dl; preserving value of x23 into a new reg
mov rdx, [ r10 + 0x0 ]; saving arg2[0] in rdx.
mov [ rsp + 0x28 ], rcx; spilling x444 to mem
mov [ rsp + 0x30 ], r14; spilling x442 to mem
mulx rcx, r14, r15; x91, x90<- x1 * arg2[0]
mov [ rsp + 0x38 ], r13; spilling x440 to mem
seto r13b; spill OF x65 to reg (r13)
mov [ rsp + 0x40 ], rbx; spilling x438 to mem
mov rbx, -0x2 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, rax
mov rax, 0xffffffffffffffff ; moving imm to reg
mov rdx, rax; 0xffffffffffffffff to rdx
mulx rax, rbx, r14; x134, x133<- x105 * 0xffffffffffffffff
seto dl; spill OF x106 to reg (rdx)
mov [ rsp + 0x48 ], rbp; spilling x4 to mem
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, r14
mov bl, dl; preserving value of x106 into a new reg
mov rdx, [ r10 + 0x10 ]; saving arg2[2] in rdx.
mov [ rsp + 0x50 ], rax; spilling x134 to mem
mulx rbp, rax, rdi; x17, x16<- x7 * arg2[2]
mov [ rsp + 0x58 ], rbp; spilling x17 to mem
mov rbp, 0xffffffffffffffff ; moving imm to reg
mov rdx, r11; x20 to rdx
mov byte [ rsp + 0x60 ], bl; spilling byte x106 to mem
mulx r11, rbx, rbp; x44, x43<- x20 * 0xffffffffffffffff
setc bpl; spill CF x50 to reg (rbp)
clc;
mov [ rsp + 0x68 ], r11; spilling x44 to mem
mov r11, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, r11; loading flag
adcx r12, rax
seto r9b; spill OF x149 to reg (r9)
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rax, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, rax; loading flag
adox r8, rbx
setc bpl; spill CF x25 to reg (rbp)
clc;
movzx r13, r13b
adcx r13, rax; loading flag
adcx r12, r8
xchg rdx, r15; x1, swapping with x20, which is currently in rdx
mulx r13, rbx, [ r10 + 0x8 ]; x89, x88<- x1 * arg2[1]
mov r8, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r14; x105, swapping with x1, which is currently in rdx
mulx r11, rax, r8; x132, x131<- x105 * 0xffffffffffffffff
seto r8b; spill OF x52 to reg (r8)
mov [ rsp + 0x70 ], r11; spilling x132 to mem
mov r11, -0x2 ; moving imm to reg
inc r11; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, rcx
seto cl; spill OF x93 to reg (rcx)
movzx r11, byte [ rsp + 0x60 ]; load byte memx106 to register64
mov [ rsp + 0x78 ], r13; spilling x89 to mem
mov r13, -0x1 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r13, -0x1 ; moving imm to reg
adox r11, r13; loading flag
adox r12, rbx
mov r11, [ rsi + 0x10 ]; load m64 x2 to register64
setc bl; spill CF x67 to reg (rbx)
clc;
adcx rax, [ rsp + 0x50 ]
setc r13b; spill CF x136 to reg (r13)
clc;
mov byte [ rsp + 0x80 ], cl; spilling byte x93 to mem
mov rcx, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, rcx; loading flag
adcx r12, rax
xchg rdx, r11; x2, swapping with x105, which is currently in rdx
mulx r9, rax, [ r10 + 0x0 ]; x178, x177<- x2 * arg2[0]
seto cl; spill OF x108 to reg (rcx)
mov [ rsp + 0x88 ], r9; spilling x178 to mem
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rax, r12
mov r12, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rax; x192, swapping with x2, which is currently in rdx
mov byte [ rsp + 0x90 ], cl; spilling byte x108 to mem
mulx r9, rcx, r12; x221, x220<- x192 * 0xffffffffffffffff
setc r12b; spill CF x151 to reg (r12)
clc;
adcx rcx, rdx
mov rcx, rdx; preserving value of x192 into a new reg
mov rdx, [ r10 + 0x18 ]; saving arg2[3] in rdx.
mov [ rsp + 0x98 ], r9; spilling x221 to mem
mov byte [ rsp + 0xa0 ], r12b; spilling byte x151 to mem
mulx r9, r12, rdi; x15, x14<- x7 * arg2[3]
mov [ rsp + 0xa8 ], r9; spilling x15 to mem
mov r9, 0xfdc1767ae2ffffff ; moving imm to reg
mov rdx, r15; x20 to rdx
mov byte [ rsp + 0xb0 ], r13b; spilling byte x136 to mem
mulx r15, r13, r9; x42, x41<- x20 * 0xfdc1767ae2ffffff
setc r9b; spill CF x236 to reg (r9)
clc;
mov [ rsp + 0xb8 ], r15; spilling x42 to mem
mov r15, -0x1 ; moving imm to reg
movzx rbp, bpl
adcx rbp, r15; loading flag
adcx r12, [ rsp + 0x58 ]
mov rbp, rdx; preserving value of x20 into a new reg
mov rdx, [ r10 + 0x10 ]; saving arg2[2] in rdx.
mov byte [ rsp + 0xc0 ], r9b; spilling byte x236 to mem
mulx r15, r9, r14; x87, x86<- x1 * arg2[2]
mov [ rsp + 0xc8 ], r15; spilling x87 to mem
setc r15b; spill CF x27 to reg (r15)
clc;
mov [ rsp + 0xd0 ], r9; spilling x86 to mem
mov r9, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, r9; loading flag
adcx r13, [ rsp + 0x68 ]
setc r8b; spill CF x54 to reg (r8)
clc;
movzx rbx, bl
adcx rbx, r9; loading flag
adcx r12, r13
mov rbx, [ rsp + 0xd0 ]; load m64 x86 to register64
setc r13b; spill CF x69 to reg (r13)
movzx r9, byte [ rsp + 0x80 ]; load byte memx93 to register64
clc;
mov byte [ rsp + 0xd8 ], r15b; spilling byte x27 to mem
mov r15, -0x1 ; moving imm to reg
adcx r9, r15; loading flag
adcx rbx, [ rsp + 0x78 ]
mov r9, 0xffffffffffffffff ; moving imm to reg
mov rdx, r9; 0xffffffffffffffff to rdx
mulx r9, r15, r11; x130, x129<- x105 * 0xffffffffffffffff
setc dl; spill CF x95 to reg (rdx)
mov [ rsp + 0xe0 ], r9; spilling x130 to mem
movzx r9, byte [ rsp + 0xb0 ]; load byte memx136 to register64
clc;
mov byte [ rsp + 0xe8 ], r13b; spilling byte x69 to mem
mov r13, -0x1 ; moving imm to reg
adcx r9, r13; loading flag
adcx r15, [ rsp + 0x70 ]
seto r9b; spill OF x193 to reg (r9)
movzx r13, byte [ rsp + 0x90 ]; load byte memx108 to register64
mov byte [ rsp + 0xf0 ], dl; spilling byte x95 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r13, rdx; loading flag
adox r12, rbx
seto r13b; spill OF x110 to reg (r13)
movzx rbx, byte [ rsp + 0xa0 ]; load byte memx151 to register64
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
adox rbx, rdx; loading flag
adox r12, r15
mov rdx, rax; x2 to rdx
mulx rax, rbx, [ r10 + 0x8 ]; x176, x175<- x2 * arg2[1]
seto r15b; spill OF x153 to reg (r15)
mov byte [ rsp + 0xf8 ], r13b; spilling byte x110 to mem
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, [ rsp + 0x88 ]
seto r13b; spill OF x180 to reg (r13)
mov byte [ rsp + 0x100 ], r15b; spilling byte x153 to mem
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r15, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, r15; loading flag
adox r12, rbx
mov r9, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r9; 0xffffffffffffffff, swapping with x2, which is currently in rdx
mulx rbx, r15, rcx; x219, x218<- x192 * 0xffffffffffffffff
seto dl; spill OF x195 to reg (rdx)
mov [ rsp + 0x108 ], rbx; spilling x219 to mem
mov rbx, -0x2 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, [ rsp + 0x98 ]
setc bl; spill CF x138 to reg (rbx)
mov byte [ rsp + 0x110 ], dl; spilling byte x195 to mem
movzx rdx, byte [ rsp + 0xc0 ]; load byte memx236 to register64
clc;
mov [ rsp + 0x118 ], rax; spilling x176 to mem
mov rax, -0x1 ; moving imm to reg
adcx rdx, rax; loading flag
adcx r12, r15
mov rdx, [ rsi + 0x18 ]; load m64 x3 to register64
mulx r15, rax, [ r10 + 0x0 ]; x265, x264<- x3 * arg2[0]
mov byte [ rsp + 0x120 ], bl; spilling byte x138 to mem
setc bl; spill CF x238 to reg (rbx)
clc;
adcx rax, r12
mov r12, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r12; 0xffffffffffffffff, swapping with x3, which is currently in rdx
mov byte [ rsp + 0x128 ], bl; spilling byte x238 to mem
mov [ rsp + 0x130 ], r15; spilling x265 to mem
mulx rbx, r15, rax; x308, x307<- x279 * 0xffffffffffffffff
mov [ rsp + 0x138 ], r15; spilling x307 to mem
mov byte [ rsp + 0x140 ], r13b; spilling byte x180 to mem
mulx r15, r13, rax; x306, x305<- x279 * 0xffffffffffffffff
seto dl; spill OF x223 to reg (rdx)
mov byte [ rsp + 0x148 ], r8b; spilling byte x54 to mem
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, rbx
mov rbx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rax; x279, swapping with x223, which is currently in rdx
mov [ rsp + 0x150 ], r13; spilling x309 to mem
mulx r8, r13, rbx; x304, x303<- x279 * 0xffffffffffffffff
mov rbx, 0xfdc1767ae2ffffff ; moving imm to reg
mov byte [ rsp + 0x158 ], al; spilling byte x223 to mem
mov [ rsp + 0x160 ], r8; spilling x304 to mem
mulx rax, r8, rbx; x302, x301<- x279 * 0xfdc1767ae2ffffff
adox r13, r15
mov r15, [ rsp + 0x160 ]; x313, copying x304 here, cause x304 is needed in a reg for other than x313, namely all: , x313--x314, size: 1
adox r15, r8
mov r8, 0x7bc65c783158aea3 ; moving imm to reg
mov [ rsp + 0x168 ], r15; spilling x313 to mem
mulx rbx, r15, r8; x300, x299<- x279 * 0x7bc65c783158aea3
adox r15, rax
mov rax, 0x6cfc5fd681c52056 ; moving imm to reg
mov [ rsp + 0x170 ], r15; spilling x315 to mem
mulx r8, r15, rax; x298, x297<- x279 * 0x6cfc5fd681c52056
mov rax, 0x2341f27177344 ; moving imm to reg
mov [ rsp + 0x178 ], r13; spilling x311 to mem
mov [ rsp + 0x180 ], r8; spilling x298 to mem
mulx r13, r8, rax; x296, x295<- x279 * 0x2341f27177344
adox r15, rbx
mov rbx, [ rsp + 0x180 ]; x319, copying x298 here, cause x298 is needed in a reg for other than x319, namely all: , x319--x320, size: 1
adox rbx, r8
mov r8, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, r8; 0x7bc65c783158aea3, swapping with x279, which is currently in rdx
mov [ rsp + 0x188 ], rbx; spilling x319 to mem
mulx rax, rbx, rbp; x40, x39<- x20 * 0x7bc65c783158aea3
mov rdx, 0x0 ; moving imm to reg
adox r13, rdx
movzx rdx, byte [ rsp + 0x148 ]; load byte memx54 to register64
mov [ rsp + 0x190 ], r13; spilling x321 to mem
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rdx, r13; loading flag
adox rbx, [ rsp + 0xb8 ]
mov rdx, 0x6cfc5fd681c52056 ; moving imm to reg
mov [ rsp + 0x198 ], r15; spilling x317 to mem
mulx r13, r15, rbp; x38, x37<- x20 * 0x6cfc5fd681c52056
mov rdx, 0x2341f27177344 ; moving imm to reg
mov [ rsp + 0x1a0 ], rbx; spilling x55 to mem
mulx rbp, rbx, rbp; x36, x35<- x20 * 0x2341f27177344
adox r15, rax
adox rbx, r13
mov rax, rdx; preserving value of 0x2341f27177344 into a new reg
mov rdx, [ r10 + 0x10 ]; saving arg2[2] in rdx.
mov [ rsp + 0x1a8 ], rbx; spilling x59 to mem
mulx r13, rbx, r9; x174, x173<- x2 * arg2[2]
mov rax, 0x0 ; moving imm to reg
adox rbp, rax
mov rdx, r9; x2 to rdx
mulx r9, rax, [ r10 + 0x18 ]; x172, x171<- x2 * arg2[3]
mov [ rsp + 0x1b0 ], rbp; spilling x61 to mem
mov [ rsp + 0x1b8 ], r15; spilling x57 to mem
mulx rbp, r15, [ r10 + 0x20 ]; x170, x169<- x2 * arg2[4]
mov [ rsp + 0x1c0 ], rbp; spilling x170 to mem
movzx rbp, byte [ rsp + 0x140 ]; load byte memx180 to register64
mov [ rsp + 0x1c8 ], r15; spilling x169 to mem
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbp, r15; loading flag
adox rbx, [ rsp + 0x118 ]
adox rax, r13
mov rbp, [ rsp + 0x1c8 ]; x185, copying x169 here, cause x169 is needed in a reg for other than x185, namely all: , x185--x186, size: 1
adox rbp, r9
mulx r13, r9, [ r10 + 0x28 ]; x168, x167<- x2 * arg2[5]
mov r15, [ rsp + 0x1c0 ]; x187, copying x170 here, cause x170 is needed in a reg for other than x187, namely all: , x187--x188, size: 1
adox r15, r9
mulx rdx, r9, [ r10 + 0x30 ]; x166, x165<- x2 * arg2[6]
adox r9, r13
mov r13, 0x0 ; moving imm to reg
adox rdx, r13
xchg rdx, r12; x3, swapping with x191, which is currently in rdx
mov [ rsp + 0x1d0 ], r12; spilling x191 to mem
mulx r13, r12, [ r10 + 0x8 ]; x263, x262<- x3 * arg2[1]
mov [ rsp + 0x1d8 ], r9; spilling x189 to mem
mov [ rsp + 0x1e0 ], r15; spilling x187 to mem
mulx r9, r15, [ r10 + 0x10 ]; x261, x260<- x3 * arg2[2]
mov [ rsp + 0x1e8 ], rbp; spilling x185 to mem
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, [ rsp + 0x130 ]
mov [ rsp + 0x1f0 ], rax; spilling x183 to mem
mulx rbp, rax, [ r10 + 0x18 ]; x259, x258<- x3 * arg2[3]
adox r15, r13
adox rax, r9
mulx r13, r9, [ r10 + 0x20 ]; x257, x256<- x3 * arg2[4]
adox r9, rbp
mov [ rsp + 0x1f8 ], r9; spilling x272 to mem
mulx rbp, r9, [ r10 + 0x28 ]; x255, x254<- x3 * arg2[5]
adox r9, r13
mulx rdx, r13, [ r10 + 0x30 ]; x253, x252<- x3 * arg2[6]
adox r13, rbp
mov rbp, [ rsi + 0x30 ]; load m64 x6 to register64
mov [ rsp + 0x200 ], r13; spilling x276 to mem
mov r13, 0x0 ; moving imm to reg
adox rdx, r13
mov r13, rdx; preserving value of x278 into a new reg
mov rdx, [ r10 + 0x0 ]; saving arg2[0] in rdx.
mov [ rsp + 0x208 ], r9; spilling x274 to mem
mov [ rsp + 0x210 ], rax; spilling x270 to mem
mulx r9, rax, rbp; x526, x525<- x6 * arg2[0]
mov rdx, rbp; x6 to rdx
mov [ rsp + 0x218 ], r13; spilling x278 to mem
mulx rbp, r13, [ r10 + 0x8 ]; x524, x523<- x6 * arg2[1]
mov [ rsp + 0x220 ], rax; spilling x525 to mem
mov rax, -0x2 ; moving imm to reg
inc rax; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, r9
mulx r9, rax, [ r10 + 0x10 ]; x522, x521<- x6 * arg2[2]
adox rax, rbp
mov [ rsp + 0x228 ], rax; spilling x529 to mem
mulx rbp, rax, [ r10 + 0x20 ]; x518, x517<- x6 * arg2[4]
mov [ rsp + 0x230 ], r13; spilling x527 to mem
mov [ rsp + 0x238 ], r15; spilling x268 to mem
mulx r13, r15, [ r10 + 0x18 ]; x520, x519<- x6 * arg2[3]
adox r15, r9
adox rax, r13
mulx r9, r13, [ r10 + 0x28 ]; x516, x515<- x6 * arg2[5]
adox r13, rbp
mulx rdx, rbp, [ r10 + 0x30 ]; x514, x513<- x6 * arg2[6]
adox rbp, r9
setc r9b; spill CF x280 to reg (r9)
clc;
adcx r8, [ rsp + 0x138 ]
mov r8, 0x0 ; moving imm to reg
adox rdx, r8
mov r8, rdx; preserving value of x539 into a new reg
mov rdx, [ r10 + 0x20 ]; saving arg2[4] in rdx.
mov [ rsp + 0x240 ], rbp; spilling x537 to mem
mov [ rsp + 0x248 ], r13; spilling x535 to mem
mulx rbp, r13, rdi; x13, x12<- x7 * arg2[4]
mov [ rsp + 0x250 ], r8; spilling x539 to mem
movzx r8, byte [ rsp + 0xd8 ]; load byte memx27 to register64
mov [ rsp + 0x258 ], rax; spilling x533 to mem
mov rax, -0x1 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rax, -0x1 ; moving imm to reg
adox r8, rax; loading flag
adox r13, [ rsp + 0xa8 ]
mov rdx, [ r10 + 0x18 ]; arg2[3] to rdx
mulx r8, rax, r14; x85, x84<- x1 * arg2[3]
mov [ rsp + 0x260 ], r15; spilling x531 to mem
setc r15b; spill CF x323 to reg (r15)
mov [ rsp + 0x268 ], r8; spilling x85 to mem
movzx r8, byte [ rsp + 0xf0 ]; load byte memx95 to register64
clc;
mov [ rsp + 0x270 ], rbp; spilling x13 to mem
mov rbp, -0x1 ; moving imm to reg
adcx r8, rbp; loading flag
adcx rax, [ rsp + 0xc8 ]
seto r8b; spill OF x29 to reg (r8)
movzx rbp, byte [ rsp + 0xe8 ]; load byte memx69 to register64
mov byte [ rsp + 0x278 ], r15b; spilling byte x323 to mem
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbp, r15; loading flag
adox r13, [ rsp + 0x1a0 ]
seto bpl; spill OF x71 to reg (rbp)
movzx r15, byte [ rsp + 0xf8 ]; load byte memx110 to register64
mov byte [ rsp + 0x280 ], r8b; spilling byte x29 to mem
mov r8, 0x0 ; moving imm to reg
dec r8; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, r8; loading flag
adox r13, rax
mov r15, 0xfdc1767ae2ffffff ; moving imm to reg
mov rdx, r11; x105 to rdx
mulx r11, rax, r15; x128, x127<- x105 * 0xfdc1767ae2ffffff
seto r8b; spill OF x112 to reg (r8)
movzx r15, byte [ rsp + 0x120 ]; load byte memx138 to register64
mov [ rsp + 0x288 ], r11; spilling x128 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
adox r15, r11; loading flag
adox rax, [ rsp + 0xe0 ]
setc r15b; spill CF x97 to reg (r15)
movzx r11, byte [ rsp + 0x100 ]; load byte memx153 to register64
clc;
mov byte [ rsp + 0x290 ], r8b; spilling byte x112 to mem
mov r8, -0x1 ; moving imm to reg
adcx r11, r8; loading flag
adcx r13, rax
setc r11b; spill CF x155 to reg (r11)
movzx rax, byte [ rsp + 0x110 ]; load byte memx195 to register64
clc;
adcx rax, r8; loading flag
adcx r13, rbx
mov rax, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rcx; x192, swapping with x105, which is currently in rdx
mulx rbx, r8, rax; x217, x216<- x192 * 0xffffffffffffffff
seto al; spill OF x140 to reg (rax)
mov [ rsp + 0x298 ], rbx; spilling x217 to mem
movzx rbx, byte [ rsp + 0x158 ]; load byte memx223 to register64
mov byte [ rsp + 0x2a0 ], r11b; spilling byte x155 to mem
mov r11, 0x0 ; moving imm to reg
dec r11; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbx, r11; loading flag
adox r8, [ rsp + 0x108 ]
seto bl; spill OF x225 to reg (rbx)
movzx r11, byte [ rsp + 0x128 ]; load byte memx238 to register64
mov byte [ rsp + 0x2a8 ], al; spilling byte x140 to mem
mov rax, -0x1 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rax, -0x1 ; moving imm to reg
adox r11, rax; loading flag
adox r13, r8
setc r11b; spill CF x197 to reg (r11)
clc;
movzx r9, r9b
adcx r9, rax; loading flag
adcx r13, r12
seto r9b; spill OF x240 to reg (r9)
movzx r12, byte [ rsp + 0x278 ]; load byte memx323 to register64
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
adox r12, r8; loading flag
adox r13, [ rsp + 0x150 ]
mov r12, rdx; preserving value of x192 into a new reg
mov rdx, [ rsp + 0x48 ]; saving x4 in rdx.
mulx rax, r8, [ r10 + 0x0 ]; x352, x351<- x4 * arg2[0]
mov [ rsp + 0x2b0 ], rax; spilling x352 to mem
seto al; spill OF x325 to reg (rax)
mov byte [ rsp + 0x2b8 ], r9b; spilling byte x240 to mem
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, r13
mov r13, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r8; x366, swapping with x4, which is currently in rdx
mov byte [ rsp + 0x2c0 ], al; spilling byte x325 to mem
mulx r9, rax, r13; x395, x394<- x366 * 0xffffffffffffffff
setc r13b; spill CF x282 to reg (r13)
clc;
adcx rax, rdx
mov rax, rdx; preserving value of x366 into a new reg
mov rdx, [ r10 + 0x28 ]; saving arg2[5] in rdx.
mov [ rsp + 0x2c8 ], r9; spilling x395 to mem
mov byte [ rsp + 0x2d0 ], r13b; spilling byte x282 to mem
mulx r9, r13, rdi; x11, x10<- x7 * arg2[5]
mov [ rsp + 0x2d8 ], r9; spilling x11 to mem
setc r9b; spill CF x410 to reg (r9)
mov byte [ rsp + 0x2e0 ], bl; spilling byte x225 to mem
movzx rbx, byte [ rsp + 0x280 ]; load byte memx29 to register64
clc;
mov byte [ rsp + 0x2e8 ], r11b; spilling byte x197 to mem
mov r11, -0x1 ; moving imm to reg
adcx rbx, r11; loading flag
adcx r13, [ rsp + 0x270 ]
mov rdx, r14; x1 to rdx
mulx r14, rbx, [ r10 + 0x20 ]; x83, x82<- x1 * arg2[4]
seto r11b; spill OF x367 to reg (r11)
mov [ rsp + 0x2f0 ], r14; spilling x83 to mem
mov r14, -0x1 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r14, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, r14; loading flag
adox r13, [ rsp + 0x1b8 ]
setc bpl; spill CF x31 to reg (rbp)
clc;
movzx r15, r15b
adcx r15, r14; loading flag
adcx rbx, [ rsp + 0x268 ]
mov r15, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, rcx; x105, swapping with x1, which is currently in rdx
mov byte [ rsp + 0x2f8 ], bpl; spilling byte x31 to mem
mulx r14, rbp, r15; x126, x125<- x105 * 0x7bc65c783158aea3
setc r15b; spill CF x99 to reg (r15)
mov [ rsp + 0x300 ], r14; spilling x126 to mem
movzx r14, byte [ rsp + 0x2a8 ]; load byte memx140 to register64
clc;
mov byte [ rsp + 0x308 ], r9b; spilling byte x410 to mem
mov r9, -0x1 ; moving imm to reg
adcx r14, r9; loading flag
adcx rbp, [ rsp + 0x288 ]
seto r14b; spill OF x73 to reg (r14)
movzx r9, byte [ rsp + 0x290 ]; load byte memx112 to register64
mov byte [ rsp + 0x310 ], r15b; spilling byte x99 to mem
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r15, -0x1 ; moving imm to reg
adox r9, r15; loading flag
adox r13, rbx
setc r9b; spill CF x142 to reg (r9)
movzx rbx, byte [ rsp + 0x2a0 ]; load byte memx155 to register64
clc;
adcx rbx, r15; loading flag
adcx r13, rbp
mov rbx, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, r12; x192, swapping with x105, which is currently in rdx
mulx rbp, r15, rbx; x215, x214<- x192 * 0xfdc1767ae2ffffff
seto bl; spill OF x114 to reg (rbx)
mov [ rsp + 0x318 ], rbp; spilling x215 to mem
movzx rbp, byte [ rsp + 0x2e8 ]; load byte memx197 to register64
mov byte [ rsp + 0x320 ], r9b; spilling byte x142 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbp, r9; loading flag
adox r13, [ rsp + 0x1f0 ]
setc bpl; spill CF x157 to reg (rbp)
movzx r9, byte [ rsp + 0x2e0 ]; load byte memx225 to register64
clc;
mov byte [ rsp + 0x328 ], bl; spilling byte x114 to mem
mov rbx, -0x1 ; moving imm to reg
adcx r9, rbx; loading flag
adcx r15, [ rsp + 0x298 ]
setc r9b; spill CF x227 to reg (r9)
movzx rbx, byte [ rsp + 0x2b8 ]; load byte memx240 to register64
clc;
mov byte [ rsp + 0x330 ], bpl; spilling byte x157 to mem
mov rbp, -0x1 ; moving imm to reg
adcx rbx, rbp; loading flag
adcx r13, r15
setc bl; spill CF x242 to reg (rbx)
movzx r15, byte [ rsp + 0x2d0 ]; load byte memx282 to register64
clc;
adcx r15, rbp; loading flag
adcx r13, [ rsp + 0x238 ]
setc r15b; spill CF x284 to reg (r15)
movzx rbp, byte [ rsp + 0x2c0 ]; load byte memx325 to register64
clc;
mov byte [ rsp + 0x338 ], bl; spilling byte x242 to mem
mov rbx, -0x1 ; moving imm to reg
adcx rbp, rbx; loading flag
adcx r13, [ rsp + 0x178 ]
xchg rdx, r8; x4, swapping with x192, which is currently in rdx
mulx rbp, rbx, [ r10 + 0x8 ]; x350, x349<- x4 * arg2[1]
mov [ rsp + 0x340 ], rbp; spilling x350 to mem
mov rbp, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbp; 0xffffffffffffffff, swapping with x4, which is currently in rdx
mov byte [ rsp + 0x348 ], r15b; spilling byte x284 to mem
mov byte [ rsp + 0x350 ], r9b; spilling byte x227 to mem
mulx r15, r9, rax; x393, x392<- x366 * 0xffffffffffffffff
setc dl; spill CF x327 to reg (rdx)
clc;
adcx rbx, [ rsp + 0x2b0 ]
mov [ rsp + 0x358 ], r15; spilling x393 to mem
setc r15b; spill CF x354 to reg (r15)
clc;
mov byte [ rsp + 0x360 ], dl; spilling byte x327 to mem
mov rdx, -0x1 ; moving imm to reg
movzx r11, r11b
adcx r11, rdx; loading flag
adcx r13, rbx
seto r11b; spill OF x199 to reg (r11)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r9, [ rsp + 0x2c8 ]
seto bl; spill OF x397 to reg (rbx)
movzx rdx, byte [ rsp + 0x308 ]; load byte memx410 to register64
mov byte [ rsp + 0x368 ], r15b; spilling byte x354 to mem
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r15, -0x1 ; moving imm to reg
adox rdx, r15; loading flag
adox r13, r9
setc dl; spill CF x369 to reg (rdx)
clc;
adcx r13, [ rsp + 0x40 ]
mov r9, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r13; x453, swapping with x369, which is currently in rdx
mov byte [ rsp + 0x370 ], bl; spilling byte x397 to mem
mulx r15, rbx, r9; x482, x481<- x453 * 0xffffffffffffffff
xchg rdx, rdi; x7, swapping with x453, which is currently in rdx
mulx rdx, r9, [ r10 + 0x30 ]; x9, x8<- x7 * arg2[6]
mov [ rsp + 0x378 ], rdx; spilling x9 to mem
setc dl; spill CF x454 to reg (rdx)
clc;
adcx rbx, rdi
seto bl; spill OF x412 to reg (rbx)
mov [ rsp + 0x380 ], r15; spilling x482 to mem
movzx r15, byte [ rsp + 0x2f8 ]; load byte memx31 to register64
mov byte [ rsp + 0x388 ], dl; spilling byte x454 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, rdx; loading flag
adox r9, [ rsp + 0x2d8 ]
seto r15b; spill OF x33 to reg (r15)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, rdx; loading flag
adox r9, [ rsp + 0x1a8 ]
mov rdx, rcx; x1 to rdx
mulx rcx, r14, [ r10 + 0x28 ]; x81, x80<- x1 * arg2[5]
mov [ rsp + 0x390 ], rcx; spilling x81 to mem
setc cl; spill CF x497 to reg (rcx)
mov byte [ rsp + 0x398 ], r15b; spilling byte x33 to mem
movzx r15, byte [ rsp + 0x310 ]; load byte memx99 to register64
clc;
mov byte [ rsp + 0x3a0 ], bl; spilling byte x412 to mem
mov rbx, -0x1 ; moving imm to reg
adcx r15, rbx; loading flag
adcx r14, [ rsp + 0x2f0 ]
mov r15, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, r12; x105, swapping with x1, which is currently in rdx
mov byte [ rsp + 0x3a8 ], cl; spilling byte x497 to mem
mulx rbx, rcx, r15; x124, x123<- x105 * 0x6cfc5fd681c52056
seto r15b; spill OF x75 to reg (r15)
mov [ rsp + 0x3b0 ], rbx; spilling x124 to mem
movzx rbx, byte [ rsp + 0x320 ]; load byte memx142 to register64
mov byte [ rsp + 0x3b8 ], r13b; spilling byte x369 to mem
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbx, r13; loading flag
adox rcx, [ rsp + 0x300 ]
seto bl; spill OF x144 to reg (rbx)
movzx r13, byte [ rsp + 0x328 ]; load byte memx114 to register64
mov byte [ rsp + 0x3c0 ], r15b; spilling byte x75 to mem
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r15, -0x1 ; moving imm to reg
adox r13, r15; loading flag
adox r9, r14
seto r13b; spill OF x116 to reg (r13)
movzx r14, byte [ rsp + 0x330 ]; load byte memx157 to register64
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
adox r14, r15; loading flag
adox r9, rcx
seto r14b; spill OF x159 to reg (r14)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rcx, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, rcx; loading flag
adox r9, [ rsp + 0x1e8 ]
mov r11, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, r8; x192, swapping with x105, which is currently in rdx
mulx r15, rcx, r11; x213, x212<- x192 * 0x7bc65c783158aea3
seto r11b; spill OF x201 to reg (r11)
mov [ rsp + 0x3c8 ], r15; spilling x213 to mem
movzx r15, byte [ rsp + 0x350 ]; load byte memx227 to register64
mov byte [ rsp + 0x3d0 ], r14b; spilling byte x159 to mem
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, r14; loading flag
adox rcx, [ rsp + 0x318 ]
setc r15b; spill CF x101 to reg (r15)
movzx r14, byte [ rsp + 0x338 ]; load byte memx242 to register64
clc;
mov byte [ rsp + 0x3d8 ], r11b; spilling byte x201 to mem
mov r11, -0x1 ; moving imm to reg
adcx r14, r11; loading flag
adcx r9, rcx
seto r14b; spill OF x229 to reg (r14)
movzx rcx, byte [ rsp + 0x348 ]; load byte memx284 to register64
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r11, -0x1 ; moving imm to reg
adox rcx, r11; loading flag
adox r9, [ rsp + 0x210 ]
seto cl; spill OF x286 to reg (rcx)
movzx r11, byte [ rsp + 0x360 ]; load byte memx327 to register64
mov byte [ rsp + 0x3e0 ], r14b; spilling byte x229 to mem
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r11, r14; loading flag
adox r9, [ rsp + 0x168 ]
xchg rdx, rbp; x4, swapping with x192, which is currently in rdx
mulx r11, r14, [ r10 + 0x10 ]; x348, x347<- x4 * arg2[2]
mov [ rsp + 0x3e8 ], r11; spilling x348 to mem
setc r11b; spill CF x244 to reg (r11)
mov byte [ rsp + 0x3f0 ], cl; spilling byte x286 to mem
movzx rcx, byte [ rsp + 0x368 ]; load byte memx354 to register64
clc;
mov byte [ rsp + 0x3f8 ], bl; spilling byte x144 to mem
mov rbx, -0x1 ; moving imm to reg
adcx rcx, rbx; loading flag
adcx r14, [ rsp + 0x340 ]
seto cl; spill OF x329 to reg (rcx)
movzx rbx, byte [ rsp + 0x3b8 ]; load byte memx369 to register64
mov byte [ rsp + 0x400 ], r11b; spilling byte x244 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
adox rbx, r11; loading flag
adox r9, r14
mov rbx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rax; x366, swapping with x4, which is currently in rdx
mulx r14, r11, rbx; x391, x390<- x366 * 0xffffffffffffffff
setc bl; spill CF x356 to reg (rbx)
mov [ rsp + 0x408 ], r14; spilling x391 to mem
movzx r14, byte [ rsp + 0x370 ]; load byte memx397 to register64
clc;
mov byte [ rsp + 0x410 ], cl; spilling byte x329 to mem
mov rcx, -0x1 ; moving imm to reg
adcx r14, rcx; loading flag
adcx r11, [ rsp + 0x358 ]
setc r14b; spill CF x399 to reg (r14)
movzx rcx, byte [ rsp + 0x3a0 ]; load byte memx412 to register64
clc;
mov byte [ rsp + 0x418 ], bl; spilling byte x356 to mem
mov rbx, -0x1 ; moving imm to reg
adcx rcx, rbx; loading flag
adcx r9, r11
mov rcx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rcx; 0xffffffffffffffff, swapping with x366, which is currently in rdx
mulx r11, rbx, rdi; x480, x479<- x453 * 0xffffffffffffffff
setc dl; spill CF x414 to reg (rdx)
mov [ rsp + 0x420 ], r11; spilling x480 to mem
movzx r11, byte [ rsp + 0x388 ]; load byte memx454 to register64
clc;
mov byte [ rsp + 0x428 ], r14b; spilling byte x399 to mem
mov r14, -0x1 ; moving imm to reg
adcx r11, r14; loading flag
adcx r9, [ rsp + 0x38 ]
seto r11b; spill OF x371 to reg (r11)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rbx, [ rsp + 0x380 ]
setc r14b; spill CF x456 to reg (r14)
mov byte [ rsp + 0x430 ], dl; spilling byte x414 to mem
movzx rdx, byte [ rsp + 0x3a8 ]; load byte memx497 to register64
clc;
mov byte [ rsp + 0x438 ], r11b; spilling byte x371 to mem
mov r11, -0x1 ; moving imm to reg
adcx rdx, r11; loading flag
adcx r9, rbx
setc dl; spill CF x499 to reg (rdx)
clc;
adcx r9, [ rsp + 0x220 ]
mov rbx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbx; 0xffffffffffffffff, swapping with x499, which is currently in rdx
mov byte [ rsp + 0x440 ], bl; spilling byte x499 to mem
mulx r11, rbx, r9; x569, x568<- x540 * 0xffffffffffffffff
movzx rdx, byte [ rsp + 0x398 ]; x34, copying x33 here, cause x33 is needed in a reg for other than x34, namely all: , x34, size: 1
mov [ rsp + 0x448 ], r11; spilling x569 to mem
mov r11, [ rsp + 0x378 ]; load m64 x9 to register64
lea rdx, [ rdx + r11 ]; r8/64 + m8
seto r11b; spill OF x484 to reg (r11)
mov byte [ rsp + 0x450 ], r14b; spilling byte x456 to mem
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, r9
xchg rdx, r12; x1, swapping with x34, which is currently in rdx
mulx rdx, rbx, [ r10 + 0x30 ]; x79, x78<- x1 * arg2[6]
seto r14b; spill OF x584 to reg (r14)
mov [ rsp + 0x458 ], rdx; spilling x79 to mem
movzx rdx, byte [ rsp + 0x3c0 ]; load byte memx75 to register64
mov byte [ rsp + 0x460 ], r11b; spilling byte x484 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
adox rdx, r11; loading flag
adox r12, [ rsp + 0x1b0 ]
mov rdx, 0x2341f27177344 ; moving imm to reg
mulx r8, r11, r8; x122, x121<- x105 * 0x2341f27177344
seto dl; spill OF x77 to reg (rdx)
mov [ rsp + 0x468 ], r8; spilling x122 to mem
mov r8, -0x1 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r8, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, r8; loading flag
adox rbx, [ rsp + 0x390 ]
setc r15b; spill CF x541 to reg (r15)
clc;
movzx r13, r13b
adcx r13, r8; loading flag
adcx r12, rbx
seto r13b; spill OF x103 to reg (r13)
movzx rbx, byte [ rsp + 0x3f8 ]; load byte memx144 to register64
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
adox rbx, r8; loading flag
adox r11, [ rsp + 0x3b0 ]
seto bl; spill OF x146 to reg (rbx)
movzx r8, byte [ rsp + 0x3d0 ]; load byte memx159 to register64
mov byte [ rsp + 0x470 ], dl; spilling byte x77 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r8, rdx; loading flag
adox r12, r11
mov r8, 0x6cfc5fd681c52056 ; moving imm to reg
mov rdx, rbp; x192 to rdx
mulx rbp, r11, r8; x211, x210<- x192 * 0x6cfc5fd681c52056
seto r8b; spill OF x161 to reg (r8)
mov [ rsp + 0x478 ], rbp; spilling x211 to mem
movzx rbp, byte [ rsp + 0x3d8 ]; load byte memx201 to register64
mov byte [ rsp + 0x480 ], bl; spilling byte x146 to mem
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbp, rbx; loading flag
adox r12, [ rsp + 0x1e0 ]
seto bpl; spill OF x203 to reg (rbp)
movzx rbx, byte [ rsp + 0x3e0 ]; load byte memx229 to register64
mov byte [ rsp + 0x488 ], r8b; spilling byte x161 to mem
mov r8, -0x1 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r8, -0x1 ; moving imm to reg
adox rbx, r8; loading flag
adox r11, [ rsp + 0x3c8 ]
setc bl; spill CF x118 to reg (rbx)
movzx r8, byte [ rsp + 0x400 ]; load byte memx244 to register64
clc;
mov byte [ rsp + 0x490 ], bpl; spilling byte x203 to mem
mov rbp, -0x1 ; moving imm to reg
adcx r8, rbp; loading flag
adcx r12, r11
setc r8b; spill CF x246 to reg (r8)
movzx r11, byte [ rsp + 0x3f0 ]; load byte memx286 to register64
clc;
adcx r11, rbp; loading flag
adcx r12, [ rsp + 0x1f8 ]
seto r11b; spill OF x231 to reg (r11)
movzx rbp, byte [ rsp + 0x410 ]; load byte memx329 to register64
mov byte [ rsp + 0x498 ], r8b; spilling byte x246 to mem
mov r8, 0x0 ; moving imm to reg
dec r8; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbp, r8; loading flag
adox r12, [ rsp + 0x170 ]
mov rbp, rdx; preserving value of x192 into a new reg
mov rdx, [ r10 + 0x18 ]; saving arg2[3] in rdx.
mov byte [ rsp + 0x4a0 ], r11b; spilling byte x231 to mem
mulx r8, r11, rax; x346, x345<- x4 * arg2[3]
mov [ rsp + 0x4a8 ], r8; spilling x346 to mem
seto r8b; spill OF x331 to reg (r8)
mov byte [ rsp + 0x4b0 ], bl; spilling byte x118 to mem
movzx rbx, byte [ rsp + 0x418 ]; load byte memx356 to register64
mov byte [ rsp + 0x4b8 ], r13b; spilling byte x103 to mem
mov r13, -0x1 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r13, -0x1 ; moving imm to reg
adox rbx, r13; loading flag
adox r11, [ rsp + 0x3e8 ]
mov rbx, 0xfdc1767ae2ffffff ; moving imm to reg
mov rdx, rbx; 0xfdc1767ae2ffffff to rdx
mulx rbx, r13, rcx; x389, x388<- x366 * 0xfdc1767ae2ffffff
setc dl; spill CF x288 to reg (rdx)
mov [ rsp + 0x4c0 ], rbx; spilling x389 to mem
movzx rbx, byte [ rsp + 0x438 ]; load byte memx371 to register64
clc;
mov byte [ rsp + 0x4c8 ], r8b; spilling byte x331 to mem
mov r8, -0x1 ; moving imm to reg
adcx rbx, r8; loading flag
adcx r12, r11
setc bl; spill CF x373 to reg (rbx)
movzx r11, byte [ rsp + 0x428 ]; load byte memx399 to register64
clc;
adcx r11, r8; loading flag
adcx r13, [ rsp + 0x408 ]
setc r11b; spill CF x401 to reg (r11)
movzx r8, byte [ rsp + 0x430 ]; load byte memx414 to register64
clc;
mov byte [ rsp + 0x4d0 ], bl; spilling byte x373 to mem
mov rbx, -0x1 ; moving imm to reg
adcx r8, rbx; loading flag
adcx r12, r13
seto r8b; spill OF x358 to reg (r8)
movzx r13, byte [ rsp + 0x450 ]; load byte memx456 to register64
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
adox r13, rbx; loading flag
adox r12, [ rsp + 0x30 ]
mov r13, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rdi; x453, swapping with x288, which is currently in rdx
mov byte [ rsp + 0x4d8 ], r11b; spilling byte x401 to mem
mulx rbx, r11, r13; x478, x477<- x453 * 0xffffffffffffffff
setc r13b; spill CF x416 to reg (r13)
mov [ rsp + 0x4e0 ], rbx; spilling x478 to mem
movzx rbx, byte [ rsp + 0x460 ]; load byte memx484 to register64
clc;
mov byte [ rsp + 0x4e8 ], r8b; spilling byte x358 to mem
mov r8, -0x1 ; moving imm to reg
adcx rbx, r8; loading flag
adcx r11, [ rsp + 0x420 ]
setc bl; spill CF x486 to reg (rbx)
movzx r8, byte [ rsp + 0x440 ]; load byte memx499 to register64
clc;
mov byte [ rsp + 0x4f0 ], r13b; spilling byte x416 to mem
mov r13, -0x1 ; moving imm to reg
adcx r8, r13; loading flag
adcx r12, r11
setc r8b; spill CF x501 to reg (r8)
clc;
movzx r15, r15b
adcx r15, r13; loading flag
adcx r12, [ rsp + 0x230 ]
mov r15, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r9; x540, swapping with x453, which is currently in rdx
mulx r11, r13, r15; x567, x566<- x540 * 0xffffffffffffffff
seto r15b; spill OF x458 to reg (r15)
mov [ rsp + 0x4f8 ], r11; spilling x567 to mem
mov r11, -0x2 ; moving imm to reg
inc r11; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, [ rsp + 0x448 ]
seto r11b; spill OF x571 to reg (r11)
mov byte [ rsp + 0x500 ], r8b; spilling byte x501 to mem
mov r8, 0x0 ; moving imm to reg
dec r8; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r14, r14b
adox r14, r8; loading flag
adox r12, r13
movzx r14, byte [ rsp + 0x4b8 ]; x104, copying x103 here, cause x103 is needed in a reg for other than x104, namely all: , x104, size: 1
mov r13, [ rsp + 0x458 ]; load m64 x79 to register64
lea r14, [ r14 + r13 ]; r8/64 + m8
setc r13b; spill CF x543 to reg (r13)
seto r8b; spill OF x586 to reg (r8)
mov byte [ rsp + 0x508 ], r11b; spilling byte x571 to mem
mov r11, r12; x600, copying x585 here, cause x585 is needed in a reg for other than x600, namely all: , x600--x601, x616, size: 2
mov byte [ rsp + 0x510 ], bl; spilling byte x486 to mem
mov rbx, 0xffffffffffffffff ; moving imm to reg
sub r11, rbx
movzx rbx, byte [ rsp + 0x4b0 ]; load byte memx118 to register64
mov [ rsp + 0x518 ], r11; spilling x600 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
mov byte [ rsp + 0x520 ], r8b; spilling byte x586 to mem
movzx r8, byte [ rsp + 0x470 ]; load byte memx77 to register64
adox rbx, r11; loading flag
adox r14, r8
movzx r8, byte [ rsp + 0x480 ]; x147, copying x146 here, cause x146 is needed in a reg for other than x147, namely all: , x147, size: 1
mov rbx, [ rsp + 0x468 ]; load m64 x122 to register64
lea r8, [ r8 + rbx ]; r8/64 + m8
setc bl; spill CF x601 to reg (rbx)
movzx r11, byte [ rsp + 0x488 ]; load byte memx161 to register64
clc;
mov byte [ rsp + 0x528 ], r13b; spilling byte x543 to mem
mov r13, -0x1 ; moving imm to reg
adcx r11, r13; loading flag
adcx r14, r8
seto r11b; spill OF x120 to reg (r11)
movzx r8, byte [ rsp + 0x490 ]; load byte memx203 to register64
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
adox r8, r13; loading flag
adox r14, [ rsp + 0x1d8 ]
mov r8, 0x2341f27177344 ; moving imm to reg
xchg rdx, r8; 0x2341f27177344, swapping with x540, which is currently in rdx
mulx rbp, r13, rbp; x209, x208<- x192 * 0x2341f27177344
seto dl; spill OF x205 to reg (rdx)
mov [ rsp + 0x530 ], rbp; spilling x209 to mem
movzx rbp, byte [ rsp + 0x4a0 ]; load byte memx231 to register64
mov byte [ rsp + 0x538 ], r11b; spilling byte x120 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
adox rbp, r11; loading flag
adox r13, [ rsp + 0x478 ]
seto bpl; spill OF x233 to reg (rbp)
movzx r11, byte [ rsp + 0x498 ]; load byte memx246 to register64
mov byte [ rsp + 0x540 ], dl; spilling byte x205 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r11, rdx; loading flag
adox r14, r13
seto r11b; spill OF x248 to reg (r11)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
movzx rdi, dil
adox rdi, r13; loading flag
adox r14, [ rsp + 0x208 ]
setc dil; spill CF x163 to reg (rdi)
movzx rdx, byte [ rsp + 0x4c8 ]; load byte memx331 to register64
clc;
adcx rdx, r13; loading flag
adcx r14, [ rsp + 0x198 ]
mov rdx, [ r10 + 0x20 ]; arg2[4] to rdx
mov byte [ rsp + 0x548 ], r11b; spilling byte x248 to mem
mulx r13, r11, rax; x344, x343<- x4 * arg2[4]
mov [ rsp + 0x550 ], r13; spilling x344 to mem
setc r13b; spill CF x333 to reg (r13)
mov byte [ rsp + 0x558 ], bpl; spilling byte x233 to mem
movzx rbp, byte [ rsp + 0x4e8 ]; load byte memx358 to register64
clc;
mov byte [ rsp + 0x560 ], dil; spilling byte x163 to mem
mov rdi, -0x1 ; moving imm to reg
adcx rbp, rdi; loading flag
adcx r11, [ rsp + 0x4a8 ]
mov rbp, 0x7bc65c783158aea3 ; moving imm to reg
mov rdx, rcx; x366 to rdx
mulx rcx, rdi, rbp; x387, x386<- x366 * 0x7bc65c783158aea3
seto bpl; spill OF x290 to reg (rbp)
mov [ rsp + 0x568 ], rcx; spilling x387 to mem
movzx rcx, byte [ rsp + 0x4d0 ]; load byte memx373 to register64
mov byte [ rsp + 0x570 ], r13b; spilling byte x333 to mem
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rcx, r13; loading flag
adox r14, r11
seto cl; spill OF x375 to reg (rcx)
movzx r11, byte [ rsp + 0x4d8 ]; load byte memx401 to register64
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
adox r11, r13; loading flag
adox rdi, [ rsp + 0x4c0 ]
setc r11b; spill CF x360 to reg (r11)
movzx r13, byte [ rsp + 0x4f0 ]; load byte memx416 to register64
clc;
mov byte [ rsp + 0x578 ], cl; spilling byte x375 to mem
mov rcx, -0x1 ; moving imm to reg
adcx r13, rcx; loading flag
adcx r14, rdi
setc r13b; spill CF x418 to reg (r13)
clc;
movzx r15, r15b
adcx r15, rcx; loading flag
adcx r14, [ rsp + 0x28 ]
mov r15, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, r9; x453, swapping with x366, which is currently in rdx
mulx rdi, rcx, r15; x476, x475<- x453 * 0xfdc1767ae2ffffff
setc r15b; spill CF x460 to reg (r15)
mov [ rsp + 0x580 ], rdi; spilling x476 to mem
movzx rdi, byte [ rsp + 0x510 ]; load byte memx486 to register64
clc;
mov byte [ rsp + 0x588 ], r13b; spilling byte x418 to mem
mov r13, -0x1 ; moving imm to reg
adcx rdi, r13; loading flag
adcx rcx, [ rsp + 0x4e0 ]
setc dil; spill CF x488 to reg (rdi)
movzx r13, byte [ rsp + 0x500 ]; load byte memx501 to register64
clc;
mov byte [ rsp + 0x590 ], r15b; spilling byte x460 to mem
mov r15, -0x1 ; moving imm to reg
adcx r13, r15; loading flag
adcx r14, rcx
setc r13b; spill CF x503 to reg (r13)
movzx rcx, byte [ rsp + 0x528 ]; load byte memx543 to register64
clc;
adcx rcx, r15; loading flag
adcx r14, [ rsp + 0x228 ]
mov rcx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r8; x540, swapping with x453, which is currently in rdx
mov byte [ rsp + 0x598 ], r13b; spilling byte x503 to mem
mulx r15, r13, rcx; x565, x564<- x540 * 0xffffffffffffffff
seto cl; spill OF x403 to reg (rcx)
mov [ rsp + 0x5a0 ], r15; spilling x565 to mem
movzx r15, byte [ rsp + 0x508 ]; load byte memx571 to register64
mov byte [ rsp + 0x5a8 ], dil; spilling byte x488 to mem
mov rdi, 0x0 ; moving imm to reg
dec rdi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, rdi; loading flag
adox r13, [ rsp + 0x4f8 ]
seto r15b; spill OF x573 to reg (r15)
movzx rdi, byte [ rsp + 0x520 ]; load byte memx586 to register64
mov byte [ rsp + 0x5b0 ], cl; spilling byte x403 to mem
mov rcx, -0x1 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rcx, -0x1 ; moving imm to reg
adox rdi, rcx; loading flag
adox r14, r13
setc dil; spill CF x545 to reg (rdi)
seto r13b; spill OF x588 to reg (r13)
movzx rcx, bl; x601, copying x601 here, cause x601 is needed in a reg for other than x601, namely all: , x602--x603, size: 1
add rcx, -0x1
mov rbx, r14; x602, copying x587 here, cause x587 is needed in a reg for other than x602, namely all: , x617, x602--x603, size: 2
mov rcx, 0xffffffffffffffff ; moving imm to reg
sbb rbx, rcx
movzx rcx, byte [ rsp + 0x560 ]; x164, copying x163 here, cause x163 is needed in a reg for other than x164, namely all: , x164, size: 1
mov [ rsp + 0x5b8 ], rbx; spilling x602 to mem
movzx rbx, byte [ rsp + 0x538 ]; load byte memx120 to register64
lea rcx, [ rcx + rbx ]; r64+m8
movzx rbx, byte [ rsp + 0x540 ]; load byte memx205 to register64
mov byte [ rsp + 0x5c0 ], r13b; spilling byte x588 to mem
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbx, r13; loading flag
adox rcx, [ rsp + 0x1d0 ]
movzx rbx, byte [ rsp + 0x558 ]; x234, copying x233 here, cause x233 is needed in a reg for other than x234, namely all: , x234, size: 1
mov r13, [ rsp + 0x530 ]; load m64 x209 to register64
lea rbx, [ rbx + r13 ]; r8/64 + m8
setc r13b; spill CF x603 to reg (r13)
mov byte [ rsp + 0x5c8 ], r15b; spilling byte x573 to mem
movzx r15, byte [ rsp + 0x548 ]; load byte memx248 to register64
clc;
mov byte [ rsp + 0x5d0 ], dil; spilling byte x545 to mem
mov rdi, -0x1 ; moving imm to reg
adcx r15, rdi; loading flag
adcx rcx, rbx
xchg rdx, rax; x4, swapping with x540, which is currently in rdx
mulx r15, rbx, [ r10 + 0x28 ]; x342, x341<- x4 * arg2[5]
seto dil; spill OF x207 to reg (rdi)
mov [ rsp + 0x5d8 ], r15; spilling x342 to mem
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r15, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, r15; loading flag
adox rcx, [ rsp + 0x200 ]
seto bpl; spill OF x292 to reg (rbp)
movzx r15, byte [ rsp + 0x570 ]; load byte memx333 to register64
mov byte [ rsp + 0x5e0 ], dil; spilling byte x207 to mem
mov rdi, 0x0 ; moving imm to reg
dec rdi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, rdi; loading flag
adox rcx, [ rsp + 0x188 ]
seto r15b; spill OF x335 to reg (r15)
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdi, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, rdi; loading flag
adox rbx, [ rsp + 0x550 ]
mov r11, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, r11; 0x6cfc5fd681c52056, swapping with x4, which is currently in rdx
mov byte [ rsp + 0x5e8 ], r15b; spilling byte x335 to mem
mulx rdi, r15, r9; x385, x384<- x366 * 0x6cfc5fd681c52056
seto dl; spill OF x362 to reg (rdx)
mov [ rsp + 0x5f0 ], rdi; spilling x385 to mem
movzx rdi, byte [ rsp + 0x578 ]; load byte memx375 to register64
mov byte [ rsp + 0x5f8 ], bpl; spilling byte x292 to mem
mov rbp, 0x0 ; moving imm to reg
dec rbp; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rdi, rbp; loading flag
adox rcx, rbx
setc dil; spill CF x250 to reg (rdi)
movzx rbx, byte [ rsp + 0x5b0 ]; load byte memx403 to register64
clc;
adcx rbx, rbp; loading flag
adcx r15, [ rsp + 0x568 ]
setc bl; spill CF x405 to reg (rbx)
movzx rbp, byte [ rsp + 0x588 ]; load byte memx418 to register64
clc;
mov byte [ rsp + 0x600 ], dl; spilling byte x362 to mem
mov rdx, -0x1 ; moving imm to reg
adcx rbp, rdx; loading flag
adcx rcx, r15
mov rbp, 0x7bc65c783158aea3 ; moving imm to reg
mov rdx, r8; x453 to rdx
mulx r8, r15, rbp; x474, x473<- x453 * 0x7bc65c783158aea3
setc bpl; spill CF x420 to reg (rbp)
mov [ rsp + 0x608 ], r8; spilling x474 to mem
movzx r8, byte [ rsp + 0x590 ]; load byte memx460 to register64
clc;
mov byte [ rsp + 0x610 ], bl; spilling byte x405 to mem
mov rbx, -0x1 ; moving imm to reg
adcx r8, rbx; loading flag
adcx rcx, [ rsp + 0x20 ]
setc r8b; spill CF x462 to reg (r8)
movzx rbx, byte [ rsp + 0x5a8 ]; load byte memx488 to register64
clc;
mov byte [ rsp + 0x618 ], bpl; spilling byte x420 to mem
mov rbp, -0x1 ; moving imm to reg
adcx rbx, rbp; loading flag
adcx r15, [ rsp + 0x580 ]
seto bl; spill OF x377 to reg (rbx)
movzx rbp, byte [ rsp + 0x598 ]; load byte memx503 to register64
mov byte [ rsp + 0x620 ], r8b; spilling byte x462 to mem
mov r8, 0x0 ; moving imm to reg
dec r8; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbp, r8; loading flag
adox rcx, r15
setc bpl; spill CF x490 to reg (rbp)
movzx r15, byte [ rsp + 0x5d0 ]; load byte memx545 to register64
clc;
adcx r15, r8; loading flag
adcx rcx, [ rsp + 0x260 ]
mov r15, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, r15; 0xfdc1767ae2ffffff, swapping with x453, which is currently in rdx
mov byte [ rsp + 0x628 ], bpl; spilling byte x490 to mem
mulx r8, rbp, rax; x563, x562<- x540 * 0xfdc1767ae2ffffff
seto dl; spill OF x505 to reg (rdx)
mov [ rsp + 0x630 ], r8; spilling x563 to mem
movzx r8, byte [ rsp + 0x5c8 ]; load byte memx573 to register64
mov byte [ rsp + 0x638 ], bl; spilling byte x377 to mem
mov rbx, -0x1 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbx, -0x1 ; moving imm to reg
adox r8, rbx; loading flag
adox rbp, [ rsp + 0x5a0 ]
seto r8b; spill OF x575 to reg (r8)
movzx rbx, byte [ rsp + 0x5c0 ]; load byte memx588 to register64
mov byte [ rsp + 0x640 ], dl; spilling byte x505 to mem
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
adox rbx, rdx; loading flag
adox rcx, rbp
setc bl; spill CF x547 to reg (rbx)
seto bpl; spill OF x590 to reg (rbp)
movzx rdx, r13b; x603, copying x603 here, cause x603 is needed in a reg for other than x603, namely all: , x604--x605, size: 1
add rdx, -0x1
mov r13, rcx; x604, copying x589 here, cause x589 is needed in a reg for other than x604, namely all: , x618, x604--x605, size: 2
mov byte [ rsp + 0x648 ], r8b; spilling byte x575 to mem
mov r8, 0xffffffffffffffff ; moving imm to reg
sbb r13, r8
movzx r8, dil; x251, copying x250 here, cause x250 is needed in a reg for other than x251, namely all: , x251, size: 1
mov [ rsp + 0x650 ], r13; spilling x604 to mem
movzx r13, byte [ rsp + 0x5e0 ]; load byte memx207 to register64
lea r8, [ r8 + r13 ]; r64+m8
movzx r13, byte [ rsp + 0x5f8 ]; load byte memx292 to register64
mov rdi, -0x1 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdi, -0x1 ; moving imm to reg
adox r13, rdi; loading flag
adox r8, [ rsp + 0x218 ]
mov rdx, r11; x4 to rdx
mulx rdx, r11, [ r10 + 0x30 ]; x340, x339<- x4 * arg2[6]
setc r13b; spill CF x605 to reg (r13)
movzx rdi, byte [ rsp + 0x5e8 ]; load byte memx335 to register64
clc;
mov [ rsp + 0x658 ], rdx; spilling x340 to mem
mov rdx, -0x1 ; moving imm to reg
adcx rdi, rdx; loading flag
adcx r8, [ rsp + 0x190 ]
seto dil; spill OF x294 to reg (rdi)
movzx rdx, byte [ rsp + 0x600 ]; load byte memx362 to register64
mov byte [ rsp + 0x660 ], r13b; spilling byte x605 to mem
mov r13, -0x1 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r13, -0x1 ; moving imm to reg
adox rdx, r13; loading flag
adox r11, [ rsp + 0x5d8 ]
seto dl; spill OF x364 to reg (rdx)
movzx r13, byte [ rsp + 0x638 ]; load byte memx377 to register64
mov byte [ rsp + 0x668 ], dil; spilling byte x294 to mem
mov rdi, 0x0 ; moving imm to reg
dec rdi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r13, rdi; loading flag
adox r8, r11
mov r13, 0x2341f27177344 ; moving imm to reg
xchg rdx, r9; x366, swapping with x364, which is currently in rdx
mulx rdx, r11, r13; x383, x382<- x366 * 0x2341f27177344
seto dil; spill OF x379 to reg (rdi)
movzx r13, byte [ rsp + 0x610 ]; load byte memx405 to register64
mov [ rsp + 0x670 ], rdx; spilling x383 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r13, rdx; loading flag
adox r11, [ rsp + 0x5f0 ]
mov r13, 0x6cfc5fd681c52056 ; moving imm to reg
mov rdx, r13; 0x6cfc5fd681c52056 to rdx
mov byte [ rsp + 0x678 ], dil; spilling byte x379 to mem
mulx r13, rdi, r15; x472, x471<- x453 * 0x6cfc5fd681c52056
setc dl; spill CF x337 to reg (rdx)
mov [ rsp + 0x680 ], r13; spilling x472 to mem
movzx r13, byte [ rsp + 0x618 ]; load byte memx420 to register64
clc;
mov byte [ rsp + 0x688 ], r9b; spilling byte x364 to mem
mov r9, -0x1 ; moving imm to reg
adcx r13, r9; loading flag
adcx r8, r11
seto r13b; spill OF x407 to reg (r13)
movzx r11, byte [ rsp + 0x620 ]; load byte memx462 to register64
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
adox r11, r9; loading flag
adox r8, [ rsp + 0x18 ]
setc r11b; spill CF x422 to reg (r11)
movzx r9, byte [ rsp + 0x628 ]; load byte memx490 to register64
clc;
mov byte [ rsp + 0x690 ], r13b; spilling byte x407 to mem
mov r13, -0x1 ; moving imm to reg
adcx r9, r13; loading flag
adcx rdi, [ rsp + 0x608 ]
seto r9b; spill OF x464 to reg (r9)
movzx r13, byte [ rsp + 0x640 ]; load byte memx505 to register64
mov byte [ rsp + 0x698 ], r11b; spilling byte x422 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
adox r13, r11; loading flag
adox r8, rdi
setc r13b; spill CF x492 to reg (r13)
clc;
movzx rbx, bl
adcx rbx, r11; loading flag
adcx r8, [ rsp + 0x258 ]
mov rbx, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, rax; x540, swapping with x337, which is currently in rdx
mulx rdi, r11, rbx; x561, x560<- x540 * 0x7bc65c783158aea3
seto bl; spill OF x507 to reg (rbx)
mov [ rsp + 0x6a0 ], rdi; spilling x561 to mem
movzx rdi, byte [ rsp + 0x648 ]; load byte memx575 to register64
mov byte [ rsp + 0x6a8 ], r13b; spilling byte x492 to mem
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rdi, r13; loading flag
adox r11, [ rsp + 0x630 ]
setc dil; spill CF x549 to reg (rdi)
clc;
movzx rbp, bpl
adcx rbp, r13; loading flag
adcx r8, r11
setc bpl; spill CF x592 to reg (rbp)
seto r11b; spill OF x577 to reg (r11)
movzx r13, byte [ rsp + 0x660 ]; x605, copying x605 here, cause x605 is needed in a reg for other than x605, namely all: , x606--x607, size: 1
add r13, -0x1
mov r13, r8; x606, copying x591 here, cause x591 is needed in a reg for other than x606, namely all: , x619, x606--x607, size: 2
mov byte [ rsp + 0x6b0 ], dil; spilling byte x549 to mem
mov rdi, 0xfdc1767ae2ffffff ; moving imm to reg
sbb r13, rdi
movzx rdi, al; x338, copying x337 here, cause x337 is needed in a reg for other than x338, namely all: , x338, size: 1
mov [ rsp + 0x6b8 ], r13; spilling x606 to mem
movzx r13, byte [ rsp + 0x668 ]; load byte memx294 to register64
lea rdi, [ rdi + r13 ]; r64+m8
movzx r13, byte [ rsp + 0x688 ]; x365, copying x364 here, cause x364 is needed in a reg for other than x365, namely all: , x365, size: 1
mov rax, [ rsp + 0x658 ]; load m64 x340 to register64
lea r13, [ r13 + rax ]; r8/64 + m8
movzx rax, byte [ rsp + 0x678 ]; load byte memx379 to register64
mov byte [ rsp + 0x6c0 ], bpl; spilling byte x592 to mem
mov rbp, -0x1 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
adox rax, rbp; loading flag
adox rdi, r13
movzx rax, byte [ rsp + 0x690 ]; x408, copying x407 here, cause x407 is needed in a reg for other than x408, namely all: , x408, size: 1
mov r13, [ rsp + 0x670 ]; load m64 x383 to register64
lea rax, [ rax + r13 ]; r8/64 + m8
setc r13b; spill CF x607 to reg (r13)
movzx rbp, byte [ rsp + 0x698 ]; load byte memx422 to register64
clc;
mov byte [ rsp + 0x6c8 ], r11b; spilling byte x577 to mem
mov r11, -0x1 ; moving imm to reg
adcx rbp, r11; loading flag
adcx rdi, rax
setc bpl; spill CF x424 to reg (rbp)
clc;
movzx r9, r9b
adcx r9, r11; loading flag
adcx rdi, [ rsp + 0x10 ]
mov r9, 0x2341f27177344 ; moving imm to reg
xchg rdx, r15; x453, swapping with x540, which is currently in rdx
mulx rdx, rax, r9; x470, x469<- x453 * 0x2341f27177344
setc r11b; spill CF x466 to reg (r11)
movzx r9, byte [ rsp + 0x6a8 ]; load byte memx492 to register64
clc;
mov [ rsp + 0x6d0 ], rdx; spilling x470 to mem
mov rdx, -0x1 ; moving imm to reg
adcx r9, rdx; loading flag
adcx rax, [ rsp + 0x680 ]
setc r9b; spill CF x494 to reg (r9)
clc;
movzx rbx, bl
adcx rbx, rdx; loading flag
adcx rdi, rax
mov rbx, 0x6cfc5fd681c52056 ; moving imm to reg
mov rdx, rbx; 0x6cfc5fd681c52056 to rdx
mulx rbx, rax, r15; x559, x558<- x540 * 0x6cfc5fd681c52056
setc dl; spill CF x509 to reg (rdx)
mov [ rsp + 0x6d8 ], rbx; spilling x559 to mem
movzx rbx, byte [ rsp + 0x6b0 ]; load byte memx549 to register64
clc;
mov byte [ rsp + 0x6e0 ], r9b; spilling byte x494 to mem
mov r9, -0x1 ; moving imm to reg
adcx rbx, r9; loading flag
adcx rdi, [ rsp + 0x248 ]
setc bl; spill CF x551 to reg (rbx)
movzx r9, byte [ rsp + 0x6c8 ]; load byte memx577 to register64
clc;
mov [ rsp + 0x6e8 ], rsi; spilling arg1 to mem
mov rsi, -0x1 ; moving imm to reg
adcx r9, rsi; loading flag
adcx rax, [ rsp + 0x6a0 ]
setc r9b; spill CF x579 to reg (r9)
movzx rsi, byte [ rsp + 0x6c0 ]; load byte memx592 to register64
clc;
mov byte [ rsp + 0x6f0 ], bl; spilling byte x551 to mem
mov rbx, -0x1 ; moving imm to reg
adcx rsi, rbx; loading flag
adcx rdi, rax
setc sil; spill CF x594 to reg (rsi)
seto al; spill OF x381 to reg (rax)
movzx rbx, r13b; x607, copying x607 here, cause x607 is needed in a reg for other than x607, namely all: , x608--x609, size: 1
add rbx, -0x1
mov rbx, rdi; x608, copying x593 here, cause x593 is needed in a reg for other than x608, namely all: , x608--x609, x620, size: 2
mov r13, 0x7bc65c783158aea3 ; moving imm to reg
sbb rbx, r13
movzx r13, bpl; x425, copying x424 here, cause x424 is needed in a reg for other than x425, namely all: , x425, size: 1
movzx rax, al
lea r13, [ r13 + rax ]
mov rax, -0x1 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, rbp; loading flag
adox r13, [ rsp + 0x8 ]
movzx r11, byte [ rsp + 0x6e0 ]; x495, copying x494 here, cause x494 is needed in a reg for other than x495, namely all: , x495, size: 1
mov rax, [ rsp + 0x6d0 ]; load m64 x470 to register64
lea r11, [ r11 + rax ]; r8/64 + m8
mov rax, 0x2341f27177344 ; moving imm to reg
xchg rdx, r15; x540, swapping with x509, which is currently in rdx
mulx rdx, rbp, rax; x557, x556<- x540 * 0x2341f27177344
seto al; spill OF x468 to reg (rax)
mov [ rsp + 0x6f8 ], rbx; spilling x608 to mem
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r15, r15b
adox r15, rbx; loading flag
adox r13, r11
seto r15b; spill OF x511 to reg (r15)
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r11, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, r11; loading flag
adox rbp, [ rsp + 0x6d8 ]
setc r9b; spill CF x609 to reg (r9)
movzx rbx, byte [ rsp + 0x6f0 ]; load byte memx551 to register64
clc;
adcx rbx, r11; loading flag
adcx r13, [ rsp + 0x240 ]
setc bl; spill CF x553 to reg (rbx)
clc;
movzx rsi, sil
adcx rsi, r11; loading flag
adcx r13, rbp
movzx rsi, r15b; x512, copying x511 here, cause x511 is needed in a reg for other than x512, namely all: , x512, size: 1
movzx rax, al
lea rsi, [ rsi + rax ]
setc al; spill CF x596 to reg (rax)
seto r15b; spill OF x581 to reg (r15)
movzx rbp, r9b; x609, copying x609 here, cause x609 is needed in a reg for other than x609, namely all: , x610--x611, size: 1
add rbp, -0x1
mov rbp, r13; x610, copying x595 here, cause x595 is needed in a reg for other than x610, namely all: , x610--x611, x621, size: 2
mov r9, 0x6cfc5fd681c52056 ; moving imm to reg
sbb rbp, r9
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r11, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, r11; loading flag
adox rsi, [ rsp + 0x250 ]
movzx rbx, r15b; x582, copying x581 here, cause x581 is needed in a reg for other than x582, namely all: , x582, size: 1
lea rbx, [ rbx + rdx ]
seto dl; spill OF x555 to reg (rdx)
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
movzx rax, al
adox rax, r15; loading flag
adox rsi, rbx
seto al; spill OF x598 to reg (rax)
mov rbx, rsi; x612, copying x597 here, cause x597 is needed in a reg for other than x612, namely all: , x622, x612--x613, size: 2
mov r11, 0x2341f27177344 ; moving imm to reg
sbb rbx, r11
movzx r15, al; x599, copying x598 here, cause x598 is needed in a reg for other than x599, namely all: , x599, size: 1
movzx rdx, dl
lea r15, [ r15 + rdx ]
sbb r15, 0x00000000
cmovc rbx, rsi; if CF, x622<- x597 (nzVar)
mov r15, [ rsp + 0x5b8 ]; x617, copying x602 here, cause x602 is needed in a reg for other than x617, namely all: , x617, size: 1
cmovc r15, r14; if CF, x617<- x587 (nzVar)
cmovc rbp, r13; if CF, x621<- x595 (nzVar)
mov r14, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r14 + 0x28 ], rbp; out1[5] = x621
mov [ r14 + 0x8 ], r15; out1[1] = x617
mov r13, [ rsp + 0x6f8 ]; x620, copying x608 here, cause x608 is needed in a reg for other than x620, namely all: , x620, size: 1
cmovc r13, rdi; if CF, x620<- x593 (nzVar)
mov rdi, [ rsp + 0x6b8 ]; x619, copying x606 here, cause x606 is needed in a reg for other than x619, namely all: , x619, size: 1
cmovc rdi, r8; if CF, x619<- x591 (nzVar)
mov r8, [ rsp + 0x650 ]; x618, copying x604 here, cause x604 is needed in a reg for other than x618, namely all: , x618, size: 1
cmovc r8, rcx; if CF, x618<- x589 (nzVar)
mov rcx, [ rsp + 0x518 ]; x616, copying x600 here, cause x600 is needed in a reg for other than x616, namely all: , x616, size: 1
cmovc rcx, r12; if CF, x616<- x585 (nzVar)
mov [ r14 + 0x0 ], rcx; out1[0] = x616
mov [ r14 + 0x30 ], rbx; out1[6] = x622
mov [ r14 + 0x10 ], r8; out1[2] = x618
mov [ r14 + 0x20 ], r13; out1[4] = x620
mov [ r14 + 0x18 ], rdi; out1[3] = x619
mov rbx, [ rsp + 0x700 ]; restoring from stack
mov rbp, [ rsp + 0x708 ]; restoring from stack
mov r12, [ rsp + 0x710 ]; restoring from stack
mov r13, [ rsp + 0x718 ]; restoring from stack
mov r14, [ rsp + 0x720 ]; restoring from stack
mov r15, [ rsp + 0x728 ]; restoring from stack
add rsp, 0x730 
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; clocked at 2200 MHz
; first cyclecount 309.13, best 308.94, lastGood 324.35714285714283
; seed 3664281231704237 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 54821 ms / 500 runs=> 109.642ms/run
; Time spent for assembling and measureing (initial batch_size=28, initial num_batches=101): 1156 ms
; Ratio (time for assembling + measure)/(total runtime for 500runs): 0.021086809799164552
; number reverted permutation/ tried permutation: 146 / 248 =58.871%
; number reverted decision/ tried decision: 140 / 253 =55.336%