SECTION .text
	GLOBAL square_p434
square_p434:
sub rsp, 0x668 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x638 ], rbx; saving to stack
mov [ rsp + 0x640 ], rbp; saving to stack
mov [ rsp + 0x648 ], r12; saving to stack
mov [ rsp + 0x650 ], r13; saving to stack
mov [ rsp + 0x658 ], r14; saving to stack
mov [ rsp + 0x660 ], r15; saving to stack
mov rax, [ rsi + 0x8 ]; load m64 x1 to register64
mov r10, [ rsi + 0x0 ]; load m64 x7 to register64
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mulx r11, rbx, rax; x81, x80<- x1 * arg1[5]
mov rdx, rax; x1 to rdx
mulx rax, rbp, [ rsi + 0x8 ]; x89, x88<- x1 * arg1[1]
mulx r12, r13, [ rsi + 0x0 ]; x91, x90<- x1 * arg1[0]
mulx r14, r15, [ rsi + 0x18 ]; x85, x84<- x1 * arg1[3]
mulx rcx, r8, [ rsi + 0x10 ]; x87, x86<- x1 * arg1[2]
test al, al
adox rbp, r12
mov r9, rdx; preserving value of x1 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r12, rdi, r10; x21, x20<- x7 * arg1[0]
mov rdx, r9; x1 to rdx
mov [ rsp + 0x8 ], rbp; spilling x92 to mem
mulx r9, rbp, [ rsi + 0x20 ]; x83, x82<- x1 * arg1[4]
mov [ rsp + 0x10 ], r13; spilling x90 to mem
mulx rdx, r13, [ rsi + 0x30 ]; x79, x78<- x1 * arg1[6]
adox r8, rax
adox r15, rcx
adox rbp, r14
mov rax, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, rdi; x20, swapping with x79, which is currently in rdx
mulx r14, rcx, rax; x40, x39<- x20 * 0x7bc65c783158aea3
mov rax, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x18 ], rbp; spilling x98 to mem
mov [ rsp + 0x20 ], r15; spilling x96 to mem
mulx rbp, r15, rax; x48, x47<- x20 * 0xffffffffffffffff
mov [ rsp + 0x28 ], r8; spilling x94 to mem
mov [ rsp + 0x30 ], r12; spilling x21 to mem
mulx r8, r12, rax; x44, x43<- x20 * 0xffffffffffffffff
mov [ rsp + 0x38 ], r15; spilling x47 to mem
mov [ rsp + 0x40 ], r14; spilling x40 to mem
mulx r15, r14, rax; x46, x45<- x20 * 0xffffffffffffffff
mov rax, [ rsi + 0x18 ]; load m64 x3 to register64
adox rbx, r9
mov r9, 0xfdc1767ae2ffffff ; moving imm to reg
mov [ rsp + 0x48 ], rbx; spilling x100 to mem
mov [ rsp + 0x50 ], rdi; spilling x79 to mem
mulx rbx, rdi, r9; x42, x41<- x20 * 0xfdc1767ae2ffffff
adcx r14, rbp
adox r13, r11
adcx r12, r15
adcx rdi, r8
xchg rdx, rax; x3, swapping with x20, which is currently in rdx
mulx r11, rbp, [ rsi + 0x0 ]; x265, x264<- x3 * arg1[0]
mov r8, 0x2341f27177344 ; moving imm to reg
xchg rdx, r8; 0x2341f27177344, swapping with x3, which is currently in rdx
mulx r15, r9, rax; x36, x35<- x20 * 0x2341f27177344
mov [ rsp + 0x58 ], rbp; spilling x264 to mem
mov rbp, rdx; preserving value of 0x2341f27177344 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x60 ], r13; spilling x102 to mem
mov [ rsp + 0x68 ], rdi; spilling x53 to mem
mulx r13, rdi, r8; x263, x262<- x3 * arg1[1]
mov rdx, 0x6cfc5fd681c52056 ; moving imm to reg
mov [ rsp + 0x70 ], r12; spilling x51 to mem
mulx rbp, r12, rax; x38, x37<- x20 * 0x6cfc5fd681c52056
adcx rcx, rbx
mov rbx, [ rsp + 0x50 ]; x104, copying x79 here, cause x79 is needed in a reg for other than x104, namely all: , x104, size: 1
mov rdx, 0x0 ; moving imm to reg
adox rbx, rdx
mov rdx, [ rsp + 0x40 ]; x57, copying x40 here, cause x40 is needed in a reg for other than x57, namely all: , x57--x58, size: 1
adcx rdx, r12
xchg rdx, r8; x3, swapping with x57, which is currently in rdx
mov [ rsp + 0x78 ], rbx; spilling x104 to mem
mulx r12, rbx, [ rsi + 0x10 ]; x261, x260<- x3 * arg1[2]
adcx r9, rbp
mov [ rsp + 0x80 ], r9; spilling x59 to mem
mulx rbp, r9, [ rsi + 0x18 ]; x259, x258<- x3 * arg1[3]
adc r15, 0x0
mov [ rsp + 0x88 ], r15; spilling x61 to mem
xor r15, r15
adox rdi, r11
adcx rax, [ rsp + 0x38 ]
mov rax, rdx; preserving value of x3 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r11, r15, r10; x19, x18<- x7 * arg1[1]
setc dl; spill CF x63 to reg (rdx)
clc;
adcx r15, [ rsp + 0x30 ]
adox rbx, r13
xchg rdx, rax; x3, swapping with x63, which is currently in rdx
mov [ rsp + 0x90 ], rbx; spilling x268 to mem
mulx r13, rbx, [ rsi + 0x20 ]; x257, x256<- x3 * arg1[4]
mov [ rsp + 0x98 ], rdi; spilling x266 to mem
mov rdi, [ rsi + 0x10 ]; load m64 x2 to register64
mov [ rsp + 0xa0 ], r8; spilling x57 to mem
setc r8b; spill CF x23 to reg (r8)
clc;
mov [ rsp + 0xa8 ], rcx; spilling x55 to mem
mov rcx, -0x1 ; moving imm to reg
movzx rax, al
adcx rax, rcx; loading flag
adcx r15, r14
mulx r14, rax, [ rsi + 0x30 ]; x253, x252<- x3 * arg1[6]
mulx rdx, rcx, [ rsi + 0x28 ]; x255, x254<- x3 * arg1[5]
mov [ rsp + 0xb0 ], r11; spilling x19 to mem
mov r11, rdx; preserving value of x255 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov byte [ rsp + 0xb8 ], r8b; spilling byte x23 to mem
mov [ rsp + 0xc0 ], r14; spilling x253 to mem
mulx r8, r14, rdi; x178, x177<- x2 * arg1[0]
adox r9, r12
adox rbx, rbp
adox rcx, r13
adox rax, r11
setc dl; spill CF x65 to reg (rdx)
clc;
adcx r15, [ rsp + 0x10 ]
mov r12, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r15; x105, swapping with x65, which is currently in rdx
mulx rbp, r13, r12; x132, x131<- x105 * 0xffffffffffffffff
mov r11, rdx; preserving value of x105 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0xc8 ], rax; spilling x276 to mem
mulx r12, rax, r10; x17, x16<- x7 * arg1[2]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0xd0 ], rcx; spilling x274 to mem
mov [ rsp + 0xd8 ], rbx; spilling x272 to mem
mulx rcx, rbx, r11; x134, x133<- x105 * 0xffffffffffffffff
mov rdx, [ rsp + 0xc0 ]; x278, copying x253 here, cause x253 is needed in a reg for other than x278, namely all: , x278, size: 1
mov [ rsp + 0xe0 ], r9; spilling x270 to mem
mov r9, 0x0 ; moving imm to reg
adox rdx, r9
movzx r9, byte [ rsp + 0xb8 ]; load byte memx23 to register64
mov [ rsp + 0xe8 ], rdx; spilling x278 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r9, rdx; loading flag
adox rax, [ rsp + 0xb0 ]
seto r9b; spill OF x25 to reg (r9)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rbx, r11
seto bl; spill OF x149 to reg (rbx)
dec rdx; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r15, r15b
adox r15, rdx; loading flag
adox rax, [ rsp + 0x70 ]
mov r15, [ rsp + 0x8 ]; x107, copying x92 here, cause x92 is needed in a reg for other than x107, namely all: , x107--x108, size: 1
adcx r15, rax
setc al; spill CF x108 to reg (rax)
clc;
adcx r13, rcx
setc cl; spill CF x136 to reg (rcx)
clc;
movzx rbx, bl
adcx rbx, rdx; loading flag
adcx r15, r13
setc bl; spill CF x151 to reg (rbx)
clc;
adcx r14, r15
mov r13, 0xffffffffffffffff ; moving imm to reg
mov rdx, r14; x192 to rdx
mulx r14, r15, r13; x221, x220<- x192 * 0xffffffffffffffff
mov r13, 0x6cfc5fd681c52056 ; moving imm to reg
mov byte [ rsp + 0xf0 ], bl; spilling byte x151 to mem
mov byte [ rsp + 0xf8 ], al; spilling byte x108 to mem
mulx rbx, rax, r13; x211, x210<- x192 * 0x6cfc5fd681c52056
mov r13, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x100 ], rbp; spilling x132 to mem
mov byte [ rsp + 0x108 ], cl; spilling byte x136 to mem
mulx rbp, rcx, r13; x219, x218<- x192 * 0xffffffffffffffff
mov r13, rdx; preserving value of x192 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x110 ], rbx; spilling x211 to mem
mov [ rsp + 0x118 ], rax; spilling x210 to mem
mulx rbx, rax, rdi; x176, x175<- x2 * arg1[1]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x120 ], rbx; spilling x176 to mem
mov [ rsp + 0x128 ], r12; spilling x17 to mem
mulx rbx, r12, r13; x217, x216<- x192 * 0xffffffffffffffff
mov rdx, 0xfdc1767ae2ffffff ; moving imm to reg
mov [ rsp + 0x130 ], rbx; spilling x217 to mem
mov byte [ rsp + 0x138 ], r9b; spilling byte x25 to mem
mulx rbx, r9, r13; x215, x214<- x192 * 0xfdc1767ae2ffffff
seto dl; spill OF x67 to reg (rdx)
mov [ rsp + 0x140 ], rbx; spilling x215 to mem
mov rbx, -0x2 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rcx, r14
setc r14b; spill CF x193 to reg (r14)
clc;
adcx rax, r8
mov r8, 0x2341f27177344 ; moving imm to reg
xchg rdx, r13; x192, swapping with x67, which is currently in rdx
mov [ rsp + 0x148 ], rcx; spilling x222 to mem
mulx rbx, rcx, r8; x209, x208<- x192 * 0x2341f27177344
adox r12, rbp
seto bpl; spill OF x225 to reg (rbp)
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, rdx
xchg rdx, r10; x7, swapping with x192, which is currently in rdx
mulx r15, r8, [ rsi + 0x18 ]; x15, x14<- x7 * arg1[3]
mov [ rsp + 0x150 ], r12; spilling x224 to mem
setc r12b; spill CF x180 to reg (r12)
mov [ rsp + 0x158 ], rbx; spilling x209 to mem
movzx rbx, byte [ rsp + 0x138 ]; load byte memx25 to register64
clc;
mov [ rsp + 0x160 ], r15; spilling x15 to mem
mov r15, -0x1 ; moving imm to reg
adcx rbx, r15; loading flag
adcx r8, [ rsp + 0x128 ]
setc bl; spill CF x27 to reg (rbx)
clc;
movzx rbp, bpl
adcx rbp, r15; loading flag
adcx r9, [ rsp + 0x130 ]
seto bpl; spill OF x236 to reg (rbp)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, r15; loading flag
adox r8, [ rsp + 0x68 ]
mov r13, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, r13; 0x7bc65c783158aea3, swapping with x7, which is currently in rdx
mulx r10, r15, r10; x213, x212<- x192 * 0x7bc65c783158aea3
mov rdx, [ rsp + 0x140 ]; x228, copying x215 here, cause x215 is needed in a reg for other than x228, namely all: , x228--x229, size: 1
adcx rdx, r15
mov r15, [ rsp + 0x118 ]; x230, copying x210 here, cause x210 is needed in a reg for other than x230, namely all: , x230--x231, size: 1
adcx r15, r10
mov r10, [ rsp + 0x110 ]; x232, copying x211 here, cause x211 is needed in a reg for other than x232, namely all: , x232--x233, size: 1
adcx r10, rcx
mov rcx, rdx; preserving value of x228 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x168 ], r10; spilling x232 to mem
mov [ rsp + 0x170 ], r15; spilling x230 to mem
mulx r10, r15, r13; x13, x12<- x7 * arg1[4]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x178 ], rcx; spilling x228 to mem
mov [ rsp + 0x180 ], r9; spilling x226 to mem
mulx rcx, r9, r11; x130, x129<- x105 * 0xffffffffffffffff
xchg rdx, rdi; x2, swapping with 0xffffffffffffffff, which is currently in rdx
mov byte [ rsp + 0x188 ], r12b; spilling byte x180 to mem
mulx rdi, r12, [ rsi + 0x18 ]; x172, x171<- x2 * arg1[3]
mov [ rsp + 0x190 ], rdi; spilling x172 to mem
seto dil; spill OF x69 to reg (rdi)
mov [ rsp + 0x198 ], r12; spilling x171 to mem
movzx r12, byte [ rsp + 0x108 ]; load byte memx136 to register64
mov [ rsp + 0x1a0 ], rcx; spilling x130 to mem
mov rcx, -0x1 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rcx, -0x1 ; moving imm to reg
adox r12, rcx; loading flag
adox r9, [ rsp + 0x100 ]
seto r12b; spill OF x138 to reg (r12)
movzx rcx, byte [ rsp + 0xf8 ]; load byte memx108 to register64
mov byte [ rsp + 0x1a8 ], dil; spilling byte x69 to mem
mov rdi, -0x1 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdi, -0x1 ; moving imm to reg
adox rcx, rdi; loading flag
adox r8, [ rsp + 0x28 ]
setc cl; spill CF x233 to reg (rcx)
movzx rdi, byte [ rsp + 0xf0 ]; load byte memx151 to register64
clc;
mov byte [ rsp + 0x1b0 ], r12b; spilling byte x138 to mem
mov r12, -0x1 ; moving imm to reg
adcx rdi, r12; loading flag
adcx r8, r9
setc dil; spill CF x153 to reg (rdi)
clc;
movzx r14, r14b
adcx r14, r12; loading flag
adcx r8, rax
setc r14b; spill CF x195 to reg (r14)
clc;
movzx rbp, bpl
adcx rbp, r12; loading flag
adcx r8, [ rsp + 0x148 ]
mov rax, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, rax; 0xfdc1767ae2ffffff, swapping with x2, which is currently in rdx
mulx rbp, r9, r11; x128, x127<- x105 * 0xfdc1767ae2ffffff
mov r12, rdx; preserving value of 0xfdc1767ae2ffffff into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x1b8 ], r8; spilling x237 to mem
mov byte [ rsp + 0x1c0 ], r14b; spilling byte x195 to mem
mulx r8, r14, r13; x11, x10<- x7 * arg1[5]
seto dl; spill OF x110 to reg (rdx)
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbx, bl
adox rbx, r12; loading flag
adox r15, [ rsp + 0x160 ]
movzx rbx, cl; x234, copying x233 here, cause x233 is needed in a reg for other than x234, namely all: , x234, size: 1
mov r12, [ rsp + 0x158 ]; load m64 x209 to register64
lea rbx, [ rbx + r12 ]; r8/64 + m8
adox r14, r10
mov r12b, dl; preserving value of x110 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mulx r13, rcx, r13; x9, x8<- x7 * arg1[6]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x1c8 ], rbx; spilling x234 to mem
mulx r10, rbx, rax; x174, x173<- x2 * arg1[2]
seto dl; spill OF x31 to reg (rdx)
mov [ rsp + 0x1d0 ], r13; spilling x9 to mem
movzx r13, byte [ rsp + 0x1a8 ]; load byte memx69 to register64
mov [ rsp + 0x1d8 ], rcx; spilling x8 to mem
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r13, rcx; loading flag
adox r15, [ rsp + 0xa8 ]
setc r13b; spill CF x238 to reg (r13)
movzx rcx, byte [ rsp + 0x1b0 ]; load byte memx138 to register64
clc;
mov [ rsp + 0x1e0 ], r8; spilling x11 to mem
mov r8, -0x1 ; moving imm to reg
adcx rcx, r8; loading flag
adcx r9, [ rsp + 0x1a0 ]
mov rcx, [ rsp + 0xa0 ]; x72, copying x57 here, cause x57 is needed in a reg for other than x72, namely all: , x72--x73, size: 1
adox rcx, r14
seto r14b; spill OF x73 to reg (r14)
movzx r8, byte [ rsp + 0x188 ]; load byte memx180 to register64
mov byte [ rsp + 0x1e8 ], r13b; spilling byte x238 to mem
mov r13, -0x1 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r13, -0x1 ; moving imm to reg
adox r8, r13; loading flag
adox rbx, [ rsp + 0x120 ]
mov r8, [ rsp + 0x198 ]; x183, copying x171 here, cause x171 is needed in a reg for other than x183, namely all: , x183--x184, size: 1
adox r8, r10
seto r10b; spill OF x184 to reg (r10)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, r13; loading flag
adox r15, [ rsp + 0x20 ]
mov r12, [ rsp + 0x18 ]; x113, copying x98 here, cause x98 is needed in a reg for other than x113, namely all: , x113--x114, size: 1
adox r12, rcx
mov rcx, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, r11; x105, swapping with x31, which is currently in rdx
mov byte [ rsp + 0x1f0 ], r10b; spilling byte x184 to mem
mulx r13, r10, rcx; x124, x123<- x105 * 0x6cfc5fd681c52056
mov rcx, 0x7bc65c783158aea3 ; moving imm to reg
mov [ rsp + 0x1f8 ], r13; spilling x124 to mem
mov byte [ rsp + 0x200 ], r14b; spilling byte x73 to mem
mulx r13, r14, rcx; x126, x125<- x105 * 0x7bc65c783158aea3
setc cl; spill CF x140 to reg (rcx)
clc;
mov [ rsp + 0x208 ], r8; spilling x183 to mem
mov r8, -0x1 ; moving imm to reg
movzx rdi, dil
adcx rdi, r8; loading flag
adcx r15, r9
seto dil; spill OF x114 to reg (rdi)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r9; loading flag
adox rbp, r14
adox r10, r13
adcx rbp, r12
setc cl; spill CF x157 to reg (rcx)
movzx r12, byte [ rsp + 0x1c0 ]; load byte memx195 to register64
clc;
adcx r12, r9; loading flag
adcx r15, rbx
mov r12, [ rsp + 0x1d8 ]; load m64 x8 to register64
seto bl; spill OF x144 to reg (rbx)
inc r9; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov r8, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, r8; loading flag
adox r12, [ rsp + 0x1e0 ]
mov r11, [ rsp + 0x208 ]; x198, copying x183 here, cause x183 is needed in a reg for other than x198, namely all: , x198--x199, size: 1
adcx r11, rbp
setc r13b; spill CF x199 to reg (r13)
movzx r14, byte [ rsp + 0x200 ]; load byte memx73 to register64
clc;
adcx r14, r8; loading flag
adcx r12, [ rsp + 0x80 ]
setc r14b; spill CF x75 to reg (r14)
movzx rbp, byte [ rsp + 0x1e8 ]; load byte memx238 to register64
clc;
adcx rbp, r8; loading flag
adcx r15, [ rsp + 0x150 ]
mov rbp, [ rsp + 0x180 ]; x241, copying x226 here, cause x226 is needed in a reg for other than x241, namely all: , x241--x242, size: 1
adcx rbp, r11
mov r11, [ rsp + 0x1d0 ]; x34, copying x9 here, cause x9 is needed in a reg for other than x34, namely all: , x34, size: 1
adox r11, r9
mov r9, rdx; preserving value of x105 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x210 ], rbp; spilling x241 to mem
mulx r8, rbp, rax; x168, x167<- x2 * arg1[5]
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, rdx; loading flag
adox r11, [ rsp + 0x88 ]
setc r14b; spill CF x242 to reg (r14)
clc;
movzx rdi, dil
adcx rdi, rdx; loading flag
adcx r12, [ rsp + 0x48 ]
mov rdi, [ rsp + 0x60 ]; x117, copying x102 here, cause x102 is needed in a reg for other than x117, namely all: , x117--x118, size: 1
adcx rdi, r11
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x218 ], r15; spilling x239 to mem
mulx r11, r15, rax; x170, x169<- x2 * arg1[4]
mov rdx, rax; x2 to rdx
mulx rdx, rax, [ rsi + 0x30 ]; x166, x165<- x2 * arg1[6]
mov [ rsp + 0x220 ], rdx; spilling x166 to mem
mov rdx, 0x2341f27177344 ; moving imm to reg
mov byte [ rsp + 0x228 ], r14b; spilling byte x242 to mem
mulx r9, r14, r9; x122, x121<- x105 * 0x2341f27177344
setc dl; spill CF x118 to reg (rdx)
clc;
mov [ rsp + 0x230 ], r9; spilling x122 to mem
mov r9, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, r9; loading flag
adcx r12, r10
setc r10b; spill CF x159 to reg (r10)
clc;
movzx rbx, bl
adcx rbx, r9; loading flag
adcx r14, [ rsp + 0x1f8 ]
seto bl; spill OF x77 to reg (rbx)
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rcx, -0x1 ; moving imm to reg
movzx r10, r10b
adox r10, rcx; loading flag
adox rdi, r14
seto r10b; spill OF x161 to reg (r10)
movzx r14, byte [ rsp + 0x1f0 ]; load byte memx184 to register64
inc rcx; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov r9, -0x1 ; moving imm to reg
adox r14, r9; loading flag
adox r15, [ rsp + 0x190 ]
adox rbp, r11
setc r14b; spill CF x146 to reg (r14)
clc;
movzx r13, r13b
adcx r13, r9; loading flag
adcx r12, r15
adcx rbp, rdi
mov r13, [ rsi + 0x28 ]; load m64 x5 to register64
adox rax, r8
seto r8b; spill OF x190 to reg (r8)
movzx r11, byte [ rsp + 0x228 ]; load byte memx242 to register64
dec rcx; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
adox r11, rcx; loading flag
adox r12, [ rsp + 0x178 ]
movzx r9, r14b; x147, copying x146 here, cause x146 is needed in a reg for other than x147, namely all: , x147, size: 1
mov r11, [ rsp + 0x230 ]; load m64 x122 to register64
lea r9, [ r9 + r11 ]; r8/64 + m8
movzx r11, bl; x119, copying x77 here, cause x77 is needed in a reg for other than x119, namely all: , x119--x120, size: 1
setc r14b; spill CF x203 to reg (r14)
clc;
movzx rdx, dl
adcx rdx, rcx; loading flag
adcx r11, [ rsp + 0x78 ]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbx, rdi, r13; x437, x436<- x5 * arg1[1]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mulx r15, rcx, r13; x429, x428<- x5 * arg1[5]
mov rdx, r13; x5 to rdx
mov [ rsp + 0x238 ], r12; spilling x243 to mem
mulx r13, r12, [ rsi + 0x0 ]; x439, x438<- x5 * arg1[0]
mov [ rsp + 0x240 ], r12; spilling x438 to mem
setc r12b; spill CF x120 to reg (r12)
clc;
mov [ rsp + 0x248 ], r15; spilling x429 to mem
mov r15, -0x1 ; moving imm to reg
movzx r10, r10b
adcx r10, r15; loading flag
adcx r11, r9
mov r10, [ rsp + 0x170 ]; x245, copying x230 here, cause x230 is needed in a reg for other than x245, namely all: , x245--x246, size: 1
adox r10, rbp
setc bpl; spill CF x163 to reg (rbp)
clc;
movzx r14, r14b
adcx r14, r15; loading flag
adcx r11, rax
movzx r14, bpl; x164, copying x163 here, cause x163 is needed in a reg for other than x164, namely all: , x164, size: 1
movzx r12, r12b
lea r14, [ r14 + r12 ]
movzx rax, r8b; x191, copying x190 here, cause x190 is needed in a reg for other than x191, namely all: , x191, size: 1
mov r9, [ rsp + 0x220 ]; load m64 x166 to register64
lea rax, [ rax + r9 ]; r8/64 + m8
mov r9, [ rsp + 0x168 ]; x247, copying x232 here, cause x232 is needed in a reg for other than x247, namely all: , x247--x248, size: 1
adox r9, r11
mulx r8, r12, [ rsi + 0x10 ]; x435, x434<- x5 * arg1[2]
mov rbp, [ rsi + 0x20 ]; load m64 x4 to register64
seto r11b; spill OF x248 to reg (r11)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rdi, r13
adcx rax, r14
mulx r13, r14, [ rsi + 0x20 ]; x431, x430<- x5 * arg1[4]
mov [ rsp + 0x250 ], r9; spilling x247 to mem
mov r9, [ rsp + 0x1b8 ]; load m64 x237 to register64
mov [ rsp + 0x258 ], r10; spilling x245 to mem
setc r10b; spill CF x207 to reg (r10)
clc;
adcx r9, [ rsp + 0x58 ]
mov [ rsp + 0x260 ], rdi; spilling x440 to mem
mulx r15, rdi, [ rsi + 0x18 ]; x433, x432<- x5 * arg1[3]
mov [ rsp + 0x268 ], rcx; spilling x428 to mem
setc cl; spill CF x280 to reg (rcx)
clc;
mov [ rsp + 0x270 ], r13; spilling x431 to mem
mov r13, -0x1 ; moving imm to reg
movzx r11, r11b
adcx r11, r13; loading flag
adcx rax, [ rsp + 0x1c8 ]
movzx r11, r10b; x251, copying x207 here, cause x207 is needed in a reg for other than x251, namely all: , x251, size: 1
mov r13, 0x0 ; moving imm to reg
adcx r11, r13
mulx rdx, r10, [ rsi + 0x30 ]; x427, x426<- x5 * arg1[6]
mov r13, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r13; 0xffffffffffffffff, swapping with x427, which is currently in rdx
mov [ rsp + 0x278 ], r11; spilling x251 to mem
mov [ rsp + 0x280 ], rax; spilling x249 to mem
mulx r11, rax, r9; x308, x307<- x279 * 0xffffffffffffffff
mov [ rsp + 0x288 ], r13; spilling x427 to mem
mov [ rsp + 0x290 ], rax; spilling x307 to mem
mulx r13, rax, r9; x306, x305<- x279 * 0xffffffffffffffff
mov rdx, [ rsp + 0x218 ]; load m64 x239 to register64
clc;
mov [ rsp + 0x298 ], r13; spilling x306 to mem
mov r13, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, r13; loading flag
adcx rdx, [ rsp + 0x98 ]
adox r12, rbx
adox rdi, r8
xchg rdx, rbp; x4, swapping with x281, which is currently in rdx
mulx rbx, r8, [ rsi + 0x0 ]; x352, x351<- x4 * arg1[0]
adox r14, r15
mov rcx, [ rsp + 0x270 ]; load m64 x431 to register64
mov r15, [ rsp + 0x268 ]; x448, copying x428 here, cause x428 is needed in a reg for other than x448, namely all: , x448--x449, size: 1
adox r15, rcx
mov rcx, [ rsp + 0x248 ]; x450, copying x429 here, cause x429 is needed in a reg for other than x450, namely all: , x450--x451, size: 1
adox rcx, r10
seto r10b; spill OF x451 to reg (r10)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rax, r11
mov r11, r9; _, copying x279 here, cause x279 is needed in a reg for other than _, namely all: , x295--x296, x299--x300, x303--x304, x301--x302, _--x323, x297--x298, size: 6
mov [ rsp + 0x2a0 ], rcx; spilling x450 to mem
setc cl; spill CF x282 to reg (rcx)
clc;
adcx r11, [ rsp + 0x290 ]
movzx r11, r10b; x452, copying x451 here, cause x451 is needed in a reg for other than x452, namely all: , x452, size: 1
mov r13, [ rsp + 0x288 ]; load m64 x427 to register64
lea r11, [ r11 + r13 ]; r8/64 + m8
adcx rax, rbp
mov r13, [ rsp + 0x90 ]; load m64 x268 to register64
setc bpl; spill CF x325 to reg (rbp)
clc;
mov r10, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, r10; loading flag
adcx r13, [ rsp + 0x210 ]
mov rcx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rcx; 0xffffffffffffffff, swapping with x4, which is currently in rdx
mov [ rsp + 0x2a8 ], r11; spilling x452 to mem
mulx r10, r11, r9; x304, x303<- x279 * 0xffffffffffffffff
setc dl; spill CF x284 to reg (rdx)
clc;
adcx r8, rax
mov rax, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rax; 0xffffffffffffffff, swapping with x284, which is currently in rdx
mov [ rsp + 0x2b0 ], r15; spilling x448 to mem
mov [ rsp + 0x2b8 ], r14; spilling x446 to mem
mulx r15, r14, r8; x395, x394<- x366 * 0xffffffffffffffff
mov rdx, [ rsp + 0x298 ]; x311, copying x306 here, cause x306 is needed in a reg for other than x311, namely all: , x311--x312, size: 1
adox rdx, r11
setc r11b; spill CF x367 to reg (r11)
clc;
mov [ rsp + 0x2c0 ], rdi; spilling x444 to mem
mov rdi, -0x1 ; moving imm to reg
movzx rbp, bpl
adcx rbp, rdi; loading flag
adcx r13, rdx
mov rbp, 0xffffffffffffffff ; moving imm to reg
mov rdx, r8; x366 to rdx
mulx r8, rdi, rbp; x391, x390<- x366 * 0xffffffffffffffff
xchg rdx, rcx; x4, swapping with x366, which is currently in rdx
mov [ rsp + 0x2c8 ], r12; spilling x442 to mem
mulx rbp, r12, [ rsi + 0x8 ]; x350, x349<- x4 * arg1[1]
mov [ rsp + 0x2d0 ], r8; spilling x391 to mem
seto r8b; spill OF x312 to reg (r8)
mov [ rsp + 0x2d8 ], rdi; spilling x390 to mem
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, rbx
mov rbx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbx; 0xffffffffffffffff, swapping with x4, which is currently in rdx
mov [ rsp + 0x2e0 ], rbp; spilling x350 to mem
mulx rdi, rbp, rcx; x393, x392<- x366 * 0xffffffffffffffff
seto dl; spill OF x354 to reg (rdx)
mov [ rsp + 0x2e8 ], rdi; spilling x393 to mem
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, rcx
seto r14b; spill OF x410 to reg (r14)
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rbp, r15
mov r15, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, r9; x279, swapping with x354, which is currently in rdx
mov byte [ rsp + 0x2f0 ], r9b; spilling byte x354 to mem
mulx rdi, r9, r15; x302, x301<- x279 * 0xfdc1767ae2ffffff
setc r15b; spill CF x327 to reg (r15)
clc;
mov [ rsp + 0x2f8 ], rdi; spilling x302 to mem
mov rdi, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, rdi; loading flag
adcx r10, r9
seto r8b; spill OF x397 to reg (r8)
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, r9; loading flag
adox r13, r12
setc r11b; spill CF x314 to reg (r11)
clc;
movzx r14, r14b
adcx r14, r9; loading flag
adcx r13, rbp
setc r12b; spill CF x412 to reg (r12)
clc;
adcx r13, [ rsp + 0x240 ]
mov r14, rdx; preserving value of x279 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx rbp, rdi, rbx; x348, x347<- x4 * arg1[2]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov byte [ rsp + 0x300 ], r11b; spilling byte x314 to mem
mulx r9, r11, r13; x482, x481<- x453 * 0xffffffffffffffff
mov rdx, [ rsp + 0xe0 ]; load m64 x270 to register64
mov byte [ rsp + 0x308 ], r12b; spilling byte x412 to mem
setc r12b; spill CF x454 to reg (r12)
clc;
mov [ rsp + 0x310 ], rbp; spilling x348 to mem
mov rbp, -0x1 ; moving imm to reg
movzx rax, al
adcx rax, rbp; loading flag
adcx rdx, [ rsp + 0x238 ]
setc al; spill CF x286 to reg (rax)
clc;
movzx r15, r15b
adcx r15, rbp; loading flag
adcx rdx, r10
seto r15b; spill OF x369 to reg (r15)
movzx r10, byte [ rsp + 0x2f0 ]; load byte memx354 to register64
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
adox r10, rbp; loading flag
adox rdi, [ rsp + 0x2e0 ]
mov r10, [ rsp + 0x2d8 ]; load m64 x390 to register64
setc bpl; spill CF x329 to reg (rbp)
clc;
mov byte [ rsp + 0x318 ], al; spilling byte x286 to mem
mov rax, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, rax; loading flag
adcx r10, [ rsp + 0x2e8 ]
mov r8, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, rcx; x366, swapping with x328, which is currently in rdx
mov byte [ rsp + 0x320 ], bpl; spilling byte x329 to mem
mulx rax, rbp, r8; x389, x388<- x366 * 0xfdc1767ae2ffffff
mov r8, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r13; x453, swapping with x366, which is currently in rdx
mov [ rsp + 0x328 ], rax; spilling x389 to mem
mov [ rsp + 0x330 ], rbp; spilling x388 to mem
mulx rax, rbp, r8; x480, x479<- x453 * 0xffffffffffffffff
setc r8b; spill CF x399 to reg (r8)
clc;
adcx rbp, r9
mov r9, rdx; preserving value of x453 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x338 ], rax; spilling x480 to mem
mov byte [ rsp + 0x340 ], r8b; spilling byte x399 to mem
mulx rax, r8, rbx; x346, x345<- x4 * arg1[3]
mov rdx, [ rsi + 0x30 ]; load m64 x6 to register64
mov [ rsp + 0x348 ], rax; spilling x346 to mem
setc al; spill CF x484 to reg (rax)
clc;
mov [ rsp + 0x350 ], rbp; spilling x483 to mem
mov rbp, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, rbp; loading flag
adcx rcx, rdi
mov r15, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, r15; 0x7bc65c783158aea3, swapping with x6, which is currently in rdx
mulx rdi, rbp, r14; x300, x299<- x279 * 0x7bc65c783158aea3
setc dl; spill CF x371 to reg (rdx)
clc;
adcx r11, r9
mov r11, [ rsp + 0x310 ]; x357, copying x348 here, cause x348 is needed in a reg for other than x357, namely all: , x357--x358, size: 1
adox r11, r8
seto r8b; spill OF x358 to reg (r8)
mov [ rsp + 0x358 ], rdi; spilling x300 to mem
movzx rdi, byte [ rsp + 0x308 ]; load byte memx412 to register64
mov byte [ rsp + 0x360 ], al; spilling byte x484 to mem
mov rax, 0x0 ; moving imm to reg
dec rax; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rdi, rax; loading flag
adox rcx, r10
mov dil, dl; preserving value of x371 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r10, rax, r15; x526, x525<- x6 * arg1[0]
seto dl; spill OF x414 to reg (rdx)
mov byte [ rsp + 0x368 ], r8b; spilling byte x358 to mem
mov r8, -0x1 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r8, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, r8; loading flag
adox rcx, [ rsp + 0x260 ]
mov r12, [ rsp + 0x350 ]; x498, copying x483 here, cause x483 is needed in a reg for other than x498, namely all: , x498--x499, size: 1
adcx r12, rcx
seto cl; spill OF x456 to reg (rcx)
movzx r8, byte [ rsp + 0x300 ]; load byte memx314 to register64
mov byte [ rsp + 0x370 ], dl; spilling byte x414 to mem
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
adox r8, rdx; loading flag
adox rbp, [ rsp + 0x2f8 ]
mov r8, 0x6cfc5fd681c52056 ; moving imm to reg
mov rdx, r14; x279 to rdx
mov byte [ rsp + 0x378 ], cl; spilling byte x456 to mem
mulx r14, rcx, r8; x298, x297<- x279 * 0x6cfc5fd681c52056
mov r8, [ rsp + 0xd8 ]; load m64 x272 to register64
mov [ rsp + 0x380 ], r14; spilling x298 to mem
seto r14b; spill OF x316 to reg (r14)
mov [ rsp + 0x388 ], rcx; spilling x297 to mem
movzx rcx, byte [ rsp + 0x318 ]; load byte memx286 to register64
mov [ rsp + 0x390 ], r10; spilling x526 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rcx, r10; loading flag
adox r8, [ rsp + 0x258 ]
seto cl; spill OF x288 to reg (rcx)
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rax, r12
mov r12, rdx; preserving value of x279 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov byte [ rsp + 0x398 ], r14b; spilling byte x316 to mem
mulx r10, r14, r15; x524, x523<- x6 * arg1[1]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x3a0 ], r10; spilling x524 to mem
mov byte [ rsp + 0x3a8 ], cl; spilling byte x288 to mem
mulx r10, rcx, rax; x567, x566<- x540 * 0xffffffffffffffff
mov [ rsp + 0x3b0 ], r10; spilling x567 to mem
mov [ rsp + 0x3b8 ], rcx; spilling x566 to mem
mulx r10, rcx, rax; x569, x568<- x540 * 0xffffffffffffffff
setc dl; spill CF x499 to reg (rdx)
clc;
adcx rcx, rax
setc cl; spill CF x584 to reg (rcx)
mov [ rsp + 0x3c0 ], r10; spilling x569 to mem
movzx r10, byte [ rsp + 0x320 ]; load byte memx329 to register64
clc;
mov byte [ rsp + 0x3c8 ], dl; spilling byte x499 to mem
mov rdx, -0x1 ; moving imm to reg
adcx r10, rdx; loading flag
adcx r8, rbp
mov r10, 0xffffffffffffffff ; moving imm to reg
mov rdx, r9; x453 to rdx
mulx r9, rbp, r10; x478, x477<- x453 * 0xffffffffffffffff
setc r10b; spill CF x331 to reg (r10)
clc;
mov byte [ rsp + 0x3d0 ], cl; spilling byte x584 to mem
mov rcx, -0x1 ; moving imm to reg
movzx rdi, dil
adcx rdi, rcx; loading flag
adcx r8, r11
mov rdi, [ rsp + 0x2d0 ]; load m64 x391 to register64
seto r11b; spill OF x541 to reg (r11)
movzx rcx, byte [ rsp + 0x340 ]; load byte memx399 to register64
mov byte [ rsp + 0x3d8 ], r10b; spilling byte x331 to mem
mov r10, -0x1 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r10, -0x1 ; moving imm to reg
adox rcx, r10; loading flag
adox rdi, [ rsp + 0x330 ]
seto cl; spill OF x401 to reg (rcx)
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r14, [ rsp + 0x390 ]
seto r10b; spill OF x528 to reg (r10)
mov [ rsp + 0x3e0 ], r14; spilling x527 to mem
movzx r14, byte [ rsp + 0x370 ]; load byte memx414 to register64
mov byte [ rsp + 0x3e8 ], r11b; spilling byte x541 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
adox r14, r11; loading flag
adox r8, rdi
seto r14b; spill OF x416 to reg (r14)
movzx rdi, byte [ rsp + 0x360 ]; load byte memx484 to register64
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r11, -0x1 ; moving imm to reg
adox rdi, r11; loading flag
adox rbp, [ rsp + 0x338 ]
xchg rdx, rbx; x4, swapping with x453, which is currently in rdx
mulx rdi, r11, [ rsi + 0x20 ]; x344, x343<- x4 * arg1[4]
mov [ rsp + 0x3f0 ], rdi; spilling x344 to mem
mov rdi, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, rdi; 0x7bc65c783158aea3, swapping with x4, which is currently in rdx
mov byte [ rsp + 0x3f8 ], r10b; spilling byte x528 to mem
mov byte [ rsp + 0x400 ], r14b; spilling byte x416 to mem
mulx r10, r14, r13; x387, x386<- x366 * 0x7bc65c783158aea3
seto dl; spill OF x486 to reg (rdx)
mov [ rsp + 0x408 ], r10; spilling x387 to mem
movzx r10, byte [ rsp + 0x378 ]; load byte memx456 to register64
mov [ rsp + 0x410 ], r11; spilling x343 to mem
mov r11, 0x0 ; moving imm to reg
dec r11; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r10, r11; loading flag
adox r8, [ rsp + 0x2c8 ]
mov r10, [ rsp + 0xd0 ]; load m64 x274 to register64
setc r11b; spill CF x373 to reg (r11)
mov [ rsp + 0x418 ], rbp; spilling x485 to mem
movzx rbp, byte [ rsp + 0x3a8 ]; load byte memx288 to register64
clc;
mov [ rsp + 0x420 ], r8; spilling x457 to mem
mov r8, -0x1 ; moving imm to reg
adcx rbp, r8; loading flag
adcx r10, [ rsp + 0x250 ]
setc bpl; spill CF x290 to reg (rbp)
clc;
movzx rcx, cl
adcx rcx, r8; loading flag
adcx r14, [ rsp + 0x328 ]
mov rcx, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, rcx; 0xfdc1767ae2ffffff, swapping with x486, which is currently in rdx
mov [ rsp + 0x428 ], r14; spilling x402 to mem
mulx r8, r14, rbx; x476, x475<- x453 * 0xfdc1767ae2ffffff
mov rdx, [ rsp + 0xc8 ]; load m64 x276 to register64
mov [ rsp + 0x430 ], r8; spilling x476 to mem
seto r8b; spill OF x458 to reg (r8)
mov byte [ rsp + 0x438 ], r11b; spilling byte x373 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, r11; loading flag
adox rdx, [ rsp + 0x280 ]
seto bpl; spill OF x292 to reg (rbp)
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r11, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r11; loading flag
adox r9, r14
mov rcx, [ rsp + 0x418 ]; load m64 x485 to register64
setc r14b; spill CF x403 to reg (r14)
movzx r11, byte [ rsp + 0x3c8 ]; load byte memx499 to register64
clc;
mov byte [ rsp + 0x440 ], bpl; spilling byte x292 to mem
mov rbp, -0x1 ; moving imm to reg
adcx r11, rbp; loading flag
adcx rcx, [ rsp + 0x420 ]
mov r11, [ rsp + 0x3c0 ]; load m64 x569 to register64
seto bpl; spill OF x488 to reg (rbp)
mov [ rsp + 0x448 ], rdx; spilling x291 to mem
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, [ rsp + 0x3b8 ]
seto dl; spill OF x571 to reg (rdx)
mov byte [ rsp + 0x450 ], bpl; spilling byte x488 to mem
movzx rbp, byte [ rsp + 0x3e8 ]; load byte memx541 to register64
mov byte [ rsp + 0x458 ], r14b; spilling byte x403 to mem
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbp, r14; loading flag
adox rcx, [ rsp + 0x3e0 ]
setc bpl; spill CF x501 to reg (rbp)
movzx r14, byte [ rsp + 0x3d0 ]; load byte memx584 to register64
clc;
mov [ rsp + 0x460 ], r9; spilling x487 to mem
mov r9, -0x1 ; moving imm to reg
adcx r14, r9; loading flag
adcx rcx, r11
mov r14, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, rbx; x453, swapping with x571, which is currently in rdx
mulx r11, r9, r14; x474, x473<- x453 * 0x7bc65c783158aea3
mov r14, [ rsp + 0x388 ]; load m64 x297 to register64
mov [ rsp + 0x468 ], r11; spilling x474 to mem
seto r11b; spill OF x543 to reg (r11)
mov [ rsp + 0x470 ], r9; spilling x473 to mem
movzx r9, byte [ rsp + 0x398 ]; load byte memx316 to register64
mov [ rsp + 0x478 ], rcx; spilling x585 to mem
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r9, rcx; loading flag
adox r14, [ rsp + 0x358 ]
seto r9b; spill OF x318 to reg (r9)
movzx rcx, byte [ rsp + 0x3d8 ]; load byte memx331 to register64
mov byte [ rsp + 0x480 ], r11b; spilling byte x543 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
adox rcx, r11; loading flag
adox r10, r14
mov rcx, [ rsp + 0x348 ]; load m64 x346 to register64
setc r14b; spill CF x586 to reg (r14)
movzx r11, byte [ rsp + 0x368 ]; load byte memx358 to register64
clc;
mov byte [ rsp + 0x488 ], r9b; spilling byte x318 to mem
mov r9, -0x1 ; moving imm to reg
adcx r11, r9; loading flag
adcx rcx, [ rsp + 0x410 ]
mov r11, rdx; preserving value of x453 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov byte [ rsp + 0x490 ], r14b; spilling byte x586 to mem
mulx r9, r14, r15; x522, x521<- x6 * arg1[2]
seto dl; spill OF x333 to reg (rdx)
mov [ rsp + 0x498 ], r9; spilling x522 to mem
movzx r9, byte [ rsp + 0x438 ]; load byte memx373 to register64
mov byte [ rsp + 0x4a0 ], bpl; spilling byte x501 to mem
mov rbp, 0x0 ; moving imm to reg
dec rbp; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r9, rbp; loading flag
adox r10, rcx
seto r9b; spill OF x375 to reg (r9)
movzx rcx, byte [ rsp + 0x400 ]; load byte memx416 to register64
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
adox rcx, rbp; loading flag
adox r10, [ rsp + 0x428 ]
mov rcx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rax; x540, swapping with x333, which is currently in rdx
mov byte [ rsp + 0x4a8 ], r9b; spilling byte x375 to mem
mulx rbp, r9, rcx; x565, x564<- x540 * 0xffffffffffffffff
setc cl; spill CF x360 to reg (rcx)
clc;
mov [ rsp + 0x4b0 ], rbp; spilling x565 to mem
mov rbp, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, rbp; loading flag
adcx r10, [ rsp + 0x2c0 ]
setc r8b; spill CF x460 to reg (r8)
clc;
movzx rbx, bl
adcx rbx, rbp; loading flag
adcx r9, [ rsp + 0x3b0 ]
seto bl; spill OF x418 to reg (rbx)
movzx rbp, byte [ rsp + 0x3f8 ]; load byte memx528 to register64
mov byte [ rsp + 0x4b8 ], r8b; spilling byte x460 to mem
mov r8, -0x1 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r8, -0x1 ; moving imm to reg
adox rbp, r8; loading flag
adox r14, [ rsp + 0x3a0 ]
setc bpl; spill CF x573 to reg (rbp)
movzx r8, byte [ rsp + 0x4a0 ]; load byte memx501 to register64
clc;
mov byte [ rsp + 0x4c0 ], bl; spilling byte x418 to mem
mov rbx, -0x1 ; moving imm to reg
adcx r8, rbx; loading flag
adcx r10, [ rsp + 0x460 ]
seto r8b; spill OF x530 to reg (r8)
movzx rbx, byte [ rsp + 0x480 ]; load byte memx543 to register64
mov byte [ rsp + 0x4c8 ], bpl; spilling byte x573 to mem
mov rbp, -0x1 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
adox rbx, rbp; loading flag
adox r10, r14
mov rbx, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, rbx; 0x6cfc5fd681c52056, swapping with x540, which is currently in rdx
mulx r14, rbp, r13; x385, x384<- x366 * 0x6cfc5fd681c52056
setc dl; spill CF x503 to reg (rdx)
mov [ rsp + 0x4d0 ], r14; spilling x385 to mem
movzx r14, byte [ rsp + 0x490 ]; load byte memx586 to register64
clc;
mov byte [ rsp + 0x4d8 ], r8b; spilling byte x530 to mem
mov r8, -0x1 ; moving imm to reg
adcx r14, r8; loading flag
adcx r10, r9
setc r14b; spill CF x588 to reg (r14)
seto r9b; spill OF x545 to reg (r9)
mov r8, [ rsp + 0x478 ]; x600, copying x585 here, cause x585 is needed in a reg for other than x600, namely all: , x616, x600--x601, size: 2
mov [ rsp + 0x4e0 ], r10; spilling x587 to mem
mov r10, 0xffffffffffffffff ; moving imm to reg
sub r8, r10
mov r10, 0x2341f27177344 ; moving imm to reg
xchg rdx, r10; 0x2341f27177344, swapping with x503, which is currently in rdx
mov [ rsp + 0x4e8 ], r8; spilling x600 to mem
mulx r12, r8, r12; x296, x295<- x279 * 0x2341f27177344
movzx rdx, byte [ rsp + 0x488 ]; load byte memx318 to register64
mov [ rsp + 0x4f0 ], r12; spilling x296 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rdx, r12; loading flag
adox r8, [ rsp + 0x380 ]
seto dl; spill OF x320 to reg (rdx)
movzx r12, byte [ rsp + 0x458 ]; load byte memx403 to register64
mov byte [ rsp + 0x4f8 ], r14b; spilling byte x588 to mem
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r12, r14; loading flag
adox rbp, [ rsp + 0x408 ]
mov r12, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, r12; 0xfdc1767ae2ffffff, swapping with x320, which is currently in rdx
mov byte [ rsp + 0x500 ], r12b; spilling byte x320 to mem
mulx r14, r12, rbx; x563, x562<- x540 * 0xfdc1767ae2ffffff
setc dl; spill CF x601 to reg (rdx)
clc;
mov [ rsp + 0x508 ], r14; spilling x563 to mem
mov r14, -0x1 ; moving imm to reg
movzx rax, al
adcx rax, r14; loading flag
adcx r8, [ rsp + 0x448 ]
mov al, dl; preserving value of x601 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov byte [ rsp + 0x510 ], r9b; spilling byte x545 to mem
mulx r14, r9, rdi; x342, x341<- x4 * arg1[5]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x518 ], r14; spilling x342 to mem
mov byte [ rsp + 0x520 ], al; spilling byte x601 to mem
mulx r14, rax, r15; x520, x519<- x6 * arg1[3]
seto dl; spill OF x405 to reg (rdx)
mov [ rsp + 0x528 ], r14; spilling x520 to mem
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rcx, cl
adox rcx, r14; loading flag
adox r9, [ rsp + 0x3f0 ]
seto cl; spill OF x362 to reg (rcx)
movzx r14, byte [ rsp + 0x4a8 ]; load byte memx375 to register64
mov byte [ rsp + 0x530 ], dl; spilling byte x405 to mem
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
adox r14, rdx; loading flag
adox r8, r9
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r14, r9, r15; x518, x517<- x6 * arg1[4]
seto dl; spill OF x377 to reg (rdx)
mov [ rsp + 0x538 ], r14; spilling x518 to mem
movzx r14, byte [ rsp + 0x4c0 ]; load byte memx418 to register64
mov [ rsp + 0x540 ], r9; spilling x517 to mem
mov r9, -0x1 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r9, -0x1 ; moving imm to reg
adox r14, r9; loading flag
adox r8, rbp
setc r14b; spill CF x335 to reg (r14)
movzx rbp, byte [ rsp + 0x4b8 ]; load byte memx460 to register64
clc;
adcx rbp, r9; loading flag
adcx r8, [ rsp + 0x2b8 ]
mov rbp, [ rsp + 0x470 ]; load m64 x473 to register64
setc r9b; spill CF x462 to reg (r9)
mov byte [ rsp + 0x548 ], dl; spilling byte x377 to mem
movzx rdx, byte [ rsp + 0x450 ]; load byte memx488 to register64
clc;
mov byte [ rsp + 0x550 ], cl; spilling byte x362 to mem
mov rcx, -0x1 ; moving imm to reg
adcx rdx, rcx; loading flag
adcx rbp, [ rsp + 0x430 ]
seto dl; spill OF x420 to reg (rdx)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rcx, -0x1 ; moving imm to reg
movzx r10, r10b
adox r10, rcx; loading flag
adox r8, rbp
mov r10, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, r10; 0x6cfc5fd681c52056, swapping with x420, which is currently in rdx
mulx rbp, rcx, r11; x472, x471<- x453 * 0x6cfc5fd681c52056
seto dl; spill OF x505 to reg (rdx)
mov [ rsp + 0x558 ], rbp; spilling x472 to mem
movzx rbp, byte [ rsp + 0x4c8 ]; load byte memx573 to register64
mov byte [ rsp + 0x560 ], r9b; spilling byte x462 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbp, r9; loading flag
adox r12, [ rsp + 0x4b0 ]
setc bpl; spill CF x490 to reg (rbp)
seto r9b; spill OF x575 to reg (r9)
mov byte [ rsp + 0x568 ], dl; spilling byte x505 to mem
movzx rdx, byte [ rsp + 0x520 ]; x601, copying x601 here, cause x601 is needed in a reg for other than x601, namely all: , x602--x603, size: 1
add rdx, -0x1
mov rdx, [ rsp + 0x4e0 ]; x602, copying x587 here, cause x587 is needed in a reg for other than x602, namely all: , x617, x602--x603, size: 2
mov byte [ rsp + 0x570 ], r10b; spilling byte x420 to mem
mov r10, 0xffffffffffffffff ; moving imm to reg
sbb rdx, r10
movzx r10, byte [ rsp + 0x4d8 ]; load byte memx530 to register64
mov [ rsp + 0x578 ], rdx; spilling x602 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r10, rdx; loading flag
adox rax, [ rsp + 0x498 ]
setc r10b; spill CF x603 to reg (r10)
movzx rdx, byte [ rsp + 0x510 ]; load byte memx545 to register64
clc;
mov byte [ rsp + 0x580 ], r9b; spilling byte x575 to mem
mov r9, -0x1 ; moving imm to reg
adcx rdx, r9; loading flag
adcx r8, rax
seto dl; spill OF x532 to reg (rdx)
movzx rax, byte [ rsp + 0x4f8 ]; load byte memx588 to register64
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
adox rax, r9; loading flag
adox r8, r12
setc al; spill CF x547 to reg (rax)
seto r12b; spill OF x590 to reg (r12)
movzx r9, r10b; x603, copying x603 here, cause x603 is needed in a reg for other than x603, namely all: , x604--x605, size: 1
add r9, -0x1
mov r10, r8; x604, copying x589 here, cause x589 is needed in a reg for other than x604, namely all: , x604--x605, x618, size: 2
mov r9, 0xffffffffffffffff ; moving imm to reg
sbb r10, r9
movzx r9, byte [ rsp + 0x500 ]; x321, copying x320 here, cause x320 is needed in a reg for other than x321, namely all: , x321, size: 1
mov [ rsp + 0x588 ], r10; spilling x604 to mem
mov r10, [ rsp + 0x4f0 ]; load m64 x296 to register64
lea r9, [ r9 + r10 ]; r8/64 + m8
mov r10, [ rsp + 0x278 ]; load m64 x251 to register64
mov byte [ rsp + 0x590 ], r12b; spilling byte x590 to mem
movzx r12, byte [ rsp + 0x440 ]; load byte memx292 to register64
mov byte [ rsp + 0x598 ], al; spilling byte x547 to mem
mov rax, 0x0 ; moving imm to reg
dec rax; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r12, rax; loading flag
adox r10, [ rsp + 0xe8 ]
seto r12b; spill OF x294 to reg (r12)
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rax, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, rax; loading flag
adox r10, r9
seto r14b; spill OF x337 to reg (r14)
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, r9; loading flag
adox rcx, [ rsp + 0x468 ]
xchg rdx, rdi; x4, swapping with x532, which is currently in rdx
mulx rdx, rbp, [ rsi + 0x30 ]; x340, x339<- x4 * arg1[6]
seto al; spill OF x492 to reg (rax)
movzx r9, byte [ rsp + 0x550 ]; load byte memx362 to register64
mov [ rsp + 0x5a0 ], rdx; spilling x340 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r9, rdx; loading flag
adox rbp, [ rsp + 0x518 ]
mov r9, 0x2341f27177344 ; moving imm to reg
mov rdx, r9; 0x2341f27177344 to rdx
mulx r13, r9, r13; x383, x382<- x366 * 0x2341f27177344
movzx rdx, r14b; x338, copying x337 here, cause x337 is needed in a reg for other than x338, namely all: , x338, size: 1
movzx r12, r12b
lea rdx, [ rdx + r12 ]
seto r12b; spill OF x364 to reg (r12)
movzx r14, byte [ rsp + 0x530 ]; load byte memx405 to register64
mov byte [ rsp + 0x5a8 ], al; spilling byte x492 to mem
mov rax, -0x1 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rax, -0x1 ; moving imm to reg
adox r14, rax; loading flag
adox r9, [ rsp + 0x4d0 ]
mov r14, [ rsp + 0x540 ]; load m64 x517 to register64
seto al; spill OF x407 to reg (rax)
mov [ rsp + 0x5b0 ], rdx; spilling x338 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rdi, dil
adox rdi, rdx; loading flag
adox r14, [ rsp + 0x528 ]
seto dil; spill OF x534 to reg (rdi)
movzx rdx, byte [ rsp + 0x548 ]; load byte memx377 to register64
mov [ rsp + 0x5b8 ], r13; spilling x383 to mem
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rdx, r13; loading flag
adox r10, rbp
seto dl; spill OF x379 to reg (rdx)
movzx rbp, byte [ rsp + 0x570 ]; load byte memx420 to register64
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
adox rbp, r13; loading flag
adox r10, r9
seto bpl; spill OF x422 to reg (rbp)
movzx r9, byte [ rsp + 0x560 ]; load byte memx462 to register64
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
adox r9, r13; loading flag
adox r10, [ rsp + 0x2b0 ]
mov r9, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, r9; 0x7bc65c783158aea3, swapping with x379, which is currently in rdx
mov byte [ rsp + 0x5c0 ], bpl; spilling byte x422 to mem
mulx r13, rbp, rbx; x561, x560<- x540 * 0x7bc65c783158aea3
mov [ rsp + 0x5c8 ], r13; spilling x561 to mem
mov r13, rdx; preserving value of 0x7bc65c783158aea3 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov byte [ rsp + 0x5d0 ], r9b; spilling byte x379 to mem
mov [ rsp + 0x5d8 ], rbp; spilling x560 to mem
mulx r9, rbp, r15; x516, x515<- x6 * arg1[5]
seto dl; spill OF x464 to reg (rdx)
movzx r13, byte [ rsp + 0x568 ]; load byte memx505 to register64
mov [ rsp + 0x5e0 ], r9; spilling x516 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r13, r9; loading flag
adox r10, rcx
movzx r13, r12b; x365, copying x364 here, cause x364 is needed in a reg for other than x365, namely all: , x365, size: 1
mov rcx, [ rsp + 0x5a0 ]; load m64 x340 to register64
lea r13, [ r13 + rcx ]; r8/64 + m8
seto cl; spill OF x507 to reg (rcx)
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
movzx rdi, dil
adox rdi, r12; loading flag
adox rbp, [ rsp + 0x538 ]
setc dil; spill CF x605 to reg (rdi)
movzx r9, byte [ rsp + 0x598 ]; load byte memx547 to register64
clc;
adcx r9, r12; loading flag
adcx r10, r14
movzx r9, al; x408, copying x407 here, cause x407 is needed in a reg for other than x408, namely all: , x408, size: 1
mov r14, [ rsp + 0x5b8 ]; load m64 x383 to register64
lea r9, [ r9 + r14 ]; r8/64 + m8
mov r14b, dl; preserving value of x464 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mulx r15, rax, r15; x514, x513<- x6 * arg1[6]
mov rdx, [ rsp + 0x5d8 ]; load m64 x560 to register64
setc r12b; spill CF x549 to reg (r12)
mov [ rsp + 0x5e8 ], r15; spilling x514 to mem
movzx r15, byte [ rsp + 0x580 ]; load byte memx575 to register64
clc;
mov [ rsp + 0x5f0 ], rbp; spilling x535 to mem
mov rbp, -0x1 ; moving imm to reg
adcx r15, rbp; loading flag
adcx rdx, [ rsp + 0x508 ]
mov r15, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, r15; 0x6cfc5fd681c52056, swapping with x576, which is currently in rdx
mov byte [ rsp + 0x5f8 ], r12b; spilling byte x549 to mem
mulx rbp, r12, rbx; x559, x558<- x540 * 0x6cfc5fd681c52056
setc dl; spill CF x577 to reg (rdx)
mov [ rsp + 0x600 ], rbp; spilling x559 to mem
movzx rbp, byte [ rsp + 0x5d0 ]; load byte memx379 to register64
clc;
mov byte [ rsp + 0x608 ], cl; spilling byte x507 to mem
mov rcx, -0x1 ; moving imm to reg
adcx rbp, rcx; loading flag
adcx r13, [ rsp + 0x5b0 ]
setc bpl; spill CF x381 to reg (rbp)
movzx rcx, byte [ rsp + 0x590 ]; load byte memx590 to register64
clc;
mov [ rsp + 0x610 ], r12; spilling x558 to mem
mov r12, -0x1 ; moving imm to reg
adcx rcx, r12; loading flag
adcx r10, r15
setc cl; spill CF x592 to reg (rcx)
movzx r15, byte [ rsp + 0x5c0 ]; load byte memx422 to register64
clc;
adcx r15, r12; loading flag
adcx r13, r9
mov r15, 0x2341f27177344 ; moving imm to reg
xchg rdx, rbx; x540, swapping with x577, which is currently in rdx
mulx rdx, r9, r15; x557, x556<- x540 * 0x2341f27177344
setc r12b; spill CF x424 to reg (r12)
seto r15b; spill OF x536 to reg (r15)
mov [ rsp + 0x618 ], rdx; spilling x557 to mem
movzx rdx, dil; x605, copying x605 here, cause x605 is needed in a reg for other than x605, namely all: , x606--x607, size: 1
add rdx, -0x1
mov rdx, r10; x606, copying x591 here, cause x591 is needed in a reg for other than x606, namely all: , x606--x607, x619, size: 2
mov byte [ rsp + 0x620 ], cl; spilling byte x592 to mem
mov rcx, 0xfdc1767ae2ffffff ; moving imm to reg
sbb rdx, rcx
movzx rcx, r12b; x425, copying x424 here, cause x424 is needed in a reg for other than x425, namely all: , x425, size: 1
movzx rbp, bpl
lea rcx, [ rcx + rbp ]
mov rbp, 0x2341f27177344 ; moving imm to reg
xchg rdx, rbp; 0x2341f27177344, swapping with x606, which is currently in rdx
mulx r11, r12, r11; x470, x469<- x453 * 0x2341f27177344
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r14, r14b
adox r14, rdx; loading flag
adox r13, [ rsp + 0x2a0 ]
setc r14b; spill CF x607 to reg (r14)
clc;
movzx r15, r15b
adcx r15, rdx; loading flag
adcx rax, [ rsp + 0x5e0 ]
setc r15b; spill CF x538 to reg (r15)
movzx rdx, byte [ rsp + 0x5a8 ]; load byte memx492 to register64
clc;
mov [ rsp + 0x628 ], rbp; spilling x606 to mem
mov rbp, -0x1 ; moving imm to reg
adcx rdx, rbp; loading flag
adcx r12, [ rsp + 0x558 ]
mov rdx, 0x0 ; moving imm to reg
adcx r11, rdx
mov rdx, [ rsp + 0x2a8 ]; x467, copying x452 here, cause x452 is needed in a reg for other than x467, namely all: , x467--x468, size: 1
adox rdx, rcx
mov rcx, [ rsp + 0x5c8 ]; load m64 x561 to register64
clc;
movzx rbx, bl
adcx rbx, rbp; loading flag
adcx rcx, [ rsp + 0x610 ]
setc bl; spill CF x579 to reg (rbx)
movzx rbp, byte [ rsp + 0x608 ]; load byte memx507 to register64
clc;
mov byte [ rsp + 0x630 ], r15b; spilling byte x538 to mem
mov r15, -0x1 ; moving imm to reg
adcx rbp, r15; loading flag
adcx r13, r12
adcx r11, rdx
setc bpl; spill CF x511 to reg (rbp)
clc;
movzx rbx, bl
adcx rbx, r15; loading flag
adcx r9, [ rsp + 0x600 ]
setc r12b; spill CF x581 to reg (r12)
movzx rdx, byte [ rsp + 0x5f8 ]; load byte memx549 to register64
clc;
adcx rdx, r15; loading flag
adcx r13, [ rsp + 0x5f0 ]
adcx rax, r11
setc dl; spill CF x553 to reg (rdx)
movzx rbx, byte [ rsp + 0x620 ]; load byte memx592 to register64
clc;
adcx rbx, r15; loading flag
adcx r13, rcx
movzx rbx, bpl; x512, copying x511 here, cause x511 is needed in a reg for other than x512, namely all: , x512, size: 1
mov rcx, 0x0 ; moving imm to reg
adox rbx, rcx
setc bpl; spill CF x594 to reg (rbp)
movzx r11, r14b; x607, copying x607 here, cause x607 is needed in a reg for other than x607, namely all: , x608--x609, size: 1
add r11, -0x1
mov r11, r13; x608, copying x593 here, cause x593 is needed in a reg for other than x608, namely all: , x608--x609, x620, size: 2
mov r14, 0x7bc65c783158aea3 ; moving imm to reg
sbb r11, r14
movzx rcx, byte [ rsp + 0x630 ]; x539, copying x538 here, cause x538 is needed in a reg for other than x539, namely all: , x539, size: 1
mov r15, [ rsp + 0x5e8 ]; load m64 x514 to register64
lea rcx, [ rcx + r15 ]; r8/64 + m8
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r15, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, r15; loading flag
adox rax, r9
seto r9b; spill OF x596 to reg (r9)
mov rbp, rax; x610, copying x595 here, cause x595 is needed in a reg for other than x610, namely all: , x621, x610--x611, size: 2
mov r15, 0x6cfc5fd681c52056 ; moving imm to reg
sbb rbp, r15
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r15, -0x1 ; moving imm to reg
movzx rdx, dl
adox rdx, r15; loading flag
adox rbx, rcx
movzx rdx, r12b; x582, copying x581 here, cause x581 is needed in a reg for other than x582, namely all: , x582, size: 1
mov rcx, [ rsp + 0x618 ]; load m64 x557 to register64
lea rdx, [ rdx + rcx ]; r8/64 + m8
setc cl; spill CF x611 to reg (rcx)
clc;
movzx r9, r9b
adcx r9, r15; loading flag
adcx rbx, rdx
seto r12b; spill OF x599 to reg (r12)
adc r12b, 0x0
movzx r12, r12b
movzx r9, cl; x611, copying x611 here, cause x611 is needed in a reg for other than x611, namely all: , x612--x613, size: 1
add r9, -0x1
mov rcx, rbx; x612, copying x597 here, cause x597 is needed in a reg for other than x612, namely all: , x612--x613, x622, size: 2
mov r9, 0x2341f27177344 ; moving imm to reg
sbb rcx, r9
movzx rdx, r12b; _, copying x599 here, cause x599 is needed in a reg for other than _, namely all: , _--x615, size: 1
sbb rdx, 0x00000000
mov rdx, [ rsp + 0x4e8 ]; x616, copying x600 here, cause x600 is needed in a reg for other than x616, namely all: , x616, size: 1
cmovc rdx, [ rsp + 0x478 ]; if CF, x616<- x585 (nzVar)
cmovc rcx, rbx; if CF, x622<- x597 (nzVar)
cmovc r11, r13; if CF, x620<- x593 (nzVar)
mov r13, [ rsp + 0x578 ]; x617, copying x602 here, cause x602 is needed in a reg for other than x617, namely all: , x617, size: 1
cmovc r13, [ rsp + 0x4e0 ]; if CF, x617<- x587 (nzVar)
mov rbx, [ rsp + 0x588 ]; x618, copying x604 here, cause x604 is needed in a reg for other than x618, namely all: , x618, size: 1
cmovc rbx, r8; if CF, x618<- x589 (nzVar)
mov r8, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r8 + 0x20 ], r11; out1[4] = x620
mov [ r8 + 0x8 ], r13; out1[1] = x617
mov [ r8 + 0x10 ], rbx; out1[2] = x618
mov r12, [ rsp + 0x628 ]; x619, copying x606 here, cause x606 is needed in a reg for other than x619, namely all: , x619, size: 1
cmovc r12, r10; if CF, x619<- x591 (nzVar)
cmovc rbp, rax; if CF, x621<- x595 (nzVar)
mov [ r8 + 0x28 ], rbp; out1[5] = x621
mov [ r8 + 0x30 ], rcx; out1[6] = x622
mov [ r8 + 0x0 ], rdx; out1[0] = x616
mov [ r8 + 0x18 ], r12; out1[3] = x619
mov rbx, [ rsp + 0x638 ]; restoring from stack
mov rbp, [ rsp + 0x640 ]; restoring from stack
mov r12, [ rsp + 0x648 ]; restoring from stack
mov r13, [ rsp + 0x650 ]; restoring from stack
mov r14, [ rsp + 0x658 ]; restoring from stack
mov r15, [ rsp + 0x660 ]; restoring from stack
add rsp, 0x668 
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; clocked at 3600 MHz
; first cyclecount 365.17, best 359.105, lastGood 392.7586206896552
; seed 3715409675138377 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5290118 ms / 60000 runs=> 88.16863333333333ms/run
; Time spent for assembling and measureing (initial batch_size=29, initial num_batches=101): 110595 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.020905960887828968
; number reverted permutation/ tried permutation: 17063 / 30114 =56.661%
; number reverted decision/ tried decision: 16125 / 29887 =53.953%