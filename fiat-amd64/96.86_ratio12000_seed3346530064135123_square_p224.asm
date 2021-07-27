SECTION .text
	GLOBAL square_p224
square_p224:
sub rsp, 0x130 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x100 ], rbx; saving to stack
mov [ rsp + 0x108 ], rbp; saving to stack
mov [ rsp + 0x110 ], r12; saving to stack
mov [ rsp + 0x118 ], r13; saving to stack
mov [ rsp + 0x120 ], r14; saving to stack
mov [ rsp + 0x128 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x4 to register64
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r10, r11, rax; x10, x9<- x4 * arg1[1]
mov rdx, rax; x4 to rdx
mulx rax, rbx, [ rsi + 0x0 ]; x12, x11<- x4 * arg1[0]
mov rbp, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbx; x11, swapping with x4, which is currently in rdx
mulx r12, r13, rbp; _, x20<- x11 * 0xffffffffffffffff
add r11, rax; could be done better, if r0 has been u8 as well
mov r12, r13; _, copying x20 here, cause x20 is needed in a reg for other than _, namely all: , x26--x27, _--x34, x24--x25, x22--x23, size: 4
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, rdx
mov r12, 0xffffffff00000000 ; moving imm to reg
mov rdx, r12; 0xffffffff00000000 to rdx
mulx r12, r15, r13; x27, x26<- x20 * 0xffffffff00000000
mov rcx, [ rsi + 0x8 ]; load m64 x1 to register64
adox r15, r11
mov r8, rdx; preserving value of 0xffffffff00000000 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r9, rax, rcx; x50, x49<- x1 * arg1[0]
seto dl; spill OF x36 to reg (rdx)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rax, r15
xchg rdx, rbp; 0xffffffffffffffff, swapping with x36, which is currently in rdx
mulx r11, r15, rax; _, x68<- x58 * 0xffffffffffffffff
mulx r11, r14, r15; x73, x72<- x68 * 0xffffffffffffffff
xchg rdx, r15; x68, swapping with 0xffffffffffffffff, which is currently in rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r15, rdi, r8; x75, x74<- x68 * 0xffffffff00000000
seto r8b; spill OF x59 to reg (r8)
mov [ rsp + 0x8 ], rdi; spilling x74 to mem
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, r15
mov r15, 0xffffffff ; moving imm to reg
mov [ rsp + 0x10 ], r14; spilling x76 to mem
mulx rdi, r14, r15; x71, x70<- x68 * 0xffffffff
adox r14, r11
mov r11, 0x0 ; moving imm to reg
adox rdi, r11
mov r15, -0x3 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rdx, rax
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rax, r11, rbx; x8, x7<- x4 * arg1[2]
adcx r11, r10
mov rdx, 0xffffffffffffffff ; moving imm to reg
mulx r10, r15, r13; x25, x24<- x20 * 0xffffffffffffffff
seto dl; spill OF x82 to reg (rdx)
mov [ rsp + 0x18 ], rdi; spilling x80 to mem
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, r12
seto r12b; spill OF x29 to reg (r12)
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdi, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, rdi; loading flag
adox r11, r15
xchg rdx, rcx; x1, swapping with x82, which is currently in rdx
mulx rbp, r15, [ rsi + 0x8 ]; x48, x47<- x1 * arg1[1]
setc dil; spill CF x16 to reg (rdi)
clc;
adcx r15, r9
setc r9b; spill CF x52 to reg (r9)
clc;
mov [ rsp + 0x20 ], r14; spilling x78 to mem
mov r14, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, r14; loading flag
adcx r11, r15
mov r8, [ rsi + 0x10 ]; load m64 x2 to register64
seto r15b; spill OF x38 to reg (r15)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r14; loading flag
adox r11, [ rsp + 0x8 ]
xchg rdx, r8; x2, swapping with x1, which is currently in rdx
mulx rcx, r14, [ rsi + 0x0 ]; x99, x98<- x2 * arg1[0]
mov [ rsp + 0x28 ], rcx; spilling x99 to mem
setc cl; spill CF x61 to reg (rcx)
clc;
adcx r14, r11
mov r11, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r11; 0xffffffffffffffff, swapping with x2, which is currently in rdx
mov byte [ rsp + 0x30 ], cl; spilling byte x61 to mem
mov [ rsp + 0x38 ], rbp; spilling x48 to mem
mulx rcx, rbp, r14; _, x117<- x107 * 0xffffffffffffffff
mov rcx, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov byte [ rsp + 0x40 ], r9b; spilling byte x52 to mem
mulx rbx, r9, rbx; x6, x5<- x4 * arg1[3]
mov rdx, rbp; _, copying x117 here, cause x117 is needed in a reg for other than _, namely all: , x119--x120, x123--x124, _--x131, x121--x122, size: 4
setc cl; spill CF x108 to reg (rcx)
clc;
adcx rdx, r14
seto dl; spill OF x84 to reg (rdx)
mov r14, -0x1 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r14, -0x1 ; moving imm to reg
movzx rdi, dil
adox rdi, r14; loading flag
adox rax, r9
mov rdi, 0xffffffff ; moving imm to reg
xchg rdx, rdi; 0xffffffff, swapping with x84, which is currently in rdx
mulx r13, r9, r13; x23, x22<- x20 * 0xffffffff
setc r14b; spill CF x131 to reg (r14)
clc;
mov rdx, -0x1 ; moving imm to reg
movzx r12, r12b
adcx r12, rdx; loading flag
adcx r10, r9
mov rdx, r8; x1 to rdx
mulx r8, r12, [ rsi + 0x10 ]; x46, x45<- x1 * arg1[2]
seto r9b; spill OF x18 to reg (r9)
mov [ rsp + 0x48 ], r8; spilling x46 to mem
mov r8, -0x1 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r8, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, r8; loading flag
adox rax, r10
setc r15b; spill CF x31 to reg (r15)
movzx r10, byte [ rsp + 0x40 ]; load byte memx52 to register64
clc;
adcx r10, r8; loading flag
adcx r12, [ rsp + 0x38 ]
seto r10b; spill OF x40 to reg (r10)
movzx r8, byte [ rsp + 0x30 ]; load byte memx61 to register64
mov [ rsp + 0x50 ], rbx; spilling x6 to mem
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r8, rbx; loading flag
adox rax, r12
seto r8b; spill OF x63 to reg (r8)
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
movzx rdi, dil
adox rdi, r12; loading flag
adox rax, [ rsp + 0x10 ]
xchg rdx, r11; x2, swapping with x1, which is currently in rdx
mulx rdi, rbx, [ rsi + 0x8 ]; x97, x96<- x2 * arg1[1]
setc r12b; spill CF x54 to reg (r12)
clc;
adcx rbx, [ rsp + 0x28 ]
mov [ rsp + 0x58 ], rdi; spilling x97 to mem
mov rdi, 0xffffffff00000000 ; moving imm to reg
xchg rdx, rdi; 0xffffffff00000000, swapping with x2, which is currently in rdx
mov byte [ rsp + 0x60 ], r8b; spilling byte x63 to mem
mov byte [ rsp + 0x68 ], r12b; spilling byte x54 to mem
mulx r8, r12, rbp; x124, x123<- x117 * 0xffffffff00000000
setc dl; spill CF x101 to reg (rdx)
clc;
mov [ rsp + 0x70 ], r8; spilling x124 to mem
mov r8, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, r8; loading flag
adcx rax, rbx
seto cl; spill OF x86 to reg (rcx)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, rbx; loading flag
adox rax, r12
mov r14, [ rsi + 0x18 ]; load m64 x3 to register64
xchg rdx, r14; x3, swapping with x101, which is currently in rdx
mulx r12, r8, [ rsi + 0x0 ]; x148, x147<- x3 * arg1[0]
setc bl; spill CF x110 to reg (rbx)
clc;
adcx r8, rax
mov rax, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rax; 0xffffffffffffffff, swapping with x3, which is currently in rdx
mov [ rsp + 0x78 ], r12; spilling x148 to mem
mov byte [ rsp + 0x80 ], bl; spilling byte x110 to mem
mulx r12, rbx, r8; _, x166<- x156 * 0xffffffffffffffff
mov r12, 0xffffffff00000000 ; moving imm to reg
xchg rdx, rbx; x166, swapping with 0xffffffffffffffff, which is currently in rdx
mov byte [ rsp + 0x88 ], r14b; spilling byte x101 to mem
mulx rbx, r14, r12; x173, x172<- x166 * 0xffffffff00000000
mov r12, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x90 ], r14; spilling x172 to mem
mov byte [ rsp + 0x98 ], cl; spilling byte x86 to mem
mulx r14, rcx, r12; x171, x170<- x166 * 0xffffffffffffffff
setc r12b; spill CF x157 to reg (r12)
clc;
adcx rcx, rbx
mov rbx, 0xffffffff ; moving imm to reg
mov [ rsp + 0xa0 ], rcx; spilling x174 to mem
mov byte [ rsp + 0xa8 ], r12b; spilling byte x157 to mem
mulx rcx, r12, rbx; x169, x168<- x166 * 0xffffffff
adcx r12, r14
movzx r14, r15b; x32, copying x31 here, cause x31 is needed in a reg for other than x32, namely all: , x32, size: 1
lea r14, [ r14 + r13 ]
mov r13, 0x0 ; moving imm to reg
adcx rcx, r13
movzx r15, r9b; x19, copying x18 here, cause x18 is needed in a reg for other than x19, namely all: , x19, size: 1
mov r13, [ rsp + 0x50 ]; load m64 x6 to register64
lea r15, [ r15 + r13 ]; r8/64 + m8
clc;
mov r13, -0x1 ; moving imm to reg
movzx r10, r10b
adcx r10, r13; loading flag
adcx r15, r14
mov r9, rdx; preserving value of x166 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx r11, r10, r11; x44, x43<- x1 * arg1[3]
seto dl; spill OF x133 to reg (rdx)
movzx r14, byte [ rsp + 0x68 ]; load byte memx54 to register64
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
adox r14, r13; loading flag
adox r10, [ rsp + 0x48 ]
seto r14b; spill OF x56 to reg (r14)
movzx r13, byte [ rsp + 0x60 ]; load byte memx63 to register64
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r13, rbx; loading flag
adox r15, r10
movzx r13, r14b; x57, copying x56 here, cause x56 is needed in a reg for other than x57, namely all: , x57, size: 1
lea r13, [ r13 + r11 ]
setc r11b; spill CF x42 to reg (r11)
movzx r10, byte [ rsp + 0x98 ]; load byte memx86 to register64
clc;
adcx r10, rbx; loading flag
adcx r15, [ rsp + 0x20 ]
movzx r10, r11b; x66, copying x42 here, cause x42 is needed in a reg for other than x66, namely all: , x66--x67, size: 1
adox r10, r13
mov r11, [ rsp + 0x18 ]; x89, copying x80 here, cause x80 is needed in a reg for other than x89, namely all: , x89--x90, size: 1
adcx r11, r10
xchg rdx, rdi; x2, swapping with x133, which is currently in rdx
mulx r14, r13, [ rsi + 0x10 ]; x95, x94<- x2 * arg1[2]
seto r10b; spill OF x91 to reg (r10)
adc r10b, 0x0
movzx r10, r10b
adox r9, r8
movzx r9, byte [ rsp + 0x88 ]; load byte memx101 to register64
adcx r9, rbx; loading flag
adcx r13, [ rsp + 0x58 ]
setc r9b; spill CF x103 to reg (r9)
movzx r8, byte [ rsp + 0x80 ]; load byte memx110 to register64
clc;
adcx r8, rbx; loading flag
adcx r15, r13
mov r8, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbp; x117, swapping with x2, which is currently in rdx
mulx r13, rbx, r8; x122, x121<- x117 * 0xffffffffffffffff
seto r8b; spill OF x180 to reg (r8)
mov [ rsp + 0xb0 ], rcx; spilling x178 to mem
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, [ rsp + 0x70 ]
setc cl; spill CF x112 to reg (rcx)
clc;
mov [ rsp + 0xb8 ], r12; spilling x176 to mem
mov r12, -0x1 ; moving imm to reg
movzx rdi, dil
adcx rdi, r12; loading flag
adcx r15, rbx
xchg rdx, rax; x3, swapping with x117, which is currently in rdx
mulx rdi, rbx, [ rsi + 0x8 ]; x146, x145<- x3 * arg1[1]
setc r12b; spill CF x135 to reg (r12)
clc;
adcx rbx, [ rsp + 0x78 ]
mov byte [ rsp + 0xc0 ], r10b; spilling byte x91 to mem
setc r10b; spill CF x150 to reg (r10)
mov [ rsp + 0xc8 ], rdi; spilling x146 to mem
movzx rdi, byte [ rsp + 0xa8 ]; load byte memx157 to register64
clc;
mov byte [ rsp + 0xd0 ], r12b; spilling byte x135 to mem
mov r12, -0x1 ; moving imm to reg
adcx rdi, r12; loading flag
adcx r15, rbx
seto dil; spill OF x126 to reg (rdi)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, rbx; loading flag
adox r15, [ rsp + 0x90 ]
xchg rdx, rbp; x2, swapping with x3, which is currently in rdx
mulx rdx, r8, [ rsi + 0x18 ]; x93, x92<- x2 * arg1[3]
setc bl; spill CF x159 to reg (rbx)
mov [ rsp + 0xd8 ], rdx; spilling x93 to mem
seto dl; spill OF x182 to reg (rdx)
mov byte [ rsp + 0xe0 ], r10b; spilling byte x150 to mem
mov r10, r15; x190, copying x181 here, cause x181 is needed in a reg for other than x190, namely all: , x200, x190--x191, size: 2
sub r10, 0x00000001
dec r12; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r9, r9b
adox r9, r12; loading flag
adox r14, r8
seto r9b; spill OF x105 to reg (r9)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r8; loading flag
adox r11, r14
mov rcx, 0xffffffff ; moving imm to reg
xchg rdx, rax; x117, swapping with x182, which is currently in rdx
mulx rdx, r14, rcx; x120, x119<- x117 * 0xffffffff
mov r12, rdx; preserving value of x120 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r8, rcx, rbp; x144, x143<- x3 * arg1[2]
seto dl; spill OF x114 to reg (rdx)
mov [ rsp + 0xe8 ], r10; spilling x190 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rdi, dil
adox rdi, r10; loading flag
adox r13, r14
setc dil; spill CF x191 to reg (rdi)
movzx r14, byte [ rsp + 0xd0 ]; load byte memx135 to register64
clc;
adcx r14, r10; loading flag
adcx r11, r13
setc r14b; spill CF x137 to reg (r14)
movzx r13, byte [ rsp + 0xe0 ]; load byte memx150 to register64
clc;
adcx r13, r10; loading flag
adcx rcx, [ rsp + 0xc8 ]
setc r13b; spill CF x152 to reg (r13)
clc;
movzx rbx, bl
adcx rbx, r10; loading flag
adcx r11, rcx
setc bl; spill CF x161 to reg (rbx)
clc;
movzx rax, al
adcx rax, r10; loading flag
adcx r11, [ rsp + 0xa0 ]
movzx rax, r9b; x106, copying x105 here, cause x105 is needed in a reg for other than x106, namely all: , x106, size: 1
mov rcx, [ rsp + 0xd8 ]; load m64 x93 to register64
lea rax, [ rax + rcx ]; r8/64 + m8
setc cl; spill CF x184 to reg (rcx)
seto r9b; spill OF x128 to reg (r9)
movzx r10, dil; x191, copying x191 here, cause x191 is needed in a reg for other than x191, namely all: , x192--x193, size: 1
add r10, -0x1
mov r10, r11; x192, copying x183 here, cause x183 is needed in a reg for other than x192, namely all: , x201, x192--x193, size: 2
mov byte [ rsp + 0xf0 ], bl; spilling byte x161 to mem
mov rbx, 0xffffffff00000000 ; moving imm to reg
sbb r10, rbx
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
mov [ rsp + 0xf8 ], r10; spilling x192 to mem
movzx r10, byte [ rsp + 0xc0 ]; load byte memx91 to register64
movzx rdx, dl
adox rdx, rbx; loading flag
adox rax, r10
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rbp, r10, rbp; x142, x141<- x3 * arg1[3]
movzx rdx, r9b; x129, copying x128 here, cause x128 is needed in a reg for other than x129, namely all: , x129, size: 1
lea rdx, [ rdx + r12 ]
seto r12b; spill OF x116 to reg (r12)
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, r9; loading flag
adox rax, rdx
seto r14b; spill OF x139 to reg (r14)
dec rbx; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx r13, r13b
adox r13, rbx; loading flag
adox r8, r10
movzx r9, r14b; x140, copying x139 here, cause x139 is needed in a reg for other than x140, namely all: , x140, size: 1
movzx r12, r12b
lea r9, [ r9 + r12 ]
seto r13b; spill OF x154 to reg (r13)
movzx r12, byte [ rsp + 0xf0 ]; load byte memx161 to register64
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r10, -0x1 ; moving imm to reg
adox r12, r10; loading flag
adox rax, r8
seto r12b; spill OF x163 to reg (r12)
dec rbx; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx rcx, cl
adox rcx, rbx; loading flag
adox rax, [ rsp + 0xb8 ]
seto r10b; spill OF x186 to reg (r10)
mov rcx, rax; x194, copying x185 here, cause x185 is needed in a reg for other than x194, namely all: , x194--x195, x202, size: 2
mov rdx, 0xffffffffffffffff ; moving imm to reg
sbb rcx, rdx
movzx r14, r13b; x155, copying x154 here, cause x154 is needed in a reg for other than x155, namely all: , x155, size: 1
lea r14, [ r14 + rbp ]
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, rbp; loading flag
adox r9, r14
seto r8b; spill OF x165 to reg (r8)
dec rbx; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx r10, r10b
adox r10, rbx; loading flag
adox r9, [ rsp + 0xb0 ]
seto bpl; spill OF x188 to reg (rbp)
mov r13, r9; x196, copying x187 here, cause x187 is needed in a reg for other than x196, namely all: , x203, x196--x197, size: 2
mov r12, 0xffffffff ; moving imm to reg
sbb r13, r12
movzx r10, bpl; x189, copying x188 here, cause x188 is needed in a reg for other than x189, namely all: , x189, size: 1
movzx r8, r8b
lea r10, [ r10 + r8 ]
sbb r10, 0x00000000
mov r10, [ rsp + 0xe8 ]; x200, copying x190 here, cause x190 is needed in a reg for other than x200, namely all: , x200, size: 1
cmovc r10, r15; if CF, x200<- x181 (nzVar)
mov r15, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r15 + 0x0 ], r10; out1[0] = x200
cmovc r13, r9; if CF, x203<- x187 (nzVar)
mov [ r15 + 0x18 ], r13; out1[3] = x203
mov r14, [ rsp + 0xf8 ]; x201, copying x192 here, cause x192 is needed in a reg for other than x201, namely all: , x201, size: 1
cmovc r14, r11; if CF, x201<- x183 (nzVar)
cmovc rcx, rax; if CF, x202<- x185 (nzVar)
mov [ r15 + 0x10 ], rcx; out1[2] = x202
mov [ r15 + 0x8 ], r14; out1[1] = x201
mov rbx, [ rsp + 0x100 ]; restoring from stack
mov rbp, [ rsp + 0x108 ]; restoring from stack
mov r12, [ rsp + 0x110 ]; restoring from stack
mov r13, [ rsp + 0x118 ]; restoring from stack
mov r14, [ rsp + 0x120 ]; restoring from stack
mov r15, [ rsp + 0x128 ]; restoring from stack
add rsp, 0x130 
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; clocked at 2200 MHz
; first cyclecount 100.64, best 96.67469879518072, lastGood 96.86046511627907
; seed 3346530064135123 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 9430 ms / 500 runs=> 18.86ms/run
; Time spent for assembling and measureing (initial batch_size=86, initial num_batches=101): 1068 ms
; Ratio (time for assembling + measure)/(total runtime for 500runs): 0.11325556733828208
; number reverted permutation/ tried permutation: 194 / 254 =76.378%
; number reverted decision/ tried decision: 155 / 247 =62.753%