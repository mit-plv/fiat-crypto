SECTION .text
	GLOBAL square_p384
square_p384:
sub rsp, 0x278 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x248 ], rbx; saving to stack
mov [ rsp + 0x250 ], rbp; saving to stack
mov [ rsp + 0x258 ], r12; saving to stack
mov [ rsp + 0x260 ], r13; saving to stack
mov [ rsp + 0x268 ], r14; saving to stack
mov [ rsp + 0x270 ], r15; saving to stack
mov rax, [ rsi + 0x8 ]; load m64 x1 to register64
mov rdx, rax; x1 to rdx
mulx rax, r10, [ rsi + 0x10 ]; x76, x75<- x1 * arg1[2]
mulx r11, rbx, [ rsi + 0x8 ]; x78, x77<- x1 * arg1[1]
mulx rbp, r12, [ rsi + 0x20 ]; x72, x71<- x1 * arg1[4]
mulx r13, r14, [ rsi + 0x0 ]; x80, x79<- x1 * arg1[0]
add rbx, r13; could be done better, if r0 has been u8 as well
mulx r15, rcx, [ rsi + 0x18 ]; x74, x73<- x1 * arg1[3]
mulx rdx, r8, [ rsi + 0x28 ]; x70, x69<- x1 * arg1[5]
mov r9, [ rsi + 0x0 ]; load m64 x6 to register64
adcx r10, r11
adcx rcx, rax
mov rax, rdx; preserving value of x70 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r11, r13, r9; x18, x17<- x6 * arg1[0]
adcx r12, r15
adcx r8, rbp
mov rdx, 0x100000001 ; moving imm to reg
mulx rbp, r15, r13; _, x30<- x17 * 0x100000001
adc rax, 0x0
mov rbp, rdx; preserving value of 0x100000001 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov [ rsp + 0x8 ], rax; spilling x91 to mem
mulx rdi, rax, r9; x16, x15<- x6 * arg1[1]
mov rdx, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x10 ], r8; spilling x89 to mem
mulx rbp, r8, r15; x41, x40<- x30 * 0xffffffff00000000
mov rdx, 0xffffffff ; moving imm to reg
mov [ rsp + 0x18 ], r12; spilling x87 to mem
mov [ rsp + 0x20 ], rcx; spilling x85 to mem
mulx r12, rcx, r15; x43, x42<- x30 * 0xffffffff
test al, al
adox rcx, r13
adcx r8, r12
setc cl; spill CF x45 to reg (rcx)
clc;
adcx rax, r11
adox r8, rax
seto r11b; spill OF x58 to reg (r11)
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, r8
mov r12, rdx; preserving value of 0xffffffff into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx rax, r8, r9; x14, x13<- x6 * arg1[2]
mov rdx, 0x100000001 ; moving imm to reg
mulx r13, r12, r14; _, x106<- x92 * 0x100000001
mov r13, 0xffffffff ; moving imm to reg
xchg rdx, r13; 0xffffffff, swapping with 0x100000001, which is currently in rdx
mov [ rsp + 0x28 ], r10; spilling x83 to mem
mulx r13, r10, r12; x119, x118<- x106 * 0xffffffff
adcx r8, rdi
seto dil; spill OF x93 to reg (rdi)
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r10, r14
mov r10, 0xfffffffffffffffe ; moving imm to reg
mov rdx, r10; 0xfffffffffffffffe to rdx
mulx r10, r14, r15; x39, x38<- x30 * 0xfffffffffffffffe
seto dl; spill OF x132 to reg (rdx)
mov [ rsp + 0x30 ], r10; spilling x39 to mem
mov r10, -0x1 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r10, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r10; loading flag
adox rbp, r14
seto cl; spill OF x47 to reg (rcx)
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, r14; loading flag
adox r8, rbp
setc r11b; spill CF x22 to reg (r11)
clc;
movzx rdi, dil
adcx rdi, r14; loading flag
adcx r8, rbx
mov rbx, 0xffffffff00000000 ; moving imm to reg
xchg rdx, rbx; 0xffffffff00000000, swapping with x132, which is currently in rdx
mulx rdi, rbp, r12; x117, x116<- x106 * 0xffffffff00000000
mov r10, [ rsi + 0x10 ]; load m64 x2 to register64
seto r14b; spill OF x60 to reg (r14)
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, r13
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x38 ], rdi; spilling x117 to mem
mulx r13, rdi, r10; x157, x156<- x2 * arg1[0]
seto dl; spill OF x121 to reg (rdx)
mov [ rsp + 0x40 ], r13; spilling x157 to mem
mov r13, -0x1 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r13, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, r13; loading flag
adox r8, rbp
setc bl; spill CF x95 to reg (rbx)
clc;
adcx rdi, r8
mov rbp, 0x100000001 ; moving imm to reg
xchg rdx, rbp; 0x100000001, swapping with x121, which is currently in rdx
mulx r8, r13, rdi; _, x183<- x169 * 0x100000001
mov r8, rdx; preserving value of 0x100000001 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov byte [ rsp + 0x48 ], bpl; spilling byte x121 to mem
mov byte [ rsp + 0x50 ], bl; spilling byte x95 to mem
mulx rbp, rbx, r9; x12, x11<- x6 * arg1[3]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x58 ], rbp; spilling x12 to mem
mulx r8, rbp, r15; x37, x36<- x30 * 0xffffffffffffffff
mov rdx, 0xffffffff ; moving imm to reg
mov [ rsp + 0x60 ], r8; spilling x37 to mem
mov byte [ rsp + 0x68 ], r14b; spilling byte x60 to mem
mulx r8, r14, r13; x196, x195<- x183 * 0xffffffff
setc dl; spill CF x170 to reg (rdx)
clc;
mov [ rsp + 0x70 ], r8; spilling x196 to mem
mov r8, -0x1 ; moving imm to reg
movzx r11, r11b
adcx r11, r8; loading flag
adcx rax, rbx
setc r11b; spill CF x24 to reg (r11)
clc;
movzx rcx, cl
adcx rcx, r8; loading flag
adcx rbp, [ rsp + 0x30 ]
setc cl; spill CF x49 to reg (rcx)
clc;
adcx r14, rdi
setc r14b; spill CF x209 to reg (r14)
movzx rdi, byte [ rsp + 0x68 ]; load byte memx60 to register64
clc;
adcx rdi, r8; loading flag
adcx rax, rbp
mov rdi, 0xfffffffffffffffe ; moving imm to reg
xchg rdx, r12; x106, swapping with x170, which is currently in rdx
mulx rbx, rbp, rdi; x115, x114<- x106 * 0xfffffffffffffffe
setc r8b; spill CF x62 to reg (r8)
movzx rdi, byte [ rsp + 0x50 ]; load byte memx95 to register64
clc;
mov [ rsp + 0x78 ], rbx; spilling x115 to mem
mov rbx, -0x1 ; moving imm to reg
adcx rdi, rbx; loading flag
adcx rax, [ rsp + 0x28 ]
mov rdi, rdx; preserving value of x106 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov byte [ rsp + 0x80 ], r8b; spilling byte x62 to mem
mulx rbx, r8, r10; x155, x154<- x2 * arg1[1]
setc dl; spill CF x97 to reg (rdx)
mov [ rsp + 0x88 ], rbx; spilling x155 to mem
movzx rbx, byte [ rsp + 0x48 ]; load byte memx121 to register64
clc;
mov byte [ rsp + 0x90 ], cl; spilling byte x49 to mem
mov rcx, -0x1 ; moving imm to reg
adcx rbx, rcx; loading flag
adcx rbp, [ rsp + 0x38 ]
adox rbp, rax
seto bl; spill OF x136 to reg (rbx)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r8, [ rsp + 0x40 ]
seto al; spill OF x159 to reg (rax)
dec rcx; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r12, r12b
adox r12, rcx; loading flag
adox rbp, r8
mov r12b, dl; preserving value of x97 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r8, rcx, r9; x10, x9<- x6 * arg1[4]
mov rdx, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x98 ], r8; spilling x10 to mem
mov byte [ rsp + 0xa0 ], al; spilling byte x159 to mem
mulx r8, rax, r13; x194, x193<- x183 * 0xffffffff00000000
setc dl; spill CF x123 to reg (rdx)
clc;
adcx rax, [ rsp + 0x70 ]
mov [ rsp + 0xa8 ], r8; spilling x194 to mem
seto r8b; spill OF x172 to reg (r8)
mov byte [ rsp + 0xb0 ], bl; spilling byte x136 to mem
mov rbx, -0x1 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbx, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, rbx; loading flag
adox rcx, [ rsp + 0x58 ]
setc r11b; spill CF x198 to reg (r11)
clc;
movzx r14, r14b
adcx r14, rbx; loading flag
adcx rbp, rax
mov r14, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r15; x30, swapping with x123, which is currently in rdx
mulx rax, rbx, r14; x35, x34<- x30 * 0xffffffffffffffff
setc r14b; spill CF x211 to reg (r14)
mov [ rsp + 0xb8 ], rbp; spilling x210 to mem
movzx rbp, byte [ rsp + 0x90 ]; load byte memx49 to register64
clc;
mov [ rsp + 0xc0 ], rax; spilling x35 to mem
mov rax, -0x1 ; moving imm to reg
adcx rbp, rax; loading flag
adcx rbx, [ rsp + 0x60 ]
seto bpl; spill OF x26 to reg (rbp)
movzx rax, byte [ rsp + 0x80 ]; load byte memx62 to register64
mov byte [ rsp + 0xc8 ], r14b; spilling byte x211 to mem
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rax, r14; loading flag
adox rcx, rbx
setc al; spill CF x51 to reg (rax)
clc;
movzx r12, r12b
adcx r12, r14; loading flag
adcx rcx, [ rsp + 0x20 ]
mov r12, rdx; preserving value of x30 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx rbx, r14, r10; x153, x152<- x2 * arg1[2]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0xd0 ], rbx; spilling x153 to mem
mov byte [ rsp + 0xd8 ], bpl; spilling byte x26 to mem
mulx rbx, rbp, rdi; x113, x112<- x106 * 0xffffffffffffffff
seto dl; spill OF x64 to reg (rdx)
mov [ rsp + 0xe0 ], rbx; spilling x113 to mem
mov rbx, -0x1 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbx, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, rbx; loading flag
adox rbp, [ rsp + 0x78 ]
setc r15b; spill CF x99 to reg (r15)
movzx rbx, byte [ rsp + 0xb0 ]; load byte memx136 to register64
clc;
mov byte [ rsp + 0xe8 ], dl; spilling byte x64 to mem
mov rdx, -0x1 ; moving imm to reg
adcx rbx, rdx; loading flag
adcx rcx, rbp
mov rbx, 0xfffffffffffffffe ; moving imm to reg
mov rdx, r13; x183 to rdx
mulx r13, rbp, rbx; x192, x191<- x183 * 0xfffffffffffffffe
setc bl; spill CF x138 to reg (rbx)
mov [ rsp + 0xf0 ], r13; spilling x192 to mem
movzx r13, byte [ rsp + 0xa0 ]; load byte memx159 to register64
clc;
mov byte [ rsp + 0xf8 ], r15b; spilling byte x99 to mem
mov r15, -0x1 ; moving imm to reg
adcx r13, r15; loading flag
adcx r14, [ rsp + 0x88 ]
setc r13b; spill CF x161 to reg (r13)
clc;
movzx r11, r11b
adcx r11, r15; loading flag
adcx rbp, [ rsp + 0xa8 ]
setc r11b; spill CF x200 to reg (r11)
clc;
movzx r8, r8b
adcx r8, r15; loading flag
adcx rcx, r14
setc r8b; spill CF x174 to reg (r8)
movzx r14, byte [ rsp + 0xc8 ]; load byte memx211 to register64
clc;
adcx r14, r15; loading flag
adcx rcx, rbp
mov r14, rdx; preserving value of x183 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx r9, rbp, r9; x8, x7<- x6 * arg1[5]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mulx r12, r15, r12; x33, x32<- x30 * 0xffffffffffffffff
setc dl; spill CF x213 to reg (rdx)
clc;
mov [ rsp + 0x100 ], rcx; spilling x212 to mem
mov rcx, -0x1 ; moving imm to reg
movzx rax, al
adcx rax, rcx; loading flag
adcx r15, [ rsp + 0xc0 ]
setc al; spill CF x53 to reg (rax)
movzx rcx, byte [ rsp + 0xd8 ]; load byte memx26 to register64
clc;
mov [ rsp + 0x108 ], r12; spilling x33 to mem
mov r12, -0x1 ; moving imm to reg
adcx rcx, r12; loading flag
adcx rbp, [ rsp + 0x98 ]
mov rcx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rcx; 0xffffffffffffffff, swapping with x213, which is currently in rdx
mov byte [ rsp + 0x110 ], al; spilling byte x53 to mem
mulx r12, rax, rdi; x111, x110<- x106 * 0xffffffffffffffff
setc dl; spill CF x28 to reg (rdx)
mov [ rsp + 0x118 ], r12; spilling x111 to mem
movzx r12, byte [ rsp + 0xe8 ]; load byte memx64 to register64
clc;
mov [ rsp + 0x120 ], r9; spilling x8 to mem
mov r9, -0x1 ; moving imm to reg
adcx r12, r9; loading flag
adcx rbp, r15
mov r12b, dl; preserving value of x28 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx r15, r9, r10; x151, x150<- x2 * arg1[3]
seto dl; spill OF x125 to reg (rdx)
mov [ rsp + 0x128 ], r15; spilling x151 to mem
movzx r15, byte [ rsp + 0xf8 ]; load byte memx99 to register64
mov byte [ rsp + 0x130 ], r12b; spilling byte x28 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, r12; loading flag
adox rbp, [ rsp + 0x18 ]
seto r15b; spill OF x101 to reg (r15)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
movzx rdx, dl
adox rdx, r12; loading flag
adox rax, [ rsp + 0xe0 ]
setc dl; spill CF x66 to reg (rdx)
clc;
movzx r13, r13b
adcx r13, r12; loading flag
adcx r9, [ rsp + 0xd0 ]
setc r13b; spill CF x163 to reg (r13)
clc;
movzx rbx, bl
adcx rbx, r12; loading flag
adcx rbp, rax
mov rbx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r14; x183, swapping with x66, which is currently in rdx
mulx rax, r12, rbx; x190, x189<- x183 * 0xffffffffffffffff
setc bl; spill CF x140 to reg (rbx)
clc;
mov [ rsp + 0x138 ], rax; spilling x190 to mem
mov rax, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, rax; loading flag
adcx rbp, r9
seto r8b; spill OF x127 to reg (r8)
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, r9; loading flag
adox r12, [ rsp + 0xf0 ]
seto r11b; spill OF x202 to reg (r11)
inc r9; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov rax, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, rax; loading flag
adox rbp, r12
movzx rcx, byte [ rsp + 0x130 ]; x29, copying x28 here, cause x28 is needed in a reg for other than x29, namely all: , x29, size: 1
mov r12, [ rsp + 0x120 ]; load m64 x8 to register64
lea rcx, [ rcx + r12 ]; r8/64 + m8
movzx r12, byte [ rsp + 0x110 ]; x54, copying x53 here, cause x53 is needed in a reg for other than x54, namely all: , x54, size: 1
mov r9, [ rsp + 0x108 ]; load m64 x33 to register64
lea r12, [ r12 + r9 ]; r8/64 + m8
setc r9b; spill CF x176 to reg (r9)
clc;
movzx r14, r14b
adcx r14, rax; loading flag
adcx rcx, r12
mov r14, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r14; 0xffffffffffffffff, swapping with x183, which is currently in rdx
mulx rdi, r12, rdi; x109, x108<- x106 * 0xffffffffffffffff
seto al; spill OF x215 to reg (rax)
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r8, r8b
adox r8, rdx; loading flag
adox r12, [ rsp + 0x118 ]
mov rdx, r10; x2 to rdx
mulx r10, r8, [ rsi + 0x20 ]; x149, x148<- x2 * arg1[4]
mov [ rsp + 0x140 ], rbp; spilling x214 to mem
setc bpl; spill CF x68 to reg (rbp)
clc;
mov [ rsp + 0x148 ], r10; spilling x149 to mem
mov r10, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, r10; loading flag
adcx rcx, [ rsp + 0x10 ]
setc r15b; spill CF x103 to reg (r15)
clc;
movzx r13, r13b
adcx r13, r10; loading flag
adcx r8, [ rsp + 0x128 ]
seto r13b; spill OF x129 to reg (r13)
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r10, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, r10; loading flag
adox rcx, r12
mov rbx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r14; x183, swapping with x2, which is currently in rdx
mulx r12, r10, rbx; x188, x187<- x183 * 0xffffffffffffffff
seto bl; spill OF x142 to reg (rbx)
mov [ rsp + 0x150 ], r12; spilling x188 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r9, r9b
adox r9, r12; loading flag
adox rcx, r8
seto r9b; spill OF x178 to reg (r9)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, r8; loading flag
adox r10, [ rsp + 0x138 ]
setc r11b; spill CF x165 to reg (r11)
clc;
movzx rax, al
adcx rax, r8; loading flag
adcx rcx, r10
movzx rax, r13b; x130, copying x129 here, cause x129 is needed in a reg for other than x130, namely all: , x130, size: 1
lea rax, [ rax + rdi ]
mov rdi, 0xffffffffffffffff ; moving imm to reg
mulx rdx, r13, rdi; x186, x185<- x183 * 0xffffffffffffffff
movzx r10, bpl; x104, copying x68 here, cause x68 is needed in a reg for other than x104, namely all: , x104--x105, size: 1
setc r12b; spill CF x217 to reg (r12)
clc;
movzx r15, r15b
adcx r15, r8; loading flag
adcx r10, [ rsp + 0x8 ]
setc bpl; spill CF x105 to reg (rbp)
clc;
movzx rbx, bl
adcx rbx, r8; loading flag
adcx r10, rax
movzx r15, bpl; x145, copying x105 here, cause x105 is needed in a reg for other than x145, namely all: , x145, size: 1
mov rbx, 0x0 ; moving imm to reg
adcx r15, rbx
mov rax, [ rsp + 0x150 ]; x205, copying x188 here, cause x188 is needed in a reg for other than x205, namely all: , x205--x206, size: 1
adox rax, r13
mov r13, rdx; preserving value of x186 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx r14, rbp, r14; x147, x146<- x2 * arg1[5]
clc;
movzx r11, r11b
adcx r11, r8; loading flag
adcx rbp, [ rsp + 0x148 ]
adcx r14, rbx
clc;
movzx r9, r9b
adcx r9, r8; loading flag
adcx r10, rbp
seto dl; spill OF x206 to reg (rdx)
dec rbx; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx r12, r12b
adox r12, rbx; loading flag
adox r10, rax
movzx r8, dl; x207, copying x206 here, cause x206 is needed in a reg for other than x207, namely all: , x207, size: 1
lea r8, [ r8 + r13 ]
adcx r14, r15
adox r8, r14
mov r11, [ rsi + 0x18 ]; load m64 x3 to register64
seto r9b; spill OF x222 to reg (r9)
adc r9b, 0x0
movzx r9, r9b
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r12, r13, r11; x234, x233<- x3 * arg1[0]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r15, rax, r11; x232, x231<- x3 * arg1[1]
adox r13, [ rsp + 0xb8 ]
adcx rax, r12
mov rdx, 0x100000001 ; moving imm to reg
mulx rbp, r14, r13; _, x260<- x246 * 0x100000001
mov rbp, [ rsp + 0x100 ]; x248, copying x212 here, cause x212 is needed in a reg for other than x248, namely all: , x248--x249, size: 1
adox rbp, rax
mov r12, 0xffffffff ; moving imm to reg
xchg rdx, r14; x260, swapping with 0x100000001, which is currently in rdx
mulx rax, rbx, r12; x273, x272<- x260 * 0xffffffff
setc r12b; spill CF x236 to reg (r12)
clc;
adcx rbx, r13
mov rbx, 0xffffffff00000000 ; moving imm to reg
mulx r13, r14, rbx; x271, x270<- x260 * 0xffffffff00000000
mov rdi, rdx; preserving value of x260 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov byte [ rsp + 0x158 ], r9b; spilling byte x222 to mem
mulx rbx, r9, r11; x230, x229<- x3 * arg1[2]
seto dl; spill OF x249 to reg (rdx)
mov [ rsp + 0x160 ], r8; spilling x220 to mem
mov r8, 0x0 ; moving imm to reg
dec r8; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r12, r12b
adox r12, r8; loading flag
adox r15, r9
seto r12b; spill OF x238 to reg (r12)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r14, rax
seto al; spill OF x275 to reg (rax)
dec r8; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx rdx, dl
adox rdx, r8; loading flag
adox r15, [ rsp + 0x140 ]
mov rdx, 0xfffffffffffffffe ; moving imm to reg
mulx r9, r8, rdi; x269, x268<- x260 * 0xfffffffffffffffe
adcx r14, rbp
seto bpl; spill OF x251 to reg (rbp)
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
movzx rax, al
adox rax, rdx; loading flag
adox r13, r8
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rax, r8, r11; x228, x227<- x3 * arg1[3]
adcx r13, r15
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x168 ], r13; spilling x289 to mem
mulx r15, r13, rdi; x267, x266<- x260 * 0xffffffffffffffff
setc dl; spill CF x290 to reg (rdx)
clc;
mov [ rsp + 0x170 ], r14; spilling x287 to mem
mov r14, -0x1 ; moving imm to reg
movzx r12, r12b
adcx r12, r14; loading flag
adcx rbx, r8
adox r13, r9
seto r12b; spill OF x279 to reg (r12)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, r9; loading flag
adox rcx, rbx
seto bpl; spill OF x253 to reg (rbp)
inc r9; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov r14, -0x1 ; moving imm to reg
movzx rdx, dl
adox rdx, r14; loading flag
adox rcx, r13
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r8, rbx, r11; x226, x225<- x3 * arg1[4]
adcx rbx, rax
mov rdx, 0xffffffffffffffff ; moving imm to reg
mulx rax, r13, rdi; x265, x264<- x260 * 0xffffffffffffffff
seto r9b; spill OF x292 to reg (r9)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, r14; loading flag
adox r10, rbx
mov rbp, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx r11, rbx, r11; x224, x223<- x3 * arg1[5]
seto dl; spill OF x255 to reg (rdx)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, r14; loading flag
adox r15, r13
adcx rbx, r8
seto r12b; spill OF x281 to reg (r12)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, r8; loading flag
adox r10, r15
xchg rdx, rbp; 0xffffffffffffffff, swapping with x255, which is currently in rdx
mulx rdi, r9, rdi; x263, x262<- x260 * 0xffffffffffffffff
adcx r11, r14
clc;
movzx rbp, bpl
adcx rbp, r8; loading flag
adcx rbx, [ rsp + 0x160 ]
movzx r13, byte [ rsp + 0x158 ]; x258, copying x222 here, cause x222 is needed in a reg for other than x258, namely all: , x258--x259, size: 1
adcx r13, r11
setc bpl; spill CF x259 to reg (rbp)
clc;
movzx r12, r12b
adcx r12, r8; loading flag
adcx rax, r9
mov r15, [ rsi + 0x20 ]; load m64 x4 to register64
adcx rdi, r14
adox rax, rbx
mov r12, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r9, r11, r15; x311, x310<- x4 * arg1[0]
adox rdi, r13
movzx rdx, bpl; x299, copying x259 here, cause x259 is needed in a reg for other than x299, namely all: , x299, size: 1
adox rdx, r14
xor rbx, rbx
adox r11, [ rsp + 0x170 ]
mov r14, rdx; preserving value of x299 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx rbp, r13, r15; x309, x308<- x4 * arg1[1]
mov rdx, 0x100000001 ; moving imm to reg
mulx rbx, r8, r11; _, x337<- x323 * 0x100000001
mov rbx, 0xffffffff ; moving imm to reg
xchg rdx, r8; x337, swapping with 0x100000001, which is currently in rdx
mulx r8, r12, rbx; x350, x349<- x337 * 0xffffffff
mov rbx, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x178 ], r14; spilling x299 to mem
mov [ rsp + 0x180 ], rdi; spilling x297 to mem
mulx r14, rdi, rbx; x348, x347<- x337 * 0xffffffff00000000
adcx r12, r11
setc r12b; spill CF x363 to reg (r12)
clc;
adcx r13, r9
mov r9, [ rsp + 0x168 ]; x325, copying x289 here, cause x289 is needed in a reg for other than x325, namely all: , x325--x326, size: 1
adox r9, r13
mov r11, [ rsi + 0x28 ]; load m64 x5 to register64
setc r13b; spill CF x313 to reg (r13)
clc;
adcx rdi, r8
setc r8b; spill CF x352 to reg (r8)
clc;
mov rbx, -0x1 ; moving imm to reg
movzx r12, r12b
adcx r12, rbx; loading flag
adcx r9, rdi
mov r12, rdx; preserving value of x337 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx rdi, rbx, r11; x388, x387<- x5 * arg1[0]
setc dl; spill CF x365 to reg (rdx)
clc;
adcx rbx, r9
mov r9b, dl; preserving value of x365 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x188 ], rax; spilling x295 to mem
mov [ rsp + 0x190 ], r10; spilling x293 to mem
mulx rax, r10, r15; x307, x306<- x4 * arg1[2]
mov rdx, 0x100000001 ; moving imm to reg
mov [ rsp + 0x198 ], rax; spilling x307 to mem
mov [ rsp + 0x1a0 ], rdi; spilling x388 to mem
mulx rax, rdi, rbx; _, x414<- x400 * 0x100000001
mov rax, 0xffffffff ; moving imm to reg
xchg rdx, rdi; x414, swapping with 0x100000001, which is currently in rdx
mov byte [ rsp + 0x1a8 ], r9b; spilling byte x365 to mem
mulx rdi, r9, rax; x427, x426<- x414 * 0xffffffff
setc al; spill CF x401 to reg (rax)
clc;
mov [ rsp + 0x1b0 ], rdi; spilling x427 to mem
mov rdi, -0x1 ; moving imm to reg
movzx r13, r13b
adcx r13, rdi; loading flag
adcx rbp, r10
adox rbp, rcx
seto cl; spill OF x328 to reg (rcx)
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r9, rbx
mov r9, 0xfffffffffffffffe ; moving imm to reg
xchg rdx, r12; x337, swapping with x414, which is currently in rdx
mulx r13, rbx, r9; x346, x345<- x337 * 0xfffffffffffffffe
seto r10b; spill OF x440 to reg (r10)
dec rdi; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r8, r8b
adox r8, rdi; loading flag
adox r14, rbx
seto r8b; spill OF x354 to reg (r8)
movzx rbx, byte [ rsp + 0x1a8 ]; load byte memx365 to register64
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdi, -0x1 ; moving imm to reg
adox rbx, rdi; loading flag
adox rbp, r14
mov rbx, rdx; preserving value of x337 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r14, rdi, r11; x386, x385<- x5 * arg1[1]
mov rdx, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x1b8 ], r14; spilling x386 to mem
mulx r9, r14, r12; x425, x424<- x414 * 0xffffffff00000000
seto dl; spill OF x367 to reg (rdx)
mov [ rsp + 0x1c0 ], r9; spilling x425 to mem
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rdi, [ rsp + 0x1a0 ]
seto r9b; spill OF x390 to reg (r9)
mov byte [ rsp + 0x1c8 ], dl; spilling byte x367 to mem
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
movzx rax, al
adox rax, rdx; loading flag
adox rbp, rdi
seto al; spill OF x403 to reg (rax)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r14, [ rsp + 0x1b0 ]
seto dil; spill OF x429 to reg (rdi)
dec rdx; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r10, r10b
adox r10, rdx; loading flag
adox rbp, r14
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r10, r14, r15; x305, x304<- x4 * arg1[3]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x1d0 ], rbp; spilling x441 to mem
mov [ rsp + 0x1d8 ], r10; spilling x305 to mem
mulx rbp, r10, rbx; x344, x343<- x337 * 0xffffffffffffffff
mov rdx, [ rsp + 0x198 ]; x316, copying x307 here, cause x307 is needed in a reg for other than x316, namely all: , x316--x317, size: 1
adcx rdx, r14
setc r14b; spill CF x317 to reg (r14)
clc;
mov [ rsp + 0x1e0 ], rbp; spilling x344 to mem
mov rbp, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, rbp; loading flag
adcx rdx, [ rsp + 0x190 ]
setc cl; spill CF x330 to reg (rcx)
clc;
movzx r8, r8b
adcx r8, rbp; loading flag
adcx r13, r10
mov r8, rdx; preserving value of x329 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r10, rbp, r11; x384, x383<- x5 * arg1[2]
setc dl; spill CF x356 to reg (rdx)
mov [ rsp + 0x1e8 ], r10; spilling x384 to mem
movzx r10, byte [ rsp + 0x1c8 ]; load byte memx367 to register64
clc;
mov byte [ rsp + 0x1f0 ], cl; spilling byte x330 to mem
mov rcx, -0x1 ; moving imm to reg
adcx r10, rcx; loading flag
adcx r8, r13
setc r10b; spill CF x369 to reg (r10)
clc;
movzx r9, r9b
adcx r9, rcx; loading flag
adcx rbp, [ rsp + 0x1b8 ]
setc r9b; spill CF x392 to reg (r9)
clc;
movzx rax, al
adcx rax, rcx; loading flag
adcx r8, rbp
mov rax, 0xfffffffffffffffe ; moving imm to reg
xchg rdx, rax; 0xfffffffffffffffe, swapping with x356, which is currently in rdx
mulx r13, rbp, r12; x423, x422<- x414 * 0xfffffffffffffffe
setc cl; spill CF x405 to reg (rcx)
clc;
mov rdx, -0x1 ; moving imm to reg
movzx rdi, dil
adcx rdi, rdx; loading flag
adcx rbp, [ rsp + 0x1c0 ]
adox rbp, r8
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx rdi, r8, r15; x303, x302<- x4 * arg1[4]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x1f8 ], rbp; spilling x443 to mem
mov [ rsp + 0x200 ], rdi; spilling x303 to mem
mulx rbp, rdi, rbx; x342, x341<- x337 * 0xffffffffffffffff
seto dl; spill OF x444 to reg (rdx)
mov [ rsp + 0x208 ], rbp; spilling x342 to mem
mov rbp, -0x1 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
movzx rax, al
adox rax, rbp; loading flag
adox rdi, [ rsp + 0x1e0 ]
seto al; spill OF x358 to reg (rax)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, rbp; loading flag
adox r8, [ rsp + 0x1d8 ]
seto r14b; spill OF x319 to reg (r14)
movzx rbp, byte [ rsp + 0x1f0 ]; load byte memx330 to register64
mov byte [ rsp + 0x210 ], al; spilling byte x358 to mem
mov rax, 0x0 ; moving imm to reg
dec rax; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbp, rax; loading flag
adox r8, [ rsp + 0x188 ]
seto bpl; spill OF x332 to reg (rbp)
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rax, -0x1 ; moving imm to reg
movzx r10, r10b
adox r10, rax; loading flag
adox r8, rdi
mov r10b, dl; preserving value of x444 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx rdi, rax, r11; x382, x381<- x5 * arg1[3]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x218 ], rdi; spilling x382 to mem
mov byte [ rsp + 0x220 ], bpl; spilling byte x332 to mem
mulx rdi, rbp, r12; x421, x420<- x414 * 0xffffffffffffffff
seto dl; spill OF x371 to reg (rdx)
mov [ rsp + 0x228 ], rdi; spilling x421 to mem
mov rdi, 0x0 ; moving imm to reg
dec rdi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r9, r9b
adox r9, rdi; loading flag
adox rax, [ rsp + 0x1e8 ]
seto r9b; spill OF x394 to reg (r9)
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdi, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, rdi; loading flag
adox r8, rax
mov cl, dl; preserving value of x371 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx r15, rax, r15; x301, x300<- x4 * arg1[5]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mulx rbx, rdi, rbx; x340, x339<- x337 * 0xffffffffffffffff
xchg rdx, r11; x5, swapping with 0xffffffffffffffff, which is currently in rdx
mov [ rsp + 0x230 ], rbx; spilling x340 to mem
mulx r11, rbx, [ rsi + 0x20 ]; x380, x379<- x5 * arg1[4]
adcx rbp, r13
setc r13b; spill CF x433 to reg (r13)
clc;
mov [ rsp + 0x238 ], r11; spilling x380 to mem
mov r11, -0x1 ; moving imm to reg
movzx r10, r10b
adcx r10, r11; loading flag
adcx r8, rbp
setc r10b; spill CF x446 to reg (r10)
clc;
movzx r14, r14b
adcx r14, r11; loading flag
adcx rax, [ rsp + 0x200 ]
setc r14b; spill CF x321 to reg (r14)
movzx rbp, byte [ rsp + 0x220 ]; load byte memx332 to register64
clc;
adcx rbp, r11; loading flag
adcx rax, [ rsp + 0x180 ]
setc bpl; spill CF x334 to reg (rbp)
movzx r11, byte [ rsp + 0x210 ]; load byte memx358 to register64
clc;
mov [ rsp + 0x240 ], r8; spilling x445 to mem
mov r8, -0x1 ; moving imm to reg
adcx r11, r8; loading flag
adcx rdi, [ rsp + 0x208 ]
setc r11b; spill CF x360 to reg (r11)
clc;
movzx rcx, cl
adcx rcx, r8; loading flag
adcx rax, rdi
setc cl; spill CF x373 to reg (rcx)
clc;
movzx r9, r9b
adcx r9, r8; loading flag
adcx rbx, [ rsp + 0x218 ]
adox rbx, rax
mov r9, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r9; 0xffffffffffffffff, swapping with x5, which is currently in rdx
mulx rdi, rax, r12; x419, x418<- x414 * 0xffffffffffffffff
movzx r8, r14b; x322, copying x321 here, cause x321 is needed in a reg for other than x322, namely all: , x322, size: 1
lea r8, [ r8 + r15 ]
setc r15b; spill CF x396 to reg (r15)
clc;
mov r14, -0x1 ; moving imm to reg
movzx rbp, bpl
adcx rbp, r14; loading flag
adcx r8, [ rsp + 0x178 ]
setc bpl; spill CF x336 to reg (rbp)
clc;
movzx r13, r13b
adcx r13, r14; loading flag
adcx rax, [ rsp + 0x228 ]
mov r13, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx r9, r14, r9; x378, x377<- x5 * arg1[5]
movzx rdx, r11b; x361, copying x360 here, cause x360 is needed in a reg for other than x361, namely all: , x361, size: 1
mov r13, [ rsp + 0x230 ]; load m64 x340 to register64
lea rdx, [ rdx + r13 ]; r8/64 + m8
seto r13b; spill OF x409 to reg (r13)
mov r11, 0x0 ; moving imm to reg
dec r11; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rcx, cl
adox rcx, r11; loading flag
adox r8, rdx
seto cl; spill OF x375 to reg (rcx)
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
movzx r10, r10b
adox r10, rdx; loading flag
adox rbx, rax
mov r10, 0xffffffffffffffff ; moving imm to reg
mov rdx, r12; x414 to rdx
mulx rdx, r12, r10; x417, x416<- x414 * 0xffffffffffffffff
movzx rax, cl; x376, copying x375 here, cause x375 is needed in a reg for other than x376, namely all: , x376, size: 1
movzx rbp, bpl
lea rax, [ rax + rbp ]
adcx r12, rdi
setc dil; spill CF x437 to reg (rdi)
clc;
mov rbp, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, rbp; loading flag
adcx r14, [ rsp + 0x238 ]
setc r15b; spill CF x398 to reg (r15)
clc;
movzx r13, r13b
adcx r13, rbp; loading flag
adcx r8, r14
movzx r13, dil; x438, copying x437 here, cause x437 is needed in a reg for other than x438, namely all: , x438, size: 1
lea r13, [ r13 + rdx ]
movzx rcx, r15b; x399, copying x398 here, cause x398 is needed in a reg for other than x399, namely all: , x399, size: 1
lea rcx, [ rcx + r9 ]
adcx rcx, rax
adox r12, r8
adox r13, rcx
seto r9b; spill OF x453 to reg (r9)
adc r9b, 0x0
movzx r9, r9b
mov rdx, [ rsp + 0x1d0 ]; x454, copying x441 here, cause x441 is needed in a reg for other than x454, namely all: , x468, x454--x455, size: 2
mov rax, 0xffffffff ; moving imm to reg
sub rdx, rax
mov rdi, [ rsp + 0x1f8 ]; x456, copying x443 here, cause x443 is needed in a reg for other than x456, namely all: , x456--x457, x469, size: 2
mov r14, 0xffffffff00000000 ; moving imm to reg
sbb rdi, r14
mov r15, [ rsp + 0x240 ]; x458, copying x445 here, cause x445 is needed in a reg for other than x458, namely all: , x470, x458--x459, size: 2
mov r8, 0xfffffffffffffffe ; moving imm to reg
sbb r15, r8
mov rcx, rbx; x460, copying x447 here, cause x447 is needed in a reg for other than x460, namely all: , x471, x460--x461, size: 2
sbb rcx, r10
mov r11, r12; x462, copying x449 here, cause x449 is needed in a reg for other than x462, namely all: , x472, x462--x463, size: 2
sbb r11, r10
mov rbp, r13; x464, copying x451 here, cause x451 is needed in a reg for other than x464, namely all: , x473, x464--x465, size: 2
sbb rbp, r10
movzx r8, r9b; _, copying x453 here, cause x453 is needed in a reg for other than _, namely all: , _--x467, size: 1
sbb r8, 0x00000000
cmovc rcx, rbx; if CF, x471<- x447 (nzVar)
cmovc r15, [ rsp + 0x240 ]; if CF, x470<- x445 (nzVar)
cmovc rbp, r13; if CF, x473<- x451 (nzVar)
mov r8, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r8 + 0x18 ], rcx; out1[3] = x471
cmovc r11, r12; if CF, x472<- x449 (nzVar)
mov [ r8 + 0x10 ], r15; out1[2] = x470
cmovc rdi, [ rsp + 0x1f8 ]; if CF, x469<- x443 (nzVar)
mov [ r8 + 0x20 ], r11; out1[4] = x472
mov [ r8 + 0x8 ], rdi; out1[1] = x469
cmovc rdx, [ rsp + 0x1d0 ]; if CF, x468<- x441 (nzVar)
mov [ r8 + 0x28 ], rbp; out1[5] = x473
mov [ r8 + 0x0 ], rdx; out1[0] = x468
mov rbx, [ rsp + 0x248 ]; restoring from stack
mov rbp, [ rsp + 0x250 ]; restoring from stack
mov r12, [ rsp + 0x258 ]; restoring from stack
mov r13, [ rsp + 0x260 ]; restoring from stack
mov r14, [ rsp + 0x268 ]; restoring from stack
mov r15, [ rsp + 0x270 ]; restoring from stack
add rsp, 0x278 
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; clocked at 1600 MHz
; first cyclecount 177.885, best 136.0561797752809, lastGood 136.5056179775281
; seed 4259079871647348 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4164361 ms / 60000 runs=> 69.40601666666667ms/run
; Time spent for assembling and measureing (initial batch_size=91, initial num_batches=101): 262222 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.0629681240411194
; number reverted permutation/ tried permutation: 29331 / 30178 =97.193%
; number reverted decision/ tried decision: 28510 / 29823 =95.597%