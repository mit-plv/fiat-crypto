SECTION .text
	GLOBAL mul_p434
mul_p434:
sub rsp, 0x3b0 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x380 ], rbx; saving to stack
mov [ rsp + 0x388 ], rbp; saving to stack
mov [ rsp + 0x390 ], r12; saving to stack
mov [ rsp + 0x398 ], r13; saving to stack
mov [ rsp + 0x3a0 ], r14; saving to stack
mov [ rsp + 0x3a8 ], r15; saving to stack
mov rax, [ rsi + 0x18 ]; load m64 x3 to register64
mov r10, [ rsi + 0x20 ]; load m64 x4 to register64
mov r11, [ rsi + 0x0 ]; load m64 x7 to register64
mov rbx, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x0 ]; saving arg2[0] in rdx.
mulx rbp, r12, r11; x21, x20<- x7 * arg2[0]
mov r13, 0xffffffffffffffff ; moving imm to reg
mov rdx, r13; 0xffffffffffffffff to rdx
mulx r13, r14, r12; x48, x47<- x20 * 0xffffffffffffffff
test al, al
adox r14, r12
mov r14, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ rbx + 0x8 ]; saving arg2[1] in rdx.
mulx r15, rcx, r11; x19, x18<- x7 * arg2[1]
adcx rcx, rbp
mov rdx, r12; x20 to rdx
mulx r12, r8, r14; x46, x45<- x20 * 0xffffffffffffffff
seto r9b; spill OF x63 to reg (r9)
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, r13
setc r13b; spill CF x23 to reg (r13)
clc;
movzx r9, r9b
adcx r9, rbp; loading flag
adcx rcx, r8
mov r9, [ rsi + 0x8 ]; load m64 x1 to register64
mov r8, rdx; preserving value of x20 into a new reg
mov rdx, [ rbx + 0x0 ]; saving arg2[0] in rdx.
mulx rbp, r14, r9; x91, x90<- x1 * arg2[0]
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
setc dil; spill CF x65 to reg (rdi)
clc;
adcx r14, rcx
mov rcx, 0xffffffffffffffff ; moving imm to reg
mov rdx, rcx; 0xffffffffffffffff to rdx
mov [ rsp + 0x8 ], r10; spilling x4 to mem
mulx rcx, r10, r14; x134, x133<- x105 * 0xffffffffffffffff
setc dl; spill CF x106 to reg (rdx)
clc;
adcx r10, r14
mov r10b, dl; preserving value of x106 into a new reg
mov rdx, [ rbx + 0x10 ]; saving arg2[2] in rdx.
mov [ rsp + 0x10 ], rax; spilling x3 to mem
mov [ rsp + 0x18 ], rcx; spilling x134 to mem
mulx rax, rcx, r11; x17, x16<- x7 * arg2[2]
mov [ rsp + 0x20 ], rax; spilling x17 to mem
setc al; spill CF x149 to reg (rax)
clc;
mov byte [ rsp + 0x28 ], r10b; spilling byte x106 to mem
mov r10, -0x1 ; moving imm to reg
movzx r13, r13b
adcx r13, r10; loading flag
adcx r15, rcx
mov r13, 0xffffffffffffffff ; moving imm to reg
mov rdx, r8; x20 to rdx
mulx r8, rcx, r13; x44, x43<- x20 * 0xffffffffffffffff
adox rcx, r12
mov r12, rdx; preserving value of x20 into a new reg
mov rdx, [ rbx + 0x8 ]; saving arg2[1] in rdx.
mulx r10, r13, r9; x89, x88<- x1 * arg2[1]
mov [ rsp + 0x30 ], r10; spilling x89 to mem
seto r10b; spill OF x52 to reg (r10)
mov [ rsp + 0x38 ], r8; spilling x44 to mem
mov r8, 0x0 ; moving imm to reg
dec r8; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rdi, dil
adox rdi, r8; loading flag
adox r15, rcx
seto dil; spill OF x67 to reg (rdi)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r13, rbp
mov rbp, 0xffffffffffffffff ; moving imm to reg
mov rdx, rbp; 0xffffffffffffffff to rdx
mulx rbp, rcx, r14; x132, x131<- x105 * 0xffffffffffffffff
seto r8b; spill OF x93 to reg (r8)
movzx rdx, byte [ rsp + 0x28 ]; load byte memx106 to register64
mov [ rsp + 0x40 ], rbp; spilling x132 to mem
mov rbp, 0x0 ; moving imm to reg
dec rbp; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rdx, rbp; loading flag
adox r15, r13
setc dl; spill CF x25 to reg (rdx)
clc;
adcx rcx, [ rsp + 0x18 ]
setc r13b; spill CF x136 to reg (r13)
clc;
movzx rax, al
adcx rax, rbp; loading flag
adcx r15, rcx
xchg rdx, r11; x7, swapping with x25, which is currently in rdx
mulx rax, rcx, [ rbx + 0x18 ]; x15, x14<- x7 * arg2[3]
mov rbp, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, r12; x20, swapping with x7, which is currently in rdx
mov [ rsp + 0x48 ], r15; spilling x150 to mem
mov [ rsp + 0x50 ], rax; spilling x15 to mem
mulx r15, rax, rbp; x42, x41<- x20 * 0xfdc1767ae2ffffff
seto bpl; spill OF x108 to reg (rbp)
mov [ rsp + 0x58 ], rsi; spilling arg1 to mem
mov rsi, 0x0 ; moving imm to reg
dec rsi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r10, r10b
adox r10, rsi; loading flag
adox rax, [ rsp + 0x38 ]
seto r10b; spill OF x54 to reg (r10)
inc rsi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rsi, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, rsi; loading flag
adox rcx, [ rsp + 0x20 ]
seto r11b; spill OF x27 to reg (r11)
inc rsi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rsi, -0x1 ; moving imm to reg
movzx rdi, dil
adox rdi, rsi; loading flag
adox rcx, rax
xchg rdx, r9; x1, swapping with x20, which is currently in rdx
mulx rdi, rax, [ rbx + 0x10 ]; x87, x86<- x1 * arg2[2]
setc sil; spill CF x151 to reg (rsi)
clc;
mov [ rsp + 0x60 ], rdi; spilling x87 to mem
mov rdi, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, rdi; loading flag
adcx rax, [ rsp + 0x30 ]
seto r8b; spill OF x69 to reg (r8)
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdi, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, rdi; loading flag
adox rcx, rax
mov rbp, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r14; x105, swapping with x1, which is currently in rdx
mulx rax, rdi, rbp; x130, x129<- x105 * 0xffffffffffffffff
seto bpl; spill OF x110 to reg (rbp)
mov [ rsp + 0x68 ], rax; spilling x130 to mem
mov rax, 0x0 ; moving imm to reg
dec rax; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r13, r13b
adox r13, rax; loading flag
adox rdi, [ rsp + 0x40 ]
setc r13b; spill CF x95 to reg (r13)
clc;
movzx rsi, sil
adcx rsi, rax; loading flag
adcx rcx, rdi
mov rsi, rdx; preserving value of x105 into a new reg
mov rdx, [ rbx + 0x20 ]; saving arg2[4] in rdx.
mulx rdi, rax, r12; x13, x12<- x7 * arg2[4]
mov [ rsp + 0x70 ], rcx; spilling x152 to mem
mov rcx, 0x7bc65c783158aea3 ; moving imm to reg
mov rdx, r9; x20 to rdx
mov [ rsp + 0x78 ], rdi; spilling x13 to mem
mulx r9, rdi, rcx; x40, x39<- x20 * 0x7bc65c783158aea3
setc cl; spill CF x153 to reg (rcx)
clc;
mov [ rsp + 0x80 ], r9; spilling x40 to mem
mov r9, -0x1 ; moving imm to reg
movzx r11, r11b
adcx r11, r9; loading flag
adcx rax, [ rsp + 0x50 ]
setc r11b; spill CF x29 to reg (r11)
clc;
movzx r10, r10b
adcx r10, r9; loading flag
adcx r15, rdi
setc r10b; spill CF x56 to reg (r10)
clc;
movzx r8, r8b
adcx r8, r9; loading flag
adcx rax, r15
xchg rdx, r14; x1, swapping with x20, which is currently in rdx
mulx r8, rdi, [ rbx + 0x18 ]; x85, x84<- x1 * arg2[3]
seto r15b; spill OF x138 to reg (r15)
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, r9; loading flag
adox rdi, [ rsp + 0x60 ]
seto r13b; spill OF x97 to reg (r13)
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, r9; loading flag
adox rax, rdi
mov rbp, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, rsi; x105, swapping with x1, which is currently in rdx
mulx rdi, r9, rbp; x128, x127<- x105 * 0xfdc1767ae2ffffff
setc bpl; spill CF x71 to reg (rbp)
clc;
mov [ rsp + 0x88 ], rdi; spilling x128 to mem
mov rdi, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, rdi; loading flag
adcx r9, [ rsp + 0x68 ]
seto r15b; spill OF x112 to reg (r15)
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdi, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, rdi; loading flag
adox rax, r9
xchg rdx, r12; x7, swapping with x105, which is currently in rdx
mulx rcx, r9, [ rbx + 0x28 ]; x11, x10<- x7 * arg2[5]
seto dil; spill OF x155 to reg (rdi)
mov [ rsp + 0x90 ], rax; spilling x154 to mem
mov rax, -0x1 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rax, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, rax; loading flag
adox r9, [ rsp + 0x78 ]
mov r11, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, r14; x20, swapping with x7, which is currently in rdx
mov [ rsp + 0x98 ], rcx; spilling x11 to mem
mulx rax, rcx, r11; x38, x37<- x20 * 0x6cfc5fd681c52056
setc r11b; spill CF x140 to reg (r11)
clc;
mov [ rsp + 0xa0 ], rax; spilling x38 to mem
mov rax, -0x1 ; moving imm to reg
movzx r10, r10b
adcx r10, rax; loading flag
adcx rcx, [ rsp + 0x80 ]
seto r10b; spill OF x31 to reg (r10)
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rax, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, rax; loading flag
adox r9, rcx
xchg rdx, rsi; x1, swapping with x20, which is currently in rdx
mulx rbp, rcx, [ rbx + 0x20 ]; x83, x82<- x1 * arg2[4]
seto al; spill OF x73 to reg (rax)
mov [ rsp + 0xa8 ], rbp; spilling x83 to mem
mov rbp, -0x1 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, rbp; loading flag
adox r8, rcx
seto r13b; spill OF x99 to reg (r13)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rcx, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, rcx; loading flag
adox r9, r8
mov r15, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, r12; x105, swapping with x1, which is currently in rdx
mulx r8, rbp, r15; x126, x125<- x105 * 0x7bc65c783158aea3
setc cl; spill CF x58 to reg (rcx)
clc;
mov r15, -0x1 ; moving imm to reg
movzx r11, r11b
adcx r11, r15; loading flag
adcx rbp, [ rsp + 0x88 ]
setc r11b; spill CF x142 to reg (r11)
clc;
movzx rdi, dil
adcx rdi, r15; loading flag
adcx r9, rbp
mov rdi, rdx; preserving value of x105 into a new reg
mov rdx, [ rbx + 0x30 ]; saving arg2[6] in rdx.
mulx r14, rbp, r14; x9, x8<- x7 * arg2[6]
setc r15b; spill CF x157 to reg (r15)
clc;
mov [ rsp + 0xb0 ], r9; spilling x156 to mem
mov r9, -0x1 ; moving imm to reg
movzx r10, r10b
adcx r10, r9; loading flag
adcx rbp, [ rsp + 0x98 ]
mov r10, 0x2341f27177344 ; moving imm to reg
mov rdx, r10; 0x2341f27177344 to rdx
mulx rsi, r10, rsi; x36, x35<- x20 * 0x2341f27177344
seto r9b; spill OF x114 to reg (r9)
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, rdx; loading flag
adox r10, [ rsp + 0xa0 ]
setc cl; spill CF x33 to reg (rcx)
clc;
movzx rax, al
adcx rax, rdx; loading flag
adcx rbp, r10
mov rdx, r12; x1 to rdx
mulx r12, rax, [ rbx + 0x28 ]; x81, x80<- x1 * arg2[5]
seto r10b; spill OF x60 to reg (r10)
mov [ rsp + 0xb8 ], r12; spilling x81 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, r12; loading flag
adox rax, [ rsp + 0xa8 ]
seto r13b; spill OF x101 to reg (r13)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, r12; loading flag
adox rbp, rax
mov r9, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, rdi; x105, swapping with x1, which is currently in rdx
mulx rax, r12, r9; x124, x123<- x105 * 0x6cfc5fd681c52056
seto r9b; spill OF x116 to reg (r9)
mov [ rsp + 0xc0 ], rax; spilling x124 to mem
mov rax, 0x0 ; moving imm to reg
dec rax; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r11, r11b
adox r11, rax; loading flag
adox r8, r12
seto r11b; spill OF x144 to reg (r11)
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, r12; loading flag
adox rbp, r8
movzx r15, cl; x34, copying x33 here, cause x33 is needed in a reg for other than x34, namely all: , x34, size: 1
lea r15, [ r15 + r14 ]
movzx r14, r10b; x61, copying x60 here, cause x60 is needed in a reg for other than x61, namely all: , x61, size: 1
lea r14, [ r14 + rsi ]
adcx r14, r15
mov rcx, rdx; preserving value of x105 into a new reg
mov rdx, [ rbx + 0x30 ]; saving arg2[6] in rdx.
mulx rdi, rsi, rdi; x79, x78<- x1 * arg2[6]
setc r10b; spill CF x77 to reg (r10)
clc;
movzx r13, r13b
adcx r13, r12; loading flag
adcx rsi, [ rsp + 0xb8 ]
setc r13b; spill CF x103 to reg (r13)
clc;
movzx r9, r9b
adcx r9, r12; loading flag
adcx r14, rsi
mov r9, 0x2341f27177344 ; moving imm to reg
mov rdx, r9; 0x2341f27177344 to rdx
mulx rcx, r9, rcx; x122, x121<- x105 * 0x2341f27177344
seto r8b; spill OF x159 to reg (r8)
dec rax; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx r11, r11b
adox r11, rax; loading flag
adox r9, [ rsp + 0xc0 ]
seto r12b; spill OF x146 to reg (r12)
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r11, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, r11; loading flag
adox r14, r9
movzx r8, r13b; x104, copying x103 here, cause x103 is needed in a reg for other than x104, namely all: , x104, size: 1
lea r8, [ r8 + rdi ]
movzx r15, r10b; x119, copying x77 here, cause x77 is needed in a reg for other than x119, namely all: , x119--x120, size: 1
adcx r15, r8
movzx r10, r12b; x147, copying x146 here, cause x146 is needed in a reg for other than x147, namely all: , x147, size: 1
lea r10, [ r10 + rcx ]
adox r10, r15
seto dil; spill OF x164 to reg (rdi)
adc dil, 0x0
movzx rdi, dil
mov rsi, [ rsp + 0x58 ]; load m64 arg1 to register64
mov r13, [ rsi + 0x10 ]; load m64 x2 to register64
mov rcx, rdx; preserving value of 0x2341f27177344 into a new reg
mov rdx, [ rbx + 0x0 ]; saving arg2[0] in rdx.
mulx r9, r12, r13; x178, x177<- x2 * arg2[0]
adox r12, [ rsp + 0x48 ]
mov r8, 0xffffffffffffffff ; moving imm to reg
mov rdx, r8; 0xffffffffffffffff to rdx
mulx r8, r15, r12; x221, x220<- x192 * 0xffffffffffffffff
adcx r15, r12
mov r15, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ rbx + 0x8 ]; saving arg2[1] in rdx.
mulx rax, r11, r13; x176, x175<- x2 * arg2[1]
setc cl; spill CF x236 to reg (rcx)
clc;
adcx r11, r9
mov r9, [ rsp + 0x70 ]; x194, copying x152 here, cause x152 is needed in a reg for other than x194, namely all: , x194--x195, size: 1
adox r9, r11
mov rdx, r15; 0xffffffffffffffff to rdx
mulx r15, r11, r12; x219, x218<- x192 * 0xffffffffffffffff
seto dl; spill OF x195 to reg (rdx)
mov byte [ rsp + 0xc8 ], dil; spilling byte x164 to mem
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, r8
seto r8b; spill OF x223 to reg (r8)
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdi, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, rdi; loading flag
adox r9, r11
mov cl, dl; preserving value of x195 into a new reg
mov rdx, [ rbx + 0x10 ]; saving arg2[2] in rdx.
mulx r11, rdi, r13; x174, x173<- x2 * arg2[2]
adcx rdi, rax
mov rax, 0xffffffffffffffff ; moving imm to reg
mov rdx, r12; x192 to rdx
mov [ rsp + 0xd0 ], r9; spilling x237 to mem
mulx r12, r9, rax; x217, x216<- x192 * 0xffffffffffffffff
setc al; spill CF x182 to reg (rax)
clc;
mov [ rsp + 0xd8 ], r10; spilling x162 to mem
mov r10, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, r10; loading flag
adcx rdi, [ rsp + 0x90 ]
seto cl; spill OF x238 to reg (rcx)
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r10, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, r10; loading flag
adox r15, r9
seto r8b; spill OF x225 to reg (r8)
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r9; loading flag
adox rdi, r15
mov rcx, rdx; preserving value of x192 into a new reg
mov rdx, [ rbx + 0x18 ]; saving arg2[3] in rdx.
mulx r15, r10, r13; x172, x171<- x2 * arg2[3]
seto r9b; spill OF x240 to reg (r9)
mov [ rsp + 0xe0 ], rdi; spilling x239 to mem
mov rdi, 0x0 ; moving imm to reg
dec rdi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rax, al
adox rax, rdi; loading flag
adox r11, r10
mov rax, 0xfdc1767ae2ffffff ; moving imm to reg
mov rdx, rcx; x192 to rdx
mulx rcx, r10, rax; x215, x214<- x192 * 0xfdc1767ae2ffffff
mov rdi, [ rsp + 0xb0 ]; x198, copying x156 here, cause x156 is needed in a reg for other than x198, namely all: , x198--x199, size: 1
adcx rdi, r11
seto r11b; spill OF x184 to reg (r11)
mov rax, -0x1 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rax, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, rax; loading flag
adox r12, r10
seto r8b; spill OF x227 to reg (r8)
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r10, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, r10; loading flag
adox rdi, r12
mov r9, rdx; preserving value of x192 into a new reg
mov rdx, [ rbx + 0x20 ]; saving arg2[4] in rdx.
mulx r12, rax, r13; x170, x169<- x2 * arg2[4]
seto r10b; spill OF x242 to reg (r10)
mov [ rsp + 0xe8 ], rdi; spilling x241 to mem
mov rdi, 0x0 ; moving imm to reg
dec rdi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r11, r11b
adox r11, rdi; loading flag
adox r15, rax
adcx r15, rbp
mov rbp, 0x7bc65c783158aea3 ; moving imm to reg
mov rdx, r9; x192 to rdx
mulx r9, r11, rbp; x213, x212<- x192 * 0x7bc65c783158aea3
seto al; spill OF x186 to reg (rax)
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdi, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, rdi; loading flag
adox rcx, r11
setc r8b; spill CF x201 to reg (r8)
clc;
movzx r10, r10b
adcx r10, rdi; loading flag
adcx r15, rcx
mov r10, rdx; preserving value of x192 into a new reg
mov rdx, [ rbx + 0x28 ]; saving arg2[5] in rdx.
mulx r11, rcx, r13; x168, x167<- x2 * arg2[5]
seto dil; spill OF x229 to reg (rdi)
mov rbp, 0x0 ; moving imm to reg
dec rbp; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rax, al
adox rax, rbp; loading flag
adox r12, rcx
seto al; spill OF x188 to reg (rax)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rcx, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, rcx; loading flag
adox r14, r12
mov r8, 0x6cfc5fd681c52056 ; moving imm to reg
mov rdx, r8; 0x6cfc5fd681c52056 to rdx
mulx r8, r12, r10; x211, x210<- x192 * 0x6cfc5fd681c52056
setc bpl; spill CF x244 to reg (rbp)
clc;
movzx rdi, dil
adcx rdi, rcx; loading flag
adcx r9, r12
setc dil; spill CF x231 to reg (rdi)
clc;
movzx rbp, bpl
adcx rbp, rcx; loading flag
adcx r14, r9
mov rbp, rdx; preserving value of 0x6cfc5fd681c52056 into a new reg
mov rdx, [ rbx + 0x30 ]; saving arg2[6] in rdx.
mulx r13, r12, r13; x166, x165<- x2 * arg2[6]
setc r9b; spill CF x246 to reg (r9)
clc;
movzx rax, al
adcx rax, rcx; loading flag
adcx r11, r12
mov rax, [ rsp + 0xd8 ]; x204, copying x162 here, cause x162 is needed in a reg for other than x204, namely all: , x204--x205, size: 1
adox rax, r11
mov r12, 0x2341f27177344 ; moving imm to reg
mov rdx, r12; 0x2341f27177344 to rdx
mulx r10, r12, r10; x209, x208<- x192 * 0x2341f27177344
setc r11b; spill CF x190 to reg (r11)
clc;
movzx rdi, dil
adcx rdi, rcx; loading flag
adcx r8, r12
setc dil; spill CF x233 to reg (rdi)
clc;
movzx r9, r9b
adcx r9, rcx; loading flag
adcx rax, r8
movzx r9, r11b; x191, copying x190 here, cause x190 is needed in a reg for other than x191, namely all: , x191, size: 1
lea r9, [ r9 + r13 ]
movzx r13, byte [ rsp + 0xc8 ]; x206, copying x164 here, cause x164 is needed in a reg for other than x206, namely all: , x206--x207, size: 1
adox r13, r9
movzx r11, dil; x234, copying x233 here, cause x233 is needed in a reg for other than x234, namely all: , x234, size: 1
lea r11, [ r11 + r10 ]
adcx r11, r13
seto r10b; spill OF x251 to reg (r10)
adc r10b, 0x0
movzx r10, r10b
mov r12, rdx; preserving value of 0x2341f27177344 into a new reg
mov rdx, [ rbx + 0x8 ]; saving arg2[1] in rdx.
mulx r8, rdi, [ rsp + 0x10 ]; x263, x262<- x3 * arg2[1]
mov rdx, [ rsp + 0x10 ]; x3 to rdx
mulx r9, r13, [ rbx + 0x0 ]; x265, x264<- x3 * arg2[0]
mulx rcx, r12, [ rbx + 0x10 ]; x261, x260<- x3 * arg2[2]
adox rdi, r9
mulx r9, rbp, [ rbx + 0x18 ]; x259, x258<- x3 * arg2[3]
adox r12, r8
adox rbp, rcx
mulx r8, rcx, [ rbx + 0x20 ]; x257, x256<- x3 * arg2[4]
adox rcx, r9
mov byte [ rsp + 0xf0 ], r10b; spilling byte x251 to mem
mulx r9, r10, [ rbx + 0x28 ]; x255, x254<- x3 * arg2[5]
adox r10, r8
mulx rdx, r8, [ rbx + 0x30 ]; x253, x252<- x3 * arg2[6]
adox r8, r9
adcx r13, [ rsp + 0xd0 ]
mov r9, 0x0 ; moving imm to reg
adox rdx, r9
mov r9, [ rsp + 0xe0 ]; x281, copying x239 here, cause x239 is needed in a reg for other than x281, namely all: , x281--x282, size: 1
adcx r9, rdi
mov rdi, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rdi; 0xffffffffffffffff, swapping with x278, which is currently in rdx
mov [ rsp + 0xf8 ], rdi; spilling x278 to mem
mov [ rsp + 0x100 ], r8; spilling x276 to mem
mulx rdi, r8, r13; x308, x307<- x279 * 0xffffffffffffffff
mov [ rsp + 0x108 ], r11; spilling x249 to mem
mov [ rsp + 0x110 ], r10; spilling x274 to mem
mulx r11, r10, r13; x306, x305<- x279 * 0xffffffffffffffff
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, r13
seto r8b; spill OF x323 to reg (r8)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r10, rdi
mov rdi, [ rsp + 0xe8 ]; x283, copying x241 here, cause x241 is needed in a reg for other than x283, namely all: , x283--x284, size: 1
adcx rdi, r12
setc r12b; spill CF x284 to reg (r12)
clc;
mov rdx, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, rdx; loading flag
adcx r9, r10
mov r8, 0xffffffffffffffff ; moving imm to reg
mov rdx, r13; x279 to rdx
mulx r13, r10, r8; x304, x303<- x279 * 0xffffffffffffffff
adox r10, r11
adcx r10, rdi
setc r11b; spill CF x327 to reg (r11)
clc;
mov rdi, -0x1 ; moving imm to reg
movzx r12, r12b
adcx r12, rdi; loading flag
adcx r15, rbp
mov rbp, 0xfdc1767ae2ffffff ; moving imm to reg
mulx r12, rdi, rbp; x302, x301<- x279 * 0xfdc1767ae2ffffff
adox rdi, r13
adcx rcx, r14
seto r14b; spill OF x314 to reg (r14)
mov r13, -0x1 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r13, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, r13; loading flag
adox r15, rdi
mov r11, 0x7bc65c783158aea3 ; moving imm to reg
mulx rdi, r13, r11; x300, x299<- x279 * 0x7bc65c783158aea3
setc r11b; spill CF x288 to reg (r11)
clc;
mov rbp, -0x1 ; moving imm to reg
movzx r14, r14b
adcx r14, rbp; loading flag
adcx r12, r13
adox r12, rcx
mov r14, 0x6cfc5fd681c52056 ; moving imm to reg
mulx rcx, r13, r14; x298, x297<- x279 * 0x6cfc5fd681c52056
adcx r13, rdi
seto dil; spill OF x331 to reg (rdi)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, rbp; loading flag
adox rax, [ rsp + 0x110 ]
seto r11b; spill OF x290 to reg (r11)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx rdi, dil
adox rdi, rbp; loading flag
adox rax, r13
mov rdi, [ rsp + 0x100 ]; load m64 x276 to register64
setc r13b; spill CF x318 to reg (r13)
clc;
movzx r11, r11b
adcx r11, rbp; loading flag
adcx rdi, [ rsp + 0x108 ]
mov r11, 0x2341f27177344 ; moving imm to reg
mulx rdx, rbp, r11; x296, x295<- x279 * 0x2341f27177344
setc r8b; spill CF x292 to reg (r8)
clc;
mov r14, -0x1 ; moving imm to reg
movzx r13, r13b
adcx r13, r14; loading flag
adcx rcx, rbp
adox rcx, rdi
mov r13, [ rsp + 0xf8 ]; load m64 x278 to register64
setc dil; spill CF x320 to reg (rdi)
clc;
movzx rbp, byte [ rsp + 0xf0 ]; load byte memx251 to register64
movzx r8, r8b
adcx r8, r14; loading flag
adcx r13, rbp
movzx rbp, dil; x321, copying x320 here, cause x320 is needed in a reg for other than x321, namely all: , x321, size: 1
lea rbp, [ rbp + rdx ]
adox rbp, r13
seto r8b; spill OF x338 to reg (r8)
adc r8b, 0x0
movzx r8, r8b
mov rdx, [ rsp + 0x8 ]; x4 to rdx
mulx rdi, r13, [ rbx + 0x0 ]; x352, x351<- x4 * arg2[0]
adox r13, r9
mov r9, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r9; 0xffffffffffffffff, swapping with x4, which is currently in rdx
mulx r14, r11, r13; x393, x392<- x366 * 0xffffffffffffffff
mov byte [ rsp + 0x118 ], r8b; spilling byte x338 to mem
mov [ rsp + 0x120 ], rbp; spilling x336 to mem
mulx r8, rbp, r13; x395, x394<- x366 * 0xffffffffffffffff
mov [ rsp + 0x128 ], rcx; spilling x334 to mem
mov [ rsp + 0x130 ], rax; spilling x332 to mem
mulx rcx, rax, r13; x391, x390<- x366 * 0xffffffffffffffff
adcx r11, r8
mov r8, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, r13; x366, swapping with 0xffffffffffffffff, which is currently in rdx
mov [ rsp + 0x138 ], r12; spilling x330 to mem
mulx r13, r12, r8; x389, x388<- x366 * 0xfdc1767ae2ffffff
adcx rax, r14
adcx r12, rcx
mov r14, 0x7bc65c783158aea3 ; moving imm to reg
mulx rcx, r8, r14; x387, x386<- x366 * 0x7bc65c783158aea3
adcx r8, r13
mov r13, 0x6cfc5fd681c52056 ; moving imm to reg
mov [ rsp + 0x140 ], r8; spilling x402 to mem
mulx r14, r8, r13; x385, x384<- x366 * 0x6cfc5fd681c52056
mov r13, 0x2341f27177344 ; moving imm to reg
mov [ rsp + 0x148 ], r12; spilling x400 to mem
mov [ rsp + 0x150 ], rax; spilling x398 to mem
mulx r12, rax, r13; x383, x382<- x366 * 0x2341f27177344
adcx r8, rcx
adcx rax, r14
mov rcx, 0x0 ; moving imm to reg
adcx r12, rcx
clc;
adcx rbp, rdx
mov rdx, r9; x4 to rdx
mulx rbp, r9, [ rbx + 0x8 ]; x350, x349<- x4 * arg2[1]
seto r14b; spill OF x367 to reg (r14)
mov r13, -0x3 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r9, rdi
mov rdi, [ rsi + 0x28 ]; load m64 x5 to register64
seto cl; spill OF x354 to reg (rcx)
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r14, r14b
adox r14, r13; loading flag
adox r10, r9
mov r14, rdx; preserving value of x4 into a new reg
mov rdx, [ rbx + 0x0 ]; saving arg2[0] in rdx.
mulx r9, r13, rdi; x439, x438<- x5 * arg2[0]
adcx r11, r10
setc r10b; spill CF x412 to reg (r10)
clc;
adcx r13, r11
mov r11, 0xffffffffffffffff ; moving imm to reg
mov rdx, r11; 0xffffffffffffffff to rdx
mov [ rsp + 0x158 ], r12; spilling x408 to mem
mulx r11, r12, r13; x480, x479<- x453 * 0xffffffffffffffff
mov [ rsp + 0x160 ], rax; spilling x406 to mem
mov [ rsp + 0x168 ], r8; spilling x404 to mem
mulx rax, r8, r13; x482, x481<- x453 * 0xffffffffffffffff
setc dl; spill CF x454 to reg (rdx)
clc;
adcx r12, rax
mov rax, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rax; 0xffffffffffffffff, swapping with x454, which is currently in rdx
mov [ rsp + 0x170 ], r12; spilling x483 to mem
mov byte [ rsp + 0x178 ], al; spilling byte x454 to mem
mulx r12, rax, r13; x478, x477<- x453 * 0xffffffffffffffff
adcx rax, r11
mov r11, 0xfdc1767ae2ffffff ; moving imm to reg
xchg rdx, r11; 0xfdc1767ae2ffffff, swapping with 0xffffffffffffffff, which is currently in rdx
mov [ rsp + 0x180 ], rax; spilling x485 to mem
mulx r11, rax, r13; x476, x475<- x453 * 0xfdc1767ae2ffffff
adcx rax, r12
mov r12, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, r13; x453, swapping with 0xfdc1767ae2ffffff, which is currently in rdx
mov [ rsp + 0x188 ], rax; spilling x487 to mem
mulx r13, rax, r12; x474, x473<- x453 * 0x7bc65c783158aea3
adcx rax, r11
mov r11, 0x6cfc5fd681c52056 ; moving imm to reg
mov [ rsp + 0x190 ], rax; spilling x489 to mem
mulx r12, rax, r11; x472, x471<- x453 * 0x6cfc5fd681c52056
adcx rax, r13
mov r13, 0x2341f27177344 ; moving imm to reg
mov [ rsp + 0x198 ], rax; spilling x491 to mem
mulx r11, rax, r13; x470, x469<- x453 * 0x2341f27177344
adcx rax, r12
mov r12, 0x0 ; moving imm to reg
adcx r11, r12
xchg rdx, r14; x4, swapping with x453, which is currently in rdx
mulx r12, r13, [ rbx + 0x10 ]; x348, x347<- x4 * arg2[2]
clc;
mov [ rsp + 0x1a0 ], r11; spilling x495 to mem
mov r11, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, r11; loading flag
adcx rbp, r13
mulx rcx, r13, [ rbx + 0x18 ]; x346, x345<- x4 * arg2[3]
adcx r13, r12
mulx r12, r11, [ rbx + 0x20 ]; x344, x343<- x4 * arg2[4]
adcx r11, rcx
mov [ rsp + 0x1a8 ], rax; spilling x493 to mem
mulx rcx, rax, [ rbx + 0x28 ]; x342, x341<- x4 * arg2[5]
adcx rax, r12
mulx rdx, r12, [ rbx + 0x30 ]; x340, x339<- x4 * arg2[6]
adcx r12, rcx
mov rcx, 0x0 ; moving imm to reg
adcx rdx, rcx
clc;
adcx r8, r14
adox rbp, r15
seto r8b; spill OF x371 to reg (r8)
dec rcx; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r10, r10b
adox r10, rcx; loading flag
adox rbp, [ rsp + 0x150 ]
xchg rdx, rdi; x5, swapping with x365, which is currently in rdx
mulx r15, r10, [ rbx + 0x8 ]; x437, x436<- x5 * arg2[1]
seto r14b; spill OF x414 to reg (r14)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r10, r9
setc r9b; spill CF x497 to reg (r9)
movzx rcx, byte [ rsp + 0x178 ]; load byte memx454 to register64
clc;
mov [ rsp + 0x1b0 ], rdi; spilling x365 to mem
mov rdi, -0x1 ; moving imm to reg
adcx rcx, rdi; loading flag
adcx rbp, r10
seto cl; spill OF x441 to reg (rcx)
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r10, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, r10; loading flag
adox rbp, [ rsp + 0x170 ]
mov r9, [ rsi + 0x30 ]; load m64 x6 to register64
xchg rdx, r9; x6, swapping with x5, which is currently in rdx
mulx rdi, r10, [ rbx + 0x0 ]; x526, x525<- x6 * arg2[0]
mov [ rsp + 0x1b8 ], r12; spilling x363 to mem
setc r12b; spill CF x456 to reg (r12)
clc;
adcx r10, rbp
mov rbp, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbp; 0xffffffffffffffff, swapping with x6, which is currently in rdx
mov [ rsp + 0x1c0 ], rax; spilling x361 to mem
mov [ rsp + 0x1c8 ], r11; spilling x359 to mem
mulx rax, r11, r10; x569, x568<- x540 * 0xffffffffffffffff
setc dl; spill CF x541 to reg (rdx)
clc;
adcx r11, r10
seto r11b; spill OF x499 to reg (r11)
mov byte [ rsp + 0x1d0 ], dl; spilling byte x541 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r8, r8b
adox r8, rdx; loading flag
adox r13, [ rsp + 0x138 ]
seto r8b; spill OF x373 to reg (r8)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, rdx; loading flag
adox r13, [ rsp + 0x148 ]
mov rdx, [ rbx + 0x10 ]; arg2[2] to rdx
mov byte [ rsp + 0x1d8 ], r8b; spilling byte x373 to mem
mulx r14, r8, r9; x435, x434<- x5 * arg2[2]
mov [ rsp + 0x1e0 ], r14; spilling x435 to mem
seto r14b; spill OF x416 to reg (r14)
mov [ rsp + 0x1e8 ], rax; spilling x569 to mem
mov rax, -0x1 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rax, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, rax; loading flag
adox r15, r8
seto cl; spill OF x443 to reg (rcx)
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, r8; loading flag
adox r13, r15
seto r12b; spill OF x458 to reg (r12)
dec rax; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx r11, r11b
adox r11, rax; loading flag
adox r13, [ rsp + 0x180 ]
mov rdx, [ rbx + 0x8 ]; arg2[1] to rdx
mulx r8, r11, rbp; x524, x523<- x6 * arg2[1]
setc r15b; spill CF x584 to reg (r15)
clc;
adcx r11, rdi
mov rdi, 0xffffffffffffffff ; moving imm to reg
mov rdx, r10; x540 to rdx
mulx r10, rax, rdi; x567, x566<- x540 * 0xffffffffffffffff
setc dil; spill CF x528 to reg (rdi)
clc;
adcx rax, [ rsp + 0x1e8 ]
mov [ rsp + 0x1f0 ], r10; spilling x567 to mem
setc r10b; spill CF x571 to reg (r10)
mov [ rsp + 0x1f8 ], r8; spilling x524 to mem
movzx r8, byte [ rsp + 0x1d0 ]; load byte memx541 to register64
clc;
mov byte [ rsp + 0x200 ], dil; spilling byte x528 to mem
mov rdi, -0x1 ; moving imm to reg
adcx r8, rdi; loading flag
adcx r13, r11
setc r8b; spill CF x543 to reg (r8)
clc;
movzx r15, r15b
adcx r15, rdi; loading flag
adcx r13, rax
setc r15b; spill CF x586 to reg (r15)
seto r11b; spill OF x501 to reg (r11)
mov rax, r13; x600, copying x585 here, cause x585 is needed in a reg for other than x600, namely all: , x600--x601, x616, size: 2
mov rdi, 0xffffffffffffffff ; moving imm to reg
sub rax, rdi
mov rdi, [ rsp + 0x1c8 ]; load m64 x359 to register64
mov [ rsp + 0x208 ], rax; spilling x600 to mem
movzx rax, byte [ rsp + 0x1d8 ]; load byte memx373 to register64
mov byte [ rsp + 0x210 ], r15b; spilling byte x586 to mem
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rax, r15; loading flag
adox rdi, [ rsp + 0x130 ]
xchg rdx, r9; x5, swapping with x540, which is currently in rdx
mulx rax, r15, [ rbx + 0x18 ]; x433, x432<- x5 * arg2[3]
mov [ rsp + 0x218 ], rax; spilling x433 to mem
setc al; spill CF x601 to reg (rax)
clc;
mov byte [ rsp + 0x220 ], r10b; spilling byte x571 to mem
mov r10, -0x1 ; moving imm to reg
movzx r14, r14b
adcx r14, r10; loading flag
adcx rdi, [ rsp + 0x140 ]
setc r14b; spill CF x418 to reg (r14)
clc;
movzx rcx, cl
adcx rcx, r10; loading flag
adcx r15, [ rsp + 0x1e0 ]
setc cl; spill CF x445 to reg (rcx)
clc;
movzx r12, r12b
adcx r12, r10; loading flag
adcx rdi, r15
seto r12b; spill OF x375 to reg (r12)
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, r15; loading flag
adox rdi, [ rsp + 0x188 ]
xchg rdx, rbp; x6, swapping with x5, which is currently in rdx
mulx r11, r10, [ rbx + 0x10 ]; x522, x521<- x6 * arg2[2]
seto r15b; spill OF x503 to reg (r15)
mov [ rsp + 0x228 ], r11; spilling x522 to mem
movzx r11, byte [ rsp + 0x200 ]; load byte memx528 to register64
mov byte [ rsp + 0x230 ], cl; spilling byte x445 to mem
mov rcx, -0x1 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rcx, -0x1 ; moving imm to reg
adox r11, rcx; loading flag
adox r10, [ rsp + 0x1f8 ]
setc r11b; spill CF x460 to reg (r11)
clc;
movzx r8, r8b
adcx r8, rcx; loading flag
adcx rdi, r10
mov r8, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r9; x540, swapping with x6, which is currently in rdx
mulx r10, rcx, r8; x565, x564<- x540 * 0xffffffffffffffff
setc r8b; spill CF x545 to reg (r8)
mov [ rsp + 0x238 ], r10; spilling x565 to mem
movzx r10, byte [ rsp + 0x220 ]; load byte memx571 to register64
clc;
mov byte [ rsp + 0x240 ], r15b; spilling byte x503 to mem
mov r15, -0x1 ; moving imm to reg
adcx r10, r15; loading flag
adcx rcx, [ rsp + 0x1f0 ]
setc r10b; spill CF x573 to reg (r10)
movzx r15, byte [ rsp + 0x210 ]; load byte memx586 to register64
clc;
mov byte [ rsp + 0x248 ], r8b; spilling byte x545 to mem
mov r8, -0x1 ; moving imm to reg
adcx r15, r8; loading flag
adcx rdi, rcx
setc r15b; spill CF x588 to reg (r15)
seto cl; spill OF x530 to reg (rcx)
movzx r8, al; x601, copying x601 here, cause x601 is needed in a reg for other than x601, namely all: , x602--x603, size: 1
add r8, -0x1
mov rax, rdi; x602, copying x587 here, cause x587 is needed in a reg for other than x602, namely all: , x602--x603, x617, size: 2
mov r8, 0xffffffffffffffff ; moving imm to reg
sbb rax, r8
mov r8, [ rsp + 0x1c0 ]; load m64 x361 to register64
mov [ rsp + 0x250 ], rax; spilling x602 to mem
mov rax, -0x1 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rax, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, rax; loading flag
adox r8, [ rsp + 0x128 ]
mov r12, rdx; preserving value of x540 into a new reg
mov rdx, [ rbx + 0x20 ]; saving arg2[4] in rdx.
mov byte [ rsp + 0x258 ], r15b; spilling byte x588 to mem
mulx rax, r15, rbp; x431, x430<- x5 * arg2[4]
mov [ rsp + 0x260 ], rax; spilling x431 to mem
seto al; spill OF x377 to reg (rax)
mov byte [ rsp + 0x268 ], r10b; spilling byte x573 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r14, r14b
adox r14, r10; loading flag
adox r8, [ rsp + 0x168 ]
setc r14b; spill CF x603 to reg (r14)
movzx r10, byte [ rsp + 0x230 ]; load byte memx445 to register64
clc;
mov byte [ rsp + 0x270 ], al; spilling byte x377 to mem
mov rax, -0x1 ; moving imm to reg
adcx r10, rax; loading flag
adcx r15, [ rsp + 0x218 ]
seto r10b; spill OF x420 to reg (r10)
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rax, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, rax; loading flag
adox r8, r15
seto r11b; spill OF x462 to reg (r11)
movzx r15, byte [ rsp + 0x240 ]; load byte memx503 to register64
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rax, -0x1 ; moving imm to reg
adox r15, rax; loading flag
adox r8, [ rsp + 0x190 ]
mov rdx, [ rbx + 0x18 ]; arg2[3] to rdx
mulx r15, rax, r9; x520, x519<- x6 * arg2[3]
mov [ rsp + 0x278 ], r15; spilling x520 to mem
seto r15b; spill OF x505 to reg (r15)
mov byte [ rsp + 0x280 ], r11b; spilling byte x462 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r11; loading flag
adox rax, [ rsp + 0x228 ]
setc cl; spill CF x447 to reg (rcx)
movzx r11, byte [ rsp + 0x248 ]; load byte memx545 to register64
clc;
mov byte [ rsp + 0x288 ], r15b; spilling byte x505 to mem
mov r15, -0x1 ; moving imm to reg
adcx r11, r15; loading flag
adcx r8, rax
mov r11, 0xfdc1767ae2ffffff ; moving imm to reg
mov rdx, r12; x540 to rdx
mulx r12, rax, r11; x563, x562<- x540 * 0xfdc1767ae2ffffff
setc r15b; spill CF x547 to reg (r15)
movzx r11, byte [ rsp + 0x268 ]; load byte memx573 to register64
clc;
mov [ rsp + 0x290 ], r12; spilling x563 to mem
mov r12, -0x1 ; moving imm to reg
adcx r11, r12; loading flag
adcx rax, [ rsp + 0x238 ]
seto r11b; spill OF x532 to reg (r11)
movzx r12, byte [ rsp + 0x258 ]; load byte memx588 to register64
mov byte [ rsp + 0x298 ], r15b; spilling byte x547 to mem
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r12, r15; loading flag
adox r8, rax
setc r12b; spill CF x575 to reg (r12)
seto al; spill OF x590 to reg (rax)
movzx r15, r14b; x603, copying x603 here, cause x603 is needed in a reg for other than x603, namely all: , x604--x605, size: 1
add r15, -0x1
mov r14, r8; x604, copying x589 here, cause x589 is needed in a reg for other than x604, namely all: , x618, x604--x605, size: 2
mov r15, 0xffffffffffffffff ; moving imm to reg
sbb r14, r15
mov r15, [ rsp + 0x120 ]; load m64 x336 to register64
mov [ rsp + 0x2a0 ], r14; spilling x604 to mem
movzx r14, byte [ rsp + 0x270 ]; load byte memx377 to register64
mov byte [ rsp + 0x2a8 ], al; spilling byte x590 to mem
mov rax, 0x0 ; moving imm to reg
dec rax; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r14, rax; loading flag
adox r15, [ rsp + 0x1b8 ]
seto r14b; spill OF x379 to reg (r14)
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rax, -0x1 ; moving imm to reg
movzx r10, r10b
adox r10, rax; loading flag
adox r15, [ rsp + 0x160 ]
xchg rdx, rbp; x5, swapping with x540, which is currently in rdx
mulx r10, rax, [ rbx + 0x28 ]; x429, x428<- x5 * arg2[5]
mov [ rsp + 0x2b0 ], r10; spilling x429 to mem
seto r10b; spill OF x422 to reg (r10)
mov byte [ rsp + 0x2b8 ], r14b; spilling byte x379 to mem
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rcx, cl
adox rcx, r14; loading flag
adox rax, [ rsp + 0x260 ]
setc cl; spill CF x605 to reg (rcx)
movzx r14, byte [ rsp + 0x280 ]; load byte memx462 to register64
clc;
mov byte [ rsp + 0x2c0 ], r10b; spilling byte x422 to mem
mov r10, -0x1 ; moving imm to reg
adcx r14, r10; loading flag
adcx r15, rax
setc r14b; spill CF x464 to reg (r14)
movzx rax, byte [ rsp + 0x288 ]; load byte memx505 to register64
clc;
adcx rax, r10; loading flag
adcx r15, [ rsp + 0x198 ]
xchg rdx, r9; x6, swapping with x5, which is currently in rdx
mulx rax, r10, [ rbx + 0x20 ]; x518, x517<- x6 * arg2[4]
mov [ rsp + 0x2c8 ], rax; spilling x518 to mem
setc al; spill CF x507 to reg (rax)
clc;
mov byte [ rsp + 0x2d0 ], r14b; spilling byte x464 to mem
mov r14, -0x1 ; moving imm to reg
movzx r11, r11b
adcx r11, r14; loading flag
adcx r10, [ rsp + 0x278 ]
seto r11b; spill OF x449 to reg (r11)
movzx r14, byte [ rsp + 0x298 ]; load byte memx547 to register64
mov byte [ rsp + 0x2d8 ], al; spilling byte x507 to mem
mov rax, 0x0 ; moving imm to reg
dec rax; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r14, rax; loading flag
adox r15, r10
mov r14, 0x7bc65c783158aea3 ; moving imm to reg
xchg rdx, r14; 0x7bc65c783158aea3, swapping with x6, which is currently in rdx
mulx r10, rax, rbp; x561, x560<- x540 * 0x7bc65c783158aea3
setc dl; spill CF x534 to reg (rdx)
clc;
mov [ rsp + 0x2e0 ], r10; spilling x561 to mem
mov r10, -0x1 ; moving imm to reg
movzx r12, r12b
adcx r12, r10; loading flag
adcx rax, [ rsp + 0x290 ]
setc r12b; spill CF x577 to reg (r12)
movzx r10, byte [ rsp + 0x2a8 ]; load byte memx590 to register64
clc;
mov byte [ rsp + 0x2e8 ], dl; spilling byte x534 to mem
mov rdx, -0x1 ; moving imm to reg
adcx r10, rdx; loading flag
adcx r15, rax
setc r10b; spill CF x592 to reg (r10)
seto al; spill OF x549 to reg (rax)
movzx rdx, cl; x605, copying x605 here, cause x605 is needed in a reg for other than x605, namely all: , x606--x607, size: 1
add rdx, -0x1
mov rcx, r15; x606, copying x591 here, cause x591 is needed in a reg for other than x606, namely all: , x619, x606--x607, size: 2
mov byte [ rsp + 0x2f0 ], r12b; spilling byte x577 to mem
mov r12, 0xfdc1767ae2ffffff ; moving imm to reg
sbb rcx, r12
movzx r12, byte [ rsp + 0x118 ]; load byte memx338 to register64
mov [ rsp + 0x2f8 ], rcx; spilling x606 to mem
movzx rcx, byte [ rsp + 0x2b8 ]; load byte memx379 to register64
mov byte [ rsp + 0x300 ], r10b; spilling byte x592 to mem
mov r10, -0x1 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r10, -0x1 ; moving imm to reg
adox rcx, r10; loading flag
adox r12, [ rsp + 0x1b0 ]
mov rdx, [ rbx + 0x30 ]; arg2[6] to rdx
mulx r9, rcx, r9; x427, x426<- x5 * arg2[6]
setc r10b; spill CF x607 to reg (r10)
mov [ rsp + 0x308 ], r9; spilling x427 to mem
movzx r9, byte [ rsp + 0x2c0 ]; load byte memx422 to register64
clc;
mov byte [ rsp + 0x310 ], al; spilling byte x549 to mem
mov rax, -0x1 ; moving imm to reg
adcx r9, rax; loading flag
adcx r12, [ rsp + 0x158 ]
setc r9b; spill CF x424 to reg (r9)
clc;
movzx r11, r11b
adcx r11, rax; loading flag
adcx rcx, [ rsp + 0x2b0 ]
setc r11b; spill CF x451 to reg (r11)
movzx rax, byte [ rsp + 0x2d0 ]; load byte memx464 to register64
clc;
mov byte [ rsp + 0x318 ], r9b; spilling byte x424 to mem
mov r9, -0x1 ; moving imm to reg
adcx rax, r9; loading flag
adcx r12, rcx
setc al; spill CF x466 to reg (rax)
movzx rcx, byte [ rsp + 0x2d8 ]; load byte memx507 to register64
clc;
adcx rcx, r9; loading flag
adcx r12, [ rsp + 0x1a8 ]
mov rdx, r14; x6 to rdx
mulx r14, rcx, [ rbx + 0x28 ]; x516, x515<- x6 * arg2[5]
seto r9b; spill OF x381 to reg (r9)
mov [ rsp + 0x320 ], r14; spilling x516 to mem
movzx r14, byte [ rsp + 0x2e8 ]; load byte memx534 to register64
mov byte [ rsp + 0x328 ], al; spilling byte x466 to mem
mov rax, 0x0 ; moving imm to reg
dec rax; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r14, rax; loading flag
adox rcx, [ rsp + 0x2c8 ]
mov r14, 0x6cfc5fd681c52056 ; moving imm to reg
xchg rdx, rbp; x540, swapping with x6, which is currently in rdx
mov byte [ rsp + 0x330 ], r9b; spilling byte x381 to mem
mulx rax, r9, r14; x559, x558<- x540 * 0x6cfc5fd681c52056
setc r14b; spill CF x509 to reg (r14)
mov [ rsp + 0x338 ], rax; spilling x559 to mem
movzx rax, byte [ rsp + 0x310 ]; load byte memx549 to register64
clc;
mov byte [ rsp + 0x340 ], r11b; spilling byte x451 to mem
mov r11, -0x1 ; moving imm to reg
adcx rax, r11; loading flag
adcx r12, rcx
setc al; spill CF x551 to reg (rax)
movzx rcx, byte [ rsp + 0x2f0 ]; load byte memx577 to register64
clc;
adcx rcx, r11; loading flag
adcx r9, [ rsp + 0x2e0 ]
setc cl; spill CF x579 to reg (rcx)
movzx r11, byte [ rsp + 0x300 ]; load byte memx592 to register64
clc;
mov byte [ rsp + 0x348 ], al; spilling byte x551 to mem
mov rax, -0x1 ; moving imm to reg
adcx r11, rax; loading flag
adcx r12, r9
setc r11b; spill CF x594 to reg (r11)
seto r9b; spill OF x536 to reg (r9)
movzx rax, r10b; x607, copying x607 here, cause x607 is needed in a reg for other than x607, namely all: , x608--x609, size: 1
add rax, -0x1
mov rax, r12; x608, copying x593 here, cause x593 is needed in a reg for other than x608, namely all: , x608--x609, x620, size: 2
mov r10, 0x7bc65c783158aea3 ; moving imm to reg
sbb rax, r10
movzx r10, byte [ rsp + 0x340 ]; x452, copying x451 here, cause x451 is needed in a reg for other than x452, namely all: , x452, size: 1
mov [ rsp + 0x350 ], rax; spilling x608 to mem
mov rax, [ rsp + 0x308 ]; load m64 x427 to register64
lea r10, [ r10 + rax ]; r8/64 + m8
movzx rax, byte [ rsp + 0x318 ]; x425, copying x424 here, cause x424 is needed in a reg for other than x425, namely all: , x425, size: 1
mov byte [ rsp + 0x358 ], r11b; spilling byte x594 to mem
movzx r11, byte [ rsp + 0x330 ]; load byte memx381 to register64
lea rax, [ rax + r11 ]; r64+m8
movzx r11, byte [ rsp + 0x328 ]; load byte memx466 to register64
mov byte [ rsp + 0x360 ], cl; spilling byte x579 to mem
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r11, rcx; loading flag
adox rax, r10
seto r11b; spill OF x468 to reg (r11)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r10, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, r10; loading flag
adox rax, [ rsp + 0x1a0 ]
xchg rdx, rbp; x6, swapping with x540, which is currently in rdx
mulx rdx, r14, [ rbx + 0x30 ]; x514, x513<- x6 * arg2[6]
seto cl; spill OF x511 to reg (rcx)
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r10, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, r10; loading flag
adox r14, [ rsp + 0x320 ]
seto r9b; spill OF x538 to reg (r9)
movzx r10, byte [ rsp + 0x348 ]; load byte memx551 to register64
mov [ rsp + 0x368 ], rdx; spilling x514 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r10, rdx; loading flag
adox rax, r14
mov r10, 0x2341f27177344 ; moving imm to reg
mov rdx, r10; 0x2341f27177344 to rdx
mulx rbp, r10, rbp; x557, x556<- x540 * 0x2341f27177344
setc r14b; spill CF x609 to reg (r14)
movzx rdx, byte [ rsp + 0x360 ]; load byte memx579 to register64
clc;
mov byte [ rsp + 0x370 ], r9b; spilling byte x538 to mem
mov r9, -0x1 ; moving imm to reg
adcx rdx, r9; loading flag
adcx r10, [ rsp + 0x338 ]
setc dl; spill CF x581 to reg (rdx)
movzx r9, byte [ rsp + 0x358 ]; load byte memx594 to register64
clc;
mov [ rsp + 0x378 ], rbp; spilling x557 to mem
mov rbp, -0x1 ; moving imm to reg
adcx r9, rbp; loading flag
adcx rax, r10
movzx r9, cl; x512, copying x511 here, cause x511 is needed in a reg for other than x512, namely all: , x512, size: 1
movzx r11, r11b
lea r9, [ r9 + r11 ]
setc r11b; spill CF x596 to reg (r11)
seto cl; spill OF x553 to reg (rcx)
movzx r10, r14b; x609, copying x609 here, cause x609 is needed in a reg for other than x609, namely all: , x610--x611, size: 1
add r10, -0x1
mov r10, rax; x610, copying x595 here, cause x595 is needed in a reg for other than x610, namely all: , x610--x611, x621, size: 2
mov r14, 0x6cfc5fd681c52056 ; moving imm to reg
sbb r10, r14
movzx rbp, dl; x582, copying x581 here, cause x581 is needed in a reg for other than x582, namely all: , x582, size: 1
mov r14, [ rsp + 0x378 ]; load m64 x557 to register64
lea rbp, [ rbp + r14 ]; r8/64 + m8
movzx r14, byte [ rsp + 0x370 ]; x539, copying x538 here, cause x538 is needed in a reg for other than x539, namely all: , x539, size: 1
mov rdx, [ rsp + 0x368 ]; load m64 x514 to register64
lea r14, [ r14 + rdx ]; r8/64 + m8
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rcx, cl
adox rcx, rdx; loading flag
adox r9, r14
seto cl; spill OF x555 to reg (rcx)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, r14; loading flag
adox r9, rbp
movzx r11, cl; x599, copying x555 here, cause x555 is needed in a reg for other than x599, namely all: , x599, size: 1
adox r11, rdx
mov rbp, r9; x612, copying x597 here, cause x597 is needed in a reg for other than x612, namely all: , x612--x613, x622, size: 2
mov rcx, 0x2341f27177344 ; moving imm to reg
sbb rbp, rcx
sbb r11, 0x00000000
mov r11, [ rsp + 0x2a0 ]; x618, copying x604 here, cause x604 is needed in a reg for other than x618, namely all: , x618, size: 1
cmovc r11, r8; if CF, x618<- x589 (nzVar)
mov r8, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r8 + 0x10 ], r11; out1[2] = x618
cmovc rbp, r9; if CF, x622<- x597 (nzVar)
mov r9, [ rsp + 0x2f8 ]; x619, copying x606 here, cause x606 is needed in a reg for other than x619, namely all: , x619, size: 1
cmovc r9, r15; if CF, x619<- x591 (nzVar)
mov [ r8 + 0x30 ], rbp; out1[6] = x622
mov r15, [ rsp + 0x208 ]; x616, copying x600 here, cause x600 is needed in a reg for other than x616, namely all: , x616, size: 1
cmovc r15, r13; if CF, x616<- x585 (nzVar)
mov r13, [ rsp + 0x350 ]; x620, copying x608 here, cause x608 is needed in a reg for other than x620, namely all: , x620, size: 1
cmovc r13, r12; if CF, x620<- x593 (nzVar)
cmovc r10, rax; if CF, x621<- x595 (nzVar)
mov r12, [ rsp + 0x250 ]; x617, copying x602 here, cause x602 is needed in a reg for other than x617, namely all: , x617, size: 1
cmovc r12, rdi; if CF, x617<- x587 (nzVar)
mov [ r8 + 0x20 ], r13; out1[4] = x620
mov [ r8 + 0x8 ], r12; out1[1] = x617
mov [ r8 + 0x18 ], r9; out1[3] = x619
mov [ r8 + 0x0 ], r15; out1[0] = x616
mov [ r8 + 0x28 ], r10; out1[5] = x621
mov rbx, [ rsp + 0x380 ]; restoring from stack
mov rbp, [ rsp + 0x388 ]; restoring from stack
mov r12, [ rsp + 0x390 ]; restoring from stack
mov r13, [ rsp + 0x398 ]; restoring from stack
mov r14, [ rsp + 0x3a0 ]; restoring from stack
mov r15, [ rsp + 0x3a8 ]; restoring from stack
add rsp, 0x3b0 
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; clocked at 1600 MHz
; first cyclecount 234.0325, best 229.105, lastGood 240.21428571428572
; seed 535677244591890 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 56243 ms / 500 runs=> 112.486ms/run
; Time spent for assembling and measureing (initial batch_size=41, initial num_batches=101): 1803 ms
; Ratio (time for assembling + measure)/(total runtime for 500runs): 0.03205732268904575
; number reverted permutation/ tried permutation: 184 / 234 =78.632%
; number reverted decision/ tried decision: 178 / 267 =66.667%