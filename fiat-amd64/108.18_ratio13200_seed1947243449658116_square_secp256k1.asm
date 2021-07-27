SECTION .text
	GLOBAL square_secp256k1
square_secp256k1:
sub rsp, 0x168 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x138 ], rbx; saving to stack
mov [ rsp + 0x140 ], rbp; saving to stack
mov [ rsp + 0x148 ], r12; saving to stack
mov [ rsp + 0x150 ], r13; saving to stack
mov [ rsp + 0x158 ], r14; saving to stack
mov [ rsp + 0x160 ], r15; saving to stack
mov rax, [ rsi + 0x10 ]; load m64 x2 to register64
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r10, r11, rax; x103, x102<- x2 * arg1[2]
mov rdx, rax; x2 to rdx
mulx rax, rbx, [ rsi + 0x8 ]; x105, x104<- x2 * arg1[1]
mulx rbp, r12, [ rsi + 0x0 ]; x107, x106<- x2 * arg1[0]
test al, al
adox rbx, rbp
mulx rdx, r13, [ rsi + 0x18 ]; x101, x100<- x2 * arg1[3]
adox r11, rax
adox r13, r10
mov r14, [ rsi + 0x0 ]; load m64 x4 to register64
mov r15, 0x0 ; moving imm to reg
adox rdx, r15
xchg rdx, r14; x4, swapping with x114, which is currently in rdx
mulx rcx, r8, [ rsi + 0x0 ]; x12, x11<- x4 * arg1[0]
mov r9, 0xd838091dd2253531 ; moving imm to reg
xchg rdx, r9; 0xd838091dd2253531, swapping with x4, which is currently in rdx
mulx r10, rax, r8; _, x20<- x11 * 0xd838091dd2253531
mov r10, 0xfffffffefffffc2f ; moving imm to reg
xchg rdx, r10; 0xfffffffefffffc2f, swapping with 0xd838091dd2253531, which is currently in rdx
mulx rbp, r15, rax; x29, x28<- x20 * 0xfffffffefffffc2f
mov r10, rdx; preserving value of 0xfffffffefffffc2f into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov [ rsp + 0x8 ], r14; spilling x114 to mem
mulx rdi, r14, r9; x10, x9<- x4 * arg1[1]
adcx r15, r8
mov r15, 0xffffffffffffffff ; moving imm to reg
mov rdx, rax; x20 to rdx
mulx rax, r8, r15; x27, x26<- x20 * 0xffffffffffffffff
mov r15, -0x2 ; moving imm to reg
inc r15; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, rcx
mov rcx, [ rsi + 0x8 ]; load m64 x1 to register64
seto r15b; spill OF x14 to reg (r15)
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, rbp
adcx r8, r14
mov rbp, rdx; preserving value of x20 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r14, r10, rcx; x54, x53<- x1 * arg1[0]
setc dl; spill CF x40 to reg (rdx)
clc;
adcx r10, r8
mov r8, 0xd838091dd2253531 ; moving imm to reg
xchg rdx, r8; 0xd838091dd2253531, swapping with x40, which is currently in rdx
mov [ rsp + 0x10 ], r13; spilling x112 to mem
mov [ rsp + 0x18 ], r11; spilling x110 to mem
mulx r13, r11, r10; _, x72<- x62 * 0xd838091dd2253531
mov r13, 0xfffffffefffffc2f ; moving imm to reg
xchg rdx, r11; x72, swapping with 0xd838091dd2253531, which is currently in rdx
mov [ rsp + 0x20 ], rbx; spilling x108 to mem
mulx r11, rbx, r13; x81, x80<- x72 * 0xfffffffefffffc2f
mov r13, rdx; preserving value of x72 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x28 ], r12; spilling x106 to mem
mov [ rsp + 0x30 ], r11; spilling x81 to mem
mulx r12, r11, r9; x8, x7<- x4 * arg1[2]
seto dl; spill OF x31 to reg (rdx)
mov [ rsp + 0x38 ], r12; spilling x8 to mem
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, r10
mov rbx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbx; 0xffffffffffffffff, swapping with x31, which is currently in rdx
mulx r10, r12, rbp; x25, x24<- x20 * 0xffffffffffffffff
setc dl; spill CF x63 to reg (rdx)
clc;
mov [ rsp + 0x40 ], r10; spilling x25 to mem
mov r10, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, r10; loading flag
adcx rdi, r11
setc r15b; spill CF x16 to reg (r15)
clc;
movzx rbx, bl
adcx rbx, r10; loading flag
adcx rax, r12
setc bl; spill CF x33 to reg (rbx)
clc;
movzx r8, r8b
adcx r8, r10; loading flag
adcx rdi, rax
xchg rdx, rcx; x1, swapping with x63, which is currently in rdx
mulx r8, r11, [ rsi + 0x8 ]; x52, x51<- x1 * arg1[1]
setc r12b; spill CF x42 to reg (r12)
clc;
adcx r11, r14
seto r14b; spill OF x90 to reg (r14)
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rax, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, rax; loading flag
adox rdi, r11
mov rcx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rcx; 0xffffffffffffffff, swapping with x1, which is currently in rdx
mulx r11, r10, r13; x79, x78<- x72 * 0xffffffffffffffff
setc al; spill CF x56 to reg (rax)
clc;
adcx r10, [ rsp + 0x30 ]
setc dl; spill CF x83 to reg (rdx)
clc;
mov [ rsp + 0x48 ], r11; spilling x79 to mem
mov r11, -0x1 ; moving imm to reg
movzx r14, r14b
adcx r14, r11; loading flag
adcx rdi, r10
seto r14b; spill OF x65 to reg (r14)
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rdi, [ rsp + 0x28 ]
mov r10, 0xd838091dd2253531 ; moving imm to reg
xchg rdx, r10; 0xd838091dd2253531, swapping with x83, which is currently in rdx
mov byte [ rsp + 0x50 ], r10b; spilling byte x83 to mem
mulx r11, r10, rdi; _, x125<- x115 * 0xd838091dd2253531
mov r11, 0xfffffffefffffc2f ; moving imm to reg
xchg rdx, r11; 0xfffffffefffffc2f, swapping with 0xd838091dd2253531, which is currently in rdx
mov byte [ rsp + 0x58 ], r14b; spilling byte x65 to mem
mulx r11, r14, r10; x134, x133<- x125 * 0xfffffffefffffc2f
setc dl; spill CF x92 to reg (rdx)
clc;
adcx r14, rdi
xchg rdx, r9; x4, swapping with x92, which is currently in rdx
mulx rdx, r14, [ rsi + 0x18 ]; x6, x5<- x4 * arg1[3]
mov rdi, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbp; x20, swapping with x6, which is currently in rdx
mov [ rsp + 0x60 ], rbp; spilling x6 to mem
mulx rdx, rbp, rdi; x23, x22<- x20 * 0xffffffffffffffff
setc dil; spill CF x143 to reg (rdi)
clc;
mov [ rsp + 0x68 ], rdx; spilling x23 to mem
mov rdx, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, rdx; loading flag
adcx r14, [ rsp + 0x38 ]
setc r15b; spill CF x18 to reg (r15)
clc;
movzx rbx, bl
adcx rbx, rdx; loading flag
adcx rbp, [ rsp + 0x40 ]
mov rdx, rcx; x1 to rdx
mulx rcx, rbx, [ rsi + 0x10 ]; x50, x49<- x1 * arg1[2]
mov [ rsp + 0x70 ], rcx; spilling x50 to mem
setc cl; spill CF x35 to reg (rcx)
clc;
mov byte [ rsp + 0x78 ], r15b; spilling byte x18 to mem
mov r15, -0x1 ; moving imm to reg
movzx rax, al
adcx rax, r15; loading flag
adcx r8, rbx
setc al; spill CF x58 to reg (rax)
clc;
movzx r12, r12b
adcx r12, r15; loading flag
adcx r14, rbp
mov r12, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r13; x72, swapping with x1, which is currently in rdx
mulx rbp, rbx, r12; x77, x76<- x72 * 0xffffffffffffffff
setc r15b; spill CF x44 to reg (r15)
movzx r12, byte [ rsp + 0x58 ]; load byte memx65 to register64
clc;
mov [ rsp + 0x80 ], rbp; spilling x77 to mem
mov rbp, -0x1 ; moving imm to reg
adcx r12, rbp; loading flag
adcx r14, r8
setc r12b; spill CF x67 to reg (r12)
movzx r8, byte [ rsp + 0x50 ]; load byte memx83 to register64
clc;
adcx r8, rbp; loading flag
adcx rbx, [ rsp + 0x48 ]
setc r8b; spill CF x85 to reg (r8)
clc;
movzx r9, r9b
adcx r9, rbp; loading flag
adcx r14, rbx
mov r9, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r10; x125, swapping with x72, which is currently in rdx
mulx rbx, rbp, r9; x132, x131<- x125 * 0xffffffffffffffff
mov r9, [ rsp + 0x20 ]; x117, copying x108 here, cause x108 is needed in a reg for other than x117, namely all: , x117--x118, size: 1
adox r9, r14
setc r14b; spill CF x94 to reg (r14)
clc;
adcx rbp, r11
mov r11, [ rsi + 0x18 ]; load m64 x3 to register64
mov [ rsp + 0x88 ], rbx; spilling x132 to mem
seto bl; spill OF x118 to reg (rbx)
mov byte [ rsp + 0x90 ], r14b; spilling byte x94 to mem
mov r14, -0x1 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r14, -0x1 ; moving imm to reg
movzx rdi, dil
adox rdi, r14; loading flag
adox r9, rbp
mov rdi, rdx; preserving value of x125 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx rbp, r14, r11; x160, x159<- x3 * arg1[0]
seto dl; spill OF x145 to reg (rdx)
mov [ rsp + 0x98 ], rbp; spilling x160 to mem
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, r9
mov r9, 0xd838091dd2253531 ; moving imm to reg
xchg rdx, r14; x168, swapping with x145, which is currently in rdx
mov byte [ rsp + 0xa0 ], r14b; spilling byte x145 to mem
mulx rbp, r14, r9; _, x178<- x168 * 0xd838091dd2253531
movzx rbp, cl; x36, copying x35 here, cause x35 is needed in a reg for other than x36, namely all: , x36, size: 1
mov r9, [ rsp + 0x68 ]; load m64 x23 to register64
lea rbp, [ rbp + r9 ]; r8/64 + m8
movzx r9, byte [ rsp + 0x78 ]; x19, copying x18 here, cause x18 is needed in a reg for other than x19, namely all: , x19, size: 1
mov rcx, [ rsp + 0x60 ]; load m64 x6 to register64
lea r9, [ r9 + rcx ]; r8/64 + m8
mov rcx, 0xfffffffefffffc2f ; moving imm to reg
xchg rdx, r14; x178, swapping with x168, which is currently in rdx
mov byte [ rsp + 0xa8 ], bl; spilling byte x118 to mem
mov byte [ rsp + 0xb0 ], r8b; spilling byte x85 to mem
mulx rbx, r8, rcx; x187, x186<- x178 * 0xfffffffefffffc2f
setc cl; spill CF x136 to reg (rcx)
clc;
adcx r8, r14
xchg rdx, r13; x1, swapping with x178, which is currently in rdx
mulx rdx, r8, [ rsi + 0x18 ]; x48, x47<- x1 * arg1[3]
seto r14b; spill OF x169 to reg (r14)
mov [ rsp + 0xb8 ], rdx; spilling x48 to mem
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, rdx; loading flag
adox r9, rbp
seto r15b; spill OF x46 to reg (r15)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx rax, al
adox rax, rbp; loading flag
adox r8, [ rsp + 0x70 ]
seto al; spill OF x60 to reg (rax)
inc rbp; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, rdx; loading flag
adox r9, r8
mov r12, 0xffffffffffffffff ; moving imm to reg
mov rdx, r10; x72 to rdx
mulx rdx, r10, r12; x75, x74<- x72 * 0xffffffffffffffff
seto r8b; spill OF x69 to reg (r8)
movzx rbp, byte [ rsp + 0xb0 ]; load byte memx85 to register64
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbp, r12; loading flag
adox r10, [ rsp + 0x80 ]
mov rbp, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rdi; x125, swapping with x75, which is currently in rdx
mov [ rsp + 0xc0 ], rdi; spilling x75 to mem
mulx r12, rdi, rbp; x130, x129<- x125 * 0xffffffffffffffff
setc bpl; spill CF x196 to reg (rbp)
mov [ rsp + 0xc8 ], r12; spilling x130 to mem
movzx r12, byte [ rsp + 0x90 ]; load byte memx94 to register64
clc;
mov byte [ rsp + 0xd0 ], r15b; spilling byte x46 to mem
mov r15, -0x1 ; moving imm to reg
adcx r12, r15; loading flag
adcx r9, r10
setc r12b; spill CF x96 to reg (r12)
movzx r10, byte [ rsp + 0xa8 ]; load byte memx118 to register64
clc;
adcx r10, r15; loading flag
adcx r9, [ rsp + 0x18 ]
seto r10b; spill OF x87 to reg (r10)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r15; loading flag
adox rdi, [ rsp + 0x88 ]
xchg rdx, r11; x3, swapping with x125, which is currently in rdx
mulx rcx, r15, [ rsi + 0x8 ]; x158, x157<- x3 * arg1[1]
mov [ rsp + 0xd8 ], rcx; spilling x158 to mem
seto cl; spill OF x138 to reg (rcx)
mov byte [ rsp + 0xe0 ], r12b; spilling byte x96 to mem
movzx r12, byte [ rsp + 0xa0 ]; load byte memx145 to register64
mov byte [ rsp + 0xe8 ], r10b; spilling byte x87 to mem
mov r10, -0x1 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r10, -0x1 ; moving imm to reg
adox r12, r10; loading flag
adox r9, rdi
setc r12b; spill CF x120 to reg (r12)
clc;
adcx r15, [ rsp + 0x98 ]
seto dil; spill OF x147 to reg (rdi)
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r10, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, r10; loading flag
adox r9, r15
mov r14, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r13; x178, swapping with x3, which is currently in rdx
mulx r15, r10, r14; x185, x184<- x178 * 0xffffffffffffffff
setc r14b; spill CF x162 to reg (r14)
clc;
adcx r10, rbx
setc bl; spill CF x189 to reg (rbx)
clc;
mov [ rsp + 0xf0 ], r15; spilling x185 to mem
mov r15, -0x1 ; moving imm to reg
movzx rbp, bpl
adcx rbp, r15; loading flag
adcx r9, r10
movzx rbp, al; x61, copying x60 here, cause x60 is needed in a reg for other than x61, namely all: , x61, size: 1
mov r10, [ rsp + 0xb8 ]; load m64 x48 to register64
lea rbp, [ rbp + r10 ]; r8/64 + m8
setc r10b; spill CF x198 to reg (r10)
clc;
movzx rax, byte [ rsp + 0xd0 ]; load byte memx46 to register64
movzx r8, r8b
adcx r8, r15; loading flag
adcx rbp, rax
movzx rax, byte [ rsp + 0xe8 ]; x88, copying x87 here, cause x87 is needed in a reg for other than x88, namely all: , x88, size: 1
mov r8, [ rsp + 0xc0 ]; load m64 x75 to register64
lea rax, [ rax + r8 ]; r8/64 + m8
setc r8b; spill CF x71 to reg (r8)
seto r15b; spill OF x171 to reg (r15)
mov byte [ rsp + 0xf8 ], r10b; spilling byte x198 to mem
mov r10, r9; x206, copying x197 here, cause x197 is needed in a reg for other than x206, namely all: , x216, x206--x207, size: 2
mov byte [ rsp + 0x100 ], bl; spilling byte x189 to mem
mov rbx, 0xfffffffefffffc2f ; moving imm to reg
sub r10, rbx
mov rbx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbx; 0xffffffffffffffff, swapping with x178, which is currently in rdx
mov [ rsp + 0x108 ], r10; spilling x206 to mem
mulx r11, r10, r11; x128, x127<- x125 * 0xffffffffffffffff
movzx rdx, byte [ rsp + 0xe0 ]; load byte memx96 to register64
mov [ rsp + 0x110 ], r11; spilling x128 to mem
mov r11, 0x0 ; moving imm to reg
dec r11; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rdx, r11; loading flag
adox rbp, rax
seto dl; spill OF x98 to reg (rdx)
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rax, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, rax; loading flag
adox r10, [ rsp + 0xc8 ]
xchg rdx, r13; x3, swapping with x98, which is currently in rdx
mulx rcx, r11, [ rsi + 0x10 ]; x156, x155<- x3 * arg1[2]
setc al; spill CF x207 to reg (rax)
clc;
mov [ rsp + 0x118 ], rcx; spilling x156 to mem
mov rcx, -0x1 ; moving imm to reg
movzx r12, r12b
adcx r12, rcx; loading flag
adcx rbp, [ rsp + 0x10 ]
setc r12b; spill CF x122 to reg (r12)
clc;
movzx rdi, dil
adcx rdi, rcx; loading flag
adcx rbp, r10
seto dil; spill OF x140 to reg (rdi)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r10, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, r10; loading flag
adox r11, [ rsp + 0xd8 ]
setc r14b; spill CF x149 to reg (r14)
clc;
movzx r15, r15b
adcx r15, r10; loading flag
adcx rbp, r11
mov r15, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbx; x178, swapping with x3, which is currently in rdx
mulx r11, rcx, r15; x183, x182<- x178 * 0xffffffffffffffff
setc r10b; spill CF x173 to reg (r10)
movzx r15, byte [ rsp + 0x100 ]; load byte memx189 to register64
clc;
mov [ rsp + 0x120 ], r11; spilling x183 to mem
mov r11, -0x1 ; moving imm to reg
adcx r15, r11; loading flag
adcx rcx, [ rsp + 0xf0 ]
seto r15b; spill OF x164 to reg (r15)
movzx r11, byte [ rsp + 0xf8 ]; load byte memx198 to register64
mov byte [ rsp + 0x128 ], r10b; spilling byte x173 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r11, r10; loading flag
adox rbp, rcx
setc r11b; spill CF x191 to reg (r11)
seto cl; spill OF x200 to reg (rcx)
movzx r10, al; x207, copying x207 here, cause x207 is needed in a reg for other than x207, namely all: , x208--x209, size: 1
add r10, -0x1
mov rax, rbp; x208, copying x199 here, cause x199 is needed in a reg for other than x208, namely all: , x217, x208--x209, size: 2
mov r10, 0xffffffffffffffff ; moving imm to reg
sbb rax, r10
movzx r10, r13b; x99, copying x98 here, cause x98 is needed in a reg for other than x99, namely all: , x99, size: 1
movzx r8, r8b
lea r10, [ r10 + r8 ]
mov r8, -0x1 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r13, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, r13; loading flag
adox r10, [ rsp + 0x8 ]
movzx r12, dil; x141, copying x140 here, cause x140 is needed in a reg for other than x141, namely all: , x141, size: 1
mov r8, [ rsp + 0x110 ]; load m64 x128 to register64
lea r12, [ r12 + r8 ]; r8/64 + m8
mov r8, rdx; preserving value of x178 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx rbx, rdi, rbx; x154, x153<- x3 * arg1[3]
seto dl; spill OF x124 to reg (rdx)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, r13; loading flag
adox rdi, [ rsp + 0x118 ]
mov r15, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r15; 0xffffffffffffffff, swapping with x124, which is currently in rdx
mulx r8, r13, r8; x181, x180<- x178 * 0xffffffffffffffff
seto dl; spill OF x166 to reg (rdx)
mov [ rsp + 0x130 ], rax; spilling x208 to mem
mov rax, 0x0 ; moving imm to reg
dec rax; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r14, r14b
adox r14, rax; loading flag
adox r10, r12
seto r14b; spill OF x151 to reg (r14)
movzx r12, byte [ rsp + 0x128 ]; load byte memx173 to register64
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rax, -0x1 ; moving imm to reg
adox r12, rax; loading flag
adox r10, rdi
movzx r12, dl; x167, copying x166 here, cause x166 is needed in a reg for other than x167, namely all: , x167, size: 1
lea r12, [ r12 + rbx ]
setc bl; spill CF x209 to reg (rbx)
clc;
movzx r11, r11b
adcx r11, rax; loading flag
adcx r13, [ rsp + 0x120 ]
seto r11b; spill OF x175 to reg (r11)
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdi, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, rdi; loading flag
adox r10, r13
setc cl; spill CF x193 to reg (rcx)
seto dl; spill OF x202 to reg (rdx)
movzx r13, bl; x209, copying x209 here, cause x209 is needed in a reg for other than x209, namely all: , x210--x211, size: 1
add r13, -0x1
mov rbx, r10; x210, copying x201 here, cause x201 is needed in a reg for other than x210, namely all: , x218, x210--x211, size: 2
mov r13, 0xffffffffffffffff ; moving imm to reg
sbb rbx, r13
movzx rax, r14b; x152, copying x151 here, cause x151 is needed in a reg for other than x152, namely all: , x152, size: 1
movzx r15, r15b
lea rax, [ rax + r15 ]
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, r15; loading flag
adox rax, r12
movzx r14, cl; x194, copying x193 here, cause x193 is needed in a reg for other than x194, namely all: , x194, size: 1
lea r14, [ r14 + r8 ]
seto r8b; spill OF x177 to reg (r8)
dec rdi; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx rdx, dl
adox rdx, rdi; loading flag
adox rax, r14
movzx r15, r8b; x205, copying x177 here, cause x177 is needed in a reg for other than x205, namely all: , x205, size: 1
mov r11, 0x0 ; moving imm to reg
adox r15, r11
mov r12, rax; x212, copying x203 here, cause x203 is needed in a reg for other than x212, namely all: , x219, x212--x213, size: 2
sbb r12, r13
sbb r15, 0x00000000
mov r15, [ rsp + 0x130 ]; x217, copying x208 here, cause x208 is needed in a reg for other than x217, namely all: , x217, size: 1
cmovc r15, rbp; if CF, x217<- x199 (nzVar)
mov rbp, [ rsp + 0x108 ]; x216, copying x206 here, cause x206 is needed in a reg for other than x216, namely all: , x216, size: 1
cmovc rbp, r9; if CF, x216<- x197 (nzVar)
mov r9, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r9 + 0x8 ], r15; out1[1] = x217
cmovc rbx, r10; if CF, x218<- x201 (nzVar)
cmovc r12, rax; if CF, x219<- x203 (nzVar)
mov [ r9 + 0x0 ], rbp; out1[0] = x216
mov [ r9 + 0x18 ], r12; out1[3] = x219
mov [ r9 + 0x10 ], rbx; out1[2] = x218
mov rbx, [ rsp + 0x138 ]; restoring from stack
mov rbp, [ rsp + 0x140 ]; restoring from stack
mov r12, [ rsp + 0x148 ]; restoring from stack
mov r13, [ rsp + 0x150 ]; restoring from stack
mov r14, [ rsp + 0x158 ]; restoring from stack
mov r15, [ rsp + 0x160 ]; restoring from stack
add rsp, 0x168 
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; clocked at 2200 MHz
; first cyclecount 112.71, best 102.51515151515152, lastGood 108.18181818181819
; seed 1947243449658116 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 10869 ms / 500 runs=> 21.738ms/run
; Time spent for assembling and measureing (initial batch_size=67, initial num_batches=101): 996 ms
; Ratio (time for assembling + measure)/(total runtime for 500runs): 0.09163676511178581
; number reverted permutation/ tried permutation: 169 / 256 =66.016%
; number reverted decision/ tried decision: 152 / 245 =62.041%