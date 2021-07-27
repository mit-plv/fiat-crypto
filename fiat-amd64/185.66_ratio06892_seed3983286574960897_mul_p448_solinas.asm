SECTION .text
	GLOBAL mul_p448_solinas
mul_p448_solinas:
sub rsp, 0x3e8 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x3b8 ], rbx; saving to stack
mov [ rsp + 0x3c0 ], rbp; saving to stack
mov [ rsp + 0x3c8 ], r12; saving to stack
mov [ rsp + 0x3d0 ], r13; saving to stack
mov [ rsp + 0x3d8 ], r14; saving to stack
mov [ rsp + 0x3e0 ], r15; saving to stack
mov rax, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x28 ]; saving arg2[5] in rdx.
mulx r10, r11, [ rsi + 0x30 ]; x44, x43<- arg1[6] * arg2[5]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbx, rbp, [ rax + 0x10 ]; x176, x175<- arg1[1] * arg2[2]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx r12, r13, [ rax + 0x20 ]; x32, x31<- arg1[7] * arg2[4]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mulx r14, r15, [ rsi + 0x28 ]; x54, x53<- arg1[5] * arg2[6]
add r13, r11; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rcx, r8, [ rax + 0x18 ]; x190, x189<- arg1[0] * arg2[3]
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, r15
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx r11, r15, [ rsi + 0x10 ]; x164, x163<- arg1[2] * arg2[1]
adcx r10, r12
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx r12, r9, [ rsi + 0x18 ]; x154, x153<- arg1[3] * arg2[0]
adox r14, r10
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r10, rdi, [ rsi + 0x20 ]; x62, x61<- arg1[4] * arg2[7]
test al, al
adox r13, rdi
adox r10, r14
adcx r13, r9
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mulx r9, r14, [ rsi + 0x8 ]; x174, x173<- arg1[1] * arg2[3]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x8 ], r9; spilling x174 to mem
mulx rdi, r9, [ rsi + 0x10 ]; x162, x161<- arg1[2] * arg2[2]
mov [ rsp + 0x10 ], rdi; spilling x162 to mem
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, r15
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r15, rdi, [ rax + 0x0 ]; x144, x143<- arg1[4] * arg2[0]
adcx r12, r10
adox r11, r12
xor r10, r10
adox r13, rbp
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mulx rbp, r12, [ rax + 0x30 ]; x22, x21<- arg1[6] * arg2[6]
adox rbx, r11
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r11, r10, [ rax + 0x20 ]; x188, x187<- arg1[0] * arg2[4]
adcx r13, r8
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x18 ], r11; spilling x188 to mem
mulx r8, r11, [ rax + 0x38 ]; x124, x123<- arg1[1] * arg2[7]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x20 ], r15; spilling x144 to mem
mov [ rsp + 0x28 ], r8; spilling x124 to mem
mulx r15, r8, [ rsi + 0x30 ]; x42, x41<- arg1[6] * arg2[6]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x30 ], r15; spilling x42 to mem
mov [ rsp + 0x38 ], rbp; spilling x22 to mem
mulx r15, rbp, [ rsi + 0x38 ]; x30, x29<- arg1[7] * arg2[5]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x40 ], r15; spilling x30 to mem
mov [ rsp + 0x48 ], r10; spilling x187 to mem
mulx r15, r10, [ rsi + 0x18 ]; x118, x117<- arg1[3] * arg2[5]
adcx rcx, rbx
mov rbx, r13; x225, copying x221 here, cause x221 is needed in a reg for other than x225, namely all: , x225, x226, size: 2
shrd rbx, rcx, 56; x225 <- x223||x221 >> 56
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x50 ], r15; spilling x118 to mem
mulx rcx, r15, [ rax + 0x20 ]; x112, x111<- arg1[4] * arg2[4]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x58 ], rcx; spilling x112 to mem
mov [ rsp + 0x60 ], rbx; spilling x225 to mem
mulx rcx, rbx, [ rax + 0x28 ]; x18, x17<- arg1[7] * arg2[5]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x68 ], rcx; spilling x18 to mem
mov [ rsp + 0x70 ], r14; spilling x173 to mem
mulx rcx, r14, [ rsi + 0x28 ]; x104, x103<- arg1[5] * arg2[3]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x78 ], rcx; spilling x104 to mem
mov [ rsp + 0x80 ], r9; spilling x161 to mem
mulx rcx, r9, [ rsi + 0x28 ]; x24, x23<- arg1[5] * arg2[7]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x88 ], rcx; spilling x24 to mem
mov [ rsp + 0x90 ], rdi; spilling x143 to mem
mulx rcx, rdi, [ rsi + 0x18 ]; x152, x151<- arg1[3] * arg2[1]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x98 ], rcx; spilling x152 to mem
mov [ rsp + 0xa0 ], rdi; spilling x151 to mem
mulx rcx, rdi, [ rax + 0x30 ]; x122, x121<- arg1[2] * arg2[6]
test al, al
adox rbx, r12
adcx rbx, r9
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx r12, r9, [ rax + 0x8 ]; x88, x87<- arg1[7] * arg2[1]
mov [ rsp + 0xa8 ], rcx; spilling x122 to mem
setc cl; spill CF x388 to reg (rcx)
clc;
adcx rbx, rbp
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0xb0 ], r12; spilling x88 to mem
mulx rbp, r12, [ rsi + 0x28 ]; x52, x51<- arg1[5] * arg2[7]
mov [ rsp + 0xb8 ], rbp; spilling x52 to mem
setc bpl; spill CF x392 to reg (rbp)
clc;
adcx rbx, r8
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov byte [ rsp + 0xc0 ], bpl; spilling byte x392 to mem
mulx r8, rbp, [ rsi + 0x30 ]; x96, x95<- arg1[6] * arg2[2]
mov [ rsp + 0xc8 ], r8; spilling x96 to mem
setc r8b; spill CF x396 to reg (r8)
clc;
adcx rbx, r12
setc r12b; spill CF x400 to reg (r12)
clc;
adcx rbx, r9
seto r9b; spill OF x384 to reg (r9)
mov byte [ rsp + 0xd0 ], r12b; spilling byte x400 to mem
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, rbp
seto bpl; spill OF x408 to reg (rbp)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rbx, r14
setc r14b; spill CF x404 to reg (r14)
clc;
adcx rbx, r15
seto r15b; spill OF x412 to reg (r15)
mov byte [ rsp + 0xd8 ], bpl; spilling byte x408 to mem
mov rbp, -0x3 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbx, r10
setc r10b; spill CF x416 to reg (r10)
clc;
adcx rbx, rdi
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx rdi, r12, [ rsi + 0x18 ]; x146, x145<- arg1[3] * arg2[4]
setc bpl; spill CF x424 to reg (rbp)
clc;
adcx rbx, r11
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov byte [ rsp + 0xe0 ], bpl; spilling byte x424 to mem
mulx r11, rbp, [ rax + 0x30 ]; x98, x97<- arg1[5] * arg2[6]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov byte [ rsp + 0xe8 ], r10b; spilling byte x416 to mem
mov byte [ rsp + 0xf0 ], r15b; spilling byte x412 to mem
mulx r10, r15, [ rsi + 0x28 ]; x132, x131<- arg1[5] * arg2[2]
mov byte [ rsp + 0xf8 ], r14b; spilling byte x404 to mem
setc r14b; spill CF x428 to reg (r14)
clc;
adcx rbx, [ rsp + 0x90 ]
mov byte [ rsp + 0x100 ], r14b; spilling byte x428 to mem
setc r14b; spill CF x432 to reg (r14)
clc;
adcx rbx, [ rsp + 0xa0 ]
mov byte [ rsp + 0x108 ], r14b; spilling byte x432 to mem
setc r14b; spill CF x436 to reg (r14)
clc;
adcx rbx, [ rsp + 0x80 ]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov byte [ rsp + 0x110 ], r14b; spilling byte x436 to mem
mov [ rsp + 0x118 ], rdi; spilling x146 to mem
mulx r14, rdi, [ rsi + 0x8 ]; x168, x167<- arg1[1] * arg2[6]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x120 ], r14; spilling x168 to mem
mov byte [ rsp + 0x128 ], r8b; spilling byte x396 to mem
mulx r14, r8, [ rsi + 0x0 ]; x182, x181<- arg1[0] * arg2[7]
mov [ rsp + 0x130 ], r14; spilling x182 to mem
setc r14b; spill CF x440 to reg (r14)
clc;
adcx rbx, [ rsp + 0x70 ]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov byte [ rsp + 0x138 ], r14b; spilling byte x440 to mem
mov [ rsp + 0x140 ], r8; spilling x181 to mem
mulx r14, r8, [ rsi + 0x38 ]; x82, x81<- arg1[7] * arg2[4]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x148 ], r10; spilling x132 to mem
mov [ rsp + 0x150 ], rdi; spilling x167 to mem
mulx r10, rdi, [ rax + 0x28 ]; x156, x155<- arg1[2] * arg2[5]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x158 ], r10; spilling x156 to mem
mov [ rsp + 0x160 ], rdi; spilling x155 to mem
mulx r10, rdi, [ rsi + 0x30 ]; x90, x89<- arg1[6] * arg2[5]
mov [ rsp + 0x168 ], r12; spilling x145 to mem
setc r12b; spill CF x444 to reg (r12)
clc;
adcx r8, rdi
adcx r10, r14
clc;
adcx rbx, [ rsp + 0x48 ]
setc r14b; spill CF x448 to reg (r14)
clc;
adcx rbx, [ rsp + 0x60 ]
setc dil; spill CF x560 to reg (rdi)
clc;
adcx r8, rbp
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov byte [ rsp + 0x170 ], dil; spilling byte x560 to mem
mulx rbp, rdi, [ rax + 0x8 ]; x128, x127<- arg1[6] * arg2[1]
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mov byte [ rsp + 0x178 ], r14b; spilling byte x448 to mem
mov byte [ rsp + 0x180 ], r12b; spilling byte x444 to mem
mulx r14, r12, [ rsi + 0x38 ]; x126, x125<- arg1[7] * arg2[0]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x188 ], rbx; spilling x559 to mem
mov [ rsp + 0x190 ], rbp; spilling x128 to mem
mulx rbx, rbp, [ rax + 0x38 ]; x106, x105<- arg1[4] * arg2[7]
mov [ rsp + 0x198 ], r14; spilling x126 to mem
seto r14b; spill OF x420 to reg (r14)
mov [ rsp + 0x1a0 ], rbx; spilling x106 to mem
mov rbx, -0x2 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, rbp
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx rbp, rbx, [ rax + 0x18 ]; x138, x137<- arg1[4] * arg2[3]
adcx r11, r10
clc;
adcx r8, r12
setc r10b; spill CF x240 to reg (r10)
clc;
adcx r8, rdi
setc dil; spill CF x244 to reg (rdi)
clc;
adcx r8, r15
mov r15, [ rsp + 0x68 ]; load m64 x18 to register64
movzx r9, r9b
lea r15, [ r9 + r15 ]
mov r9, [ rsp + 0x38 ]
lea r15, [r9+r15]
movzx rcx, cl
lea r15, [ rcx + r15 ]
mov rcx, [ rsp + 0x88 ]
lea r15, [rcx+r15]
setc r9b; spill CF x248 to reg (r9)
clc;
adcx r8, rbx
adox r11, [ rsp + 0x1a0 ]
movzx rcx, byte [ rsp + 0xc0 ]; load byte memx392 to register64
lea r15, [ rcx + r15 ]
mov rcx, [ rsp + 0x40 ]
lea r15, [rcx+r15]
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, [ rsp + 0x168 ]
movzx r10, r10b
lea r11, [ r10 + r11 ]
mov r10, [ rsp + 0x198 ]
lea r11, [r10+r11]
seto r12b; spill OF x256 to reg (r12)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r8, [ rsp + 0x160 ]
movzx rdi, dil
lea r11, [ rdi + r11 ]
mov rdi, [ rsp + 0x190 ]
lea r11, [rdi+r11]
setc bl; spill CF x252 to reg (rbx)
clc;
adcx r8, [ rsp + 0x150 ]
movzx r9, r9b
lea r11, [ r9 + r11 ]
mov r9, [ rsp + 0x148 ]
lea r11, [r9+r11]
setc r10b; spill CF x264 to reg (r10)
clc;
adcx r8, [ rsp + 0x140 ]
movzx rdi, byte [ rsp + 0x128 ]; load byte memx396 to register64
lea r15, [ rdi + r15 ]
mov rdi, [ rsp + 0x30 ]
lea r15, [rdi+r15]
movzx rbx, bl
lea rbp, [ rbp + r11 ]
lea rbp, [ rbp + rbx ]
movzx rdi, byte [ rsp + 0xd0 ]; load byte memx400 to register64
lea r15, [ rdi + r15 ]
mov rdi, [ rsp + 0xb8 ]
lea r15, [rdi+r15]
movzx r12, r12b
lea rbp, [ r12 + rbp ]
mov r12, [ rsp + 0x118 ]
lea rbp, [r12+rbp]
movzx rdi, byte [ rsp + 0xf8 ]; load byte memx404 to register64
lea r15, [ rdi + r15 ]
mov rdi, [ rsp + 0xb0 ]
lea r15, [rdi+r15]
adox rbp, [ rsp + 0x158 ]
movzx r10, r10b
lea rbp, [ r10 + rbp ]
mov r10, [ rsp + 0x120 ]
lea rbp, [r10+rbp]
adcx rbp, [ rsp + 0x130 ]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rdi, r9, [ rax + 0x18 ]; x160, x159<- arg1[2] * arg2[3]
mov rbx, r8; x562, copying x267 here, cause x267 is needed in a reg for other than x562, namely all: , x562, x563, size: 2
shrd rbx, rbp, 56; x562 <- x269||x267 >> 56
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r12, r10, [ rax + 0x10 ]; x150, x149<- arg1[3] * arg2[2]
sar byte [ rsp + 0xd8 ], 1
adcx r15, [ rsp + 0xc8 ]
sar byte [ rsp + 0xf0 ], 1
adcx r15, [ rsp + 0x78 ]
sar byte [ rsp + 0xe8 ], 1
adcx r15, [ rsp + 0x58 ]
sar  r14b, 1
adcx r15, [ rsp + 0x50 ]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx r14, r11, [ rsi + 0x20 ]; x142, x141<- arg1[4] * arg2[1]
sar byte [ rsp + 0xe0 ], 1
adcx r15, [ rsp + 0xa8 ]
sar byte [ rsp + 0x100 ], 1
adcx r15, [ rsp + 0x28 ]
sar byte [ rsp + 0x108 ], 1
adcx r15, [ rsp + 0x20 ]
sar byte [ rsp + 0x110 ], 1
adcx r15, [ rsp + 0x98 ]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx rbp, rcx, [ rax + 0x30 ]; x28, x27<- arg1[7] * arg2[6]
mov [ rsp + 0x1a8 ], r13; spilling x221 to mem
mov r13, rbx; x564, copying x562 here, cause x562 is needed in a reg for other than x564, namely all: , x569--x570, x564--x565, size: 2
adox r13, [ rsp + 0x188 ]
mov [ rsp + 0x1b0 ], rdi; spilling x160 to mem
movzx rdi, byte [ rsp + 0x138 ]; load byte memx440 to register64
lea r15, [ rdi + r15 ]
mov rdi, [ rsp + 0x10 ]
lea r15, [rdi+r15]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x1b8 ], r12; spilling x150 to mem
mulx rdi, r12, [ rsi + 0x20 ]; x110, x109<- arg1[4] * arg2[5]
mov [ rsp + 0x1c0 ], r14; spilling x142 to mem
movzx r14, byte [ rsp + 0x180 ]; load byte memx444 to register64
lea r15, [ r14 + r15 ]
mov r14, [ rsp + 0x8 ]
lea r15, [r14+r15]
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x1c8 ], r9; spilling x159 to mem
mulx r14, r9, [ rsi + 0x28 ]; x136, x135<- arg1[5] * arg2[0]
mov [ rsp + 0x1d0 ], r14; spilling x136 to mem
movzx r14, byte [ rsp + 0x178 ]; load byte memx448 to register64
lea r15, [ r14 + r15 ]
mov r14, [ rsp + 0x18 ]
lea r15, [r14+r15]
movzx r14, byte [ rsp + 0x170 ]; load byte memx560 to register64
lea r15, [ r15 + r14 ]; r64+m8
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x1d8 ], rdi; spilling x110 to mem
mulx r14, rdi, [ rsi + 0x38 ]; x16, x15<- arg1[7] * arg2[6]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x1e0 ], r10; spilling x149 to mem
mov [ rsp + 0x1e8 ], r11; spilling x141 to mem
mulx r10, r11, [ rax + 0x18 ]; x94, x93<- arg1[6] * arg2[3]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x1f0 ], r10; spilling x94 to mem
mov [ rsp + 0x1f8 ], r9; spilling x135 to mem
mulx r10, r9, [ rax + 0x28 ]; x186, x185<- arg1[0] * arg2[5]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x200 ], r10; spilling x186 to mem
mov [ rsp + 0x208 ], r9; spilling x185 to mem
mulx r10, r9, [ rsi + 0x30 ]; x20, x19<- arg1[6] * arg2[7]
clc;
adcx rdi, r9
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x210 ], rbp; spilling x28 to mem
mulx r9, rbp, [ rax + 0x38 ]; x40, x39<- arg1[6] * arg2[7]
adcx r10, r14
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x218 ], r9; spilling x40 to mem
mulx r14, r9, [ rax + 0x38 ]; x120, x119<- arg1[2] * arg2[7]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x220 ], r14; spilling x120 to mem
mov [ rsp + 0x228 ], r9; spilling x119 to mem
mulx r14, r9, [ rax + 0x10 ]; x86, x85<- arg1[7] * arg2[2]
mov [ rsp + 0x230 ], r14; spilling x86 to mem
mov r14, 0x0 ; moving imm to reg
adox r15, r14
test al, al
adox rdi, rcx
adcx rdi, rbp
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx rcx, rbp, [ rsi + 0x28 ]; x102, x101<- arg1[5] * arg2[4]
setc r14b; spill CF x332 to reg (r14)
mov [ rsp + 0x238 ], rcx; spilling x102 to mem
seto cl; spill OF x328 to reg (rcx)
mov [ rsp + 0x240 ], r10; spilling x325 to mem
mov r10, r13; x567, copying x564 here, cause x564 is needed in a reg for other than x567, namely all: , x567, x568, size: 2
shrd r10, r15, 56; x567 <- x566||x564 >> 56
xor r15, r15
adox rdi, r9
adcx rdi, r11
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mulx r11, r9, [ rsi + 0x18 ]; x116, x115<- arg1[3] * arg2[6]
mov [ rsp + 0x248 ], r10; spilling x567 to mem
setc r10b; spill CF x340 to reg (r10)
clc;
adcx rdi, rbp
setc bpl; spill CF x344 to reg (rbp)
clc;
adcx rdi, r12
mov r12, [ rsp + 0x210 ]; load m64 x28 to register64
movzx rcx, cl
lea r12, [ rcx + r12 ]
mov rcx, [ rsp + 0x240 ]
lea r12, [rcx+r12]
setc cl; spill CF x348 to reg (rcx)
clc;
adcx rdi, r9
setc r9b; spill CF x352 to reg (r9)
clc;
adcx rdi, [ rsp + 0x228 ]
mov [ rsp + 0x250 ], r11; spilling x116 to mem
setc r11b; spill CF x356 to reg (r11)
clc;
adcx rdi, [ rsp + 0x1f8 ]
mov byte [ rsp + 0x258 ], r11b; spilling byte x356 to mem
setc r11b; spill CF x360 to reg (r11)
clc;
adcx rdi, [ rsp + 0x1e8 ]
movzx r14, r14b
lea r12, [ r14 + r12 ]
mov r14, [ rsp + 0x218 ]
lea r12, [r14+r12]
adox r12, [ rsp + 0x230 ]
movzx r10, r10b
lea r12, [ r10 + r12 ]
mov r10, [ rsp + 0x1f0 ]
lea r12, [r10+r12]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx r14, r10, [ rsi + 0x8 ]; x172, x171<- arg1[1] * arg2[4]
movzx rbp, bpl
lea r12, [ rbp + r12 ]
mov rbp, [ rsp + 0x238 ]
lea r12, [rbp+r12]
mov rbp, -0x3 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rdi, [ rsp + 0x1e0 ]
movzx rcx, cl
lea r12, [ rcx + r12 ]
mov rcx, [ rsp + 0x1d8 ]
lea r12, [rcx+r12]
movzx r9, r9b
lea r12, [ r9 + r12 ]
mov r9, [ rsp + 0x250 ]
lea r12, [r9+r12]
setc cl; spill CF x364 to reg (rcx)
clc;
adcx rdi, [ rsp + 0x1c8 ]
movzx r9, byte [ rsp + 0x258 ]; load byte memx356 to register64
lea r12, [ r9 + r12 ]
mov r9, [ rsp + 0x220 ]
lea r12, [r9+r12]
movzx r11, r11b
lea r12, [ r11 + r12 ]
mov r11, [ rsp + 0x1d0 ]
lea r12, [r11+r12]
movzx rcx, cl
lea r12, [ rcx + r12 ]
mov rcx, [ rsp + 0x1c0 ]
lea r12, [rcx+r12]
setc r9b; spill CF x372 to reg (r9)
clc;
adcx rdi, r10
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mulx r11, rcx, [ rsi + 0x0 ]; x184, x183<- arg1[0] * arg2[6]
seto r10b; spill OF x368 to reg (r10)
mov rbp, -0x3 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rdi, [ rsp + 0x208 ]
movzx r10, r10b
lea r12, [ r10 + r12 ]
mov r10, [ rsp + 0x1b8 ]
lea r12, [r10+r12]
movzx r9, r9b
lea r12, [ r9 + r12 ]
mov r9, [ rsp + 0x1b0 ]
lea r12, [r9+r12]
adcx r14, r12
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx r10, r9, [ rsi + 0x30 ]; x130, x129<- arg1[6] * arg2[0]
clc;
adcx rdi, [ rsp + 0x248 ]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mulx r12, r15, [ rsi + 0x38 ]; x26, x25<- arg1[7] * arg2[7]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x260 ], r11; spilling x184 to mem
mulx rbp, r11, [ rax + 0x8 ]; x134, x133<- arg1[5] * arg2[1]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x268 ], rcx; spilling x183 to mem
mov [ rsp + 0x270 ], rbp; spilling x134 to mem
mulx rcx, rbp, [ rax + 0x38 ]; x14, x13<- arg1[7] * arg2[7]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x278 ], r10; spilling x130 to mem
mov [ rsp + 0x280 ], r11; spilling x133 to mem
mulx r10, r11, [ rsi + 0x20 ]; x108, x107<- arg1[4] * arg2[6]
adox r14, [ rsp + 0x200 ]
adc r14, 0x0
mov [ rsp + 0x288 ], r9; spilling x129 to mem
mov r9, rdi; x580, copying x572 here, cause x572 is needed in a reg for other than x580, namely all: , x580, x581, size: 2
shrd r9, r14, 56; x580 <- x574||x572 >> 56
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x290 ], r9; spilling x580 to mem
mulx r14, r9, [ rsi + 0x38 ]; x84, x83<- arg1[7] * arg2[3]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x298 ], r10; spilling x108 to mem
mov [ rsp + 0x2a0 ], r11; spilling x107 to mem
mulx r10, r11, [ rax + 0x20 ]; x158, x157<- arg1[2] * arg2[4]
test al, al
adox rbp, r15
adcx rbp, r9
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx r15, r9, [ rsi + 0x30 ]; x92, x91<- arg1[6] * arg2[4]
adox r12, rcx
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x2a8 ], r10; spilling x158 to mem
mulx rcx, r10, [ rsi + 0x28 ]; x100, x99<- arg1[5] * arg2[5]
mov [ rsp + 0x2b0 ], r11; spilling x157 to mem
mov r11, -0x2 ; moving imm to reg
inc r11; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, r9
adcx r14, r12
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mulx r9, r12, [ rsi + 0x8 ]; x170, x169<- arg1[1] * arg2[5]
clc;
adcx rbp, r10
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r10, r11, [ rax + 0x10 ]; x140, x139<- arg1[4] * arg2[2]
adox r15, r14
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x2b8 ], r9; spilling x170 to mem
mulx r14, r9, [ rsi + 0x18 ]; x114, x113<- arg1[3] * arg2[7]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x2c0 ], r12; spilling x169 to mem
mov [ rsp + 0x2c8 ], r10; spilling x140 to mem
mulx r12, r10, [ rax + 0x18 ]; x148, x147<- arg1[3] * arg2[3]
adcx rcx, r15
add rbp, [ rsp + 0x2a0 ]; could be done better, if r0 has been u8 as well
mov r15, -0x2 ; moving imm to reg
inc r15; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, r9
adcx rcx, [ rsp + 0x298 ]
clc;
adcx rbp, [ rsp + 0x288 ]
adox r14, rcx
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rbp, [ rsp + 0x280 ]
setc r9b; spill CF x296 to reg (r9)
clc;
adcx rbp, r11
setc r11b; spill CF x304 to reg (r11)
clc;
adcx rbp, r10
movzx r9, r9b
lea r14, [ r9 + r14 ]
mov r9, [ rsp + 0x278 ]
lea r14, [r9+r14]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r10, rcx, [ rax + 0x20 ]; x68, x67<- arg1[4] * arg2[4]
adox r14, [ rsp + 0x270 ]
mov r9, -0x3 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbp, [ rsp + 0x2b0 ]
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx r15, r9, [ rsi + 0x0 ]; x196, x195<- arg1[0] * arg2[0]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x2d0 ], r15; spilling x196 to mem
mov [ rsp + 0x2d8 ], r9; spilling x195 to mem
mulx r15, r9, [ rsi + 0x38 ]; x6, x5<- arg1[7] * arg2[5]
movzx r11, r11b
lea r14, [ r11 + r14 ]
mov r11, [ rsp + 0x2c8 ]
lea r14, [r11+r14]
adcx r12, r14
adox r12, [ rsp + 0x2a8 ]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mulx r11, r14, [ rax + 0x38 ]; x12, x11<- arg1[5] * arg2[7]
mov [ rsp + 0x2e0 ], r10; spilling x68 to mem
xor r10, r10
adox rbp, [ rsp + 0x2c0 ]
adcx rbp, [ rsp + 0x268 ]
adox r12, [ rsp + 0x2b8 ]
adcx r12, [ rsp + 0x260 ]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x2e8 ], rcx; spilling x67 to mem
mulx r10, rcx, [ rsi + 0x30 ]; x50, x49<- arg1[6] * arg2[2]
mov [ rsp + 0x2f0 ], r10; spilling x50 to mem
xor r10, r10
adox rbp, [ rsp + 0x290 ]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x2f8 ], rbp; spilling x582 to mem
mulx r10, rbp, [ rax + 0x28 ]; x74, x73<- arg1[3] * arg2[5]
mov [ rsp + 0x300 ], r10; spilling x74 to mem
mov r10, 0x0 ; moving imm to reg
adox r12, r10
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x308 ], r12; spilling x584 to mem
mulx r10, r12, [ rax + 0x18 ]; x60, x59<- arg1[5] * arg2[3]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x310 ], rbp; spilling x73 to mem
mov [ rsp + 0x318 ], r10; spilling x60 to mem
mulx rbp, r10, [ rsi + 0x30 ]; x10, x9<- arg1[6] * arg2[6]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x320 ], r12; spilling x59 to mem
mov [ rsp + 0x328 ], rcx; spilling x49 to mem
mulx r12, rcx, [ rsi + 0x10 ]; x78, x77<- arg1[2] * arg2[6]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x330 ], r12; spilling x78 to mem
mov [ rsp + 0x338 ], rcx; spilling x77 to mem
mulx r12, rcx, [ rsi + 0x8 ]; x80, x79<- arg1[1] * arg2[7]
adcx r9, r10
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r9, r14
adcx rbp, r15
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx r15, r14, [ rsi + 0x38 ]; x38, x37<- arg1[7] * arg2[1]
clc;
adcx r9, r14
adox r11, rbp
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r9, [ rsp + 0x328 ]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rbp, r14, [ rax + 0x30 ]; x72, x71<- arg1[3] * arg2[6]
adcx r15, r11
adox r15, [ rsp + 0x2f0 ]
test al, al
adox r9, [ rsp + 0x320 ]
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx r11, r10, [ rsi + 0x8 ]; x180, x179<- arg1[1] * arg2[0]
adcx r9, [ rsp + 0x2e8 ]
adox r15, [ rsp + 0x318 ]
mov [ rsp + 0x340 ], r11; spilling x180 to mem
mov r11, -0x2 ; moving imm to reg
inc r11; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r9, [ rsp + 0x310 ]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x348 ], r10; spilling x179 to mem
mulx r11, r10, [ rax + 0x28 ]; x66, x65<- arg1[4] * arg2[5]
adcx r15, [ rsp + 0x2e0 ]
clc;
adcx r9, [ rsp + 0x338 ]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x350 ], rbp; spilling x72 to mem
mov [ rsp + 0x358 ], r14; spilling x71 to mem
mulx rbp, r14, [ rax + 0x18 ]; x48, x47<- arg1[6] * arg2[3]
adox r15, [ rsp + 0x300 ]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x360 ], r11; spilling x66 to mem
mov [ rsp + 0x368 ], r10; spilling x65 to mem
mulx r11, r10, [ rsi + 0x30 ]; x8, x7<- arg1[6] * arg2[7]
adcx r15, [ rsp + 0x330 ]
test al, al
adox r9, rcx
adcx r9, [ rsp + 0x2d8 ]
adox r12, r15
adcx r12, [ rsp + 0x2d0 ]
test al, al
adox rbx, r9
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx rcx, r15, [ rax + 0x30 ]; x4, x3<- arg1[7] * arg2[6]
mov r9, 0x0 ; moving imm to reg
adox r12, r9
mov r9, rbx; x575, copying x569 here, cause x569 is needed in a reg for other than x575, namely all: , x575, x576, size: 2
shrd r9, r12, 56; x575 <- x571||x569 >> 56
test al, al
adox r15, r10
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx r10, r12, [ rax + 0x10 ]; x36, x35<- arg1[7] * arg2[2]
adox r11, rcx
adcx r15, r12
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mulx rcx, r12, [ rax + 0x20 ]; x58, x57<- arg1[5] * arg2[4]
adcx r10, r11
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x370 ], r9; spilling x575 to mem
mulx r11, r9, [ rax + 0x8 ]; x194, x193<- arg1[0] * arg2[1]
add r15, r14; could be done better, if r0 has been u8 as well
adcx rbp, r10
test al, al
adox r15, r12
adcx r15, [ rsp + 0x368 ]
adox rcx, rbp
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx r14, r12, [ rsi + 0x10 ]; x166, x165<- arg1[2] * arg2[0]
adcx rcx, [ rsp + 0x360 ]
xor r10, r10
adox r15, [ rsp + 0x358 ]
adox rcx, [ rsp + 0x350 ]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mulx rbp, r10, [ rsi + 0x10 ]; x76, x75<- arg1[2] * arg2[7]
adcx r15, r10
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x378 ], r14; spilling x166 to mem
mulx r10, r14, [ rsi + 0x38 ]; x2, x1<- arg1[7] * arg2[7]
adcx rbp, rcx
xor rcx, rcx
adox r15, [ rsp + 0x348 ]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x380 ], r12; spilling x165 to mem
mulx rcx, r12, [ rax + 0x38 ]; x70, x69<- arg1[3] * arg2[7]
adcx r15, r9
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x388 ], rcx; spilling x70 to mem
mulx r9, rcx, [ rax + 0x10 ]; x192, x191<- arg1[0] * arg2[2]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x390 ], r9; spilling x192 to mem
mov [ rsp + 0x398 ], rcx; spilling x191 to mem
mulx r9, rcx, [ rax + 0x18 ]; x34, x33<- arg1[7] * arg2[3]
adox rbp, [ rsp + 0x340 ]
adcx r11, rbp
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x3a0 ], r12; spilling x69 to mem
mulx rbp, r12, [ rax + 0x20 ]; x46, x45<- arg1[6] * arg2[4]
test al, al
adox r15, [ rsp + 0x370 ]
mov [ rsp + 0x3a8 ], r15; spilling x577 to mem
mov r15, 0x0 ; moving imm to reg
adox r11, r15
adcx r14, rcx
mov rcx, -0x3 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r14, r12
adcx r9, r10
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mulx r10, r12, [ rax + 0x28 ]; x56, x55<- arg1[5] * arg2[5]
adox rbp, r9
mov r9, [ rsp + 0x3a8 ]; load m64 x577 to register64
mov r15, r9; x585, copying x577 here, cause x577 is needed in a reg for other than x585, namely all: , x586, x585, size: 2
shrd r15, r11, 56; x585 <- x579||x577 >> 56
test al, al
adox r14, r12
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx r11, r12, [ rsi + 0x8 ]; x178, x177<- arg1[1] * arg2[1]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x3b0 ], r15; spilling x585 to mem
mulx rcx, r15, [ rsi + 0x20 ]; x64, x63<- arg1[4] * arg2[6]
adcx r14, r15
adox r10, rbp
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, [ rsp + 0x3a0 ]
adcx rcx, r10
clc;
adcx r14, [ rsp + 0x380 ]
adox rcx, [ rsp + 0x388 ]
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r14, r12
adcx rcx, [ rsp + 0x378 ]
adox r11, rcx
mov r12, [ rsp + 0x2f8 ]; load m64 x582 to register64
mov r15, [ rsp + 0x308 ]; load m64 x584 to register64
mov r10, r12; x590, copying x582 here, cause x582 is needed in a reg for other than x590, namely all: , x590, x591, size: 2
shrd r10, r15, 56; x590 <- x584||x582 >> 56
xor r15, r15
adox r14, [ rsp + 0x398 ]
adox r11, [ rsp + 0x390 ]
mov rbp, 0xffffffffffffff ; moving imm to reg
and r8, rbp; x563 <- x267&0xffffffffffffff
adox r14, [ rsp + 0x3b0 ]
seto cl; spill OF x588 to reg (rcx)
mov r15, [ rsp + 0x1a8 ]; x226, copying x221 here, cause x221 is needed in a reg for other than x226, namely all: , x226, size: 1
and r15, rbp; x226 <- x221&0xffffffffffffff
and rbx, rbp; x576 <- x569&0xffffffffffffff
lea r10, [ r10 + r8 ]
movzx r8, cl; x589, copying x588 here, cause x588 is needed in a reg for other than x589, namely all: , x589, size: 1
lea r8, [ r8 + r11 ]
mov r11, r10; x597, copying x592 here, cause x592 is needed in a reg for other than x597, namely all: , x597, x596, size: 2
and r11, rbp; x597 <- x592&0xffffffffffffff
and r13, rbp; x568 <- x564&0xffffffffffffff
mov rcx, r14; x593, copying x587 here, cause x587 is needed in a reg for other than x593, namely all: , x593, x594, size: 2
shrd rcx, r8, 56; x593 <- x589||x587 >> 56
lea rcx, [ rcx + r15 ]
and r9, rbp; x586 <- x577&0xffffffffffffff
and r12, rbp; x591 <- x582&0xffffffffffffff
mov r15, rcx; x599, copying x595 here, cause x595 is needed in a reg for other than x599, namely all: , x599, x598, size: 2
and r15, rbp; x599 <- x595&0xffffffffffffff
mov r8, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r8 + 0x38 ], r11; out1[7] = x597
shr r10, 56; x596 <- x592>> 56
and r14, rbp; x594 <- x587&0xffffffffffffff
shr rcx, 56; x598 <- x595>> 56
mov [ r8 + 0x30 ], r12; out1[6] = x591
mov [ r8 + 0x10 ], r14; out1[2] = x594
lea r13, [ r13 + r10 ]
mov [ r8 + 0x18 ], r15; out1[3] = x599
lea rbx, [ rbx + r10 ]
mov r11, rbx; x607, copying x601 here, cause x601 is needed in a reg for other than x607, namely all: , x606, x607, size: 2
and r11, rbp; x607 <- x601&0xffffffffffffff
shr rbx, 56; x606 <- x601>> 56
lea rbx, [ rbx + r9 ]
lea rcx, [ rcx + r13 ]
mov [ r8 + 0x8 ], rbx; out1[1] = x608
mov [ r8 + 0x0 ], r11; out1[0] = x607
mov r9, rcx; x604, copying x602 here, cause x602 is needed in a reg for other than x604, namely all: , x603, x604, size: 2
and r9, rbp; x604 <- x602&0xffffffffffffff
shr rcx, 56; x603 <- x602>> 56
and rdi, rbp; x581 <- x572&0xffffffffffffff
mov [ r8 + 0x20 ], r9; out1[4] = x604
lea rcx, [ rcx + rdi ]
mov [ r8 + 0x28 ], rcx; out1[5] = x605
mov rbx, [ rsp + 0x3b8 ]; restoring from stack
mov rbp, [ rsp + 0x3c0 ]; restoring from stack
mov r12, [ rsp + 0x3c8 ]; restoring from stack
mov r13, [ rsp + 0x3d0 ]; restoring from stack
mov r14, [ rsp + 0x3d8 ]; restoring from stack
mov r15, [ rsp + 0x3e0 ]; restoring from stack
add rsp, 0x3e8 
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; clocked at 2200 MHz
; first cyclecount 293.25, best 178.16, lastGood 185.6578947368421
; seed 3983286574960897 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5340716 ms / 60000 runs=> 89.01193333333333ms/run
; Time spent for assembling and measureing (initial batch_size=77, initial num_batches=101): 240387 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.04501025705167622
; number reverted permutation/ tried permutation: 18554 / 30161 =61.517%
; number reverted decision/ tried decision: 15953 / 29840 =53.462%