SECTION .text
	GLOBAL mul_p448_solinas
mul_p448_solinas:
sub rsp, 0x3a8 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x378 ], rbx; saving to stack
mov [ rsp + 0x380 ], rbp; saving to stack
mov [ rsp + 0x388 ], r12; saving to stack
mov [ rsp + 0x390 ], r13; saving to stack
mov [ rsp + 0x398 ], r14; saving to stack
mov [ rsp + 0x3a0 ], r15; saving to stack
mov rax, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x20 ]; saving arg2[4] in rdx.
mulx r10, r11, [ rsi + 0x38 ]; x32, x31<- arg1[7] * arg2[4]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mulx rbx, rbp, [ rsi + 0x30 ]; x44, x43<- arg1[6] * arg2[5]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mulx r12, r13, [ rax + 0x30 ]; x54, x53<- arg1[5] * arg2[6]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r14, r15, [ rax + 0x0 ]; x154, x153<- arg1[3] * arg2[0]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx rcx, r8, [ rsi + 0x10 ]; x164, x163<- arg1[2] * arg2[1]
xor r9, r9
adox r11, rbp
adox rbx, r10
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mulx r10, rbp, [ rsi + 0x20 ]; x62, x61<- arg1[4] * arg2[7]
adcx r11, r13
mov r13, -0x3 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r11, rbp
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbp, r9, [ rax + 0x10 ]; x176, x175<- arg1[1] * arg2[2]
adcx r12, rbx
adox r10, r12
add r11, r15; could be done better, if r0 has been u8 as well
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, r8
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r15, r8, [ rax + 0x18 ]; x190, x189<- arg1[0] * arg2[3]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mulx rbx, r12, [ rsi + 0x38 ]; x30, x29<- arg1[7] * arg2[5]
adcx r14, r10
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r10, r13, [ rax + 0x8 ]; x152, x151<- arg1[3] * arg2[1]
adox rcx, r14
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r14, rdi, [ rsi + 0x0 ]; x188, x187<- arg1[0] * arg2[4]
add r11, r9; could be done better, if r0 has been u8 as well
adcx rbp, rcx
xor r9, r9
adox r11, r8
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r8, rcx, [ rax + 0x28 ]; x118, x117<- arg1[3] * arg2[5]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x8 ], r14; spilling x188 to mem
mulx r9, r14, [ rsi + 0x30 ]; x42, x41<- arg1[6] * arg2[6]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x10 ], r10; spilling x152 to mem
mov [ rsp + 0x18 ], r8; spilling x118 to mem
mulx r10, r8, [ rax + 0x10 ]; x162, x161<- arg1[2] * arg2[2]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x20 ], r10; spilling x162 to mem
mov [ rsp + 0x28 ], r9; spilling x42 to mem
mulx r10, r9, [ rsi + 0x28 ]; x104, x103<- arg1[5] * arg2[3]
adox r15, rbp
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x30 ], r10; spilling x104 to mem
mulx rbp, r10, [ rax + 0x20 ]; x112, x111<- arg1[4] * arg2[4]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x38 ], rbp; spilling x112 to mem
mov [ rsp + 0x40 ], rbx; spilling x30 to mem
mulx rbp, rbx, [ rax + 0x28 ]; x18, x17<- arg1[7] * arg2[5]
mov [ rsp + 0x48 ], rbp; spilling x18 to mem
mov rbp, r11; x225, copying x221 here, cause x221 is needed in a reg for other than x225, namely all: , x225, x226, size: 2
shrd rbp, r15, 56; x225 <- x223||x221 >> 56
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x50 ], rbp; spilling x225 to mem
mulx r15, rbp, [ rax + 0x30 ]; x22, x21<- arg1[6] * arg2[6]
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x58 ], r15; spilling x22 to mem
mov [ rsp + 0x60 ], rdi; spilling x187 to mem
mulx r15, rdi, [ rsi + 0x20 ]; x144, x143<- arg1[4] * arg2[0]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x68 ], r15; spilling x144 to mem
mov [ rsp + 0x70 ], r8; spilling x161 to mem
mulx r15, r8, [ rsi + 0x10 ]; x122, x121<- arg1[2] * arg2[6]
mov [ rsp + 0x78 ], r15; spilling x122 to mem
xor r15, r15
adox rbx, rbp
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbp, r15, [ rax + 0x18 ]; x174, x173<- arg1[1] * arg2[3]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x80 ], rbp; spilling x174 to mem
mov [ rsp + 0x88 ], r15; spilling x173 to mem
mulx rbp, r15, [ rsi + 0x28 ]; x24, x23<- arg1[5] * arg2[7]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x90 ], rbp; spilling x24 to mem
mov [ rsp + 0x98 ], r13; spilling x151 to mem
mulx rbp, r13, [ rsi + 0x28 ]; x52, x51<- arg1[5] * arg2[7]
adcx rbx, r15
seto r15b; spill OF x384 to reg (r15)
mov [ rsp + 0xa0 ], rbp; spilling x52 to mem
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, r12
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r12, rbp, [ rax + 0x38 ]; x124, x123<- arg1[1] * arg2[7]
mov [ rsp + 0xa8 ], r12; spilling x124 to mem
setc r12b; spill CF x388 to reg (r12)
clc;
adcx rbx, r14
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov byte [ rsp + 0xb0 ], r12b; spilling byte x388 to mem
mulx r14, r12, [ rsi + 0x30 ]; x96, x95<- arg1[6] * arg2[2]
mov [ rsp + 0xb8 ], r14; spilling x96 to mem
setc r14b; spill CF x396 to reg (r14)
clc;
adcx rbx, r13
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov byte [ rsp + 0xc0 ], r14b; spilling byte x396 to mem
mulx r13, r14, [ rsi + 0x38 ]; x88, x87<- arg1[7] * arg2[1]
mov [ rsp + 0xc8 ], r13; spilling x88 to mem
setc r13b; spill CF x400 to reg (r13)
clc;
adcx rbx, r14
setc r14b; spill CF x404 to reg (r14)
clc;
adcx rbx, r12
seto r12b; spill OF x392 to reg (r12)
mov byte [ rsp + 0xd0 ], r14b; spilling byte x404 to mem
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, r9
seto r9b; spill OF x412 to reg (r9)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rbx, r10
setc r10b; spill CF x408 to reg (r10)
clc;
adcx rbx, rcx
setc cl; spill CF x420 to reg (rcx)
clc;
adcx rbx, r8
setc r8b; spill CF x424 to reg (r8)
clc;
adcx rbx, rbp
seto bpl; spill OF x416 to reg (rbp)
mov byte [ rsp + 0xd8 ], r8b; spilling byte x424 to mem
mov r8, -0x3 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbx, rdi
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rdi, r14, [ rax + 0x20 ]; x146, x145<- arg1[3] * arg2[4]
setc r8b; spill CF x428 to reg (r8)
clc;
adcx rbx, [ rsp + 0x98 ]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov byte [ rsp + 0xe0 ], r8b; spilling byte x428 to mem
mov byte [ rsp + 0xe8 ], cl; spilling byte x420 to mem
mulx r8, rcx, [ rax + 0x38 ]; x182, x181<- arg1[0] * arg2[7]
mov byte [ rsp + 0xf0 ], bpl; spilling byte x416 to mem
setc bpl; spill CF x436 to reg (rbp)
clc;
adcx rbx, [ rsp + 0x70 ]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov byte [ rsp + 0xf8 ], bpl; spilling byte x436 to mem
mov byte [ rsp + 0x100 ], r9b; spilling byte x412 to mem
mulx rbp, r9, [ rax + 0x28 ]; x90, x89<- arg1[6] * arg2[5]
mov byte [ rsp + 0x108 ], r10b; spilling byte x408 to mem
setc r10b; spill CF x440 to reg (r10)
clc;
adcx rbx, [ rsp + 0x88 ]
mov byte [ rsp + 0x110 ], r10b; spilling byte x440 to mem
setc r10b; spill CF x444 to reg (r10)
clc;
adcx rbx, [ rsp + 0x60 ]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov byte [ rsp + 0x118 ], r10b; spilling byte x444 to mem
mov byte [ rsp + 0x120 ], r13b; spilling byte x400 to mem
mulx r10, r13, [ rax + 0x20 ]; x82, x81<- arg1[7] * arg2[4]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x128 ], r8; spilling x182 to mem
mov [ rsp + 0x130 ], rcx; spilling x181 to mem
mulx r8, rcx, [ rax + 0x0 ]; x126, x125<- arg1[7] * arg2[0]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov byte [ rsp + 0x138 ], r12b; spilling byte x392 to mem
mov [ rsp + 0x140 ], rdi; spilling x146 to mem
mulx r12, rdi, [ rsi + 0x20 ]; x106, x105<- arg1[4] * arg2[7]
mov [ rsp + 0x148 ], r14; spilling x145 to mem
setc r14b; spill CF x448 to reg (r14)
clc;
adcx r13, r9
setc r9b; spill CF x228 to reg (r9)
clc;
adcx rbx, [ rsp + 0x50 ]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov byte [ rsp + 0x150 ], r14b; spilling byte x448 to mem
mov [ rsp + 0x158 ], rbx; spilling x559 to mem
mulx r14, rbx, [ rsi + 0x28 ]; x132, x131<- arg1[5] * arg2[2]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x160 ], r14; spilling x132 to mem
mov [ rsp + 0x168 ], rbx; spilling x131 to mem
mulx r14, rbx, [ rsi + 0x28 ]; x98, x97<- arg1[5] * arg2[6]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov byte [ rsp + 0x170 ], r15b; spilling byte x384 to mem
mov [ rsp + 0x178 ], r8; spilling x126 to mem
mulx r15, r8, [ rax + 0x18 ]; x138, x137<- arg1[4] * arg2[3]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x180 ], r15; spilling x138 to mem
mov [ rsp + 0x188 ], r8; spilling x137 to mem
mulx r15, r8, [ rsi + 0x8 ]; x168, x167<- arg1[1] * arg2[6]
mov [ rsp + 0x190 ], r15; spilling x168 to mem
setc r15b; spill CF x560 to reg (r15)
clc;
adcx r13, rbx
setc bl; spill CF x232 to reg (rbx)
clc;
adcx r13, rdi
movzx r9, r9b
lea rbp, [ rbp + r10 ]
lea rbp, [ rbp + r9 ]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r10, rdi, [ rax + 0x28 ]; x156, x155<- arg1[2] * arg2[5]
movzx rbx, bl
lea r14, [ r14 + rbp ]
lea r14, [ r14 + rbx ]
adcx r12, r14
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx r9, rbx, [ rsi + 0x30 ]; x128, x127<- arg1[6] * arg2[1]
clc;
adcx r13, rcx
seto cl; spill OF x432 to reg (rcx)
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, rbx
adcx r12, [ rsp + 0x178 ]
mov r14, [ rsp + 0x58 ]; load m64 x22 to register64
movzx rbx, byte [ rsp + 0x170 ]; load byte memx384 to register64
lea r14, [ rbx + r14 ]
mov rbx, [ rsp + 0x48 ]
lea r14, [rbx+r14]
adox r9, r12
xor rbx, rbx
adox r13, [ rsp + 0x168 ]
adox r9, [ rsp + 0x160 ]
adcx r13, [ rsp + 0x188 ]
mov r12, -0x3 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r13, [ rsp + 0x148 ]
adcx r9, [ rsp + 0x180 ]
adox r9, [ rsp + 0x140 ]
add r13, rdi; could be done better, if r0 has been u8 as well
adcx r10, r9
sar byte [ rsp + 0xb0 ], 1
adcx r14, [ rsp + 0x90 ]
adox r13, r8
adox r10, [ rsp + 0x190 ]
sar byte [ rsp + 0x138 ], 1
adcx r14, [ rsp + 0x40 ]
sar byte [ rsp + 0xc0 ], 1
adcx r14, [ rsp + 0x28 ]
adox r13, [ rsp + 0x130 ]
adox r10, [ rsp + 0x128 ]
sar byte [ rsp + 0x120 ], 1
adcx r14, [ rsp + 0xa0 ]
mov r8, r13; x562, copying x267 here, cause x267 is needed in a reg for other than x562, namely all: , x562, x563, size: 2
shrd r8, r10, 56; x562 <- x269||x267 >> 56
sar byte [ rsp + 0xd0 ], 1
adcx r14, [ rsp + 0xc8 ]
sar byte [ rsp + 0x108 ], 1
adcx r14, [ rsp + 0xb8 ]
mov rdi, r8; x564, copying x562 here, cause x562 is needed in a reg for other than x564, namely all: , x564--x565, x569--x570, size: 2
adox rdi, [ rsp + 0x158 ]
movzx r9, byte [ rsp + 0x100 ]; load byte memx412 to register64
lea r14, [ r9 + r14 ]
mov r9, [ rsp + 0x30 ]
lea r14, [r9+r14]
mov r9, 0xffffffffffffff ; moving imm to reg
seto r10b; spill OF x565 to reg (r10)
mov rbx, rdi; x568, copying x564 here, cause x564 is needed in a reg for other than x568, namely all: , x568, x567, size: 2
and rbx, r9; x568 <- x564&0xffffffffffffff
sar byte [ rsp + 0xf0 ], 1
adcx r14, [ rsp + 0x38 ]
sar byte [ rsp + 0xe8 ], 1
adcx r14, [ rsp + 0x18 ]
sar byte [ rsp + 0xd8 ], 1
adcx r14, [ rsp + 0x78 ]
sar byte [ rsp + 0xe0 ], 1
adcx r14, [ rsp + 0xa8 ]
sar  cl, 1
adcx r14, [ rsp + 0x68 ]
sar byte [ rsp + 0xf8 ], 1
adcx r14, [ rsp + 0x10 ]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx rcx, r12, [ rsi + 0x38 ]; x86, x85<- arg1[7] * arg2[2]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbp, r9, [ rax + 0x20 ]; x172, x171<- arg1[1] * arg2[4]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x198 ], r11; spilling x221 to mem
mov [ rsp + 0x1a0 ], rbx; spilling x568 to mem
mulx r11, rbx, [ rax + 0x30 ]; x16, x15<- arg1[7] * arg2[6]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x1a8 ], rbp; spilling x172 to mem
mov [ rsp + 0x1b0 ], r9; spilling x171 to mem
mulx rbp, r9, [ rsi + 0x18 ]; x150, x149<- arg1[3] * arg2[2]
sar byte [ rsp + 0x110 ], 1
adcx r14, [ rsp + 0x20 ]
sar byte [ rsp + 0x118 ], 1
adcx r14, [ rsp + 0x80 ]
sar byte [ rsp + 0x150 ], 1
adcx r14, [ rsp + 0x8 ]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x1b8 ], rbp; spilling x150 to mem
mov [ rsp + 0x1c0 ], r9; spilling x149 to mem
mulx rbp, r9, [ rsi + 0x10 ]; x160, x159<- arg1[2] * arg2[3]
mov [ rsp + 0x1c8 ], rbp; spilling x160 to mem
movzx rbp, r15b; x561, copying x560 here, cause x560 is needed in a reg for other than x561, namely all: , x561, size: 1
lea rbp, [ rbp + r14 ]
movzx r15, r10b; x566, copying x565 here, cause x565 is needed in a reg for other than x566, namely all: , x566, size: 1
lea r15, [ r15 + rbp ]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mulx r10, r14, [ rsi + 0x20 ]; x110, x109<- arg1[4] * arg2[5]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x1d0 ], r9; spilling x159 to mem
mulx rbp, r9, [ rax + 0x20 ]; x102, x101<- arg1[5] * arg2[4]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x1d8 ], r10; spilling x110 to mem
mov [ rsp + 0x1e0 ], rbp; spilling x102 to mem
mulx r10, rbp, [ rsi + 0x20 ]; x142, x141<- arg1[4] * arg2[1]
shrd rdi, r15, 56; x567 <- x566||x564 >> 56
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x1e8 ], rdi; spilling x567 to mem
mulx r15, rdi, [ rax + 0x28 ]; x186, x185<- arg1[0] * arg2[5]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x1f0 ], r15; spilling x186 to mem
mov [ rsp + 0x1f8 ], r10; spilling x142 to mem
mulx r15, r10, [ rsi + 0x30 ]; x94, x93<- arg1[6] * arg2[3]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x200 ], rdi; spilling x185 to mem
mov [ rsp + 0x208 ], rbp; spilling x141 to mem
mulx rdi, rbp, [ rax + 0x30 ]; x28, x27<- arg1[7] * arg2[6]
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x210 ], r15; spilling x94 to mem
mov [ rsp + 0x218 ], rcx; spilling x86 to mem
mulx r15, rcx, [ rsi + 0x28 ]; x136, x135<- arg1[5] * arg2[0]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x220 ], r15; spilling x136 to mem
mov [ rsp + 0x228 ], rcx; spilling x135 to mem
mulx r15, rcx, [ rsi + 0x30 ]; x40, x39<- arg1[6] * arg2[7]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x230 ], r15; spilling x40 to mem
mov [ rsp + 0x238 ], rdi; spilling x28 to mem
mulx r15, rdi, [ rax + 0x38 ]; x20, x19<- arg1[6] * arg2[7]
add rbx, rdi; could be done better, if r0 has been u8 as well
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, rbp
setc bpl; spill CF x324 to reg (rbp)
clc;
adcx rbx, rcx
setc cl; spill CF x332 to reg (rcx)
clc;
adcx rbx, r12
setc r12b; spill CF x336 to reg (r12)
clc;
adcx rbx, r10
setc r10b; spill CF x340 to reg (r10)
clc;
adcx rbx, r9
movzx rbp, bpl
lea r15, [ r15 + r11 ]
lea r15, [ r15 + rbp ]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mulx r11, r9, [ rsi + 0x18 ]; x116, x115<- arg1[3] * arg2[6]
setc bpl; spill CF x344 to reg (rbp)
clc;
adcx rbx, r14
setc r14b; spill CF x348 to reg (r14)
clc;
adcx rbx, r9
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mulx r9, rdi, [ rsi + 0x10 ]; x120, x119<- arg1[2] * arg2[7]
adox r15, [ rsp + 0x238 ]
movzx rcx, cl
lea r15, [ rcx + r15 ]
mov rcx, [ rsp + 0x230 ]
lea r15, [rcx+r15]
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, rdi
movzx r12, r12b
lea r15, [ r12 + r15 ]
mov r12, [ rsp + 0x218 ]
lea r15, [r12+r15]
setc r12b; spill CF x352 to reg (r12)
clc;
adcx rbx, [ rsp + 0x228 ]
movzx r10, r10b
lea r15, [ r10 + r15 ]
mov r10, [ rsp + 0x210 ]
lea r15, [r10+r15]
movzx rbp, bpl
lea r15, [ rbp + r15 ]
mov rbp, [ rsp + 0x1e0 ]
lea r15, [rbp+r15]
movzx r14, r14b
lea r15, [ r14 + r15 ]
mov r14, [ rsp + 0x1d8 ]
lea r15, [r14+r15]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx r10, rbp, [ rsi + 0x20 ]; x140, x139<- arg1[4] * arg2[2]
setc r14b; spill CF x360 to reg (r14)
clc;
adcx rbx, [ rsp + 0x208 ]
setc dil; spill CF x364 to reg (rdi)
clc;
adcx rbx, [ rsp + 0x1c0 ]
seto cl; spill OF x356 to reg (rcx)
mov [ rsp + 0x240 ], r10; spilling x140 to mem
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, [ rsp + 0x1d0 ]
setc r10b; spill CF x368 to reg (r10)
clc;
adcx rbx, [ rsp + 0x1b0 ]
movzx r12, r12b
lea r11, [ r11 + r15 ]
lea r11, [ r11 + r12 ]
movzx rcx, cl
lea r9, [ r9 + r11 ]
lea r9, [ r9 + rcx ]
setc r12b; spill CF x376 to reg (r12)
clc;
adcx rbx, [ rsp + 0x200 ]
movzx r14, r14b
lea r9, [ r14 + r9 ]
mov r14, [ rsp + 0x220 ]
lea r9, [r14+r9]
movzx rdi, dil
lea r9, [ rdi + r9 ]
mov rdi, [ rsp + 0x1f8 ]
lea r9, [rdi+r9]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx rcx, r14, [ rsi + 0x28 ]; x134, x133<- arg1[5] * arg2[1]
movzx r10, r10b
lea r9, [ r10 + r9 ]
mov r10, [ rsp + 0x1b8 ]
lea r9, [r10+r9]
setc r15b; spill CF x380 to reg (r15)
clc;
adcx rbx, [ rsp + 0x1e8 ]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx rdi, r10, [ rsi + 0x10 ]; x158, x157<- arg1[2] * arg2[4]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x248 ], rdi; spilling x158 to mem
mulx r11, rdi, [ rax + 0x30 ]; x184, x183<- arg1[0] * arg2[6]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x250 ], r11; spilling x184 to mem
mov [ rsp + 0x258 ], rdi; spilling x183 to mem
mulx r11, rdi, [ rax + 0x28 ]; x170, x169<- arg1[1] * arg2[5]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x260 ], r11; spilling x170 to mem
mov [ rsp + 0x268 ], rcx; spilling x134 to mem
mulx r11, rcx, [ rsi + 0x18 ]; x148, x147<- arg1[3] * arg2[3]
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x270 ], r11; spilling x148 to mem
mov [ rsp + 0x278 ], rdi; spilling x169 to mem
mulx r11, rdi, [ rsi + 0x30 ]; x130, x129<- arg1[6] * arg2[0]
adox r9, [ rsp + 0x1c8 ]
movzx r12, r12b
lea r9, [ r12 + r9 ]
mov r12, [ rsp + 0x1a8 ]
lea r9, [r12+r9]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x280 ], r11; spilling x130 to mem
mulx r12, r11, [ rax + 0x38 ]; x14, x13<- arg1[7] * arg2[7]
movzx r15, r15b
lea r9, [ r15 + r9 ]
mov r15, [ rsp + 0x1f0 ]
lea r9, [r15+r9]
adc r9, 0x0
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x288 ], r10; spilling x157 to mem
mulx r15, r10, [ rax + 0x30 ]; x108, x107<- arg1[4] * arg2[6]
mov [ rsp + 0x290 ], rcx; spilling x147 to mem
mov rcx, rbx; x580, copying x572 here, cause x572 is needed in a reg for other than x580, namely all: , x581, x580, size: 2
shrd rcx, r9, 56; x580 <- x574||x572 >> 56
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x298 ], rcx; spilling x580 to mem
mulx r9, rcx, [ rsi + 0x38 ]; x84, x83<- arg1[7] * arg2[3]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x2a0 ], r15; spilling x108 to mem
mov [ rsp + 0x2a8 ], rbp; spilling x139 to mem
mulx r15, rbp, [ rsi + 0x38 ]; x26, x25<- arg1[7] * arg2[7]
add r11, rbp; could be done better, if r0 has been u8 as well
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, rcx
adcx r15, r12
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mulx r12, rcx, [ rax + 0x20 ]; x92, x91<- arg1[6] * arg2[4]
clc;
adcx r11, rcx
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mulx rcx, rbp, [ rax + 0x28 ]; x100, x99<- arg1[5] * arg2[5]
adox r9, r15
adcx r12, r9
add r11, rbp; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r15, rbp, [ rax + 0x38 ]; x114, x113<- arg1[3] * arg2[7]
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, r10
adcx rcx, r12
clc;
adcx r11, rbp
setc r10b; spill CF x292 to reg (r10)
clc;
adcx r11, rdi
setc dil; spill CF x296 to reg (rdi)
clc;
adcx r11, r14
setc r14b; spill CF x300 to reg (r14)
clc;
adcx r11, [ rsp + 0x2a8 ]
adox rcx, [ rsp + 0x2a0 ]
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r11, [ rsp + 0x290 ]
setc r12b; spill CF x304 to reg (r12)
clc;
adcx r11, [ rsp + 0x288 ]
movzx r10, r10b
lea r15, [ r15 + rcx ]
lea r15, [ r15 + r10 ]
setc bpl; spill CF x312 to reg (rbp)
clc;
adcx r11, [ rsp + 0x278 ]
movzx rdi, dil
lea r15, [ rdi + r15 ]
mov rdi, [ rsp + 0x280 ]
lea r15, [rdi+r15]
movzx r14, r14b
lea r15, [ r14 + r15 ]
mov r14, [ rsp + 0x268 ]
lea r15, [r14+r15]
movzx r12, r12b
lea r15, [ r12 + r15 ]
mov r12, [ rsp + 0x240 ]
lea r15, [r12+r15]
adox r15, [ rsp + 0x270 ]
movzx rbp, bpl
lea r15, [ rbp + r15 ]
mov rbp, [ rsp + 0x248 ]
lea r15, [rbp+r15]
adcx r15, [ rsp + 0x260 ]
xor r10, r10
adox r11, [ rsp + 0x258 ]
adcx r11, [ rsp + 0x298 ]
adox r15, [ rsp + 0x250 ]
adc r15, 0x0
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r9, rdi, [ rax + 0x28 ]; x74, x73<- arg1[3] * arg2[5]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r14, r12, [ rax + 0x30 ]; x78, x77<- arg1[2] * arg2[6]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx rcx, rbp, [ rax + 0x20 ]; x68, x67<- arg1[4] * arg2[4]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x2b0 ], r14; spilling x78 to mem
mulx r10, r14, [ rsi + 0x28 ]; x60, x59<- arg1[5] * arg2[3]
mov [ rsp + 0x2b8 ], r12; spilling x77 to mem
mov r12, r11; x590, copying x582 here, cause x582 is needed in a reg for other than x590, namely all: , x591, x590, size: 2
shrd r12, r15, 56; x590 <- x584||x582 >> 56
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x2c0 ], r9; spilling x74 to mem
mulx r15, r9, [ rsi + 0x30 ]; x10, x9<- arg1[6] * arg2[6]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x2c8 ], rdi; spilling x73 to mem
mov [ rsp + 0x2d0 ], rcx; spilling x68 to mem
mulx rdi, rcx, [ rsi + 0x28 ]; x12, x11<- arg1[5] * arg2[7]
mov [ rsp + 0x2d8 ], rbp; spilling x67 to mem
mov rbp, 0xffffffffffffff ; moving imm to reg
and r13, rbp; x563 <- x267&0xffffffffffffff
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x2e0 ], r10; spilling x60 to mem
mulx rbp, r10, [ rsi + 0x38 ]; x6, x5<- arg1[7] * arg2[5]
adox r10, r9
lea r12, [ r12 + r13 ]
adox r15, rbp
adcx r10, rcx
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx r9, rcx, [ rsi + 0x38 ]; x38, x37<- arg1[7] * arg2[1]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r13, rbp, [ rax + 0x0 ]; x196, x195<- arg1[0] * arg2[0]
adcx rdi, r15
mov r15, r12; x596, copying x592 here, cause x592 is needed in a reg for other than x596, namely all: , x597, x596, size: 2
shr r15, 56; x596 <- x592>> 56
mov [ rsp + 0x2e8 ], r13; spilling x196 to mem
mov r13, r15; x600, copying x596 here, cause x596 is needed in a reg for other than x600, namely all: , x600, x601, size: 2
add r13, [ rsp + 0x1a0 ]
test al, al
adox r10, rcx
adox r9, rdi
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx rcx, rdi, [ rsi + 0x30 ]; x50, x49<- arg1[6] * arg2[2]
adcx r10, rdi
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r10, r14
adcx rcx, r9
adox rcx, [ rsp + 0x2e0 ]
test al, al
adox r10, [ rsp + 0x2d8 ]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx r14, r9, [ rsi + 0x38 ]; x36, x35<- arg1[7] * arg2[2]
adox rcx, [ rsp + 0x2d0 ]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x2f0 ], r13; spilling x600 to mem
mulx rdi, r13, [ rax + 0x38 ]; x80, x79<- arg1[1] * arg2[7]
adcx r10, [ rsp + 0x2c8 ]
adcx rcx, [ rsp + 0x2c0 ]
add r10, [ rsp + 0x2b8 ]; could be done better, if r0 has been u8 as well
adcx rcx, [ rsp + 0x2b0 ]
add r10, r13; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x2f8 ], r14; spilling x36 to mem
mulx r13, r14, [ rax + 0x28 ]; x66, x65<- arg1[4] * arg2[5]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x300 ], r13; spilling x66 to mem
mov [ rsp + 0x308 ], r14; spilling x65 to mem
mulx r13, r14, [ rax + 0x30 ]; x72, x71<- arg1[3] * arg2[6]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x310 ], r13; spilling x72 to mem
mov [ rsp + 0x318 ], r14; spilling x71 to mem
mulx r13, r14, [ rax + 0x8 ]; x194, x193<- arg1[0] * arg2[1]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x320 ], r13; spilling x194 to mem
mov [ rsp + 0x328 ], r14; spilling x193 to mem
mulx r13, r14, [ rax + 0x38 ]; x8, x7<- arg1[6] * arg2[7]
adcx rdi, rcx
test al, al
adox r10, rbp
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mulx rbp, rcx, [ rsi + 0x38 ]; x4, x3<- arg1[7] * arg2[6]
adcx r8, r10
adox rdi, [ rsp + 0x2e8 ]
adc rdi, 0x0
add rcx, r14; could be done better, if r0 has been u8 as well
adcx r13, rbp
mov r14, r8; x575, copying x569 here, cause x569 is needed in a reg for other than x575, namely all: , x576, x575, size: 2
shrd r14, rdi, 56; x575 <- x571||x569 >> 56
test al, al
adox rcx, r9
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r9, r10, [ rax + 0x0 ]; x180, x179<- arg1[1] * arg2[0]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mulx rbp, rdi, [ rsi + 0x30 ]; x48, x47<- arg1[6] * arg2[3]
adcx rcx, rdi
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x330 ], r14; spilling x575 to mem
mulx rdi, r14, [ rax + 0x20 ]; x58, x57<- arg1[5] * arg2[4]
adox r13, [ rsp + 0x2f8 ]
adcx rbp, r13
add rcx, r14; could be done better, if r0 has been u8 as well
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rcx, [ rsp + 0x308 ]
adcx rdi, rbp
adox rdi, [ rsp + 0x300 ]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mulx r13, rbp, [ rsi + 0x10 ]; x76, x75<- arg1[2] * arg2[7]
add rcx, [ rsp + 0x318 ]; could be done better, if r0 has been u8 as well
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rcx, rbp
adcx rdi, [ rsp + 0x310 ]
clc;
adcx rcx, r10
adox r13, rdi
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx r10, rbp, [ rsi + 0x8 ]; x178, x177<- arg1[1] * arg2[1]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mulx rdi, r14, [ rsi + 0x38 ]; x2, x1<- arg1[7] * arg2[7]
adcx r9, r13
xor r13, r13
adox rcx, [ rsp + 0x328 ]
adcx rcx, [ rsp + 0x330 ]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x338 ], r10; spilling x178 to mem
mulx r13, r10, [ rax + 0x18 ]; x34, x33<- arg1[7] * arg2[3]
adox r9, [ rsp + 0x320 ]
adc r9, 0x0
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x340 ], rbp; spilling x177 to mem
mov [ rsp + 0x348 ], rdi; spilling x2 to mem
mulx rbp, rdi, [ rax + 0x10 ]; x192, x191<- arg1[0] * arg2[2]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x350 ], rbp; spilling x192 to mem
mov [ rsp + 0x358 ], rdi; spilling x191 to mem
mulx rbp, rdi, [ rax + 0x30 ]; x64, x63<- arg1[4] * arg2[6]
mov [ rsp + 0x360 ], rbp; spilling x64 to mem
xor rbp, rbp
adox r14, r10
seto r10b; spill OF x452 to reg (r10)
mov rbp, rcx; x585, copying x577 here, cause x577 is needed in a reg for other than x585, namely all: , x586, x585, size: 2
shrd rbp, r9, 56; x585 <- x579||x577 >> 56
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x368 ], rbp; spilling x585 to mem
mulx r9, rbp, [ rsi + 0x18 ]; x70, x69<- arg1[3] * arg2[7]
sar  r10b, 1
adcx r13, [ rsp + 0x348 ]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x370 ], r9; spilling x70 to mem
mulx r10, r9, [ rsi + 0x30 ]; x46, x45<- arg1[6] * arg2[4]
adox r14, r9
adox r10, r13
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mulx r13, r9, [ rsi + 0x28 ]; x56, x55<- arg1[5] * arg2[5]
add r14, r9; could be done better, if r0 has been u8 as well
adcx r13, r10
add r14, rdi; could be done better, if r0 has been u8 as well
adcx r13, [ rsp + 0x360 ]
add r14, rbp; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rdi, rbp, [ rax + 0x0 ]; x166, x165<- arg1[2] * arg2[0]
adcx r13, [ rsp + 0x370 ]
add r14, rbp; could be done better, if r0 has been u8 as well
adcx rdi, r13
xor r10, r10
adox r14, [ rsp + 0x340 ]
adox rdi, [ rsp + 0x338 ]
adcx r14, [ rsp + 0x358 ]
adcx rdi, [ rsp + 0x350 ]
mov r9, 0xffffffffffffff ; moving imm to reg
and r8, r9; x576 <- x569&0xffffffffffffff
mov rbp, [ rsp + 0x198 ]; x226, copying x221 here, cause x221 is needed in a reg for other than x226, namely all: , x226, size: 1
and rbp, r9; x226 <- x221&0xffffffffffffff
adox r14, [ rsp + 0x368 ]
lea r8, [ r8 + r15 ]
adox rdi, r10
mov r15, r8; x607, copying x601 here, cause x601 is needed in a reg for other than x607, namely all: , x607, x606, size: 2
and r15, r9; x607 <- x601&0xffffffffffffff
mov r13, r14; x593, copying x587 here, cause x587 is needed in a reg for other than x593, namely all: , x593, x594, size: 2
shrd r13, rdi, 56; x593 <- x589||x587 >> 56
lea r13, [ r13 + rbp ]
and rcx, r9; x586 <- x577&0xffffffffffffff
mov rbp, r13; x598, copying x595 here, cause x595 is needed in a reg for other than x598, namely all: , x599, x598, size: 2
shr rbp, 56; x598 <- x595>> 56
and r12, r9; x597 <- x592&0xffffffffffffff
add rbp, [ rsp + 0x2f0 ]
mov rdi, rbp; x603, copying x602 here, cause x602 is needed in a reg for other than x603, namely all: , x604, x603, size: 2
shr rdi, 56; x603 <- x602>> 56
and rbx, r9; x581 <- x572&0xffffffffffffff
lea rdi, [ rdi + rbx ]
shr r8, 56; x606 <- x601>> 56
and r11, r9; x591 <- x582&0xffffffffffffff
lea r8, [ r8 + rcx ]
and r14, r9; x594 <- x587&0xffffffffffffff
mov rcx, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rcx + 0x0 ], r15; out1[0] = x607
mov [ rcx + 0x38 ], r12; out1[7] = x597
mov [ rcx + 0x8 ], r8; out1[1] = x608
and rbp, r9; x604 <- x602&0xffffffffffffff
mov [ rcx + 0x30 ], r11; out1[6] = x591
and r13, r9; x599 <- x595&0xffffffffffffff
mov [ rcx + 0x28 ], rdi; out1[5] = x605
mov [ rcx + 0x10 ], r14; out1[2] = x594
mov [ rcx + 0x18 ], r13; out1[3] = x599
mov [ rcx + 0x20 ], rbp; out1[4] = x604
mov rbx, [ rsp + 0x378 ]; restoring from stack
mov rbp, [ rsp + 0x380 ]; restoring from stack
mov r12, [ rsp + 0x388 ]; restoring from stack
mov r13, [ rsp + 0x390 ]; restoring from stack
mov r14, [ rsp + 0x398 ]; restoring from stack
mov r15, [ rsp + 0x3a0 ]; restoring from stack
add rsp, 0x3a8 
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; clocked at 4799 MHz
; first cyclecount 296.345, best 216.125, lastGood 217.625
; seed 2132581807946336 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4770096 ms / 60000 runs=> 79.5016ms/run
; Time spent for assembling and measureing (initial batch_size=56, initial num_batches=101): 171205 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.03589131120212256
; number reverted permutation/ tried permutation: 19716 / 29961 =65.806%
; number reverted decision/ tried decision: 16694 / 30040 =55.573%