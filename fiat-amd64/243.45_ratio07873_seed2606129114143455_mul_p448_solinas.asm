SECTION .text
	GLOBAL mul_p448_solinas
mul_p448_solinas:
sub rsp, 0x3e0 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x3b0 ], rbx; saving to stack
mov [ rsp + 0x3b8 ], rbp; saving to stack
mov [ rsp + 0x3c0 ], r12; saving to stack
mov [ rsp + 0x3c8 ], r13; saving to stack
mov [ rsp + 0x3d0 ], r14; saving to stack
mov [ rsp + 0x3d8 ], r15; saving to stack
mov rax, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x20 ]; saving arg2[4] in rdx.
mulx r10, r11, [ rsi + 0x38 ]; x32, x31<- arg1[7] * arg2[4]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mulx rbx, rbp, [ rsi + 0x20 ]; x62, x61<- arg1[4] * arg2[7]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mulx r12, r13, [ rsi + 0x30 ]; x44, x43<- arg1[6] * arg2[5]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r14, r15, [ rax + 0x18 ]; x190, x189<- arg1[0] * arg2[3]
xor rcx, rcx
adox r11, r13
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx r8, r9, [ rsi + 0x8 ]; x176, x175<- arg1[1] * arg2[2]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx r13, rcx, [ rsi + 0x10 ]; x164, x163<- arg1[2] * arg2[1]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov [ rsp + 0x8 ], r14; spilling x190 to mem
mulx rdi, r14, [ rsi + 0x28 ]; x54, x53<- arg1[5] * arg2[6]
adcx r11, r14
adox r12, r10
adcx rdi, r12
xor r10, r10
adox r11, rbp
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rbp, r14, [ rax + 0x0 ]; x154, x153<- arg1[3] * arg2[0]
adcx r11, r14
adox rbx, rdi
adcx rbp, rbx
test al, al
adox r11, rcx
adox r13, rbp
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rcx, r12, [ rax + 0x10 ]; x162, x161<- arg1[2] * arg2[2]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx rdi, r14, [ rsi + 0x18 ]; x152, x151<- arg1[3] * arg2[1]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mulx rbx, rbp, [ rsi + 0x8 ]; x124, x123<- arg1[1] * arg2[7]
adcx r11, r9
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r9, r10, [ rax + 0x0 ]; x144, x143<- arg1[4] * arg2[0]
adcx r8, r13
add r11, r15; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r15, r13, [ rax + 0x18 ]; x174, x173<- arg1[1] * arg2[3]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x10 ], r15; spilling x174 to mem
mov [ rsp + 0x18 ], rcx; spilling x162 to mem
mulx r15, rcx, [ rsi + 0x0 ]; x188, x187<- arg1[0] * arg2[4]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x20 ], r15; spilling x188 to mem
mov [ rsp + 0x28 ], rdi; spilling x152 to mem
mulx r15, rdi, [ rsi + 0x18 ]; x118, x117<- arg1[3] * arg2[5]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x30 ], r9; spilling x144 to mem
mov [ rsp + 0x38 ], rbx; spilling x124 to mem
mulx r9, rbx, [ rsi + 0x28 ]; x52, x51<- arg1[5] * arg2[7]
adcx r8, [ rsp + 0x8 ]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x40 ], r15; spilling x118 to mem
mov [ rsp + 0x48 ], r9; spilling x52 to mem
mulx r15, r9, [ rax + 0x30 ]; x122, x121<- arg1[2] * arg2[6]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x50 ], r15; spilling x122 to mem
mov [ rsp + 0x58 ], rcx; spilling x187 to mem
mulx r15, rcx, [ rsi + 0x38 ]; x18, x17<- arg1[7] * arg2[5]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x60 ], r15; spilling x18 to mem
mov [ rsp + 0x68 ], r13; spilling x173 to mem
mulx r15, r13, [ rsi + 0x30 ]; x22, x21<- arg1[6] * arg2[6]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x70 ], r15; spilling x22 to mem
mov [ rsp + 0x78 ], r12; spilling x161 to mem
mulx r15, r12, [ rsi + 0x20 ]; x112, x111<- arg1[4] * arg2[4]
mov [ rsp + 0x80 ], r15; spilling x112 to mem
mov r15, r11; x225, copying x221 here, cause x221 is needed in a reg for other than x225, namely all: , x225, x226, size: 2
shrd r15, r8, 56; x225 <- x223||x221 >> 56
test al, al
adox rcx, r13
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx r8, r13, [ rax + 0x28 ]; x30, x29<- arg1[7] * arg2[5]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x88 ], r8; spilling x30 to mem
mov [ rsp + 0x90 ], r15; spilling x225 to mem
mulx r8, r15, [ rax + 0x8 ]; x88, x87<- arg1[7] * arg2[1]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x98 ], r8; spilling x88 to mem
mov [ rsp + 0xa0 ], r14; spilling x151 to mem
mulx r8, r14, [ rsi + 0x28 ]; x24, x23<- arg1[5] * arg2[7]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0xa8 ], r8; spilling x24 to mem
mov [ rsp + 0xb0 ], r10; spilling x143 to mem
mulx r8, r10, [ rsi + 0x28 ]; x104, x103<- arg1[5] * arg2[3]
adcx rcx, r14
setc r14b; spill CF x388 to reg (r14)
clc;
adcx rcx, r13
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0xb8 ], r8; spilling x104 to mem
mulx r13, r8, [ rsi + 0x30 ]; x42, x41<- arg1[6] * arg2[6]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0xc0 ], r13; spilling x42 to mem
mov byte [ rsp + 0xc8 ], r14b; spilling byte x388 to mem
mulx r13, r14, [ rax + 0x10 ]; x96, x95<- arg1[6] * arg2[2]
mov [ rsp + 0xd0 ], r13; spilling x96 to mem
setc r13b; spill CF x392 to reg (r13)
clc;
adcx rcx, r8
seto r8b; spill OF x384 to reg (r8)
mov byte [ rsp + 0xd8 ], r13b; spilling byte x392 to mem
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rcx, rbx
setc bl; spill CF x396 to reg (rbx)
clc;
adcx rcx, r15
setc r15b; spill CF x404 to reg (r15)
clc;
adcx rcx, r14
setc r14b; spill CF x408 to reg (r14)
clc;
adcx rcx, r10
seto r10b; spill OF x400 to reg (r10)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rcx, r12
setc r12b; spill CF x412 to reg (r12)
clc;
adcx rcx, rdi
seto dil; spill OF x416 to reg (rdi)
mov byte [ rsp + 0xe0 ], r12b; spilling byte x412 to mem
mov r12, -0x3 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rcx, r9
setc r9b; spill CF x420 to reg (r9)
clc;
adcx rcx, rbp
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx rbp, r13, [ rsi + 0x38 ]; x82, x81<- arg1[7] * arg2[4]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov byte [ rsp + 0xe8 ], r9b; spilling byte x420 to mem
mulx r12, r9, [ rax + 0x30 ]; x168, x167<- arg1[1] * arg2[6]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov byte [ rsp + 0xf0 ], dil; spilling byte x416 to mem
mov byte [ rsp + 0xf8 ], r14b; spilling byte x408 to mem
mulx rdi, r14, [ rsi + 0x20 ]; x138, x137<- arg1[4] * arg2[3]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov byte [ rsp + 0x100 ], r15b; spilling byte x404 to mem
mov byte [ rsp + 0x108 ], r10b; spilling byte x400 to mem
mulx r15, r10, [ rax + 0x10 ]; x132, x131<- arg1[5] * arg2[2]
mov byte [ rsp + 0x110 ], bl; spilling byte x396 to mem
setc bl; spill CF x428 to reg (rbx)
clc;
adcx rcx, [ rsp + 0xb0 ]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov byte [ rsp + 0x118 ], bl; spilling byte x428 to mem
mov [ rsp + 0x120 ], r12; spilling x168 to mem
mulx rbx, r12, [ rsi + 0x0 ]; x182, x181<- arg1[0] * arg2[7]
mov [ rsp + 0x128 ], rbx; spilling x182 to mem
seto bl; spill OF x424 to reg (rbx)
mov [ rsp + 0x130 ], r12; spilling x181 to mem
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rcx, [ rsp + 0xa0 ]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov byte [ rsp + 0x138 ], bl; spilling byte x424 to mem
mulx r12, rbx, [ rsi + 0x18 ]; x146, x145<- arg1[3] * arg2[4]
mov [ rsp + 0x140 ], r9; spilling x167 to mem
seto r9b; spill OF x436 to reg (r9)
mov [ rsp + 0x148 ], r12; spilling x146 to mem
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rcx, [ rsp + 0x78 ]
setc r12b; spill CF x432 to reg (r12)
clc;
adcx rcx, [ rsp + 0x68 ]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov byte [ rsp + 0x150 ], r9b; spilling byte x436 to mem
mov byte [ rsp + 0x158 ], r12b; spilling byte x432 to mem
mulx r9, r12, [ rsi + 0x30 ]; x128, x127<- arg1[6] * arg2[1]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x160 ], rdi; spilling x138 to mem
mov [ rsp + 0x168 ], r15; spilling x132 to mem
mulx rdi, r15, [ rax + 0x30 ]; x98, x97<- arg1[5] * arg2[6]
mov [ rsp + 0x170 ], r9; spilling x128 to mem
setc r9b; spill CF x444 to reg (r9)
clc;
adcx rcx, [ rsp + 0x58 ]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov byte [ rsp + 0x178 ], r9b; spilling byte x444 to mem
mov byte [ rsp + 0x180 ], r8b; spilling byte x384 to mem
mulx r9, r8, [ rax + 0x28 ]; x90, x89<- arg1[6] * arg2[5]
mov [ rsp + 0x188 ], rbx; spilling x145 to mem
seto bl; spill OF x440 to reg (rbx)
mov [ rsp + 0x190 ], r14; spilling x137 to mem
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, r8
setc r8b; spill CF x448 to reg (r8)
clc;
adcx r13, r15
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mulx r15, r14, [ rsi + 0x20 ]; x106, x105<- arg1[4] * arg2[7]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov byte [ rsp + 0x198 ], r8b; spilling byte x448 to mem
mov byte [ rsp + 0x1a0 ], bl; spilling byte x440 to mem
mulx r8, rbx, [ rsi + 0x10 ]; x156, x155<- arg1[2] * arg2[5]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x1a8 ], r8; spilling x156 to mem
mov [ rsp + 0x1b0 ], rbx; spilling x155 to mem
mulx r8, rbx, [ rax + 0x0 ]; x126, x125<- arg1[7] * arg2[0]
adox r9, rbp
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rcx, [ rsp + 0x90 ]
setc bpl; spill CF x232 to reg (rbp)
clc;
adcx r13, r14
setc r14b; spill CF x236 to reg (r14)
clc;
adcx r13, rbx
setc bl; spill CF x240 to reg (rbx)
clc;
adcx r13, r12
movzx rbp, bpl
lea rdi, [ rdi + r9 ]
lea rdi, [ rdi + rbp ]
setc r12b; spill CF x244 to reg (r12)
clc;
adcx r13, r10
movzx r14, r14b
lea r15, [ r15 + rdi ]
lea r15, [ r15 + r14 ]
seto r10b; spill OF x560 to reg (r10)
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, [ rsp + 0x190 ]
movzx rbx, bl
lea r8, [ r8 + r15 ]
lea r8, [ r8 + rbx ]
seto r9b; spill OF x252 to reg (r9)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r13, [ rsp + 0x188 ]
mov r14, [ rsp + 0x60 ]; load m64 x18 to register64
movzx rbx, byte [ rsp + 0x180 ]; load byte memx384 to register64
lea r14, [ rbx + r14 ]
mov rbx, [ rsp + 0x70 ]
lea r14, [rbx+r14]
movzx r12, r12b
lea r8, [ r12 + r8 ]
mov r12, [ rsp + 0x170 ]
lea r8, [r12+r8]
adcx r8, [ rsp + 0x168 ]
movzx r9, r9b
lea r8, [ r9 + r8 ]
mov r9, [ rsp + 0x160 ]
lea r8, [r9+r8]
adox r8, [ rsp + 0x148 ]
add r13, [ rsp + 0x1b0 ]; could be done better, if r0 has been u8 as well
adcx r8, [ rsp + 0x1a8 ]
xor rbx, rbx
adox r13, [ rsp + 0x140 ]
adcx r13, [ rsp + 0x130 ]
adox r8, [ rsp + 0x120 ]
adcx r8, [ rsp + 0x128 ]
mov rbp, r13; x562, copying x267 here, cause x267 is needed in a reg for other than x562, namely all: , x563, x562, size: 2
shrd rbp, r8, 56; x562 <- x269||x267 >> 56
sar byte [ rsp + 0xc8 ], 1
adcx r14, [ rsp + 0xa8 ]
sar byte [ rsp + 0xd8 ], 1
adcx r14, [ rsp + 0x88 ]
sar byte [ rsp + 0x110 ], 1
adcx r14, [ rsp + 0xc0 ]
sar byte [ rsp + 0x108 ], 1
adcx r14, [ rsp + 0x48 ]
sar byte [ rsp + 0x100 ], 1
adcx r14, [ rsp + 0x98 ]
sar byte [ rsp + 0xf8 ], 1
adcx r14, [ rsp + 0xd0 ]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx r12, rdi, [ rsi + 0x20 ]; x142, x141<- arg1[4] * arg2[1]
sar byte [ rsp + 0xe0 ], 1
adcx r14, [ rsp + 0xb8 ]
sar byte [ rsp + 0xf0 ], 1
adcx r14, [ rsp + 0x80 ]
sar byte [ rsp + 0xe8 ], 1
adcx r14, [ rsp + 0x40 ]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx r15, r9, [ rsi + 0x18 ]; x150, x149<- arg1[3] * arg2[2]
sar byte [ rsp + 0x138 ], 1
adcx r14, [ rsp + 0x50 ]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mulx r8, rbx, [ rsi + 0x10 ]; x120, x119<- arg1[2] * arg2[7]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x1b8 ], r15; spilling x150 to mem
mov [ rsp + 0x1c0 ], r12; spilling x142 to mem
mulx r15, r12, [ rsi + 0x8 ]; x172, x171<- arg1[1] * arg2[4]
sar byte [ rsp + 0x118 ], 1
adcx r14, [ rsp + 0x38 ]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x1c8 ], r15; spilling x172 to mem
mov [ rsp + 0x1d0 ], r8; spilling x120 to mem
mulx r15, r8, [ rax + 0x10 ]; x86, x85<- arg1[7] * arg2[2]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x1d8 ], r12; spilling x171 to mem
mov [ rsp + 0x1e0 ], r9; spilling x149 to mem
mulx r12, r9, [ rsi + 0x10 ]; x160, x159<- arg1[2] * arg2[3]
sar byte [ rsp + 0x158 ], 1
adcx r14, [ rsp + 0x30 ]
sar byte [ rsp + 0x150 ], 1
adcx r14, [ rsp + 0x28 ]
sar byte [ rsp + 0x1a0 ], 1
adcx r14, [ rsp + 0x18 ]
mov [ rsp + 0x1e8 ], r12; spilling x160 to mem
mov r12, rbp; x564, copying x562 here, cause x562 is needed in a reg for other than x564, namely all: , x569--x570, x564--x565, size: 2
adox r12, rcx
movzx rcx, byte [ rsp + 0x178 ]; load byte memx444 to register64
lea r14, [ rcx + r14 ]
mov rcx, [ rsp + 0x10 ]
lea r14, [rcx+r14]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x1f0 ], r9; spilling x159 to mem
mulx rcx, r9, [ rax + 0x0 ]; x136, x135<- arg1[5] * arg2[0]
mov [ rsp + 0x1f8 ], rcx; spilling x136 to mem
movzx rcx, byte [ rsp + 0x198 ]; load byte memx448 to register64
lea r14, [ rcx + r14 ]
mov rcx, [ rsp + 0x20 ]
lea r14, [rcx+r14]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x200 ], r15; spilling x86 to mem
mulx rcx, r15, [ rsi + 0x30 ]; x94, x93<- arg1[6] * arg2[3]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x208 ], rcx; spilling x94 to mem
mov [ rsp + 0x210 ], rdi; spilling x141 to mem
mulx rcx, rdi, [ rsi + 0x28 ]; x102, x101<- arg1[5] * arg2[4]
mov [ rsp + 0x218 ], rcx; spilling x102 to mem
movzx rcx, r10b; x561, copying x560 here, cause x560 is needed in a reg for other than x561, namely all: , x561, size: 1
lea rcx, [ rcx + r14 ]
mov r10, 0x0 ; moving imm to reg
adox rcx, r10
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mulx r14, r10, [ rsi + 0x0 ]; x186, x185<- arg1[0] * arg2[5]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x220 ], r11; spilling x221 to mem
mov [ rsp + 0x228 ], r14; spilling x186 to mem
mulx r11, r14, [ rsi + 0x38 ]; x16, x15<- arg1[7] * arg2[6]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x230 ], r10; spilling x185 to mem
mov [ rsp + 0x238 ], r9; spilling x135 to mem
mulx r10, r9, [ rsi + 0x20 ]; x110, x109<- arg1[4] * arg2[5]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x240 ], r10; spilling x110 to mem
mov [ rsp + 0x248 ], rbx; spilling x119 to mem
mulx r10, rbx, [ rsi + 0x30 ]; x20, x19<- arg1[6] * arg2[7]
mov [ rsp + 0x250 ], r11; spilling x16 to mem
mov r11, r12; x567, copying x564 here, cause x564 is needed in a reg for other than x567, namely all: , x568, x567, size: 2
shrd r11, rcx, 56; x567 <- x566||x564 >> 56
test al, al
adox r14, rbx
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mulx rcx, rbx, [ rax + 0x38 ]; x40, x39<- arg1[6] * arg2[7]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x258 ], r11; spilling x567 to mem
mov [ rsp + 0x260 ], rcx; spilling x40 to mem
mulx r11, rcx, [ rsi + 0x38 ]; x28, x27<- arg1[7] * arg2[6]
adcx r14, rcx
setc cl; spill CF x328 to reg (rcx)
clc;
adcx r14, rbx
setc bl; spill CF x332 to reg (rbx)
clc;
adcx r14, r8
setc r8b; spill CF x336 to reg (r8)
clc;
adcx r14, r15
setc r15b; spill CF x340 to reg (r15)
clc;
adcx r14, rdi
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov byte [ rsp + 0x268 ], r15b; spilling byte x340 to mem
mulx rdi, r15, [ rsi + 0x18 ]; x116, x115<- arg1[3] * arg2[6]
mov [ rsp + 0x270 ], rdi; spilling x116 to mem
setc dil; spill CF x344 to reg (rdi)
clc;
adcx r14, r9
setc r9b; spill CF x348 to reg (r9)
clc;
adcx r14, r15
adox r10, [ rsp + 0x250 ]
mov r15, -0x2 ; moving imm to reg
inc r15; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, [ rsp + 0x248 ]
movzx rcx, cl
lea r11, [ r11 + r10 ]
lea r11, [ r11 + rcx ]
movzx rbx, bl
lea r11, [ rbx + r11 ]
mov rbx, [ rsp + 0x260 ]
lea r11, [rbx+r11]
setc cl; spill CF x352 to reg (rcx)
clc;
adcx r14, [ rsp + 0x238 ]
setc bl; spill CF x360 to reg (rbx)
clc;
adcx r14, [ rsp + 0x210 ]
movzx r8, r8b
lea r11, [ r8 + r11 ]
mov r8, [ rsp + 0x200 ]
lea r11, [r8+r11]
movzx r8, byte [ rsp + 0x268 ]; load byte memx340 to register64
lea r11, [ r8 + r11 ]
mov r8, [ rsp + 0x208 ]
lea r11, [r8+r11]
setc r8b; spill CF x364 to reg (r8)
clc;
adcx r14, [ rsp + 0x1e0 ]
movzx rdi, dil
lea r11, [ rdi + r11 ]
mov rdi, [ rsp + 0x218 ]
lea r11, [rdi+r11]
movzx r9, r9b
lea r11, [ r9 + r11 ]
mov r9, [ rsp + 0x240 ]
lea r11, [r9+r11]
setc dil; spill CF x368 to reg (rdi)
clc;
adcx r14, [ rsp + 0x1f0 ]
movzx rcx, cl
lea r11, [ rcx + r11 ]
mov rcx, [ rsp + 0x270 ]
lea r11, [rcx+r11]
setc r9b; spill CF x372 to reg (r9)
clc;
adcx r14, [ rsp + 0x1d8 ]
adox r11, [ rsp + 0x1d0 ]
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r14, [ rsp + 0x230 ]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rcx, r10, [ rax + 0x30 ]; x184, x183<- arg1[0] * arg2[6]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x278 ], rcx; spilling x184 to mem
mulx r15, rcx, [ rsi + 0x20 ]; x140, x139<- arg1[4] * arg2[2]
movzx rbx, bl
lea r11, [ rbx + r11 ]
mov rbx, [ rsp + 0x1f8 ]
lea r11, [rbx+r11]
movzx r8, r8b
lea r11, [ r8 + r11 ]
mov r8, [ rsp + 0x1c0 ]
lea r11, [r8+r11]
movzx rdi, dil
lea r11, [ rdi + r11 ]
mov rdi, [ rsp + 0x1b8 ]
lea r11, [rdi+r11]
movzx r9, r9b
lea r11, [ r9 + r11 ]
mov r9, [ rsp + 0x1e8 ]
lea r11, [r9+r11]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx rbx, r8, [ rax + 0x18 ]; x84, x83<- arg1[7] * arg2[3]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rdi, r9, [ rax + 0x28 ]; x170, x169<- arg1[1] * arg2[5]
adcx r11, [ rsp + 0x1c8 ]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x280 ], r10; spilling x183 to mem
mov [ rsp + 0x288 ], rdi; spilling x170 to mem
mulx r10, rdi, [ rax + 0x38 ]; x114, x113<- arg1[3] * arg2[7]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x290 ], r9; spilling x169 to mem
mov [ rsp + 0x298 ], r15; spilling x140 to mem
mulx r9, r15, [ rsi + 0x20 ]; x108, x107<- arg1[4] * arg2[6]
adox r11, [ rsp + 0x228 ]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x2a0 ], rcx; spilling x139 to mem
mov [ rsp + 0x2a8 ], r10; spilling x114 to mem
mulx rcx, r10, [ rax + 0x8 ]; x134, x133<- arg1[5] * arg2[1]
add r14, [ rsp + 0x258 ]; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x2b0 ], rcx; spilling x134 to mem
mov [ rsp + 0x2b8 ], r10; spilling x133 to mem
mulx rcx, r10, [ rax + 0x0 ]; x130, x129<- arg1[6] * arg2[0]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x2c0 ], rcx; spilling x130 to mem
mov [ rsp + 0x2c8 ], r10; spilling x129 to mem
mulx rcx, r10, [ rax + 0x38 ]; x26, x25<- arg1[7] * arg2[7]
adc r11, 0x0
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x2d0 ], r9; spilling x108 to mem
mov [ rsp + 0x2d8 ], rdi; spilling x113 to mem
mulx r9, rdi, [ rax + 0x20 ]; x92, x91<- arg1[6] * arg2[4]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x2e0 ], r15; spilling x107 to mem
mov [ rsp + 0x2e8 ], r9; spilling x92 to mem
mulx r15, r9, [ rsi + 0x38 ]; x14, x13<- arg1[7] * arg2[7]
mov [ rsp + 0x2f0 ], rdi; spilling x91 to mem
mov rdi, r14; x580, copying x572 here, cause x572 is needed in a reg for other than x580, namely all: , x580, x581, size: 2
shrd rdi, r11, 56; x580 <- x574||x572 >> 56
test al, al
adox r9, r10
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r10, r11, [ rax + 0x18 ]; x148, x147<- arg1[3] * arg2[3]
adox rcx, r15
adcx r9, r8
adcx rbx, rcx
add r9, [ rsp + 0x2f0 ]; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mulx r8, r15, [ rax + 0x28 ]; x100, x99<- arg1[5] * arg2[5]
adcx rbx, [ rsp + 0x2e8 ]
test al, al
adox r9, r15
adox r8, rbx
adcx r9, [ rsp + 0x2e0 ]
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r9, [ rsp + 0x2d8 ]
adcx r8, [ rsp + 0x2d0 ]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r15, rbx, [ rax + 0x20 ]; x158, x157<- arg1[2] * arg2[4]
clc;
adcx r9, [ rsp + 0x2c8 ]
adox r8, [ rsp + 0x2a8 ]
adcx r8, [ rsp + 0x2c0 ]
xor rcx, rcx
adox r9, [ rsp + 0x2b8 ]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x2f8 ], rdi; spilling x580 to mem
mulx rcx, rdi, [ rsi + 0x10 ]; x78, x77<- arg1[2] * arg2[6]
adox r8, [ rsp + 0x2b0 ]
adcx r9, [ rsp + 0x2a0 ]
adcx r8, [ rsp + 0x298 ]
test al, al
adox r9, r11
adcx r9, rbx
seto r11b; spill OF x308 to reg (r11)
mov rbx, -0x2 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r9, [ rsp + 0x290 ]
movzx r11, r11b
lea r10, [ r10 + r8 ]
lea r10, [ r10 + r11 ]
adcx r15, r10
adox r15, [ rsp + 0x288 ]
add r9, [ rsp + 0x280 ]; could be done better, if r0 has been u8 as well
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r9, [ rsp + 0x2f8 ]
adcx r15, [ rsp + 0x278 ]
adox r15, rbx
mov r8, 0xffffffffffffff ; moving imm to reg
and r13, r8; x563 <- x267&0xffffffffffffff
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r11, r10, [ rax + 0x0 ]; x196, x195<- arg1[0] * arg2[0]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx rbx, r8, [ rax + 0x20 ]; x68, x67<- arg1[4] * arg2[4]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x300 ], r11; spilling x196 to mem
mov [ rsp + 0x308 ], r10; spilling x195 to mem
mulx r11, r10, [ rax + 0x28 ]; x6, x5<- arg1[7] * arg2[5]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x310 ], rcx; spilling x78 to mem
mov [ rsp + 0x318 ], rdi; spilling x77 to mem
mulx rcx, rdi, [ rsi + 0x30 ]; x10, x9<- arg1[6] * arg2[6]
mov [ rsp + 0x320 ], rbx; spilling x68 to mem
mov rbx, r9; x590, copying x582 here, cause x582 is needed in a reg for other than x590, namely all: , x590, x591, size: 2
shrd rbx, r15, 56; x590 <- x584||x582 >> 56
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x328 ], r8; spilling x67 to mem
mulx r15, r8, [ rsi + 0x30 ]; x50, x49<- arg1[6] * arg2[2]
lea rbx, [ rbx + r13 ]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x330 ], r15; spilling x50 to mem
mulx r13, r15, [ rax + 0x38 ]; x12, x11<- arg1[5] * arg2[7]
add r10, rdi; could be done better, if r0 has been u8 as well
adcx rcx, r11
mov r11, 0xffffffffffffff ; moving imm to reg
mov rdi, rbx; x597, copying x592 here, cause x592 is needed in a reg for other than x597, namely all: , x597, x596, size: 2
and rdi, r11; x597 <- x592&0xffffffffffffff
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x338 ], rdi; spilling x597 to mem
mulx r11, rdi, [ rsi + 0x38 ]; x38, x37<- arg1[7] * arg2[1]
adox r10, r15
adox r13, rcx
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r15, rcx, [ rax + 0x38 ]; x80, x79<- arg1[1] * arg2[7]
adcx r10, rdi
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x340 ], r15; spilling x80 to mem
mulx rdi, r15, [ rax + 0x28 ]; x74, x73<- arg1[3] * arg2[5]
adcx r11, r13
test al, al
adox r10, r8
adox r11, [ rsp + 0x330 ]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mulx r8, r13, [ rax + 0x18 ]; x60, x59<- arg1[5] * arg2[3]
adcx r10, r13
adcx r8, r11
add r10, [ rsp + 0x328 ]; could be done better, if r0 has been u8 as well
adcx r8, [ rsp + 0x320 ]
add r10, r15; could be done better, if r0 has been u8 as well
adcx rdi, r8
test al, al
adox r10, [ rsp + 0x318 ]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r15, r11, [ rax + 0x30 ]; x72, x71<- arg1[3] * arg2[6]
adox rdi, [ rsp + 0x310 ]
adcx r10, rcx
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx rcx, r13, [ rax + 0x10 ]; x36, x35<- arg1[7] * arg2[2]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x348 ], r15; spilling x72 to mem
mulx r8, r15, [ rsi + 0x0 ]; x194, x193<- arg1[0] * arg2[1]
adcx rdi, [ rsp + 0x340 ]
add r10, [ rsp + 0x308 ]; could be done better, if r0 has been u8 as well
adcx rdi, [ rsp + 0x300 ]
add rbp, r10; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x350 ], r8; spilling x194 to mem
mulx r10, r8, [ rax + 0x38 ]; x8, x7<- arg1[6] * arg2[7]
adc rdi, 0x0
mov [ rsp + 0x358 ], r15; spilling x193 to mem
mov r15, rbp; x575, copying x569 here, cause x569 is needed in a reg for other than x575, namely all: , x576, x575, size: 2
shrd r15, rdi, 56; x575 <- x571||x569 >> 56
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x360 ], r15; spilling x575 to mem
mulx rdi, r15, [ rsi + 0x38 ]; x4, x3<- arg1[7] * arg2[6]
test al, al
adox r15, r8
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x368 ], r11; spilling x71 to mem
mulx r8, r11, [ rsi + 0x10 ]; x76, x75<- arg1[2] * arg2[7]
adox r10, rdi
adcx r15, r13
adcx rcx, r10
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mulx r13, rdi, [ rsi + 0x30 ]; x48, x47<- arg1[6] * arg2[3]
test al, al
adox r15, rdi
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx r10, rdi, [ rsi + 0x28 ]; x58, x57<- arg1[5] * arg2[4]
adcx r15, rdi
adox r13, rcx
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx rcx, rdi, [ rax + 0x28 ]; x66, x65<- arg1[4] * arg2[5]
adcx r10, r13
add r15, rdi; could be done better, if r0 has been u8 as well
adcx rcx, r10
add r15, [ rsp + 0x368 ]; could be done better, if r0 has been u8 as well
adcx rcx, [ rsp + 0x348 ]
add r15, r11; could be done better, if r0 has been u8 as well
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx r11, r13, [ rsi + 0x10 ]; x166, x165<- arg1[2] * arg2[0]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rdi, r10, [ rax + 0x0 ]; x180, x179<- arg1[1] * arg2[0]
adcx r8, rcx
add r15, r10; could be done better, if r0 has been u8 as well
adcx rdi, r8
test al, al
adox r15, [ rsp + 0x358 ]
adcx r15, [ rsp + 0x360 ]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx rcx, r10, [ rsi + 0x0 ]; x192, x191<- arg1[0] * arg2[2]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x370 ], rcx; spilling x192 to mem
mulx r8, rcx, [ rsi + 0x20 ]; x64, x63<- arg1[4] * arg2[6]
adox rdi, [ rsp + 0x350 ]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x378 ], r10; spilling x191 to mem
mov [ rsp + 0x380 ], r11; spilling x166 to mem
mulx r10, r11, [ rax + 0x18 ]; x34, x33<- arg1[7] * arg2[3]
adc rdi, 0x0
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x388 ], r13; spilling x165 to mem
mov [ rsp + 0x390 ], r8; spilling x64 to mem
mulx r13, r8, [ rsi + 0x30 ]; x46, x45<- arg1[6] * arg2[4]
mov [ rsp + 0x398 ], rcx; spilling x63 to mem
mov rcx, r15; x585, copying x577 here, cause x577 is needed in a reg for other than x585, namely all: , x585, x586, size: 2
shrd rcx, rdi, 56; x585 <- x579||x577 >> 56
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x3a0 ], rcx; spilling x585 to mem
mulx rdi, rcx, [ rsi + 0x38 ]; x2, x1<- arg1[7] * arg2[7]
add rcx, r11; could be done better, if r0 has been u8 as well
adcx r10, rdi
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mulx r11, rdi, [ rsi + 0x18 ]; x70, x69<- arg1[3] * arg2[7]
add rcx, r8; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x3a8 ], r11; spilling x70 to mem
mulx r8, r11, [ rax + 0x28 ]; x56, x55<- arg1[5] * arg2[5]
adcx r13, r10
add rcx, r11; could be done better, if r0 has been u8 as well
adcx r8, r13
add rcx, [ rsp + 0x398 ]; could be done better, if r0 has been u8 as well
adcx r8, [ rsp + 0x390 ]
xor r10, r10
adox rcx, rdi
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rdi, r11, [ rax + 0x8 ]; x178, x177<- arg1[1] * arg2[1]
adcx rcx, [ rsp + 0x388 ]
adox r8, [ rsp + 0x3a8 ]
mov r13, [ rsp + 0x0 ]; load m64 out1 to register64
mov r10, [ rsp + 0x338 ]; TMP = x597
mov [ r13 + 0x38 ], r10; out1[7] = TMP
adcx r8, [ rsp + 0x380 ]
add rcx, r11; could be done better, if r0 has been u8 as well
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rcx, [ rsp + 0x378 ]
adcx rdi, r8
adox rdi, [ rsp + 0x370 ]
xor r11, r11
adox rcx, [ rsp + 0x3a0 ]
adox rdi, r11
mov r8, 0xffffffffffffff ; moving imm to reg
mov r11, rcx; x594, copying x587 here, cause x587 is needed in a reg for other than x594, namely all: , x593, x594, size: 2
and r11, r8; x594 <- x587&0xffffffffffffff
and rbp, r8; x576 <- x569&0xffffffffffffff
shr rbx, 56; x596 <- x592>> 56
mov r10, [ rsp + 0x220 ]; x226, copying x221 here, cause x221 is needed in a reg for other than x226, namely all: , x226, size: 1
and r10, r8; x226 <- x221&0xffffffffffffff
shrd rcx, rdi, 56; x593 <- x589||x587 >> 56
and r14, r8; x581 <- x572&0xffffffffffffff
and r12, r8; x568 <- x564&0xffffffffffffff
lea rcx, [ rcx + r10 ]
mov rdi, rcx; x598, copying x595 here, cause x595 is needed in a reg for other than x598, namely all: , x598, x599, size: 2
shr rdi, 56; x598 <- x595>> 56
lea r12, [ r12 + rbx ]
lea rbp, [ rbp + rbx ]
mov rbx, rbp; x606, copying x601 here, cause x601 is needed in a reg for other than x606, namely all: , x607, x606, size: 2
shr rbx, 56; x606 <- x601>> 56
lea rdi, [ rdi + r12 ]
mov r10, rdi; x603, copying x602 here, cause x602 is needed in a reg for other than x603, namely all: , x604, x603, size: 2
shr r10, 56; x603 <- x602>> 56
and rdi, r8; x604 <- x602&0xffffffffffffff
mov [ r13 + 0x20 ], rdi; out1[4] = x604
and r15, r8; x586 <- x577&0xffffffffffffff
lea rbx, [ rbx + r15 ]
and r9, r8; x591 <- x582&0xffffffffffffff
and rbp, r8; x607 <- x601&0xffffffffffffff
and rcx, r8; x599 <- x595&0xffffffffffffff
lea r10, [ r10 + r14 ]
mov [ r13 + 0x18 ], rcx; out1[3] = x599
mov [ r13 + 0x30 ], r9; out1[6] = x591
mov [ r13 + 0x10 ], r11; out1[2] = x594
mov [ r13 + 0x28 ], r10; out1[5] = x605
mov [ r13 + 0x8 ], rbx; out1[1] = x608
mov [ r13 + 0x0 ], rbp; out1[0] = x607
mov rbx, [ rsp + 0x3b0 ]; restoring from stack
mov rbp, [ rsp + 0x3b8 ]; restoring from stack
mov r12, [ rsp + 0x3c0 ]; restoring from stack
mov r13, [ rsp + 0x3c8 ]; restoring from stack
mov r14, [ rsp + 0x3d0 ]; restoring from stack
mov r15, [ rsp + 0x3d8 ]; restoring from stack
add rsp, 0x3e0 
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; clocked at 2600 MHz
; first cyclecount 327.13, best 243.27450980392157, lastGood 243.45098039215685
; seed 2606129114143455 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 7024845 ms / 60000 runs=> 117.08075ms/run
; Time spent for assembling and measureing (initial batch_size=51, initial num_batches=101): 282542 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.04022038920431696
; number reverted permutation/ tried permutation: 20402 / 30001 =68.004%
; number reverted decision/ tried decision: 16953 / 30000 =56.510%