SECTION .text
	GLOBAL mul_p448_solinas
mul_p448_solinas:
sub rsp, 0x438 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x408 ], rbx; saving to stack
mov [ rsp + 0x410 ], rbp; saving to stack
mov [ rsp + 0x418 ], r12; saving to stack
mov [ rsp + 0x420 ], r13; saving to stack
mov [ rsp + 0x428 ], r14; saving to stack
mov [ rsp + 0x430 ], r15; saving to stack
mov rax, rdx; preserving value of arg2 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx r10, r11, [ rax + 0x0 ]; x154, x153<- arg1[3] * arg2[0]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx rbx, rbp, [ rsi + 0x38 ]; x32, x31<- arg1[7] * arg2[4]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r12, r13, [ rax + 0x38 ]; x62, x61<- arg1[4] * arg2[7]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r14, r15, [ rax + 0x10 ]; x176, x175<- arg1[1] * arg2[2]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mulx rcx, r8, [ rax + 0x28 ]; x44, x43<- arg1[6] * arg2[5]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r9, rdi, [ rax + 0x30 ]; x54, x53<- arg1[5] * arg2[6]
test al, al
adox rbp, r8
adcx rbp, rdi
adox rcx, rbx
mov rbx, -0x2 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, r13
adcx r9, rcx
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r13, r8, [ rax + 0x8 ]; x164, x163<- arg1[2] * arg2[1]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mulx rdi, rcx, [ rsi + 0x0 ]; x190, x189<- arg1[0] * arg2[3]
adox r12, r9
xor r9, r9
adox rbp, r11
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx r11, r9, [ rsi + 0x0 ]; x188, x187<- arg1[0] * arg2[4]
adcx rbp, r8
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mulx r8, rbx, [ rsi + 0x8 ]; x174, x173<- arg1[1] * arg2[3]
mov [ rsp + 0x8 ], r11; spilling x188 to mem
setc r11b; spill CF x214 to reg (r11)
clc;
adcx rbp, r15
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x10 ], r8; spilling x174 to mem
mulx r15, r8, [ rsi + 0x18 ]; x118, x117<- arg1[3] * arg2[5]
adox r10, r12
movzx r11, r11b
lea r13, [ r13 + r10 ]
lea r13, [ r13 + r11 ]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mulx r12, r11, [ rax + 0x18 ]; x104, x103<- arg1[5] * arg2[3]
adcx r14, r13
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r10, r13, [ rax + 0x0 ]; x144, x143<- arg1[4] * arg2[0]
mov [ rsp + 0x18 ], r10; spilling x144 to mem
xor r10, r10
adox rbp, rcx
adox rdi, r14
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mulx rcx, r14, [ rax + 0x10 ]; x96, x95<- arg1[6] * arg2[2]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x20 ], r15; spilling x118 to mem
mulx r10, r15, [ rax + 0x20 ]; x112, x111<- arg1[4] * arg2[4]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x28 ], r10; spilling x112 to mem
mov [ rsp + 0x30 ], r12; spilling x104 to mem
mulx r10, r12, [ rax + 0x10 ]; x162, x161<- arg1[2] * arg2[2]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x38 ], r10; spilling x162 to mem
mov [ rsp + 0x40 ], rcx; spilling x96 to mem
mulx r10, rcx, [ rsi + 0x28 ]; x24, x23<- arg1[5] * arg2[7]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x48 ], r10; spilling x24 to mem
mov [ rsp + 0x50 ], r9; spilling x187 to mem
mulx r10, r9, [ rax + 0x30 ]; x42, x41<- arg1[6] * arg2[6]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x58 ], r10; spilling x42 to mem
mov [ rsp + 0x60 ], rbx; spilling x173 to mem
mulx r10, rbx, [ rsi + 0x8 ]; x124, x123<- arg1[1] * arg2[7]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x68 ], r10; spilling x124 to mem
mov [ rsp + 0x70 ], r12; spilling x161 to mem
mulx r10, r12, [ rsi + 0x38 ]; x18, x17<- arg1[7] * arg2[5]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x78 ], r10; spilling x18 to mem
mov [ rsp + 0x80 ], r13; spilling x143 to mem
mulx r10, r13, [ rsi + 0x38 ]; x30, x29<- arg1[7] * arg2[5]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x88 ], r10; spilling x30 to mem
mov [ rsp + 0x90 ], rbx; spilling x123 to mem
mulx r10, rbx, [ rsi + 0x18 ]; x146, x145<- arg1[3] * arg2[4]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x98 ], r10; spilling x146 to mem
mov [ rsp + 0xa0 ], rbx; spilling x145 to mem
mulx r10, rbx, [ rax + 0x30 ]; x22, x21<- arg1[6] * arg2[6]
mov [ rsp + 0xa8 ], r10; spilling x22 to mem
mov r10, rbp; x225, copying x221 here, cause x221 is needed in a reg for other than x225, namely all: , x225, x226, size: 2
shrd r10, rdi, 56; x225 <- x223||x221 >> 56
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0xb0 ], r10; spilling x225 to mem
mulx rdi, r10, [ rsi + 0x38 ]; x88, x87<- arg1[7] * arg2[1]
mov [ rsp + 0xb8 ], rdi; spilling x88 to mem
xor rdi, rdi
adox r12, rbx
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mulx rbx, rdi, [ rsi + 0x0 ]; x182, x181<- arg1[0] * arg2[7]
adcx r12, rcx
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0xc0 ], rbx; spilling x182 to mem
mulx rcx, rbx, [ rax + 0x8 ]; x152, x151<- arg1[3] * arg2[1]
mov [ rsp + 0xc8 ], rcx; spilling x152 to mem
setc cl; spill CF x388 to reg (rcx)
clc;
adcx r12, r13
seto r13b; spill OF x384 to reg (r13)
mov [ rsp + 0xd0 ], rdi; spilling x181 to mem
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, r9
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mulx r9, rdi, [ rsi + 0x10 ]; x122, x121<- arg1[2] * arg2[6]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0xd8 ], r9; spilling x122 to mem
mov byte [ rsp + 0xe0 ], cl; spilling byte x388 to mem
mulx r9, rcx, [ rsi + 0x28 ]; x52, x51<- arg1[5] * arg2[7]
mov [ rsp + 0xe8 ], r9; spilling x52 to mem
seto r9b; spill OF x396 to reg (r9)
mov byte [ rsp + 0xf0 ], r13b; spilling byte x384 to mem
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, rcx
setc cl; spill CF x392 to reg (rcx)
clc;
adcx r12, r10
setc r10b; spill CF x404 to reg (r10)
clc;
adcx r12, r14
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mulx r14, r13, [ rsi + 0x10 ]; x156, x155<- arg1[2] * arg2[5]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0xf8 ], r14; spilling x156 to mem
mov [ rsp + 0x100 ], r13; spilling x155 to mem
mulx r14, r13, [ rax + 0x18 ]; x138, x137<- arg1[4] * arg2[3]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov byte [ rsp + 0x108 ], r10b; spilling byte x404 to mem
mov [ rsp + 0x110 ], r14; spilling x138 to mem
mulx r10, r14, [ rsi + 0x8 ]; x168, x167<- arg1[1] * arg2[6]
mov [ rsp + 0x118 ], r10; spilling x168 to mem
setc r10b; spill CF x408 to reg (r10)
clc;
adcx r12, r11
seto r11b; spill OF x400 to reg (r11)
mov [ rsp + 0x120 ], r14; spilling x167 to mem
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, r15
seto r15b; spill OF x416 to reg (r15)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r12, r8
seto r8b; spill OF x420 to reg (r8)
mov byte [ rsp + 0x128 ], r15b; spilling byte x416 to mem
mov r15, -0x3 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r12, rdi
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx rdi, r14, [ rax + 0x0 ]; x126, x125<- arg1[7] * arg2[0]
setc r15b; spill CF x412 to reg (r15)
clc;
adcx r12, [ rsp + 0x90 ]
mov byte [ rsp + 0x130 ], r8b; spilling byte x420 to mem
seto r8b; spill OF x424 to reg (r8)
mov byte [ rsp + 0x138 ], r15b; spilling byte x412 to mem
mov r15, -0x2 ; moving imm to reg
inc r15; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, [ rsp + 0x80 ]
setc r15b; spill CF x428 to reg (r15)
clc;
adcx r12, rbx
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov byte [ rsp + 0x140 ], r15b; spilling byte x428 to mem
mulx rbx, r15, [ rax + 0x20 ]; x82, x81<- arg1[7] * arg2[4]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov byte [ rsp + 0x148 ], r8b; spilling byte x424 to mem
mov byte [ rsp + 0x150 ], r10b; spilling byte x408 to mem
mulx r8, r10, [ rax + 0x30 ]; x98, x97<- arg1[5] * arg2[6]
mov byte [ rsp + 0x158 ], r11b; spilling byte x400 to mem
seto r11b; spill OF x432 to reg (r11)
mov byte [ rsp + 0x160 ], r9b; spilling byte x396 to mem
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, [ rsp + 0x70 ]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov byte [ rsp + 0x168 ], r11b; spilling byte x432 to mem
mulx r9, r11, [ rsi + 0x30 ]; x90, x89<- arg1[6] * arg2[5]
mov byte [ rsp + 0x170 ], cl; spilling byte x392 to mem
seto cl; spill OF x440 to reg (rcx)
mov [ rsp + 0x178 ], r13; spilling x137 to mem
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, [ rsp + 0x60 ]
seto r13b; spill OF x444 to reg (r13)
mov byte [ rsp + 0x180 ], cl; spilling byte x440 to mem
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, r11
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mulx r11, rcx, [ rsi + 0x20 ]; x106, x105<- arg1[4] * arg2[7]
mov byte [ rsp + 0x188 ], r13b; spilling byte x444 to mem
setc r13b; spill CF x436 to reg (r13)
clc;
adcx r12, [ rsp + 0x50 ]
adox r9, rbx
mov rbx, -0x2 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, r10
seto r10b; spill OF x232 to reg (r10)
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r12, [ rsp + 0xb0 ]
movzx r10, r10b
lea r8, [ r8 + r9 ]
lea r8, [ r8 + r10 ]
setc r9b; spill CF x448 to reg (r9)
clc;
adcx r15, rcx
adcx r11, r8
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx rcx, r10, [ rsi + 0x28 ]; x132, x131<- arg1[5] * arg2[2]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mulx r8, rbx, [ rax + 0x8 ]; x128, x127<- arg1[6] * arg2[1]
clc;
adcx r15, r14
seto r14b; spill OF x560 to reg (r14)
mov byte [ rsp + 0x190 ], r9b; spilling byte x448 to mem
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, rbx
adcx rdi, r11
mov r11, [ rsp + 0xa8 ]; load m64 x22 to register64
movzx rbx, byte [ rsp + 0xf0 ]; load byte memx384 to register64
lea r11, [ rbx + r11 ]
mov rbx, [ rsp + 0x78 ]
lea r11, [rbx+r11]
adox r8, rdi
xor rbx, rbx
adox r15, r10
adcx r15, [ rsp + 0x178 ]
movzx r10, byte [ rsp + 0xe0 ]; load byte memx388 to register64
lea r11, [ r10 + r11 ]
mov r10, [ rsp + 0x48 ]
lea r11, [r10+r11]
movzx r10, byte [ rsp + 0x170 ]; load byte memx392 to register64
lea r11, [ r10 + r11 ]
mov r10, [ rsp + 0x88 ]
lea r11, [r10+r11]
movzx r10, byte [ rsp + 0x160 ]; load byte memx396 to register64
lea r11, [ r10 + r11 ]
mov r10, [ rsp + 0x58 ]
lea r11, [r10+r11]
adox rcx, r8
adcx rcx, [ rsp + 0x110 ]
test al, al
adox r15, [ rsp + 0xa0 ]
movzx r10, byte [ rsp + 0x158 ]; load byte memx400 to register64
lea r11, [ r10 + r11 ]
adcx r11, [ rsp + 0xe8 ]
movzx r10, byte [ rsp + 0x108 ]; load byte memx404 to register64
lea r11, [ r10 + r11 ]
mov r10, [ rsp + 0xb8 ]
lea r11, [r10+r11]
adox rcx, [ rsp + 0x98 ]
sar byte [ rsp + 0x150 ], 1
adcx r11, [ rsp + 0x40 ]
adox r15, [ rsp + 0x100 ]
movzx r10, byte [ rsp + 0x138 ]; load byte memx412 to register64
lea r11, [ r10 + r11 ]
mov r10, [ rsp + 0x30 ]
lea r11, [r10+r11]
clc;
adcx r15, [ rsp + 0x120 ]
adox rcx, [ rsp + 0xf8 ]
adcx rcx, [ rsp + 0x118 ]
add r15, [ rsp + 0xd0 ]; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mulx r10, rdi, [ rax + 0x0 ]; x136, x135<- arg1[5] * arg2[0]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r8, rbx, [ rax + 0x8 ]; x142, x141<- arg1[4] * arg2[1]
adcx rcx, [ rsp + 0xc0 ]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x198 ], r8; spilling x142 to mem
mulx r9, r8, [ rsi + 0x10 ]; x160, x159<- arg1[2] * arg2[3]
sar byte [ rsp + 0x128 ], 1
adcx r11, [ rsp + 0x28 ]
sar byte [ rsp + 0x130 ], 1
adcx r11, [ rsp + 0x20 ]
mov [ rsp + 0x1a0 ], r9; spilling x160 to mem
mov r9, r15; x562, copying x267 here, cause x267 is needed in a reg for other than x562, namely all: , x562, x563, size: 2
shrd r9, rcx, 56; x562 <- x269||x267 >> 56
sar byte [ rsp + 0x148 ], 1
adcx r11, [ rsp + 0xd8 ]
mov rcx, r9; x564, copying x562 here, cause x562 is needed in a reg for other than x564, namely all: , x569--x570, x564--x565, size: 2
adox rcx, r12
movzx r12, byte [ rsp + 0x140 ]; load byte memx428 to register64
lea r11, [ r12 + r11 ]
mov r12, [ rsp + 0x68 ]
lea r11, [r12+r11]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x1a8 ], r8; spilling x159 to mem
mulx r12, r8, [ rsi + 0x18 ]; x150, x149<- arg1[3] * arg2[2]
mov [ rsp + 0x1b0 ], r12; spilling x150 to mem
movzx r12, byte [ rsp + 0x168 ]; load byte memx432 to register64
lea r11, [ r12 + r11 ]
mov r12, [ rsp + 0x18 ]
lea r11, [r12+r11]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x1b8 ], r8; spilling x149 to mem
mulx r12, r8, [ rsi + 0x38 ]; x86, x85<- arg1[7] * arg2[2]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x1c0 ], rbx; spilling x141 to mem
mov [ rsp + 0x1c8 ], r10; spilling x136 to mem
mulx rbx, r10, [ rax + 0x18 ]; x94, x93<- arg1[6] * arg2[3]
movzx r13, r13b
lea r11, [ r13 + r11 ]
mov r13, [ rsp + 0xc8 ]
lea r11, [r13+r11]
mov r13, 0xffffffffffffff ; moving imm to reg
mov [ rsp + 0x1d0 ], rdi; spilling x135 to mem
seto dil; spill OF x565 to reg (rdi)
mov [ rsp + 0x1d8 ], rbx; spilling x94 to mem
mov rbx, rcx; x568, copying x564 here, cause x564 is needed in a reg for other than x568, namely all: , x567, x568, size: 2
and rbx, r13; x568 <- x564&0xffffffffffffff
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x1e0 ], rbx; spilling x568 to mem
mulx r13, rbx, [ rax + 0x30 ]; x16, x15<- arg1[7] * arg2[6]
sar byte [ rsp + 0x180 ], 1
adcx r11, [ rsp + 0x38 ]
sar byte [ rsp + 0x188 ], 1
adcx r11, [ rsp + 0x10 ]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x1e8 ], r12; spilling x86 to mem
mov [ rsp + 0x1f0 ], r10; spilling x93 to mem
mulx r12, r10, [ rax + 0x30 ]; x116, x115<- arg1[3] * arg2[6]
sar byte [ rsp + 0x190 ], 1
adcx r11, [ rsp + 0x8 ]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x1f8 ], r12; spilling x116 to mem
mov [ rsp + 0x200 ], r10; spilling x115 to mem
mulx r12, r10, [ rax + 0x28 ]; x186, x185<- arg1[0] * arg2[5]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x208 ], r12; spilling x186 to mem
mov [ rsp + 0x210 ], r10; spilling x185 to mem
mulx r12, r10, [ rax + 0x28 ]; x110, x109<- arg1[4] * arg2[5]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x218 ], r12; spilling x110 to mem
mov [ rsp + 0x220 ], r10; spilling x109 to mem
mulx r12, r10, [ rax + 0x38 ]; x20, x19<- arg1[6] * arg2[7]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x228 ], r8; spilling x85 to mem
mov [ rsp + 0x230 ], r13; spilling x16 to mem
mulx r8, r13, [ rax + 0x20 ]; x102, x101<- arg1[5] * arg2[4]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x238 ], r8; spilling x102 to mem
mov [ rsp + 0x240 ], r13; spilling x101 to mem
mulx r8, r13, [ rsi + 0x10 ]; x120, x119<- arg1[2] * arg2[7]
mov [ rsp + 0x248 ], r8; spilling x120 to mem
movzx r8, r14b; x561, copying x560 here, cause x560 is needed in a reg for other than x561, namely all: , x561, size: 1
lea r8, [ r8 + r11 ]
movzx r14, dil; x566, copying x565 here, cause x565 is needed in a reg for other than x566, namely all: , x566, size: 1
lea r14, [ r14 + r8 ]
adox rbx, r10
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx rdi, r11, [ rax + 0x30 ]; x28, x27<- arg1[7] * arg2[6]
adox r12, [ rsp + 0x230 ]
test al, al
adox rbx, r11
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mulx r10, r8, [ rsi + 0x30 ]; x40, x39<- arg1[6] * arg2[7]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x250 ], r13; spilling x119 to mem
mulx r11, r13, [ rax + 0x20 ]; x172, x171<- arg1[1] * arg2[4]
adcx rbx, r8
setc r8b; spill CF x332 to reg (r8)
clc;
adcx rbx, [ rsp + 0x228 ]
mov [ rsp + 0x258 ], rbp; spilling x221 to mem
setc bpl; spill CF x336 to reg (rbp)
clc;
adcx rbx, [ rsp + 0x1f0 ]
adox rdi, r12
setc r12b; spill CF x340 to reg (r12)
shrd rcx, r14, 56; x567 <- x566||x564 >> 56
sar  r8b, 1
adcx r10, rdi
sar  bpl, 1
adcx r10, [ rsp + 0x1e8 ]
adox rbx, [ rsp + 0x240 ]
movzx r12, r12b
lea r10, [ r12 + r10 ]
mov r12, [ rsp + 0x1d8 ]
lea r10, [r12+r10]
clc;
adcx rbx, [ rsp + 0x220 ]
adox r10, [ rsp + 0x238 ]
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, [ rsp + 0x200 ]
adcx r10, [ rsp + 0x218 ]
adox r10, [ rsp + 0x1f8 ]
test al, al
adox rbx, [ rsp + 0x250 ]
adcx rbx, [ rsp + 0x1d0 ]
adox r10, [ rsp + 0x248 ]
adcx r10, [ rsp + 0x1c8 ]
add rbx, [ rsp + 0x1c0 ]; could be done better, if r0 has been u8 as well
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rbx, [ rsp + 0x1b8 ]
adcx r10, [ rsp + 0x198 ]
clc;
adcx rbx, [ rsp + 0x1a8 ]
seto r8b; spill OF x368 to reg (r8)
mov rbp, -0x3 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbx, r13
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx r13, r12, [ rax + 0x38 ]; x14, x13<- arg1[7] * arg2[7]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rdi, r14, [ rax + 0x30 ]; x184, x183<- arg1[0] * arg2[6]
movzx r8, r8b
lea r10, [ r8 + r10 ]
mov r8, [ rsp + 0x1b0 ]
lea r10, [r8+r10]
adcx r10, [ rsp + 0x1a0 ]
adox r11, r10
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx r8, r10, [ rsi + 0x28 ]; x134, x133<- arg1[5] * arg2[1]
test al, al
adox rbx, [ rsp + 0x210 ]
adox r11, [ rsp + 0x208 ]
adcx rbx, rcx
adc r11, 0x0
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mulx rcx, rbp, [ rsi + 0x18 ]; x114, x113<- arg1[3] * arg2[7]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x260 ], rdi; spilling x184 to mem
mov [ rsp + 0x268 ], r8; spilling x134 to mem
mulx rdi, r8, [ rsi + 0x18 ]; x148, x147<- arg1[3] * arg2[3]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x270 ], rdi; spilling x148 to mem
mov [ rsp + 0x278 ], r14; spilling x183 to mem
mulx rdi, r14, [ rax + 0x30 ]; x108, x107<- arg1[4] * arg2[6]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x280 ], rcx; spilling x114 to mem
mov [ rsp + 0x288 ], r8; spilling x147 to mem
mulx rcx, r8, [ rax + 0x10 ]; x140, x139<- arg1[4] * arg2[2]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x290 ], rcx; spilling x140 to mem
mov [ rsp + 0x298 ], r8; spilling x139 to mem
mulx rcx, r8, [ rax + 0x28 ]; x170, x169<- arg1[1] * arg2[5]
mov [ rsp + 0x2a0 ], rcx; spilling x170 to mem
mov rcx, rbx; x580, copying x572 here, cause x572 is needed in a reg for other than x580, namely all: , x581, x580, size: 2
shrd rcx, r11, 56; x580 <- x574||x572 >> 56
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x2a8 ], rcx; spilling x580 to mem
mulx r11, rcx, [ rax + 0x38 ]; x26, x25<- arg1[7] * arg2[7]
add r12, rcx; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x2b0 ], r8; spilling x169 to mem
mulx rcx, r8, [ rax + 0x0 ]; x130, x129<- arg1[6] * arg2[0]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x2b8 ], rcx; spilling x130 to mem
mov [ rsp + 0x2c0 ], rdi; spilling x108 to mem
mulx rcx, rdi, [ rsi + 0x30 ]; x92, x91<- arg1[6] * arg2[4]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x2c8 ], r10; spilling x133 to mem
mov [ rsp + 0x2d0 ], r8; spilling x129 to mem
mulx r10, r8, [ rsi + 0x38 ]; x84, x83<- arg1[7] * arg2[3]
adcx r11, r13
add r12, r8; could be done better, if r0 has been u8 as well
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mulx r13, r8, [ rsi + 0x28 ]; x100, x99<- arg1[5] * arg2[5]
mov [ rsp + 0x2d8 ], r13; spilling x100 to mem
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, rdi
adcx r10, r11
clc;
adcx r12, r8
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx rdi, r11, [ rsi + 0x10 ]; x158, x157<- arg1[2] * arg2[4]
adox rcx, r10
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r12, r14
seto r14b; spill OF x288 to reg (r14)
mov r8, -0x3 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r12, rbp
seto bpl; spill OF x292 to reg (rbp)
mov r10, -0x3 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug 7; load -3, increase it, discard the information #workaround). #last resort
adox r12, [ rsp + 0x2d0 ]
setc r10b; spill CF x284 to reg (r10)
clc;
adcx r12, [ rsp + 0x2c8 ]
movzx r10, r10b
lea rcx, [ r10 + rcx ]
mov r10, [ rsp + 0x2d8 ]
lea rcx, [r10+rcx]
movzx r14, r14b
lea rcx, [ r14 + rcx ]
mov r14, [ rsp + 0x2c0 ]
lea rcx, [r14+rcx]
setc r10b; spill CF x300 to reg (r10)
clc;
adcx r12, [ rsp + 0x298 ]
seto r14b; spill OF x296 to reg (r14)
mov r8, -0x3 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r12, [ rsp + 0x288 ]
seto r8b; spill OF x308 to reg (r8)
mov [ rsp + 0x2e0 ], rdi; spilling x158 to mem
mov rdi, -0x3 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r12, r11
movzx rbp, bpl
lea rcx, [ rbp + rcx ]
mov rbp, [ rsp + 0x280 ]
lea rcx, [rbp+rcx]
seto r11b; spill OF x312 to reg (r11)
mov rbp, -0x3 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug 7; load -3, increase it, discard the information #workaround). #last resort
adox r12, [ rsp + 0x2b0 ]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx rbp, r13, [ rax + 0x20 ]; x68, x67<- arg1[4] * arg2[4]
setc dil; spill CF x304 to reg (rdi)
clc;
adcx r12, [ rsp + 0x278 ]
movzx r14, r14b
lea rcx, [ r14 + rcx ]
mov r14, [ rsp + 0x2b8 ]
lea rcx, [r14+rcx]
mov r14, 0xffffffffffffff ; moving imm to reg
mov [ rsp + 0x2e8 ], rbp; spilling x68 to mem
setc bpl; spill CF x320 to reg (rbp)
mov [ rsp + 0x2f0 ], r13; spilling x67 to mem
seto r13b; spill OF x316 to reg (r13)
and r15, r14; x563 <- x267&0xffffffffffffff
sar  r10b, 1
adcx rcx, [ rsp + 0x268 ]
sar  dil, 1
adcx rcx, [ rsp + 0x290 ]
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx r10, rdi, [ rsi + 0x0 ]; x196, x195<- arg1[0] * arg2[0]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x2f8 ], r10; spilling x196 to mem
mulx r14, r10, [ rax + 0x30 ]; x10, x9<- arg1[6] * arg2[6]
sar  r8b, 1
adcx rcx, [ rsp + 0x270 ]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x300 ], rdi; spilling x195 to mem
mulx r8, rdi, [ rax + 0x38 ]; x80, x79<- arg1[1] * arg2[7]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x308 ], r8; spilling x80 to mem
mov [ rsp + 0x310 ], rdi; spilling x79 to mem
mulx r8, rdi, [ rax + 0x30 ]; x78, x77<- arg1[2] * arg2[6]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x318 ], r8; spilling x78 to mem
mov [ rsp + 0x320 ], rdi; spilling x77 to mem
mulx r8, rdi, [ rax + 0x38 ]; x12, x11<- arg1[5] * arg2[7]
sar  r11b, 1
adcx rcx, [ rsp + 0x2e0 ]
sar  r13b, 1
adcx rcx, [ rsp + 0x2a0 ]
sar  bpl, 1
adcx rcx, [ rsp + 0x260 ]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx r11, r13, [ rax + 0x28 ]; x6, x5<- arg1[7] * arg2[5]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x328 ], r8; spilling x12 to mem
mulx rbp, r8, [ rsi + 0x30 ]; x50, x49<- arg1[6] * arg2[2]
adox r12, [ rsp + 0x2a8 ]
clc;
adcx r13, r10
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x330 ], rbp; spilling x50 to mem
mulx r10, rbp, [ rax + 0x28 ]; x74, x73<- arg1[3] * arg2[5]
mov [ rsp + 0x338 ], r10; spilling x74 to mem
mov r10, 0x0 ; moving imm to reg
adox rcx, r10
mov [ rsp + 0x340 ], rbp; spilling x73 to mem
mov rbp, -0x3 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r13, rdi
setc dil; spill CF x520 to reg (rdi)
seto r10b; spill OF x524 to reg (r10)
mov rbp, r12; x590, copying x582 here, cause x582 is needed in a reg for other than x590, namely all: , x590, x591, size: 2
shrd rbp, rcx, 56; x590 <- x584||x582 >> 56
lea rbp, [ rbp + r15 ]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx r15, rcx, [ rax + 0x8 ]; x38, x37<- arg1[7] * arg2[1]
sar  dil, 1
adcx r14, r11
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mulx r11, rdi, [ rsi + 0x28 ]; x60, x59<- arg1[5] * arg2[3]
mov [ rsp + 0x348 ], r11; spilling x60 to mem
mov r11, rbp; x596, copying x592 here, cause x592 is needed in a reg for other than x596, namely all: , x596, x597, size: 2
shr r11, 56; x596 <- x592>> 56
add r13, rcx; could be done better, if r0 has been u8 as well
movzx r10, r10b
lea r14, [ r10 + r14 ]
mov r10, [ rsp + 0x328 ]
lea r14, [r10+r14]
adcx r15, r14
test al, al
adox r13, r8
adcx r13, rdi
adox r15, [ rsp + 0x330 ]
mov r8, 0xffffffffffffff ; moving imm to reg
setc r10b; spill CF x536 to reg (r10)
and r12, r8; x591 <- x582&0xffffffffffffff
mov rcx, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rcx + 0x30 ], r12; out1[6] = x591
sar  r10b, 1
adcx r15, [ rsp + 0x348 ]
adox r13, [ rsp + 0x2f0 ]
adox r15, [ rsp + 0x2e8 ]
xor rdi, rdi
adox r13, [ rsp + 0x340 ]
adcx r13, [ rsp + 0x320 ]
adox r15, [ rsp + 0x338 ]
mov r14, -0x3 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r13, [ rsp + 0x310 ]
mov r10, r11; x600, copying x596 here, cause x596 is needed in a reg for other than x600, namely all: , x601, x600, size: 2
mov r12, [ rsp + 0x1e0 ]; load m64 x568 to register64
lea r10, [ r10 + r12 ]; r8/64 + m8
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx r12, rdi, [ rax + 0x10 ]; x36, x35<- arg1[7] * arg2[2]
adcx r15, [ rsp + 0x318 ]
clc;
adcx r13, [ rsp + 0x300 ]
adox r15, [ rsp + 0x308 ]
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r9, r13
adcx r15, [ rsp + 0x2f8 ]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mulx r13, r14, [ rsi + 0x38 ]; x4, x3<- arg1[7] * arg2[6]
mov r8, 0x0 ; moving imm to reg
adox r15, r8
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x0 ], rcx; spilling out1 to mem
mulx r8, rcx, [ rax + 0x20 ]; x58, x57<- arg1[5] * arg2[4]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x350 ], r10; spilling x600 to mem
mov [ rsp + 0x358 ], r8; spilling x58 to mem
mulx r10, r8, [ rax + 0x0 ]; x180, x179<- arg1[1] * arg2[0]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x360 ], r10; spilling x180 to mem
mov [ rsp + 0x368 ], r8; spilling x179 to mem
mulx r10, r8, [ rax + 0x38 ]; x8, x7<- arg1[6] * arg2[7]
mov [ rsp + 0x370 ], r12; spilling x36 to mem
mov r12, r9; x575, copying x569 here, cause x569 is needed in a reg for other than x575, namely all: , x576, x575, size: 2
shrd r12, r15, 56; x575 <- x571||x569 >> 56
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x378 ], r12; spilling x575 to mem
mulx r15, r12, [ rsi + 0x20 ]; x66, x65<- arg1[4] * arg2[5]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x380 ], r15; spilling x66 to mem
mov [ rsp + 0x388 ], r12; spilling x65 to mem
mulx r15, r12, [ rax + 0x30 ]; x72, x71<- arg1[3] * arg2[6]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x390 ], r15; spilling x72 to mem
mov [ rsp + 0x398 ], r12; spilling x71 to mem
mulx r15, r12, [ rax + 0x18 ]; x48, x47<- arg1[6] * arg2[3]
mov [ rsp + 0x3a0 ], r15; spilling x48 to mem
mov r15, 0xffffffffffffff ; moving imm to reg
and r9, r15; x576 <- x569&0xffffffffffffff
adox r14, r8
adcx r14, rdi
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mulx rdi, r8, [ rsi + 0x10 ]; x76, x75<- arg1[2] * arg2[7]
seto r15b; spill OF x484 to reg (r15)
mov [ rsp + 0x3a8 ], r9; spilling x576 to mem
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, r12
movzx r15, r15b
lea r10, [ r10 + r13 ]
lea r10, [ r10 + r15 ]
seto r13b; spill OF x492 to reg (r13)
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r14, rcx
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mulx rcx, r12, [ rsi + 0x38 ]; x34, x33<- arg1[7] * arg2[3]
setc r15b; spill CF x488 to reg (r15)
clc;
adcx r14, [ rsp + 0x388 ]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x3b0 ], rcx; spilling x34 to mem
mulx r9, rcx, [ rsi + 0x0 ]; x194, x193<- arg1[0] * arg2[1]
mov [ rsp + 0x3b8 ], r12; spilling x33 to mem
setc r12b; spill CF x500 to reg (r12)
clc;
adcx r14, [ rsp + 0x398 ]
movzx r15, r15b
lea r10, [ r15 + r10 ]
mov r15, [ rsp + 0x370 ]
lea r10, [r15+r10]
seto r15b; spill OF x496 to reg (r15)
mov [ rsp + 0x3c0 ], r9; spilling x194 to mem
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, r8
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx r8, r9, [ rsi + 0x10 ]; x166, x165<- arg1[2] * arg2[0]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x3c8 ], r8; spilling x166 to mem
mov [ rsp + 0x3d0 ], r9; spilling x165 to mem
mulx r8, r9, [ rsi + 0x8 ]; x178, x177<- arg1[1] * arg2[1]
mov [ rsp + 0x3d8 ], r8; spilling x178 to mem
setc r8b; spill CF x504 to reg (r8)
clc;
adcx r14, [ rsp + 0x368 ]
movzx r13, r13b
lea r10, [ r13 + r10 ]
mov r13, [ rsp + 0x3a0 ]
lea r10, [r13+r10]
movzx r15, r15b
lea r10, [ r15 + r10 ]
mov r15, [ rsp + 0x358 ]
lea r10, [r15+r10]
movzx r12, r12b
lea r10, [ r12 + r10 ]
mov r12, [ rsp + 0x380 ]
lea r10, [r12+r10]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r13, r15, [ rax + 0x38 ]; x70, x69<- arg1[3] * arg2[7]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x3e0 ], r9; spilling x177 to mem
mulx r12, r9, [ rax + 0x30 ]; x64, x63<- arg1[4] * arg2[6]
movzx r8, r8b
lea r10, [ r8 + r10 ]
mov r8, [ rsp + 0x390 ]
lea r10, [r8+r10]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x3e8 ], r13; spilling x70 to mem
mulx r8, r13, [ rsi + 0x30 ]; x46, x45<- arg1[6] * arg2[4]
adox rdi, r10
adcx rdi, [ rsp + 0x360 ]
add r14, rcx; could be done better, if r0 has been u8 as well
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, [ rsp + 0x378 ]
adcx rdi, [ rsp + 0x3c0 ]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mulx r10, rcx, [ rsi + 0x38 ]; x2, x1<- arg1[7] * arg2[7]
clc;
adcx rcx, [ rsp + 0x3b8 ]
adcx r10, [ rsp + 0x3b0 ]
mov [ rsp + 0x3f0 ], r15; spilling x69 to mem
mov r15, 0x0 ; moving imm to reg
adox rdi, r15
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x3f8 ], r12; spilling x64 to mem
mulx r15, r12, [ rsi + 0x0 ]; x192, x191<- arg1[0] * arg2[2]
add rcx, r13; could be done better, if r0 has been u8 as well
adcx r8, r10
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mulx r13, r10, [ rsi + 0x28 ]; x56, x55<- arg1[5] * arg2[5]
mov [ rsp + 0x400 ], r15; spilling x192 to mem
xor r15, r15
adox rcx, r10
adox r13, r8
adcx rcx, r9
setc r9b; spill CF x464 to reg (r9)
mov r8, r14; x585, copying x577 here, cause x577 is needed in a reg for other than x585, namely all: , x586, x585, size: 2
shrd r8, rdi, 56; x585 <- x579||x577 >> 56
mov rdi, 0xffffffffffffff ; moving imm to reg
and rbx, rdi; x581 <- x572&0xffffffffffffff
sar  r9b, 1
adcx r13, [ rsp + 0x3f8 ]
adox rcx, [ rsp + 0x3f0 ]
adox r13, [ rsp + 0x3e8 ]
and rbp, rdi; x597 <- x592&0xffffffffffffff
adox rcx, [ rsp + 0x3d0 ]
adcx r11, [ rsp + 0x3a8 ]
adox r13, [ rsp + 0x3c8 ]
test al, al
adox rcx, [ rsp + 0x3e0 ]
adcx rcx, r12
setc r12b; spill CF x480 to reg (r12)
seto r10b; spill OF x476 to reg (r10)
mov r9, r11; x606, copying x601 here, cause x601 is needed in a reg for other than x606, namely all: , x607, x606, size: 2
shr r9, 56; x606 <- x601>> 56
sar  r10b, 1
adcx r13, [ rsp + 0x3d8 ]
and r14, rdi; x586 <- x577&0xffffffffffffff
adox rcx, r8
seto r8b; spill OF x588 to reg (r8)
mov r10, rcx; x594, copying x587 here, cause x587 is needed in a reg for other than x594, namely all: , x594, x593, size: 2
and r10, rdi; x594 <- x587&0xffffffffffffff
sar  r12b, 1
adcx r13, [ rsp + 0x400 ]
movzx r12, r8b; x589, copying x588 here, cause x588 is needed in a reg for other than x589, namely all: , x589, size: 1
lea r12, [ r12 + r13 ]
shrd rcx, r12, 56; x593 <- x589||x587 >> 56
mov r8, [ rsp + 0x258 ]; x226, copying x221 here, cause x221 is needed in a reg for other than x226, namely all: , x226, size: 1
and r8, rdi; x226 <- x221&0xffffffffffffff
mov r13, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r13 + 0x10 ], r10; out1[2] = x594
lea rcx, [ rcx + r8 ]
mov [ r13 + 0x38 ], rbp; out1[7] = x597
mov r12, rcx; x598, copying x595 here, cause x595 is needed in a reg for other than x598, namely all: , x598, x599, size: 2
shr r12, 56; x598 <- x595>> 56
and rcx, rdi; x599 <- x595&0xffffffffffffff
mov [ r13 + 0x18 ], rcx; out1[3] = x599
lea r9, [ r9 + r14 ]
add r12, [ rsp + 0x350 ]
and r11, rdi; x607 <- x601&0xffffffffffffff
mov r14, r12; x604, copying x602 here, cause x602 is needed in a reg for other than x604, namely all: , x603, x604, size: 2
and r14, rdi; x604 <- x602&0xffffffffffffff
mov [ r13 + 0x0 ], r11; out1[0] = x607
shr r12, 56; x603 <- x602>> 56
lea r12, [ r12 + rbx ]
mov [ r13 + 0x28 ], r12; out1[5] = x605
mov [ r13 + 0x20 ], r14; out1[4] = x604
mov [ r13 + 0x8 ], r9; out1[1] = x608
mov rbx, [ rsp + 0x408 ]; restoring from stack
mov rbp, [ rsp + 0x410 ]; restoring from stack
mov r12, [ rsp + 0x418 ]; restoring from stack
mov r13, [ rsp + 0x420 ]; restoring from stack
mov r14, [ rsp + 0x428 ]; restoring from stack
mov r15, [ rsp + 0x430 ]; restoring from stack
add rsp, 0x438 
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; clocked at 3600 MHz
; first cyclecount 229.83, best 184.88732394366198, lastGood 187.54285714285714
; seed 95742508246954 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4067432 ms / 60000 runs=> 67.79053333333333ms/run
; Time spent for assembling and measureing (initial batch_size=70, initial num_batches=101): 185439 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.04559117398889521
; number reverted permutation/ tried permutation: 16240 / 30254 =53.679%
; number reverted decision/ tried decision: 15228 / 29747 =51.192%