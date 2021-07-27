SECTION .text
	GLOBAL mul_p448_solinas
mul_p448_solinas:
sub rsp, 0x508 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x4d8 ], rbx; saving to stack
mov [ rsp + 0x4e0 ], rbp; saving to stack
mov [ rsp + 0x4e8 ], r12; saving to stack
mov [ rsp + 0x4f0 ], r13; saving to stack
mov [ rsp + 0x4f8 ], r14; saving to stack
mov [ rsp + 0x500 ], r15; saving to stack
mov rax, rdx; preserving value of arg2 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r10, r11, [ rax + 0x38 ]; x182, x181<- arg1[0] * arg2[7]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mulx rbx, rbp, [ rsi + 0x10 ]; x156, x155<- arg1[2] * arg2[5]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mulx r12, r13, [ rsi + 0x8 ]; x168, x167<- arg1[1] * arg2[6]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx r14, r15, [ rsi + 0x18 ]; x146, x145<- arg1[3] * arg2[4]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx rcx, r8, [ rax + 0x18 ]; x138, x137<- arg1[4] * arg2[3]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r9, rdi, [ rsi + 0x28 ]; x132, x131<- arg1[5] * arg2[2]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x8 ], r10; spilling x182 to mem
mov [ rsp + 0x10 ], r12; spilling x168 to mem
mulx r10, r12, [ rsi + 0x20 ]; x106, x105<- arg1[4] * arg2[7]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x18 ], rbx; spilling x156 to mem
mov [ rsp + 0x20 ], r14; spilling x146 to mem
mulx rbx, r14, [ rsi + 0x30 ]; x128, x127<- arg1[6] * arg2[1]
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x28 ], rcx; spilling x138 to mem
mov [ rsp + 0x30 ], r9; spilling x132 to mem
mulx rcx, r9, [ rsi + 0x38 ]; x126, x125<- arg1[7] * arg2[0]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x38 ], rbx; spilling x128 to mem
mov [ rsp + 0x40 ], rcx; spilling x126 to mem
mulx rbx, rcx, [ rax + 0x30 ]; x98, x97<- arg1[5] * arg2[6]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x48 ], r10; spilling x106 to mem
mov [ rsp + 0x50 ], rbx; spilling x98 to mem
mulx r10, rbx, [ rsi + 0x38 ]; x82, x81<- arg1[7] * arg2[4]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x58 ], r10; spilling x82 to mem
mov [ rsp + 0x60 ], r11; spilling x181 to mem
mulx r10, r11, [ rsi + 0x30 ]; x90, x89<- arg1[6] * arg2[5]
mov [ rsp + 0x68 ], r10; spilling x90 to mem
xor r10, r10
adox rbx, r11
adcx rbx, rcx
seto cl; spill OF x228 to reg (rcx)
mov r11, -0x3 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbx, r12
seto r12b; spill OF x236 to reg (r12)
mov r11, -0x3 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbx, r9
setc r9b; spill CF x232 to reg (r9)
clc;
adcx rbx, r14
seto r14b; spill OF x240 to reg (r14)
mov r11, -0x3 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbx, rdi
seto dil; spill OF x248 to reg (rdi)
mov r11, -0x3 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbx, r8
setc r8b; spill CF x244 to reg (r8)
clc;
adcx rbx, r15
setc r15b; spill CF x256 to reg (r15)
clc;
adcx rbx, rbp
setc bpl; spill CF x260 to reg (rbp)
clc;
adcx rbx, r13
seto r13b; spill OF x252 to reg (r13)
mov r11, -0x3 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbx, [ rsp + 0x60 ]
mov r10, [ rsp + 0x58 ]; load m64 x82 to register64
movzx rcx, cl
lea r10, [ rcx + r10 ]
mov rcx, [ rsp + 0x68 ]
lea r10, [rcx+r10]
movzx r9, r9b
lea r10, [ r9 + r10 ]
mov r9, [ rsp + 0x50 ]
lea r10, [r9+r10]
movzx r12, r12b
lea r10, [ r12 + r10 ]
mov r12, [ rsp + 0x48 ]
lea r10, [r12+r10]
movzx r14, r14b
lea r10, [ r14 + r10 ]
mov r14, [ rsp + 0x40 ]
lea r10, [r14+r10]
movzx r8, r8b
lea r10, [ r8 + r10 ]
mov r8, [ rsp + 0x38 ]
lea r10, [r8+r10]
movzx rdi, dil
lea r10, [ rdi + r10 ]
mov rdi, [ rsp + 0x30 ]
lea r10, [rdi+r10]
movzx r13, r13b
lea r10, [ r13 + r10 ]
mov r13, [ rsp + 0x28 ]
lea r10, [r13+r10]
movzx r15, r15b
lea r10, [ r15 + r10 ]
mov r15, [ rsp + 0x20 ]
lea r10, [r15+r10]
movzx rbp, bpl
lea r10, [ rbp + r10 ]
mov rbp, [ rsp + 0x18 ]
lea r10, [rbp+r10]
adcx r10, [ rsp + 0x10 ]
adox r10, [ rsp + 0x8 ]
mov rcx, rbx; x562, copying x267 here, cause x267 is needed in a reg for other than x562, namely all: , x562, x563, size: 2
shrd rcx, r10, 56; x562 <- x269||x267 >> 56
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r9, r12, [ rax + 0x8 ]; x164, x163<- arg1[2] * arg2[1]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r14, r8, [ rax + 0x10 ]; x176, x175<- arg1[1] * arg2[2]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mulx rdi, r13, [ rsi + 0x0 ]; x190, x189<- arg1[0] * arg2[3]
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx r15, rbp, [ rsi + 0x18 ]; x154, x153<- arg1[3] * arg2[0]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mulx r10, r11, [ rsi + 0x20 ]; x62, x61<- arg1[4] * arg2[7]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x70 ], rcx; spilling x562 to mem
mov [ rsp + 0x78 ], rdi; spilling x190 to mem
mulx rcx, rdi, [ rax + 0x30 ]; x54, x53<- arg1[5] * arg2[6]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x80 ], r14; spilling x176 to mem
mov [ rsp + 0x88 ], r9; spilling x164 to mem
mulx r14, r9, [ rsi + 0x30 ]; x44, x43<- arg1[6] * arg2[5]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x90 ], r15; spilling x154 to mem
mov [ rsp + 0x98 ], r10; spilling x62 to mem
mulx r15, r10, [ rax + 0x20 ]; x32, x31<- arg1[7] * arg2[4]
add r10, r9; could be done better, if r0 has been u8 as well
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r10, rdi
setc dil; spill CF x198 to reg (rdi)
clc;
adcx r10, r11
seto r11b; spill OF x202 to reg (r11)
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r10, rbp
movzx rdi, dil
lea r14, [ r14 + r15 ]
lea r14, [ r14 + rdi ]
movzx r11, r11b
lea rcx, [ rcx + r14 ]
lea rcx, [ rcx + r11 ]
setc bpl; spill CF x206 to reg (rbp)
clc;
adcx r10, r12
setc r12b; spill CF x214 to reg (r12)
clc;
adcx r10, r8
setc r8b; spill CF x218 to reg (r8)
clc;
adcx r10, r13
movzx rbp, bpl
lea rcx, [ rbp + rcx ]
mov rbp, [ rsp + 0x98 ]
lea rcx, [rbp+rcx]
adox rcx, [ rsp + 0x90 ]
movzx r12, r12b
lea rcx, [ r12 + rcx ]
mov r12, [ rsp + 0x88 ]
lea rcx, [r12+rcx]
movzx r8, r8b
lea rcx, [ r8 + rcx ]
mov r8, [ rsp + 0x80 ]
lea rcx, [r8+rcx]
adcx rcx, [ rsp + 0x78 ]
mov r13, r10; x225, copying x221 here, cause x221 is needed in a reg for other than x225, namely all: , x226, x225, size: 2
shrd r13, rcx, 56; x225 <- x223||x221 >> 56
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx r15, rdi, [ rsi + 0x0 ]; x188, x187<- arg1[0] * arg2[4]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mulx r11, rbp, [ rsi + 0x8 ]; x174, x173<- arg1[1] * arg2[3]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx r14, r12, [ rsi + 0x10 ]; x162, x161<- arg1[2] * arg2[2]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx r8, rcx, [ rsi + 0x18 ]; x152, x151<- arg1[3] * arg2[1]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0xa0 ], r15; spilling x188 to mem
mulx r9, r15, [ rax + 0x0 ]; x144, x143<- arg1[4] * arg2[0]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0xa8 ], r11; spilling x174 to mem
mov [ rsp + 0xb0 ], r14; spilling x162 to mem
mulx r11, r14, [ rsi + 0x10 ]; x122, x121<- arg1[2] * arg2[6]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0xb8 ], r8; spilling x152 to mem
mov [ rsp + 0xc0 ], r9; spilling x144 to mem
mulx r8, r9, [ rax + 0x38 ]; x124, x123<- arg1[1] * arg2[7]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0xc8 ], r8; spilling x124 to mem
mov [ rsp + 0xd0 ], r11; spilling x122 to mem
mulx r8, r11, [ rsi + 0x18 ]; x118, x117<- arg1[3] * arg2[5]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0xd8 ], r8; spilling x118 to mem
mov [ rsp + 0xe0 ], r13; spilling x225 to mem
mulx r8, r13, [ rax + 0x20 ]; x112, x111<- arg1[4] * arg2[4]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0xe8 ], r8; spilling x112 to mem
mov [ rsp + 0xf0 ], rdi; spilling x187 to mem
mulx r8, rdi, [ rax + 0x18 ]; x104, x103<- arg1[5] * arg2[3]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0xf8 ], r8; spilling x104 to mem
mov [ rsp + 0x100 ], rbp; spilling x173 to mem
mulx r8, rbp, [ rax + 0x10 ]; x96, x95<- arg1[6] * arg2[2]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x108 ], r8; spilling x96 to mem
mov [ rsp + 0x110 ], r12; spilling x161 to mem
mulx r8, r12, [ rax + 0x8 ]; x88, x87<- arg1[7] * arg2[1]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x118 ], r8; spilling x88 to mem
mov [ rsp + 0x120 ], rcx; spilling x151 to mem
mulx r8, rcx, [ rsi + 0x28 ]; x52, x51<- arg1[5] * arg2[7]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x128 ], r8; spilling x52 to mem
mov [ rsp + 0x130 ], r15; spilling x143 to mem
mulx r8, r15, [ rax + 0x28 ]; x30, x29<- arg1[7] * arg2[5]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x138 ], r8; spilling x30 to mem
mov [ rsp + 0x140 ], r9; spilling x123 to mem
mulx r8, r9, [ rax + 0x30 ]; x22, x21<- arg1[6] * arg2[6]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x148 ], r8; spilling x22 to mem
mov [ rsp + 0x150 ], r14; spilling x121 to mem
mulx r8, r14, [ rax + 0x30 ]; x42, x41<- arg1[6] * arg2[6]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x158 ], r8; spilling x42 to mem
mov [ rsp + 0x160 ], r11; spilling x117 to mem
mulx r8, r11, [ rsi + 0x28 ]; x24, x23<- arg1[5] * arg2[7]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x168 ], r8; spilling x24 to mem
mov [ rsp + 0x170 ], r13; spilling x111 to mem
mulx r8, r13, [ rax + 0x28 ]; x18, x17<- arg1[7] * arg2[5]
mov [ rsp + 0x178 ], r8; spilling x18 to mem
xor r8, r8
adox r13, r9
adcx r13, r11
setc r9b; spill CF x388 to reg (r9)
clc;
adcx r13, r15
seto r15b; spill OF x384 to reg (r15)
mov r11, -0x3 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r13, r14
seto r14b; spill OF x396 to reg (r14)
mov r11, -0x3 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r13, rcx
seto cl; spill OF x400 to reg (rcx)
mov r11, -0x3 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r13, r12
setc r12b; spill CF x392 to reg (r12)
clc;
adcx r13, rbp
setc bpl; spill CF x408 to reg (rbp)
clc;
adcx r13, rdi
setc dil; spill CF x412 to reg (rdi)
clc;
adcx r13, [ rsp + 0x170 ]
seto r11b; spill OF x404 to reg (r11)
mov byte [ rsp + 0x180 ], dil; spilling byte x412 to mem
mov rdi, -0x3 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r13, [ rsp + 0x160 ]
seto dil; spill OF x420 to reg (rdi)
mov byte [ rsp + 0x188 ], bpl; spilling byte x408 to mem
mov rbp, -0x3 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r13, [ rsp + 0x150 ]
setc bpl; spill CF x416 to reg (rbp)
clc;
adcx r13, [ rsp + 0x140 ]
mov byte [ rsp + 0x190 ], dil; spilling byte x420 to mem
setc dil; spill CF x428 to reg (rdi)
clc;
adcx r13, [ rsp + 0x130 ]
mov byte [ rsp + 0x198 ], dil; spilling byte x428 to mem
setc dil; spill CF x432 to reg (rdi)
clc;
adcx r13, [ rsp + 0x120 ]
mov byte [ rsp + 0x1a0 ], dil; spilling byte x432 to mem
setc dil; spill CF x436 to reg (rdi)
clc;
adcx r13, [ rsp + 0x110 ]
mov byte [ rsp + 0x1a8 ], dil; spilling byte x436 to mem
seto dil; spill OF x424 to reg (rdi)
mov byte [ rsp + 0x1b0 ], bpl; spilling byte x416 to mem
mov rbp, -0x3 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r13, [ rsp + 0x100 ]
seto bpl; spill OF x444 to reg (rbp)
mov byte [ rsp + 0x1b8 ], dil; spilling byte x424 to mem
mov rdi, -0x3 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r13, [ rsp + 0xf0 ]
seto dil; spill OF x448 to reg (rdi)
mov byte [ rsp + 0x1c0 ], bpl; spilling byte x444 to mem
mov rbp, -0x3 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r13, [ rsp + 0xe0 ]
mov r8, [ rsp + 0x178 ]; load m64 x18 to register64
movzx r15, r15b
lea r8, [ r15 + r8 ]
mov r15, [ rsp + 0x148 ]
lea r8, [r15+r8]
movzx r9, r9b
lea r8, [ r9 + r8 ]
mov r9, [ rsp + 0x168 ]
lea r8, [r9+r8]
movzx r12, r12b
lea r8, [ r12 + r8 ]
mov r12, [ rsp + 0x138 ]
lea r8, [r12+r8]
movzx r14, r14b
lea r8, [ r14 + r8 ]
mov r14, [ rsp + 0x158 ]
lea r8, [r14+r8]
movzx rcx, cl
lea r8, [ rcx + r8 ]
mov rcx, [ rsp + 0x128 ]
lea r8, [rcx+r8]
movzx r11, r11b
lea r8, [ r11 + r8 ]
mov r11, [ rsp + 0x118 ]
lea r8, [r11+r8]
movzx r15, byte [ rsp + 0x188 ]; load byte memx408 to register64
lea r8, [ r15 + r8 ]
mov r15, [ rsp + 0x108 ]
lea r8, [r15+r8]
movzx r9, byte [ rsp + 0x180 ]; load byte memx412 to register64
lea r8, [ r9 + r8 ]
mov r9, [ rsp + 0xf8 ]
lea r8, [r9+r8]
movzx r12, byte [ rsp + 0x1b0 ]; load byte memx416 to register64
lea r8, [ r12 + r8 ]
mov r12, [ rsp + 0xe8 ]
lea r8, [r12+r8]
movzx r14, byte [ rsp + 0x190 ]; load byte memx420 to register64
lea r8, [ r14 + r8 ]
mov r14, [ rsp + 0xd8 ]
lea r8, [r14+r8]
movzx rcx, byte [ rsp + 0x1b8 ]; load byte memx424 to register64
lea r8, [ rcx + r8 ]
mov rcx, [ rsp + 0xd0 ]
lea r8, [rcx+r8]
movzx r11, byte [ rsp + 0x198 ]; load byte memx428 to register64
lea r8, [ r11 + r8 ]
mov r11, [ rsp + 0xc8 ]
lea r8, [r11+r8]
movzx r15, byte [ rsp + 0x1a0 ]; load byte memx432 to register64
lea r8, [ r15 + r8 ]
mov r15, [ rsp + 0xc0 ]
lea r8, [r15+r8]
movzx r9, byte [ rsp + 0x1a8 ]; load byte memx436 to register64
lea r8, [ r9 + r8 ]
mov r9, [ rsp + 0xb8 ]
lea r8, [r9+r8]
adcx r8, [ rsp + 0xb0 ]
movzx r12, byte [ rsp + 0x1c0 ]; load byte memx444 to register64
lea r8, [ r12 + r8 ]
mov r12, [ rsp + 0xa8 ]
lea r8, [r12+r8]
movzx rdi, dil
lea r8, [ rdi + r8 ]
mov rdi, [ rsp + 0xa0 ]
lea r8, [rdi+r8]
mov r14, 0x0 ; moving imm to reg
adox r8, r14
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx rcx, r11, [ rsi + 0x0 ]; x196, x195<- arg1[0] * arg2[0]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r15, r9, [ rax + 0x38 ]; x80, x79<- arg1[1] * arg2[7]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r12, rdi, [ rax + 0x30 ]; x78, x77<- arg1[2] * arg2[6]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r14, rbp, [ rax + 0x28 ]; x74, x73<- arg1[3] * arg2[5]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x1c8 ], rbx; spilling x267 to mem
mov [ rsp + 0x1d0 ], r8; spilling x561 to mem
mulx rbx, r8, [ rsi + 0x20 ]; x68, x67<- arg1[4] * arg2[4]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x1d8 ], r13; spilling x559 to mem
mov [ rsp + 0x1e0 ], rcx; spilling x196 to mem
mulx r13, rcx, [ rsi + 0x28 ]; x60, x59<- arg1[5] * arg2[3]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x1e8 ], r15; spilling x80 to mem
mov [ rsp + 0x1f0 ], r12; spilling x78 to mem
mulx r15, r12, [ rax + 0x10 ]; x50, x49<- arg1[6] * arg2[2]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x1f8 ], r14; spilling x74 to mem
mov [ rsp + 0x200 ], rbx; spilling x68 to mem
mulx r14, rbx, [ rsi + 0x28 ]; x12, x11<- arg1[5] * arg2[7]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x208 ], r13; spilling x60 to mem
mov [ rsp + 0x210 ], r15; spilling x50 to mem
mulx r13, r15, [ rax + 0x8 ]; x38, x37<- arg1[7] * arg2[1]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x218 ], r13; spilling x38 to mem
mov [ rsp + 0x220 ], r14; spilling x12 to mem
mulx r13, r14, [ rsi + 0x30 ]; x10, x9<- arg1[6] * arg2[6]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x228 ], r13; spilling x10 to mem
mov [ rsp + 0x230 ], r11; spilling x195 to mem
mulx r13, r11, [ rax + 0x28 ]; x6, x5<- arg1[7] * arg2[5]
add r11, r14; could be done better, if r0 has been u8 as well
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, rbx
setc bl; spill CF x520 to reg (rbx)
clc;
adcx r11, r15
seto r15b; spill OF x524 to reg (r15)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r11, r12
setc r12b; spill CF x528 to reg (r12)
clc;
adcx r11, rcx
seto cl; spill OF x532 to reg (rcx)
mov byte [ rsp + 0x238 ], r12b; spilling byte x528 to mem
mov r12, -0x3 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r11, r8
seto r8b; spill OF x540 to reg (r8)
mov r12, -0x3 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r11, rbp
setc bpl; spill CF x536 to reg (rbp)
clc;
adcx r11, rdi
seto dil; spill OF x544 to reg (rdi)
mov r12, -0x3 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r11, r9
setc r9b; spill CF x548 to reg (r9)
clc;
adcx r11, [ rsp + 0x230 ]
setc r12b; spill CF x556 to reg (r12)
clc;
adcx r11, [ rsp + 0x70 ]
movzx rbx, bl
lea r13, [ rbx + r13 ]
mov rbx, [ rsp + 0x228 ]
lea r13, [rbx+r13]
movzx r15, r15b
lea r13, [ r15 + r13 ]
mov r15, [ rsp + 0x220 ]
lea r13, [r15+r13]
movzx rbx, byte [ rsp + 0x238 ]; load byte memx528 to register64
lea r13, [ rbx + r13 ]
mov rbx, [ rsp + 0x218 ]
lea r13, [rbx+r13]
movzx rcx, cl
lea r13, [ rcx + r13 ]
mov rcx, [ rsp + 0x210 ]
lea r13, [rcx+r13]
movzx rbp, bpl
lea r13, [ rbp + r13 ]
mov rbp, [ rsp + 0x208 ]
lea r13, [rbp+r13]
movzx r8, r8b
lea r13, [ r8 + r13 ]
mov r8, [ rsp + 0x200 ]
lea r13, [r8+r13]
movzx rdi, dil
lea r13, [ rdi + r13 ]
mov rdi, [ rsp + 0x1f8 ]
lea r13, [rdi+r13]
movzx r9, r9b
lea r13, [ r9 + r13 ]
mov r9, [ rsp + 0x1f0 ]
lea r13, [r9+r13]
adox r13, [ rsp + 0x1e8 ]
movzx r12, r12b
lea r13, [ r12 + r13 ]
mov r12, [ rsp + 0x1e0 ]
lea r13, [r12+r13]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx r15, rbx, [ rsi + 0x0 ]; x194, x193<- arg1[0] * arg2[1]
adc r13, 0x0
mov rcx, r11; x575, copying x569 here, cause x569 is needed in a reg for other than x575, namely all: , x576, x575, size: 2
shrd rcx, r13, 56; x575 <- x571||x569 >> 56
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx rbp, r8, [ rsi + 0x8 ]; x180, x179<- arg1[1] * arg2[0]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mulx rdi, r9, [ rsi + 0x10 ]; x76, x75<- arg1[2] * arg2[7]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mulx r12, r13, [ rsi + 0x20 ]; x66, x65<- arg1[4] * arg2[5]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x240 ], r15; spilling x194 to mem
mulx r14, r15, [ rax + 0x30 ]; x72, x71<- arg1[3] * arg2[6]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x248 ], rbp; spilling x180 to mem
mov [ rsp + 0x250 ], rdi; spilling x76 to mem
mulx rbp, rdi, [ rsi + 0x38 ]; x36, x35<- arg1[7] * arg2[2]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x258 ], r14; spilling x72 to mem
mov [ rsp + 0x260 ], r12; spilling x66 to mem
mulx r14, r12, [ rax + 0x20 ]; x58, x57<- arg1[5] * arg2[4]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x268 ], r14; spilling x58 to mem
mov [ rsp + 0x270 ], rbp; spilling x36 to mem
mulx r14, rbp, [ rsi + 0x30 ]; x8, x7<- arg1[6] * arg2[7]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x278 ], r14; spilling x8 to mem
mov [ rsp + 0x280 ], rcx; spilling x575 to mem
mulx r14, rcx, [ rax + 0x18 ]; x48, x47<- arg1[6] * arg2[3]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x288 ], r14; spilling x48 to mem
mov [ rsp + 0x290 ], rbx; spilling x193 to mem
mulx r14, rbx, [ rsi + 0x38 ]; x4, x3<- arg1[7] * arg2[6]
add rbx, rbp; could be done better, if r0 has been u8 as well
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, rdi
setc dil; spill CF x484 to reg (rdi)
clc;
adcx rbx, rcx
setc cl; spill CF x492 to reg (rcx)
clc;
adcx rbx, r12
seto r12b; spill OF x488 to reg (r12)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rbx, r13
seto r13b; spill OF x500 to reg (r13)
mov byte [ rsp + 0x298 ], cl; spilling byte x492 to mem
mov rcx, -0x3 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbx, r15
seto r15b; spill OF x504 to reg (r15)
mov rcx, -0x3 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbx, r9
seto r9b; spill OF x508 to reg (r9)
mov rcx, -0x3 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbx, r8
setc r8b; spill CF x496 to reg (r8)
clc;
adcx rbx, [ rsp + 0x290 ]
setc cl; spill CF x516 to reg (rcx)
clc;
adcx rbx, [ rsp + 0x280 ]
movzx rdi, dil
lea r14, [ rdi + r14 ]
mov rdi, [ rsp + 0x278 ]
lea r14, [rdi+r14]
movzx r12, r12b
lea r14, [ r12 + r14 ]
mov r12, [ rsp + 0x270 ]
lea r14, [r12+r14]
movzx rdi, byte [ rsp + 0x298 ]; load byte memx492 to register64
lea r14, [ rdi + r14 ]
mov rdi, [ rsp + 0x288 ]
lea r14, [rdi+r14]
movzx r8, r8b
lea r14, [ r8 + r14 ]
mov r8, [ rsp + 0x268 ]
lea r14, [r8+r14]
movzx r13, r13b
lea r14, [ r13 + r14 ]
mov r13, [ rsp + 0x260 ]
lea r14, [r13+r14]
movzx r15, r15b
lea r14, [ r15 + r14 ]
mov r15, [ rsp + 0x258 ]
lea r14, [r15+r14]
movzx r9, r9b
lea r14, [ r9 + r14 ]
mov r9, [ rsp + 0x250 ]
lea r14, [r9+r14]
adox r14, [ rsp + 0x248 ]
movzx rcx, cl
lea r14, [ rcx + r14 ]
mov rcx, [ rsp + 0x240 ]
lea r14, [rcx+r14]
adc r14, 0x0
mov r12, [ rsp + 0x1d8 ]; load m64 x559 to register64
add r12, [ rsp + 0x70 ]; could be done better, if r0 has been u8 as well
mov rdi, 0xffffffffffffff ; moving imm to reg
setc r8b; spill CF x565 to reg (r8)
mov r13, r12; x568, copying x564 here, cause x564 is needed in a reg for other than x568, namely all: , x568, x567, size: 2
and r13, rdi; x568 <- x564&0xffffffffffffff
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r15, r9, [ rax + 0x28 ]; x186, x185<- arg1[0] * arg2[5]
movzx rcx, r8b; x566, copying x565 here, cause x565 is needed in a reg for other than x566, namely all: , x566, size: 1
add rcx, [ rsp + 0x1d0 ]
shrd r12, rcx, 56; x567 <- x566||x564 >> 56
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mulx r8, rcx, [ rsi + 0x10 ]; x160, x159<- arg1[2] * arg2[3]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbp, rdi, [ rax + 0x20 ]; x172, x171<- arg1[1] * arg2[4]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x2a0 ], r13; spilling x568 to mem
mov [ rsp + 0x2a8 ], r14; spilling x579 to mem
mulx r13, r14, [ rsi + 0x18 ]; x150, x149<- arg1[3] * arg2[2]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x2b0 ], rbx; spilling x577 to mem
mov [ rsp + 0x2b8 ], r15; spilling x186 to mem
mulx rbx, r15, [ rsi + 0x20 ]; x142, x141<- arg1[4] * arg2[1]
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x2c0 ], rbp; spilling x172 to mem
mov [ rsp + 0x2c8 ], r8; spilling x160 to mem
mulx rbp, r8, [ rsi + 0x28 ]; x136, x135<- arg1[5] * arg2[0]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x2d0 ], r13; spilling x150 to mem
mov [ rsp + 0x2d8 ], rbx; spilling x142 to mem
mulx r13, rbx, [ rax + 0x38 ]; x120, x119<- arg1[2] * arg2[7]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x2e0 ], rbp; spilling x136 to mem
mov [ rsp + 0x2e8 ], r13; spilling x120 to mem
mulx rbp, r13, [ rax + 0x30 ]; x116, x115<- arg1[3] * arg2[6]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x2f0 ], rbp; spilling x116 to mem
mov [ rsp + 0x2f8 ], r12; spilling x567 to mem
mulx rbp, r12, [ rsi + 0x30 ]; x94, x93<- arg1[6] * arg2[3]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x300 ], rbp; spilling x94 to mem
mov [ rsp + 0x308 ], r9; spilling x185 to mem
mulx rbp, r9, [ rsi + 0x20 ]; x110, x109<- arg1[4] * arg2[5]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x310 ], rbp; spilling x110 to mem
mov [ rsp + 0x318 ], rdi; spilling x171 to mem
mulx rbp, rdi, [ rsi + 0x28 ]; x102, x101<- arg1[5] * arg2[4]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x320 ], rbp; spilling x102 to mem
mov [ rsp + 0x328 ], rcx; spilling x159 to mem
mulx rbp, rcx, [ rax + 0x38 ]; x40, x39<- arg1[6] * arg2[7]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x330 ], r10; spilling x221 to mem
mov [ rsp + 0x338 ], rbp; spilling x40 to mem
mulx r10, rbp, [ rsi + 0x38 ]; x86, x85<- arg1[7] * arg2[2]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x340 ], r10; spilling x86 to mem
mov [ rsp + 0x348 ], r14; spilling x149 to mem
mulx r10, r14, [ rsi + 0x38 ]; x28, x27<- arg1[7] * arg2[6]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x350 ], r10; spilling x28 to mem
mov [ rsp + 0x358 ], r15; spilling x141 to mem
mulx r10, r15, [ rax + 0x38 ]; x20, x19<- arg1[6] * arg2[7]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x360 ], r10; spilling x20 to mem
mov [ rsp + 0x368 ], r8; spilling x135 to mem
mulx r10, r8, [ rax + 0x30 ]; x16, x15<- arg1[7] * arg2[6]
test al, al
adox r8, r15
adcx r8, r14
seto r14b; spill OF x324 to reg (r14)
mov r15, -0x2 ; moving imm to reg
inc r15; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, rcx
setc cl; spill CF x328 to reg (rcx)
clc;
adcx r8, rbp
setc bpl; spill CF x336 to reg (rbp)
clc;
adcx r8, r12
seto r12b; spill OF x332 to reg (r12)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r8, rdi
seto dil; spill OF x344 to reg (rdi)
mov byte [ rsp + 0x370 ], bpl; spilling byte x336 to mem
mov rbp, -0x3 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r8, r9
setc r9b; spill CF x340 to reg (r9)
clc;
adcx r8, r13
setc r13b; spill CF x352 to reg (r13)
clc;
adcx r8, rbx
seto bl; spill OF x348 to reg (rbx)
mov rbp, -0x3 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r8, [ rsp + 0x368 ]
setc bpl; spill CF x356 to reg (rbp)
clc;
adcx r8, [ rsp + 0x358 ]
mov byte [ rsp + 0x378 ], bpl; spilling byte x356 to mem
seto bpl; spill OF x360 to reg (rbp)
mov byte [ rsp + 0x380 ], r13b; spilling byte x352 to mem
mov r13, -0x3 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r8, [ rsp + 0x348 ]
setc r13b; spill CF x364 to reg (r13)
clc;
adcx r8, [ rsp + 0x328 ]
mov byte [ rsp + 0x388 ], r13b; spilling byte x364 to mem
seto r13b; spill OF x368 to reg (r13)
mov byte [ rsp + 0x390 ], bpl; spilling byte x360 to mem
mov rbp, -0x3 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r8, [ rsp + 0x318 ]
movzx r14, r14b
lea r10, [ r14 + r10 ]
mov r14, [ rsp + 0x360 ]
lea r10, [r14+r10]
seto r14b; spill OF x376 to reg (r14)
mov rbp, -0x3 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r8, [ rsp + 0x308 ]
seto bpl; spill OF x380 to reg (rbp)
mov byte [ rsp + 0x398 ], r14b; spilling byte x376 to mem
mov r14, -0x3 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r8, [ rsp + 0x2f8 ]
movzx rcx, cl
lea r10, [ rcx + r10 ]
mov rcx, [ rsp + 0x350 ]
lea r10, [rcx+r10]
movzx r12, r12b
lea r10, [ r12 + r10 ]
mov r12, [ rsp + 0x338 ]
lea r10, [r12+r10]
movzx rcx, byte [ rsp + 0x370 ]; load byte memx336 to register64
lea r10, [ rcx + r10 ]
mov rcx, [ rsp + 0x340 ]
lea r10, [rcx+r10]
movzx r9, r9b
lea r10, [ r9 + r10 ]
mov r9, [ rsp + 0x300 ]
lea r10, [r9+r10]
movzx rdi, dil
lea r10, [ rdi + r10 ]
mov rdi, [ rsp + 0x320 ]
lea r10, [rdi+r10]
movzx rbx, bl
lea r10, [ rbx + r10 ]
mov rbx, [ rsp + 0x310 ]
lea r10, [rbx+r10]
movzx r12, byte [ rsp + 0x380 ]; load byte memx352 to register64
lea r10, [ r12 + r10 ]
mov r12, [ rsp + 0x2f0 ]
lea r10, [r12+r10]
movzx rcx, byte [ rsp + 0x378 ]; load byte memx356 to register64
lea r10, [ rcx + r10 ]
mov rcx, [ rsp + 0x2e8 ]
lea r10, [rcx+r10]
movzx r9, byte [ rsp + 0x390 ]; load byte memx360 to register64
lea r10, [ r9 + r10 ]
mov r9, [ rsp + 0x2e0 ]
lea r10, [r9+r10]
movzx rdi, byte [ rsp + 0x388 ]; load byte memx364 to register64
lea r10, [ rdi + r10 ]
mov rdi, [ rsp + 0x2d8 ]
lea r10, [rdi+r10]
movzx r13, r13b
lea r10, [ r13 + r10 ]
mov r13, [ rsp + 0x2d0 ]
lea r10, [r13+r10]
adcx r10, [ rsp + 0x2c8 ]
movzx rbx, byte [ rsp + 0x398 ]; load byte memx376 to register64
lea r10, [ rbx + r10 ]
mov rbx, [ rsp + 0x2c0 ]
lea r10, [rbx+r10]
movzx rbp, bpl
lea r10, [ rbp + r10 ]
mov rbp, [ rsp + 0x2b8 ]
lea r10, [rbp+r10]
adox r10, r15
mov r12, r8; x580, copying x572 here, cause x572 is needed in a reg for other than x580, namely all: , x580, x581, size: 2
shrd r12, r10, 56; x580 <- x574||x572 >> 56
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rcx, r9, [ rax + 0x30 ]; x184, x183<- arg1[0] * arg2[6]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rdi, r13, [ rax + 0x28 ]; x170, x169<- arg1[1] * arg2[5]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rbx, rbp, [ rax + 0x18 ]; x148, x147<- arg1[3] * arg2[3]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx r10, r15, [ rsi + 0x10 ]; x158, x157<- arg1[2] * arg2[4]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x3a0 ], rcx; spilling x184 to mem
mulx r14, rcx, [ rax + 0x8 ]; x134, x133<- arg1[5] * arg2[1]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x3a8 ], rdi; spilling x170 to mem
mov [ rsp + 0x3b0 ], r10; spilling x158 to mem
mulx rdi, r10, [ rax + 0x10 ]; x140, x139<- arg1[4] * arg2[2]
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x3b8 ], rbx; spilling x148 to mem
mov [ rsp + 0x3c0 ], rdi; spilling x140 to mem
mulx rbx, rdi, [ rsi + 0x30 ]; x130, x129<- arg1[6] * arg2[0]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x3c8 ], r14; spilling x134 to mem
mov [ rsp + 0x3d0 ], rbx; spilling x130 to mem
mulx r14, rbx, [ rax + 0x30 ]; x108, x107<- arg1[4] * arg2[6]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x3d8 ], r14; spilling x108 to mem
mov [ rsp + 0x3e0 ], r12; spilling x580 to mem
mulx r14, r12, [ rsi + 0x18 ]; x114, x113<- arg1[3] * arg2[7]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x3e8 ], r14; spilling x114 to mem
mov [ rsp + 0x3f0 ], r9; spilling x183 to mem
mulx r14, r9, [ rax + 0x20 ]; x92, x91<- arg1[6] * arg2[4]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x3f8 ], r14; spilling x92 to mem
mov [ rsp + 0x400 ], r13; spilling x169 to mem
mulx r14, r13, [ rax + 0x28 ]; x100, x99<- arg1[5] * arg2[5]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x408 ], r14; spilling x100 to mem
mov [ rsp + 0x410 ], r15; spilling x157 to mem
mulx r14, r15, [ rax + 0x18 ]; x84, x83<- arg1[7] * arg2[3]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x418 ], r14; spilling x84 to mem
mov [ rsp + 0x420 ], rbp; spilling x147 to mem
mulx r14, rbp, [ rax + 0x38 ]; x14, x13<- arg1[7] * arg2[7]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x428 ], r14; spilling x14 to mem
mov [ rsp + 0x430 ], r10; spilling x139 to mem
mulx r14, r10, [ rsi + 0x38 ]; x26, x25<- arg1[7] * arg2[7]
add rbp, r10; could be done better, if r0 has been u8 as well
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, r15
setc r15b; spill CF x272 to reg (r15)
clc;
adcx rbp, r9
seto r9b; spill OF x276 to reg (r9)
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rbp, r13
seto r13b; spill OF x284 to reg (r13)
mov byte [ rsp + 0x438 ], r9b; spilling byte x276 to mem
mov r9, -0x3 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbp, rbx
seto bl; spill OF x288 to reg (rbx)
mov r9, -0x3 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbp, r12
setc r12b; spill CF x280 to reg (r12)
clc;
adcx rbp, rdi
setc dil; spill CF x296 to reg (rdi)
clc;
adcx rbp, rcx
setc cl; spill CF x300 to reg (rcx)
clc;
adcx rbp, [ rsp + 0x430 ]
setc r9b; spill CF x304 to reg (r9)
clc;
adcx rbp, [ rsp + 0x420 ]
mov byte [ rsp + 0x440 ], r9b; spilling byte x304 to mem
seto r9b; spill OF x292 to reg (r9)
mov byte [ rsp + 0x448 ], cl; spilling byte x300 to mem
mov rcx, -0x3 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbp, [ rsp + 0x410 ]
seto cl; spill OF x312 to reg (rcx)
mov byte [ rsp + 0x450 ], dil; spilling byte x296 to mem
mov rdi, -0x3 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbp, [ rsp + 0x400 ]
setc dil; spill CF x308 to reg (rdi)
clc;
adcx rbp, [ rsp + 0x3f0 ]
mov byte [ rsp + 0x458 ], cl; spilling byte x312 to mem
setc cl; spill CF x320 to reg (rcx)
clc;
adcx rbp, [ rsp + 0x3e0 ]
movzx r15, r15b
lea r14, [ r15 + r14 ]
mov r15, [ rsp + 0x428 ]
lea r14, [r15+r14]
movzx r15, byte [ rsp + 0x438 ]; load byte memx276 to register64
lea r14, [ r15 + r14 ]
mov r15, [ rsp + 0x418 ]
lea r14, [r15+r14]
movzx r12, r12b
lea r14, [ r12 + r14 ]
mov r12, [ rsp + 0x3f8 ]
lea r14, [r12+r14]
movzx r13, r13b
lea r14, [ r13 + r14 ]
mov r13, [ rsp + 0x408 ]
lea r14, [r13+r14]
movzx rbx, bl
lea r14, [ rbx + r14 ]
mov rbx, [ rsp + 0x3d8 ]
lea r14, [rbx+r14]
movzx r9, r9b
lea r14, [ r9 + r14 ]
mov r9, [ rsp + 0x3e8 ]
lea r14, [r9+r14]
movzx r15, byte [ rsp + 0x450 ]; load byte memx296 to register64
lea r14, [ r15 + r14 ]
mov r15, [ rsp + 0x3d0 ]
lea r14, [r15+r14]
movzx r12, byte [ rsp + 0x448 ]; load byte memx300 to register64
lea r14, [ r12 + r14 ]
mov r12, [ rsp + 0x3c8 ]
lea r14, [r12+r14]
movzx r13, byte [ rsp + 0x440 ]; load byte memx304 to register64
lea r14, [ r13 + r14 ]
mov r13, [ rsp + 0x3c0 ]
lea r14, [r13+r14]
movzx rdi, dil
lea r14, [ rdi + r14 ]
mov rdi, [ rsp + 0x3b8 ]
lea r14, [rdi+r14]
movzx rbx, byte [ rsp + 0x458 ]; load byte memx312 to register64
lea r14, [ rbx + r14 ]
mov rbx, [ rsp + 0x3b0 ]
lea r14, [rbx+r14]
adox r14, [ rsp + 0x3a8 ]
movzx rcx, cl
lea r14, [ rcx + r14 ]
mov rcx, [ rsp + 0x3a0 ]
lea r14, [rcx+r14]
adc r14, 0x0
mov r9, [ rsp + 0x2b0 ]; load m64 x577 to register64
mov r15, [ rsp + 0x2a8 ]; load m64 x579 to register64
mov r12, r9; x585, copying x577 here, cause x577 is needed in a reg for other than x585, namely all: , x585, x586, size: 2
shrd r12, r15, 56; x585 <- x579||x577 >> 56
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx r15, r13, [ rsi + 0x0 ]; x192, x191<- arg1[0] * arg2[2]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx rdi, rbx, [ rsi + 0x8 ]; x178, x177<- arg1[1] * arg2[1]
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx rcx, r10, [ rsi + 0x10 ]; x166, x165<- arg1[2] * arg2[0]
mov [ rsp + 0x460 ], r15; spilling x192 to mem
mov r15, rbp; x590, copying x582 here, cause x582 is needed in a reg for other than x590, namely all: , x590, x591, size: 2
shrd r15, r14, 56; x590 <- x584||x582 >> 56
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x468 ], r15; spilling x590 to mem
mulx r14, r15, [ rax + 0x30 ]; x64, x63<- arg1[4] * arg2[6]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x470 ], rdi; spilling x178 to mem
mov [ rsp + 0x478 ], rcx; spilling x166 to mem
mulx rdi, rcx, [ rax + 0x38 ]; x70, x69<- arg1[3] * arg2[7]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x480 ], rdi; spilling x70 to mem
mov [ rsp + 0x488 ], r14; spilling x64 to mem
mulx rdi, r14, [ rsi + 0x38 ]; x34, x33<- arg1[7] * arg2[3]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x490 ], rdi; spilling x34 to mem
mov [ rsp + 0x498 ], r12; spilling x585 to mem
mulx rdi, r12, [ rsi + 0x28 ]; x56, x55<- arg1[5] * arg2[5]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x4a0 ], rdi; spilling x56 to mem
mov [ rsp + 0x4a8 ], r13; spilling x191 to mem
mulx rdi, r13, [ rax + 0x20 ]; x46, x45<- arg1[6] * arg2[4]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x4b0 ], rdi; spilling x46 to mem
mov [ rsp + 0x4b8 ], rbx; spilling x177 to mem
mulx rdi, rbx, [ rsi + 0x38 ]; x2, x1<- arg1[7] * arg2[7]
test al, al
adox rbx, r14
adcx rbx, r13
setc r14b; spill CF x456 to reg (r14)
clc;
adcx rbx, r12
seto r12b; spill OF x452 to reg (r12)
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, r15
seto r15b; spill OF x464 to reg (r15)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rbx, rcx
setc cl; spill CF x460 to reg (rcx)
clc;
adcx rbx, r10
setc r10b; spill CF x472 to reg (r10)
clc;
adcx rbx, [ rsp + 0x4b8 ]
mov byte [ rsp + 0x4c0 ], r10b; spilling byte x472 to mem
seto r10b; spill OF x468 to reg (r10)
mov byte [ rsp + 0x4c8 ], r15b; spilling byte x464 to mem
mov r15, -0x3 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbx, [ rsp + 0x4a8 ]
seto r15b; spill OF x480 to reg (r15)
mov byte [ rsp + 0x4d0 ], r10b; spilling byte x468 to mem
mov r10, -0x3 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbx, [ rsp + 0x498 ]
movzx r12, r12b
lea rdi, [ r12 + rdi ]
mov r12, [ rsp + 0x490 ]
lea rdi, [r12+rdi]
movzx r14, r14b
lea rdi, [ r14 + rdi ]
mov r14, [ rsp + 0x4b0 ]
lea rdi, [r14+rdi]
movzx rcx, cl
lea rdi, [ rcx + rdi ]
mov rcx, [ rsp + 0x4a0 ]
lea rdi, [rcx+rdi]
movzx r12, byte [ rsp + 0x4c8 ]; load byte memx464 to register64
lea rdi, [ r12 + rdi ]
mov r12, [ rsp + 0x488 ]
lea rdi, [r12+rdi]
movzx r14, byte [ rsp + 0x4d0 ]; load byte memx468 to register64
lea rdi, [ r14 + rdi ]
mov r14, [ rsp + 0x480 ]
lea rdi, [r14+rdi]
movzx rcx, byte [ rsp + 0x4c0 ]; load byte memx472 to register64
lea rdi, [ rcx + rdi ]
mov rcx, [ rsp + 0x478 ]
lea rdi, [rcx+rdi]
adcx rdi, [ rsp + 0x470 ]
movzx r15, r15b
lea rdi, [ r15 + rdi ]
mov r15, [ rsp + 0x460 ]
lea rdi, [r15+rdi]
adox rdi, r13
mov r12, 0xffffffffffffff ; moving imm to reg
mov r14, [ rsp + 0x330 ]; x226, copying x221 here, cause x221 is needed in a reg for other than x226, namely all: , x226, size: 1
and r14, r12; x226 <- x221&0xffffffffffffff
mov rcx, rbx; x593, copying x587 here, cause x587 is needed in a reg for other than x593, namely all: , x593, x594, size: 2
shrd rcx, rdi, 56; x593 <- x589||x587 >> 56
and r11, r12; x576 <- x569&0xffffffffffffff
lea rcx, [ rcx + r14 ]
mov r15, rcx; x599, copying x595 here, cause x595 is needed in a reg for other than x599, namely all: , x598, x599, size: 2
and r15, r12; x599 <- x595&0xffffffffffffff
mov rdi, [ rsp + 0x1c8 ]; x563, copying x267 here, cause x267 is needed in a reg for other than x563, namely all: , x563, size: 1
and rdi, r12; x563 <- x267&0xffffffffffffff
shr rcx, 56; x598 <- x595>> 56
mov r14, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r14 + 0x18 ], r15; out1[3] = x599
add rdi, [ rsp + 0x468 ]
mov r15, rdi; x596, copying x592 here, cause x592 is needed in a reg for other than x596, namely all: , x596, x597, size: 2
shr r15, 56; x596 <- x592>> 56
mov r13, r15; x600, copying x596 here, cause x596 is needed in a reg for other than x600, namely all: , x600, x601, size: 2
add r13, [ rsp + 0x2a0 ]
lea rcx, [ rcx + r13 ]
mov r13, rcx; x603, copying x602 here, cause x602 is needed in a reg for other than x603, namely all: , x603, x604, size: 2
shr r13, 56; x603 <- x602>> 56
and rbp, r12; x591 <- x582&0xffffffffffffff
lea r11, [ r11 + r15 ]
mov [ r14 + 0x30 ], rbp; out1[6] = x591
mov r15, r11; x607, copying x601 here, cause x601 is needed in a reg for other than x607, namely all: , x606, x607, size: 2
and r15, r12; x607 <- x601&0xffffffffffffff
mov [ r14 + 0x0 ], r15; out1[0] = x607
shr r11, 56; x606 <- x601>> 56
and r8, r12; x581 <- x572&0xffffffffffffff
lea r13, [ r13 + r8 ]
and r9, r12; x586 <- x577&0xffffffffffffff
mov [ r14 + 0x28 ], r13; out1[5] = x605
lea r11, [ r11 + r9 ]
and rcx, r12; x604 <- x602&0xffffffffffffff
mov [ r14 + 0x20 ], rcx; out1[4] = x604
mov [ r14 + 0x8 ], r11; out1[1] = x608
and rdi, r12; x597 <- x592&0xffffffffffffff
and rbx, r12; x594 <- x587&0xffffffffffffff
mov [ r14 + 0x38 ], rdi; out1[7] = x597
mov [ r14 + 0x10 ], rbx; out1[2] = x594
mov rbx, [ rsp + 0x4d8 ]; restoring from stack
mov rbp, [ rsp + 0x4e0 ]; restoring from stack
mov r12, [ rsp + 0x4e8 ]; restoring from stack
mov r13, [ rsp + 0x4f0 ]; restoring from stack
mov r14, [ rsp + 0x4f8 ]; restoring from stack
mov r15, [ rsp + 0x500 ]; restoring from stack
add rsp, 0x508 
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; clocked at 1600 MHz
; first cyclecount 183.31, best 177.85955056179776, lastGood 178.6627906976744
; seed 42736280487937 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 60669 ms / 500 runs=> 121.338ms/run
; Time spent for assembling and measureing (initial batch_size=89, initial num_batches=101): 3490 ms
; Ratio (time for assembling + measure)/(total runtime for 500runs): 0.05752526001747185
; number reverted permutation/ tried permutation: 173 / 244 =70.902%
; number reverted decision/ tried decision: 150 / 257 =58.366%