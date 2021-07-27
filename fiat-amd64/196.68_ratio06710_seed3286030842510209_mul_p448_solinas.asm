SECTION .text
	GLOBAL mul_p448_solinas
mul_p448_solinas:
sub rsp, 0x468 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x438 ], rbx; saving to stack
mov [ rsp + 0x440 ], rbp; saving to stack
mov [ rsp + 0x448 ], r12; saving to stack
mov [ rsp + 0x450 ], r13; saving to stack
mov [ rsp + 0x458 ], r14; saving to stack
mov [ rsp + 0x460 ], r15; saving to stack
mov rax, rdx; preserving value of arg2 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r10, r11, [ rax + 0x38 ]; x62, x61<- arg1[4] * arg2[7]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mulx rbx, rbp, [ rax + 0x28 ]; x44, x43<- arg1[6] * arg2[5]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mulx r12, r13, [ rsi + 0x0 ]; x190, x189<- arg1[0] * arg2[3]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx r14, r15, [ rsi + 0x38 ]; x32, x31<- arg1[7] * arg2[4]
add r15, rbp; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mulx rcx, r8, [ rax + 0x30 ]; x54, x53<- arg1[5] * arg2[6]
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, r8
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx rbp, r8, [ rsi + 0x18 ]; x154, x153<- arg1[3] * arg2[0]
seto r9b; spill OF x202 to reg (r9)
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, r11
adcx rbx, r14
movzx r9, r9b
lea rcx, [ rcx + rbx ]
lea rcx, [ rcx + r9 ]
clc;
adcx r15, r8
adox r10, rcx
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r11, r14, [ rax + 0x8 ]; x164, x163<- arg1[2] * arg2[1]
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r15, r14
adcx rbp, r10
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r9, r8, [ rax + 0x20 ]; x188, x187<- arg1[0] * arg2[4]
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx rbx, rcx, [ rsi + 0x20 ]; x144, x143<- arg1[4] * arg2[0]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mulx r10, r14, [ rsi + 0x38 ]; x30, x29<- arg1[7] * arg2[5]
adox r11, rbp
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx rbp, rdi, [ rsi + 0x8 ]; x176, x175<- arg1[1] * arg2[2]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x8 ], r9; spilling x188 to mem
mov [ rsp + 0x10 ], rbx; spilling x144 to mem
mulx r9, rbx, [ rsi + 0x18 ]; x118, x117<- arg1[3] * arg2[5]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x18 ], r9; spilling x118 to mem
mov [ rsp + 0x20 ], r10; spilling x30 to mem
mulx r9, r10, [ rsi + 0x10 ]; x122, x121<- arg1[2] * arg2[6]
test al, al
adox r15, rdi
adox rbp, r11
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r11, rdi, [ rax + 0x10 ]; x162, x161<- arg1[2] * arg2[2]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x28 ], r11; spilling x162 to mem
mov [ rsp + 0x30 ], r9; spilling x122 to mem
mulx r11, r9, [ rax + 0x8 ]; x152, x151<- arg1[3] * arg2[1]
adcx r15, r13
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x38 ], r11; spilling x152 to mem
mulx r13, r11, [ rax + 0x8 ]; x88, x87<- arg1[7] * arg2[1]
adcx r12, rbp
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x40 ], r13; spilling x88 to mem
mulx rbp, r13, [ rax + 0x30 ]; x22, x21<- arg1[6] * arg2[6]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x48 ], rbp; spilling x22 to mem
mov [ rsp + 0x50 ], r8; spilling x187 to mem
mulx rbp, r8, [ rsi + 0x20 ]; x112, x111<- arg1[4] * arg2[4]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x58 ], rbp; spilling x112 to mem
mov [ rsp + 0x60 ], rdi; spilling x161 to mem
mulx rbp, rdi, [ rsi + 0x8 ]; x124, x123<- arg1[1] * arg2[7]
mov [ rsp + 0x68 ], rbp; spilling x124 to mem
mov rbp, r15; x225, copying x221 here, cause x221 is needed in a reg for other than x225, namely all: , x226, x225, size: 2
shrd rbp, r12, 56; x225 <- x223||x221 >> 56
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x70 ], rbp; spilling x225 to mem
mulx r12, rbp, [ rsi + 0x38 ]; x18, x17<- arg1[7] * arg2[5]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x78 ], r12; spilling x18 to mem
mov [ rsp + 0x80 ], r9; spilling x151 to mem
mulx r12, r9, [ rax + 0x18 ]; x174, x173<- arg1[1] * arg2[3]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x88 ], r12; spilling x174 to mem
mov [ rsp + 0x90 ], r9; spilling x173 to mem
mulx r12, r9, [ rsi + 0x28 ]; x24, x23<- arg1[5] * arg2[7]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x98 ], r12; spilling x24 to mem
mov [ rsp + 0xa0 ], rcx; spilling x143 to mem
mulx r12, rcx, [ rax + 0x30 ]; x42, x41<- arg1[6] * arg2[6]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0xa8 ], r12; spilling x42 to mem
mov [ rsp + 0xb0 ], rdi; spilling x123 to mem
mulx r12, rdi, [ rsi + 0x28 ]; x52, x51<- arg1[5] * arg2[7]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0xb8 ], r12; spilling x52 to mem
mov [ rsp + 0xc0 ], r10; spilling x121 to mem
mulx r12, r10, [ rsi + 0x30 ]; x96, x95<- arg1[6] * arg2[2]
test al, al
adox rbp, r13
adcx rbp, r9
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mulx r13, r9, [ rax + 0x18 ]; x104, x103<- arg1[5] * arg2[3]
mov [ rsp + 0xc8 ], r13; spilling x104 to mem
setc r13b; spill CF x388 to reg (r13)
clc;
adcx rbp, r14
seto r14b; spill OF x384 to reg (r14)
mov [ rsp + 0xd0 ], r12; spilling x96 to mem
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, rcx
setc cl; spill CF x392 to reg (rcx)
clc;
adcx rbp, rdi
setc dil; spill CF x400 to reg (rdi)
clc;
adcx rbp, r11
setc r11b; spill CF x404 to reg (r11)
clc;
adcx rbp, r10
seto r10b; spill OF x396 to reg (r10)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rbp, r9
setc r9b; spill CF x408 to reg (r9)
clc;
adcx rbp, r8
seto r8b; spill OF x412 to reg (r8)
mov byte [ rsp + 0xd8 ], r9b; spilling byte x408 to mem
mov r9, -0x3 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbp, rbx
setc bl; spill CF x416 to reg (rbx)
clc;
adcx rbp, [ rsp + 0xc0 ]
setc r9b; spill CF x424 to reg (r9)
clc;
adcx rbp, [ rsp + 0xb0 ]
mov byte [ rsp + 0xe0 ], r9b; spilling byte x424 to mem
setc r9b; spill CF x428 to reg (r9)
clc;
adcx rbp, [ rsp + 0xa0 ]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov byte [ rsp + 0xe8 ], r9b; spilling byte x428 to mem
mulx r12, r9, [ rsi + 0x0 ]; x182, x181<- arg1[0] * arg2[7]
mov byte [ rsp + 0xf0 ], bl; spilling byte x416 to mem
seto bl; spill OF x420 to reg (rbx)
mov byte [ rsp + 0xf8 ], r8b; spilling byte x412 to mem
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, [ rsp + 0x80 ]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov byte [ rsp + 0x100 ], bl; spilling byte x420 to mem
mulx r8, rbx, [ rax + 0x18 ]; x138, x137<- arg1[4] * arg2[3]
mov [ rsp + 0x108 ], r12; spilling x182 to mem
setc r12b; spill CF x432 to reg (r12)
clc;
adcx rbp, [ rsp + 0x60 ]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov byte [ rsp + 0x110 ], r12b; spilling byte x432 to mem
mov byte [ rsp + 0x118 ], r11b; spilling byte x404 to mem
mulx r12, r11, [ rsi + 0x28 ]; x98, x97<- arg1[5] * arg2[6]
mov byte [ rsp + 0x120 ], dil; spilling byte x400 to mem
seto dil; spill OF x436 to reg (rdi)
mov byte [ rsp + 0x128 ], r10b; spilling byte x396 to mem
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, [ rsp + 0x90 ]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov byte [ rsp + 0x130 ], dil; spilling byte x436 to mem
mulx r10, rdi, [ rax + 0x20 ]; x82, x81<- arg1[7] * arg2[4]
mov byte [ rsp + 0x138 ], cl; spilling byte x392 to mem
setc cl; spill CF x440 to reg (rcx)
clc;
adcx rbp, [ rsp + 0x50 ]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov byte [ rsp + 0x140 ], cl; spilling byte x440 to mem
mov byte [ rsp + 0x148 ], r13b; spilling byte x388 to mem
mulx rcx, r13, [ rax + 0x28 ]; x156, x155<- arg1[2] * arg2[5]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x150 ], rcx; spilling x156 to mem
mov [ rsp + 0x158 ], r9; spilling x181 to mem
mulx rcx, r9, [ rax + 0x0 ]; x126, x125<- arg1[7] * arg2[0]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x160 ], r8; spilling x138 to mem
mov byte [ rsp + 0x168 ], r14b; spilling byte x384 to mem
mulx r8, r14, [ rax + 0x20 ]; x146, x145<- arg1[3] * arg2[4]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x170 ], r8; spilling x146 to mem
mov [ rsp + 0x178 ], rcx; spilling x126 to mem
mulx r8, rcx, [ rsi + 0x8 ]; x168, x167<- arg1[1] * arg2[6]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x180 ], r8; spilling x168 to mem
mov [ rsp + 0x188 ], rcx; spilling x167 to mem
mulx r8, rcx, [ rsi + 0x30 ]; x90, x89<- arg1[6] * arg2[5]
mov [ rsp + 0x190 ], r13; spilling x155 to mem
seto r13b; spill OF x444 to reg (r13)
mov [ rsp + 0x198 ], r14; spilling x145 to mem
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rdi, rcx
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mulx rcx, r14, [ rsi + 0x20 ]; x106, x105<- arg1[4] * arg2[7]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov byte [ rsp + 0x1a0 ], r13b; spilling byte x444 to mem
mov [ rsp + 0x1a8 ], rbx; spilling x137 to mem
mulx r13, rbx, [ rax + 0x8 ]; x128, x127<- arg1[6] * arg2[1]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x1b0 ], r13; spilling x128 to mem
mov [ rsp + 0x1b8 ], rcx; spilling x106 to mem
mulx r13, rcx, [ rax + 0x10 ]; x132, x131<- arg1[5] * arg2[2]
mov [ rsp + 0x1c0 ], r13; spilling x132 to mem
setc r13b; spill CF x448 to reg (r13)
clc;
adcx rbp, [ rsp + 0x70 ]
mov [ rsp + 0x1c8 ], rbp; spilling x559 to mem
setc bpl; spill CF x560 to reg (rbp)
clc;
adcx rdi, r11
adox r8, r10
adcx r12, r8
test al, al
adox rdi, r14
adcx rdi, r9
setc r11b; spill CF x240 to reg (r11)
clc;
adcx rdi, rbx
setc r10b; spill CF x244 to reg (r10)
clc;
adcx rdi, rcx
adox r12, [ rsp + 0x1b8 ]
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rdi, [ rsp + 0x1a8 ]
seto r14b; spill OF x252 to reg (r14)
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rdi, [ rsp + 0x198 ]
seto bl; spill OF x256 to reg (rbx)
mov rcx, -0x3 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rdi, [ rsp + 0x190 ]
movzx r11, r11b
lea r12, [ r11 + r12 ]
mov r11, [ rsp + 0x178 ]
lea r12, [r11+r12]
movzx r10, r10b
lea r12, [ r10 + r12 ]
mov r10, [ rsp + 0x1b0 ]
lea r12, [r10+r12]
seto r8b; spill OF x260 to reg (r8)
mov r11, -0x3 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug 7; load -3, increase it, discard the information #workaround). #last resort
adox rdi, [ rsp + 0x188 ]
adcx r12, [ rsp + 0x1c0 ]
mov r11, [ rsp + 0x78 ]; load m64 x18 to register64
movzx r10, byte [ rsp + 0x168 ]; load byte memx384 to register64
lea r11, [ r10 + r11 ]
mov r10, [ rsp + 0x48 ]
lea r11, [r10+r11]
movzx r14, r14b
lea r12, [ r14 + r12 ]
mov r14, [ rsp + 0x160 ]
lea r12, [r14+r12]
clc;
adcx rdi, [ rsp + 0x158 ]
movzx rbx, bl
lea r12, [ rbx + r12 ]
mov rbx, [ rsp + 0x170 ]
lea r12, [rbx+r12]
movzx r10, byte [ rsp + 0x148 ]; load byte memx388 to register64
lea r11, [ r10 + r11 ]
mov r10, [ rsp + 0x98 ]
lea r11, [r10+r11]
movzx r10, byte [ rsp + 0x138 ]; load byte memx392 to register64
lea r11, [ r10 + r11 ]
mov r10, [ rsp + 0x20 ]
lea r11, [r10+r11]
movzx r10, byte [ rsp + 0x128 ]; load byte memx396 to register64
lea r11, [ r10 + r11 ]
mov r10, [ rsp + 0xa8 ]
lea r11, [r10+r11]
movzx r8, r8b
lea r12, [ r8 + r12 ]
mov r8, [ rsp + 0x150 ]
lea r12, [r8+r12]
movzx r10, byte [ rsp + 0x120 ]; load byte memx400 to register64
lea r11, [ r10 + r11 ]
mov r10, [ rsp + 0xb8 ]
lea r11, [r10+r11]
movzx r10, byte [ rsp + 0x118 ]; load byte memx404 to register64
lea r11, [ r10 + r11 ]
mov r10, [ rsp + 0x40 ]
lea r11, [r10+r11]
movzx r10, byte [ rsp + 0xd8 ]; load byte memx408 to register64
lea r11, [ r10 + r11 ]
mov r10, [ rsp + 0xd0 ]
lea r11, [r10+r11]
adox r12, [ rsp + 0x180 ]
adcx r12, [ rsp + 0x108 ]
sar byte [ rsp + 0xf8 ], 1
adcx r11, [ rsp + 0xc8 ]
sar byte [ rsp + 0xf0 ], 1
adcx r11, [ rsp + 0x58 ]
mov r10, rdi; x562, copying x267 here, cause x267 is needed in a reg for other than x562, namely all: , x562, x563, size: 2
shrd r10, r12, 56; x562 <- x269||x267 >> 56
sar byte [ rsp + 0x100 ], 1
adcx r11, [ rsp + 0x18 ]
sar byte [ rsp + 0xe0 ], 1
adcx r11, [ rsp + 0x30 ]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r14, rbx, [ rax + 0x38 ]; x120, x119<- arg1[2] * arg2[7]
sar byte [ rsp + 0xe8 ], 1
adcx r11, [ rsp + 0x68 ]
sar byte [ rsp + 0x110 ], 1
adcx r11, [ rsp + 0x10 ]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx r8, r12, [ rsi + 0x28 ]; x102, x101<- arg1[5] * arg2[4]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx r9, rcx, [ rsi + 0x18 ]; x150, x149<- arg1[3] * arg2[2]
sar byte [ rsp + 0x130 ], 1
adcx r11, [ rsp + 0x38 ]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x1d0 ], r9; spilling x150 to mem
mov [ rsp + 0x1d8 ], r14; spilling x120 to mem
mulx r9, r14, [ rax + 0x18 ]; x160, x159<- arg1[2] * arg2[3]
sar byte [ rsp + 0x140 ], 1
adcx r11, [ rsp + 0x28 ]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x1e0 ], r9; spilling x160 to mem
mov [ rsp + 0x1e8 ], r8; spilling x102 to mem
mulx r9, r8, [ rsi + 0x0 ]; x186, x185<- arg1[0] * arg2[5]
sar byte [ rsp + 0x1a0 ], 1
adcx r11, [ rsp + 0x88 ]
sar  r13b, 1
adcx r11, [ rsp + 0x8 ]
mov r13, r10; x564, copying x562 here, cause x562 is needed in a reg for other than x564, namely all: , x564--x565, x569--x570, size: 2
adox r13, [ rsp + 0x1c8 ]
mov [ rsp + 0x1f0 ], r9; spilling x186 to mem
movzx r9, bpl; x561, copying x560 here, cause x560 is needed in a reg for other than x561, namely all: , x561, size: 1
lea r9, [ r9 + r11 ]
mov rbp, 0x0 ; moving imm to reg
adox r9, rbp
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx r11, rbp, [ rax + 0x30 ]; x16, x15<- arg1[7] * arg2[6]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x1f8 ], r15; spilling x221 to mem
mov [ rsp + 0x200 ], r8; spilling x185 to mem
mulx r15, r8, [ rsi + 0x30 ]; x20, x19<- arg1[6] * arg2[7]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x208 ], r14; spilling x159 to mem
mov [ rsp + 0x210 ], rcx; spilling x149 to mem
mulx r14, rcx, [ rax + 0x20 ]; x172, x171<- arg1[1] * arg2[4]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x218 ], r14; spilling x172 to mem
mov [ rsp + 0x220 ], rcx; spilling x171 to mem
mulx r14, rcx, [ rsi + 0x20 ]; x110, x109<- arg1[4] * arg2[5]
mov [ rsp + 0x228 ], r14; spilling x110 to mem
xor r14, r14
adox rbp, r8
adox r15, r11
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mulx r11, r8, [ rsi + 0x38 ]; x28, x27<- arg1[7] * arg2[6]
adcx rbp, r8
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mulx r8, r14, [ rax + 0x38 ]; x40, x39<- arg1[6] * arg2[7]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x230 ], r8; spilling x40 to mem
mov [ rsp + 0x238 ], r15; spilling x325 to mem
mulx r8, r15, [ rsi + 0x38 ]; x86, x85<- arg1[7] * arg2[2]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x240 ], r8; spilling x86 to mem
mov [ rsp + 0x248 ], r11; spilling x28 to mem
mulx r8, r11, [ rsi + 0x30 ]; x94, x93<- arg1[6] * arg2[3]
mov [ rsp + 0x250 ], r8; spilling x94 to mem
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, r14
setc r14b; spill CF x328 to reg (r14)
seto r8b; spill OF x332 to reg (r8)
mov [ rsp + 0x258 ], rbx; spilling x119 to mem
mov rbx, r13; x567, copying x564 here, cause x564 is needed in a reg for other than x567, namely all: , x567, x568, size: 2
shrd rbx, r9, 56; x567 <- x566||x564 >> 56
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x260 ], rbx; spilling x567 to mem
mulx r9, rbx, [ rax + 0x30 ]; x116, x115<- arg1[3] * arg2[6]
add rbp, r15; could be done better, if r0 has been u8 as well
mov r15, -0x2 ; moving imm to reg
inc r15; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, r11
setc r11b; spill CF x336 to reg (r11)
clc;
adcx rbp, r12
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r12, r15, [ rax + 0x8 ]; x142, x141<- arg1[4] * arg2[1]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x268 ], r12; spilling x142 to mem
mov [ rsp + 0x270 ], r9; spilling x116 to mem
mulx r12, r9, [ rax + 0x0 ]; x136, x135<- arg1[5] * arg2[0]
mov [ rsp + 0x278 ], r12; spilling x136 to mem
setc r12b; spill CF x344 to reg (r12)
clc;
adcx rbp, rcx
setc cl; spill CF x348 to reg (rcx)
clc;
adcx rbp, rbx
seto bl; spill OF x340 to reg (rbx)
mov byte [ rsp + 0x280 ], cl; spilling byte x348 to mem
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, [ rsp + 0x258 ]
seto cl; spill OF x356 to reg (rcx)
mov byte [ rsp + 0x288 ], r12b; spilling byte x344 to mem
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, r9
mov r9, [ rsp + 0x248 ]; load m64 x28 to register64
movzx r14, r14b
lea r9, [ r14 + r9 ]
mov r14, [ rsp + 0x238 ]
lea r9, [r14+r9]
setc r14b; spill CF x352 to reg (r14)
clc;
adcx rbp, r15
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r15, r12, [ rax + 0x28 ]; x170, x169<- arg1[1] * arg2[5]
movzx r8, r8b
lea r9, [ r8 + r9 ]
mov r8, [ rsp + 0x230 ]
lea r9, [r8+r9]
setc r8b; spill CF x364 to reg (r8)
clc;
adcx rbp, [ rsp + 0x210 ]
movzx r11, r11b
lea r9, [ r11 + r9 ]
mov r11, [ rsp + 0x240 ]
lea r9, [r11+r9]
setc r11b; spill CF x368 to reg (r11)
clc;
adcx rbp, [ rsp + 0x208 ]
mov [ rsp + 0x290 ], r15; spilling x170 to mem
setc r15b; spill CF x372 to reg (r15)
clc;
adcx rbp, [ rsp + 0x220 ]
movzx rbx, bl
lea r9, [ rbx + r9 ]
mov rbx, [ rsp + 0x250 ]
lea r9, [rbx+r9]
movzx rbx, byte [ rsp + 0x288 ]; load byte memx344 to register64
lea r9, [ rbx + r9 ]
mov rbx, [ rsp + 0x1e8 ]
lea r9, [rbx+r9]
movzx rbx, byte [ rsp + 0x280 ]; load byte memx348 to register64
lea r9, [ rbx + r9 ]
mov rbx, [ rsp + 0x228 ]
lea r9, [rbx+r9]
movzx r14, r14b
lea r9, [ r14 + r9 ]
mov r14, [ rsp + 0x270 ]
lea r9, [r14+r9]
movzx rcx, cl
lea r9, [ rcx + r9 ]
mov rcx, [ rsp + 0x1d8 ]
lea r9, [rcx+r9]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx rbx, r14, [ rax + 0x38 ]; x14, x13<- arg1[7] * arg2[7]
adox r9, [ rsp + 0x278 ]
movzx r8, r8b
lea r9, [ r8 + r9 ]
mov r8, [ rsp + 0x268 ]
lea r9, [r8+r9]
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, [ rsp + 0x200 ]
seto r8b; spill OF x380 to reg (r8)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rbp, [ rsp + 0x260 ]
movzx r11, r11b
lea r9, [ r11 + r9 ]
mov r11, [ rsp + 0x1d0 ]
lea r9, [r11+r9]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mulx r11, rcx, [ rax + 0x28 ]; x100, x99<- arg1[5] * arg2[5]
movzx r15, r15b
lea r9, [ r15 + r9 ]
mov r15, [ rsp + 0x1e0 ]
lea r9, [r15+r9]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x298 ], r12; spilling x169 to mem
mulx r15, r12, [ rsi + 0x10 ]; x158, x157<- arg1[2] * arg2[4]
adcx r9, [ rsp + 0x218 ]
movzx r8, r8b
lea r9, [ r8 + r9 ]
mov r8, [ rsp + 0x1f0 ]
lea r9, [r8+r9]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x2a0 ], r15; spilling x158 to mem
mulx r8, r15, [ rax + 0x18 ]; x84, x83<- arg1[7] * arg2[3]
mov [ rsp + 0x2a8 ], r12; spilling x157 to mem
mov r12, 0x0 ; moving imm to reg
adox r9, r12
mov r12, rbp; x580, copying x572 here, cause x572 is needed in a reg for other than x580, namely all: , x581, x580, size: 2
shrd r12, r9, 56; x580 <- x574||x572 >> 56
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x2b0 ], r12; spilling x580 to mem
mulx r9, r12, [ rsi + 0x18 ]; x148, x147<- arg1[3] * arg2[3]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x2b8 ], r9; spilling x148 to mem
mov [ rsp + 0x2c0 ], r12; spilling x147 to mem
mulx r9, r12, [ rsi + 0x38 ]; x26, x25<- arg1[7] * arg2[7]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x2c8 ], r11; spilling x100 to mem
mov [ rsp + 0x2d0 ], r8; spilling x84 to mem
mulx r11, r8, [ rax + 0x8 ]; x134, x133<- arg1[5] * arg2[1]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x2d8 ], r11; spilling x134 to mem
mov [ rsp + 0x2e0 ], r8; spilling x133 to mem
mulx r11, r8, [ rax + 0x0 ]; x130, x129<- arg1[6] * arg2[0]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x2e8 ], r11; spilling x130 to mem
mov [ rsp + 0x2f0 ], r8; spilling x129 to mem
mulx r11, r8, [ rsi + 0x0 ]; x184, x183<- arg1[0] * arg2[6]
add r14, r12; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x2f8 ], r11; spilling x184 to mem
mulx r12, r11, [ rax + 0x20 ]; x92, x91<- arg1[6] * arg2[4]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x300 ], r8; spilling x183 to mem
mov [ rsp + 0x308 ], r12; spilling x92 to mem
mulx r8, r12, [ rsi + 0x20 ]; x140, x139<- arg1[4] * arg2[2]
mov [ rsp + 0x310 ], r8; spilling x140 to mem
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, r15
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mulx r15, r8, [ rsi + 0x18 ]; x114, x113<- arg1[3] * arg2[7]
mov [ rsp + 0x318 ], r15; spilling x114 to mem
setc r15b; spill CF x272 to reg (r15)
clc;
adcx r14, r11
movzx r15, r15b
lea r9, [ r9 + rbx ]
lea r9, [ r9 + r15 ]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mulx rbx, r15, [ rsi + 0x20 ]; x108, x107<- arg1[4] * arg2[6]
setc r11b; spill CF x280 to reg (r11)
clc;
adcx r14, rcx
setc cl; spill CF x284 to reg (rcx)
clc;
adcx r14, r15
adox r9, [ rsp + 0x2d0 ]
movzx r11, r11b
lea r9, [ r11 + r9 ]
mov r11, [ rsp + 0x308 ]
lea r9, [r11+r9]
mov r11, -0x2 ; moving imm to reg
inc r11; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, r8
movzx rcx, cl
lea r9, [ rcx + r9 ]
mov rcx, [ rsp + 0x2c8 ]
lea r9, [rcx+r9]
adcx rbx, r9
clc;
adcx r14, [ rsp + 0x2f0 ]
setc r8b; spill CF x296 to reg (r8)
clc;
adcx r14, [ rsp + 0x2e0 ]
setc r15b; spill CF x300 to reg (r15)
clc;
adcx r14, r12
adox rbx, [ rsp + 0x318 ]
movzx r8, r8b
lea rbx, [ r8 + rbx ]
mov r8, [ rsp + 0x2e8 ]
lea rbx, [r8+rbx]
movzx r15, r15b
lea rbx, [ r15 + rbx ]
mov r15, [ rsp + 0x2d8 ]
lea rbx, [r15+rbx]
adcx rbx, [ rsp + 0x310 ]
test al, al
adox r14, [ rsp + 0x2c0 ]
adcx r14, [ rsp + 0x2a8 ]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mulx r12, rcx, [ rax + 0x10 ]; x50, x49<- arg1[6] * arg2[2]
setc r9b; spill CF x312 to reg (r9)
clc;
adcx r14, [ rsp + 0x298 ]
adox rbx, [ rsp + 0x2b8 ]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mulx r8, r15, [ rsi + 0x38 ]; x6, x5<- arg1[7] * arg2[5]
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r14, [ rsp + 0x300 ]
mov r11, 0xffffffffffffff ; moving imm to reg
mov [ rsp + 0x320 ], r12; spilling x50 to mem
setc r12b; spill CF x316 to reg (r12)
mov [ rsp + 0x328 ], rcx; spilling x49 to mem
seto cl; spill OF x320 to reg (rcx)
and rdi, r11; x563 <- x267&0xffffffffffffff
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x330 ], r8; spilling x6 to mem
mulx r11, r8, [ rax + 0x30 ]; x10, x9<- arg1[6] * arg2[6]
sar  r9b, 1
adcx rbx, [ rsp + 0x2a0 ]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x338 ], r11; spilling x10 to mem
mulx r9, r11, [ rax + 0x0 ]; x196, x195<- arg1[0] * arg2[0]
mov [ rsp + 0x340 ], r9; spilling x196 to mem
mov r9, 0xffffffffffffff ; moving imm to reg
and r13, r9; x568 <- x564&0xffffffffffffff
sar  r12b, 1
adcx rbx, [ rsp + 0x290 ]
adox r14, [ rsp + 0x2b0 ]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mulx r12, r9, [ rax + 0x18 ]; x60, x59<- arg1[5] * arg2[3]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x348 ], r13; spilling x568 to mem
mov [ rsp + 0x350 ], r11; spilling x195 to mem
mulx r13, r11, [ rax + 0x28 ]; x74, x73<- arg1[3] * arg2[5]
movzx rcx, cl
lea rbx, [ rcx + rbx ]
mov rcx, [ rsp + 0x2f8 ]
lea rbx, [rcx+rbx]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x358 ], r13; spilling x74 to mem
mulx rcx, r13, [ rax + 0x38 ]; x12, x11<- arg1[5] * arg2[7]
mov [ rsp + 0x360 ], r12; spilling x60 to mem
mov r12, 0x0 ; moving imm to reg
adox rbx, r12
mov r12, r14; x590, copying x582 here, cause x582 is needed in a reg for other than x590, namely all: , x590, x591, size: 2
shrd r12, rbx, 56; x590 <- x584||x582 >> 56
lea r12, [ r12 + rdi ]
mov rdi, r12; x596, copying x592 here, cause x592 is needed in a reg for other than x596, namely all: , x597, x596, size: 2
shr rdi, 56; x596 <- x592>> 56
test al, al
adox r15, r8
mov r8, [ rsp + 0x330 ]; load m64 x6 to register64
adox r8, [ rsp + 0x338 ]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x368 ], rdi; spilling x596 to mem
mulx rbx, rdi, [ rsi + 0x20 ]; x68, x67<- arg1[4] * arg2[4]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x370 ], rbx; spilling x68 to mem
mov [ rsp + 0x378 ], r11; spilling x73 to mem
mulx rbx, r11, [ rsi + 0x38 ]; x38, x37<- arg1[7] * arg2[1]
adcx r15, r13
adcx rcx, r8
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r13, r8, [ rax + 0x30 ]; x78, x77<- arg1[2] * arg2[6]
test al, al
adox r15, r11
adcx r15, [ rsp + 0x328 ]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x380 ], r13; spilling x78 to mem
mulx r11, r13, [ rsi + 0x8 ]; x80, x79<- arg1[1] * arg2[7]
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x388 ], r11; spilling x80 to mem
mov [ rsp + 0x390 ], r13; spilling x79 to mem
mulx r11, r13, [ rsi + 0x8 ]; x180, x179<- arg1[1] * arg2[0]
mov [ rsp + 0x398 ], r11; spilling x180 to mem
seto r11b; spill OF x528 to reg (r11)
mov [ rsp + 0x3a0 ], r13; spilling x179 to mem
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, r9
movzx r11, r11b
lea rbx, [ rbx + rcx ]
lea rbx, [ rbx + r11 ]
seto r9b; spill OF x536 to reg (r9)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r15, rdi
seto dil; spill OF x540 to reg (rdi)
mov rcx, -0x3 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r15, [ rsp + 0x378 ]
adcx rbx, [ rsp + 0x320 ]
clc;
adcx r15, r8
setc r8b; spill CF x548 to reg (r8)
clc;
adcx r15, [ rsp + 0x390 ]
movzx r9, r9b
lea rbx, [ r9 + rbx ]
mov r9, [ rsp + 0x360 ]
lea rbx, [r9+rbx]
movzx rdi, dil
lea rbx, [ rdi + rbx ]
mov rdi, [ rsp + 0x370 ]
lea rbx, [rdi+rbx]
adox rbx, [ rsp + 0x358 ]
movzx r8, r8b
lea rbx, [ r8 + rbx ]
mov r8, [ rsp + 0x380 ]
lea rbx, [r8+rbx]
adcx rbx, [ rsp + 0x388 ]
xor r11, r11
adox r15, [ rsp + 0x350 ]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mulx r13, r9, [ rsi + 0x10 ]; x76, x75<- arg1[2] * arg2[7]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx rdi, r8, [ rax + 0x30 ]; x4, x3<- arg1[7] * arg2[6]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx r11, rcx, [ rsi + 0x0 ]; x194, x193<- arg1[0] * arg2[1]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x3a8 ], r11; spilling x194 to mem
mov [ rsp + 0x3b0 ], rcx; spilling x193 to mem
mulx r11, rcx, [ rax + 0x30 ]; x72, x71<- arg1[3] * arg2[6]
adox rbx, [ rsp + 0x340 ]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x3b8 ], r13; spilling x76 to mem
mov [ rsp + 0x3c0 ], r9; spilling x75 to mem
mulx r13, r9, [ rsi + 0x30 ]; x8, x7<- arg1[6] * arg2[7]
adcx r10, r15
mov r15, -0x2 ; moving imm to reg
inc r15; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, r9
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mulx r9, r15, [ rax + 0x20 ]; x58, x57<- arg1[5] * arg2[4]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x3c8 ], r11; spilling x72 to mem
mov [ rsp + 0x3d0 ], rcx; spilling x71 to mem
mulx r11, rcx, [ rsi + 0x20 ]; x66, x65<- arg1[4] * arg2[5]
adox r13, rdi
adc rbx, 0x0
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x3d8 ], r11; spilling x66 to mem
mulx rdi, r11, [ rsi + 0x38 ]; x36, x35<- arg1[7] * arg2[2]
mov [ rsp + 0x3e0 ], r9; spilling x58 to mem
mov r9, r10; x575, copying x569 here, cause x569 is needed in a reg for other than x575, namely all: , x575, x576, size: 2
shrd r9, rbx, 56; x575 <- x571||x569 >> 56
test al, al
adox r8, r11
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mulx rbx, r11, [ rax + 0x18 ]; x48, x47<- arg1[6] * arg2[3]
adcx r8, r11
adox rdi, r13
adcx rbx, rdi
add r8, r15; could be done better, if r0 has been u8 as well
mov r15, -0x2 ; moving imm to reg
inc r15; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, rcx
adcx rbx, [ rsp + 0x3e0 ]
adox rbx, [ rsp + 0x3d8 ]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx rcx, r13, [ rsi + 0x0 ]; x192, x191<- arg1[0] * arg2[2]
add r8, [ rsp + 0x3d0 ]; could be done better, if r0 has been u8 as well
adcx rbx, [ rsp + 0x3c8 ]
xor r11, r11
adox r8, [ rsp + 0x3c0 ]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx rdi, r11, [ rax + 0x38 ]; x2, x1<- arg1[7] * arg2[7]
adox rbx, [ rsp + 0x3b8 ]
adcx r8, [ rsp + 0x3a0 ]
adcx rbx, [ rsp + 0x398 ]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x3e8 ], rcx; spilling x192 to mem
mulx r15, rcx, [ rsi + 0x38 ]; x34, x33<- arg1[7] * arg2[3]
add r8, [ rsp + 0x3b0 ]; could be done better, if r0 has been u8 as well
adcx rbx, [ rsp + 0x3a8 ]
add r8, r9; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x3f0 ], r13; spilling x191 to mem
mulx r9, r13, [ rax + 0x38 ]; x70, x69<- arg1[3] * arg2[7]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x3f8 ], r9; spilling x70 to mem
mov [ rsp + 0x400 ], r8; spilling x577 to mem
mulx r9, r8, [ rsi + 0x30 ]; x46, x45<- arg1[6] * arg2[4]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x408 ], r13; spilling x69 to mem
mov [ rsp + 0x410 ], r9; spilling x46 to mem
mulx r13, r9, [ rax + 0x30 ]; x64, x63<- arg1[4] * arg2[6]
adc rbx, 0x0
test al, al
adox r11, rcx
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x418 ], rbx; spilling x579 to mem
mulx rcx, rbx, [ rsi + 0x10 ]; x166, x165<- arg1[2] * arg2[0]
adcx r11, r8
adox r15, rdi
adcx r15, [ rsp + 0x410 ]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mulx rdi, r8, [ rsi + 0x28 ]; x56, x55<- arg1[5] * arg2[5]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x420 ], rcx; spilling x166 to mem
mov [ rsp + 0x428 ], rbx; spilling x165 to mem
mulx rcx, rbx, [ rsi + 0x8 ]; x178, x177<- arg1[1] * arg2[1]
add r11, r8; could be done better, if r0 has been u8 as well
adcx rdi, r15
xor r15, r15
adox r11, r9
adox r13, rdi
mov r9, 0xffffffffffffff ; moving imm to reg
and r14, r9; x591 <- x582&0xffffffffffffff
adox r11, [ rsp + 0x408 ]
mov r8, [ rsp + 0x400 ]; load m64 x577 to register64
mov rdi, [ rsp + 0x418 ]; load m64 x579 to register64
seto r15b; spill OF x468 to reg (r15)
mov r9, r8; x585, copying x577 here, cause x577 is needed in a reg for other than x585, namely all: , x586, x585, size: 2
shrd r9, rdi, 56; x585 <- x579||x577 >> 56
mov rdi, 0xffffffffffffff ; moving imm to reg
mov [ rsp + 0x430 ], r14; spilling x591 to mem
mov r14, [ rsp + 0x1f8 ]; x226, copying x221 here, cause x221 is needed in a reg for other than x226, namely all: , x226, size: 1
and r14, rdi; x226 <- x221&0xffffffffffffff
adox r11, [ rsp + 0x428 ]
movzx r15, r15b
lea r13, [ r15 + r13 ]
adcx r13, [ rsp + 0x3f8 ]
adox r13, [ rsp + 0x420 ]
test al, al
adox r11, rbx
adcx r11, [ rsp + 0x3f0 ]
setc bl; spill CF x480 to reg (rbx)
clc;
adcx r11, r9
adox rcx, r13
movzx rbx, bl
lea rcx, [ rbx + rcx ]
mov rbx, [ rsp + 0x3e8 ]
lea rcx, [rbx+rcx]
adc rcx, 0x0
mov r15, r11; x593, copying x587 here, cause x587 is needed in a reg for other than x593, namely all: , x594, x593, size: 2
shrd r15, rcx, 56; x593 <- x589||x587 >> 56
lea r15, [ r15 + r14 ]
mov r9, r15; x598, copying x595 here, cause x595 is needed in a reg for other than x598, namely all: , x598, x599, size: 2
shr r9, 56; x598 <- x595>> 56
and r10, rdi; x576 <- x569&0xffffffffffffff
add r10, [ rsp + 0x368 ]
and r11, rdi; x594 <- x587&0xffffffffffffff
and r15, rdi; x599 <- x595&0xffffffffffffff
mov r14, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r14 + 0x10 ], r11; out1[2] = x594
mov r13, [ rsp + 0x348 ]; x600, copying x568 here, cause x568 is needed in a reg for other than x600, namely all: , x600, size: 1
add r13, [ rsp + 0x368 ]
mov rbx, r10; x607, copying x601 here, cause x601 is needed in a reg for other than x607, namely all: , x606, x607, size: 2
and rbx, rdi; x607 <- x601&0xffffffffffffff
mov rcx, [ rsp + 0x430 ]; TMP = x591
mov [ r14 + 0x30 ], rcx; out1[6] = TMP
and rbp, rdi; x581 <- x572&0xffffffffffffff
shr r10, 56; x606 <- x601>> 56
mov [ r14 + 0x18 ], r15; out1[3] = x599
lea r9, [ r9 + r13 ]
mov rcx, r9; x604, copying x602 here, cause x602 is needed in a reg for other than x604, namely all: , x603, x604, size: 2
and rcx, rdi; x604 <- x602&0xffffffffffffff
mov [ r14 + 0x0 ], rbx; out1[0] = x607
and r12, rdi; x597 <- x592&0xffffffffffffff
shr r9, 56; x603 <- x602>> 56
lea r9, [ r9 + rbp ]
mov [ r14 + 0x28 ], r9; out1[5] = x605
mov [ r14 + 0x20 ], rcx; out1[4] = x604
and r8, rdi; x586 <- x577&0xffffffffffffff
mov [ r14 + 0x38 ], r12; out1[7] = x597
lea r10, [ r10 + r8 ]
mov [ r14 + 0x8 ], r10; out1[1] = x608
mov rbx, [ rsp + 0x438 ]; restoring from stack
mov rbp, [ rsp + 0x440 ]; restoring from stack
mov r12, [ rsp + 0x448 ]; restoring from stack
mov r13, [ rsp + 0x450 ]; restoring from stack
mov r14, [ rsp + 0x458 ]; restoring from stack
mov r15, [ rsp + 0x460 ]; restoring from stack
add rsp, 0x468 
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; clocked at 2200 MHz
; first cyclecount 269.61, best 194.6216216216216, lastGood 196.67567567567568
; seed 3286030842510209 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4342598 ms / 60000 runs=> 72.37663333333333ms/run
; Time spent for assembling and measureing (initial batch_size=76, initial num_batches=101): 222907 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.05133033267182456
; number reverted permutation/ tried permutation: 18765 / 29957 =62.640%
; number reverted decision/ tried decision: 16121 / 30044 =53.658%