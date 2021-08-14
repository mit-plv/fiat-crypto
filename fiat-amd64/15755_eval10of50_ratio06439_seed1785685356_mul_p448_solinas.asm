SECTION .text
	GLOBAL mul_p448_solinas
mul_p448_solinas:
sub rsp, 0x4a0
mov rax, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x18 ]; saving arg2[3] in rdx.
mulx r10, r11, [ rsi + 0x0 ]; x190, x189<- arg1[0] * arg2[3]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rcx, r8, [ rax + 0x10 ]; x176, x175<- arg1[1] * arg2[2]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x0 ], r15; spilling callerSaver15 to mem
mulx r9, r15, [ rax + 0x8 ]; x164, x163<- arg1[2] * arg2[1]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x8 ], r14; spilling callerSaver14 to mem
mov [ rsp + 0x10 ], r13; spilling callerSaver13 to mem
mulx r14, r13, [ rax + 0x0 ]; x154, x153<- arg1[3] * arg2[0]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x18 ], r12; spilling callerSaver12 to mem
mov [ rsp + 0x20 ], rbp; spilling callerSaverbp to mem
mulx r12, rbp, [ rsi + 0x20 ]; x62, x61<- arg1[4] * arg2[7]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x28 ], rbx; spilling callerSaverbx to mem
mov [ rsp + 0x30 ], rdi; spilling out1 to mem
mulx rbx, rdi, [ rsi + 0x28 ]; x54, x53<- arg1[5] * arg2[6]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x38 ], r10; spilling x190 to mem
mov [ rsp + 0x40 ], rcx; spilling x176 to mem
mulx r10, rcx, [ rax + 0x28 ]; x44, x43<- arg1[6] * arg2[5]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x48 ], r9; spilling x164 to mem
mov [ rsp + 0x50 ], r14; spilling x154 to mem
mulx r9, r14, [ rsi + 0x38 ]; x32, x31<- arg1[7] * arg2[4]
mov [ rsp + 0x58 ], r12; spilling x62 to mem
xor r12, r12
adox r14, rcx
adcx r14, rdi
setc dil; spill CF x202 to reg (rdi)
clc;
adcx r14, rbp
setc bpl; spill CF x206 to reg (rbp)
clc;
adcx r14, r13
seto r13b; spill OF x198 to reg (r13)
mov rcx, -0x3 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r14, r15
seto r15b; spill OF x214 to reg (r15)
mov rcx, -0x3 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r14, r8
seto r8b; spill OF x218 to reg (r8)
mov rcx, -0x3 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r14, r11
movzx r13, r13b
lea r10, [ r10 + r9 ]
lea r10, [ r10 + r13 ]
movzx rdi, dil
lea rbx, [ rbx + r10 ]
lea rbx, [ rbx + rdi ]
movzx rbp, bpl
lea rbx, [ rbp + rbx ]
mov rbp, [ rsp + 0x58 ]
lea rbx, [rbp+rbx]
adcx rbx, [ rsp + 0x50 ]
movzx r15, r15b
lea rbx, [ r15 + rbx ]
mov r15, [ rsp + 0x48 ]
lea rbx, [r15+rbx]
movzx r8, r8b
lea rbx, [ r8 + rbx ]
mov r8, [ rsp + 0x40 ]
lea rbx, [r8+rbx]
adox rbx, [ rsp + 0x38 ]
mov r11, r14; x225, copying x221 here, cause x221 is needed in a reg for other than x225, namely all: , x225, x226, size: 2
shrd r11, rbx, 56; x225 <- x223||x221 >> 56
mov r9, 0x38 ; moving imm to reg
bzhi r14, r14, r9; x226 <- x221 (only least 0x38 bits)
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r13, rdi, [ rax + 0x20 ]; x188, x187<- arg1[0] * arg2[4]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mulx rbp, r15, [ rsi + 0x8 ]; x174, x173<- arg1[1] * arg2[3]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx r8, r10, [ rsi + 0x10 ]; x162, x161<- arg1[2] * arg2[2]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx rbx, r12, [ rsi + 0x18 ]; x152, x151<- arg1[3] * arg2[1]
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx r9, rcx, [ rsi + 0x20 ]; x144, x143<- arg1[4] * arg2[0]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x60 ], r14; spilling x226 to mem
mov [ rsp + 0x68 ], r13; spilling x188 to mem
mulx r14, r13, [ rax + 0x38 ]; x124, x123<- arg1[1] * arg2[7]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x70 ], rbp; spilling x174 to mem
mov [ rsp + 0x78 ], r8; spilling x162 to mem
mulx rbp, r8, [ rsi + 0x10 ]; x122, x121<- arg1[2] * arg2[6]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x80 ], rbx; spilling x152 to mem
mov [ rsp + 0x88 ], r9; spilling x144 to mem
mulx rbx, r9, [ rax + 0x28 ]; x118, x117<- arg1[3] * arg2[5]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x90 ], r14; spilling x124 to mem
mov [ rsp + 0x98 ], rbp; spilling x122 to mem
mulx r14, rbp, [ rax + 0x20 ]; x112, x111<- arg1[4] * arg2[4]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0xa0 ], rbx; spilling x118 to mem
mov [ rsp + 0xa8 ], r14; spilling x112 to mem
mulx rbx, r14, [ rsi + 0x28 ]; x104, x103<- arg1[5] * arg2[3]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0xb0 ], rbx; spilling x104 to mem
mov [ rsp + 0xb8 ], r11; spilling x225 to mem
mulx rbx, r11, [ rax + 0x10 ]; x96, x95<- arg1[6] * arg2[2]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0xc0 ], rbx; spilling x96 to mem
mov [ rsp + 0xc8 ], rdi; spilling x187 to mem
mulx rbx, rdi, [ rax + 0x8 ]; x88, x87<- arg1[7] * arg2[1]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0xd0 ], rbx; spilling x88 to mem
mov [ rsp + 0xd8 ], r15; spilling x173 to mem
mulx rbx, r15, [ rsi + 0x28 ]; x52, x51<- arg1[5] * arg2[7]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0xe0 ], rbx; spilling x52 to mem
mov [ rsp + 0xe8 ], r10; spilling x161 to mem
mulx rbx, r10, [ rax + 0x30 ]; x42, x41<- arg1[6] * arg2[6]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0xf0 ], rbx; spilling x42 to mem
mov [ rsp + 0xf8 ], r12; spilling x151 to mem
mulx rbx, r12, [ rax + 0x28 ]; x30, x29<- arg1[7] * arg2[5]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x100 ], rbx; spilling x30 to mem
mov [ rsp + 0x108 ], rcx; spilling x143 to mem
mulx rbx, rcx, [ rsi + 0x28 ]; x24, x23<- arg1[5] * arg2[7]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x110 ], rbx; spilling x24 to mem
mov [ rsp + 0x118 ], r13; spilling x123 to mem
mulx rbx, r13, [ rax + 0x30 ]; x22, x21<- arg1[6] * arg2[6]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x120 ], rbx; spilling x22 to mem
mov [ rsp + 0x128 ], r8; spilling x121 to mem
mulx rbx, r8, [ rsi + 0x38 ]; x18, x17<- arg1[7] * arg2[5]
adox r8, r13
clc;
adcx r8, rcx
setc cl; spill CF x388 to reg (rcx)
clc;
adcx r8, r12
setc r12b; spill CF x392 to reg (r12)
clc;
adcx r8, r10
setc r10b; spill CF x396 to reg (r10)
clc;
adcx r8, r15
setc r15b; spill CF x400 to reg (r15)
clc;
adcx r8, rdi
setc dil; spill CF x404 to reg (rdi)
clc;
adcx r8, r11
setc r11b; spill CF x408 to reg (r11)
clc;
adcx r8, r14
setc r14b; spill CF x412 to reg (r14)
clc;
adcx r8, rbp
seto bpl; spill OF x384 to reg (rbp)
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, r9
seto r9b; spill OF x420 to reg (r9)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r8, [ rsp + 0x128 ]
mov byte [ rsp + 0x130 ], r9b; spilling byte x420 to mem
seto r9b; spill OF x424 to reg (r9)
mov byte [ rsp + 0x138 ], r14b; spilling byte x412 to mem
mov r14, -0x3 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r8, [ rsp + 0x118 ]
setc r14b; spill CF x416 to reg (r14)
clc;
adcx r8, [ rsp + 0x108 ]
mov byte [ rsp + 0x140 ], r9b; spilling byte x424 to mem
seto r9b; spill OF x428 to reg (r9)
mov byte [ rsp + 0x148 ], r14b; spilling byte x416 to mem
mov r14, -0x3 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r8, [ rsp + 0xf8 ]
seto r14b; spill OF x436 to reg (r14)
mov byte [ rsp + 0x150 ], r9b; spilling byte x428 to mem
mov r9, -0x3 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r8, [ rsp + 0xe8 ]
setc r9b; spill CF x432 to reg (r9)
clc;
adcx r8, [ rsp + 0xd8 ]
mov byte [ rsp + 0x158 ], r14b; spilling byte x436 to mem
setc r14b; spill CF x444 to reg (r14)
clc;
adcx r8, [ rsp + 0xc8 ]
mov byte [ rsp + 0x160 ], r14b; spilling byte x444 to mem
setc r14b; spill CF x448 to reg (r14)
clc;
adcx r8, [ rsp + 0xb8 ]
movzx rbp, bpl
lea rbx, [ rbp + rbx ]
mov rbp, [ rsp + 0x120 ]
lea rbx, [rbp+rbx]
movzx rcx, cl
lea rbx, [ rcx + rbx ]
mov rcx, [ rsp + 0x110 ]
lea rbx, [rcx+rbx]
movzx r12, r12b
lea rbx, [ r12 + rbx ]
mov r12, [ rsp + 0x100 ]
lea rbx, [r12+rbx]
movzx r10, r10b
lea rbx, [ r10 + rbx ]
mov r10, [ rsp + 0xf0 ]
lea rbx, [r10+rbx]
movzx r15, r15b
lea rbx, [ r15 + rbx ]
mov r15, [ rsp + 0xe0 ]
lea rbx, [r15+rbx]
movzx rdi, dil
lea rbx, [ rdi + rbx ]
mov rdi, [ rsp + 0xd0 ]
lea rbx, [rdi+rbx]
movzx r11, r11b
lea rbx, [ r11 + rbx ]
mov r11, [ rsp + 0xc0 ]
lea rbx, [r11+rbx]
movzx rbp, byte [ rsp + 0x138 ]; load byte memx412 to register64
lea rbx, [ rbp + rbx ]
mov rbp, [ rsp + 0xb0 ]
lea rbx, [rbp+rbx]
movzx rcx, byte [ rsp + 0x148 ]; load byte memx416 to register64
lea rbx, [ rcx + rbx ]
mov rcx, [ rsp + 0xa8 ]
lea rbx, [rcx+rbx]
movzx r12, byte [ rsp + 0x130 ]; load byte memx420 to register64
lea rbx, [ r12 + rbx ]
mov r12, [ rsp + 0xa0 ]
lea rbx, [r12+rbx]
movzx r10, byte [ rsp + 0x140 ]; load byte memx424 to register64
lea rbx, [ r10 + rbx ]
mov r10, [ rsp + 0x98 ]
lea rbx, [r10+rbx]
movzx r15, byte [ rsp + 0x150 ]; load byte memx428 to register64
lea rbx, [ r15 + rbx ]
mov r15, [ rsp + 0x90 ]
lea rbx, [r15+rbx]
movzx r9, r9b
lea rbx, [ r9 + rbx ]
mov r9, [ rsp + 0x88 ]
lea rbx, [r9+rbx]
movzx rdi, byte [ rsp + 0x158 ]; load byte memx436 to register64
lea rbx, [ rdi + rbx ]
mov rdi, [ rsp + 0x80 ]
lea rbx, [rdi+rbx]
adox rbx, [ rsp + 0x78 ]
movzx r11, byte [ rsp + 0x160 ]; load byte memx444 to register64
lea rbx, [ r11 + rbx ]
mov r11, [ rsp + 0x70 ]
lea rbx, [r11+rbx]
movzx r14, r14b
lea rbx, [ r14 + rbx ]
mov r14, [ rsp + 0x68 ]
lea rbx, [r14+rbx]
adc rbx, 0x0
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mulx rbp, rcx, [ rsi + 0x0 ]; x182, x181<- arg1[0] * arg2[7]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mulx r12, r10, [ rsi + 0x8 ]; x168, x167<- arg1[1] * arg2[6]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mulx r15, r9, [ rsi + 0x10 ]; x156, x155<- arg1[2] * arg2[5]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx rdi, r11, [ rsi + 0x18 ]; x146, x145<- arg1[3] * arg2[4]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r14, r13, [ rax + 0x18 ]; x138, x137<- arg1[4] * arg2[3]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x168 ], rbx; spilling x561 to mem
mov [ rsp + 0x170 ], r8; spilling x559 to mem
mulx rbx, r8, [ rax + 0x10 ]; x132, x131<- arg1[5] * arg2[2]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x178 ], rbp; spilling x182 to mem
mov [ rsp + 0x180 ], r12; spilling x168 to mem
mulx rbp, r12, [ rax + 0x8 ]; x128, x127<- arg1[6] * arg2[1]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x188 ], r15; spilling x156 to mem
mov [ rsp + 0x190 ], rdi; spilling x146 to mem
mulx r15, rdi, [ rax + 0x0 ]; x126, x125<- arg1[7] * arg2[0]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x198 ], r14; spilling x138 to mem
mov [ rsp + 0x1a0 ], rbx; spilling x132 to mem
mulx r14, rbx, [ rsi + 0x20 ]; x106, x105<- arg1[4] * arg2[7]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x1a8 ], rbp; spilling x128 to mem
mov [ rsp + 0x1b0 ], r15; spilling x126 to mem
mulx rbp, r15, [ rax + 0x30 ]; x98, x97<- arg1[5] * arg2[6]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x1b8 ], r14; spilling x106 to mem
mov [ rsp + 0x1c0 ], rbp; spilling x98 to mem
mulx r14, rbp, [ rsi + 0x30 ]; x90, x89<- arg1[6] * arg2[5]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x1c8 ], r14; spilling x90 to mem
mov [ rsp + 0x1d0 ], rcx; spilling x181 to mem
mulx r14, rcx, [ rsi + 0x38 ]; x82, x81<- arg1[7] * arg2[4]
test al, al
adox rcx, rbp
adcx rcx, r15
setc r15b; spill CF x232 to reg (r15)
clc;
adcx rcx, rbx
seto bl; spill OF x228 to reg (rbx)
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rcx, rdi
setc dil; spill CF x236 to reg (rdi)
clc;
adcx rcx, r12
seto r12b; spill OF x240 to reg (r12)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rcx, r8
setc r8b; spill CF x244 to reg (r8)
clc;
adcx rcx, r13
seto r13b; spill OF x248 to reg (r13)
mov byte [ rsp + 0x1d8 ], r8b; spilling byte x244 to mem
mov r8, -0x3 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rcx, r11
seto r11b; spill OF x256 to reg (r11)
mov r8, -0x3 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rcx, r9
setc r9b; spill CF x252 to reg (r9)
clc;
adcx rcx, r10
setc r10b; spill CF x264 to reg (r10)
clc;
adcx rcx, [ rsp + 0x1d0 ]
movzx rbx, bl
lea r14, [ rbx + r14 ]
mov rbx, [ rsp + 0x1c8 ]
lea r14, [rbx+r14]
movzx r15, r15b
lea r14, [ r15 + r14 ]
mov r15, [ rsp + 0x1c0 ]
lea r14, [r15+r14]
movzx rdi, dil
lea r14, [ rdi + r14 ]
mov rdi, [ rsp + 0x1b8 ]
lea r14, [rdi+r14]
movzx r12, r12b
lea r14, [ r12 + r14 ]
mov r12, [ rsp + 0x1b0 ]
lea r14, [r12+r14]
movzx rbx, byte [ rsp + 0x1d8 ]; load byte memx244 to register64
lea r14, [ rbx + r14 ]
mov rbx, [ rsp + 0x1a8 ]
lea r14, [rbx+r14]
movzx r13, r13b
lea r14, [ r13 + r14 ]
mov r13, [ rsp + 0x1a0 ]
lea r14, [r13+r14]
movzx r9, r9b
lea r14, [ r9 + r14 ]
mov r9, [ rsp + 0x198 ]
lea r14, [r9+r14]
movzx r11, r11b
lea r14, [ r11 + r14 ]
mov r11, [ rsp + 0x190 ]
lea r14, [r11+r14]
adox r14, [ rsp + 0x188 ]
movzx r10, r10b
lea r14, [ r10 + r14 ]
mov r10, [ rsp + 0x180 ]
lea r14, [r10+r14]
adcx r14, [ rsp + 0x178 ]
mov r15, rcx; x562, copying x267 here, cause x267 is needed in a reg for other than x562, namely all: , x562, x563, size: 2
shrd r15, r14, 56; x562 <- x269||x267 >> 56
mov rdi, 0xffffffffffffff ; moving imm to reg
and rcx, rdi; x563 <- x267&0xffffffffffffff
mov r12, r15; x564, copying x562 here, cause x562 is needed in a reg for other than x564, namely all: , x564--x565, x569--x570, size: 2
adox r12, [ rsp + 0x170 ]
mov rbx, [ rsp + 0x168 ]; x566, copying x561 here, cause x561 is needed in a reg for other than x566, namely all: , x566, size: 1
adox rbx, rbp
mov r13, r12; x567, copying x564 here, cause x564 is needed in a reg for other than x567, namely all: , x567, x568, size: 2
shrd r13, rbx, 56; x567 <- x566||x564 >> 56
and r12, rdi; x568 <- x564&0xffffffffffffff
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx r9, r11, [ rsi + 0x0 ]; x196, x195<- arg1[0] * arg2[0]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mulx r10, r14, [ rsi + 0x8 ]; x80, x79<- arg1[1] * arg2[7]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mulx rbx, rbp, [ rsi + 0x10 ]; x78, x77<- arg1[2] * arg2[6]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r8, rdi, [ rax + 0x28 ]; x74, x73<- arg1[3] * arg2[5]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x1e0 ], r12; spilling x568 to mem
mov [ rsp + 0x1e8 ], rcx; spilling x563 to mem
mulx r12, rcx, [ rsi + 0x20 ]; x68, x67<- arg1[4] * arg2[4]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x1f0 ], r13; spilling x567 to mem
mov [ rsp + 0x1f8 ], r9; spilling x196 to mem
mulx r13, r9, [ rax + 0x18 ]; x60, x59<- arg1[5] * arg2[3]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x200 ], r10; spilling x80 to mem
mov [ rsp + 0x208 ], rbx; spilling x78 to mem
mulx r10, rbx, [ rsi + 0x30 ]; x50, x49<- arg1[6] * arg2[2]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x210 ], r8; spilling x74 to mem
mov [ rsp + 0x218 ], r12; spilling x68 to mem
mulx r8, r12, [ rax + 0x8 ]; x38, x37<- arg1[7] * arg2[1]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x220 ], r13; spilling x60 to mem
mov [ rsp + 0x228 ], r10; spilling x50 to mem
mulx r13, r10, [ rsi + 0x28 ]; x12, x11<- arg1[5] * arg2[7]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x230 ], r8; spilling x38 to mem
mov [ rsp + 0x238 ], r13; spilling x12 to mem
mulx r8, r13, [ rsi + 0x30 ]; x10, x9<- arg1[6] * arg2[6]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x240 ], r8; spilling x10 to mem
mov [ rsp + 0x248 ], r11; spilling x195 to mem
mulx r8, r11, [ rsi + 0x38 ]; x6, x5<- arg1[7] * arg2[5]
adox r11, r13
adcx r11, r10
seto r10b; spill OF x520 to reg (r10)
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, r12
seto r12b; spill OF x528 to reg (r12)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r11, rbx
seto bl; spill OF x532 to reg (rbx)
mov byte [ rsp + 0x250 ], r12b; spilling byte x528 to mem
mov r12, -0x3 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r11, r9
setc r9b; spill CF x524 to reg (r9)
clc;
adcx r11, rcx
seto cl; spill OF x536 to reg (rcx)
mov r12, -0x3 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r11, rdi
seto dil; spill OF x544 to reg (rdi)
mov r12, -0x3 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r11, rbp
setc bpl; spill CF x540 to reg (rbp)
clc;
adcx r11, r14
seto r14b; spill OF x548 to reg (r14)
mov r12, -0x3 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r11, [ rsp + 0x248 ]
setc r12b; spill CF x552 to reg (r12)
clc;
adcx r15, r11
movzx r10, r10b
lea r8, [ r10 + r8 ]
mov r10, [ rsp + 0x240 ]
lea r8, [r10+r8]
movzx r9, r9b
lea r8, [ r9 + r8 ]
mov r9, [ rsp + 0x238 ]
lea r8, [r9+r8]
movzx r10, byte [ rsp + 0x250 ]; load byte memx528 to register64
lea r8, [ r10 + r8 ]
mov r10, [ rsp + 0x230 ]
lea r8, [r10+r8]
movzx rbx, bl
lea r8, [ rbx + r8 ]
mov rbx, [ rsp + 0x228 ]
lea r8, [rbx+r8]
movzx rcx, cl
lea r8, [ rcx + r8 ]
mov rcx, [ rsp + 0x220 ]
lea r8, [rcx+r8]
movzx rbp, bpl
lea r8, [ rbp + r8 ]
mov rbp, [ rsp + 0x218 ]
lea r8, [rbp+r8]
movzx rdi, dil
lea r8, [ rdi + r8 ]
mov rdi, [ rsp + 0x210 ]
lea r8, [rdi+r8]
movzx r14, r14b
lea r8, [ r14 + r8 ]
mov r14, [ rsp + 0x208 ]
lea r8, [r14+r8]
movzx r12, r12b
lea r8, [ r12 + r8 ]
mov r12, [ rsp + 0x200 ]
lea r8, [r12+r8]
adox r8, [ rsp + 0x1f8 ]
adc r8, 0x0
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx r9, r10, [ rsi + 0x8 ]; x172, x171<- arg1[1] * arg2[4]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mulx rbx, rcx, [ rsi + 0x0 ]; x186, x185<- arg1[0] * arg2[5]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rbp, rdi, [ rax + 0x18 ]; x160, x159<- arg1[2] * arg2[3]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r14, r12, [ rax + 0x10 ]; x150, x149<- arg1[3] * arg2[2]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx r11, r13, [ rsi + 0x20 ]; x142, x141<- arg1[4] * arg2[1]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x258 ], r8; spilling x571 to mem
mov [ rsp + 0x260 ], r15; spilling x569 to mem
mulx r8, r15, [ rax + 0x0 ]; x136, x135<- arg1[5] * arg2[0]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x268 ], rbx; spilling x186 to mem
mov [ rsp + 0x270 ], r9; spilling x172 to mem
mulx rbx, r9, [ rsi + 0x10 ]; x120, x119<- arg1[2] * arg2[7]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x278 ], rbp; spilling x160 to mem
mov [ rsp + 0x280 ], r14; spilling x150 to mem
mulx rbp, r14, [ rsi + 0x18 ]; x116, x115<- arg1[3] * arg2[6]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x288 ], r11; spilling x142 to mem
mov [ rsp + 0x290 ], r8; spilling x136 to mem
mulx r11, r8, [ rax + 0x28 ]; x110, x109<- arg1[4] * arg2[5]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x298 ], rbx; spilling x120 to mem
mov [ rsp + 0x2a0 ], rbp; spilling x116 to mem
mulx rbx, rbp, [ rax + 0x20 ]; x102, x101<- arg1[5] * arg2[4]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x2a8 ], r11; spilling x110 to mem
mov [ rsp + 0x2b0 ], rbx; spilling x102 to mem
mulx r11, rbx, [ rax + 0x18 ]; x94, x93<- arg1[6] * arg2[3]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x2b8 ], r11; spilling x94 to mem
mov [ rsp + 0x2c0 ], rcx; spilling x185 to mem
mulx r11, rcx, [ rsi + 0x38 ]; x86, x85<- arg1[7] * arg2[2]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x2c8 ], r11; spilling x86 to mem
mov [ rsp + 0x2d0 ], r10; spilling x171 to mem
mulx r11, r10, [ rax + 0x38 ]; x40, x39<- arg1[6] * arg2[7]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x2d8 ], r11; spilling x40 to mem
mov [ rsp + 0x2e0 ], rdi; spilling x159 to mem
mulx r11, rdi, [ rax + 0x30 ]; x28, x27<- arg1[7] * arg2[6]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x2e8 ], r11; spilling x28 to mem
mov [ rsp + 0x2f0 ], r12; spilling x149 to mem
mulx r11, r12, [ rax + 0x38 ]; x20, x19<- arg1[6] * arg2[7]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x2f8 ], r11; spilling x20 to mem
mov [ rsp + 0x300 ], r13; spilling x141 to mem
mulx r11, r13, [ rax + 0x30 ]; x16, x15<- arg1[7] * arg2[6]
test al, al
adox r13, r12
adcx r13, rdi
setc dil; spill CF x328 to reg (rdi)
clc;
adcx r13, r10
setc r10b; spill CF x332 to reg (r10)
clc;
adcx r13, rcx
setc cl; spill CF x336 to reg (rcx)
clc;
adcx r13, rbx
seto bl; spill OF x324 to reg (rbx)
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, rbp
setc bpl; spill CF x340 to reg (rbp)
clc;
adcx r13, r8
setc r8b; spill CF x348 to reg (r8)
clc;
adcx r13, r14
setc r14b; spill CF x352 to reg (r14)
clc;
adcx r13, r9
setc r9b; spill CF x356 to reg (r9)
clc;
adcx r13, r15
setc r15b; spill CF x360 to reg (r15)
clc;
adcx r13, [ rsp + 0x300 ]
seto r12b; spill OF x344 to reg (r12)
mov byte [ rsp + 0x308 ], r15b; spilling byte x360 to mem
mov r15, -0x2 ; moving imm to reg
inc r15; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, [ rsp + 0x2f0 ]
setc r15b; spill CF x364 to reg (r15)
clc;
adcx r13, [ rsp + 0x2e0 ]
mov byte [ rsp + 0x310 ], r15b; spilling byte x364 to mem
setc r15b; spill CF x372 to reg (r15)
clc;
adcx r13, [ rsp + 0x2d0 ]
mov byte [ rsp + 0x318 ], r15b; spilling byte x372 to mem
seto r15b; spill OF x368 to reg (r15)
mov byte [ rsp + 0x320 ], r9b; spilling byte x356 to mem
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, [ rsp + 0x2c0 ]
setc r9b; spill CF x376 to reg (r9)
clc;
adcx r13, [ rsp + 0x1f0 ]
movzx rbx, bl
lea r11, [ rbx + r11 ]
mov rbx, [ rsp + 0x2f8 ]
lea r11, [rbx+r11]
movzx rdi, dil
lea r11, [ rdi + r11 ]
mov rdi, [ rsp + 0x2e8 ]
lea r11, [rdi+r11]
movzx r10, r10b
lea r11, [ r10 + r11 ]
mov r10, [ rsp + 0x2d8 ]
lea r11, [r10+r11]
movzx rcx, cl
lea r11, [ rcx + r11 ]
mov rcx, [ rsp + 0x2c8 ]
lea r11, [rcx+r11]
movzx rbp, bpl
lea r11, [ rbp + r11 ]
mov rbp, [ rsp + 0x2b8 ]
lea r11, [rbp+r11]
movzx r12, r12b
lea r11, [ r12 + r11 ]
mov r12, [ rsp + 0x2b0 ]
lea r11, [r12+r11]
movzx r8, r8b
lea r11, [ r8 + r11 ]
mov r8, [ rsp + 0x2a8 ]
lea r11, [r8+r11]
movzx r14, r14b
lea r11, [ r14 + r11 ]
mov r14, [ rsp + 0x2a0 ]
lea r11, [r14+r11]
movzx rbx, byte [ rsp + 0x320 ]; load byte memx356 to register64
lea r11, [ rbx + r11 ]
mov rbx, [ rsp + 0x298 ]
lea r11, [rbx+r11]
movzx rdi, byte [ rsp + 0x308 ]; load byte memx360 to register64
lea r11, [ rdi + r11 ]
mov rdi, [ rsp + 0x290 ]
lea r11, [rdi+r11]
movzx r10, byte [ rsp + 0x310 ]; load byte memx364 to register64
lea r11, [ r10 + r11 ]
mov r10, [ rsp + 0x288 ]
lea r11, [r10+r11]
movzx r15, r15b
lea r11, [ r15 + r11 ]
mov r15, [ rsp + 0x280 ]
lea r11, [r15+r11]
movzx rcx, byte [ rsp + 0x318 ]; load byte memx372 to register64
lea r11, [ rcx + r11 ]
mov rcx, [ rsp + 0x278 ]
lea r11, [rcx+r11]
movzx r9, r9b
lea r11, [ r9 + r11 ]
mov r9, [ rsp + 0x270 ]
lea r11, [r9+r11]
adox r11, [ rsp + 0x268 ]
adc r11, 0x0
mov rbp, [ rsp + 0x260 ]; load m64 x569 to register64
mov r12, [ rsp + 0x258 ]; load m64 x571 to register64
mov r8, rbp; x575, copying x569 here, cause x569 is needed in a reg for other than x575, namely all: , x575, x576, size: 2
shrd r8, r12, 56; x575 <- x571||x569 >> 56
mov r12, 0xffffffffffffff ; moving imm to reg
and rbp, r12; x576 <- x569&0xffffffffffffff
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r14, rbx, [ rax + 0x8 ]; x194, x193<- arg1[0] * arg2[1]
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx rdi, r10, [ rsi + 0x8 ]; x180, x179<- arg1[1] * arg2[0]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r15, rcx, [ rax + 0x38 ]; x76, x75<- arg1[2] * arg2[7]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r9, r12, [ rax + 0x30 ]; x72, x71<- arg1[3] * arg2[6]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x328 ], rbp; spilling x576 to mem
mov [ rsp + 0x330 ], r11; spilling x574 to mem
mulx rbp, r11, [ rax + 0x28 ]; x66, x65<- arg1[4] * arg2[5]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x338 ], r13; spilling x572 to mem
mov [ rsp + 0x340 ], r14; spilling x194 to mem
mulx r13, r14, [ rsi + 0x28 ]; x58, x57<- arg1[5] * arg2[4]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x348 ], rdi; spilling x180 to mem
mov [ rsp + 0x350 ], r15; spilling x76 to mem
mulx rdi, r15, [ rsi + 0x30 ]; x48, x47<- arg1[6] * arg2[3]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x358 ], r9; spilling x72 to mem
mov [ rsp + 0x360 ], rbp; spilling x66 to mem
mulx r9, rbp, [ rax + 0x10 ]; x36, x35<- arg1[7] * arg2[2]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x368 ], r13; spilling x58 to mem
mov [ rsp + 0x370 ], rdi; spilling x48 to mem
mulx r13, rdi, [ rax + 0x38 ]; x8, x7<- arg1[6] * arg2[7]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x378 ], r9; spilling x36 to mem
mov [ rsp + 0x380 ], r13; spilling x8 to mem
mulx r9, r13, [ rax + 0x30 ]; x4, x3<- arg1[7] * arg2[6]
adox r13, rdi
adcx r13, rbp
seto bpl; spill OF x484 to reg (rbp)
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, r15
seto r15b; spill OF x492 to reg (r15)
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r13, r14
seto r14b; spill OF x496 to reg (r14)
mov byte [ rsp + 0x388 ], r15b; spilling byte x492 to mem
mov r15, -0x3 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r13, r11
seto r11b; spill OF x500 to reg (r11)
mov r15, -0x3 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r13, r12
seto r12b; spill OF x504 to reg (r12)
mov r15, -0x3 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r13, rcx
seto cl; spill OF x508 to reg (rcx)
mov r15, -0x3 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r13, r10
setc r10b; spill CF x488 to reg (r10)
clc;
adcx r13, rbx
seto bl; spill OF x512 to reg (rbx)
mov r15, -0x3 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r13, r8
movzx rbp, bpl
lea r9, [ rbp + r9 ]
mov rbp, [ rsp + 0x380 ]
lea r9, [rbp+r9]
movzx r10, r10b
lea r9, [ r10 + r9 ]
mov r10, [ rsp + 0x378 ]
lea r9, [r10+r9]
movzx r8, byte [ rsp + 0x388 ]; load byte memx492 to register64
lea r9, [ r8 + r9 ]
mov r8, [ rsp + 0x370 ]
lea r9, [r8+r9]
movzx r14, r14b
lea r9, [ r14 + r9 ]
mov r14, [ rsp + 0x368 ]
lea r9, [r14+r9]
movzx r11, r11b
lea r9, [ r11 + r9 ]
mov r11, [ rsp + 0x360 ]
lea r9, [r11+r9]
movzx r12, r12b
lea r9, [ r12 + r9 ]
mov r12, [ rsp + 0x358 ]
lea r9, [r12+r9]
movzx rcx, cl
lea r9, [ rcx + r9 ]
mov rcx, [ rsp + 0x350 ]
lea r9, [rcx+r9]
movzx rbx, bl
lea r9, [ rbx + r9 ]
mov rbx, [ rsp + 0x348 ]
lea r9, [rbx+r9]
adcx r9, [ rsp + 0x340 ]
adox r9, rdi
mov rbp, [ rsp + 0x338 ]; load m64 x572 to register64
mov r10, [ rsp + 0x330 ]; load m64 x574 to register64
mov r8, rbp; x580, copying x572 here, cause x572 is needed in a reg for other than x580, namely all: , x580, x581, size: 2
shrd r8, r10, 56; x580 <- x574||x572 >> 56
mov r10, 0x38 ; moving imm to reg
bzhi rbp, rbp, r10; x581 <- x572 (only least 0x38 bits)
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mulx r14, r11, [ rsi + 0x0 ]; x184, x183<- arg1[0] * arg2[6]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mulx r12, rcx, [ rsi + 0x8 ]; x170, x169<- arg1[1] * arg2[5]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx rbx, rdi, [ rsi + 0x10 ]; x158, x157<- arg1[2] * arg2[4]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r10, r15, [ rax + 0x18 ]; x148, x147<- arg1[3] * arg2[3]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x390 ], rbp; spilling x581 to mem
mov [ rsp + 0x398 ], r9; spilling x579 to mem
mulx rbp, r9, [ rsi + 0x20 ]; x140, x139<- arg1[4] * arg2[2]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x3a0 ], r13; spilling x577 to mem
mov [ rsp + 0x3a8 ], r14; spilling x184 to mem
mulx r13, r14, [ rax + 0x8 ]; x134, x133<- arg1[5] * arg2[1]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x3b0 ], r12; spilling x170 to mem
mov [ rsp + 0x3b8 ], rbx; spilling x158 to mem
mulx r12, rbx, [ rax + 0x0 ]; x130, x129<- arg1[6] * arg2[0]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x3c0 ], r10; spilling x148 to mem
mov [ rsp + 0x3c8 ], rbp; spilling x140 to mem
mulx r10, rbp, [ rax + 0x38 ]; x114, x113<- arg1[3] * arg2[7]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x3d0 ], r13; spilling x134 to mem
mov [ rsp + 0x3d8 ], r12; spilling x130 to mem
mulx r13, r12, [ rax + 0x30 ]; x108, x107<- arg1[4] * arg2[6]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x3e0 ], r10; spilling x114 to mem
mov [ rsp + 0x3e8 ], r13; spilling x108 to mem
mulx r10, r13, [ rsi + 0x28 ]; x100, x99<- arg1[5] * arg2[5]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x3f0 ], r10; spilling x100 to mem
mov [ rsp + 0x3f8 ], r8; spilling x580 to mem
mulx r10, r8, [ rsi + 0x30 ]; x92, x91<- arg1[6] * arg2[4]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x400 ], r10; spilling x92 to mem
mov [ rsp + 0x408 ], r11; spilling x183 to mem
mulx r10, r11, [ rax + 0x18 ]; x84, x83<- arg1[7] * arg2[3]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x410 ], r10; spilling x84 to mem
mov [ rsp + 0x418 ], rcx; spilling x169 to mem
mulx r10, rcx, [ rsi + 0x38 ]; x26, x25<- arg1[7] * arg2[7]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x420 ], r10; spilling x26 to mem
mov [ rsp + 0x428 ], rdi; spilling x157 to mem
mulx r10, rdi, [ rax + 0x38 ]; x14, x13<- arg1[7] * arg2[7]
adox rdi, rcx
clc;
adcx rdi, r11
setc r11b; spill CF x276 to reg (r11)
clc;
adcx rdi, r8
seto r8b; spill OF x272 to reg (r8)
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rdi, r13
seto r13b; spill OF x284 to reg (r13)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rdi, r12
seto r12b; spill OF x288 to reg (r12)
mov byte [ rsp + 0x430 ], r13b; spilling byte x284 to mem
mov r13, -0x3 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rdi, rbp
setc bpl; spill CF x280 to reg (rbp)
clc;
adcx rdi, rbx
setc bl; spill CF x296 to reg (rbx)
clc;
adcx rdi, r14
setc r14b; spill CF x300 to reg (r14)
clc;
adcx rdi, r9
seto r9b; spill OF x292 to reg (r9)
mov r13, -0x3 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rdi, r15
setc r15b; spill CF x304 to reg (r15)
clc;
adcx rdi, [ rsp + 0x428 ]
seto r13b; spill OF x308 to reg (r13)
mov byte [ rsp + 0x438 ], r15b; spilling byte x304 to mem
mov r15, -0x3 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rdi, [ rsp + 0x418 ]
setc r15b; spill CF x312 to reg (r15)
clc;
adcx rdi, [ rsp + 0x408 ]
mov byte [ rsp + 0x440 ], r15b; spilling byte x312 to mem
setc r15b; spill CF x320 to reg (r15)
clc;
adcx rdi, [ rsp + 0x3f8 ]
movzx r8, r8b
lea r10, [ r8 + r10 ]
mov r8, [ rsp + 0x420 ]
lea r10, [r8+r10]
movzx r11, r11b
lea r10, [ r11 + r10 ]
mov r11, [ rsp + 0x410 ]
lea r10, [r11+r10]
movzx rbp, bpl
lea r10, [ rbp + r10 ]
mov rbp, [ rsp + 0x400 ]
lea r10, [rbp+r10]
movzx r8, byte [ rsp + 0x430 ]; load byte memx284 to register64
lea r10, [ r8 + r10 ]
mov r8, [ rsp + 0x3f0 ]
lea r10, [r8+r10]
movzx r12, r12b
lea r10, [ r12 + r10 ]
mov r12, [ rsp + 0x3e8 ]
lea r10, [r12+r10]
movzx r9, r9b
lea r10, [ r9 + r10 ]
mov r9, [ rsp + 0x3e0 ]
lea r10, [r9+r10]
movzx rbx, bl
lea r10, [ rbx + r10 ]
mov rbx, [ rsp + 0x3d8 ]
lea r10, [rbx+r10]
movzx r14, r14b
lea r10, [ r14 + r10 ]
mov r14, [ rsp + 0x3d0 ]
lea r10, [r14+r10]
movzx r11, byte [ rsp + 0x438 ]; load byte memx304 to register64
lea r10, [ r11 + r10 ]
mov r11, [ rsp + 0x3c8 ]
lea r10, [r11+r10]
movzx r13, r13b
lea r10, [ r13 + r10 ]
mov r13, [ rsp + 0x3c0 ]
lea r10, [r13+r10]
movzx rbp, byte [ rsp + 0x440 ]; load byte memx312 to register64
lea r10, [ rbp + r10 ]
mov rbp, [ rsp + 0x3b8 ]
lea r10, [rbp+r10]
adox r10, [ rsp + 0x3b0 ]
movzx r15, r15b
lea r10, [ r15 + r10 ]
mov r15, [ rsp + 0x3a8 ]
lea r10, [r15+r10]
adc r10, 0x0
mov r8, [ rsp + 0x3a0 ]; load m64 x577 to register64
mov r12, [ rsp + 0x398 ]; load m64 x579 to register64
mov r9, r8; x585, copying x577 here, cause x577 is needed in a reg for other than x585, namely all: , x585, x586, size: 2
shrd r9, r12, 56; x585 <- x579||x577 >> 56
mov r12, 0x38 ; moving imm to reg
bzhi r8, r8, r12; x586 <- x577 (only least 0x38 bits)
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx rbx, r14, [ rsi + 0x0 ]; x192, x191<- arg1[0] * arg2[2]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx r11, r13, [ rsi + 0x8 ]; x178, x177<- arg1[1] * arg2[1]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rbp, r15, [ rax + 0x0 ]; x166, x165<- arg1[2] * arg2[0]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mulx rcx, r12, [ rsi + 0x18 ]; x70, x69<- arg1[3] * arg2[7]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x448 ], r8; spilling x586 to mem
mov [ rsp + 0x450 ], r10; spilling x584 to mem
mulx r8, r10, [ rsi + 0x20 ]; x64, x63<- arg1[4] * arg2[6]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x458 ], rdi; spilling x582 to mem
mov [ rsp + 0x460 ], rbx; spilling x192 to mem
mulx rdi, rbx, [ rax + 0x28 ]; x56, x55<- arg1[5] * arg2[5]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x468 ], r11; spilling x178 to mem
mov [ rsp + 0x470 ], rbp; spilling x166 to mem
mulx r11, rbp, [ rax + 0x20 ]; x46, x45<- arg1[6] * arg2[4]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x478 ], rcx; spilling x70 to mem
mov [ rsp + 0x480 ], r8; spilling x64 to mem
mulx rcx, r8, [ rsi + 0x38 ]; x34, x33<- arg1[7] * arg2[3]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x488 ], rdi; spilling x56 to mem
mov [ rsp + 0x490 ], r11; spilling x46 to mem
mulx rdi, r11, [ rsi + 0x38 ]; x2, x1<- arg1[7] * arg2[7]
adox r11, r8
clc;
adcx r11, rbp
setc bpl; spill CF x456 to reg (rbp)
clc;
adcx r11, rbx
seto bl; spill OF x452 to reg (rbx)
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, r10
seto r10b; spill OF x464 to reg (r10)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r11, r12
setc r12b; spill CF x460 to reg (r12)
clc;
adcx r11, r15
seto r15b; spill OF x468 to reg (r15)
mov byte [ rsp + 0x498 ], r10b; spilling byte x464 to mem
mov r10, -0x3 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r11, r13
seto r13b; spill OF x476 to reg (r13)
mov r10, -0x3 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r11, r14
setc r14b; spill CF x472 to reg (r14)
clc;
adcx r11, r9
movzx rbx, bl
lea rcx, [ rcx + rdi ]
lea rcx, [ rcx + rbx ]
movzx rbp, bpl
lea rcx, [ rbp + rcx ]
mov rbp, [ rsp + 0x490 ]
lea rcx, [rbp+rcx]
movzx r12, r12b
lea rcx, [ r12 + rcx ]
mov r12, [ rsp + 0x488 ]
lea rcx, [r12+rcx]
movzx r9, byte [ rsp + 0x498 ]; load byte memx464 to register64
lea rcx, [ r9 + rcx ]
mov r9, [ rsp + 0x480 ]
lea rcx, [r9+rcx]
movzx r15, r15b
lea rcx, [ r15 + rcx ]
mov r15, [ rsp + 0x478 ]
lea rcx, [r15+rcx]
movzx r14, r14b
lea rcx, [ r14 + rcx ]
mov r14, [ rsp + 0x470 ]
lea rcx, [r14+rcx]
movzx r13, r13b
lea rcx, [ r13 + rcx ]
mov r13, [ rsp + 0x468 ]
lea rcx, [r13+rcx]
adox rcx, [ rsp + 0x460 ]
adc rcx, 0x0
mov rdi, [ rsp + 0x458 ]; load m64 x582 to register64
mov rbx, [ rsp + 0x450 ]; load m64 x584 to register64
mov rbp, rdi; x590, copying x582 here, cause x582 is needed in a reg for other than x590, namely all: , x590, x591, size: 2
shrd rbp, rbx, 56; x590 <- x584||x582 >> 56
mov rbx, 0x38 ; moving imm to reg
bzhi rdi, rdi, rbx; x591 <- x582 (only least 0x38 bits)
add rbp, [ rsp + 0x1e8 ]
mov r12, r11; x593, copying x587 here, cause x587 is needed in a reg for other than x593, namely all: , x593, x594, size: 2
shrd r12, rcx, 56; x593 <- x589||x587 >> 56
mov r9, 0xffffffffffffff ; moving imm to reg
and r11, r9; x594 <- x587&0xffffffffffffff
add r12, [ rsp + 0x60 ]
mov r15, rbp; x596, copying x592 here, cause x592 is needed in a reg for other than x596, namely all: , x596, x597, size: 2
shr r15, 56; x596 <- x592>> 56
bzhi rbp, rbp, rbx; x597 <- x592 (only least 0x38 bits)
mov r14, r12; x598, copying x595 here, cause x595 is needed in a reg for other than x598, namely all: , x598, x599, size: 2
shr r14, 56; x598 <- x595>> 56
and r12, r9; x599 <- x595&0xffffffffffffff
mov r13, r15; x600, copying x596 here, cause x596 is needed in a reg for other than x600, namely all: , x600, x601, size: 2
add r13, [ rsp + 0x1e0 ]
add r15, [ rsp + 0x328 ]
lea r14, [ r14 + r13 ]
mov rcx, r14; x603, copying x602 here, cause x602 is needed in a reg for other than x603, namely all: , x603, x604, size: 2
shr rcx, 56; x603 <- x602>> 56
bzhi r14, r14, rbx; x604 <- x602 (only least 0x38 bits)
add rcx, [ rsp + 0x390 ]
mov r13, r15; x606, copying x601 here, cause x601 is needed in a reg for other than x606, namely all: , x606, x607, size: 2
shr r13, 56; x606 <- x601>> 56
and r15, r9; x607 <- x601&0xffffffffffffff
add r13, [ rsp + 0x448 ]
mov r8, [ rsp + 0x30 ]; load m64 out1 to register64
mov [ r8 + 0x0 ], r15; out1[0] = x607
mov [ r8 + 0x8 ], r13; out1[1] = x608
mov [ r8 + 0x10 ], r11; out1[2] = x594
mov [ r8 + 0x18 ], r12; out1[3] = x599
mov [ r8 + 0x20 ], r14; out1[4] = x604
mov [ r8 + 0x28 ], rcx; out1[5] = x605
mov [ r8 + 0x30 ], rdi; out1[6] = x591
mov [ r8 + 0x38 ], rbp; out1[7] = x597
mov r15, [ rsp + 0x0 ] ; pop
mov r14, [ rsp + 0x8 ] ; pop
mov r13, [ rsp + 0x10 ] ; pop
mov r12, [ rsp + 0x18 ] ; pop
mov rbp, [ rsp + 0x20 ] ; pop
mov rbx, [ rsp + 0x28 ] ; pop
add rsp, 0x4a0 
ret
; cpu Intel(R) Core(TM) i5-8265U CPU @ 1.60GHz
; ratio 0.6439
; seed 1785685356 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4458 ms / 10 evals=> 445.8ms/eval
; Time spent for assembling and measureing (initial batch_size=38, initial num_batches=31): 82 ms
; number of used evaluations: 10
; Ratio (time for assembling + measure)/(total runtime for 10 evals): 0.018393898609241812
; number reverted permutation/ tried permutation: 9 / 9 =100.000%
; number reverted decision/ tried decision: 1 / 1 =100.000%