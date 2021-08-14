SECTION .text
	GLOBAL mul_p521
mul_p521:
sub rsp, 0x488
imul rax, [ rdx + 0x40 ], 0x2; x10000 <- arg2[8] * 0x2
imul r10, [ rdx + 0x38 ], 0x2; x10001 <- arg2[7] * 0x2
imul r11, [ rdx + 0x30 ], 0x2; x10002 <- arg2[6] * 0x2
imul rcx, [ rdx + 0x28 ], 0x2; x10003 <- arg2[5] * 0x2
imul r8, [ rdx + 0x20 ], 0x2; x10004 <- arg2[4] * 0x2
imul r9, [ rdx + 0x18 ], 0x2; x10005 <- arg2[3] * 0x2
mov [ rsp + 0x0 ], r15; spilling callerSaver15 to mem
imul r15, [ rdx + 0x10 ], 0x2; x10006 <- arg2[2] * 0x2
mov [ rsp + 0x8 ], r14; spilling callerSaver14 to mem
imul r14, [ rdx + 0x8 ], 0x2; x10007 <- arg2[1] * 0x2
mov [ rsp + 0x10 ], r13; spilling callerSaver13 to mem
mov r13, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x0 ]; saving arg2[0] in rdx.
mov [ rsp + 0x18 ], r12; spilling callerSaver12 to mem
mov [ rsp + 0x20 ], rbp; spilling callerSaverbp to mem
mulx r12, rbp, [ rsi + 0x0 ]; x162, x161<- arg1[0] * arg2[0]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x28 ], rbx; spilling callerSaverbx to mem
mov [ rsp + 0x30 ], rdi; spilling out1 to mem
mulx rbx, rdi, rax; x72, x71<- arg1[1] * x10000
mov rdx, r10; x10001 to rdx
mov [ rsp + 0x38 ], r12; spilling x162 to mem
mulx r10, r12, [ rsi + 0x10 ]; x70, x69<- arg1[2] * x10001
mov [ rsp + 0x40 ], rbx; spilling x72 to mem
mov rbx, rdx; preserving value of x10001 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x48 ], r10; spilling x70 to mem
mov [ rsp + 0x50 ], rbp; spilling x161 to mem
mulx r10, rbp, r11; x66, x65<- arg1[3] * x10002
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x58 ], r10; spilling x66 to mem
mov [ rsp + 0x60 ], rdi; spilling x71 to mem
mulx r10, rdi, rcx; x60, x59<- arg1[4] * x10003
mov rdx, r8; x10004 to rdx
mov [ rsp + 0x68 ], r10; spilling x60 to mem
mulx r8, r10, [ rsi + 0x28 ]; x52, x51<- arg1[5] * x10004
mov [ rsp + 0x70 ], r8; spilling x52 to mem
mov r8, rdx; preserving value of x10004 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0x78 ], r12; spilling x69 to mem
mov [ rsp + 0x80 ], rbp; spilling x65 to mem
mulx r12, rbp, r9; x42, x41<- arg1[6] * x10005
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x88 ], r12; spilling x42 to mem
mov [ rsp + 0x90 ], rdi; spilling x59 to mem
mulx r12, rdi, r15; x30, x29<- arg1[7] * x10006
mov rdx, [ rsi + 0x40 ]; arg1[8] to rdx
mov [ rsp + 0x98 ], r12; spilling x30 to mem
mulx r14, r12, r14; x16, x15<- arg1[8] * x10007
mov [ rsp + 0xa0 ], r14; spilling x16 to mem
xor r14, r14
adox r12, rdi
adcx r12, rbp
setc bpl; spill CF x168 to reg (rbp)
clc;
adcx r12, r10
setc r10b; spill CF x172 to reg (r10)
clc;
adcx r12, [ rsp + 0x90 ]
setc dil; spill CF x176 to reg (rdi)
clc;
adcx r12, [ rsp + 0x80 ]
mov byte [ rsp + 0xa8 ], dil; spilling byte x176 to mem
setc dil; spill CF x180 to reg (rdi)
clc;
adcx r12, [ rsp + 0x78 ]
mov byte [ rsp + 0xb0 ], dil; spilling byte x180 to mem
seto dil; spill OF x164 to reg (rdi)
mov byte [ rsp + 0xb8 ], r10b; spilling byte x172 to mem
mov r10, -0x3 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r12, [ rsp + 0x60 ]
setc r10b; spill CF x184 to reg (r10)
clc;
adcx r12, [ rsp + 0x50 ]
mov r14, [ rsp + 0xa0 ]; load m64 x16 to register64
movzx rdi, dil
lea r14, [ rdi + r14 ]
mov rdi, [ rsp + 0x98 ]
lea r14, [rdi+r14]
movzx rbp, bpl
lea r14, [ rbp + r14 ]
mov rbp, [ rsp + 0x88 ]
lea r14, [rbp+r14]
movzx rdi, byte [ rsp + 0xb8 ]; load byte memx172 to register64
lea r14, [ rdi + r14 ]
mov rdi, [ rsp + 0x70 ]
lea r14, [rdi+r14]
movzx rbp, byte [ rsp + 0xa8 ]; load byte memx176 to register64
lea r14, [ rbp + r14 ]
mov rbp, [ rsp + 0x68 ]
lea r14, [rbp+r14]
movzx rdi, byte [ rsp + 0xb0 ]; load byte memx180 to register64
lea r14, [ rdi + r14 ]
mov rdi, [ rsp + 0x58 ]
lea r14, [rdi+r14]
movzx r10, r10b
lea r14, [ r10 + r14 ]
mov r10, [ rsp + 0x48 ]
lea r14, [r10+r14]
adox r14, [ rsp + 0x40 ]
adcx r14, [ rsp + 0x38 ]
mov rbp, r12; x195, copying x191 here, cause x191 is needed in a reg for other than x195, namely all: , x195, x197, size: 2
shrd rbp, r14, 58; x195 <- x193||x191 >> 58
shr r14, 58; x196 <- x193>> 58
mov rdi, 0x3a ; moving imm to reg
bzhi r12, r12, rdi; x197 <- x191 (only least 0x3a bits)
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r10, rdi, [ r13 + 0x8 ]; x160, x159<- arg1[0] * arg2[1]
mov rdx, [ r13 + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0xc0 ], r12; spilling x197 to mem
mov [ rsp + 0xc8 ], r14; spilling x196 to mem
mulx r12, r14, [ rsi + 0x8 ]; x144, x143<- arg1[1] * arg2[0]
mov rdx, rax; x10000 to rdx
mov [ rsp + 0xd0 ], r10; spilling x160 to mem
mulx rax, r10, [ rsi + 0x10 ]; x68, x67<- arg1[2] * x10000
xchg rdx, rbx; x10001, swapping with x10000, which is currently in rdx
mov [ rsp + 0xd8 ], r12; spilling x144 to mem
mov [ rsp + 0xe0 ], rax; spilling x68 to mem
mulx r12, rax, [ rsi + 0x18 ]; x64, x63<- arg1[3] * x10001
xchg rdx, r11; x10002, swapping with x10001, which is currently in rdx
mov [ rsp + 0xe8 ], r12; spilling x64 to mem
mov [ rsp + 0xf0 ], rbp; spilling x195 to mem
mulx r12, rbp, [ rsi + 0x20 ]; x58, x57<- arg1[4] * x10002
xchg rdx, rcx; x10003, swapping with x10002, which is currently in rdx
mov [ rsp + 0xf8 ], r12; spilling x58 to mem
mov [ rsp + 0x100 ], rdi; spilling x159 to mem
mulx r12, rdi, [ rsi + 0x28 ]; x50, x49<- arg1[5] * x10003
mov [ rsp + 0x108 ], r12; spilling x50 to mem
mov r12, rdx; preserving value of x10003 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0x110 ], r14; spilling x143 to mem
mov [ rsp + 0x118 ], r10; spilling x67 to mem
mulx r14, r10, r8; x40, x39<- arg1[6] * x10004
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x120 ], r14; spilling x40 to mem
mov [ rsp + 0x128 ], rax; spilling x63 to mem
mulx r14, rax, r9; x28, x27<- arg1[7] * x10005
mov rdx, [ rsi + 0x40 ]; arg1[8] to rdx
mov [ rsp + 0x130 ], r14; spilling x28 to mem
mulx r15, r14, r15; x14, x13<- arg1[8] * x10006
adox r14, rax
clc;
adcx r14, r10
setc r10b; spill CF x427 to reg (r10)
clc;
adcx r14, rdi
setc dil; spill CF x431 to reg (rdi)
clc;
adcx r14, rbp
setc bpl; spill CF x435 to reg (rbp)
clc;
adcx r14, [ rsp + 0x128 ]
seto al; spill OF x423 to reg (rax)
mov byte [ rsp + 0x138 ], bpl; spilling byte x435 to mem
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, [ rsp + 0x118 ]
setc bpl; spill CF x439 to reg (rbp)
clc;
adcx r14, [ rsp + 0x110 ]
mov byte [ rsp + 0x140 ], bpl; spilling byte x439 to mem
setc bpl; spill CF x447 to reg (rbp)
clc;
adcx r14, [ rsp + 0x100 ]
mov byte [ rsp + 0x148 ], bpl; spilling byte x447 to mem
setc bpl; spill CF x451 to reg (rbp)
clc;
adcx r14, [ rsp + 0xf0 ]
movzx rax, al
lea r15, [ rax + r15 ]
mov rax, [ rsp + 0x130 ]
lea r15, [rax+r15]
movzx r10, r10b
lea r15, [ r10 + r15 ]
mov r10, [ rsp + 0x120 ]
lea r15, [r10+r15]
movzx rdi, dil
lea r15, [ rdi + r15 ]
mov rdi, [ rsp + 0x108 ]
lea r15, [rdi+r15]
movzx rax, byte [ rsp + 0x138 ]; load byte memx435 to register64
lea r15, [ rax + r15 ]
mov rax, [ rsp + 0xf8 ]
lea r15, [rax+r15]
movzx r10, byte [ rsp + 0x140 ]; load byte memx439 to register64
lea r15, [ r10 + r15 ]
mov r10, [ rsp + 0xe8 ]
lea r15, [r10+r15]
adox r15, [ rsp + 0xe0 ]
movzx rdi, byte [ rsp + 0x148 ]; load byte memx447 to register64
lea r15, [ rdi + r15 ]
mov rdi, [ rsp + 0xd8 ]
lea r15, [rdi+r15]
movzx rbp, bpl
lea r15, [ rbp + r15 ]
mov rbp, [ rsp + 0xd0 ]
lea r15, [rbp+r15]
adcx r15, [ rsp + 0xc8 ]
mov rax, r14; x458, copying x454 here, cause x454 is needed in a reg for other than x458, namely all: , x458, x460, size: 2
shrd rax, r15, 58; x458 <- x456||x454 >> 58
shr r15, 58; x459 <- x456>> 58
mov r10, 0x3a ; moving imm to reg
bzhi r14, r14, r10; x460 <- x454 (only least 0x3a bits)
mov rdx, [ r13 + 0x10 ]; arg2[2] to rdx
mulx rdi, rbp, [ rsi + 0x0 ]; x158, x157<- arg1[0] * arg2[2]
mov rdx, [ r13 + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x150 ], r14; spilling x460 to mem
mulx r10, r14, [ rsi + 0x8 ]; x142, x141<- arg1[1] * arg2[1]
mov rdx, [ r13 + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x158 ], r15; spilling x459 to mem
mov [ rsp + 0x160 ], rdi; spilling x158 to mem
mulx r15, rdi, [ rsi + 0x10 ]; x128, x127<- arg1[2] * arg2[0]
mov rdx, rbx; x10000 to rdx
mov [ rsp + 0x168 ], r10; spilling x142 to mem
mov [ rsp + 0x170 ], r15; spilling x128 to mem
mulx r10, r15, [ rsi + 0x18 ]; x62, x61<- arg1[3] * x10000
mov [ rsp + 0x178 ], r10; spilling x62 to mem
mov r10, rdx; preserving value of x10000 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x180 ], rax; spilling x458 to mem
mov [ rsp + 0x188 ], rbp; spilling x157 to mem
mulx rax, rbp, r11; x56, x55<- arg1[4] * x10001
mov rdx, rcx; x10002 to rdx
mov [ rsp + 0x190 ], rax; spilling x56 to mem
mulx rcx, rax, [ rsi + 0x28 ]; x48, x47<- arg1[5] * x10002
mov [ rsp + 0x198 ], rcx; spilling x48 to mem
mov rcx, rdx; preserving value of x10002 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0x1a0 ], r14; spilling x141 to mem
mov [ rsp + 0x1a8 ], rdi; spilling x127 to mem
mulx r14, rdi, r12; x38, x37<- arg1[6] * x10003
mov rdx, r8; x10004 to rdx
mov [ rsp + 0x1b0 ], r14; spilling x38 to mem
mulx r8, r14, [ rsi + 0x38 ]; x26, x25<- arg1[7] * x10004
xchg rdx, r9; x10005, swapping with x10004, which is currently in rdx
mov [ rsp + 0x1b8 ], r8; spilling x26 to mem
mulx rdx, r8, [ rsi + 0x40 ]; x12, x11<- arg1[8] * x10005
adox r8, r14
clc;
adcx r8, rdi
seto dil; spill OF x391 to reg (rdi)
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, rax
seto al; spill OF x399 to reg (rax)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r8, rbp
seto bpl; spill OF x403 to reg (rbp)
mov byte [ rsp + 0x1c0 ], al; spilling byte x399 to mem
mov rax, -0x3 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r8, r15
seto r15b; spill OF x407 to reg (r15)
mov rax, -0x3 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r8, [ rsp + 0x1a8 ]
setc al; spill CF x395 to reg (rax)
clc;
adcx r8, [ rsp + 0x1a0 ]
mov byte [ rsp + 0x1c8 ], r15b; spilling byte x407 to mem
setc r15b; spill CF x415 to reg (r15)
clc;
adcx r8, [ rsp + 0x188 ]
mov byte [ rsp + 0x1d0 ], r15b; spilling byte x415 to mem
seto r15b; spill OF x411 to reg (r15)
mov byte [ rsp + 0x1d8 ], bpl; spilling byte x403 to mem
mov rbp, -0x3 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r8, [ rsp + 0x180 ]
movzx rdi, dil
lea rdx, [ rdi + rdx ]
mov rdi, [ rsp + 0x1b8 ]
lea rdx, [rdi+rdx]
movzx rax, al
lea rdx, [ rax + rdx ]
mov rax, [ rsp + 0x1b0 ]
lea rdx, [rax+rdx]
movzx rdi, byte [ rsp + 0x1c0 ]; load byte memx399 to register64
lea rdx, [ rdi + rdx ]
mov rdi, [ rsp + 0x198 ]
lea rdx, [rdi+rdx]
movzx rax, byte [ rsp + 0x1d8 ]; load byte memx403 to register64
lea rdx, [ rax + rdx ]
mov rax, [ rsp + 0x190 ]
lea rdx, [rax+rdx]
movzx rdi, byte [ rsp + 0x1c8 ]; load byte memx407 to register64
lea rdx, [ rdi + rdx ]
mov rdi, [ rsp + 0x178 ]
lea rdx, [rdi+rdx]
movzx r15, r15b
lea rdx, [ r15 + rdx ]
mov r15, [ rsp + 0x170 ]
lea rdx, [r15+rdx]
movzx rax, byte [ rsp + 0x1d0 ]; load byte memx415 to register64
lea rdx, [ rax + rdx ]
mov rax, [ rsp + 0x168 ]
lea rdx, [rax+rdx]
adcx rdx, [ rsp + 0x160 ]
adox rdx, [ rsp + 0x158 ]
mov rdi, r8; x465, copying x461 here, cause x461 is needed in a reg for other than x465, namely all: , x465, x467, size: 2
shrd rdi, rdx, 58; x465 <- x463||x461 >> 58
shr rdx, 58; x466 <- x463>> 58
mov r15, rdx; preserving value of x466 into a new reg
mov rdx, [ r13 + 0x18 ]; saving arg2[3] in rdx.
mulx rax, r14, [ rsi + 0x0 ]; x156, x155<- arg1[0] * arg2[3]
mov rbp, 0x3a ; moving imm to reg
bzhi r8, r8, rbp; x467 <- x461 (only least 0x3a bits)
mov rdx, [ r13 + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x1e0 ], r8; spilling x467 to mem
mulx rbp, r8, [ rsi + 0x8 ]; x140, x139<- arg1[1] * arg2[2]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x1e8 ], r15; spilling x466 to mem
mov [ rsp + 0x1f0 ], rax; spilling x156 to mem
mulx r15, rax, [ r13 + 0x8 ]; x126, x125<- arg1[2] * arg2[1]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x1f8 ], rbp; spilling x140 to mem
mov [ rsp + 0x200 ], r15; spilling x126 to mem
mulx rbp, r15, [ r13 + 0x0 ]; x114, x113<- arg1[3] * arg2[0]
mov rdx, r10; x10000 to rdx
mov [ rsp + 0x208 ], rbp; spilling x114 to mem
mulx r10, rbp, [ rsi + 0x20 ]; x54, x53<- arg1[4] * x10000
mov [ rsp + 0x210 ], r10; spilling x54 to mem
mov r10, rdx; preserving value of x10000 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x218 ], rdi; spilling x465 to mem
mov [ rsp + 0x220 ], r14; spilling x155 to mem
mulx rdi, r14, r11; x46, x45<- arg1[5] * x10001
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x228 ], rdi; spilling x46 to mem
mov [ rsp + 0x230 ], r8; spilling x139 to mem
mulx rdi, r8, rcx; x36, x35<- arg1[6] * x10002
mov rdx, r12; x10003 to rdx
mov [ rsp + 0x238 ], rdi; spilling x36 to mem
mov [ rsp + 0x240 ], rax; spilling x125 to mem
mulx rdi, rax, [ rsi + 0x38 ]; x24, x23<- arg1[7] * x10003
xchg rdx, r9; x10004, swapping with x10003, which is currently in rdx
mov [ rsp + 0x248 ], rdi; spilling x24 to mem
mulx rdx, rdi, [ rsi + 0x40 ]; x10, x9<- arg1[8] * x10004
adox rdi, rax
clc;
adcx rdi, r8
seto r8b; spill OF x359 to reg (r8)
mov rax, -0x2 ; moving imm to reg
inc rax; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rdi, r14
setc r14b; spill CF x363 to reg (r14)
clc;
adcx rdi, rbp
seto bpl; spill OF x367 to reg (rbp)
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rdi, r15
setc r15b; spill CF x371 to reg (r15)
clc;
adcx rdi, [ rsp + 0x240 ]
mov byte [ rsp + 0x250 ], r15b; spilling byte x371 to mem
seto r15b; spill OF x375 to reg (r15)
mov byte [ rsp + 0x258 ], bpl; spilling byte x367 to mem
mov rbp, -0x3 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rdi, [ rsp + 0x230 ]
setc bpl; spill CF x379 to reg (rbp)
clc;
adcx rdi, [ rsp + 0x220 ]
mov byte [ rsp + 0x260 ], bpl; spilling byte x379 to mem
seto bpl; spill OF x383 to reg (rbp)
mov byte [ rsp + 0x268 ], r15b; spilling byte x375 to mem
mov r15, -0x3 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rdi, [ rsp + 0x218 ]
movzx r8, r8b
lea rdx, [ r8 + rdx ]
mov r8, [ rsp + 0x248 ]
lea rdx, [r8+rdx]
movzx r14, r14b
lea rdx, [ r14 + rdx ]
mov r14, [ rsp + 0x238 ]
lea rdx, [r14+rdx]
movzx r8, byte [ rsp + 0x258 ]; load byte memx367 to register64
lea rdx, [ r8 + rdx ]
mov r8, [ rsp + 0x228 ]
lea rdx, [r8+rdx]
movzx r14, byte [ rsp + 0x250 ]; load byte memx371 to register64
lea rdx, [ r14 + rdx ]
mov r14, [ rsp + 0x210 ]
lea rdx, [r14+rdx]
movzx r8, byte [ rsp + 0x268 ]; load byte memx375 to register64
lea rdx, [ r8 + rdx ]
mov r8, [ rsp + 0x208 ]
lea rdx, [r8+rdx]
movzx r14, byte [ rsp + 0x260 ]; load byte memx379 to register64
lea rdx, [ r14 + rdx ]
mov r14, [ rsp + 0x200 ]
lea rdx, [r14+rdx]
movzx rbp, bpl
lea rdx, [ rbp + rdx ]
mov rbp, [ rsp + 0x1f8 ]
lea rdx, [rbp+rdx]
adcx rdx, [ rsp + 0x1f0 ]
adox rdx, [ rsp + 0x1e8 ]
mov r8, rdi; x472, copying x468 here, cause x468 is needed in a reg for other than x472, namely all: , x472, x474, size: 2
shrd r8, rdx, 58; x472 <- x470||x468 >> 58
shr rdx, 58; x473 <- x470>> 58
mov r14, 0x3a ; moving imm to reg
bzhi rdi, rdi, r14; x474 <- x468 (only least 0x3a bits)
mov rbp, rdx; preserving value of x473 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx rax, r14, [ r13 + 0x20 ]; x154, x153<- arg1[0] * arg2[4]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x270 ], rdi; spilling x474 to mem
mulx r15, rdi, [ r13 + 0x18 ]; x138, x137<- arg1[1] * arg2[3]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x278 ], rbp; spilling x473 to mem
mov [ rsp + 0x280 ], rax; spilling x154 to mem
mulx rbp, rax, [ r13 + 0x10 ]; x124, x123<- arg1[2] * arg2[2]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x288 ], r15; spilling x138 to mem
mov [ rsp + 0x290 ], rbp; spilling x124 to mem
mulx r15, rbp, [ r13 + 0x8 ]; x112, x111<- arg1[3] * arg2[1]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x298 ], r15; spilling x112 to mem
mov [ rsp + 0x2a0 ], r8; spilling x472 to mem
mulx r15, r8, [ r13 + 0x0 ]; x102, x101<- arg1[4] * arg2[0]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x2a8 ], r15; spilling x102 to mem
mov [ rsp + 0x2b0 ], r14; spilling x153 to mem
mulx r15, r14, r10; x44, x43<- arg1[5] * x10000
mov rdx, r11; x10001 to rdx
mov [ rsp + 0x2b8 ], r15; spilling x44 to mem
mulx r11, r15, [ rsi + 0x30 ]; x34, x33<- arg1[6] * x10001
mov [ rsp + 0x2c0 ], r11; spilling x34 to mem
mov r11, rdx; preserving value of x10001 into a new reg
mov rdx, [ rsi + 0x38 ]; saving arg1[7] in rdx.
mov [ rsp + 0x2c8 ], rdi; spilling x137 to mem
mov [ rsp + 0x2d0 ], rax; spilling x123 to mem
mulx rdi, rax, rcx; x22, x21<- arg1[7] * x10002
mov rdx, [ rsi + 0x40 ]; arg1[8] to rdx
mov [ rsp + 0x2d8 ], rdi; spilling x22 to mem
mulx r9, rdi, r9; x8, x7<- arg1[8] * x10003
adox rdi, rax
clc;
adcx rdi, r15
seto r15b; spill OF x327 to reg (r15)
mov rax, -0x2 ; moving imm to reg
inc rax; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rdi, r14
setc r14b; spill CF x331 to reg (r14)
clc;
adcx rdi, r8
seto r8b; spill OF x335 to reg (r8)
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rdi, rbp
seto bpl; spill OF x343 to reg (rbp)
mov byte [ rsp + 0x2e0 ], r8b; spilling byte x335 to mem
mov r8, -0x3 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rdi, [ rsp + 0x2d0 ]
setc r8b; spill CF x339 to reg (r8)
clc;
adcx rdi, [ rsp + 0x2c8 ]
mov byte [ rsp + 0x2e8 ], bpl; spilling byte x343 to mem
seto bpl; spill OF x347 to reg (rbp)
mov byte [ rsp + 0x2f0 ], r8b; spilling byte x339 to mem
mov r8, -0x3 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rdi, [ rsp + 0x2b0 ]
seto r8b; spill OF x355 to reg (r8)
mov byte [ rsp + 0x2f8 ], bpl; spilling byte x347 to mem
mov rbp, -0x3 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rdi, [ rsp + 0x2a0 ]
movzx r15, r15b
lea r9, [ r15 + r9 ]
mov r15, [ rsp + 0x2d8 ]
lea r9, [r15+r9]
movzx r14, r14b
lea r9, [ r14 + r9 ]
mov r14, [ rsp + 0x2c0 ]
lea r9, [r14+r9]
movzx r15, byte [ rsp + 0x2e0 ]; load byte memx335 to register64
lea r9, [ r15 + r9 ]
mov r15, [ rsp + 0x2b8 ]
lea r9, [r15+r9]
movzx r14, byte [ rsp + 0x2f0 ]; load byte memx339 to register64
lea r9, [ r14 + r9 ]
mov r14, [ rsp + 0x2a8 ]
lea r9, [r14+r9]
movzx r15, byte [ rsp + 0x2e8 ]; load byte memx343 to register64
lea r9, [ r15 + r9 ]
mov r15, [ rsp + 0x298 ]
lea r9, [r15+r9]
movzx r14, byte [ rsp + 0x2f8 ]; load byte memx347 to register64
lea r9, [ r14 + r9 ]
mov r14, [ rsp + 0x290 ]
lea r9, [r14+r9]
adcx r9, [ rsp + 0x288 ]
movzx r8, r8b
lea r9, [ r8 + r9 ]
mov r8, [ rsp + 0x280 ]
lea r9, [r8+r9]
adox r9, [ rsp + 0x278 ]
mov r15, rdi; x479, copying x475 here, cause x475 is needed in a reg for other than x479, namely all: , x479, x481, size: 2
shrd r15, r9, 58; x479 <- x477||x475 >> 58
shr r9, 58; x480 <- x477>> 58
mov r14, 0x3a ; moving imm to reg
bzhi rdi, rdi, r14; x481 <- x475 (only least 0x3a bits)
mov rdx, [ r13 + 0x28 ]; arg2[5] to rdx
mulx r8, rax, [ rsi + 0x0 ]; x152, x151<- arg1[0] * arg2[5]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r14, rbp, [ r13 + 0x20 ]; x136, x135<- arg1[1] * arg2[4]
mov rdx, [ r13 + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x300 ], rdi; spilling x481 to mem
mov [ rsp + 0x308 ], r9; spilling x480 to mem
mulx rdi, r9, [ rsi + 0x10 ]; x122, x121<- arg1[2] * arg2[3]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x310 ], r8; spilling x152 to mem
mov [ rsp + 0x318 ], r14; spilling x136 to mem
mulx r8, r14, [ r13 + 0x10 ]; x110, x109<- arg1[3] * arg2[2]
mov rdx, [ r13 + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x320 ], rdi; spilling x122 to mem
mov [ rsp + 0x328 ], r8; spilling x110 to mem
mulx rdi, r8, [ rsi + 0x20 ]; x100, x99<- arg1[4] * arg2[1]
mov rdx, [ r13 + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x330 ], rdi; spilling x100 to mem
mov [ rsp + 0x338 ], r15; spilling x479 to mem
mulx rdi, r15, [ rsi + 0x28 ]; x92, x91<- arg1[5] * arg2[0]
mov rdx, r10; x10000 to rdx
mov [ rsp + 0x340 ], rdi; spilling x92 to mem
mulx r10, rdi, [ rsi + 0x30 ]; x32, x31<- arg1[6] * x10000
mov [ rsp + 0x348 ], r10; spilling x32 to mem
mov r10, rdx; preserving value of x10000 into a new reg
mov rdx, [ rsi + 0x38 ]; saving arg1[7] in rdx.
mov [ rsp + 0x350 ], rax; spilling x151 to mem
mov [ rsp + 0x358 ], rbp; spilling x135 to mem
mulx rax, rbp, r11; x20, x19<- arg1[7] * x10001
mov rdx, rcx; x10002 to rdx
mulx rdx, rcx, [ rsi + 0x40 ]; x6, x5<- arg1[8] * x10002
adox rcx, rbp
clc;
adcx rcx, rdi
seto dil; spill OF x295 to reg (rdi)
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rcx, r15
seto r15b; spill OF x303 to reg (r15)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rcx, r8
setc r8b; spill CF x299 to reg (r8)
clc;
adcx rcx, r14
seto r14b; spill OF x307 to reg (r14)
mov byte [ rsp + 0x360 ], r15b; spilling byte x303 to mem
mov r15, -0x3 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rcx, r9
setc r9b; spill CF x311 to reg (r9)
clc;
adcx rcx, [ rsp + 0x358 ]
setc r15b; spill CF x319 to reg (r15)
clc;
adcx rcx, [ rsp + 0x350 ]
mov byte [ rsp + 0x368 ], r15b; spilling byte x319 to mem
seto r15b; spill OF x315 to reg (r15)
mov byte [ rsp + 0x370 ], r9b; spilling byte x311 to mem
mov r9, -0x3 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rcx, [ rsp + 0x338 ]
movzx rdi, dil
lea rax, [ rax + rdx ]
lea rax, [ rax + rdi ]
movzx r8, r8b
lea rax, [ r8 + rax ]
mov r8, [ rsp + 0x348 ]
lea rax, [r8+rax]
movzx rdx, byte [ rsp + 0x360 ]; load byte memx303 to register64
lea rax, [ rdx + rax ]
mov rdx, [ rsp + 0x340 ]
lea rax, [rdx+rax]
movzx r14, r14b
lea rax, [ r14 + rax ]
mov r14, [ rsp + 0x330 ]
lea rax, [r14+rax]
movzx rdi, byte [ rsp + 0x370 ]; load byte memx311 to register64
lea rax, [ rdi + rax ]
mov rdi, [ rsp + 0x328 ]
lea rax, [rdi+rax]
movzx r15, r15b
lea rax, [ r15 + rax ]
mov r15, [ rsp + 0x320 ]
lea rax, [r15+rax]
movzx r8, byte [ rsp + 0x368 ]; load byte memx319 to register64
lea rax, [ r8 + rax ]
mov r8, [ rsp + 0x318 ]
lea rax, [r8+rax]
adcx rax, [ rsp + 0x310 ]
adox rax, [ rsp + 0x308 ]
mov rdx, rcx; x486, copying x482 here, cause x482 is needed in a reg for other than x486, namely all: , x486, x488, size: 2
shrd rdx, rax, 58; x486 <- x484||x482 >> 58
shr rax, 58; x487 <- x484>> 58
mov r14, 0x3a ; moving imm to reg
bzhi rcx, rcx, r14; x488 <- x482 (only least 0x3a bits)
mov rdi, rdx; preserving value of x486 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r15, r8, [ r13 + 0x30 ]; x150, x149<- arg1[0] * arg2[6]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbp, r14, [ r13 + 0x28 ]; x134, x133<- arg1[1] * arg2[5]
mov rdx, [ r13 + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x378 ], rcx; spilling x488 to mem
mulx r9, rcx, [ rsi + 0x10 ]; x120, x119<- arg1[2] * arg2[4]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x380 ], rax; spilling x487 to mem
mov [ rsp + 0x388 ], r15; spilling x150 to mem
mulx rax, r15, [ r13 + 0x18 ]; x108, x107<- arg1[3] * arg2[3]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x390 ], rbp; spilling x134 to mem
mov [ rsp + 0x398 ], r9; spilling x120 to mem
mulx rbp, r9, [ r13 + 0x10 ]; x98, x97<- arg1[4] * arg2[2]
mov rdx, [ r13 + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x3a0 ], rax; spilling x108 to mem
mov [ rsp + 0x3a8 ], rbp; spilling x98 to mem
mulx rax, rbp, [ rsi + 0x28 ]; x90, x89<- arg1[5] * arg2[1]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x3b0 ], rax; spilling x90 to mem
mov [ rsp + 0x3b8 ], rdi; spilling x486 to mem
mulx rax, rdi, [ r13 + 0x0 ]; x84, x83<- arg1[6] * arg2[0]
mov rdx, r10; x10000 to rdx
mov [ rsp + 0x3c0 ], rax; spilling x84 to mem
mulx r10, rax, [ rsi + 0x38 ]; x18, x17<- arg1[7] * x10000
mov [ rsp + 0x3c8 ], r10; spilling x18 to mem
mov r10, rdx; preserving value of x10000 into a new reg
mov rdx, [ rsi + 0x40 ]; saving arg1[8] in rdx.
mov [ rsp + 0x3d0 ], r8; spilling x149 to mem
mulx r11, r8, r11; x4, x3<- arg1[8] * x10001
adox r8, rax
clc;
adcx r8, rdi
seto dil; spill OF x263 to reg (rdi)
mov rax, -0x2 ; moving imm to reg
inc rax; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, rbp
setc bpl; spill CF x267 to reg (rbp)
clc;
adcx r8, r9
setc r9b; spill CF x275 to reg (r9)
clc;
adcx r8, r15
setc r15b; spill CF x279 to reg (r15)
clc;
adcx r8, rcx
setc cl; spill CF x283 to reg (rcx)
clc;
adcx r8, r14
setc r14b; spill CF x287 to reg (r14)
clc;
adcx r8, [ rsp + 0x3d0 ]
setc al; spill CF x291 to reg (rax)
clc;
adcx r8, [ rsp + 0x3b8 ]
movzx rdi, dil
lea r11, [ rdi + r11 ]
mov rdi, [ rsp + 0x3c8 ]
lea r11, [rdi+r11]
movzx rbp, bpl
lea r11, [ rbp + r11 ]
mov rbp, [ rsp + 0x3c0 ]
lea r11, [rbp+r11]
adox r11, [ rsp + 0x3b0 ]
movzx r9, r9b
lea r11, [ r9 + r11 ]
mov r9, [ rsp + 0x3a8 ]
lea r11, [r9+r11]
movzx r15, r15b
lea r11, [ r15 + r11 ]
mov r15, [ rsp + 0x3a0 ]
lea r11, [r15+r11]
movzx rcx, cl
lea r11, [ rcx + r11 ]
mov rcx, [ rsp + 0x398 ]
lea r11, [rcx+r11]
movzx r14, r14b
lea r11, [ r14 + r11 ]
mov r14, [ rsp + 0x390 ]
lea r11, [r14+r11]
movzx rax, al
lea r11, [ rax + r11 ]
mov rax, [ rsp + 0x388 ]
lea r11, [rax+r11]
adcx r11, [ rsp + 0x380 ]
mov rdi, r8; x493, copying x489 here, cause x489 is needed in a reg for other than x493, namely all: , x493, x495, size: 2
shrd rdi, r11, 58; x493 <- x491||x489 >> 58
shr r11, 58; x494 <- x491>> 58
mov rbp, 0x3ffffffffffffff ; moving imm to reg
and r8, rbp; x495 <- x489&0x3ffffffffffffff
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r9, r15, [ r13 + 0x38 ]; x148, x147<- arg1[0] * arg2[7]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rcx, r14, [ r13 + 0x30 ]; x132, x131<- arg1[1] * arg2[6]
mov rdx, [ r13 + 0x20 ]; arg2[4] to rdx
mulx rax, rbp, [ rsi + 0x18 ]; x106, x105<- arg1[3] * arg2[4]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x3d8 ], r8; spilling x495 to mem
mov [ rsp + 0x3e0 ], r11; spilling x494 to mem
mulx r8, r11, [ r13 + 0x28 ]; x118, x117<- arg1[2] * arg2[5]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x3e8 ], r9; spilling x148 to mem
mov [ rsp + 0x3f0 ], rcx; spilling x132 to mem
mulx r9, rcx, [ r13 + 0x18 ]; x96, x95<- arg1[4] * arg2[3]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x3f8 ], r8; spilling x118 to mem
mov [ rsp + 0x400 ], rax; spilling x106 to mem
mulx r8, rax, [ r13 + 0x10 ]; x88, x87<- arg1[5] * arg2[2]
mov rdx, [ r13 + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x408 ], r9; spilling x96 to mem
mov [ rsp + 0x410 ], r8; spilling x88 to mem
mulx r9, r8, [ rsi + 0x30 ]; x82, x81<- arg1[6] * arg2[1]
mov rdx, [ r13 + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x418 ], r9; spilling x82 to mem
mov [ rsp + 0x420 ], rdi; spilling x493 to mem
mulx r9, rdi, [ rsi + 0x38 ]; x78, x77<- arg1[7] * arg2[0]
mov rdx, r10; x10000 to rdx
mulx rdx, r10, [ rsi + 0x40 ]; x2, x1<- arg1[8] * x10000
adox r10, rdi
adcx r10, r8
setc r8b; spill CF x235 to reg (r8)
clc;
adcx r10, rax
seto al; spill OF x231 to reg (rax)
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r10, rcx
setc cl; spill CF x239 to reg (rcx)
clc;
adcx r10, rbp
setc bpl; spill CF x247 to reg (rbp)
clc;
adcx r10, r11
setc r11b; spill CF x251 to reg (r11)
clc;
adcx r10, r14
setc r14b; spill CF x255 to reg (r14)
clc;
adcx r10, r15
setc r15b; spill CF x259 to reg (r15)
clc;
adcx r10, [ rsp + 0x420 ]
movzx rax, al
lea r9, [ r9 + rdx ]
lea r9, [ r9 + rax ]
movzx r8, r8b
lea r9, [ r8 + r9 ]
mov r8, [ rsp + 0x418 ]
lea r9, [r8+r9]
movzx rcx, cl
lea r9, [ rcx + r9 ]
mov rcx, [ rsp + 0x410 ]
lea r9, [rcx+r9]
adox r9, [ rsp + 0x408 ]
movzx rbp, bpl
lea r9, [ rbp + r9 ]
mov rbp, [ rsp + 0x400 ]
lea r9, [rbp+r9]
movzx r11, r11b
lea r9, [ r11 + r9 ]
mov r11, [ rsp + 0x3f8 ]
lea r9, [r11+r9]
movzx r14, r14b
lea r9, [ r14 + r9 ]
mov r14, [ rsp + 0x3f0 ]
lea r9, [r14+r9]
movzx r15, r15b
lea r9, [ r15 + r9 ]
mov r15, [ rsp + 0x3e8 ]
lea r9, [r15+r9]
adcx r9, [ rsp + 0x3e0 ]
mov rdx, r10; x500, copying x496 here, cause x496 is needed in a reg for other than x500, namely all: , x500, x502, size: 2
shrd rdx, r9, 58; x500 <- x498||x496 >> 58
shr r9, 58; x501 <- x498>> 58
mov rax, 0x3a ; moving imm to reg
bzhi r10, r10, rax; x502 <- x496 (only least 0x3a bits)
mov r8, rdx; preserving value of x500 into a new reg
mov rdx, [ r13 + 0x40 ]; saving arg2[8] in rdx.
mulx rdx, rcx, [ rsi + 0x0 ]; x146, x145<- arg1[0] * arg2[8]
mov rbp, rdx; preserving value of x146 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r11, r14, [ r13 + 0x38 ]; x130, x129<- arg1[1] * arg2[7]
mov rdx, [ r13 + 0x30 ]; arg2[6] to rdx
mulx r15, rax, [ rsi + 0x10 ]; x116, x115<- arg1[2] * arg2[6]
mov rdx, [ r13 + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x428 ], r10; spilling x502 to mem
mulx rdi, r10, [ rsi + 0x18 ]; x104, x103<- arg1[3] * arg2[5]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x430 ], r9; spilling x501 to mem
mov [ rsp + 0x438 ], rbp; spilling x146 to mem
mulx r9, rbp, [ r13 + 0x20 ]; x94, x93<- arg1[4] * arg2[4]
mov rdx, [ r13 + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x440 ], r11; spilling x130 to mem
mov [ rsp + 0x448 ], r15; spilling x116 to mem
mulx r11, r15, [ rsi + 0x28 ]; x86, x85<- arg1[5] * arg2[3]
mov rdx, [ r13 + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x450 ], rdi; spilling x104 to mem
mov [ rsp + 0x458 ], r9; spilling x94 to mem
mulx rdi, r9, [ rsi + 0x30 ]; x80, x79<- arg1[6] * arg2[2]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x460 ], r11; spilling x86 to mem
mov [ rsp + 0x468 ], rdi; spilling x80 to mem
mulx r11, rdi, [ r13 + 0x8 ]; x76, x75<- arg1[7] * arg2[1]
mov rdx, [ rsi + 0x40 ]; arg1[8] to rdx
mov [ rsp + 0x470 ], r11; spilling x76 to mem
mov [ rsp + 0x478 ], r8; spilling x500 to mem
mulx r11, r8, [ r13 + 0x0 ]; x74, x73<- arg1[8] * arg2[0]
adox r8, rdi
clc;
adcx r8, r9
seto r9b; spill OF x199 to reg (r9)
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, r15
seto r15b; spill OF x207 to reg (r15)
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r8, rbp
setc bpl; spill CF x203 to reg (rbp)
clc;
adcx r8, r10
setc r10b; spill CF x215 to reg (r10)
clc;
adcx r8, rax
seto al; spill OF x211 to reg (rax)
mov byte [ rsp + 0x480 ], r10b; spilling byte x215 to mem
mov r10, -0x3 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r8, r14
setc r14b; spill CF x219 to reg (r14)
clc;
adcx r8, rcx
seto cl; spill OF x223 to reg (rcx)
mov r10, -0x3 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r8, [ rsp + 0x478 ]
movzx r9, r9b
lea r11, [ r9 + r11 ]
mov r9, [ rsp + 0x470 ]
lea r11, [r9+r11]
movzx rbp, bpl
lea r11, [ rbp + r11 ]
mov rbp, [ rsp + 0x468 ]
lea r11, [rbp+r11]
movzx r15, r15b
lea r11, [ r15 + r11 ]
mov r15, [ rsp + 0x460 ]
lea r11, [r15+r11]
movzx rax, al
lea r11, [ rax + r11 ]
mov rax, [ rsp + 0x458 ]
lea r11, [rax+r11]
movzx r9, byte [ rsp + 0x480 ]; load byte memx215 to register64
lea r11, [ r9 + r11 ]
mov r9, [ rsp + 0x450 ]
lea r11, [r9+r11]
movzx r14, r14b
lea r11, [ r14 + r11 ]
mov r14, [ rsp + 0x448 ]
lea r11, [r14+r11]
movzx rcx, cl
lea r11, [ rcx + r11 ]
mov rcx, [ rsp + 0x440 ]
lea r11, [rcx+r11]
adcx r11, [ rsp + 0x438 ]
adox r11, [ rsp + 0x430 ]
mov rbp, r8; x507, copying x503 here, cause x503 is needed in a reg for other than x507, namely all: , x507, x509, size: 2
shrd rbp, r11, 57; x507 <- x505||x503 >> 57
shr r11, 57; x508 <- x505>> 57
mov r15, 0x1ffffffffffffff ; moving imm to reg
and r8, r15; x509 <- x503&0x1ffffffffffffff
adox rbp, [ rsp + 0xc0 ]
adox r11, rdi
mov rax, rbp; x513, copying x510 here, cause x510 is needed in a reg for other than x513, namely all: , x513, x514, size: 2
shrd rax, r11, 58; x513 <- x512||x510 >> 58
mov r9, 0x3a ; moving imm to reg
bzhi rbp, rbp, r9; x514 <- x510 (only least 0x3a bits)
add rax, [ rsp + 0x150 ]
mov r14, rax; x516, copying x515 here, cause x515 is needed in a reg for other than x516, namely all: , x516, x517, size: 2
shr r14, 58; x516 <- x515>> 58
mov rcx, 0x3ffffffffffffff ; moving imm to reg
and rax, rcx; x517 <- x515&0x3ffffffffffffff
add r14, [ rsp + 0x1e0 ]
mov r11, [ rsp + 0x30 ]; load m64 out1 to register64
mov [ r11 + 0x0 ], rbp; out1[0] = x514
mov [ r11 + 0x8 ], rax; out1[1] = x517
mov [ r11 + 0x10 ], r14; out1[2] = x518
mov rbp, [ rsp + 0x270 ]; TMP = x474
mov [ r11 + 0x18 ], rbp; out1[3] = TMP
mov rbp, [ rsp + 0x300 ]; TMP = x481
mov [ r11 + 0x20 ], rbp; out1[4] = TMP
mov rbp, [ rsp + 0x378 ]; TMP = x488
mov [ r11 + 0x28 ], rbp; out1[5] = TMP
mov rbp, [ rsp + 0x3d8 ]; TMP = x495
mov [ r11 + 0x30 ], rbp; out1[6] = TMP
mov rbp, [ rsp + 0x428 ]; TMP = x502
mov [ r11 + 0x38 ], rbp; out1[7] = TMP
mov [ r11 + 0x40 ], r8; out1[8] = x509
mov r15, [ rsp + 0x0 ] ; pop
mov r14, [ rsp + 0x8 ] ; pop
mov r13, [ rsp + 0x10 ] ; pop
mov r12, [ rsp + 0x18 ] ; pop
mov rbp, [ rsp + 0x20 ] ; pop
mov rbx, [ rsp + 0x28 ] ; pop
add rsp, 0x488 
ret
; cpu Intel(R) Core(TM) i5-8265U CPU @ 1.60GHz
; ratio 0.7967
; seed 1785685356 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3598 ms / 10 evals=> 359.8ms/eval
; Time spent for assembling and measureing (initial batch_size=34, initial num_batches=31): 78 ms
; number of used evaluations: 10
; Ratio (time for assembling + measure)/(total runtime for 10 evals): 0.0216787103946637
; number reverted permutation/ tried permutation: 1 / 3 =33.333%
; number reverted decision/ tried decision: 5 / 7 =71.429%