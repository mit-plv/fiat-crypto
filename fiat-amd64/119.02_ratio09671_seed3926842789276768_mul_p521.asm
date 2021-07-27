SECTION .text
	GLOBAL mul_p521
mul_p521:
sub rsp, 0x3a8 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x378 ], rbx; saving to stack
mov [ rsp + 0x380 ], rbp; saving to stack
mov [ rsp + 0x388 ], r12; saving to stack
mov [ rsp + 0x390 ], r13; saving to stack
mov [ rsp + 0x398 ], r14; saving to stack
mov [ rsp + 0x3a0 ], r15; saving to stack
imul rax, [ rdx + 0x10 ], 0x2; x10006 <- arg2[2] * 0x2
mov r10, rdx; preserving value of arg2 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r11, rbx, [ r10 + 0x0 ]; x162, x161<- arg1[0] * arg2[0]
imul rbp, [ r10 + 0x38 ], 0x2; x10001 <- arg2[7] * 0x2
imul r12, [ r10 + 0x40 ], 0x2; x10000 <- arg2[8] * 0x2
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r13, r14, rbp; x70, x69<- arg1[2] * x10001
imul r15, [ r10 + 0x30 ], 0x2; x10002 <- arg2[6] * 0x2
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rcx, r8, r15; x66, x65<- arg1[3] * x10002
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r9, rdi, r12; x72, x71<- arg1[1] * x10000
mov [ rsp + 0x8 ], r11; spilling x162 to mem
imul r11, [ r10 + 0x28 ], 0x2; x10003 <- arg2[5] * 0x2
mov [ rsp + 0x10 ], r9; spilling x72 to mem
imul r9, [ r10 + 0x18 ], 0x2; x10005 <- arg2[3] * 0x2
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x18 ], r13; spilling x70 to mem
mov [ rsp + 0x20 ], rcx; spilling x66 to mem
mulx r13, rcx, r11; x60, x59<- arg1[4] * x10003
mov [ rsp + 0x28 ], r13; spilling x60 to mem
imul r13, [ r10 + 0x20 ], 0x2; x10004 <- arg2[4] * 0x2
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x30 ], rbx; spilling x161 to mem
mov [ rsp + 0x38 ], rdi; spilling x71 to mem
mulx rbx, rdi, r13; x52, x51<- arg1[5] * x10004
mov [ rsp + 0x40 ], rbx; spilling x52 to mem
imul rbx, [ r10 + 0x8 ], 0x2; x10007 <- arg2[1] * 0x2
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x48 ], r14; spilling x69 to mem
mov [ rsp + 0x50 ], r8; spilling x65 to mem
mulx r14, r8, rax; x30, x29<- arg1[7] * x10006
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x58 ], r14; spilling x30 to mem
mov [ rsp + 0x60 ], rcx; spilling x59 to mem
mulx r14, rcx, r9; x42, x41<- arg1[6] * x10005
mov rdx, [ rsi + 0x40 ]; arg1[8] to rdx
mov [ rsp + 0x68 ], rbp; spilling x10001 to mem
mulx rbx, rbp, rbx; x16, x15<- arg1[8] * x10007
add rbp, r8; could be done better, if r0 has been u8 as well
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, rcx
setc cl; spill CF x164 to reg (rcx)
clc;
adcx rbp, rdi
setc dil; spill CF x172 to reg (rdi)
clc;
adcx rbp, [ rsp + 0x60 ]
setc r8b; spill CF x176 to reg (r8)
clc;
adcx rbp, [ rsp + 0x50 ]
mov [ rsp + 0x70 ], r15; spilling x10002 to mem
seto r15b; spill OF x168 to reg (r15)
mov byte [ rsp + 0x78 ], r8b; spilling byte x176 to mem
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, [ rsp + 0x48 ]
movzx rcx, cl
lea rbx, [ rcx + rbx ]
mov rcx, [ rsp + 0x58 ]
lea rbx, [rcx+rbx]
setc cl; spill CF x180 to reg (rcx)
clc;
adcx rbp, [ rsp + 0x38 ]
seto r8b; spill OF x184 to reg (r8)
mov [ rsp + 0x80 ], r12; spilling x10000 to mem
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, [ rsp + 0x30 ]
movzx r15, r15b
lea r14, [ r14 + rbx ]
lea r14, [ r14 + r15 ]
mov rdx, [ r10 + 0x8 ]; arg2[1] to rdx
mulx r15, rbx, [ rsi + 0x0 ]; x160, x159<- arg1[0] * arg2[1]
movzx rdi, dil
lea r14, [ rdi + r14 ]
mov rdi, [ rsp + 0x40 ]
lea r14, [rdi+r14]
movzx rdi, byte [ rsp + 0x78 ]; load byte memx176 to register64
lea r14, [ rdi + r14 ]
mov rdi, [ rsp + 0x28 ]
lea r14, [rdi+r14]
movzx rcx, cl
lea r14, [ rcx + r14 ]
mov rcx, [ rsp + 0x20 ]
lea r14, [rcx+r14]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rdi, rcx, [ rsp + 0x80 ]; x68, x67<- arg1[2] * x10000
movzx r8, r8b
lea r14, [ r8 + r14 ]
mov r8, [ rsp + 0x18 ]
lea r14, [r8+r14]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mulx r8, r12, r13; x40, x39<- arg1[6] * x10004
mov rdx, [ r10 + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x88 ], r15; spilling x160 to mem
mov [ rsp + 0x90 ], rdi; spilling x68 to mem
mulx r15, rdi, [ rsi + 0x8 ]; x144, x143<- arg1[1] * arg2[0]
adcx r14, [ rsp + 0x10 ]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x98 ], r15; spilling x144 to mem
mov [ rsp + 0xa0 ], r8; spilling x40 to mem
mulx r15, r8, [ rsp + 0x70 ]; x58, x57<- arg1[4] * x10002
adox r14, [ rsp + 0x8 ]
mov [ rsp + 0xa8 ], r15; spilling x58 to mem
mov r15, rbp; x195, copying x191 here, cause x191 is needed in a reg for other than x195, namely all: , x195, x197, size: 2
shrd r15, r14, 58; x195 <- x193||x191 >> 58
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0xb0 ], r15; spilling x195 to mem
mov [ rsp + 0xb8 ], rbx; spilling x159 to mem
mulx r15, rbx, [ rsp + 0x68 ]; x64, x63<- arg1[3] * x10001
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0xc0 ], r15; spilling x64 to mem
mov [ rsp + 0xc8 ], rdi; spilling x143 to mem
mulx r15, rdi, r9; x28, x27<- arg1[7] * x10005
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0xd0 ], r15; spilling x28 to mem
mov [ rsp + 0xd8 ], rcx; spilling x67 to mem
mulx r15, rcx, r11; x50, x49<- arg1[5] * x10003
mov rdx, rax; x10006 to rdx
mulx rdx, rax, [ rsi + 0x40 ]; x14, x13<- arg1[8] * x10006
mov [ rsp + 0xe0 ], r15; spilling x50 to mem
xor r15, r15
adox rax, rdi
adcx rax, r12
seto r12b; spill OF x423 to reg (r12)
mov rdi, -0x3 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rax, rcx
setc cl; spill CF x427 to reg (rcx)
clc;
adcx rax, r8
setc r8b; spill CF x435 to reg (r8)
clc;
adcx rax, rbx
setc bl; spill CF x439 to reg (rbx)
clc;
adcx rax, [ rsp + 0xd8 ]
setc dil; spill CF x443 to reg (rdi)
clc;
adcx rax, [ rsp + 0xc8 ]
mov byte [ rsp + 0xe8 ], dil; spilling byte x443 to mem
setc dil; spill CF x447 to reg (rdi)
clc;
adcx rax, [ rsp + 0xb8 ]
mov byte [ rsp + 0xf0 ], dil; spilling byte x447 to mem
setc dil; spill CF x451 to reg (rdi)
clc;
adcx rax, [ rsp + 0xb0 ]
setc r15b; spill CF x455 to reg (r15)
mov [ rsp + 0xf8 ], rax; spilling x454 to mem
seto al; spill OF x431 to reg (rax)
shr r14, 58; x196 <- x193>> 58
sar  r12b, 1
adcx rdx, [ rsp + 0xd0 ]
sar  cl, 1
adcx rdx, [ rsp + 0xa0 ]
sar  al, 1
adcx rdx, [ rsp + 0xe0 ]
sar  r8b, 1
adcx rdx, [ rsp + 0xa8 ]
sar  bl, 1
adcx rdx, [ rsp + 0xc0 ]
sar byte [ rsp + 0xe8 ], 1
adcx rdx, [ rsp + 0x90 ]
sar byte [ rsp + 0xf0 ], 1
adcx rdx, [ rsp + 0x98 ]
sar  dil, 1
adcx rdx, [ rsp + 0x88 ]
sar  r15b, 1
adcx r14, rdx
mov r12, [ rsp + 0xf8 ]; load m64 x454 to register64
mov rcx, r12; x458, copying x454 here, cause x454 is needed in a reg for other than x458, namely all: , x460, x458, size: 2
shrd rcx, r14, 58; x458 <- x456||x454 >> 58
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mulx rax, r8, [ rsp + 0x70 ]; x48, x47<- arg1[5] * x10002
mov rdx, [ r10 + 0x10 ]; arg2[2] to rdx
mulx rbx, rdi, [ rsi + 0x0 ]; x158, x157<- arg1[0] * arg2[2]
mov rdx, r13; x10004 to rdx
mulx r13, r15, [ rsi + 0x38 ]; x26, x25<- arg1[7] * x10004
mov [ rsp + 0x100 ], rbx; spilling x158 to mem
mov rbx, rdx; preserving value of x10004 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x108 ], rax; spilling x48 to mem
mov [ rsp + 0x110 ], rcx; spilling x458 to mem
mulx rax, rcx, [ rsp + 0x68 ]; x56, x55<- arg1[4] * x10001
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x118 ], rax; spilling x56 to mem
mov [ rsp + 0x120 ], r13; spilling x26 to mem
mulx rax, r13, [ rsp + 0x80 ]; x62, x61<- arg1[3] * x10000
mov rdx, r11; x10003 to rdx
mov [ rsp + 0x128 ], rax; spilling x62 to mem
mulx r11, rax, [ rsi + 0x30 ]; x38, x37<- arg1[6] * x10003
mov [ rsp + 0x130 ], r11; spilling x38 to mem
mov r11, rdx; preserving value of x10003 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x138 ], rdi; spilling x157 to mem
mov [ rsp + 0x140 ], r13; spilling x61 to mem
mulx rdi, r13, [ r10 + 0x8 ]; x142, x141<- arg1[1] * arg2[1]
mov rdx, [ r10 + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x148 ], rdi; spilling x142 to mem
mov [ rsp + 0x150 ], r13; spilling x141 to mem
mulx rdi, r13, [ rsi + 0x10 ]; x128, x127<- arg1[2] * arg2[0]
mov rdx, r9; x10005 to rdx
mulx rdx, r9, [ rsi + 0x40 ]; x12, x11<- arg1[8] * x10005
test al, al
adox r9, r15
adcx r9, rax
seto r15b; spill OF x391 to reg (r15)
mov rax, -0x2 ; moving imm to reg
inc rax; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r9, r8
setc r8b; spill CF x395 to reg (r8)
clc;
adcx r9, rcx
setc cl; spill CF x403 to reg (rcx)
clc;
adcx r9, [ rsp + 0x140 ]
seto al; spill OF x399 to reg (rax)
mov [ rsp + 0x158 ], rdi; spilling x128 to mem
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r9, r13
seto r13b; spill OF x411 to reg (r13)
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r9, [ rsp + 0x150 ]
mov byte [ rsp + 0x160 ], r13b; spilling byte x411 to mem
setc r13b; spill CF x407 to reg (r13)
clc;
adcx r9, [ rsp + 0x138 ]
setc dil; spill CF x419 to reg (rdi)
mov byte [ rsp + 0x168 ], r13b; spilling byte x407 to mem
seto r13b; spill OF x415 to reg (r13)
shr r14, 58; x459 <- x456>> 58
sar  r15b, 1
adcx rdx, [ rsp + 0x120 ]
adox r9, [ rsp + 0x110 ]
movzx r8, r8b
lea rdx, [ r8 + rdx ]
mov r8, [ rsp + 0x130 ]
lea rdx, [r8+rdx]
movzx rax, al
lea rdx, [ rax + rdx ]
mov rax, [ rsp + 0x108 ]
lea rdx, [rax+rdx]
mov r15, 0x3ffffffffffffff ; moving imm to reg
seto r8b; spill OF x462 to reg (r8)
mov rax, r9; x467, copying x461 here, cause x461 is needed in a reg for other than x467, namely all: , x465, x467, size: 2
and rax, r15; x467 <- x461&0x3ffffffffffffff
sar  cl, 1
adcx rdx, [ rsp + 0x118 ]
sar byte [ rsp + 0x168 ], 1
adcx rdx, [ rsp + 0x128 ]
sar byte [ rsp + 0x160 ], 1
adcx rdx, [ rsp + 0x158 ]
mov rcx, rdx; preserving value of x412 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x170 ], rax; spilling x467 to mem
mulx r15, rax, [ rsp + 0x80 ]; x54, x53<- arg1[4] * x10000
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x178 ], r15; spilling x54 to mem
mov [ rsp + 0x180 ], rax; spilling x53 to mem
mulx r15, rax, [ r10 + 0x18 ]; x156, x155<- arg1[0] * arg2[3]
mov rdx, [ r10 + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x188 ], r15; spilling x156 to mem
mov [ rsp + 0x190 ], rax; spilling x155 to mem
mulx r15, rax, [ rsi + 0x8 ]; x140, x139<- arg1[1] * arg2[2]
sar  r13b, 1
adcx rcx, [ rsp + 0x148 ]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x198 ], r15; spilling x140 to mem
mulx r13, r15, r11; x24, x23<- arg1[7] * x10003
mov rdx, [ r10 + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x1a0 ], r13; spilling x24 to mem
mov [ rsp + 0x1a8 ], rax; spilling x139 to mem
mulx r13, rax, [ rsi + 0x18 ]; x114, x113<- arg1[3] * arg2[0]
sar  dil, 1
adcx rcx, [ rsp + 0x100 ]
sar  r8b, 1
adcx r14, rcx
mov rdx, [ r10 + 0x8 ]; arg2[1] to rdx
mulx rdi, r8, [ rsi + 0x10 ]; x126, x125<- arg1[2] * arg2[1]
shrd r9, r14, 58; x465 <- x463||x461 >> 58
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x1b0 ], rdi; spilling x126 to mem
mulx rcx, rdi, [ rsp + 0x68 ]; x46, x45<- arg1[5] * x10001
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x1b8 ], r13; spilling x114 to mem
mov [ rsp + 0x1c0 ], rcx; spilling x46 to mem
mulx r13, rcx, [ rsp + 0x70 ]; x36, x35<- arg1[6] * x10002
mov rdx, rbx; x10004 to rdx
mulx rdx, rbx, [ rsi + 0x40 ]; x10, x9<- arg1[8] * x10004
mov [ rsp + 0x1c8 ], r13; spilling x36 to mem
xor r13, r13
adox rbx, r15
adcx rbx, rcx
setc r15b; spill CF x363 to reg (r15)
clc;
adcx rbx, rdi
setc dil; spill CF x367 to reg (rdi)
clc;
adcx rbx, [ rsp + 0x180 ]
setc cl; spill CF x371 to reg (rcx)
clc;
adcx rbx, rax
setc al; spill CF x375 to reg (rax)
clc;
adcx rbx, r8
setc r8b; spill CF x379 to reg (r8)
clc;
adcx rbx, [ rsp + 0x1a8 ]
adox rdx, [ rsp + 0x1a0 ]
mov byte [ rsp + 0x1d0 ], r8b; spilling byte x379 to mem
mov r8, -0x3 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbx, [ rsp + 0x190 ]
setc r8b; spill CF x383 to reg (r8)
clc;
adcx rbx, r9
setc r9b; spill CF x469 to reg (r9)
seto r13b; spill OF x387 to reg (r13)
shr r14, 58; x466 <- x463>> 58
sar  r15b, 1
adcx rdx, [ rsp + 0x1c8 ]
sar  dil, 1
adcx rdx, [ rsp + 0x1c0 ]
sar  cl, 1
adcx rdx, [ rsp + 0x178 ]
sar  al, 1
adcx rdx, [ rsp + 0x1b8 ]
mov r15, 0x3ffffffffffffff ; moving imm to reg
and rbp, r15; x197 <- x191&0x3ffffffffffffff
sar byte [ rsp + 0x1d0 ], 1
adcx rdx, [ rsp + 0x1b0 ]
sar  r8b, 1
adcx rdx, [ rsp + 0x198 ]
sar  r13b, 1
adcx rdx, [ rsp + 0x188 ]
sar  r9b, 1
adcx r14, rdx
mov rdi, r14; x473, copying x470 here, cause x470 is needed in a reg for other than x473, namely all: , x472, x473, size: 2
shr rdi, 58; x473 <- x470>> 58
mov rdx, [ r10 + 0x18 ]; arg2[3] to rdx
mulx rcx, rax, [ rsi + 0x8 ]; x138, x137<- arg1[1] * arg2[3]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mulx r8, r13, [ rsp + 0x80 ]; x44, x43<- arg1[5] * x10000
mov r9, rbx; x472, copying x468 here, cause x468 is needed in a reg for other than x472, namely all: , x472, x474, size: 2
shrd r9, r14, 58; x472 <- x470||x468 >> 58
and rbx, r15; x474 <- x468&0x3ffffffffffffff
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r14, r15, [ r10 + 0x10 ]; x124, x123<- arg1[2] * arg2[2]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x1d8 ], rbx; spilling x474 to mem
mov [ rsp + 0x1e0 ], rbp; spilling x197 to mem
mulx rbx, rbp, [ rsp + 0x68 ]; x34, x33<- arg1[6] * x10001
mov rdx, [ r10 + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x1e8 ], rdi; spilling x473 to mem
mov [ rsp + 0x1f0 ], r9; spilling x472 to mem
mulx rdi, r9, [ rsi + 0x18 ]; x112, x111<- arg1[3] * arg2[1]
mov rdx, [ r10 + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x1f8 ], rcx; spilling x138 to mem
mov [ rsp + 0x200 ], r14; spilling x124 to mem
mulx rcx, r14, [ rsi + 0x0 ]; x154, x153<- arg1[0] * arg2[4]
mov rdx, [ rsi + 0x40 ]; arg1[8] to rdx
mov [ rsp + 0x208 ], rcx; spilling x154 to mem
mulx r11, rcx, r11; x8, x7<- arg1[8] * x10003
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x210 ], rdi; spilling x112 to mem
mov [ rsp + 0x218 ], r8; spilling x44 to mem
mulx rdi, r8, [ rsp + 0x70 ]; x22, x21<- arg1[7] * x10002
mov rdx, [ r10 + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x220 ], r14; spilling x153 to mem
mov [ rsp + 0x228 ], rax; spilling x137 to mem
mulx r14, rax, [ rsi + 0x20 ]; x102, x101<- arg1[4] * arg2[0]
adox rcx, r8
adox rdi, r11
adcx rcx, rbp
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rcx, r13
adcx rbx, rdi
clc;
adcx rcx, rax
seto r13b; spill OF x335 to reg (r13)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rcx, r9
mov rdx, [ r10 + 0x20 ]; arg2[4] to rdx
mulx r9, r11, [ rsi + 0x8 ]; x136, x135<- arg1[1] * arg2[4]
setc r8b; spill CF x339 to reg (r8)
clc;
adcx rcx, r15
setc r15b; spill CF x347 to reg (r15)
clc;
adcx rcx, [ rsp + 0x228 ]
seto al; spill OF x343 to reg (rax)
mov rdi, -0x3 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rcx, [ rsp + 0x220 ]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx rbp, rdi, [ rsp + 0x68 ]; x20, x19<- arg1[7] * x10001
movzx r13, r13b
lea rbx, [ r13 + rbx ]
mov r13, [ rsp + 0x218 ]
lea rbx, [r13+rbx]
movzx r8, r8b
lea r14, [ r14 + rbx ]
lea r14, [ r14 + r8 ]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mulx r13, r8, [ r10 + 0x0 ]; x92, x91<- arg1[5] * arg2[0]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x230 ], r9; spilling x136 to mem
mulx rbx, r9, [ r10 + 0x28 ]; x152, x151<- arg1[0] * arg2[5]
movzx rax, al
lea r14, [ rax + r14 ]
mov rax, [ rsp + 0x210 ]
lea r14, [rax+r14]
movzx r15, r15b
lea r14, [ r15 + r14 ]
mov r15, [ rsp + 0x200 ]
lea r14, [r15+r14]
mov rdx, [ r10 + 0x10 ]; arg2[2] to rdx
mulx rax, r15, [ rsi + 0x18 ]; x110, x109<- arg1[3] * arg2[2]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x238 ], rbx; spilling x152 to mem
mov [ rsp + 0x240 ], r9; spilling x151 to mem
mulx rbx, r9, [ rsp + 0x80 ]; x32, x31<- arg1[6] * x10000
adcx r14, [ rsp + 0x1f8 ]
clc;
adcx rcx, [ rsp + 0x1f0 ]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x248 ], rax; spilling x110 to mem
mov [ rsp + 0x250 ], r11; spilling x135 to mem
mulx rax, r11, [ r10 + 0x18 ]; x122, x121<- arg1[2] * arg2[3]
adox r14, [ rsp + 0x208 ]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x258 ], rax; spilling x122 to mem
mov [ rsp + 0x260 ], r11; spilling x121 to mem
mulx rax, r11, [ r10 + 0x8 ]; x100, x99<- arg1[4] * arg2[1]
mov rdx, [ rsp + 0x70 ]; x10002 to rdx
mov [ rsp + 0x268 ], rax; spilling x100 to mem
mulx rdx, rax, [ rsi + 0x40 ]; x6, x5<- arg1[8] * x10002
adcx r14, [ rsp + 0x1e8 ]
mov [ rsp + 0x270 ], r13; spilling x92 to mem
xor r13, r13
adox rax, rdi
seto dil; spill OF x295 to reg (rdi)
mov r13, rcx; x479, copying x475 here, cause x475 is needed in a reg for other than x479, namely all: , x479, x481, size: 2
shrd r13, r14, 58; x479 <- x477||x475 >> 58
test al, al
adox rax, r9
adcx rax, r8
movzx rdi, dil
lea rbp, [ rbp + rdx ]
lea rbp, [ rbp + rdi ]
setc r8b; spill CF x303 to reg (r8)
clc;
adcx rax, r11
setc r9b; spill CF x307 to reg (r9)
clc;
adcx rax, r15
adox rbx, rbp
setc r15b; spill CF x311 to reg (r15)
shr r14, 58; x480 <- x477>> 58
sar  r8b, 1
adcx rbx, [ rsp + 0x270 ]
mov rdx, [ r10 + 0x8 ]; arg2[1] to rdx
mulx r11, rdi, [ rsi + 0x28 ]; x90, x89<- arg1[5] * arg2[1]
adox rax, [ rsp + 0x260 ]
clc;
adcx rax, [ rsp + 0x250 ]
movzx r9, r9b
lea rbx, [ r9 + rbx ]
mov r9, [ rsp + 0x268 ]
lea rbx, [r9+rbx]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mulx r8, rbp, [ r10 + 0x0 ]; x84, x83<- arg1[6] * arg2[0]
movzx r15, r15b
lea rbx, [ r15 + rbx ]
mov r15, [ rsp + 0x248 ]
lea rbx, [r15+rbx]
adox rbx, [ rsp + 0x258 ]
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rax, [ rsp + 0x240 ]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r15, r9, [ r10 + 0x10 ]; x98, x97<- arg1[4] * arg2[2]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x278 ], r15; spilling x98 to mem
mov [ rsp + 0x280 ], r11; spilling x90 to mem
mulx r15, r11, [ r10 + 0x28 ]; x134, x133<- arg1[1] * arg2[5]
adcx rbx, [ rsp + 0x230 ]
clc;
adcx rax, r13
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x288 ], r15; spilling x134 to mem
mulx r13, r15, [ r10 + 0x18 ]; x108, x107<- arg1[3] * arg2[3]
adox rbx, [ rsp + 0x238 ]
adcx r14, rbx
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x290 ], r13; spilling x108 to mem
mulx rbx, r13, [ r10 + 0x20 ]; x120, x119<- arg1[2] * arg2[4]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x298 ], rbx; spilling x120 to mem
mov [ rsp + 0x2a0 ], r11; spilling x133 to mem
mulx rbx, r11, [ rsp + 0x80 ]; x18, x17<- arg1[7] * x10000
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x2a8 ], r13; spilling x119 to mem
mov [ rsp + 0x2b0 ], r15; spilling x107 to mem
mulx r13, r15, [ r10 + 0x30 ]; x150, x149<- arg1[0] * arg2[6]
mov rdx, [ rsp + 0x68 ]; x10001 to rdx
mov [ rsp + 0xf8 ], r12; spilling x454 to mem
mulx rdx, r12, [ rsi + 0x40 ]; x4, x3<- arg1[8] * x10001
mov [ rsp + 0x2b8 ], r13; spilling x150 to mem
mov r13, rax; x486, copying x482 here, cause x482 is needed in a reg for other than x486, namely all: , x488, x486, size: 2
shrd r13, r14, 58; x486 <- x484||x482 >> 58
add r12, r11; could be done better, if r0 has been u8 as well
adcx rbx, rdx
add r12, rbp; could be done better, if r0 has been u8 as well
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, rdi
setc dil; spill CF x267 to reg (rdi)
clc;
adcx r12, r9
movzx rdi, dil
lea r8, [ r8 + rbx ]
lea r8, [ r8 + rdi ]
setc r9b; spill CF x275 to reg (r9)
clc;
adcx r12, [ rsp + 0x2b0 ]
setc r11b; spill CF x279 to reg (r11)
clc;
adcx r12, [ rsp + 0x2a8 ]
setc dl; spill CF x283 to reg (rdx)
clc;
adcx r12, [ rsp + 0x2a0 ]
setc bl; spill CF x287 to reg (rbx)
clc;
adcx r12, r15
setc r15b; spill CF x291 to reg (r15)
clc;
adcx r12, r13
adox r8, [ rsp + 0x280 ]
setc r13b; spill CF x490 to reg (r13)
shr r14, 58; x487 <- x484>> 58
sar  r9b, 1
adcx r8, [ rsp + 0x278 ]
sar  r11b, 1
adcx r8, [ rsp + 0x290 ]
sar  dl, 1
adcx r8, [ rsp + 0x298 ]
sar  bl, 1
adcx r8, [ rsp + 0x288 ]
sar  r15b, 1
adcx r8, [ rsp + 0x2b8 ]
mov rdx, [ r10 + 0x38 ]; arg2[7] to rdx
mulx rdi, r9, [ rsi + 0x0 ]; x148, x147<- arg1[0] * arg2[7]
mov rdx, [ r10 + 0x20 ]; arg2[4] to rdx
mulx r11, rbx, [ rsi + 0x18 ]; x106, x105<- arg1[3] * arg2[4]
sar  r13b, 1
adcx r14, r8
mov rdx, [ r10 + 0x18 ]; arg2[3] to rdx
mulx r15, r13, [ rsi + 0x20 ]; x96, x95<- arg1[4] * arg2[3]
mov r8, r12; x493, copying x489 here, cause x489 is needed in a reg for other than x493, namely all: , x495, x493, size: 2
shrd r8, r14, 58; x493 <- x491||x489 >> 58
mov rdx, [ r10 + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x2c0 ], rdi; spilling x148 to mem
mulx rbp, rdi, [ rsi + 0x10 ]; x118, x117<- arg1[2] * arg2[5]
mov rdx, [ r10 + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x2c8 ], rbp; spilling x118 to mem
mov [ rsp + 0x2d0 ], r11; spilling x106 to mem
mulx rbp, r11, [ rsi + 0x30 ]; x82, x81<- arg1[6] * arg2[1]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x2d8 ], r15; spilling x96 to mem
mov [ rsp + 0x2e0 ], r8; spilling x493 to mem
mulx r15, r8, [ r10 + 0x30 ]; x132, x131<- arg1[1] * arg2[6]
mov rdx, [ r10 + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x2e8 ], r15; spilling x132 to mem
mov [ rsp + 0x2f0 ], r9; spilling x147 to mem
mulx r15, r9, [ rsi + 0x28 ]; x88, x87<- arg1[5] * arg2[2]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x2f8 ], r15; spilling x88 to mem
mov [ rsp + 0x300 ], r8; spilling x131 to mem
mulx r15, r8, [ r10 + 0x0 ]; x78, x77<- arg1[7] * arg2[0]
mov rdx, [ rsp + 0x80 ]; x10000 to rdx
mov [ rsp + 0x308 ], rdi; spilling x117 to mem
mulx rdx, rdi, [ rsi + 0x40 ]; x2, x1<- arg1[8] * x10000
add rdi, r8; could be done better, if r0 has been u8 as well
adcx r15, rdx
test al, al
adox rdi, r11
adcx rdi, r9
setc r11b; spill CF x239 to reg (r11)
clc;
adcx rdi, r13
setc r13b; spill CF x243 to reg (r13)
clc;
adcx rdi, rbx
adox rbp, r15
mov rbx, -0x2 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rdi, [ rsp + 0x308 ]
setc r9b; spill CF x247 to reg (r9)
clc;
adcx rdi, [ rsp + 0x300 ]
setc r8b; spill CF x255 to reg (r8)
clc;
adcx rdi, [ rsp + 0x2f0 ]
setc dl; spill CF x259 to reg (rdx)
clc;
adcx rdi, [ rsp + 0x2e0 ]
setc r15b; spill CF x497 to reg (r15)
seto bl; spill OF x251 to reg (rbx)
shr r14, 58; x494 <- x491>> 58
sar  r11b, 1
adcx rbp, [ rsp + 0x2f8 ]
sar  r13b, 1
adcx rbp, [ rsp + 0x2d8 ]
sar  r9b, 1
adcx rbp, [ rsp + 0x2d0 ]
mov r11b, dl; preserving value of x259 into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mulx r13, r9, [ rsi + 0x38 ]; x76, x75<- arg1[7] * arg2[1]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x310 ], r13; spilling x76 to mem
mov [ rsp + 0x318 ], r9; spilling x75 to mem
mulx r13, r9, [ r10 + 0x30 ]; x116, x115<- arg1[2] * arg2[6]
sar  bl, 1
adcx rbp, [ rsp + 0x2c8 ]
mov rdx, [ r10 + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x320 ], r13; spilling x116 to mem
mulx rbx, r13, [ rsi + 0x30 ]; x80, x79<- arg1[6] * arg2[2]
sar  r8b, 1
adcx rbp, [ rsp + 0x2e8 ]
mov rdx, [ r10 + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x328 ], rbx; spilling x80 to mem
mulx r8, rbx, [ rsi + 0x28 ]; x86, x85<- arg1[5] * arg2[3]
sar  r11b, 1
adcx rbp, [ rsp + 0x2c0 ]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x330 ], r8; spilling x86 to mem
mulx r11, r8, [ r10 + 0x28 ]; x104, x103<- arg1[3] * arg2[5]
sar  r15b, 1
adcx r14, rbp
mov rdx, [ r10 + 0x20 ]; arg2[4] to rdx
mulx r15, rbp, [ rsi + 0x20 ]; x94, x93<- arg1[4] * arg2[4]
mov [ rsp + 0x338 ], r11; spilling x104 to mem
mov r11, rdi; x500, copying x496 here, cause x496 is needed in a reg for other than x500, namely all: , x500, x502, size: 2
shrd r11, r14, 58; x500 <- x498||x496 >> 58
mov rdx, [ r10 + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x340 ], r11; spilling x500 to mem
mov [ rsp + 0x348 ], r15; spilling x94 to mem
mulx r11, r15, [ rsi + 0x40 ]; x74, x73<- arg1[8] * arg2[0]
mov [ rsp + 0x350 ], r9; spilling x115 to mem
xor r9, r9
adox r15, [ rsp + 0x318 ]
adcx r15, r13
setc r13b; spill CF x203 to reg (r13)
clc;
adcx r15, rbx
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rbx, r9, [ r10 + 0x40 ]; x146, x145<- arg1[0] * arg2[8]
mov rdx, [ r10 + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x358 ], rbx; spilling x146 to mem
mov [ rsp + 0x360 ], r9; spilling x145 to mem
mulx rbx, r9, [ rsi + 0x8 ]; x130, x129<- arg1[1] * arg2[7]
mov [ rsp + 0x368 ], rbx; spilling x130 to mem
setc bl; spill CF x207 to reg (rbx)
clc;
adcx r15, rbp
adox r11, [ rsp + 0x310 ]
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, r8
seto r8b; spill OF x215 to reg (r8)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r15, [ rsp + 0x350 ]
mov byte [ rsp + 0x370 ], r8b; spilling byte x215 to mem
setc r8b; spill CF x211 to reg (r8)
clc;
adcx r15, r9
movzx r13, r13b
lea r11, [ r13 + r11 ]
mov r13, [ rsp + 0x328 ]
lea r11, [r13+r11]
setc r13b; spill CF x223 to reg (r13)
clc;
adcx r15, [ rsp + 0x360 ]
setc r9b; spill CF x227 to reg (r9)
seto bpl; spill OF x219 to reg (rbp)
shr r14, 58; x501 <- x498>> 58
sar  bl, 1
adcx r11, [ rsp + 0x330 ]
sar  r8b, 1
adcx r11, [ rsp + 0x348 ]
adox r15, [ rsp + 0x340 ]
movzx rbx, byte [ rsp + 0x370 ]; load byte memx215 to register64
lea r11, [ rbx + r11 ]
mov rbx, [ rsp + 0x338 ]
lea r11, [rbx+r11]
mov r8, 0x3ffffffffffffff ; moving imm to reg
seto bl; spill OF x504 to reg (rbx)
and rax, r8; x488 <- x482&0x3ffffffffffffff
sar  bpl, 1
adcx r11, [ rsp + 0x320 ]
sar  r13b, 1
adcx r11, [ rsp + 0x368 ]
sar  r9b, 1
adcx r11, [ rsp + 0x358 ]
sar  bl, 1
adcx r14, r11
mov rbp, r14; x508, copying x505 here, cause x505 is needed in a reg for other than x508, namely all: , x508, x507, size: 2
shr rbp, 57; x508 <- x505>> 57
mov r13, r15; x507, copying x503 here, cause x503 is needed in a reg for other than x507, namely all: , x509, x507, size: 2
shrd r13, r14, 57; x507 <- x505||x503 >> 57
add r13, [ rsp + 0x1e0 ]; could be done better, if r0 has been u8 as well
adc rbp, 0x0
mov r9, [ rsp + 0xf8 ]; x460, copying x454 here, cause x454 is needed in a reg for other than x460, namely all: , x460, size: 1
and r9, r8; x460 <- x454&0x3ffffffffffffff
mov rbx, r13; x513, copying x510 here, cause x510 is needed in a reg for other than x513, namely all: , x514, x513, size: 2
shrd rbx, rbp, 58; x513 <- x512||x510 >> 58
mov r11, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r11 + 0x28 ], rax; out1[5] = x488
and rcx, r8; x481 <- x475&0x3ffffffffffffff
lea rbx, [ rbx + r9 ]
and rdi, r8; x502 <- x496&0x3ffffffffffffff
mov r14, rbx; x516, copying x515 here, cause x515 is needed in a reg for other than x516, namely all: , x516, x517, size: 2
shr r14, 58; x516 <- x515>> 58
mov [ r11 + 0x38 ], rdi; out1[7] = x502
add r14, [ rsp + 0x170 ]
and r13, r8; x514 <- x510&0x3ffffffffffffff
mov [ r11 + 0x10 ], r14; out1[2] = x518
mov rbp, [ rsp + 0x1d8 ]; TMP = x474
mov [ r11 + 0x18 ], rbp; out1[3] = TMP
mov [ r11 + 0x20 ], rcx; out1[4] = x481
and r12, r8; x495 <- x489&0x3ffffffffffffff
and rbx, r8; x517 <- x515&0x3ffffffffffffff
mov [ r11 + 0x8 ], rbx; out1[1] = x517
mov [ r11 + 0x30 ], r12; out1[6] = x495
mov rbp, 0x1ffffffffffffff ; moving imm to reg
and r15, rbp; x509 <- x503&0x1ffffffffffffff
mov [ r11 + 0x0 ], r13; out1[0] = x514
mov [ r11 + 0x40 ], r15; out1[8] = x509
mov rbx, [ rsp + 0x378 ]; restoring from stack
mov rbp, [ rsp + 0x380 ]; restoring from stack
mov r12, [ rsp + 0x388 ]; restoring from stack
mov r13, [ rsp + 0x390 ]; restoring from stack
mov r14, [ rsp + 0x398 ]; restoring from stack
mov r15, [ rsp + 0x3a0 ]; restoring from stack
add rsp, 0x3a8 
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; clocked at 1600 MHz
; first cyclecount 137.735, best 114.72941176470589, lastGood 119.02352941176471
; seed 3926842789276768 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5248104 ms / 60000 runs=> 87.4684ms/run
; Time spent for assembling and measureing (initial batch_size=85, initial num_batches=101): 243610 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.04641866853248335
; number reverted permutation/ tried permutation: 24594 / 30095 =81.721%
; number reverted decision/ tried decision: 20857 / 29906 =69.742%