SECTION .text
	GLOBAL mul_p521
mul_p521:
sub rsp, 0x360 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x330 ], rbx; saving to stack
mov [ rsp + 0x338 ], rbp; saving to stack
mov [ rsp + 0x340 ], r12; saving to stack
mov [ rsp + 0x348 ], r13; saving to stack
mov [ rsp + 0x350 ], r14; saving to stack
mov [ rsp + 0x358 ], r15; saving to stack
imul rax, [ rdx + 0x30 ], 0x2; x10002 <- arg2[6] * 0x2
imul r10, [ rdx + 0x28 ], 0x2; x10003 <- arg2[5] * 0x2
imul r11, [ rdx + 0x40 ], 0x2; x10000 <- arg2[8] * 0x2
imul rbx, [ rdx + 0x38 ], 0x2; x10001 <- arg2[7] * 0x2
mov rbp, rdx; preserving value of arg2 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r12, r13, rbx; x70, x69<- arg1[2] * x10001
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r14, r15, r11; x72, x71<- arg1[1] * x10000
imul rcx, [ rbp + 0x20 ], 0x2; x10004 <- arg2[4] * 0x2
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r8, r9, rax; x66, x65<- arg1[3] * x10002
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
imul rdi, [ rbp + 0x18 ], 0x2; x10005 <- arg2[3] * 0x2
mov [ rsp + 0x8 ], r14; spilling x72 to mem
imul r14, [ rbp + 0x8 ], 0x2; x10007 <- arg2[1] * 0x2
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x10 ], r15; spilling x71 to mem
mov [ rsp + 0x18 ], r12; spilling x70 to mem
mulx r15, r12, rcx; x52, x51<- arg1[5] * x10004
mov rdx, [ rbp + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x20 ], r8; spilling x66 to mem
mov [ rsp + 0x28 ], r15; spilling x52 to mem
mulx r8, r15, [ rsi + 0x0 ]; x162, x161<- arg1[0] * arg2[0]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x30 ], r8; spilling x162 to mem
mov [ rsp + 0x38 ], r15; spilling x161 to mem
mulx r8, r15, rdi; x42, x41<- arg1[6] * x10005
mov [ rsp + 0x40 ], r13; spilling x69 to mem
imul r13, [ rbp + 0x10 ], 0x2; x10006 <- arg2[2] * 0x2
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x48 ], r8; spilling x42 to mem
mov [ rsp + 0x50 ], r9; spilling x65 to mem
mulx r8, r9, r10; x60, x59<- arg1[4] * x10003
mov rdx, r14; x10007 to rdx
mulx rdx, r14, [ rsi + 0x40 ]; x16, x15<- arg1[8] * x10007
mov [ rsp + 0x58 ], rbx; spilling x10001 to mem
mov rbx, rdx; preserving value of x16 into a new reg
mov rdx, [ rsi + 0x38 ]; saving arg1[7] in rdx.
mov [ rsp + 0x60 ], r8; spilling x60 to mem
mov [ rsp + 0x68 ], r9; spilling x59 to mem
mulx r8, r9, r13; x30, x29<- arg1[7] * x10006
add r14, r9; could be done better, if r0 has been u8 as well
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, r15
setc r15b; spill CF x164 to reg (r15)
clc;
adcx r14, r12
setc r12b; spill CF x172 to reg (r12)
clc;
adcx r14, [ rsp + 0x68 ]
seto r9b; spill OF x168 to reg (r9)
mov [ rsp + 0x70 ], r11; spilling x10000 to mem
mov r11, -0x2 ; moving imm to reg
inc r11; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, [ rsp + 0x50 ]
movzx r15, r15b
lea r8, [ r8 + rbx ]
lea r8, [ r8 + r15 ]
movzx r9, r9b
lea r8, [ r9 + r8 ]
mov r9, [ rsp + 0x48 ]
lea r8, [r9+r8]
seto bl; spill OF x180 to reg (rbx)
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r14, [ rsp + 0x40 ]
movzx r12, r12b
lea r8, [ r12 + r8 ]
mov r12, [ rsp + 0x28 ]
lea r8, [r12+r8]
adcx r8, [ rsp + 0x60 ]
movzx rbx, bl
lea r8, [ rbx + r8 ]
mov rbx, [ rsp + 0x20 ]
lea r8, [rbx+r8]
adox r8, [ rsp + 0x18 ]
mov rdx, [ rsi + 0x40 ]; arg1[8] to rdx
mulx r13, r15, r13; x14, x13<- arg1[8] * x10006
xor r9, r9
adox r14, [ rsp + 0x10 ]
adcx r14, [ rsp + 0x38 ]
adox r8, [ rsp + 0x8 ]
adcx r8, [ rsp + 0x30 ]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r11, r12, [ rbp + 0x8 ]; x160, x159<- arg1[0] * arg2[1]
mov rbx, r14; x195, copying x191 here, cause x191 is needed in a reg for other than x195, namely all: , x195, x197, size: 2
shrd rbx, r8, 58; x195 <- x193||x191 >> 58
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x78 ], r11; spilling x160 to mem
mulx r9, r11, rdi; x28, x27<- arg1[7] * x10005
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x80 ], rbx; spilling x195 to mem
mov [ rsp + 0x88 ], r12; spilling x159 to mem
mulx rbx, r12, [ rsp + 0x70 ]; x68, x67<- arg1[2] * x10000
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x90 ], rbx; spilling x68 to mem
mov [ rsp + 0x98 ], r12; spilling x67 to mem
mulx rbx, r12, [ rbp + 0x0 ]; x144, x143<- arg1[1] * arg2[0]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0xa0 ], rbx; spilling x144 to mem
mov [ rsp + 0xa8 ], r12; spilling x143 to mem
mulx rbx, r12, [ rsp + 0x58 ]; x64, x63<- arg1[3] * x10001
mov rdx, rax; x10002 to rdx
mov [ rsp + 0xb0 ], rbx; spilling x64 to mem
mulx rax, rbx, [ rsi + 0x20 ]; x58, x57<- arg1[4] * x10002
mov [ rsp + 0xb8 ], rax; spilling x58 to mem
xor rax, rax
adox r15, r11
mov r11, rdx; preserving value of x10002 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0xc0 ], r13; spilling x14 to mem
mulx rax, r13, rcx; x40, x39<- arg1[6] * x10004
adcx r15, r13
mov rdx, r10; x10003 to rdx
mulx r10, r13, [ rsi + 0x28 ]; x50, x49<- arg1[5] * x10003
mov [ rsp + 0xc8 ], r10; spilling x50 to mem
setc r10b; spill CF x427 to reg (r10)
clc;
adcx r15, r13
setc r13b; spill CF x431 to reg (r13)
clc;
adcx r15, rbx
seto bl; spill OF x423 to reg (rbx)
mov byte [ rsp + 0xd0 ], r13b; spilling byte x431 to mem
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, r12
movzx rbx, bl
lea r9, [ rbx + r9 ]
mov rbx, [ rsp + 0xc0 ]
lea r9, [rbx+r9]
setc r12b; spill CF x435 to reg (r12)
clc;
adcx r15, [ rsp + 0x98 ]
movzx r10, r10b
lea rax, [ rax + r9 ]
lea rax, [ rax + r10 ]
seto bl; spill OF x439 to reg (rbx)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r15, [ rsp + 0xa8 ]
movzx r10, byte [ rsp + 0xd0 ]; load byte memx431 to register64
lea rax, [ r10 + rax ]
mov r10, [ rsp + 0xc8 ]
lea rax, [r10+rax]
seto r10b; spill OF x447 to reg (r10)
mov r9, -0x3 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r15, [ rsp + 0x88 ]
setc r9b; spill CF x443 to reg (r9)
clc;
adcx r15, [ rsp + 0x80 ]
movzx r12, r12b
lea rax, [ r12 + rax ]
mov r12, [ rsp + 0xb8 ]
lea rax, [r12+rax]
setc r12b; spill CF x455 to reg (r12)
seto r13b; spill OF x451 to reg (r13)
shr r8, 58; x196 <- x193>> 58
sar  bl, 1
adcx rax, [ rsp + 0xb0 ]
sar  r9b, 1
adcx rax, [ rsp + 0x90 ]
sar  r10b, 1
adcx rax, [ rsp + 0xa0 ]
mulx rbx, r9, [ rsi + 0x30 ]; x38, x37<- arg1[6] * x10003
sar  r13b, 1
adcx rax, [ rsp + 0x78 ]
sar  r12b, 1
adcx r8, rax
mov r10, rdx; preserving value of x10003 into a new reg
mov rdx, [ rsi + 0x40 ]; saving arg1[8] in rdx.
mulx rdi, r13, rdi; x12, x11<- arg1[8] * x10005
mov rdx, [ rbp + 0x10 ]; arg2[2] to rdx
mulx r12, rax, [ rsi + 0x0 ]; x158, x157<- arg1[0] * arg2[2]
mov rdx, [ rbp + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0xd8 ], r12; spilling x158 to mem
mov [ rsp + 0xe0 ], rax; spilling x157 to mem
mulx r12, rax, [ rsi + 0x10 ]; x128, x127<- arg1[2] * arg2[0]
mov rdx, [ rbp + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0xe8 ], r12; spilling x128 to mem
mov [ rsp + 0xf0 ], rax; spilling x127 to mem
mulx r12, rax, [ rsi + 0x8 ]; x142, x141<- arg1[1] * arg2[1]
mov [ rsp + 0xf8 ], r12; spilling x142 to mem
mov r12, r15; x458, copying x454 here, cause x454 is needed in a reg for other than x458, namely all: , x458, x460, size: 2
shrd r12, r8, 58; x458 <- x456||x454 >> 58
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x100 ], r12; spilling x458 to mem
mov [ rsp + 0x108 ], rax; spilling x141 to mem
mulx r12, rax, rcx; x26, x25<- arg1[7] * x10004
test al, al
adox r13, rax
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x110 ], rbx; spilling x38 to mem
mulx rax, rbx, [ rsp + 0x70 ]; x62, x61<- arg1[3] * x10000
adox r12, rdi
adcx r13, r9
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r9, rdi, [ rsp + 0x58 ]; x56, x55<- arg1[4] * x10001
mov rdx, r11; x10002 to rdx
mov [ rsp + 0x118 ], rax; spilling x62 to mem
mulx r11, rax, [ rsi + 0x28 ]; x48, x47<- arg1[5] * x10002
adcx r12, [ rsp + 0x110 ]
test al, al
adox r13, rax
adcx r13, rdi
adox r11, r12
adcx r9, r11
add r13, rbx; could be done better, if r0 has been u8 as well
mov rbx, -0x2 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, [ rsp + 0xf0 ]
adcx r9, [ rsp + 0x118 ]
clc;
adcx r13, [ rsp + 0x108 ]
adox r9, [ rsp + 0xe8 ]
adcx r9, [ rsp + 0xf8 ]
shr r8, 58; x459 <- x456>> 58
add r13, [ rsp + 0xe0 ]; could be done better, if r0 has been u8 as well
mulx rdi, rax, [ rsi + 0x30 ]; x36, x35<- arg1[6] * x10002
mov r12, rdx; preserving value of x10002 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx r11, rbx, [ rsp + 0x58 ]; x46, x45<- arg1[5] * x10001
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x120 ], r11; spilling x46 to mem
mov [ rsp + 0x128 ], rdi; spilling x36 to mem
mulx r11, rdi, [ rsp + 0x70 ]; x54, x53<- arg1[4] * x10000
mov rdx, [ rbp + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x130 ], r11; spilling x54 to mem
mov [ rsp + 0x138 ], rdi; spilling x53 to mem
mulx r11, rdi, [ rsi + 0x0 ]; x156, x155<- arg1[0] * arg2[3]
adcx r9, [ rsp + 0xd8 ]
test al, al
adox r13, [ rsp + 0x100 ]
mov rdx, [ rsi + 0x40 ]; arg1[8] to rdx
mov [ rsp + 0x140 ], r11; spilling x156 to mem
mulx rcx, r11, rcx; x10, x9<- arg1[8] * x10004
adox r8, r9
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x148 ], rdi; spilling x155 to mem
mulx r9, rdi, [ rbp + 0x10 ]; x140, x139<- arg1[1] * arg2[2]
mov [ rsp + 0x150 ], r9; spilling x140 to mem
mov r9, r13; x465, copying x461 here, cause x461 is needed in a reg for other than x465, namely all: , x465, x467, size: 2
shrd r9, r8, 58; x465 <- x463||x461 >> 58
mov rdx, [ rbp + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x158 ], r9; spilling x465 to mem
mov [ rsp + 0x160 ], rdi; spilling x139 to mem
mulx r9, rdi, [ rsi + 0x18 ]; x114, x113<- arg1[3] * arg2[0]
mov rdx, r10; x10003 to rdx
mov [ rsp + 0x168 ], r9; spilling x114 to mem
mulx r10, r9, [ rsi + 0x38 ]; x24, x23<- arg1[7] * x10003
mov [ rsp + 0x170 ], rdi; spilling x113 to mem
xor rdi, rdi
adox r11, r9
mov r9, rdx; preserving value of x10003 into a new reg
mov rdx, [ rbp + 0x8 ]; saving arg2[1] in rdx.
mov [ rsp + 0x178 ], rcx; spilling x10 to mem
mulx rdi, rcx, [ rsi + 0x10 ]; x126, x125<- arg1[2] * arg2[1]
adcx r11, rax
setc al; spill CF x363 to reg (rax)
clc;
adcx r11, rbx
adox r10, [ rsp + 0x178 ]
movzx rax, al
lea r10, [ rax + r10 ]
mov rax, [ rsp + 0x128 ]
lea r10, [rax+r10]
mov rbx, -0x2 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, [ rsp + 0x138 ]
setc al; spill CF x367 to reg (rax)
clc;
adcx r11, [ rsp + 0x170 ]
seto bl; spill OF x371 to reg (rbx)
mov [ rsp + 0x180 ], r14; spilling x191 to mem
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, rcx
setc cl; spill CF x375 to reg (rcx)
seto r14b; spill OF x379 to reg (r14)
shr r8, 58; x466 <- x463>> 58
sar  al, 1
adcx r10, [ rsp + 0x120 ]
sar  bl, 1
adcx r10, [ rsp + 0x130 ]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mulx rax, rbx, [ rsp + 0x58 ]; x34, x33<- arg1[6] * x10001
sar  cl, 1
adcx r10, [ rsp + 0x168 ]
adox r11, [ rsp + 0x160 ]
clc;
adcx r11, [ rsp + 0x148 ]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x188 ], rax; spilling x34 to mem
mulx rcx, rax, [ rbp + 0x18 ]; x138, x137<- arg1[1] * arg2[3]
mov [ rsp + 0x190 ], rcx; spilling x138 to mem
setc cl; spill CF x387 to reg (rcx)
clc;
adcx r11, [ rsp + 0x158 ]
mov rdx, [ rbp + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x198 ], rax; spilling x137 to mem
mov [ rsp + 0x1a0 ], rbx; spilling x33 to mem
mulx rax, rbx, [ rsi + 0x20 ]; x102, x101<- arg1[4] * arg2[0]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x1a8 ], rax; spilling x102 to mem
mov [ rsp + 0x1b0 ], rbx; spilling x101 to mem
mulx rax, rbx, [ rsp + 0x70 ]; x44, x43<- arg1[5] * x10000
movzx r14, r14b
lea rdi, [ rdi + r10 ]
lea rdi, [ rdi + r14 ]
adox rdi, [ rsp + 0x150 ]
mov rdx, [ rsi + 0x40 ]; arg1[8] to rdx
mulx r9, r14, r9; x8, x7<- arg1[8] * x10003
mov rdx, [ rbp + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x1b8 ], rax; spilling x44 to mem
mulx r10, rax, [ rsi + 0x18 ]; x112, x111<- arg1[3] * arg2[1]
movzx rcx, cl
lea rdi, [ rcx + rdi ]
mov rcx, [ rsp + 0x140 ]
lea rdi, [rcx+rdi]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x1c0 ], r10; spilling x112 to mem
mulx rcx, r10, [ rbp + 0x10 ]; x124, x123<- arg1[2] * arg2[2]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x1c8 ], rcx; spilling x124 to mem
mov [ rsp + 0x1d0 ], r10; spilling x123 to mem
mulx rcx, r10, [ rbp + 0x20 ]; x154, x153<- arg1[0] * arg2[4]
adcx r8, rdi
mov rdi, r11; x472, copying x468 here, cause x468 is needed in a reg for other than x472, namely all: , x472, x474, size: 2
shrd rdi, r8, 58; x472 <- x470||x468 >> 58
mov rdx, r12; x10002 to rdx
mov [ rsp + 0x1d8 ], rcx; spilling x154 to mem
mulx r12, rcx, [ rsi + 0x38 ]; x22, x21<- arg1[7] * x10002
add r14, rcx; could be done better, if r0 has been u8 as well
adcx r12, r9
test al, al
adox r14, [ rsp + 0x1a0 ]
adcx r14, rbx
setc bl; spill CF x335 to reg (rbx)
clc;
adcx r14, [ rsp + 0x1b0 ]
setc r9b; spill CF x339 to reg (r9)
clc;
adcx r14, rax
setc al; spill CF x343 to reg (rax)
clc;
adcx r14, [ rsp + 0x1d0 ]
adox r12, [ rsp + 0x188 ]
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, [ rsp + 0x198 ]
setc cl; spill CF x347 to reg (rcx)
clc;
adcx r14, r10
setc r10b; spill CF x355 to reg (r10)
clc;
adcx r14, rdi
setc dil; spill CF x476 to reg (rdi)
mov [ rsp + 0x1e0 ], r14; spilling x475 to mem
seto r14b; spill OF x351 to reg (r14)
shr r8, 58; x473 <- x470>> 58
sar  bl, 1
adcx r12, [ rsp + 0x1b8 ]
sar  r9b, 1
adcx r12, [ rsp + 0x1a8 ]
sar  al, 1
adcx r12, [ rsp + 0x1c0 ]
sar  cl, 1
adcx r12, [ rsp + 0x1c8 ]
sar  r14b, 1
adcx r12, [ rsp + 0x190 ]
mov rbx, rdx; preserving value of x10002 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r9, rax, [ rbp + 0x8 ]; x100, x99<- arg1[4] * arg2[1]
mov rdx, [ rbp + 0x18 ]; arg2[3] to rdx
mulx rcx, r14, [ rsi + 0x10 ]; x122, x121<- arg1[2] * arg2[3]
mov rdx, [ rbp + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x1e8 ], rcx; spilling x122 to mem
mov [ rsp + 0x1f0 ], r9; spilling x100 to mem
mulx rcx, r9, [ rsi + 0x8 ]; x136, x135<- arg1[1] * arg2[4]
sar  r10b, 1
adcx r12, [ rsp + 0x1d8 ]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x1f8 ], rcx; spilling x136 to mem
mulx r10, rcx, [ rbp + 0x28 ]; x152, x151<- arg1[0] * arg2[5]
sar  dil, 1
adcx r8, r12
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mulx rdi, r12, [ rsp + 0x70 ]; x32, x31<- arg1[6] * x10000
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x200 ], r10; spilling x152 to mem
mov [ rsp + 0x208 ], rcx; spilling x151 to mem
mulx r10, rcx, [ rbp + 0x10 ]; x110, x109<- arg1[3] * arg2[2]
mov rdx, [ rbp + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x210 ], r10; spilling x110 to mem
mov [ rsp + 0x218 ], r9; spilling x135 to mem
mulx r10, r9, [ rsi + 0x28 ]; x92, x91<- arg1[5] * arg2[0]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x220 ], r14; spilling x121 to mem
mov [ rsp + 0x228 ], rcx; spilling x109 to mem
mulx r14, rcx, [ rsp + 0x58 ]; x20, x19<- arg1[7] * x10001
mov rdx, rbx; x10002 to rdx
mulx rdx, rbx, [ rsi + 0x40 ]; x6, x5<- arg1[8] * x10002
adox rbx, rcx
clc;
adcx rbx, r12
adox r14, rdx
adcx rdi, r14
test al, al
adox rbx, r9
adox r10, rdi
mov r12, [ rsp + 0x1e0 ]; load m64 x475 to register64
mov r9, r12; x479, copying x475 here, cause x475 is needed in a reg for other than x479, namely all: , x479, x481, size: 2
shrd r9, r8, 58; x479 <- x477||x475 >> 58
test al, al
adox rbx, rax
adcx rbx, [ rsp + 0x228 ]
setc al; spill CF x311 to reg (rax)
clc;
adcx rbx, [ rsp + 0x220 ]
setc cl; spill CF x315 to reg (rcx)
clc;
adcx rbx, [ rsp + 0x218 ]
setc dl; spill CF x319 to reg (rdx)
clc;
adcx rbx, [ rsp + 0x208 ]
setc r14b; spill CF x323 to reg (r14)
clc;
adcx rbx, r9
adox r10, [ rsp + 0x1f0 ]
setc dil; spill CF x483 to reg (rdi)
shr r8, 58; x480 <- x477>> 58
sar  al, 1
adcx r10, [ rsp + 0x210 ]
sar  cl, 1
adcx r10, [ rsp + 0x1e8 ]
sar  dl, 1
adcx r10, [ rsp + 0x1f8 ]
sar  r14b, 1
adcx r10, [ rsp + 0x200 ]
mov rdx, [ rbp + 0x28 ]; arg2[5] to rdx
mulx r9, rax, [ rsi + 0x8 ]; x134, x133<- arg1[1] * arg2[5]
sar  dil, 1
adcx r8, r10
mov rdx, [ rbp + 0x8 ]; arg2[1] to rdx
mulx rcx, r14, [ rsi + 0x28 ]; x90, x89<- arg1[5] * arg2[1]
mov rdx, [ rbp + 0x18 ]; arg2[3] to rdx
mulx rdi, r10, [ rsi + 0x18 ]; x108, x107<- arg1[3] * arg2[3]
mov [ rsp + 0x230 ], r9; spilling x134 to mem
mov r9, r8; x487, copying x484 here, cause x484 is needed in a reg for other than x487, namely all: , x487, x486, size: 2
shr r9, 58; x487 <- x484>> 58
mov rdx, [ rbp + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x238 ], r9; spilling x487 to mem
mov [ rsp + 0x240 ], rax; spilling x133 to mem
mulx r9, rax, [ rsi + 0x0 ]; x150, x149<- arg1[0] * arg2[6]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x248 ], r9; spilling x150 to mem
mov [ rsp + 0x250 ], rax; spilling x149 to mem
mulx r9, rax, [ rsp + 0x70 ]; x18, x17<- arg1[7] * x10000
mov [ rsp + 0x258 ], rdi; spilling x108 to mem
mov rdi, 0x3ffffffffffffff ; moving imm to reg
mov [ rsp + 0x260 ], r10; spilling x107 to mem
mov r10, [ rsp + 0x180 ]; x197, copying x191 here, cause x191 is needed in a reg for other than x197, namely all: , x197, size: 1
and r10, rdi; x197 <- x191&0x3ffffffffffffff
and r15, rdi; x460 <- x454&0x3ffffffffffffff
mov rdx, [ rsi + 0x40 ]; arg1[8] to rdx
mov [ rsp + 0x268 ], r15; spilling x460 to mem
mulx rdi, r15, [ rsp + 0x58 ]; x4, x3<- arg1[8] * x10001
adox r15, rax
mov rdx, [ rbp + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x270 ], r10; spilling x197 to mem
mulx rax, r10, [ rsi + 0x10 ]; x120, x119<- arg1[2] * arg2[4]
adox r9, rdi
mov rdi, rbx; x486, copying x482 here, cause x482 is needed in a reg for other than x486, namely all: , x488, x486, size: 2
shrd rdi, r8, 58; x486 <- x484||x482 >> 58
mov rdx, [ rbp + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x278 ], rdi; spilling x486 to mem
mulx r8, rdi, [ rsi + 0x20 ]; x98, x97<- arg1[4] * arg2[2]
mov rdx, [ rbp + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x280 ], rax; spilling x120 to mem
mov [ rsp + 0x288 ], r10; spilling x119 to mem
mulx rax, r10, [ rsi + 0x30 ]; x84, x83<- arg1[6] * arg2[0]
add r15, r10; could be done better, if r0 has been u8 as well
adcx rax, r9
test al, al
adox r15, r14
adox rcx, rax
adcx r15, rdi
adcx r8, rcx
mov rdx, [ rbp + 0x0 ]; arg2[0] to rdx
mulx r14, r9, [ rsi + 0x38 ]; x78, x77<- arg1[7] * arg2[0]
add r15, [ rsp + 0x260 ]; could be done better, if r0 has been u8 as well
adcx r8, [ rsp + 0x258 ]
xor rdi, rdi
adox r15, [ rsp + 0x288 ]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r10, rax, [ rbp + 0x30 ]; x132, x131<- arg1[1] * arg2[6]
mov rdx, [ rbp + 0x38 ]; arg2[7] to rdx
mulx rcx, rdi, [ rsi + 0x0 ]; x148, x147<- arg1[0] * arg2[7]
adox r8, [ rsp + 0x280 ]
adcx r15, [ rsp + 0x240 ]
adcx r8, [ rsp + 0x230 ]
add r15, [ rsp + 0x250 ]; could be done better, if r0 has been u8 as well
adcx r8, [ rsp + 0x248 ]
mov [ rsp + 0x290 ], rcx; spilling x148 to mem
xor rcx, rcx
adox r15, [ rsp + 0x278 ]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x298 ], rdi; spilling x147 to mem
mulx rcx, rdi, [ rbp + 0x28 ]; x118, x117<- arg1[2] * arg2[5]
adox r8, [ rsp + 0x238 ]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x2a0 ], r10; spilling x132 to mem
mov [ rsp + 0x2a8 ], rax; spilling x131 to mem
mulx r10, rax, [ rbp + 0x20 ]; x106, x105<- arg1[3] * arg2[4]
mov [ rsp + 0x2b0 ], rcx; spilling x118 to mem
mov rcx, r15; x493, copying x489 here, cause x489 is needed in a reg for other than x493, namely all: , x493, x495, size: 2
shrd rcx, r8, 58; x493 <- x491||x489 >> 58
mov rdx, [ rsp + 0x70 ]; x10000 to rdx
mov [ rsp + 0x2b8 ], rcx; spilling x493 to mem
mulx rdx, rcx, [ rsi + 0x40 ]; x2, x1<- arg1[8] * x10000
add rcx, r9; could be done better, if r0 has been u8 as well
mov r9, rdx; preserving value of x2 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x2c0 ], rdi; spilling x117 to mem
mov [ rsp + 0x2c8 ], r10; spilling x106 to mem
mulx rdi, r10, [ rbp + 0x10 ]; x88, x87<- arg1[5] * arg2[2]
adcx r14, r9
mov rdx, [ rbp + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x2d0 ], rax; spilling x105 to mem
mulx r9, rax, [ rsi + 0x30 ]; x82, x81<- arg1[6] * arg2[1]
test al, al
adox rcx, rax
adox r9, r14
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r14, rax, [ rbp + 0x18 ]; x96, x95<- arg1[4] * arg2[3]
adcx rcx, r10
adcx rdi, r9
test al, al
adox rcx, rax
adcx rcx, [ rsp + 0x2d0 ]
adox r14, rdi
adcx r14, [ rsp + 0x2c8 ]
shr r8, 58; x494 <- x491>> 58
test al, al
adox rcx, [ rsp + 0x2c0 ]
adox r14, [ rsp + 0x2b0 ]
adcx rcx, [ rsp + 0x2a8 ]
mov rdx, [ rbp + 0x40 ]; arg2[8] to rdx
mulx rdx, r10, [ rsi + 0x0 ]; x146, x145<- arg1[0] * arg2[8]
adcx r14, [ rsp + 0x2a0 ]
xor r9, r9
adox rcx, [ rsp + 0x298 ]
mov rax, rdx; preserving value of x146 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mulx rdi, r9, [ rbp + 0x10 ]; x80, x79<- arg1[6] * arg2[2]
adox r14, [ rsp + 0x290 ]
mov rdx, [ rbp + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x2d8 ], rax; spilling x146 to mem
mov [ rsp + 0x2e0 ], r10; spilling x145 to mem
mulx rax, r10, [ rsi + 0x28 ]; x86, x85<- arg1[5] * arg2[3]
adcx rcx, [ rsp + 0x2b8 ]
mov rdx, [ rbp + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x2e8 ], rax; spilling x86 to mem
mov [ rsp + 0x2f0 ], rdi; spilling x80 to mem
mulx rax, rdi, [ rsi + 0x8 ]; x130, x129<- arg1[1] * arg2[7]
adcx r8, r14
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x2f8 ], rax; spilling x130 to mem
mulx r14, rax, [ rbp + 0x30 ]; x116, x115<- arg1[2] * arg2[6]
mov rdx, [ rsi + 0x40 ]; arg1[8] to rdx
mov [ rsp + 0x300 ], rdi; spilling x129 to mem
mov [ rsp + 0x308 ], r14; spilling x116 to mem
mulx rdi, r14, [ rbp + 0x0 ]; x74, x73<- arg1[8] * arg2[0]
mov [ rsp + 0x310 ], rax; spilling x115 to mem
mov rax, rcx; x500, copying x496 here, cause x496 is needed in a reg for other than x500, namely all: , x500, x502, size: 2
shrd rax, r8, 58; x500 <- x498||x496 >> 58
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x318 ], rax; spilling x500 to mem
mov [ rsp + 0x320 ], r10; spilling x85 to mem
mulx rax, r10, [ rbp + 0x8 ]; x76, x75<- arg1[7] * arg2[1]
add r14, r10; could be done better, if r0 has been u8 as well
adcx rax, rdi
test al, al
adox r14, r9
adcx r14, [ rsp + 0x320 ]
adox rax, [ rsp + 0x2f0 ]
adcx rax, [ rsp + 0x2e8 ]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r9, rdi, [ rbp + 0x28 ]; x104, x103<- arg1[3] * arg2[5]
mov rdx, [ rbp + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x328 ], r9; spilling x104 to mem
mulx r10, r9, [ rsi + 0x20 ]; x94, x93<- arg1[4] * arg2[4]
add r14, r9; could be done better, if r0 has been u8 as well
adcx r10, rax
add r14, rdi; could be done better, if r0 has been u8 as well
adcx r10, [ rsp + 0x328 ]
add r14, [ rsp + 0x310 ]; could be done better, if r0 has been u8 as well
adcx r10, [ rsp + 0x308 ]
test al, al
adox r14, [ rsp + 0x300 ]
adcx r14, [ rsp + 0x2e0 ]
adox r10, [ rsp + 0x2f8 ]
adcx r10, [ rsp + 0x2d8 ]
shr r8, 58; x501 <- x498>> 58
add r14, [ rsp + 0x318 ]; could be done better, if r0 has been u8 as well
adcx r8, r10
mov rax, r14; x507, copying x503 here, cause x503 is needed in a reg for other than x507, namely all: , x507, x509, size: 2
shrd rax, r8, 57; x507 <- x505||x503 >> 57
shr r8, 57; x508 <- x505>> 57
mov rdi, 0x3ffffffffffffff ; moving imm to reg
and r11, rdi; x474 <- x468&0x3ffffffffffffff
adox rax, [ rsp + 0x270 ]
seto r9b; spill OF x511 to reg (r9)
and r13, rdi; x467 <- x461&0x3ffffffffffffff
movzx r10, r9b; x512, copying x511 here, cause x511 is needed in a reg for other than x512, namely all: , x512, size: 1
lea r10, [ r10 + r8 ]
mov r8, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r8 + 0x18 ], r11; out1[3] = x474
mov r9, rax; x514, copying x510 here, cause x510 is needed in a reg for other than x514, namely all: , x513, x514, size: 2
and r9, rdi; x514 <- x510&0x3ffffffffffffff
shrd rax, r10, 58; x513 <- x512||x510 >> 58
and r15, rdi; x495 <- x489&0x3ffffffffffffff
add rax, [ rsp + 0x268 ]
mov r10, 0x1ffffffffffffff ; moving imm to reg
and r14, r10; x509 <- x503&0x1ffffffffffffff
mov r11, rax; x516, copying x515 here, cause x515 is needed in a reg for other than x516, namely all: , x517, x516, size: 2
shr r11, 58; x516 <- x515>> 58
and rcx, rdi; x502 <- x496&0x3ffffffffffffff
and rax, rdi; x517 <- x515&0x3ffffffffffffff
mov [ r8 + 0x8 ], rax; out1[1] = x517
mov [ r8 + 0x38 ], rcx; out1[7] = x502
lea r11, [ r11 + r13 ]
and r12, rdi; x481 <- x475&0x3ffffffffffffff
mov [ r8 + 0x10 ], r11; out1[2] = x518
mov [ r8 + 0x0 ], r9; out1[0] = x514
and rbx, rdi; x488 <- x482&0x3ffffffffffffff
mov [ r8 + 0x28 ], rbx; out1[5] = x488
mov [ r8 + 0x20 ], r12; out1[4] = x481
mov [ r8 + 0x30 ], r15; out1[6] = x495
mov [ r8 + 0x40 ], r14; out1[8] = x509
mov rbx, [ rsp + 0x330 ]; restoring from stack
mov rbp, [ rsp + 0x338 ]; restoring from stack
mov r12, [ rsp + 0x340 ]; restoring from stack
mov r13, [ rsp + 0x348 ]; restoring from stack
mov r14, [ rsp + 0x350 ]; restoring from stack
mov r15, [ rsp + 0x358 ]; restoring from stack
add rsp, 0x360 
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; clocked at 2600 MHz
; first cyclecount 256.1, best 186.31372549019608, lastGood 203.9375
; seed 2833800931993071 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5396750 ms / 60000 runs=> 89.94583333333334ms/run
; Time spent for assembling and measureing (initial batch_size=46, initial num_batches=101): 234868 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.04352026682725715
; number reverted permutation/ tried permutation: 22395 / 30062 =74.496%
; number reverted decision/ tried decision: 20159 / 29939 =67.334%