SECTION .text
	GLOBAL mul_p521
mul_p521:
sub rsp, 0x3e0 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x3b0 ], rbx; saving to stack
mov [ rsp + 0x3b8 ], rbp; saving to stack
mov [ rsp + 0x3c0 ], r12; saving to stack
mov [ rsp + 0x3c8 ], r13; saving to stack
mov [ rsp + 0x3d0 ], r14; saving to stack
mov [ rsp + 0x3d8 ], r15; saving to stack
imul rax, [ rdx + 0x38 ], 0x2; x10001 <- arg2[7] * 0x2
mov r10, rdx; preserving value of arg2 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r11, rbx, [ r10 + 0x0 ]; x162, x161<- arg1[0] * arg2[0]
imul rbp, [ r10 + 0x40 ], 0x2; x10000 <- arg2[8] * 0x2
mov rdx, rax; x10001 to rdx
mulx rax, r12, [ rsi + 0x10 ]; x70, x69<- arg1[2] * x10001
mov r13, rdx; preserving value of x10001 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r14, r15, rbp; x72, x71<- arg1[1] * x10000
imul rcx, [ r10 + 0x30 ], 0x2; x10002 <- arg2[6] * 0x2
imul r8, [ r10 + 0x28 ], 0x2; x10003 <- arg2[5] * 0x2
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r9, rdi, rcx; x66, x65<- arg1[3] * x10002
mov rdx, r8; x10003 to rdx
mov [ rsp + 0x8 ], r11; spilling x162 to mem
mulx r8, r11, [ rsi + 0x20 ]; x60, x59<- arg1[4] * x10003
mov [ rsp + 0x10 ], rbx; spilling x161 to mem
imul rbx, [ r10 + 0x18 ], 0x2; x10005 <- arg2[3] * 0x2
mov [ rsp + 0x18 ], r14; spilling x72 to mem
imul r14, [ r10 + 0x20 ], 0x2; x10004 <- arg2[4] * 0x2
mov [ rsp + 0x20 ], rax; spilling x70 to mem
imul rax, [ r10 + 0x10 ], 0x2; x10006 <- arg2[2] * 0x2
mov [ rsp + 0x28 ], r9; spilling x66 to mem
imul r9, [ r10 + 0x8 ], 0x2; x10007 <- arg2[1] * 0x2
xchg rdx, rax; x10006, swapping with x10003, which is currently in rdx
mov [ rsp + 0x30 ], r13; spilling x10001 to mem
mov [ rsp + 0x38 ], r15; spilling x71 to mem
mulx r13, r15, [ rsi + 0x38 ]; x30, x29<- arg1[7] * x10006
xchg rdx, r9; x10007, swapping with x10006, which is currently in rdx
mov [ rsp + 0x40 ], r8; spilling x60 to mem
mulx rdx, r8, [ rsi + 0x40 ]; x16, x15<- arg1[8] * x10007
xchg rdx, rbx; x10005, swapping with x16, which is currently in rdx
mov [ rsp + 0x48 ], r12; spilling x69 to mem
mov [ rsp + 0x50 ], rdi; spilling x65 to mem
mulx r12, rdi, [ rsi + 0x30 ]; x42, x41<- arg1[6] * x10005
add r8, r15; could be done better, if r0 has been u8 as well
mov r15, -0x2 ; moving imm to reg
inc r15; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, rdi
adcx r13, rbx
mov rbx, rdx; preserving value of x10005 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx rdi, r15, r14; x52, x51<- arg1[5] * x10004
clc;
adcx r8, r15
adox r12, r13
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, r11
setc r11b; spill CF x172 to reg (r11)
clc;
adcx r8, [ rsp + 0x50 ]
movzx r11, r11b
lea rdi, [ rdi + r12 ]
lea rdi, [ rdi + r11 ]
setc r15b; spill CF x180 to reg (r15)
clc;
adcx r8, [ rsp + 0x48 ]
adox rdi, [ rsp + 0x40 ]
mov rdx, [ r10 + 0x8 ]; arg2[1] to rdx
mulx r11, r12, [ rsi + 0x0 ]; x160, x159<- arg1[0] * arg2[1]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x58 ], r11; spilling x160 to mem
mulx r13, r11, r14; x40, x39<- arg1[6] * x10004
mov [ rsp + 0x60 ], r12; spilling x159 to mem
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, [ rsp + 0x38 ]
movzx r15, r15b
lea rdi, [ r15 + rdi ]
mov r15, [ rsp + 0x28 ]
lea rdi, [r15+rdi]
mov rdx, rbx; x10005 to rdx
mulx rbx, r15, [ rsi + 0x38 ]; x28, x27<- arg1[7] * x10005
adcx rdi, [ rsp + 0x20 ]
adox rdi, [ rsp + 0x18 ]
mov r12, rdx; preserving value of x10005 into a new reg
mov rdx, [ rsp + 0x30 ]; saving x10001 in rdx.
mov [ rsp + 0x68 ], r13; spilling x40 to mem
mov [ rsp + 0x70 ], rcx; spilling x10002 to mem
mulx r13, rcx, [ rsi + 0x18 ]; x64, x63<- arg1[3] * x10001
mov [ rsp + 0x78 ], r13; spilling x64 to mem
xor r13, r13
adox r8, [ rsp + 0x10 ]
xchg rdx, r9; x10006, swapping with x10001, which is currently in rdx
mulx rdx, r13, [ rsi + 0x40 ]; x14, x13<- arg1[8] * x10006
adcx r13, r15
seto r15b; spill OF x192 to reg (r15)
mov [ rsp + 0x80 ], rcx; spilling x63 to mem
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, r11
xchg rdx, rbp; x10000, swapping with x14, which is currently in rdx
mulx r11, rcx, [ rsi + 0x10 ]; x68, x67<- arg1[2] * x10000
mov [ rsp + 0x88 ], r11; spilling x68 to mem
mov r11, rdx; preserving value of x10000 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x90 ], rcx; spilling x67 to mem
mov [ rsp + 0x98 ], r8; spilling x191 to mem
mulx rcx, r8, rax; x50, x49<- arg1[5] * x10003
movzx r15, r15b
lea rdi, [ r15 + rdi ]
mov r15, [ rsp + 0x8 ]
lea rdi, [r15+rdi]
adcx rbx, rbp
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r15, rbp, [ rsp + 0x70 ]; x58, x57<- arg1[4] * x10002
mov rdx, [ r10 + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0xa0 ], r15; spilling x58 to mem
mov [ rsp + 0xa8 ], rcx; spilling x50 to mem
mulx r15, rcx, [ rsi + 0x8 ]; x144, x143<- arg1[1] * arg2[0]
clc;
adcx r13, r8
mov r8, [ rsp + 0x98 ]; load m64 x191 to register64
mov [ rsp + 0xb0 ], r15; spilling x144 to mem
setc r15b; spill CF x431 to reg (r15)
mov [ rsp + 0xb8 ], rcx; spilling x143 to mem
seto cl; spill OF x427 to reg (rcx)
mov [ rsp + 0xc0 ], r13; spilling x430 to mem
mov r13, r8; x195, copying x191 here, cause x191 is needed in a reg for other than x195, namely all: , x197, x195, size: 2
shrd r13, rdi, 58; x195 <- x193||x191 >> 58
mov [ rsp + 0xc8 ], r13; spilling x195 to mem
mov r13, 0x3ffffffffffffff ; moving imm to reg
and r8, r13; x197 <- x191&0x3ffffffffffffff
sar  cl, 1
adcx rbx, [ rsp + 0x68 ]
adox rbp, [ rsp + 0xc0 ]
clc;
adcx rbp, [ rsp + 0x80 ]
movzx r15, r15b
lea rbx, [ r15 + rbx ]
mov r15, [ rsp + 0xa8 ]
lea rbx, [r15+rbx]
adox rbx, [ rsp + 0xa0 ]
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, [ rsp + 0x90 ]
setc r15b; spill CF x439 to reg (r15)
seto cl; spill OF x443 to reg (rcx)
shr rdi, 58; x196 <- x193>> 58
sar  r15b, 1
adcx rbx, [ rsp + 0x78 ]
adox rbp, [ rsp + 0xb8 ]
movzx rcx, cl
lea rbx, [ rcx + rbx ]
mov rcx, [ rsp + 0x88 ]
lea rbx, [rcx+rbx]
adox rbx, [ rsp + 0xb0 ]
mov rdx, [ r10 + 0x0 ]; arg2[0] to rdx
mulx r15, rcx, [ rsi + 0x10 ]; x128, x127<- arg1[2] * arg2[0]
xor r13, r13
adox rbp, [ rsp + 0x60 ]
adcx rbp, [ rsp + 0xc8 ]
adox rbx, [ rsp + 0x58 ]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0xd0 ], r8; spilling x197 to mem
mulx r13, r8, [ r10 + 0x10 ]; x158, x157<- arg1[0] * arg2[2]
mov rdx, r12; x10005 to rdx
mulx rdx, r12, [ rsi + 0x40 ]; x12, x11<- arg1[8] * x10005
mov [ rsp + 0xd8 ], r13; spilling x158 to mem
mov r13, rdx; preserving value of x12 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0xe0 ], r8; spilling x157 to mem
mov [ rsp + 0xe8 ], r15; spilling x128 to mem
mulx r8, r15, rax; x38, x37<- arg1[6] * x10003
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0xf0 ], rcx; spilling x127 to mem
mov [ rsp + 0xf8 ], r8; spilling x38 to mem
mulx rcx, r8, r14; x26, x25<- arg1[7] * x10004
adcx rdi, rbx
test al, al
adox r12, r8
seto bl; spill OF x391 to reg (rbx)
mov r8, rbp; x458, copying x454 here, cause x454 is needed in a reg for other than x458, namely all: , x458, x460, size: 2
shrd r8, rdi, 58; x458 <- x456||x454 >> 58
mov rdx, [ rsp + 0x70 ]; x10002 to rdx
mov [ rsp + 0x100 ], r8; spilling x458 to mem
mov [ rsp + 0x108 ], r13; spilling x12 to mem
mulx r8, r13, [ rsi + 0x28 ]; x48, x47<- arg1[5] * x10002
mov [ rsp + 0x110 ], r8; spilling x48 to mem
mov r8, rdx; preserving value of x10002 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x118 ], r13; spilling x47 to mem
mov [ rsp + 0x120 ], rcx; spilling x26 to mem
mulx r13, rcx, [ r10 + 0x8 ]; x142, x141<- arg1[1] * arg2[1]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x128 ], r13; spilling x142 to mem
mov [ rsp + 0x130 ], rcx; spilling x141 to mem
mulx r13, rcx, r11; x62, x61<- arg1[3] * x10000
mov rdx, r9; x10001 to rdx
mov [ rsp + 0x138 ], r13; spilling x62 to mem
mulx r9, r13, [ rsi + 0x20 ]; x56, x55<- arg1[4] * x10001
mov [ rsp + 0x140 ], r9; spilling x56 to mem
xor r9, r9
adox r12, r15
mov r15, rdx; preserving value of x10001 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x148 ], rcx; spilling x61 to mem
mulx r9, rcx, [ r10 + 0x10 ]; x140, x139<- arg1[1] * arg2[2]
mov [ rsp + 0x150 ], r9; spilling x140 to mem
mov r9, [ rsp + 0x108 ]; load m64 x12 to register64
movzx rbx, bl
lea r9, [ rbx + r9 ]
adcx r9, [ rsp + 0x120 ]
adox r9, [ rsp + 0xf8 ]
xor rbx, rbx
adox r12, [ rsp + 0x118 ]
adcx r12, r13
setc r13b; spill CF x403 to reg (r13)
seto bl; spill OF x399 to reg (rbx)
shr rdi, 58; x459 <- x456>> 58
sar  bl, 1
adcx r9, [ rsp + 0x110 ]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x158 ], rcx; spilling x139 to mem
mulx rbx, rcx, [ r10 + 0x0 ]; x114, x113<- arg1[3] * arg2[0]
adox r12, [ rsp + 0x148 ]
movzx r13, r13b
lea r9, [ r13 + r9 ]
mov r13, [ rsp + 0x140 ]
lea r9, [r13+r9]
adox r9, [ rsp + 0x138 ]
xor r13, r13
adox r12, [ rsp + 0xf0 ]
adcx r12, [ rsp + 0x130 ]
mov rdx, [ r10 + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x160 ], rbx; spilling x114 to mem
mulx r13, rbx, [ rsi + 0x10 ]; x126, x125<- arg1[2] * arg2[1]
adox r9, [ rsp + 0xe8 ]
mov [ rsp + 0x168 ], r13; spilling x126 to mem
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, [ rsp + 0xe0 ]
adcx r9, [ rsp + 0x128 ]
mov rdx, r11; x10000 to rdx
mulx r11, r13, [ rsi + 0x20 ]; x54, x53<- arg1[4] * x10000
clc;
adcx r12, [ rsp + 0x100 ]
adox r9, [ rsp + 0xd8 ]
mov [ rsp + 0x170 ], rbx; spilling x125 to mem
mov rbx, rdx; preserving value of x10000 into a new reg
mov rdx, [ rsi + 0x40 ]; saving arg1[8] in rdx.
mov [ rsp + 0x178 ], r11; spilling x54 to mem
mulx r14, r11, r14; x10, x9<- arg1[8] * x10004
adcx rdi, r9
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x180 ], rcx; spilling x113 to mem
mulx r9, rcx, rax; x24, x23<- arg1[7] * x10003
mov [ rsp + 0x188 ], r13; spilling x53 to mem
xor r13, r13
adox r11, rcx
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mulx rcx, r13, r8; x36, x35<- arg1[6] * x10002
mov [ rsp + 0x190 ], rcx; spilling x36 to mem
seto cl; spill OF x359 to reg (rcx)
mov [ rsp + 0x198 ], r11; spilling x358 to mem
mov r11, r12; x465, copying x461 here, cause x461 is needed in a reg for other than x465, namely all: , x465, x467, size: 2
shrd r11, rdi, 58; x465 <- x463||x461 >> 58
sar  cl, 1
adcx r9, r14
mov rdx, r15; x10001 to rdx
mulx r15, r14, [ rsi + 0x28 ]; x46, x45<- arg1[5] * x10001
adox r13, [ rsp + 0x198 ]
clc;
adcx r13, r14
adox r9, [ rsp + 0x190 ]
adcx r15, r9
xchg rdx, r8; x10002, swapping with x10001, which is currently in rdx
mulx rcx, r14, [ rsi + 0x38 ]; x22, x21<- arg1[7] * x10002
mov r9, rdx; preserving value of x10002 into a new reg
mov rdx, [ r10 + 0x18 ]; saving arg2[3] in rdx.
mov [ rsp + 0x1a0 ], rcx; spilling x22 to mem
mov [ rsp + 0x1a8 ], r11; spilling x465 to mem
mulx rcx, r11, [ rsi + 0x8 ]; x138, x137<- arg1[1] * arg2[3]
shr rdi, 58; x466 <- x463>> 58
mov [ rsp + 0x1b0 ], rcx; spilling x138 to mem
xor rcx, rcx
adox r13, [ rsp + 0x188 ]
adcx r13, [ rsp + 0x180 ]
adox r15, [ rsp + 0x178 ]
adcx r15, [ rsp + 0x160 ]
test al, al
adox r13, [ rsp + 0x170 ]
adox r15, [ rsp + 0x168 ]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x1b8 ], r11; spilling x137 to mem
mulx rcx, r11, [ r10 + 0x10 ]; x124, x123<- arg1[2] * arg2[2]
adcx r13, [ rsp + 0x158 ]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x1c0 ], rcx; spilling x124 to mem
mov [ rsp + 0x1c8 ], r11; spilling x123 to mem
mulx rcx, r11, [ r10 + 0x18 ]; x156, x155<- arg1[0] * arg2[3]
mov rdx, rax; x10003 to rdx
mulx rdx, rax, [ rsi + 0x40 ]; x8, x7<- arg1[8] * x10003
adcx r15, [ rsp + 0x150 ]
add r13, r11; could be done better, if r0 has been u8 as well
adcx rcx, r15
mov r11, rdx; preserving value of x8 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x1d0 ], rcx; spilling x388 to mem
mulx r15, rcx, [ r10 + 0x20 ]; x154, x153<- arg1[0] * arg2[4]
add rax, r14; could be done better, if r0 has been u8 as well
mov rdx, r8; x10001 to rdx
mulx r8, r14, [ rsi + 0x38 ]; x20, x19<- arg1[7] * x10001
mov [ rsp + 0x1d8 ], r15; spilling x154 to mem
mov [ rsp + 0x1e0 ], r8; spilling x20 to mem
mulx r15, r8, [ rsi + 0x30 ]; x34, x33<- arg1[6] * x10001
xchg rdx, rbx; x10000, swapping with x10001, which is currently in rdx
mov [ rsp + 0x1e8 ], r14; spilling x19 to mem
mov [ rsp + 0x1f0 ], rcx; spilling x153 to mem
mulx r14, rcx, [ rsi + 0x28 ]; x44, x43<- arg1[5] * x10000
mov [ rsp + 0x1f8 ], r14; spilling x44 to mem
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, [ rsp + 0x1a8 ]
adox rdi, [ rsp + 0x1d0 ]
adcx r11, [ rsp + 0x1a0 ]
add rax, r8; could be done better, if r0 has been u8 as well
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rax, rcx
mov r8, rdx; preserving value of x10000 into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mulx rcx, r14, [ rsi + 0x18 ]; x112, x111<- arg1[3] * arg2[1]
adcx r15, r11
mov rdx, [ r10 + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x200 ], rcx; spilling x112 to mem
mulx r11, rcx, [ rsi + 0x20 ]; x102, x101<- arg1[4] * arg2[0]
adox r15, [ rsp + 0x1f8 ]
mov [ rsp + 0x208 ], r13; spilling x468 to mem
mov r13, rdi; x473, copying x470 here, cause x470 is needed in a reg for other than x473, namely all: , x472, x473, size: 2
shr r13, 58; x473 <- x470>> 58
mov [ rsp + 0x210 ], r13; spilling x473 to mem
xor r13, r13
adox rax, rcx
adox r11, r15
adcx rax, r14
mov r14, [ rsp + 0x208 ]; load m64 x468 to register64
setc cl; spill CF x343 to reg (rcx)
mov r15, r14; x472, copying x468 here, cause x468 is needed in a reg for other than x472, namely all: , x472, x474, size: 2
shrd r15, rdi, 58; x472 <- x470||x468 >> 58
sar  cl, 1
adcx r11, [ rsp + 0x200 ]
adox rax, [ rsp + 0x1c8 ]
clc;
adcx rax, [ rsp + 0x1b8 ]
adox r11, [ rsp + 0x1c0 ]
mov rdx, [ rsi + 0x40 ]; arg1[8] to rdx
mulx r9, rdi, r9; x6, x5<- arg1[8] * x10002
mov rcx, -0x3 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rax, [ rsp + 0x1f0 ]
setc cl; spill CF x351 to reg (rcx)
clc;
adcx rdi, [ rsp + 0x1e8 ]
movzx rcx, cl
lea r11, [ rcx + r11 ]
mov rcx, [ rsp + 0x1b0 ]
lea r11, [rcx+r11]
mov rdx, [ r10 + 0x28 ]; arg2[5] to rdx
mulx rcx, r13, [ rsi + 0x0 ]; x152, x151<- arg1[0] * arg2[5]
adcx r9, [ rsp + 0x1e0 ]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x218 ], rcx; spilling x152 to mem
mov [ rsp + 0x220 ], r13; spilling x151 to mem
mulx rcx, r13, [ r10 + 0x0 ]; x92, x91<- arg1[5] * arg2[0]
adox r11, [ rsp + 0x1d8 ]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x228 ], rcx; spilling x92 to mem
mov [ rsp + 0x230 ], r13; spilling x91 to mem
mulx rcx, r13, r8; x32, x31<- arg1[6] * x10000
test al, al
adox rdi, r13
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x238 ], rdi; spilling x298 to mem
mulx r13, rdi, [ r10 + 0x30 ]; x150, x149<- arg1[0] * arg2[6]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x240 ], r13; spilling x150 to mem
mov [ rsp + 0x248 ], rdi; spilling x149 to mem
mulx r13, rdi, [ r10 + 0x10 ]; x110, x109<- arg1[3] * arg2[2]
adcx rax, r15
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x250 ], r13; spilling x110 to mem
mulx r15, r13, [ r10 + 0x18 ]; x122, x121<- arg1[2] * arg2[3]
adox rcx, r9
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x258 ], r15; spilling x122 to mem
mulx r9, r15, [ r10 + 0x8 ]; x100, x99<- arg1[4] * arg2[1]
adcx r11, [ rsp + 0x210 ]
mov [ rsp + 0x260 ], r9; spilling x100 to mem
mov r9, [ rsp + 0x230 ]; load m64 x91 to register64
mov [ rsp + 0x268 ], r13; spilling x121 to mem
xor r13, r13
adox r9, [ rsp + 0x238 ]
adox rcx, [ rsp + 0x228 ]
adcx r9, r15
setc r15b; spill CF x307 to reg (r15)
mov r13, rax; x479, copying x475 here, cause x475 is needed in a reg for other than x479, namely all: , x481, x479, size: 2
shrd r13, r11, 58; x479 <- x477||x475 >> 58
mov rdx, [ r10 + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x270 ], r13; spilling x479 to mem
mov [ rsp + 0x278 ], rcx; spilling x304 to mem
mulx r13, rcx, [ rsi + 0x8 ]; x134, x133<- arg1[1] * arg2[5]
mov rdx, [ r10 + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x280 ], r13; spilling x134 to mem
mov [ rsp + 0x288 ], rcx; spilling x133 to mem
mulx r13, rcx, [ rsi + 0x8 ]; x136, x135<- arg1[1] * arg2[4]
add r9, rdi; could be done better, if r0 has been u8 as well
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r9, [ rsp + 0x268 ]
mov rdi, [ rsp + 0x278 ]; load m64 x304 to register64
movzx r15, r15b
lea rdi, [ r15 + rdi ]
mov r15, [ rsp + 0x260 ]
lea rdi, [r15+rdi]
adcx rdi, [ rsp + 0x250 ]
adox rdi, [ rsp + 0x258 ]
xor r15, r15
adox r9, rcx
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx rcx, r15, r8; x18, x17<- arg1[7] * x10000
adcx r9, [ rsp + 0x220 ]
adox r13, rdi
adcx r13, [ rsp + 0x218 ]
mov rdx, rbx; x10001 to rdx
mulx rdx, rbx, [ rsi + 0x40 ]; x4, x3<- arg1[8] * x10001
xor rdi, rdi
adox r9, [ rsp + 0x270 ]
mov rdi, rdx; preserving value of x4 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x290 ], r9; spilling x482 to mem
mov [ rsp + 0x298 ], rcx; spilling x18 to mem
mulx r9, rcx, [ r10 + 0x18 ]; x108, x107<- arg1[3] * arg2[3]
mov [ rsp + 0x2a0 ], r9; spilling x108 to mem
seto r9b; spill OF x483 to reg (r9)
shr r11, 58; x480 <- x477>> 58
sar  r9b, 1
adcx r11, r13
adox rbx, r15
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mulx r15, r13, [ r10 + 0x0 ]; x84, x83<- arg1[6] * arg2[0]
clc;
adcx rbx, r13
adox rdi, [ rsp + 0x298 ]
adcx r15, rdi
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r9, r13, [ r10 + 0x38 ]; x148, x147<- arg1[0] * arg2[7]
mov rdx, [ r10 + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x2a8 ], r9; spilling x148 to mem
mulx rdi, r9, [ rsi + 0x20 ]; x98, x97<- arg1[4] * arg2[2]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x2b0 ], r13; spilling x147 to mem
mov [ rsp + 0x2b8 ], rdi; spilling x98 to mem
mulx r13, rdi, [ r10 + 0x8 ]; x90, x89<- arg1[5] * arg2[1]
add rbx, rdi; could be done better, if r0 has been u8 as well
mov rdi, [ rsp + 0x290 ]; load m64 x482 to register64
mov [ rsp + 0x2c0 ], r15; spilling x268 to mem
setc r15b; spill CF x271 to reg (r15)
mov [ rsp + 0x2c8 ], r13; spilling x90 to mem
mov r13, rdi; x486, copying x482 here, cause x482 is needed in a reg for other than x486, namely all: , x488, x486, size: 2
shrd r13, r11, 58; x486 <- x484||x482 >> 58
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x2d0 ], r13; spilling x486 to mem
mov byte [ rsp + 0x2d8 ], r15b; spilling byte x271 to mem
mulx r13, r15, [ r10 + 0x20 ]; x120, x119<- arg1[2] * arg2[4]
shr r11, 58; x487 <- x484>> 58
mov [ rsp + 0x2e0 ], r11; spilling x487 to mem
xor r11, r11
adox rbx, r9
adcx rbx, rcx
mov rdx, [ r10 + 0x28 ]; arg2[5] to rdx
mulx rcx, r9, [ rsi + 0x10 ]; x118, x117<- arg1[2] * arg2[5]
mov r11, [ rsp + 0x2c0 ]; load m64 x268 to register64
mov [ rsp + 0x2e8 ], rcx; spilling x118 to mem
movzx rcx, byte [ rsp + 0x2d8 ]; load byte memx271 to register64
lea r11, [ rcx + r11 ]
mov rcx, [ rsp + 0x2c8 ]
lea r11, [rcx+r11]
seto cl; spill OF x275 to reg (rcx)
mov [ rsp + 0x2f0 ], r9; spilling x117 to mem
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, r15
mov rdx, [ r10 + 0x10 ]; arg2[2] to rdx
mulx r15, r9, [ rsi + 0x28 ]; x88, x87<- arg1[5] * arg2[2]
movzx rcx, cl
lea r11, [ rcx + r11 ]
mov rcx, [ rsp + 0x2b8 ]
lea r11, [rcx+r11]
mov rdx, r8; x10000 to rdx
mulx rdx, r8, [ rsi + 0x40 ]; x2, x1<- arg1[8] * x10000
mov rcx, rdx; preserving value of x2 into a new reg
mov rdx, [ r10 + 0x18 ]; saving arg2[3] in rdx.
mov [ rsp + 0x2f8 ], r15; spilling x88 to mem
mov [ rsp + 0x300 ], r9; spilling x87 to mem
mulx r15, r9, [ rsi + 0x20 ]; x96, x95<- arg1[4] * arg2[3]
adcx r11, [ rsp + 0x2a0 ]
mov rdx, [ r10 + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x308 ], r15; spilling x96 to mem
mov [ rsp + 0x310 ], r9; spilling x95 to mem
mulx r15, r9, [ rsi + 0x38 ]; x78, x77<- arg1[7] * arg2[0]
clc;
adcx rbx, [ rsp + 0x288 ]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x318 ], rcx; spilling x2 to mem
mov [ rsp + 0x320 ], r15; spilling x78 to mem
mulx rcx, r15, [ r10 + 0x8 ]; x82, x81<- arg1[6] * arg2[1]
mov [ rsp + 0x328 ], rcx; spilling x82 to mem
setc cl; spill CF x287 to reg (rcx)
clc;
adcx rbx, [ rsp + 0x248 ]
adox r13, r11
movzx rcx, cl
lea r13, [ rcx + r13 ]
mov rcx, [ rsp + 0x280 ]
lea r13, [rcx+r13]
mov rdx, [ r10 + 0x20 ]; arg2[4] to rdx
mulx r11, rcx, [ rsi + 0x18 ]; x106, x105<- arg1[3] * arg2[4]
adcx r13, [ rsp + 0x240 ]
test al, al
adox r8, r9
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x330 ], rbp; spilling x454 to mem
mulx r9, rbp, [ r10 + 0x30 ]; x116, x115<- arg1[2] * arg2[6]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x338 ], r9; spilling x116 to mem
mov [ rsp + 0x340 ], rbp; spilling x115 to mem
mulx r9, rbp, [ r10 + 0x30 ]; x132, x131<- arg1[1] * arg2[6]
adcx rbx, [ rsp + 0x2d0 ]
adcx r13, [ rsp + 0x2e0 ]
mov [ rsp + 0x348 ], r9; spilling x132 to mem
seto r9b; spill OF x231 to reg (r9)
mov [ rsp + 0x350 ], r11; spilling x106 to mem
mov r11, r13; x494, copying x491 here, cause x491 is needed in a reg for other than x494, namely all: , x494, x493, size: 2
shr r11, 58; x494 <- x491>> 58
mov [ rsp + 0x358 ], r11; spilling x494 to mem
mov r11, rbx; x493, copying x489 here, cause x489 is needed in a reg for other than x493, namely all: , x495, x493, size: 2
shrd r11, r13, 58; x493 <- x491||x489 >> 58
xor r13, r13
adox r8, r15
adcx r8, [ rsp + 0x300 ]
mov r15, [ rsp + 0x318 ]; load m64 x2 to register64
movzx r9, r9b
lea r15, [ r9 + r15 ]
mov r9, [ rsp + 0x320 ]
lea r15, [r9+r15]
setc r9b; spill CF x239 to reg (r9)
clc;
adcx r8, [ rsp + 0x310 ]
mov [ rsp + 0x360 ], r11; spilling x493 to mem
setc r11b; spill CF x243 to reg (r11)
clc;
adcx r8, rcx
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mulx rcx, r13, [ r10 + 0x10 ]; x80, x79<- arg1[6] * arg2[2]
adox r15, [ rsp + 0x328 ]
mov [ rsp + 0x368 ], rcx; spilling x80 to mem
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, [ rsp + 0x2f0 ]
seto cl; spill OF x251 to reg (rcx)
mov [ rsp + 0x370 ], r13; spilling x79 to mem
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, rbp
movzx r9, r9b
lea r15, [ r9 + r15 ]
mov r9, [ rsp + 0x2f8 ]
lea r15, [r9+r15]
setc bpl; spill CF x247 to reg (rbp)
clc;
adcx r8, [ rsp + 0x2b0 ]
mov rdx, [ r10 + 0x28 ]; arg2[5] to rdx
mulx r9, r13, [ rsi + 0x18 ]; x104, x103<- arg1[3] * arg2[5]
movzx r11, r11b
lea r15, [ r11 + r15 ]
mov r11, [ rsp + 0x308 ]
lea r15, [r11+r15]
movzx rbp, bpl
lea r15, [ rbp + r15 ]
mov rbp, [ rsp + 0x350 ]
lea r15, [rbp+r15]
movzx rcx, cl
lea r15, [ rcx + r15 ]
mov rcx, [ rsp + 0x2e8 ]
lea r15, [rcx+r15]
adox r15, [ rsp + 0x348 ]
adcx r15, [ rsp + 0x2a8 ]
add r8, [ rsp + 0x360 ]; could be done better, if r0 has been u8 as well
mov rdx, [ r10 + 0x0 ]; arg2[0] to rdx
mulx r11, rbp, [ rsi + 0x40 ]; x74, x73<- arg1[8] * arg2[0]
adcx r15, [ rsp + 0x358 ]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x378 ], r9; spilling x104 to mem
mulx rcx, r9, [ r10 + 0x8 ]; x76, x75<- arg1[7] * arg2[1]
mov [ rsp + 0x380 ], r13; spilling x103 to mem
xor r13, r13
adox rbp, r9
mov rdx, [ r10 + 0x38 ]; arg2[7] to rdx
mulx r9, r13, [ rsi + 0x8 ]; x130, x129<- arg1[1] * arg2[7]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x388 ], r9; spilling x130 to mem
mov [ rsp + 0x390 ], r13; spilling x129 to mem
mulx r9, r13, [ r10 + 0x18 ]; x86, x85<- arg1[5] * arg2[3]
adcx rbp, [ rsp + 0x370 ]
adox rcx, r11
adcx rcx, [ rsp + 0x368 ]
test al, al
adox rbp, r13
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r11, r13, [ r10 + 0x20 ]; x94, x93<- arg1[4] * arg2[4]
adox r9, rcx
adcx rbp, r13
mov rcx, 0x3ffffffffffffff ; moving imm to reg
setc r13b; spill CF x211 to reg (r13)
mov [ rsp + 0x398 ], r9; spilling x208 to mem
mov r9, [ rsp + 0x330 ]; x460, copying x454 here, cause x454 is needed in a reg for other than x460, namely all: , x460, size: 1
and r9, rcx; x460 <- x454&0x3ffffffffffffff
mov rcx, r8; x500, copying x496 here, cause x496 is needed in a reg for other than x500, namely all: , x500, x502, size: 2
shrd rcx, r15, 58; x500 <- x498||x496 >> 58
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x3a0 ], r9; spilling x460 to mem
mov [ rsp + 0x3a8 ], rcx; spilling x500 to mem
mulx r9, rcx, [ r10 + 0x40 ]; x146, x145<- arg1[0] * arg2[8]
test al, al
adox rbp, [ rsp + 0x380 ]
movzx r13, r13b
lea r11, [ r13 + r11 ]
adcx r11, [ rsp + 0x398 ]
clc;
adcx rbp, [ rsp + 0x340 ]
adox r11, [ rsp + 0x378 ]
adcx r11, [ rsp + 0x338 ]
shr r15, 58; x501 <- x498>> 58
xor r13, r13
adox rbp, [ rsp + 0x390 ]
adcx rbp, rcx
adox r11, [ rsp + 0x388 ]
mov rcx, -0x3 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbp, [ rsp + 0x3a8 ]
adcx r9, r11
adox r15, r9
mov r11, rbp; x507, copying x503 here, cause x503 is needed in a reg for other than x507, namely all: , x509, x507, size: 2
shrd r11, r15, 57; x507 <- x505||x503 >> 57
shr r15, 57; x508 <- x505>> 57
mov r9, 0x3ffffffffffffff ; moving imm to reg
and rdi, r9; x488 <- x482&0x3ffffffffffffff
adox r11, [ rsp + 0xd0 ]
adox r15, r13
mov r13, r11; x513, copying x510 here, cause x510 is needed in a reg for other than x513, namely all: , x513, x514, size: 2
shrd r13, r15, 58; x513 <- x512||x510 >> 58
and r12, r9; x467 <- x461&0x3ffffffffffffff
add r13, [ rsp + 0x3a0 ]
mov r15, 0x1ffffffffffffff ; moving imm to reg
and rbp, r15; x509 <- x503&0x1ffffffffffffff
mov rcx, r13; x516, copying x515 here, cause x515 is needed in a reg for other than x516, namely all: , x517, x516, size: 2
shr rcx, 58; x516 <- x515>> 58
and r14, r9; x474 <- x468&0x3ffffffffffffff
mov r15, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r15 + 0x28 ], rdi; out1[5] = x488
and r13, r9; x517 <- x515&0x3ffffffffffffff
and r8, r9; x502 <- x496&0x3ffffffffffffff
and r11, r9; x514 <- x510&0x3ffffffffffffff
and rax, r9; x481 <- x475&0x3ffffffffffffff
mov [ r15 + 0x38 ], r8; out1[7] = x502
mov [ r15 + 0x18 ], r14; out1[3] = x474
mov [ r15 + 0x8 ], r13; out1[1] = x517
mov [ r15 + 0x0 ], r11; out1[0] = x514
and rbx, r9; x495 <- x489&0x3ffffffffffffff
mov [ r15 + 0x20 ], rax; out1[4] = x481
mov [ r15 + 0x40 ], rbp; out1[8] = x509
lea rcx, [ rcx + r12 ]
mov [ r15 + 0x30 ], rbx; out1[6] = x495
mov [ r15 + 0x10 ], rcx; out1[2] = x518
mov rbx, [ rsp + 0x3b0 ]; restoring from stack
mov rbp, [ rsp + 0x3b8 ]; restoring from stack
mov r12, [ rsp + 0x3c0 ]; restoring from stack
mov r13, [ rsp + 0x3c8 ]; restoring from stack
mov r14, [ rsp + 0x3d0 ]; restoring from stack
mov r15, [ rsp + 0x3d8 ]; restoring from stack
add rsp, 0x3e0 
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; clocked at 2200 MHz
; first cyclecount 370.5, best 258.20512820512823, lastGood 266
; seed 4172627766484181 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4986442 ms / 60000 runs=> 83.10736666666666ms/run
; Time spent for assembling and measureing (initial batch_size=40, initial num_batches=101): 176631 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.035422250975745834
; number reverted permutation/ tried permutation: 18574 / 29939 =62.039%
; number reverted decision/ tried decision: 17728 / 30062 =58.971%