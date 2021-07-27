SECTION .text
	GLOBAL mul_p521
mul_p521:
sub rsp, 0x2b8 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x288 ], rbx; saving to stack
mov [ rsp + 0x290 ], rbp; saving to stack
mov [ rsp + 0x298 ], r12; saving to stack
mov [ rsp + 0x2a0 ], r13; saving to stack
mov [ rsp + 0x2a8 ], r14; saving to stack
mov [ rsp + 0x2b0 ], r15; saving to stack
imul rax, [ rdx + 0x38 ], 0x2; x10001 <- arg2[7] * 0x2
mov r10, rdx; preserving value of arg2 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r11, rbx, [ r10 + 0x0 ]; x162, x161<- arg1[0] * arg2[0]
imul rbp, [ r10 + 0x30 ], 0x2; x10002 <- arg2[6] * 0x2
mov rdx, rax; x10001 to rdx
mulx rax, r12, [ rsi + 0x10 ]; x70, x69<- arg1[2] * x10001
imul r13, [ r10 + 0x28 ], 0x2; x10003 <- arg2[5] * 0x2
imul r14, [ r10 + 0x40 ], 0x2; x10000 <- arg2[8] * 0x2
mov r15, rdx; preserving value of x10001 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx rcx, r8, r13; x60, x59<- arg1[4] * x10003
imul r9, [ r10 + 0x20 ], 0x2; x10004 <- arg2[4] * 0x2
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov [ rsp + 0x8 ], r11; spilling x162 to mem
mulx rdi, r11, r14; x72, x71<- arg1[1] * x10000
mov rdx, rbp; x10002 to rdx
mov [ rsp + 0x10 ], rdi; spilling x72 to mem
mulx rbp, rdi, [ rsi + 0x18 ]; x66, x65<- arg1[3] * x10002
mov [ rsp + 0x18 ], rax; spilling x70 to mem
imul rax, [ r10 + 0x10 ], 0x2; x10006 <- arg2[2] * 0x2
xchg rdx, rax; x10006, swapping with x10002, which is currently in rdx
mov [ rsp + 0x20 ], rbp; spilling x66 to mem
mov [ rsp + 0x28 ], rbx; spilling x161 to mem
mulx rbp, rbx, [ rsi + 0x38 ]; x30, x29<- arg1[7] * x10006
mov [ rsp + 0x30 ], r11; spilling x71 to mem
imul r11, [ r10 + 0x8 ], 0x2; x10007 <- arg2[1] * 0x2
mov [ rsp + 0x38 ], r15; spilling x10001 to mem
imul r15, [ r10 + 0x18 ], 0x2; x10005 <- arg2[3] * 0x2
mov [ rsp + 0x40 ], r12; spilling x69 to mem
mov r12, rdx; preserving value of x10006 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0x48 ], rdi; spilling x65 to mem
mov [ rsp + 0x50 ], rcx; spilling x60 to mem
mulx rdi, rcx, r15; x42, x41<- arg1[6] * x10005
mov rdx, r11; x10007 to rdx
mulx rdx, r11, [ rsi + 0x40 ]; x16, x15<- arg1[8] * x10007
test al, al
adox r11, rbx
adcx r11, rcx
adox rbp, rdx
mov rdx, r9; x10004 to rdx
mulx r9, rbx, [ rsi + 0x28 ]; x52, x51<- arg1[5] * x10004
adcx rdi, rbp
xor rcx, rcx
adox r11, rbx
adcx r11, r8
adox r9, rdi
adcx r9, [ rsp + 0x50 ]
add r11, [ rsp + 0x48 ]; could be done better, if r0 has been u8 as well
mov r8, -0x3 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r11, [ rsp + 0x40 ]
mov rbp, rdx; preserving value of x10004 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx rbx, rdi, [ rsp + 0x38 ]; x64, x63<- arg1[3] * x10001
setc r8b; spill CF x180 to reg (r8)
clc;
adcx r11, [ rsp + 0x30 ]
mov [ rsp + 0x58 ], rbx; spilling x64 to mem
setc bl; spill CF x188 to reg (rbx)
clc;
adcx r11, [ rsp + 0x28 ]
mov rcx, 0x3ffffffffffffff ; moving imm to reg
mov [ rsp + 0x60 ], rdi; spilling x63 to mem
setc dil; spill CF x192 to reg (rdi)
mov [ rsp + 0x68 ], r14; spilling x10000 to mem
seto r14b; spill OF x184 to reg (r14)
mov [ rsp + 0x70 ], r13; spilling x10003 to mem
mov r13, r11; x197, copying x191 here, cause x191 is needed in a reg for other than x197, namely all: , x195, x197, size: 2
and r13, rcx; x197 <- x191&0x3ffffffffffffff
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x78 ], r13; spilling x197 to mem
mulx rcx, r13, [ r10 + 0x8 ]; x160, x159<- arg1[0] * arg2[1]
sar  r8b, 1
adcx r9, [ rsp + 0x20 ]
sar  r14b, 1
adcx r9, [ rsp + 0x18 ]
sar  bl, 1
adcx r9, [ rsp + 0x10 ]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx r8, r14, r15; x28, x27<- arg1[7] * x10005
mov rdx, [ r10 + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x80 ], rcx; spilling x160 to mem
mulx rbx, rcx, [ rsi + 0x8 ]; x144, x143<- arg1[1] * arg2[0]
sar  dil, 1
adcx r9, [ rsp + 0x8 ]
mov rdx, [ rsi + 0x40 ]; arg1[8] to rdx
mulx r12, rdi, r12; x14, x13<- arg1[8] * x10006
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x88 ], r13; spilling x159 to mem
mov [ rsp + 0x90 ], rbx; spilling x144 to mem
mulx r13, rbx, rbp; x40, x39<- arg1[6] * x10004
adox rdi, r14
clc;
adcx rdi, rbx
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r14, rbx, rax; x58, x57<- arg1[4] * x10002
adox r8, r12
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x98 ], rcx; spilling x143 to mem
mulx r12, rcx, [ rsp + 0x70 ]; x50, x49<- arg1[5] * x10003
adcx r13, r8
add rdi, rcx; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r8, rcx, [ rsp + 0x68 ]; x68, x67<- arg1[2] * x10000
mov [ rsp + 0xa0 ], r8; spilling x68 to mem
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rdi, rbx
adcx r12, r13
seto bl; spill OF x435 to reg (rbx)
shrd r11, r9, 58; x195 <- x193||x191 >> 58
sar  bl, 1
adcx r14, r12
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mulx r13, rbx, [ rsp + 0x70 ]; x38, x37<- arg1[6] * x10003
adox rdi, [ rsp + 0x60 ]
clc;
adcx rdi, rcx
adox r14, [ rsp + 0x58 ]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx rcx, r12, [ rsp + 0x38 ]; x56, x55<- arg1[4] * x10001
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rdi, [ rsp + 0x98 ]
adcx r14, [ rsp + 0xa0 ]
adox r14, [ rsp + 0x90 ]
mov [ rsp + 0xa8 ], rcx; spilling x56 to mem
xor rcx, rcx
adox rdi, [ rsp + 0x88 ]
adox r14, [ rsp + 0x80 ]
shr r9, 58; x196 <- x193>> 58
mov rdx, rax; x10002 to rdx
mulx rax, r8, [ rsi + 0x28 ]; x48, x47<- arg1[5] * x10002
test al, al
adox rdi, r11
mov r11, rdx; preserving value of x10002 into a new reg
mov rdx, [ rsi + 0x38 ]; saving arg1[7] in rdx.
mov [ rsp + 0xb0 ], r12; spilling x55 to mem
mulx rcx, r12, rbp; x26, x25<- arg1[7] * x10004
mov rdx, [ r10 + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0xb8 ], rax; spilling x48 to mem
mov [ rsp + 0xc0 ], r13; spilling x38 to mem
mulx rax, r13, [ rsi + 0x0 ]; x158, x157<- arg1[0] * arg2[2]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0xc8 ], rax; spilling x158 to mem
mov [ rsp + 0xd0 ], r13; spilling x157 to mem
mulx rax, r13, [ r10 + 0x0 ]; x128, x127<- arg1[2] * arg2[0]
mov rdx, r15; x10005 to rdx
mulx rdx, r15, [ rsi + 0x40 ]; x12, x11<- arg1[8] * x10005
adox r9, r14
mov r14, rdi; x458, copying x454 here, cause x454 is needed in a reg for other than x458, namely all: , x460, x458, size: 2
shrd r14, r9, 58; x458 <- x456||x454 >> 58
add r15, r12; could be done better, if r0 has been u8 as well
adcx rcx, rdx
test al, al
adox r15, rbx
adcx r15, r8
adox rcx, [ rsp + 0xc0 ]
adcx rcx, [ rsp + 0xb8 ]
xor rbx, rbx
adox r15, [ rsp + 0xb0 ]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r8, r12, [ rsp + 0x68 ]; x62, x61<- arg1[3] * x10000
adcx r15, r12
adox rcx, [ rsp + 0xa8 ]
adcx r8, rcx
add r15, r13; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r13, r12, [ r10 + 0x8 ]; x142, x141<- arg1[1] * arg2[1]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx rcx, rbx, [ rsp + 0x70 ]; x24, x23<- arg1[7] * x10003
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0xd8 ], rcx; spilling x24 to mem
mov [ rsp + 0xe0 ], rbx; spilling x23 to mem
mulx rcx, rbx, [ r10 + 0x8 ]; x126, x125<- arg1[2] * arg2[1]
mov [ rsp + 0xe8 ], rcx; spilling x126 to mem
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, r12
adcx rax, r8
adox r13, rax
test al, al
adox r15, [ rsp + 0xd0 ]
adox r13, [ rsp + 0xc8 ]
mov rdx, [ r10 + 0x18 ]; arg2[3] to rdx
mulx r8, r12, [ rsi + 0x8 ]; x138, x137<- arg1[1] * arg2[3]
mov rdx, r11; x10002 to rdx
mulx r11, rax, [ rsi + 0x30 ]; x36, x35<- arg1[6] * x10002
shr r9, 58; x459 <- x456>> 58
add r15, r14; could be done better, if r0 has been u8 as well
adcx r9, r13
mov r14, rdx; preserving value of x10002 into a new reg
mov rdx, [ rsi + 0x40 ]; saving arg1[8] in rdx.
mulx rbp, r13, rbp; x10, x9<- arg1[8] * x10004
add r13, [ rsp + 0xe0 ]; could be done better, if r0 has been u8 as well
setc cl; spill CF x359 to reg (rcx)
mov [ rsp + 0xf0 ], r8; spilling x138 to mem
mov r8, r15; x465, copying x461 here, cause x461 is needed in a reg for other than x465, namely all: , x467, x465, size: 2
shrd r8, r9, 58; x465 <- x463||x461 >> 58
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0xf8 ], r12; spilling x137 to mem
mov [ rsp + 0x100 ], r8; spilling x465 to mem
mulx r12, r8, [ rsp + 0x38 ]; x46, x45<- arg1[5] * x10001
shr r9, 58; x466 <- x463>> 58
sar  cl, 1
adcx rbp, [ rsp + 0xd8 ]
adox r13, rax
adox r11, rbp
test al, al
adox r13, r8
mov rdx, [ r10 + 0x20 ]; arg2[4] to rdx
mulx rax, rcx, [ rsi + 0x0 ]; x154, x153<- arg1[0] * arg2[4]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r8, rbp, [ r10 + 0x0 ]; x114, x113<- arg1[3] * arg2[0]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x108 ], rax; spilling x154 to mem
mov [ rsp + 0x110 ], rcx; spilling x153 to mem
mulx rax, rcx, [ rsp + 0x68 ]; x44, x43<- arg1[5] * x10000
adox r12, r11
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x118 ], rax; spilling x44 to mem
mulx r11, rax, [ rsp + 0x68 ]; x54, x53<- arg1[4] * x10000
adcx r13, rax
adcx r11, r12
add r13, rbp; could be done better, if r0 has been u8 as well
adcx r8, r11
add r13, rbx; could be done better, if r0 has been u8 as well
mov rdx, [ r10 + 0x18 ]; arg2[3] to rdx
mulx rbx, rbp, [ rsi + 0x0 ]; x156, x155<- arg1[0] * arg2[3]
adcx r8, [ rsp + 0xe8 ]
mov rdx, [ r10 + 0x10 ]; arg2[2] to rdx
mulx r12, rax, [ rsi + 0x8 ]; x140, x139<- arg1[1] * arg2[2]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x120 ], rcx; spilling x43 to mem
mulx r11, rcx, [ r10 + 0x0 ]; x102, x101<- arg1[4] * arg2[0]
test al, al
adox r13, rax
adcx r13, rbp
adox r12, r8
adcx rbx, r12
mov rdx, [ r10 + 0x10 ]; arg2[2] to rdx
mulx rbp, r8, [ rsi + 0x10 ]; x124, x123<- arg1[2] * arg2[2]
mov rdx, [ rsp + 0x70 ]; x10003 to rdx
mulx rdx, rax, [ rsi + 0x40 ]; x8, x7<- arg1[8] * x10003
mov r12, rdx; preserving value of x8 into a new reg
mov rdx, [ rsi + 0x38 ]; saving arg1[7] in rdx.
mov [ rsp + 0x128 ], rbp; spilling x124 to mem
mov [ rsp + 0x130 ], r8; spilling x123 to mem
mulx rbp, r8, r14; x22, x21<- arg1[7] * x10002
mov [ rsp + 0x138 ], r11; spilling x102 to mem
xor r11, r11
adox rax, r8
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mulx r8, r11, [ rsp + 0x38 ]; x34, x33<- arg1[6] * x10001
adox rbp, r12
adcx r13, [ rsp + 0x100 ]
adcx r9, rbx
add rax, r11; could be done better, if r0 has been u8 as well
adcx r8, rbp
mov rbx, r13; x472, copying x468 here, cause x468 is needed in a reg for other than x472, namely all: , x472, x474, size: 2
shrd rbx, r9, 58; x472 <- x470||x468 >> 58
add rax, [ rsp + 0x120 ]; could be done better, if r0 has been u8 as well
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rax, rcx
adcx r8, [ rsp + 0x118 ]
seto cl; spill OF x339 to reg (rcx)
shr r9, 58; x473 <- x470>> 58
sar  cl, 1
adcx r8, [ rsp + 0x138 ]
mov rdx, [ r10 + 0x8 ]; arg2[1] to rdx
mulx r11, rbp, [ rsi + 0x18 ]; x112, x111<- arg1[3] * arg2[1]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx rcx, r12, [ rsp + 0x38 ]; x20, x19<- arg1[7] * x10001
adox rax, rbp
clc;
adcx rax, [ rsp + 0x130 ]
adox r11, r8
mov rdx, [ r10 + 0x18 ]; arg2[3] to rdx
mulx r8, rbp, [ rsi + 0x10 ]; x122, x121<- arg1[2] * arg2[3]
adcx r11, [ rsp + 0x128 ]
mov [ rsp + 0x140 ], r8; spilling x122 to mem
xor r8, r8
adox rax, [ rsp + 0xf8 ]
adcx rax, [ rsp + 0x110 ]
adox r11, [ rsp + 0xf0 ]
adcx r11, [ rsp + 0x108 ]
mov rdx, [ r10 + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x148 ], rbp; spilling x121 to mem
mulx r8, rbp, [ rsi + 0x28 ]; x92, x91<- arg1[5] * arg2[0]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x150 ], r8; spilling x92 to mem
mov [ rsp + 0x158 ], rbp; spilling x91 to mem
mulx r8, rbp, [ r10 + 0x20 ]; x136, x135<- arg1[1] * arg2[4]
mov rdx, [ rsi + 0x40 ]; arg1[8] to rdx
mov [ rsp + 0x160 ], r8; spilling x136 to mem
mulx r14, r8, r14; x6, x5<- arg1[8] * x10002
add r8, r12; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x168 ], rbp; spilling x135 to mem
mulx r12, rbp, [ r10 + 0x28 ]; x152, x151<- arg1[0] * arg2[5]
mov rdx, [ r10 + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x170 ], r12; spilling x152 to mem
mov [ rsp + 0x178 ], rbp; spilling x151 to mem
mulx r12, rbp, [ rsi + 0x18 ]; x110, x109<- arg1[3] * arg2[2]
adcx rcx, r14
add rax, rbx; could be done better, if r0 has been u8 as well
adcx r9, r11
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mulx rbx, r11, [ rsp + 0x68 ]; x32, x31<- arg1[6] * x10000
test al, al
adox r8, r11
adox rbx, rcx
adcx r8, [ rsp + 0x158 ]
mov rdx, [ r10 + 0x18 ]; arg2[3] to rdx
mulx r14, rcx, [ rsi + 0x18 ]; x108, x107<- arg1[3] * arg2[3]
mov rdx, [ r10 + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x180 ], r14; spilling x108 to mem
mulx r11, r14, [ rsi + 0x20 ]; x100, x99<- arg1[4] * arg2[1]
adcx rbx, [ rsp + 0x150 ]
add r8, r14; could be done better, if r0 has been u8 as well
setc r14b; spill CF x307 to reg (r14)
mov [ rsp + 0x188 ], rcx; spilling x107 to mem
mov rcx, rax; x479, copying x475 here, cause x475 is needed in a reg for other than x479, namely all: , x479, x481, size: 2
shrd rcx, r9, 58; x479 <- x477||x475 >> 58
sar  r14b, 1
adcx r11, rbx
adox r8, rbp
adox r12, r11
shr r9, 58; x480 <- x477>> 58
mov rdx, [ rsp + 0x38 ]; x10001 to rdx
mulx rdx, rbp, [ rsi + 0x40 ]; x4, x3<- arg1[8] * x10001
test al, al
adox r8, [ rsp + 0x148 ]
mov rbx, rdx; preserving value of x4 into a new reg
mov rdx, [ r10 + 0x10 ]; saving arg2[2] in rdx.
mulx r14, r11, [ rsi + 0x20 ]; x98, x97<- arg1[4] * arg2[2]
adox r12, [ rsp + 0x140 ]
adcx r8, [ rsp + 0x168 ]
adcx r12, [ rsp + 0x160 ]
mov rdx, [ r10 + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x190 ], r14; spilling x98 to mem
mov [ rsp + 0x198 ], r11; spilling x97 to mem
mulx r14, r11, [ rsi + 0x8 ]; x134, x133<- arg1[1] * arg2[5]
test al, al
adox r8, [ rsp + 0x178 ]
adcx r8, rcx
adox r12, [ rsp + 0x170 ]
adcx r9, r12
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx rcx, r12, [ rsp + 0x68 ]; x18, x17<- arg1[7] * x10000
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x1a0 ], r14; spilling x134 to mem
mov [ rsp + 0x1a8 ], r11; spilling x133 to mem
mulx r14, r11, [ r10 + 0x30 ]; x150, x149<- arg1[0] * arg2[6]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x1b0 ], r14; spilling x150 to mem
mov [ rsp + 0x1b8 ], r11; spilling x149 to mem
mulx r14, r11, [ r10 + 0x20 ]; x120, x119<- arg1[2] * arg2[4]
mov [ rsp + 0x1c0 ], r14; spilling x120 to mem
xor r14, r14
adox rbp, r12
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mulx r12, r14, [ r10 + 0x0 ]; x84, x83<- arg1[6] * arg2[0]
adox rcx, rbx
mov rbx, r8; x486, copying x482 here, cause x482 is needed in a reg for other than x486, namely all: , x486, x488, size: 2
shrd rbx, r9, 58; x486 <- x484||x482 >> 58
add rbp, r14; could be done better, if r0 has been u8 as well
mov rdx, [ r10 + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x1c8 ], rbx; spilling x486 to mem
mulx r14, rbx, [ rsi + 0x28 ]; x90, x89<- arg1[5] * arg2[1]
mov rdx, [ r10 + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x1d0 ], r11; spilling x119 to mem
mov [ rsp + 0x1d8 ], r14; spilling x90 to mem
mulx r11, r14, [ rsi + 0x38 ]; x78, x77<- arg1[7] * arg2[0]
adcx r12, rcx
test al, al
adox rbp, rbx
adox r12, [ rsp + 0x1d8 ]
adcx rbp, [ rsp + 0x198 ]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rcx, rbx, [ r10 + 0x30 ]; x132, x131<- arg1[1] * arg2[6]
adcx r12, [ rsp + 0x190 ]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x1e0 ], rcx; spilling x132 to mem
mov [ rsp + 0x1e8 ], rbx; spilling x131 to mem
mulx rcx, rbx, [ r10 + 0x28 ]; x118, x117<- arg1[2] * arg2[5]
add rbp, [ rsp + 0x188 ]; could be done better, if r0 has been u8 as well
adcx r12, [ rsp + 0x180 ]
add rbp, [ rsp + 0x1d0 ]; could be done better, if r0 has been u8 as well
adcx r12, [ rsp + 0x1c0 ]
shr r9, 58; x487 <- x484>> 58
add rbp, [ rsp + 0x1a8 ]; could be done better, if r0 has been u8 as well
adcx r12, [ rsp + 0x1a0 ]
mov [ rsp + 0x1f0 ], rcx; spilling x118 to mem
xor rcx, rcx
adox rbp, [ rsp + 0x1b8 ]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x1f8 ], rbx; spilling x117 to mem
mulx rcx, rbx, [ r10 + 0x10 ]; x88, x87<- arg1[5] * arg2[2]
adox r12, [ rsp + 0x1b0 ]
adcx rbp, [ rsp + 0x1c8 ]
adcx r9, r12
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x200 ], rcx; spilling x88 to mem
mulx r12, rcx, [ r10 + 0x38 ]; x148, x147<- arg1[0] * arg2[7]
mov rdx, [ rsp + 0x68 ]; x10000 to rdx
mov [ rsp + 0x208 ], r12; spilling x148 to mem
mulx rdx, r12, [ rsi + 0x40 ]; x2, x1<- arg1[8] * x10000
mov [ rsp + 0x210 ], rdi; spilling x454 to mem
mov rdi, rbp; x493, copying x489 here, cause x489 is needed in a reg for other than x493, namely all: , x493, x495, size: 2
shrd rdi, r9, 58; x493 <- x491||x489 >> 58
mov [ rsp + 0x218 ], rdi; spilling x493 to mem
mov rdi, rdx; preserving value of x2 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0x220 ], rcx; spilling x147 to mem
mov [ rsp + 0x228 ], rbx; spilling x87 to mem
mulx rcx, rbx, [ r10 + 0x8 ]; x82, x81<- arg1[6] * arg2[1]
add r12, r14; could be done better, if r0 has been u8 as well
adcx r11, rdi
add r12, rbx; could be done better, if r0 has been u8 as well
adcx rcx, r11
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r14, rdi, [ r10 + 0x18 ]; x96, x95<- arg1[4] * arg2[3]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rbx, r11, [ r10 + 0x40 ]; x146, x145<- arg1[0] * arg2[8]
add r12, [ rsp + 0x228 ]; could be done better, if r0 has been u8 as well
adcx rcx, [ rsp + 0x200 ]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x230 ], rbx; spilling x146 to mem
mov [ rsp + 0x238 ], r11; spilling x145 to mem
mulx rbx, r11, [ r10 + 0x20 ]; x106, x105<- arg1[3] * arg2[4]
test al, al
adox r12, rdi
mov rdx, [ r10 + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x240 ], rbx; spilling x106 to mem
mulx rdi, rbx, [ rsi + 0x10 ]; x116, x115<- arg1[2] * arg2[6]
adcx r12, r11
adox r14, rcx
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, [ rsp + 0x1f8 ]
adcx r14, [ rsp + 0x240 ]
adox r14, [ rsp + 0x1f0 ]
shr r9, 58; x494 <- x491>> 58
add r12, [ rsp + 0x1e8 ]; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r11, rcx, [ r10 + 0x38 ]; x130, x129<- arg1[1] * arg2[7]
adcx r14, [ rsp + 0x1e0 ]
mov rdx, [ r10 + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x248 ], r11; spilling x130 to mem
mov [ rsp + 0x250 ], rcx; spilling x129 to mem
mulx r11, rcx, [ rsi + 0x38 ]; x76, x75<- arg1[7] * arg2[1]
add r12, [ rsp + 0x220 ]; could be done better, if r0 has been u8 as well
adcx r14, [ rsp + 0x208 ]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x258 ], rdi; spilling x116 to mem
mov [ rsp + 0x260 ], rbx; spilling x115 to mem
mulx rdi, rbx, [ r10 + 0x20 ]; x94, x93<- arg1[4] * arg2[4]
add r12, [ rsp + 0x218 ]; could be done better, if r0 has been u8 as well
adcx r9, r14
mov rdx, [ rsi + 0x40 ]; arg1[8] to rdx
mov [ rsp + 0x268 ], rdi; spilling x94 to mem
mulx r14, rdi, [ r10 + 0x0 ]; x74, x73<- arg1[8] * arg2[0]
mov [ rsp + 0x270 ], rbx; spilling x93 to mem
xor rbx, rbx
adox rdi, rcx
adox r11, r14
mov rcx, r12; x500, copying x496 here, cause x496 is needed in a reg for other than x500, namely all: , x500, x502, size: 2
shrd rcx, r9, 58; x500 <- x498||x496 >> 58
mov rdx, [ r10 + 0x10 ]; arg2[2] to rdx
mulx r14, rbx, [ rsi + 0x30 ]; x80, x79<- arg1[6] * arg2[2]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x278 ], rcx; spilling x500 to mem
mov [ rsp + 0x280 ], r11; spilling x200 to mem
mulx rcx, r11, [ r10 + 0x18 ]; x86, x85<- arg1[5] * arg2[3]
test al, al
adox rdi, rbx
adcx rdi, r11
adox r14, [ rsp + 0x280 ]
adcx rcx, r14
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rbx, r11, [ r10 + 0x28 ]; x104, x103<- arg1[3] * arg2[5]
add rdi, [ rsp + 0x270 ]; could be done better, if r0 has been u8 as well
adcx rcx, [ rsp + 0x268 ]
add rdi, r11; could be done better, if r0 has been u8 as well
adcx rbx, rcx
add rdi, [ rsp + 0x260 ]; could be done better, if r0 has been u8 as well
setc r14b; spill CF x219 to reg (r14)
shr r9, 58; x501 <- x498>> 58
sar  r14b, 1
adcx rbx, [ rsp + 0x258 ]
adox rdi, [ rsp + 0x250 ]
adox rbx, [ rsp + 0x248 ]
add rdi, [ rsp + 0x238 ]; could be done better, if r0 has been u8 as well
adcx rbx, [ rsp + 0x230 ]
add rdi, [ rsp + 0x278 ]; could be done better, if r0 has been u8 as well
adcx r9, rbx
mov r11, 0x3ffffffffffffff ; moving imm to reg
and r8, r11; x488 <- x482&0x3ffffffffffffff
mov rcx, rdi; x507, copying x503 here, cause x503 is needed in a reg for other than x507, namely all: , x509, x507, size: 2
shrd rcx, r9, 57; x507 <- x505||x503 >> 57
shr r9, 57; x508 <- x505>> 57
and rbp, r11; x495 <- x489&0x3ffffffffffffff
adox rcx, [ rsp + 0x78 ]
mov r14, 0x0 ; moving imm to reg
adox r9, r14
mov rbx, rcx; x513, copying x510 here, cause x510 is needed in a reg for other than x513, namely all: , x514, x513, size: 2
shrd rbx, r9, 58; x513 <- x512||x510 >> 58
mov r9, 0x1ffffffffffffff ; moving imm to reg
and rdi, r9; x509 <- x503&0x1ffffffffffffff
and rcx, r11; x514 <- x510&0x3ffffffffffffff
and r12, r11; x502 <- x496&0x3ffffffffffffff
mov r14, [ rsp + 0x210 ]; x460, copying x454 here, cause x454 is needed in a reg for other than x460, namely all: , x460, size: 1
and r14, r11; x460 <- x454&0x3ffffffffffffff
lea rbx, [ rbx + r14 ]
mov r14, rbx; x517, copying x515 here, cause x515 is needed in a reg for other than x517, namely all: , x516, x517, size: 2
and r14, r11; x517 <- x515&0x3ffffffffffffff
and rax, r11; x481 <- x475&0x3ffffffffffffff
mov r9, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r9 + 0x40 ], rdi; out1[8] = x509
mov [ r9 + 0x8 ], r14; out1[1] = x517
and r15, r11; x467 <- x461&0x3ffffffffffffff
shr rbx, 58; x516 <- x515>> 58
mov [ r9 + 0x28 ], r8; out1[5] = x488
lea rbx, [ rbx + r15 ]
mov [ r9 + 0x20 ], rax; out1[4] = x481
and r13, r11; x474 <- x468&0x3ffffffffffffff
mov [ r9 + 0x10 ], rbx; out1[2] = x518
mov [ r9 + 0x38 ], r12; out1[7] = x502
mov [ r9 + 0x0 ], rcx; out1[0] = x514
mov [ r9 + 0x30 ], rbp; out1[6] = x495
mov [ r9 + 0x18 ], r13; out1[3] = x474
mov rbx, [ rsp + 0x288 ]; restoring from stack
mov rbp, [ rsp + 0x290 ]; restoring from stack
mov r12, [ rsp + 0x298 ]; restoring from stack
mov r13, [ rsp + 0x2a0 ]; restoring from stack
mov r14, [ rsp + 0x2a8 ]; restoring from stack
mov r15, [ rsp + 0x2b0 ]; restoring from stack
add rsp, 0x2b8 
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; clocked at 4888 MHz
; first cyclecount 248.425, best 162.29787234042553, lastGood 163.0212765957447
; seed 2414091731930389 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3594934 ms / 60000 runs=> 59.91556666666666ms/run
; Time spent for assembling and measureing (initial batch_size=47, initial num_batches=101): 133616 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.03716785899268248
; number reverted permutation/ tried permutation: 19580 / 29930 =65.419%
; number reverted decision/ tried decision: 18924 / 30071 =62.931%