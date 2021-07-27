SECTION .text
	GLOBAL mul_p521
mul_p521:
sub rsp, 0x2d8 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x2a8 ], rbx; saving to stack
mov [ rsp + 0x2b0 ], rbp; saving to stack
mov [ rsp + 0x2b8 ], r12; saving to stack
mov [ rsp + 0x2c0 ], r13; saving to stack
mov [ rsp + 0x2c8 ], r14; saving to stack
mov [ rsp + 0x2d0 ], r15; saving to stack
mov rax, rdx; preserving value of arg2 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r10, r11, [ rax + 0x0 ]; x162, x161<- arg1[0] * arg2[0]
imul rbx, [ rax + 0x38 ], 0x2; x10001 <- arg2[7] * 0x2
imul rbp, [ rax + 0x40 ], 0x2; x10000 <- arg2[8] * 0x2
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r12, r13, rbp; x72, x71<- arg1[1] * x10000
imul r14, [ rax + 0x20 ], 0x2; x10004 <- arg2[4] * 0x2
imul r15, [ rax + 0x30 ], 0x2; x10002 <- arg2[6] * 0x2
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mulx rcx, r8, r14; x52, x51<- arg1[5] * x10004
imul r9, [ rax + 0x8 ], 0x2; x10007 <- arg2[1] * 0x2
mov rdx, rbx; x10001 to rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx rbx, rdi, [ rsi + 0x10 ]; x70, x69<- arg1[2] * x10001
mov [ rsp + 0x8 ], r10; spilling x162 to mem
imul r10, [ rax + 0x18 ], 0x2; x10005 <- arg2[3] * 0x2
mov [ rsp + 0x10 ], r12; spilling x72 to mem
mov r12, rdx; preserving value of x10001 into a new reg
mov rdx, [ rsi + 0x40 ]; saving arg1[8] in rdx.
mov [ rsp + 0x18 ], r11; spilling x161 to mem
mulx r9, r11, r9; x16, x15<- arg1[8] * x10007
mov rdx, r15; x10002 to rdx
mov [ rsp + 0x20 ], r13; spilling x71 to mem
mulx r15, r13, [ rsi + 0x18 ]; x66, x65<- arg1[3] * x10002
mov [ rsp + 0x28 ], rbx; spilling x70 to mem
imul rbx, [ rax + 0x28 ], 0x2; x10003 <- arg2[5] * 0x2
mov [ rsp + 0x30 ], rbp; spilling x10000 to mem
imul rbp, [ rax + 0x10 ], 0x2; x10006 <- arg2[2] * 0x2
xchg rdx, rbp; x10006, swapping with x10002, which is currently in rdx
mov [ rsp + 0x38 ], rdi; spilling x69 to mem
mov [ rsp + 0x40 ], r15; spilling x66 to mem
mulx rdi, r15, [ rsi + 0x38 ]; x30, x29<- arg1[7] * x10006
mov [ rsp + 0x48 ], rcx; spilling x52 to mem
xor rcx, rcx
adox r11, r15
adox rdi, r9
xchg rdx, r10; x10005, swapping with x10006, which is currently in rdx
mulx r9, r15, [ rsi + 0x30 ]; x42, x41<- arg1[6] * x10005
adcx r11, r15
adcx r9, rdi
mov rdi, rdx; preserving value of x10005 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r15, rcx, rbx; x60, x59<- arg1[4] * x10003
mov [ rsp + 0x50 ], r15; spilling x60 to mem
xor r15, r15
adox r11, r8
adcx r11, rcx
setc r8b; spill CF x176 to reg (r8)
clc;
adcx r11, r13
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx r13, rcx, rdi; x28, x27<- arg1[7] * x10005
mov rdx, [ rsi + 0x40 ]; arg1[8] to rdx
mulx r10, r15, r10; x14, x13<- arg1[8] * x10006
adox r9, [ rsp + 0x48 ]
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x58 ], r10; spilling x14 to mem
mov [ rsp + 0x60 ], r13; spilling x28 to mem
mulx r10, r13, [ rsi + 0x8 ]; x144, x143<- arg1[1] * arg2[0]
movzx r8, r8b
lea r9, [ r8 + r9 ]
mov r8, [ rsp + 0x50 ]
lea r9, [r8+r9]
mov rdx, rbx; x10003 to rdx
mulx rbx, r8, [ rsi + 0x28 ]; x50, x49<- arg1[5] * x10003
xchg rdx, r12; x10001, swapping with x10003, which is currently in rdx
mov [ rsp + 0x68 ], r10; spilling x144 to mem
mov [ rsp + 0x70 ], r13; spilling x143 to mem
mulx r10, r13, [ rsi + 0x18 ]; x64, x63<- arg1[3] * x10001
adcx r9, [ rsp + 0x40 ]
xchg rdx, r14; x10004, swapping with x10001, which is currently in rdx
mov [ rsp + 0x78 ], r10; spilling x64 to mem
mov [ rsp + 0x80 ], rbx; spilling x50 to mem
mulx r10, rbx, [ rsi + 0x30 ]; x40, x39<- arg1[6] * x10004
test al, al
adox r11, [ rsp + 0x38 ]
adox r9, [ rsp + 0x28 ]
adcx r11, [ rsp + 0x20 ]
mov [ rsp + 0x88 ], r13; spilling x63 to mem
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, rcx
mov rcx, rdx; preserving value of x10004 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x90 ], r10; spilling x40 to mem
mulx r13, r10, rbp; x58, x57<- arg1[4] * x10002
mov [ rsp + 0x98 ], r13; spilling x58 to mem
mov r13, [ rsp + 0x58 ]; load m64 x14 to register64
adox r13, [ rsp + 0x60 ]
mov [ rsp + 0xa0 ], r10; spilling x57 to mem
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, [ rsp + 0x18 ]
adcx r9, [ rsp + 0x10 ]
adox r9, [ rsp + 0x8 ]
mov r10, r11; x195, copying x191 here, cause x191 is needed in a reg for other than x195, namely all: , x195, x197, size: 2
shrd r10, r9, 58; x195 <- x193||x191 >> 58
mov [ rsp + 0xa8 ], r10; spilling x195 to mem
xor r10, r10
adox r15, rbx
adcx r15, r8
adox r13, [ rsp + 0x90 ]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r8, rbx, [ rsp + 0x30 ]; x68, x67<- arg1[2] * x10000
setc r10b; spill CF x431 to reg (r10)
shr r9, 58; x196 <- x193>> 58
mov [ rsp + 0xb0 ], r9; spilling x196 to mem
xor r9, r9
adox r15, [ rsp + 0xa0 ]
adcx r15, [ rsp + 0x88 ]
mov rdx, rbp; x10002 to rdx
mulx rbp, r9, [ rsi + 0x28 ]; x48, x47<- arg1[5] * x10002
movzx r10, r10b
lea r13, [ r10 + r13 ]
mov r10, [ rsp + 0x80 ]
lea r13, [r10+r13]
adox r13, [ rsp + 0x98 ]
mov r10, rdx; preserving value of x10002 into a new reg
mov rdx, [ rax + 0x8 ]; saving arg2[1] in rdx.
mov [ rsp + 0xb8 ], rbp; spilling x48 to mem
mov [ rsp + 0xc0 ], r9; spilling x47 to mem
mulx rbp, r9, [ rsi + 0x0 ]; x160, x159<- arg1[0] * arg2[1]
adcx r13, [ rsp + 0x78 ]
mov [ rsp + 0xc8 ], rbp; spilling x160 to mem
xor rbp, rbp
adox r15, rbx
adcx r15, [ rsp + 0x70 ]
mov rdx, [ rsi + 0x40 ]; arg1[8] to rdx
mulx rdi, rbx, rdi; x12, x11<- arg1[8] * x10005
adox r8, r13
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r13, rbp, [ rax + 0x0 ]; x128, x127<- arg1[2] * arg2[0]
mov [ rsp + 0xd0 ], r13; spilling x128 to mem
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, r9
adcx r8, [ rsp + 0x68 ]
clc;
adcx r15, [ rsp + 0xa8 ]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx r9, r13, rcx; x26, x25<- arg1[7] * x10004
adox r8, [ rsp + 0xc8 ]
adcx r8, [ rsp + 0xb0 ]
mov [ rsp + 0xd8 ], rbp; spilling x127 to mem
mov rbp, r15; x458, copying x454 here, cause x454 is needed in a reg for other than x458, namely all: , x460, x458, size: 2
shrd rbp, r8, 58; x458 <- x456||x454 >> 58
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0xe0 ], rbp; spilling x458 to mem
mov [ rsp + 0xe8 ], rdi; spilling x12 to mem
mulx rbp, rdi, [ rsi + 0x8 ]; x142, x141<- arg1[1] * arg2[1]
test al, al
adox rbx, r13
adox r9, [ rsp + 0xe8 ]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0xf0 ], rbp; spilling x142 to mem
mulx r13, rbp, r12; x38, x37<- arg1[6] * x10003
adcx rbx, rbp
adcx r13, r9
xor r9, r9
adox rbx, [ rsp + 0xc0 ]
adox r13, [ rsp + 0xb8 ]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx rbp, r9, [ rsi + 0x0 ]; x158, x157<- arg1[0] * arg2[2]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0xf8 ], rbp; spilling x158 to mem
mov [ rsp + 0x100 ], r9; spilling x157 to mem
mulx rbp, r9, [ rsp + 0x30 ]; x62, x61<- arg1[3] * x10000
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x108 ], rdi; spilling x141 to mem
mov [ rsp + 0x110 ], rbp; spilling x62 to mem
mulx rdi, rbp, r14; x56, x55<- arg1[4] * x10001
adcx rbx, rbp
adcx rdi, r13
add rbx, r9; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r13, r9, [ rax + 0x18 ]; x156, x155<- arg1[0] * arg2[3]
adcx rdi, [ rsp + 0x110 ]
add rbx, [ rsp + 0xd8 ]; could be done better, if r0 has been u8 as well
adcx rdi, [ rsp + 0xd0 ]
shr r8, 58; x459 <- x456>> 58
add rbx, [ rsp + 0x108 ]; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x118 ], r13; spilling x156 to mem
mulx rbp, r13, [ rax + 0x8 ]; x126, x125<- arg1[2] * arg2[1]
mov [ rsp + 0x120 ], r9; spilling x155 to mem
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, [ rsp + 0x100 ]
adcx rdi, [ rsp + 0xf0 ]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x128 ], rbp; spilling x126 to mem
mulx r9, rbp, [ rsp + 0x30 ]; x54, x53<- arg1[4] * x10000
clc;
adcx rbx, [ rsp + 0xe0 ]
adox rdi, [ rsp + 0xf8 ]
adcx r8, rdi
mov rdx, r12; x10003 to rdx
mulx r12, rdi, [ rsi + 0x38 ]; x24, x23<- arg1[7] * x10003
mov [ rsp + 0x130 ], r13; spilling x125 to mem
mov r13, rdx; preserving value of x10003 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0x138 ], r9; spilling x54 to mem
mov [ rsp + 0x140 ], rbp; spilling x53 to mem
mulx r9, rbp, r10; x36, x35<- arg1[6] * x10002
mov rdx, [ rsi + 0x40 ]; arg1[8] to rdx
mov [ rsp + 0x148 ], r8; spilling x463 to mem
mulx rcx, r8, rcx; x10, x9<- arg1[8] * x10004
mov [ rsp + 0x150 ], rbx; spilling x461 to mem
xor rbx, rbx
adox r8, rdi
adcx r8, rbp
adox r12, rcx
adcx r9, r12
mov rdx, r14; x10001 to rdx
mulx r14, rdi, [ rsi + 0x28 ]; x46, x45<- arg1[5] * x10001
mov rbp, [ rsp + 0x150 ]; load m64 x461 to register64
mov rcx, [ rsp + 0x148 ]; load m64 x463 to register64
mov r12, rbp; x465, copying x461 here, cause x461 is needed in a reg for other than x465, namely all: , x467, x465, size: 2
shrd r12, rcx, 58; x465 <- x463||x461 >> 58
mov rbx, rdx; preserving value of x10001 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x158 ], r12; spilling x465 to mem
mov [ rsp + 0x160 ], r9; spilling x364 to mem
mulx r12, r9, [ rax + 0x10 ]; x140, x139<- arg1[1] * arg2[2]
test al, al
adox r8, rdi
adox r14, [ rsp + 0x160 ]
mov rdx, [ rsi + 0x40 ]; arg1[8] to rdx
mulx r13, rdi, r13; x8, x7<- arg1[8] * x10003
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x168 ], r13; spilling x8 to mem
mov [ rsp + 0x170 ], rdi; spilling x7 to mem
mulx r13, rdi, [ rsi + 0x18 ]; x114, x113<- arg1[3] * arg2[0]
adcx r8, [ rsp + 0x140 ]
mov [ rsp + 0x178 ], r12; spilling x140 to mem
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, rdi
adcx r14, [ rsp + 0x138 ]
clc;
adcx r8, [ rsp + 0x130 ]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rdi, r12, [ rax + 0x20 ]; x154, x153<- arg1[0] * arg2[4]
adox r13, r14
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x180 ], rdi; spilling x154 to mem
mulx r14, rdi, [ rsp + 0x30 ]; x44, x43<- arg1[5] * x10000
adcx r13, [ rsp + 0x128 ]
add r8, r9; could be done better, if r0 has been u8 as well
mov rdx, r10; x10002 to rdx
mulx r10, r9, [ rsi + 0x38 ]; x22, x21<- arg1[7] * x10002
adcx r13, [ rsp + 0x178 ]
add r8, [ rsp + 0x120 ]; could be done better, if r0 has been u8 as well
mov [ rsp + 0x188 ], r12; spilling x153 to mem
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, [ rsp + 0x158 ]
mov r12, rdx; preserving value of x10002 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x190 ], r14; spilling x44 to mem
mov [ rsp + 0x198 ], rdi; spilling x43 to mem
mulx r14, rdi, [ rax + 0x10 ]; x124, x123<- arg1[2] * arg2[2]
adcx r13, [ rsp + 0x118 ]
mov [ rsp + 0x1a0 ], r14; spilling x124 to mem
mov r14, 0x3ffffffffffffff ; moving imm to reg
mov [ rsp + 0x1a8 ], rdi; spilling x123 to mem
seto dil; spill OF x469 to reg (rdi)
and r11, r14; x197 <- x191&0x3ffffffffffffff
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x1b0 ], r11; spilling x197 to mem
mulx r14, r11, [ rsi + 0x20 ]; x102, x101<- arg1[4] * arg2[0]
shr rcx, 58; x466 <- x463>> 58
sar  dil, 1
adcx rcx, r13
mov rdi, r8; x472, copying x468 here, cause x468 is needed in a reg for other than x472, namely all: , x474, x472, size: 2
shrd rdi, rcx, 58; x472 <- x470||x468 >> 58
mov r13, 0x3ffffffffffffff ; moving imm to reg
and r8, r13; x474 <- x468&0x3ffffffffffffff
adox r9, [ rsp + 0x170 ]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x1b8 ], rdi; spilling x472 to mem
mulx r13, rdi, rbx; x34, x33<- arg1[6] * x10001
adcx r9, rdi
adox r10, [ rsp + 0x168 ]
adcx r13, r10
add r9, [ rsp + 0x198 ]; could be done better, if r0 has been u8 as well
mov rdi, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rdi + 0x18 ], r8; out1[3] = x474
adcx r13, [ rsp + 0x190 ]
add r9, r11; could be done better, if r0 has been u8 as well
adcx r14, r13
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mulx r11, r10, [ rsi + 0x8 ]; x138, x137<- arg1[1] * arg2[3]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx r8, r13, [ rsi + 0x18 ]; x112, x111<- arg1[3] * arg2[1]
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
xor rdi, rdi
adox r9, r13
adcx r9, [ rsp + 0x1a8 ]
adox r8, r14
mov r14, -0x3 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r9, r10
adcx r8, [ rsp + 0x1a0 ]
mov rdx, r12; x10002 to rdx
mulx rdx, r12, [ rsi + 0x40 ]; x6, x5<- arg1[8] * x10002
adox r11, r8
add r9, [ rsp + 0x188 ]; could be done better, if r0 has been u8 as well
adcx r11, [ rsp + 0x180 ]
mov r10, rdx; preserving value of x6 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx r13, r8, [ rax + 0x0 ]; x92, x91<- arg1[5] * arg2[0]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rdi, r14, [ rax + 0x20 ]; x136, x135<- arg1[1] * arg2[4]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x1c0 ], rdi; spilling x136 to mem
mov [ rsp + 0x1c8 ], r14; spilling x135 to mem
mulx rdi, r14, rbx; x20, x19<- arg1[7] * x10001
shr rcx, 58; x473 <- x470>> 58
mov [ rsp + 0x1d0 ], r13; spilling x92 to mem
xor r13, r13
adox r9, [ rsp + 0x1b8 ]
adcx r12, r14
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r14, r13, [ rax + 0x18 ]; x122, x121<- arg1[2] * arg2[3]
adox rcx, r11
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x1d8 ], r14; spilling x122 to mem
mulx r11, r14, [ rsp + 0x30 ]; x32, x31<- arg1[6] * x10000
mov [ rsp + 0x1e0 ], r13; spilling x121 to mem
setc r13b; spill CF x295 to reg (r13)
mov [ rsp + 0x1e8 ], r11; spilling x32 to mem
mov r11, r9; x479, copying x475 here, cause x475 is needed in a reg for other than x479, namely all: , x479, x481, size: 2
shrd r11, rcx, 58; x479 <- x477||x475 >> 58
shr rcx, 58; x480 <- x477>> 58
sar  r13b, 1
adcx rdi, r10
adox r12, r14
clc;
adcx r12, r8
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx r10, r8, [ rsi + 0x18 ]; x110, x109<- arg1[3] * arg2[2]
adox rdi, [ rsp + 0x1e8 ]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r13, r14, [ rax + 0x28 ]; x152, x151<- arg1[0] * arg2[5]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x1f0 ], rcx; spilling x480 to mem
mov [ rsp + 0x1f8 ], r11; spilling x479 to mem
mulx rcx, r11, [ rsi + 0x20 ]; x100, x99<- arg1[4] * arg2[1]
mov [ rsp + 0x200 ], r13; spilling x152 to mem
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, r11
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mulx r11, r13, [ rsi + 0x0 ]; x150, x149<- arg1[0] * arg2[6]
adcx rdi, [ rsp + 0x1d0 ]
clc;
adcx r12, r8
adox rcx, rdi
mov rdx, [ rsi + 0x40 ]; arg1[8] to rdx
mulx rbx, r8, rbx; x4, x3<- arg1[8] * x10001
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, [ rsp + 0x1e0 ]
seto dil; spill OF x315 to reg (rdi)
mov [ rsp + 0x208 ], r11; spilling x150 to mem
mov r11, -0x2 ; moving imm to reg
inc r11; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, [ rsp + 0x1c8 ]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x210 ], r13; spilling x149 to mem
mulx r11, r13, [ rsi + 0x10 ]; x120, x119<- arg1[2] * arg2[4]
adcx r10, rcx
movzx rdi, dil
lea r10, [ rdi + r10 ]
mov rdi, [ rsp + 0x1d8 ]
lea r10, [rdi+r10]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx rcx, rdi, [ rsp + 0x30 ]; x18, x17<- arg1[7] * x10000
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x218 ], r11; spilling x120 to mem
mov [ rsp + 0x220 ], r13; spilling x119 to mem
mulx r11, r13, [ rsi + 0x20 ]; x98, x97<- arg1[4] * arg2[2]
clc;
adcx r12, r14
adox r10, [ rsp + 0x1c0 ]
adcx r10, [ rsp + 0x200 ]
add r12, [ rsp + 0x1f8 ]; could be done better, if r0 has been u8 as well
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, rdi
adox rcx, rbx
adcx r10, [ rsp + 0x1f0 ]
mov rbx, r12; x486, copying x482 here, cause x482 is needed in a reg for other than x486, namely all: , x486, x488, size: 2
shrd rbx, r10, 58; x486 <- x484||x482 >> 58
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mulx rdi, r14, [ rax + 0x0 ]; x84, x83<- arg1[6] * arg2[0]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x228 ], rbx; spilling x486 to mem
mov [ rsp + 0x230 ], r11; spilling x98 to mem
mulx rbx, r11, [ rsi + 0x28 ]; x90, x89<- arg1[5] * arg2[1]
test al, al
adox r8, r14
adox rdi, rcx
adcx r8, r11
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, r13
adcx rbx, rdi
adox rbx, [ rsp + 0x230 ]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r13, r14, [ rax + 0x28 ]; x134, x133<- arg1[1] * arg2[5]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mulx r11, rdi, [ rsi + 0x18 ]; x108, x107<- arg1[3] * arg2[3]
shr r10, 58; x487 <- x484>> 58
add r8, rdi; could be done better, if r0 has been u8 as well
mov rdx, [ rsp + 0x30 ]; x10000 to rdx
mulx rdx, rdi, [ rsi + 0x40 ]; x2, x1<- arg1[8] * x10000
adcx r11, rbx
add r8, [ rsp + 0x220 ]; could be done better, if r0 has been u8 as well
adcx r11, [ rsp + 0x218 ]
test al, al
adox r8, r14
mov rbx, rdx; preserving value of x2 into a new reg
mov rdx, [ rax + 0x30 ]; saving arg2[6] in rdx.
mulx r14, rcx, [ rsi + 0x8 ]; x132, x131<- arg1[1] * arg2[6]
adox r13, r11
adcx r8, [ rsp + 0x210 ]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x238 ], r15; spilling x454 to mem
mulx r11, r15, [ rax + 0x0 ]; x78, x77<- arg1[7] * arg2[0]
adcx r13, [ rsp + 0x208 ]
test al, al
adox rdi, r15
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x240 ], r14; spilling x132 to mem
mulx r15, r14, [ rsi + 0x30 ]; x82, x81<- arg1[6] * arg2[1]
adcx r8, [ rsp + 0x228 ]
adox r11, rbx
adcx r10, r13
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mulx rbx, r13, [ rsi + 0x0 ]; x148, x147<- arg1[0] * arg2[7]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x248 ], rbx; spilling x148 to mem
mov [ rsp + 0x250 ], r13; spilling x147 to mem
mulx rbx, r13, [ rsi + 0x18 ]; x106, x105<- arg1[3] * arg2[4]
mov [ rsp + 0x258 ], rcx; spilling x131 to mem
xor rcx, rcx
adox rdi, r14
adox r15, r11
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mulx r14, r11, [ rax + 0x10 ]; x88, x87<- arg1[5] * arg2[2]
mov rcx, r8; x493, copying x489 here, cause x489 is needed in a reg for other than x493, namely all: , x495, x493, size: 2
shrd rcx, r10, 58; x493 <- x491||x489 >> 58
mov [ rsp + 0x260 ], rcx; spilling x493 to mem
xor rcx, rcx
adox rdi, r11
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mulx r11, rcx, [ rsi + 0x20 ]; x96, x95<- arg1[4] * arg2[3]
adcx rdi, rcx
adox r14, r15
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r15, rcx, [ rax + 0x28 ]; x118, x117<- arg1[2] * arg2[5]
adcx r11, r14
test al, al
adox rdi, r13
adcx rdi, rcx
adox rbx, r11
adcx r15, rbx
xor r13, r13
adox rdi, [ rsp + 0x258 ]
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx r14, rcx, [ rsi + 0x40 ]; x74, x73<- arg1[8] * arg2[0]
adox r15, [ rsp + 0x240 ]
shr r10, 58; x494 <- x491>> 58
xor r11, r11
adox rdi, [ rsp + 0x250 ]
adox r15, [ rsp + 0x248 ]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx r13, rbx, [ rsi + 0x20 ]; x94, x93<- arg1[4] * arg2[4]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x268 ], r13; spilling x94 to mem
mulx r11, r13, [ rsi + 0x10 ]; x116, x115<- arg1[2] * arg2[6]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x270 ], r11; spilling x116 to mem
mov [ rsp + 0x278 ], r13; spilling x115 to mem
mulx r11, r13, [ rsi + 0x8 ]; x130, x129<- arg1[1] * arg2[7]
adcx rdi, [ rsp + 0x260 ]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x280 ], r11; spilling x130 to mem
mov [ rsp + 0x288 ], r13; spilling x129 to mem
mulx r11, r13, [ rax + 0x28 ]; x104, x103<- arg1[3] * arg2[5]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x290 ], r11; spilling x104 to mem
mov [ rsp + 0x298 ], r13; spilling x103 to mem
mulx r11, r13, [ rsi + 0x38 ]; x76, x75<- arg1[7] * arg2[1]
adcx r10, r15
mov r15, rdi; x500, copying x496 here, cause x496 is needed in a reg for other than x500, namely all: , x500, x502, size: 2
shrd r15, r10, 58; x500 <- x498||x496 >> 58
mov [ rsp + 0x2a0 ], r15; spilling x500 to mem
xor r15, r15
adox rcx, r13
adox r11, r14
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mulx r14, r13, [ rax + 0x10 ]; x80, x79<- arg1[6] * arg2[2]
adcx rcx, r13
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mulx r13, r15, [ rsi + 0x28 ]; x86, x85<- arg1[5] * arg2[3]
adcx r14, r11
test al, al
adox rcx, r15
adox r13, r14
adcx rcx, rbx
adcx r13, [ rsp + 0x268 ]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rbx, r11, [ rax + 0x40 ]; x146, x145<- arg1[0] * arg2[8]
xor r15, r15
adox rcx, [ rsp + 0x298 ]
adcx rcx, [ rsp + 0x278 ]
adox r13, [ rsp + 0x290 ]
mov r14, -0x3 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rcx, [ rsp + 0x288 ]
adcx r13, [ rsp + 0x270 ]
clc;
adcx rcx, r11
adox r13, [ rsp + 0x280 ]
adcx rbx, r13
mov r11, 0x3ffffffffffffff ; moving imm to reg
mov r13, [ rsp + 0x238 ]; x460, copying x454 here, cause x454 is needed in a reg for other than x460, namely all: , x460, size: 1
and r13, r11; x460 <- x454&0x3ffffffffffffff
shr r10, 58; x501 <- x498>> 58
xor r14, r14
adox rcx, [ rsp + 0x2a0 ]
adox r10, rbx
and rbp, r11; x467 <- x461&0x3ffffffffffffff
mov r15, 0x1ffffffffffffff ; moving imm to reg
mov rbx, rcx; x509, copying x503 here, cause x503 is needed in a reg for other than x509, namely all: , x509, x507, size: 2
and rbx, r15; x509 <- x503&0x1ffffffffffffff
shrd rcx, r10, 57; x507 <- x505||x503 >> 57
and r9, r11; x481 <- x475&0x3ffffffffffffff
adox rcx, [ rsp + 0x1b0 ]
seto r14b; spill OF x511 to reg (r14)
shr r10, 57; x508 <- x505>> 57
movzx r15, r14b; x512, copying x511 here, cause x511 is needed in a reg for other than x512, namely all: , x512, size: 1
lea r15, [ r15 + r10 ]
and rdi, r11; x502 <- x496&0x3ffffffffffffff
mov r14, rcx; x513, copying x510 here, cause x510 is needed in a reg for other than x513, namely all: , x513, x514, size: 2
shrd r14, r15, 58; x513 <- x512||x510 >> 58
and rcx, r11; x514 <- x510&0x3ffffffffffffff
lea r14, [ r14 + r13 ]
mov r13, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r13 + 0x0 ], rcx; out1[0] = x514
mov r10, r14; x516, copying x515 here, cause x515 is needed in a reg for other than x516, namely all: , x516, x517, size: 2
shr r10, 58; x516 <- x515>> 58
and r12, r11; x488 <- x482&0x3ffffffffffffff
and r14, r11; x517 <- x515&0x3ffffffffffffff
mov [ r13 + 0x20 ], r9; out1[4] = x481
mov [ r13 + 0x8 ], r14; out1[1] = x517
and r8, r11; x495 <- x489&0x3ffffffffffffff
lea r10, [ r10 + rbp ]
mov [ r13 + 0x10 ], r10; out1[2] = x518
mov [ r13 + 0x38 ], rdi; out1[7] = x502
mov [ r13 + 0x28 ], r12; out1[5] = x488
mov [ r13 + 0x40 ], rbx; out1[8] = x509
mov [ r13 + 0x30 ], r8; out1[6] = x495
mov rbx, [ rsp + 0x2a8 ]; restoring from stack
mov rbp, [ rsp + 0x2b0 ]; restoring from stack
mov r12, [ rsp + 0x2b8 ]; restoring from stack
mov r13, [ rsp + 0x2c0 ]; restoring from stack
mov r14, [ rsp + 0x2c8 ]; restoring from stack
mov r15, [ rsp + 0x2d0 ]; restoring from stack
add rsp, 0x2d8 
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; clocked at 2200 MHz
; first cyclecount 217.17, best 139.53125, lastGood 144.28125
; seed 380019983455042 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3015708 ms / 60000 runs=> 50.2618ms/run
; Time spent for assembling and measureing (initial batch_size=65, initial num_batches=101): 120003 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.03979264570707774
; number reverted permutation/ tried permutation: 19393 / 30014 =64.613%
; number reverted decision/ tried decision: 18237 / 29987 =60.816%