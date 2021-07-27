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
imul rax, [ rdx + 0x28 ], 0x2; x10003 <- arg2[5] * 0x2
imul r10, [ rdx + 0x40 ], 0x2; x10000 <- arg2[8] * 0x2
mov r11, rdx; preserving value of arg2 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx rbx, rbp, r10; x72, x71<- arg1[1] * x10000
imul r12, [ r11 + 0x38 ], 0x2; x10001 <- arg2[7] * 0x2
imul r13, [ r11 + 0x8 ], 0x2; x10007 <- arg2[1] * 0x2
imul r14, [ r11 + 0x10 ], 0x2; x10006 <- arg2[2] * 0x2
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r15, rcx, r12; x70, x69<- arg1[2] * x10001
imul r8, [ r11 + 0x30 ], 0x2; x10002 <- arg2[6] * 0x2
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r9, rdi, [ r11 + 0x0 ]; x162, x161<- arg1[0] * arg2[0]
mov [ rsp + 0x8 ], r10; spilling x10000 to mem
imul r10, [ r11 + 0x20 ], 0x2; x10004 <- arg2[4] * 0x2
mov rdx, r14; x10006 to rdx
mov [ rsp + 0x10 ], r9; spilling x162 to mem
mulx r14, r9, [ rsi + 0x38 ]; x30, x29<- arg1[7] * x10006
mov [ rsp + 0x18 ], rbx; spilling x72 to mem
mov rbx, rdx; preserving value of x10006 into a new reg
mov rdx, [ rsi + 0x40 ]; saving arg1[8] in rdx.
mov [ rsp + 0x20 ], r15; spilling x70 to mem
mulx r13, r15, r13; x16, x15<- arg1[8] * x10007
mov rdx, r10; x10004 to rdx
mov [ rsp + 0x28 ], rdi; spilling x161 to mem
mulx r10, rdi, [ rsi + 0x28 ]; x52, x51<- arg1[5] * x10004
test al, al
adox r15, r9
mov r9, rdx; preserving value of x10004 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x30 ], rbp; spilling x71 to mem
mov [ rsp + 0x38 ], rcx; spilling x69 to mem
mulx rbp, rcx, rax; x60, x59<- arg1[4] * x10003
adox r14, r13
imul r13, [ r11 + 0x18 ], 0x2; x10005 <- arg2[3] * 0x2
mov rdx, r13; x10005 to rdx
mov [ rsp + 0x40 ], rbp; spilling x60 to mem
mulx r13, rbp, [ rsi + 0x30 ]; x42, x41<- arg1[6] * x10005
add r15, rbp; could be done better, if r0 has been u8 as well
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, rdi
seto dil; spill OF x172 to reg (rdi)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r15, rcx
xchg rdx, rax; x10003, swapping with x10005, which is currently in rdx
mulx rcx, rbp, [ rsi + 0x28 ]; x50, x49<- arg1[5] * x10003
mov [ rsp + 0x48 ], rcx; spilling x50 to mem
mov rcx, rdx; preserving value of x10003 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x50 ], rbp; spilling x49 to mem
mov [ rsp + 0x58 ], r12; spilling x10001 to mem
mulx rbp, r12, r8; x66, x65<- arg1[3] * x10002
adcx r13, r14
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x60 ], rbp; spilling x66 to mem
mulx r14, rbp, r9; x40, x39<- arg1[6] * x10004
clc;
adcx r15, r12
movzx rdi, dil
lea r10, [ r10 + r13 ]
lea r10, [ r10 + rdi ]
setc dil; spill CF x180 to reg (rdi)
clc;
adcx r15, [ rsp + 0x38 ]
adox r10, [ rsp + 0x40 ]
mov rdx, [ r11 + 0x0 ]; arg2[0] to rdx
mulx r12, r13, [ rsi + 0x8 ]; x144, x143<- arg1[1] * arg2[0]
movzx rdi, dil
lea r10, [ rdi + r10 ]
mov rdi, [ rsp + 0x60 ]
lea r10, [rdi+r10]
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, [ rsp + 0x30 ]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x68 ], r12; spilling x144 to mem
mulx rdi, r12, [ rsp + 0x58 ]; x64, x63<- arg1[3] * x10001
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x70 ], rdi; spilling x64 to mem
mov [ rsp + 0x78 ], r13; spilling x143 to mem
mulx rdi, r13, rax; x28, x27<- arg1[7] * x10005
mov [ rsp + 0x80 ], r12; spilling x63 to mem
seto r12b; spill OF x188 to reg (r12)
mov [ rsp + 0x88 ], r14; spilling x40 to mem
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, [ rsp + 0x28 ]
adcx r10, [ rsp + 0x20 ]
movzx r12, r12b
lea r10, [ r12 + r10 ]
mov r12, [ rsp + 0x18 ]
lea r10, [r12+r10]
mov rdx, [ r11 + 0x8 ]; arg2[1] to rdx
mulx r12, r14, [ rsi + 0x0 ]; x160, x159<- arg1[0] * arg2[1]
mov rdx, [ rsi + 0x40 ]; arg1[8] to rdx
mov [ rsp + 0x90 ], r12; spilling x160 to mem
mulx rbx, r12, rbx; x14, x13<- arg1[8] * x10006
adox r10, [ rsp + 0x10 ]
mov [ rsp + 0x98 ], r14; spilling x159 to mem
mov r14, r15; x195, copying x191 here, cause x191 is needed in a reg for other than x195, namely all: , x197, x195, size: 2
shrd r14, r10, 58; x195 <- x193||x191 >> 58
add r12, r13; could be done better, if r0 has been u8 as well
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, rbp
mov rdx, r8; x10002 to rdx
mulx r8, rbp, [ rsi + 0x20 ]; x58, x57<- arg1[4] * x10002
adcx rdi, rbx
adox rdi, [ rsp + 0x88 ]
test al, al
adox r12, [ rsp + 0x50 ]
mov rbx, rdx; preserving value of x10002 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0xa0 ], r14; spilling x195 to mem
mulx r13, r14, [ r11 + 0x8 ]; x142, x141<- arg1[1] * arg2[1]
adcx r12, rbp
seto bpl; spill OF x431 to reg (rbp)
mov [ rsp + 0xa8 ], r13; spilling x142 to mem
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, [ rsp + 0x80 ]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0xb0 ], r14; spilling x141 to mem
mulx r13, r14, [ rsp + 0x8 ]; x68, x67<- arg1[2] * x10000
mov rdx, r9; x10004 to rdx
mov [ rsp + 0xb8 ], r13; spilling x68 to mem
mulx r9, r13, [ rsi + 0x38 ]; x26, x25<- arg1[7] * x10004
movzx rbp, bpl
lea rdi, [ rbp + rdi ]
mov rbp, [ rsp + 0x48 ]
lea rdi, [rbp+rdi]
seto bpl; spill OF x439 to reg (rbp)
mov [ rsp + 0xc0 ], r9; spilling x26 to mem
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, r14
adcx r8, rdi
clc;
adcx r12, [ rsp + 0x78 ]
mov r14, rdx; preserving value of x10004 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mulx rdi, r9, rcx; x38, x37<- arg1[6] * x10003
mov [ rsp + 0xc8 ], rdi; spilling x38 to mem
setc dil; spill CF x447 to reg (rdi)
mov [ rsp + 0xd0 ], r9; spilling x37 to mem
seto r9b; spill OF x443 to reg (r9)
shr r10, 58; x196 <- x193>> 58
test al, al
adox r12, [ rsp + 0x98 ]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0xd8 ], r13; spilling x25 to mem
mov [ rsp + 0xe0 ], r10; spilling x196 to mem
mulx r13, r10, [ r11 + 0x0 ]; x128, x127<- arg1[2] * arg2[0]
movzx rbp, bpl
lea r8, [ rbp + r8 ]
adcx r8, [ rsp + 0x70 ]
clc;
adcx r12, [ rsp + 0xa0 ]
movzx r9, r9b
lea r8, [ r9 + r8 ]
mov r9, [ rsp + 0xb8 ]
lea r8, [r9+r8]
movzx rdi, dil
lea r8, [ rdi + r8 ]
mov rdi, [ rsp + 0x68 ]
lea r8, [rdi+r8]
mov rdx, [ rsi + 0x40 ]; arg1[8] to rdx
mulx rax, rbp, rax; x12, x11<- arg1[8] * x10005
adox r8, [ rsp + 0x90 ]
adcx r8, [ rsp + 0xe0 ]
mov r9, r12; x458, copying x454 here, cause x454 is needed in a reg for other than x458, namely all: , x458, x460, size: 2
shrd r9, r8, 58; x458 <- x456||x454 >> 58
add rbp, [ rsp + 0xd8 ]; could be done better, if r0 has been u8 as well
adcx rax, [ rsp + 0xc0 ]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0xe8 ], r13; spilling x128 to mem
mulx rdi, r13, [ rsp + 0x8 ]; x62, x61<- arg1[3] * x10000
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0xf0 ], r9; spilling x458 to mem
mov [ rsp + 0xf8 ], rdi; spilling x62 to mem
mulx r9, rdi, rbx; x48, x47<- arg1[5] * x10002
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x100 ], r10; spilling x127 to mem
mov [ rsp + 0x108 ], r13; spilling x61 to mem
mulx r10, r13, [ r11 + 0x8 ]; x126, x125<- arg1[2] * arg2[1]
add rbp, [ rsp + 0xd0 ]; could be done better, if r0 has been u8 as well
mov [ rsp + 0x110 ], r10; spilling x126 to mem
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, rdi
mov rdx, [ r11 + 0x10 ]; arg2[2] to rdx
mulx rdi, r10, [ rsi + 0x0 ]; x158, x157<- arg1[0] * arg2[2]
adcx rax, [ rsp + 0xc8 ]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x118 ], r13; spilling x125 to mem
mov [ rsp + 0x120 ], rdi; spilling x158 to mem
mulx r13, rdi, [ rsp + 0x58 ]; x56, x55<- arg1[4] * x10001
adox r9, rax
add rbp, rdi; could be done better, if r0 has been u8 as well
adcx r13, r9
mov rdx, rbx; x10002 to rdx
mulx rbx, rax, [ rsi + 0x30 ]; x36, x35<- arg1[6] * x10002
shr r8, 58; x459 <- x456>> 58
mov rdi, rdx; preserving value of x10002 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x128 ], rbx; spilling x36 to mem
mulx r9, rbx, [ rsp + 0x58 ]; x46, x45<- arg1[5] * x10001
mov [ rsp + 0x130 ], r9; spilling x46 to mem
xor r9, r9
adox rbp, [ rsp + 0x108 ]
adcx rbp, [ rsp + 0x100 ]
adox r13, [ rsp + 0xf8 ]
mov [ rsp + 0x138 ], rbx; spilling x45 to mem
mov rbx, -0x3 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbp, [ rsp + 0xb0 ]
setc bl; spill CF x411 to reg (rbx)
clc;
adcx rbp, r10
seto r10b; spill OF x415 to reg (r10)
mov [ rsp + 0x140 ], rax; spilling x35 to mem
mov rax, -0x3 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbp, [ rsp + 0xf0 ]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r9, rax, [ r11 + 0x10 ]; x140, x139<- arg1[1] * arg2[2]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x148 ], r9; spilling x140 to mem
mov [ rsp + 0x150 ], rax; spilling x139 to mem
mulx r9, rax, [ r11 + 0x0 ]; x114, x113<- arg1[3] * arg2[0]
movzx rbx, bl
lea r13, [ rbx + r13 ]
mov rbx, [ rsp + 0xe8 ]
lea r13, [rbx+r13]
mov rdx, rcx; x10003 to rdx
mulx rcx, rbx, [ rsi + 0x38 ]; x24, x23<- arg1[7] * x10003
mov [ rsp + 0x158 ], r9; spilling x114 to mem
mov r9, rdx; preserving value of x10003 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x160 ], rax; spilling x113 to mem
mov [ rsp + 0x168 ], rbp; spilling x461 to mem
mulx rax, rbp, [ r11 + 0x18 ]; x156, x155<- arg1[0] * arg2[3]
mov rdx, r14; x10004 to rdx
mulx rdx, r14, [ rsi + 0x40 ]; x10, x9<- arg1[8] * x10004
movzx r10, r10b
lea r13, [ r10 + r13 ]
mov r10, [ rsp + 0xa8 ]
lea r13, [r10+r13]
mov r10, rdx; preserving value of x10 into a new reg
mov rdx, [ r11 + 0x20 ]; saving arg2[4] in rdx.
mov [ rsp + 0x170 ], rax; spilling x156 to mem
mov [ rsp + 0x178 ], rbp; spilling x155 to mem
mulx rax, rbp, [ rsi + 0x0 ]; x154, x153<- arg1[0] * arg2[4]
adcx r13, [ rsp + 0x120 ]
adox r8, r13
xor r13, r13
adox r14, rbx
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx rbx, r13, [ rsp + 0x8 ]; x54, x53<- arg1[4] * x10000
adox rcx, r10
mov r10, [ rsp + 0x168 ]; load m64 x461 to register64
mov [ rsp + 0x180 ], rax; spilling x154 to mem
mov rax, r10; x465, copying x461 here, cause x461 is needed in a reg for other than x465, namely all: , x467, x465, size: 2
shrd rax, r8, 58; x465 <- x463||x461 >> 58
mov [ rsp + 0x188 ], rbp; spilling x153 to mem
xor rbp, rbp
adox r14, [ rsp + 0x140 ]
adox rcx, [ rsp + 0x128 ]
adcx r14, [ rsp + 0x138 ]
adcx rcx, [ rsp + 0x130 ]
add r14, r13; could be done better, if r0 has been u8 as well
adcx rbx, rcx
add r14, [ rsp + 0x160 ]; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mulx r13, rcx, [ rsp + 0x58 ]; x34, x33<- arg1[6] * x10001
mov rdx, [ r11 + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x190 ], r13; spilling x34 to mem
mulx rbp, r13, [ rsi + 0x10 ]; x124, x123<- arg1[2] * arg2[2]
adcx rbx, [ rsp + 0x158 ]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x198 ], rbp; spilling x124 to mem
mov [ rsp + 0x1a0 ], r13; spilling x123 to mem
mulx rbp, r13, rdi; x22, x21<- arg1[7] * x10002
mov [ rsp + 0x1a8 ], rbp; spilling x22 to mem
xor rbp, rbp
adox r14, [ rsp + 0x118 ]
adox rbx, [ rsp + 0x110 ]
adcx r14, [ rsp + 0x150 ]
mov [ rsp + 0x1b0 ], rcx; spilling x33 to mem
mov rcx, -0x3 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r14, [ rsp + 0x178 ]
adcx rbx, [ rsp + 0x148 ]
seto bpl; spill OF x387 to reg (rbp)
shr r8, 58; x466 <- x463>> 58
test al, al
adox r14, rax
movzx rbp, bpl
lea rbx, [ rbp + rbx ]
adcx rbx, [ rsp + 0x170 ]
adox r8, rbx
mov rdx, r9; x10003 to rdx
mulx rdx, r9, [ rsi + 0x40 ]; x8, x7<- arg1[8] * x10003
mov rax, r14; x472, copying x468 here, cause x468 is needed in a reg for other than x472, namely all: , x474, x472, size: 2
shrd rax, r8, 58; x472 <- x470||x468 >> 58
mov rbp, rdx; preserving value of x8 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx rbx, rcx, [ r11 + 0x0 ]; x102, x101<- arg1[4] * arg2[0]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x1b8 ], r15; spilling x191 to mem
mov [ rsp + 0x1c0 ], rax; spilling x472 to mem
mulx r15, rax, [ rsp + 0x8 ]; x44, x43<- arg1[5] * x10000
test al, al
adox r9, r13
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x1c8 ], rbx; spilling x102 to mem
mulx r13, rbx, [ r11 + 0x8 ]; x112, x111<- arg1[3] * arg2[1]
adcx r9, [ rsp + 0x1b0 ]
adox rbp, [ rsp + 0x1a8 ]
mov [ rsp + 0x1d0 ], r13; spilling x112 to mem
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r9, rax
adcx rbp, [ rsp + 0x190 ]
clc;
adcx r9, rcx
adox r15, rbp
adcx r15, [ rsp + 0x1c8 ]
test al, al
adox r9, rbx
adox r15, [ rsp + 0x1d0 ]
adcx r9, [ rsp + 0x1a0 ]
mov rdx, [ r11 + 0x18 ]; arg2[3] to rdx
mulx rcx, rax, [ rsi + 0x8 ]; x138, x137<- arg1[1] * arg2[3]
mov rdx, [ r11 + 0x20 ]; arg2[4] to rdx
mulx rbx, rbp, [ rsi + 0x8 ]; x136, x135<- arg1[1] * arg2[4]
adcx r15, [ rsp + 0x198 ]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x1d8 ], rbx; spilling x136 to mem
mulx r13, rbx, [ r11 + 0x0 ]; x92, x91<- arg1[5] * arg2[0]
shr r8, 58; x473 <- x470>> 58
test al, al
adox r9, rax
adcx r9, [ rsp + 0x188 ]
adox rcx, r15
mov rdx, [ rsp + 0x58 ]; x10001 to rdx
mulx rax, r15, [ rsi + 0x38 ]; x20, x19<- arg1[7] * x10001
mov [ rsp + 0x1e0 ], rbp; spilling x135 to mem
mov rbp, rdx; preserving value of x10001 into a new reg
mov rdx, [ rsi + 0x40 ]; saving arg1[8] in rdx.
mov [ rsp + 0x1e8 ], r13; spilling x92 to mem
mulx rdi, r13, rdi; x6, x5<- arg1[8] * x10002
mov [ rsp + 0x1f0 ], rbx; spilling x91 to mem
mov rbx, -0x2 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r9, [ rsp + 0x1c0 ]
mov rdx, [ r11 + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x1f8 ], rdi; spilling x6 to mem
mulx rbx, rdi, [ rsi + 0x0 ]; x152, x151<- arg1[0] * arg2[5]
mov rdx, [ r11 + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x200 ], rbx; spilling x152 to mem
mov [ rsp + 0x208 ], rdi; spilling x151 to mem
mulx rbx, rdi, [ rsi + 0x18 ]; x110, x109<- arg1[3] * arg2[2]
adcx rcx, [ rsp + 0x180 ]
adox r8, rcx
add r13, r15; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r15, rcx, [ r11 + 0x18 ]; x122, x121<- arg1[2] * arg2[3]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x210 ], r15; spilling x122 to mem
mov [ rsp + 0x218 ], rbx; spilling x110 to mem
mulx r15, rbx, [ rsp + 0x8 ]; x32, x31<- arg1[6] * x10000
mov [ rsp + 0x220 ], rcx; spilling x121 to mem
setc cl; spill CF x295 to reg (rcx)
mov [ rsp + 0x228 ], rdi; spilling x109 to mem
mov rdi, r9; x479, copying x475 here, cause x475 is needed in a reg for other than x479, namely all: , x481, x479, size: 2
shrd rdi, r8, 58; x479 <- x477||x475 >> 58
add r13, rbx; could be done better, if r0 has been u8 as well
movzx rcx, cl
lea rax, [ rcx + rax ]
mov rcx, [ rsp + 0x1f8 ]
lea rax, [rcx+rax]
adcx r15, rax
add r13, [ rsp + 0x1f0 ]; could be done better, if r0 has been u8 as well
adcx r15, [ rsp + 0x1e8 ]
mov rdx, [ r11 + 0x8 ]; arg2[1] to rdx
mulx rcx, rbx, [ rsi + 0x20 ]; x100, x99<- arg1[4] * arg2[1]
add r13, rbx; could be done better, if r0 has been u8 as well
adcx rcx, r15
add r13, [ rsp + 0x228 ]; could be done better, if r0 has been u8 as well
mov rax, -0x2 ; moving imm to reg
inc rax; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, [ rsp + 0x220 ]
adcx rcx, [ rsp + 0x218 ]
mov rdx, [ r11 + 0x10 ]; arg2[2] to rdx
mulx r15, rbx, [ rsi + 0x20 ]; x98, x97<- arg1[4] * arg2[2]
clc;
adcx r13, [ rsp + 0x1e0 ]
adox rcx, [ rsp + 0x210 ]
adcx rcx, [ rsp + 0x1d8 ]
xor rax, rax
adox r13, [ rsp + 0x208 ]
adcx r13, rdi
setc dil; spill CF x483 to reg (rdi)
seto al; spill OF x323 to reg (rax)
shr r8, 58; x480 <- x477>> 58
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x230 ], r13; spilling x482 to mem
mov [ rsp + 0x238 ], r15; spilling x98 to mem
mulx r13, r15, [ rsp + 0x8 ]; x18, x17<- arg1[7] * x10000
mov rdx, [ r11 + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x240 ], rbx; spilling x97 to mem
mov [ rsp + 0x248 ], r13; spilling x18 to mem
mulx rbx, r13, [ rsi + 0x10 ]; x120, x119<- arg1[2] * arg2[4]
mov rdx, rbp; x10001 to rdx
mulx rdx, rbp, [ rsi + 0x40 ]; x4, x3<- arg1[8] * x10001
sar  al, 1
adcx rcx, [ rsp + 0x200 ]
sar  dil, 1
adcx r8, rcx
mov rax, rdx; preserving value of x4 into a new reg
mov rdx, [ r11 + 0x30 ]; saving arg2[6] in rdx.
mulx rdi, rcx, [ rsi + 0x0 ]; x150, x149<- arg1[0] * arg2[6]
mov rdx, [ r11 + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x250 ], rdi; spilling x150 to mem
mov [ rsp + 0x258 ], rcx; spilling x149 to mem
mulx rdi, rcx, [ rsi + 0x18 ]; x108, x107<- arg1[3] * arg2[3]
adox rbp, r15
mov rdx, [ r11 + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x260 ], rbx; spilling x120 to mem
mulx r15, rbx, [ rsi + 0x30 ]; x84, x83<- arg1[6] * arg2[0]
mov rdx, [ r11 + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x268 ], rdi; spilling x108 to mem
mov [ rsp + 0x270 ], r13; spilling x119 to mem
mulx rdi, r13, [ rsi + 0x10 ]; x118, x117<- arg1[2] * arg2[5]
clc;
adcx rbp, rbx
adox rax, [ rsp + 0x248 ]
setc bl; spill CF x267 to reg (rbx)
mov [ rsp + 0x278 ], rdi; spilling x118 to mem
mov rdi, r8; x487, copying x484 here, cause x484 is needed in a reg for other than x487, namely all: , x486, x487, size: 2
shr rdi, 58; x487 <- x484>> 58
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x280 ], r13; spilling x117 to mem
mov [ rsp + 0x288 ], rdi; spilling x487 to mem
mulx r13, rdi, [ r11 + 0x8 ]; x90, x89<- arg1[5] * arg2[1]
mov rdx, [ r11 + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x290 ], rcx; spilling x107 to mem
mov [ rsp + 0x298 ], r13; spilling x90 to mem
mulx rcx, r13, [ rsi + 0x8 ]; x134, x133<- arg1[1] * arg2[5]
sar  bl, 1
adcx r15, rax
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rbx, rax, [ r11 + 0x20 ]; x106, x105<- arg1[3] * arg2[4]
adox rbp, rdi
clc;
adcx rbp, [ rsp + 0x240 ]
adox r15, [ rsp + 0x298 ]
mov rdx, [ r11 + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x2a0 ], rbx; spilling x106 to mem
mulx rdi, rbx, [ rsi + 0x38 ]; x78, x77<- arg1[7] * arg2[0]
adcx r15, [ rsp + 0x238 ]
mov [ rsp + 0x2a8 ], rax; spilling x105 to mem
mov rax, [ rsp + 0x230 ]; load m64 x482 to register64
mov [ rsp + 0x2b0 ], rcx; spilling x134 to mem
mov rcx, rax; x486, copying x482 here, cause x482 is needed in a reg for other than x486, namely all: , x488, x486, size: 2
shrd rcx, r8, 58; x486 <- x484||x482 >> 58
add rbp, [ rsp + 0x290 ]; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x40 ]; arg1[8] to rdx
mov [ rsp + 0x2b8 ], rdi; spilling x78 to mem
mulx r8, rdi, [ rsp + 0x8 ]; x2, x1<- arg1[8] * x10000
mov [ rsp + 0x2c0 ], r8; spilling x2 to mem
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, [ rsp + 0x270 ]
adcx r15, [ rsp + 0x268 ]
adox r15, [ rsp + 0x260 ]
test al, al
adox rbp, r13
adcx rbp, [ rsp + 0x258 ]
mov rdx, [ r11 + 0x8 ]; arg2[1] to rdx
mulx r13, r8, [ rsi + 0x30 ]; x82, x81<- arg1[6] * arg2[1]
mov [ rsp + 0x2c8 ], r12; spilling x454 to mem
setc r12b; spill CF x291 to reg (r12)
clc;
adcx rbp, rcx
setc cl; spill CF x490 to reg (rcx)
clc;
adcx rdi, rbx
mov rbx, [ rsp + 0x2b8 ]; load m64 x78 to register64
adcx rbx, [ rsp + 0x2c0 ]
adox r15, [ rsp + 0x2b0 ]
mov [ rsp + 0x2d0 ], rbp; spilling x489 to mem
xor rbp, rbp
adox rdi, r8
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r8, rbp, [ r11 + 0x18 ]; x96, x95<- arg1[4] * arg2[3]
adox r13, rbx
sar  r12b, 1
adcx r15, [ rsp + 0x250 ]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r12, rbx, [ r11 + 0x30 ]; x132, x131<- arg1[1] * arg2[6]
sar  cl, 1
adcx r15, [ rsp + 0x288 ]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x2d8 ], r12; spilling x132 to mem
mulx rcx, r12, [ r11 + 0x10 ]; x88, x87<- arg1[5] * arg2[2]
adox rdi, r12
adox rcx, r13
test al, al
adox rdi, rbp
mov rbp, [ rsp + 0x2d0 ]; load m64 x489 to register64
seto r13b; spill OF x243 to reg (r13)
mov r12, rbp; x493, copying x489 here, cause x489 is needed in a reg for other than x493, namely all: , x493, x495, size: 2
shrd r12, r15, 58; x493 <- x491||x489 >> 58
sar  r13b, 1
adcx r8, rcx
adox rdi, [ rsp + 0x2a8 ]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rcx, r13, [ r11 + 0x38 ]; x148, x147<- arg1[0] * arg2[7]
mov rdx, [ r11 + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x2e0 ], r12; spilling x493 to mem
mov [ rsp + 0x2e8 ], rcx; spilling x148 to mem
mulx r12, rcx, [ rsi + 0x28 ]; x86, x85<- arg1[5] * arg2[3]
adox r8, [ rsp + 0x2a0 ]
mov [ rsp + 0x2f0 ], r12; spilling x86 to mem
xor r12, r12
adox rdi, [ rsp + 0x280 ]
adcx rdi, rbx
adox r8, [ rsp + 0x278 ]
adcx r8, [ rsp + 0x2d8 ]
mov rbx, 0x3ffffffffffffff ; moving imm to reg
and rbp, rbx; x495 <- x489&0x3ffffffffffffff
shr r15, 58; x494 <- x491>> 58
xor rbx, rbx
adox rdi, r13
mov rdx, [ rsi + 0x40 ]; arg1[8] to rdx
mulx r12, r13, [ r11 + 0x0 ]; x74, x73<- arg1[8] * arg2[0]
adox r8, [ rsp + 0x2e8 ]
adcx rdi, [ rsp + 0x2e0 ]
adcx r15, r8
mov r8, rdi; x500, copying x496 here, cause x496 is needed in a reg for other than x500, namely all: , x500, x502, size: 2
shrd r8, r15, 58; x500 <- x498||x496 >> 58
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x2f8 ], rbp; spilling x495 to mem
mulx rbx, rbp, [ r11 + 0x8 ]; x76, x75<- arg1[7] * arg2[1]
shr r15, 58; x501 <- x498>> 58
test al, al
adox r13, rbp
adox rbx, r12
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mulx r12, rbp, [ r11 + 0x10 ]; x80, x79<- arg1[6] * arg2[2]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x300 ], r15; spilling x501 to mem
mov [ rsp + 0x308 ], r8; spilling x500 to mem
mulx r15, r8, [ r11 + 0x40 ]; x146, x145<- arg1[0] * arg2[8]
adcx r13, rbp
adcx r12, rbx
xor rbx, rbx
adox r13, rcx
mov rdx, [ r11 + 0x38 ]; arg2[7] to rdx
mulx rcx, rbp, [ rsi + 0x8 ]; x130, x129<- arg1[1] * arg2[7]
mov rdx, [ r11 + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x310 ], r15; spilling x146 to mem
mulx rbx, r15, [ rsi + 0x20 ]; x94, x93<- arg1[4] * arg2[4]
mov rdx, [ r11 + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x318 ], rcx; spilling x130 to mem
mov [ rsp + 0x320 ], r8; spilling x145 to mem
mulx rcx, r8, [ rsi + 0x18 ]; x104, x103<- arg1[3] * arg2[5]
adox r12, [ rsp + 0x2f0 ]
adcx r13, r15
adcx rbx, r12
mov rdx, [ r11 + 0x30 ]; arg2[6] to rdx
mulx r15, r12, [ rsi + 0x10 ]; x116, x115<- arg1[2] * arg2[6]
test al, al
adox r13, r8
adcx r13, r12
adox rcx, rbx
mov r8, 0x3ffffffffffffff ; moving imm to reg
setc bl; spill CF x219 to reg (rbx)
mov r12, [ rsp + 0x1b8 ]; x197, copying x191 here, cause x191 is needed in a reg for other than x197, namely all: , x197, size: 1
and r12, r8; x197 <- x191&0x3ffffffffffffff
mov [ rsp + 0x328 ], r12; spilling x197 to mem
mov r12, [ rsp + 0x2c8 ]; x460, copying x454 here, cause x454 is needed in a reg for other than x460, namely all: , x460, size: 1
and r12, r8; x460 <- x454&0x3ffffffffffffff
sar  bl, 1
adcx r15, rcx
adox r13, rbp
clc;
adcx r13, [ rsp + 0x320 ]
adox r15, [ rsp + 0x318 ]
adcx r15, [ rsp + 0x310 ]
xor rbp, rbp
adox r13, [ rsp + 0x308 ]
adox r15, [ rsp + 0x300 ]
mov rbx, r13; x507, copying x503 here, cause x503 is needed in a reg for other than x507, namely all: , x507, x509, size: 2
shrd rbx, r15, 57; x507 <- x505||x503 >> 57
shr r15, 57; x508 <- x505>> 57
add rbx, [ rsp + 0x328 ]; could be done better, if r0 has been u8 as well
setc cl; spill CF x511 to reg (rcx)
and r10, r8; x467 <- x461&0x3ffffffffffffff
and r9, r8; x481 <- x475&0x3ffffffffffffff
mov rbp, rbx; x514, copying x510 here, cause x510 is needed in a reg for other than x514, namely all: , x513, x514, size: 2
and rbp, r8; x514 <- x510&0x3ffffffffffffff
movzx r8, cl; x512, copying x511 here, cause x511 is needed in a reg for other than x512, namely all: , x512, size: 1
lea r8, [ r8 + r15 ]
mov r15, [ rsp + 0x0 ]; load m64 out1 to register64
mov rcx, [ rsp + 0x2f8 ]; TMP = x495
mov [ r15 + 0x30 ], rcx; out1[6] = TMP
shrd rbx, r8, 58; x513 <- x512||x510 >> 58
mov rcx, 0x1ffffffffffffff ; moving imm to reg
and r13, rcx; x509 <- x503&0x1ffffffffffffff
mov r8, 0x3ffffffffffffff ; moving imm to reg
and r14, r8; x474 <- x468&0x3ffffffffffffff
lea rbx, [ rbx + r12 ]
mov [ r15 + 0x18 ], r14; out1[3] = x474
mov r12, rbx; x516, copying x515 here, cause x515 is needed in a reg for other than x516, namely all: , x516, x517, size: 2
shr r12, 58; x516 <- x515>> 58
mov [ r15 + 0x0 ], rbp; out1[0] = x514
and rdi, r8; x502 <- x496&0x3ffffffffffffff
mov [ r15 + 0x38 ], rdi; out1[7] = x502
lea r12, [ r12 + r10 ]
mov [ r15 + 0x20 ], r9; out1[4] = x481
and rbx, r8; x517 <- x515&0x3ffffffffffffff
and rax, r8; x488 <- x482&0x3ffffffffffffff
mov [ r15 + 0x40 ], r13; out1[8] = x509
mov [ r15 + 0x28 ], rax; out1[5] = x488
mov [ r15 + 0x8 ], rbx; out1[1] = x517
mov [ r15 + 0x10 ], r12; out1[2] = x518
mov rbx, [ rsp + 0x330 ]; restoring from stack
mov rbp, [ rsp + 0x338 ]; restoring from stack
mov r12, [ rsp + 0x340 ]; restoring from stack
mov r13, [ rsp + 0x348 ]; restoring from stack
mov r14, [ rsp + 0x350 ]; restoring from stack
mov r15, [ rsp + 0x358 ]; restoring from stack
add rsp, 0x360 
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; clocked at 3600 MHz
; first cyclecount 175.11, best 143.59375, lastGood 145.5625
; seed 3475301888420410 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2963689 ms / 60000 runs=> 49.394816666666664ms/run
; Time spent for assembling and measureing (initial batch_size=65, initial num_batches=101): 113098 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.03816122406905718
; number reverted permutation/ tried permutation: 17336 / 30023 =57.742%
; number reverted decision/ tried decision: 17416 / 29978 =58.096%