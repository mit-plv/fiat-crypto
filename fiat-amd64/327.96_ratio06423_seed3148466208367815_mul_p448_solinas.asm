SECTION .text
	GLOBAL mul_p448_solinas
mul_p448_solinas:
sub rsp, 0x4b0 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x480 ], rbx; saving to stack
mov [ rsp + 0x488 ], rbp; saving to stack
mov [ rsp + 0x490 ], r12; saving to stack
mov [ rsp + 0x498 ], r13; saving to stack
mov [ rsp + 0x4a0 ], r14; saving to stack
mov [ rsp + 0x4a8 ], r15; saving to stack
mov rax, rdx; preserving value of arg2 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r10, r11, [ rax + 0x20 ]; x68, x67<- arg1[4] * arg2[4]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx rbx, rbp, [ rsi + 0x38 ]; x38, x37<- arg1[7] * arg2[1]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mulx r12, r13, [ rsi + 0x30 ]; x10, x9<- arg1[6] * arg2[6]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mulx r14, r15, [ rsi + 0x8 ]; x80, x79<- arg1[1] * arg2[7]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx rcx, r8, [ rsi + 0x30 ]; x50, x49<- arg1[6] * arg2[2]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r9, rdi, [ rsi + 0x38 ]; x6, x5<- arg1[7] * arg2[5]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x8 ], r14; spilling x80 to mem
mov [ rsp + 0x10 ], r10; spilling x68 to mem
mulx r14, r10, [ rax + 0x38 ]; x12, x11<- arg1[5] * arg2[7]
test al, al
adox rdi, r13
adcx rdi, r10
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mulx r13, r10, [ rsi + 0x18 ]; x74, x73<- arg1[3] * arg2[5]
mov [ rsp + 0x18 ], r13; spilling x74 to mem
setc r13b; spill CF x524 to reg (r13)
clc;
adcx rdi, rbp
seto bpl; spill OF x520 to reg (rbp)
mov [ rsp + 0x20 ], rcx; spilling x50 to mem
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rdi, r8
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r8, rcx, [ rax + 0x20 ]; x146, x145<- arg1[3] * arg2[4]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x28 ], rbx; spilling x38 to mem
mov [ rsp + 0x30 ], r14; spilling x12 to mem
mulx rbx, r14, [ rax + 0x18 ]; x60, x59<- arg1[5] * arg2[3]
mov [ rsp + 0x38 ], rbx; spilling x60 to mem
setc bl; spill CF x528 to reg (rbx)
clc;
adcx rdi, r14
seto r14b; spill OF x532 to reg (r14)
mov byte [ rsp + 0x40 ], bl; spilling byte x528 to mem
mov rbx, -0x2 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rdi, r11
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mulx r11, rbx, [ rsi + 0x10 ]; x78, x77<- arg1[2] * arg2[6]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x48 ], r11; spilling x78 to mem
mov byte [ rsp + 0x50 ], r14b; spilling byte x532 to mem
mulx r11, r14, [ rax + 0x28 ]; x90, x89<- arg1[6] * arg2[5]
mov byte [ rsp + 0x58 ], r13b; spilling byte x524 to mem
seto r13b; spill OF x540 to reg (r13)
mov [ rsp + 0x60 ], r8; spilling x146 to mem
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rdi, r10
seto r10b; spill OF x544 to reg (r10)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rdi, rbx
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mulx rbx, r8, [ rsi + 0x8 ]; x168, x167<- arg1[1] * arg2[6]
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mov byte [ rsp + 0x68 ], r10b; spilling byte x544 to mem
mov byte [ rsp + 0x70 ], r13b; spilling byte x540 to mem
mulx r10, r13, [ rsi + 0x0 ]; x196, x195<- arg1[0] * arg2[0]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x78 ], r10; spilling x196 to mem
mov [ rsp + 0x80 ], rbx; spilling x168 to mem
mulx r10, rbx, [ rax + 0x38 ]; x182, x181<- arg1[0] * arg2[7]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x88 ], r10; spilling x182 to mem
mov [ rsp + 0x90 ], rbx; spilling x181 to mem
mulx r10, rbx, [ rsi + 0x20 ]; x138, x137<- arg1[4] * arg2[3]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x98 ], r8; spilling x167 to mem
mov [ rsp + 0xa0 ], rcx; spilling x145 to mem
mulx r8, rcx, [ rax + 0x30 ]; x98, x97<- arg1[5] * arg2[6]
mov [ rsp + 0xa8 ], r10; spilling x138 to mem
setc r10b; spill CF x536 to reg (r10)
clc;
adcx rdi, r15
seto r15b; spill OF x548 to reg (r15)
mov byte [ rsp + 0xb0 ], r10b; spilling byte x536 to mem
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rdi, r13
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mulx r13, r10, [ rsi + 0x10 ]; x156, x155<- arg1[2] * arg2[5]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0xb8 ], rdi; spilling x555 to mem
mov byte [ rsp + 0xc0 ], r15b; spilling byte x548 to mem
mulx rdi, r15, [ rax + 0x38 ]; x106, x105<- arg1[4] * arg2[7]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0xc8 ], r13; spilling x156 to mem
mov [ rsp + 0xd0 ], r10; spilling x155 to mem
mulx r13, r10, [ rsi + 0x38 ]; x82, x81<- arg1[7] * arg2[4]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0xd8 ], r9; spilling x6 to mem
mov [ rsp + 0xe0 ], r12; spilling x10 to mem
mulx r9, r12, [ rax + 0x10 ]; x132, x131<- arg1[5] * arg2[2]
mov byte [ rsp + 0xe8 ], bpl; spilling byte x520 to mem
seto bpl; spill OF x556 to reg (rbp)
mov [ rsp + 0xf0 ], rbx; spilling x137 to mem
mov rbx, -0x2 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r10, r14
adox r11, r13
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx r14, r13, [ rsi + 0x30 ]; x128, x127<- arg1[6] * arg2[1]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov byte [ rsp + 0xf8 ], bpl; spilling byte x556 to mem
mulx rbx, rbp, [ rax + 0x0 ]; x126, x125<- arg1[7] * arg2[0]
mov [ rsp + 0x100 ], r9; spilling x132 to mem
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r10, rcx
setc cl; spill CF x552 to reg (rcx)
clc;
adcx r10, r15
setc r15b; spill CF x236 to reg (r15)
clc;
adcx r10, rbp
adox r8, r11
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r10, r13
movzx r15, r15b
lea rdi, [ rdi + r8 ]
lea rdi, [ rdi + r15 ]
adcx rbx, rdi
clc;
adcx r10, r12
adox r14, rbx
adcx r14, [ rsp + 0x100 ]
add r10, [ rsp + 0xf0 ]; could be done better, if r0 has been u8 as well
mov r12, [ rsp + 0xe0 ]; load m64 x10 to register64
movzx r11, byte [ rsp + 0xe8 ]; load byte memx520 to register64
lea r12, [ r11 + r12 ]
mov r11, [ rsp + 0xd8 ]
lea r12, [r11+r12]
adcx r14, [ rsp + 0xa8 ]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r11, r13, [ rax + 0x38 ]; x76, x75<- arg1[2] * arg2[7]
add r10, [ rsp + 0xa0 ]; could be done better, if r0 has been u8 as well
adcx r14, [ rsp + 0x60 ]
xor rbp, rbp
adox r10, [ rsp + 0xd0 ]
adox r14, [ rsp + 0xc8 ]
sar byte [ rsp + 0x58 ], 1
adcx r12, [ rsp + 0x30 ]
adox r10, [ rsp + 0x98 ]
adox r14, [ rsp + 0x80 ]
sar byte [ rsp + 0x40 ], 1
adcx r12, [ rsp + 0x28 ]
sar byte [ rsp + 0x50 ], 1
adcx r12, [ rsp + 0x20 ]
adox r10, [ rsp + 0x90 ]
adox r14, [ rsp + 0x88 ]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r9, r15, [ rax + 0x28 ]; x66, x65<- arg1[4] * arg2[5]
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx r8, rdi, [ rsi + 0x8 ]; x180, x179<- arg1[1] * arg2[0]
sar byte [ rsp + 0xb0 ], 1
adcx r12, [ rsp + 0x38 ]
mov rbx, r10; x562, copying x267 here, cause x267 is needed in a reg for other than x562, namely all: , x563, x562, size: 2
shrd rbx, r14, 56; x562 <- x269||x267 >> 56
sar byte [ rsp + 0x70 ], 1
adcx r12, [ rsp + 0x10 ]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r14, rbp, [ rax + 0x8 ]; x194, x193<- arg1[0] * arg2[1]
sar byte [ rsp + 0x68 ], 1
adcx r12, [ rsp + 0x18 ]
sar byte [ rsp + 0xc0 ], 1
adcx r12, [ rsp + 0x48 ]
sar  cl, 1
adcx r12, [ rsp + 0x8 ]
sar byte [ rsp + 0xf8 ], 1
adcx r12, [ rsp + 0x78 ]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x108 ], r14; spilling x194 to mem
mulx rcx, r14, [ rsi + 0x38 ]; x4, x3<- arg1[7] * arg2[6]
mov [ rsp + 0x110 ], r8; spilling x180 to mem
mov r8, rbx; x569, copying x562 here, cause x562 is needed in a reg for other than x569, namely all: , x569--x570, x564--x565, size: 2
adox r8, [ rsp + 0xb8 ]
mov [ rsp + 0x118 ], rbp; spilling x193 to mem
mov rbp, 0x0 ; moving imm to reg
adox r12, rbp
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x120 ], r11; spilling x76 to mem
mulx rbp, r11, [ rsi + 0x28 ]; x58, x57<- arg1[5] * arg2[4]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x128 ], rdi; spilling x179 to mem
mov [ rsp + 0x130 ], r13; spilling x75 to mem
mulx rdi, r13, [ rsi + 0x30 ]; x8, x7<- arg1[6] * arg2[7]
mov [ rsp + 0x138 ], r9; spilling x66 to mem
mov r9, r8; x575, copying x569 here, cause x569 is needed in a reg for other than x575, namely all: , x576, x575, size: 2
shrd r9, r12, 56; x575 <- x571||x569 >> 56
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x140 ], r9; spilling x575 to mem
mulx r12, r9, [ rsi + 0x30 ]; x48, x47<- arg1[6] * arg2[3]
test al, al
adox r14, r13
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x148 ], r15; spilling x65 to mem
mulx r13, r15, [ rax + 0x10 ]; x36, x35<- arg1[7] * arg2[2]
adcx r14, r15
adox rdi, rcx
adcx r13, rdi
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rcx, r15, [ rax + 0x30 ]; x72, x71<- arg1[3] * arg2[6]
test al, al
adox r14, r9
adcx r14, r11
adox r12, r13
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx r11, r9, [ rsi + 0x10 ]; x166, x165<- arg1[2] * arg2[0]
adcx rbp, r12
test al, al
adox r14, [ rsp + 0x148 ]
adcx r14, r15
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rdi, r13, [ rax + 0x10 ]; x192, x191<- arg1[0] * arg2[2]
adox rbp, [ rsp + 0x138 ]
adcx rcx, rbp
test al, al
adox r14, [ rsp + 0x130 ]
adcx r14, [ rsp + 0x128 ]
adox rcx, [ rsp + 0x120 ]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx r15, r12, [ rsi + 0x8 ]; x178, x177<- arg1[1] * arg2[1]
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, [ rsp + 0x118 ]
adcx rcx, [ rsp + 0x110 ]
clc;
adcx r14, [ rsp + 0x140 ]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x150 ], rdi; spilling x192 to mem
mulx rbp, rdi, [ rsi + 0x38 ]; x34, x33<- arg1[7] * arg2[3]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x158 ], r13; spilling x191 to mem
mov [ rsp + 0x160 ], r15; spilling x178 to mem
mulx r13, r15, [ rsi + 0x38 ]; x2, x1<- arg1[7] * arg2[7]
adox rcx, [ rsp + 0x108 ]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x168 ], r12; spilling x177 to mem
mov [ rsp + 0x170 ], r11; spilling x166 to mem
mulx r12, r11, [ rax + 0x28 ]; x56, x55<- arg1[5] * arg2[5]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x178 ], r9; spilling x165 to mem
mov [ rsp + 0x180 ], r12; spilling x56 to mem
mulx r9, r12, [ rsi + 0x30 ]; x46, x45<- arg1[6] * arg2[4]
adc rcx, 0x0
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x188 ], r9; spilling x46 to mem
mov [ rsp + 0x190 ], r11; spilling x55 to mem
mulx r9, r11, [ rax + 0x30 ]; x64, x63<- arg1[4] * arg2[6]
mov [ rsp + 0x198 ], r9; spilling x64 to mem
xor r9, r9
adox r15, rdi
adox rbp, r13
mov rdi, r14; x585, copying x577 here, cause x577 is needed in a reg for other than x585, namely all: , x585, x586, size: 2
shrd rdi, rcx, 56; x585 <- x579||x577 >> 56
add r15, r12; could be done better, if r0 has been u8 as well
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mulx r13, r12, [ rsi + 0x18 ]; x70, x69<- arg1[3] * arg2[7]
mov rcx, -0x3 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r15, [ rsp + 0x190 ]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r9, rcx, [ rax + 0x10 ]; x176, x175<- arg1[1] * arg2[2]
adcx rbp, [ rsp + 0x188 ]
adox rbp, [ rsp + 0x180 ]
mov [ rsp + 0x1a0 ], r9; spilling x176 to mem
xor r9, r9
adox r15, r11
adox rbp, [ rsp + 0x198 ]
adcx r15, r12
adcx r13, rbp
xor r11, r11
adox r15, [ rsp + 0x178 ]
adox r13, [ rsp + 0x170 ]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mulx r9, r12, [ rsi + 0x0 ]; x190, x189<- arg1[0] * arg2[3]
adcx r15, [ rsp + 0x168 ]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mulx rbp, r11, [ rsi + 0x28 ]; x54, x53<- arg1[5] * arg2[6]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x1a8 ], r9; spilling x190 to mem
mov [ rsp + 0x1b0 ], r12; spilling x189 to mem
mulx r9, r12, [ rax + 0x28 ]; x44, x43<- arg1[6] * arg2[5]
adcx r13, [ rsp + 0x160 ]
add r15, [ rsp + 0x158 ]; could be done better, if r0 has been u8 as well
adcx r13, [ rsp + 0x150 ]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x1b8 ], rcx; spilling x175 to mem
mov [ rsp + 0x1c0 ], rbp; spilling x54 to mem
mulx rcx, rbp, [ rsi + 0x10 ]; x164, x163<- arg1[2] * arg2[1]
test al, al
adox r15, rdi
mov rdi, 0x0 ; moving imm to reg
adox r13, rdi
mov rdi, r15; x593, copying x587 here, cause x587 is needed in a reg for other than x593, namely all: , x593, x594, size: 2
shrd rdi, r13, 56; x593 <- x589||x587 >> 56
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x1c8 ], rcx; spilling x164 to mem
mulx r13, rcx, [ rax + 0x20 ]; x32, x31<- arg1[7] * arg2[4]
mov [ rsp + 0x1d0 ], rdi; spilling x593 to mem
xor rdi, rdi
adox rcx, r12
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mulx r12, rdi, [ rsi + 0x20 ]; x62, x61<- arg1[4] * arg2[7]
adox r9, r13
adcx rcx, r11
adcx r9, [ rsp + 0x1c0 ]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r11, r13, [ rax + 0x0 ]; x154, x153<- arg1[3] * arg2[0]
test al, al
adox rcx, rdi
adox r12, r9
adcx rcx, r13
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rcx, rbp
setc bpl; spill CF x210 to reg (rbp)
clc;
adcx rcx, [ rsp + 0x1b8 ]
setc r9b; spill CF x218 to reg (r9)
clc;
adcx rcx, [ rsp + 0x1b0 ]
mov r13, 0xffffffffffffff ; moving imm to reg
setc dil; spill CF x222 to reg (rdi)
mov byte [ rsp + 0x1d8 ], r9b; spilling byte x218 to mem
seto r9b; spill OF x214 to reg (r9)
mov [ rsp + 0x1e0 ], r12; spilling x207 to mem
mov r12, rcx; x226, copying x221 here, cause x221 is needed in a reg for other than x226, namely all: , x226, x225, size: 2
and r12, r13; x226 <- x221&0xffffffffffffff
add r12, [ rsp + 0x1d0 ]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x1e8 ], r12; spilling x595 to mem
mulx r13, r12, [ rax + 0x10 ]; x162, x161<- arg1[2] * arg2[2]
sar  bpl, 1
adcx r11, [ rsp + 0x1e0 ]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x1f0 ], r13; spilling x162 to mem
mulx rbp, r13, [ rsi + 0x30 ]; x42, x41<- arg1[6] * arg2[6]
sar  r9b, 1
adcx r11, [ rsp + 0x1c8 ]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x1f8 ], r12; spilling x161 to mem
mulx r9, r12, [ rsi + 0x18 ]; x152, x151<- arg1[3] * arg2[1]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x200 ], r9; spilling x152 to mem
mov [ rsp + 0x208 ], r12; spilling x151 to mem
mulx r9, r12, [ rsi + 0x8 ]; x174, x173<- arg1[1] * arg2[3]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x210 ], r9; spilling x174 to mem
mov [ rsp + 0x218 ], r12; spilling x173 to mem
mulx r9, r12, [ rsi + 0x0 ]; x188, x187<- arg1[0] * arg2[4]
sar byte [ rsp + 0x1d8 ], 1
adcx r11, [ rsp + 0x1a0 ]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x220 ], r9; spilling x188 to mem
mov [ rsp + 0x228 ], r12; spilling x187 to mem
mulx r9, r12, [ rax + 0x0 ]; x144, x143<- arg1[4] * arg2[0]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x230 ], r9; spilling x144 to mem
mov [ rsp + 0x238 ], r12; spilling x143 to mem
mulx r9, r12, [ rsi + 0x8 ]; x124, x123<- arg1[1] * arg2[7]
sar  dil, 1
adcx r11, [ rsp + 0x1a8 ]
mov rdi, [ rsp + 0x1e8 ]; x598, copying x595 here, cause x595 is needed in a reg for other than x598, namely all: , x599, x598, size: 2
shr rdi, 56; x598 <- x595>> 56
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x240 ], rdi; spilling x598 to mem
mov [ rsp + 0x248 ], r9; spilling x124 to mem
mulx rdi, r9, [ rax + 0x18 ]; x104, x103<- arg1[5] * arg2[3]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x250 ], rdi; spilling x104 to mem
mov [ rsp + 0x258 ], r12; spilling x123 to mem
mulx rdi, r12, [ rax + 0x8 ]; x88, x87<- arg1[7] * arg2[1]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x260 ], rdi; spilling x88 to mem
mov [ rsp + 0x268 ], r9; spilling x103 to mem
mulx rdi, r9, [ rsi + 0x38 ]; x30, x29<- arg1[7] * arg2[5]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x270 ], rbp; spilling x42 to mem
mov [ rsp + 0x278 ], rdi; spilling x30 to mem
mulx rbp, rdi, [ rsi + 0x28 ]; x24, x23<- arg1[5] * arg2[7]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x280 ], rbp; spilling x24 to mem
mov [ rsp + 0x288 ], r12; spilling x87 to mem
mulx rbp, r12, [ rax + 0x30 ]; x22, x21<- arg1[6] * arg2[6]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x290 ], rbp; spilling x22 to mem
mov [ rsp + 0x298 ], r13; spilling x41 to mem
mulx rbp, r13, [ rsi + 0x38 ]; x18, x17<- arg1[7] * arg2[5]
shrd rcx, r11, 56; x225 <- x223||x221 >> 56
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x2a0 ], rcx; spilling x225 to mem
mulx r11, rcx, [ rsi + 0x10 ]; x122, x121<- arg1[2] * arg2[6]
mov [ rsp + 0x2a8 ], r11; spilling x122 to mem
xor r11, r11
adox r13, r12
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx r12, r11, [ rsi + 0x30 ]; x96, x95<- arg1[6] * arg2[2]
adcx r13, rdi
setc dil; spill CF x388 to reg (rdi)
clc;
adcx r13, r9
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x2b0 ], r12; spilling x96 to mem
mulx r9, r12, [ rsi + 0x28 ]; x52, x51<- arg1[5] * arg2[7]
mov [ rsp + 0x2b8 ], rcx; spilling x121 to mem
setc cl; spill CF x392 to reg (rcx)
clc;
adcx r13, [ rsp + 0x298 ]
adox rbp, [ rsp + 0x290 ]
mov [ rsp + 0x2c0 ], r9; spilling x52 to mem
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, r12
setc r12b; spill CF x396 to reg (r12)
clc;
adcx r13, [ rsp + 0x288 ]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov byte [ rsp + 0x2c8 ], r12b; spilling byte x396 to mem
mulx r9, r12, [ rax + 0x20 ]; x112, x111<- arg1[4] * arg2[4]
mov [ rsp + 0x2d0 ], r9; spilling x112 to mem
setc r9b; spill CF x404 to reg (r9)
clc;
adcx r13, r11
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov byte [ rsp + 0x2d8 ], r9b; spilling byte x404 to mem
mulx r11, r9, [ rax + 0x28 ]; x118, x117<- arg1[3] * arg2[5]
movzx rdi, dil
lea rbp, [ rdi + rbp ]
mov rdi, [ rsp + 0x280 ]
lea rbp, [rdi+rbp]
movzx rcx, cl
lea rbp, [ rcx + rbp ]
mov rcx, [ rsp + 0x278 ]
lea rbp, [rcx+rbp]
movzx rdi, byte [ rsp + 0x2c8 ]; load byte memx396 to register64
lea rbp, [ rdi + rbp ]
mov rdi, [ rsp + 0x270 ]
lea rbp, [rdi+rbp]
setc cl; spill CF x408 to reg (rcx)
clc;
adcx r13, [ rsp + 0x268 ]
setc dil; spill CF x412 to reg (rdi)
clc;
adcx r13, r12
adox rbp, [ rsp + 0x2c0 ]
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, r9
movzx r9, byte [ rsp + 0x2d8 ]; load byte memx404 to register64
lea rbp, [ r9 + rbp ]
mov r9, [ rsp + 0x260 ]
lea rbp, [r9+rbp]
seto r9b; spill OF x420 to reg (r9)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r13, [ rsp + 0x2b8 ]
mov [ rsp + 0x2e0 ], r11; spilling x118 to mem
setc r11b; spill CF x416 to reg (r11)
clc;
adcx r13, [ rsp + 0x258 ]
mov byte [ rsp + 0x2e8 ], r9b; spilling byte x420 to mem
setc r9b; spill CF x428 to reg (r9)
clc;
adcx r13, [ rsp + 0x238 ]
movzx rcx, cl
lea rbp, [ rcx + rbp ]
mov rcx, [ rsp + 0x2b0 ]
lea rbp, [rcx+rbp]
movzx rdi, dil
lea rbp, [ rdi + rbp ]
mov rdi, [ rsp + 0x250 ]
lea rbp, [rdi+rbp]
seto cl; spill OF x424 to reg (rcx)
mov rdi, -0x3 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r13, [ rsp + 0x208 ]
setc dil; spill CF x432 to reg (rdi)
clc;
adcx r13, [ rsp + 0x1f8 ]
mov byte [ rsp + 0x2f0 ], dil; spilling byte x432 to mem
seto dil; spill OF x436 to reg (rdi)
mov byte [ rsp + 0x2f8 ], r9b; spilling byte x428 to mem
mov r9, -0x3 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r13, [ rsp + 0x218 ]
movzx r11, r11b
lea rbp, [ r11 + rbp ]
mov r11, [ rsp + 0x2d0 ]
lea rbp, [r11+rbp]
movzx r11, byte [ rsp + 0x2e8 ]; load byte memx420 to register64
lea rbp, [ r11 + rbp ]
mov r11, [ rsp + 0x2e0 ]
lea rbp, [r11+rbp]
seto r11b; spill OF x444 to reg (r11)
mov r9, -0x3 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r13, [ rsp + 0x228 ]
seto r9b; spill OF x448 to reg (r9)
mov byte [ rsp + 0x300 ], r11b; spilling byte x444 to mem
mov r11, -0x3 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r13, [ rsp + 0x2a0 ]
movzx rcx, cl
lea rbp, [ rcx + rbp ]
mov rcx, [ rsp + 0x2a8 ]
lea rbp, [rcx+rbp]
movzx rcx, byte [ rsp + 0x2f8 ]; load byte memx428 to register64
lea rbp, [ rcx + rbp ]
mov rcx, [ rsp + 0x248 ]
lea rbp, [rcx+rbp]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx rcx, r12, [ rsi + 0x20 ]; x142, x141<- arg1[4] * arg2[1]
movzx r11, byte [ rsp + 0x2f0 ]; load byte memx432 to register64
lea rbp, [ r11 + rbp ]
mov r11, [ rsp + 0x230 ]
lea rbp, [r11+rbp]
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x308 ], rcx; spilling x142 to mem
mulx r11, rcx, [ rsi + 0x28 ]; x136, x135<- arg1[5] * arg2[0]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x310 ], r11; spilling x136 to mem
mov [ rsp + 0x318 ], r12; spilling x141 to mem
mulx r11, r12, [ rax + 0x20 ]; x172, x171<- arg1[1] * arg2[4]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x320 ], r11; spilling x172 to mem
mov [ rsp + 0x328 ], r12; spilling x171 to mem
mulx r11, r12, [ rax + 0x30 ]; x28, x27<- arg1[7] * arg2[6]
movzx rdi, dil
lea rbp, [ rdi + rbp ]
mov rdi, [ rsp + 0x200 ]
lea rbp, [rdi+rbp]
seto dil; spill OF x560 to reg (rdi)
mov [ rsp + 0x330 ], rcx; spilling x135 to mem
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, r13
adcx rbp, [ rsp + 0x1f0 ]
movzx r13, byte [ rsp + 0x300 ]; load byte memx444 to register64
lea rbp, [ r13 + rbp ]
mov r13, [ rsp + 0x210 ]
lea rbp, [r13+rbp]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r13, rcx, [ rax + 0x28 ]; x186, x185<- arg1[0] * arg2[5]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x338 ], r13; spilling x186 to mem
mov [ rsp + 0x340 ], rcx; spilling x185 to mem
mulx r13, rcx, [ rsi + 0x10 ]; x120, x119<- arg1[2] * arg2[7]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x348 ], r13; spilling x120 to mem
mov [ rsp + 0x350 ], r11; spilling x28 to mem
mulx r13, r11, [ rsi + 0x10 ]; x160, x159<- arg1[2] * arg2[3]
movzx r9, r9b
lea rbp, [ r9 + rbp ]
mov r9, [ rsp + 0x220 ]
lea rbp, [r9+rbp]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x358 ], r13; spilling x160 to mem
mulx r9, r13, [ rax + 0x28 ]; x110, x109<- arg1[4] * arg2[5]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x360 ], r10; spilling x267 to mem
mov [ rsp + 0x368 ], r9; spilling x110 to mem
mulx r10, r9, [ rax + 0x38 ]; x20, x19<- arg1[6] * arg2[7]
mov [ rsp + 0x370 ], r11; spilling x159 to mem
movzx r11, dil; x561, copying x560 here, cause x560 is needed in a reg for other than x561, namely all: , x561, size: 1
lea r11, [ r11 + rbp ]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx rdi, rbp, [ rax + 0x30 ]; x16, x15<- arg1[7] * arg2[6]
mov [ rsp + 0x378 ], rcx; spilling x119 to mem
mov rcx, 0x0 ; moving imm to reg
adox r11, rcx
mov rcx, rbx; x567, copying x564 here, cause x564 is needed in a reg for other than x567, namely all: , x568, x567, size: 2
shrd rcx, r11, 56; x567 <- x566||x564 >> 56
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x380 ], rcx; spilling x567 to mem
mulx r11, rcx, [ rax + 0x10 ]; x86, x85<- arg1[7] * arg2[2]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x388 ], r11; spilling x86 to mem
mov [ rsp + 0x390 ], rdi; spilling x16 to mem
mulx r11, rdi, [ rsi + 0x30 ]; x40, x39<- arg1[6] * arg2[7]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x398 ], r11; spilling x40 to mem
mov [ rsp + 0x3a0 ], r10; spilling x20 to mem
mulx r11, r10, [ rsi + 0x30 ]; x94, x93<- arg1[6] * arg2[3]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x3a8 ], r11; spilling x94 to mem
mov [ rsp + 0x3b0 ], r13; spilling x109 to mem
mulx r11, r13, [ rsi + 0x18 ]; x116, x115<- arg1[3] * arg2[6]
test al, al
adox rbp, r9
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x3b8 ], r11; spilling x116 to mem
mulx r9, r11, [ rax + 0x20 ]; x102, x101<- arg1[5] * arg2[4]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x3c0 ], r9; spilling x102 to mem
mov [ rsp + 0x3c8 ], r13; spilling x115 to mem
mulx r9, r13, [ rax + 0x10 ]; x150, x149<- arg1[3] * arg2[2]
adcx rbp, r12
seto r12b; spill OF x324 to reg (r12)
mov [ rsp + 0x3d0 ], r9; spilling x150 to mem
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, rdi
setc dil; spill CF x328 to reg (rdi)
clc;
adcx rbp, rcx
seto cl; spill OF x332 to reg (rcx)
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rbp, r10
setc r10b; spill CF x336 to reg (r10)
clc;
adcx rbp, r11
setc r11b; spill CF x344 to reg (r11)
clc;
adcx rbp, [ rsp + 0x3b0 ]
mov byte [ rsp + 0x3d8 ], r11b; spilling byte x344 to mem
setc r11b; spill CF x348 to reg (r11)
clc;
adcx rbp, [ rsp + 0x3c8 ]
mov r9, [ rsp + 0x390 ]; load m64 x16 to register64
movzx r12, r12b
lea r9, [ r12 + r9 ]
mov r12, [ rsp + 0x3a0 ]
lea r9, [r12+r9]
seto r12b; spill OF x340 to reg (r12)
mov byte [ rsp + 0x3e0 ], r11b; spilling byte x348 to mem
mov r11, -0x2 ; moving imm to reg
inc r11; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, [ rsp + 0x378 ]
movzx rdi, dil
lea r9, [ rdi + r9 ]
mov rdi, [ rsp + 0x350 ]
lea r9, [rdi+r9]
movzx rcx, cl
lea r9, [ rcx + r9 ]
mov rcx, [ rsp + 0x398 ]
lea r9, [rcx+r9]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mulx rdi, rcx, [ rsi + 0x8 ]; x170, x169<- arg1[1] * arg2[5]
movzx r10, r10b
lea r9, [ r10 + r9 ]
mov r10, [ rsp + 0x388 ]
lea r9, [r10+r9]
setc r10b; spill CF x352 to reg (r10)
clc;
adcx rbp, [ rsp + 0x330 ]
seto r11b; spill OF x356 to reg (r11)
mov [ rsp + 0x3e8 ], rdi; spilling x170 to mem
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, [ rsp + 0x318 ]
movzx r12, r12b
lea r9, [ r12 + r9 ]
mov r12, [ rsp + 0x3a8 ]
lea r9, [r12+r9]
seto r12b; spill OF x364 to reg (r12)
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rbp, r13
setc r13b; spill CF x360 to reg (r13)
clc;
adcx rbp, [ rsp + 0x370 ]
mov [ rsp + 0x3f0 ], rcx; spilling x169 to mem
setc cl; spill CF x372 to reg (rcx)
clc;
adcx rbp, [ rsp + 0x328 ]
movzx rdi, byte [ rsp + 0x3d8 ]; load byte memx344 to register64
lea r9, [ rdi + r9 ]
mov rdi, [ rsp + 0x3c0 ]
lea r9, [rdi+r9]
movzx rdi, byte [ rsp + 0x3e0 ]; load byte memx348 to register64
lea r9, [ rdi + r9 ]
mov rdi, [ rsp + 0x368 ]
lea r9, [rdi+r9]
movzx r10, r10b
lea r9, [ r10 + r9 ]
mov r10, [ rsp + 0x3b8 ]
lea r9, [r10+r9]
seto dil; spill OF x368 to reg (rdi)
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, [ rsp + 0x340 ]
movzx r11, r11b
lea r9, [ r11 + r9 ]
mov r11, [ rsp + 0x348 ]
lea r9, [r11+r9]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx r11, r10, [ rsi + 0x10 ]; x158, x157<- arg1[2] * arg2[4]
movzx r13, r13b
lea r9, [ r13 + r9 ]
mov r13, [ rsp + 0x310 ]
lea r9, [r13+r9]
movzx r12, r12b
lea r9, [ r12 + r9 ]
mov r12, [ rsp + 0x308 ]
lea r9, [r12+r9]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mulx r13, r12, [ rsi + 0x18 ]; x114, x113<- arg1[3] * arg2[7]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x3f8 ], r8; spilling x569 to mem
mov [ rsp + 0x400 ], r11; spilling x158 to mem
mulx r8, r11, [ rax + 0x38 ]; x14, x13<- arg1[7] * arg2[7]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x408 ], r10; spilling x157 to mem
mov [ rsp + 0x410 ], r13; spilling x114 to mem
mulx r10, r13, [ rsi + 0x38 ]; x26, x25<- arg1[7] * arg2[7]
movzx rdi, dil
lea r9, [ rdi + r9 ]
mov rdi, [ rsp + 0x3d0 ]
lea r9, [rdi+r9]
seto dil; spill OF x380 to reg (rdi)
mov [ rsp + 0x418 ], r12; spilling x113 to mem
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, [ rsp + 0x380 ]
movzx rcx, cl
lea r9, [ rcx + r9 ]
mov rcx, [ rsp + 0x358 ]
lea r9, [rcx+r9]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mulx rcx, r12, [ rsi + 0x0 ]; x184, x183<- arg1[0] * arg2[6]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x420 ], rcx; spilling x184 to mem
mov [ rsp + 0x428 ], r12; spilling x183 to mem
mulx rcx, r12, [ rsi + 0x28 ]; x134, x133<- arg1[5] * arg2[1]
adcx r9, [ rsp + 0x320 ]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x430 ], rcx; spilling x134 to mem
mov [ rsp + 0x438 ], r12; spilling x133 to mem
mulx rcx, r12, [ rsi + 0x38 ]; x84, x83<- arg1[7] * arg2[3]
clc;
adcx r11, r13
movzx rdi, dil
lea r9, [ rdi + r9 ]
mov rdi, [ rsp + 0x338 ]
lea r9, [rdi+r9]
seto dil; spill OF x573 to reg (rdi)
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, r12
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx r12, r13, [ rsi + 0x30 ]; x92, x91<- arg1[6] * arg2[4]
mov [ rsp + 0x440 ], r12; spilling x92 to mem
movzx r12, dil; x574, copying x573 here, cause x573 is needed in a reg for other than x574, namely all: , x574, size: 1
lea r12, [ r12 + r9 ]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rdi, r9, [ rax + 0x18 ]; x148, x147<- arg1[3] * arg2[3]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x448 ], rdi; spilling x148 to mem
mov [ rsp + 0x450 ], r9; spilling x147 to mem
mulx rdi, r9, [ rax + 0x28 ]; x100, x99<- arg1[5] * arg2[5]
mov [ rsp + 0x458 ], rdi; spilling x100 to mem
setc dil; spill CF x272 to reg (rdi)
clc;
adcx r11, r13
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x460 ], rcx; spilling x84 to mem
mulx r13, rcx, [ rax + 0x0 ]; x130, x129<- arg1[6] * arg2[0]
mov [ rsp + 0x468 ], r13; spilling x130 to mem
setc r13b; spill CF x280 to reg (r13)
clc;
adcx r11, r9
setc r9b; spill CF x284 to reg (r9)
mov [ rsp + 0x470 ], rcx; spilling x129 to mem
seto cl; spill OF x276 to reg (rcx)
mov byte [ rsp + 0x478 ], r13b; spilling byte x280 to mem
mov r13, rbp; x580, copying x572 here, cause x572 is needed in a reg for other than x580, namely all: , x580, x581, size: 2
shrd r13, r12, 56; x580 <- x574||x572 >> 56
sar  dil, 1
adcx r10, r8
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mulx r8, rdi, [ rsi + 0x20 ]; x108, x107<- arg1[4] * arg2[6]
adox r11, rdi
clc;
adcx r11, [ rsp + 0x418 ]
movzx rcx, cl
lea r10, [ rcx + r10 ]
mov rcx, [ rsp + 0x460 ]
lea r10, [rcx+r10]
movzx rcx, byte [ rsp + 0x478 ]; load byte memx280 to register64
lea r10, [ rcx + r10 ]
mov rcx, [ rsp + 0x440 ]
lea r10, [rcx+r10]
mov r12, 0xffffffffffffff ; moving imm to reg
setc cl; spill CF x292 to reg (rcx)
seto dil; spill OF x288 to reg (rdi)
and rbx, r12; x568 <- x564&0xffffffffffffff
sar  r9b, 1
adcx r10, [ rsp + 0x458 ]
sar  dil, 1
adcx r8, r10
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r9, rdi, [ rax + 0x10 ]; x140, x139<- arg1[4] * arg2[2]
sar  cl, 1
adcx r8, [ rsp + 0x410 ]
adox r11, [ rsp + 0x470 ]
clc;
adcx r11, [ rsp + 0x438 ]
adox r8, [ rsp + 0x468 ]
adcx r8, [ rsp + 0x430 ]
xor rcx, rcx
adox r11, rdi
adcx r11, [ rsp + 0x450 ]
adox r9, r8
adcx r9, [ rsp + 0x448 ]
add r11, [ rsp + 0x408 ]; could be done better, if r0 has been u8 as well
mov r10, -0x3 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r11, [ rsp + 0x3f0 ]
seto dil; spill OF x316 to reg (rdi)
mov r8, -0x3 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug 7; load -3, increase it, discard the information #workaround). #last resort
adox r11, [ rsp + 0x428 ]
seto r8b; spill OF x320 to reg (r8)
mov r10, -0x3 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r11, r13
setc r13b; spill CF x312 to reg (r13)
seto cl; spill OF x583 to reg (rcx)
mov r10, r11; x591, copying x582 here, cause x582 is needed in a reg for other than x591, namely all: , x590, x591, size: 2
and r10, r12; x591 <- x582&0xffffffffffffff
sar  r13b, 1
adcx r9, [ rsp + 0x400 ]
sar  dil, 1
adcx r9, [ rsp + 0x3e8 ]
mov r13, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r13 + 0x30 ], r10; out1[6] = x591
mov rdi, [ rsp + 0x360 ]; x563, copying x267 here, cause x267 is needed in a reg for other than x563, namely all: , x563, size: 1
and rdi, r12; x563 <- x267&0xffffffffffffff
sar  r8b, 1
adcx r9, [ rsp + 0x420 ]
and r15, r12; x594 <- x587&0xffffffffffffff
movzx r8, cl; x584, copying x583 here, cause x583 is needed in a reg for other than x584, namely all: , x584, size: 1
lea r8, [ r8 + r9 ]
and r14, r12; x586 <- x577&0xffffffffffffff
shrd r11, r8, 56; x590 <- x584||x582 >> 56
mov rcx, [ rsp + 0x3f8 ]; x576, copying x569 here, cause x569 is needed in a reg for other than x576, namely all: , x576, size: 1
and rcx, r12; x576 <- x569&0xffffffffffffff
lea r11, [ r11 + rdi ]
mov [ r13 + 0x10 ], r15; out1[2] = x594
mov r10, r11; x596, copying x592 here, cause x592 is needed in a reg for other than x596, namely all: , x597, x596, size: 2
shr r10, 56; x596 <- x592>> 56
lea rbx, [ rbx + r10 ]
and rbp, r12; x581 <- x572&0xffffffffffffff
lea rcx, [ rcx + r10 ]
and r11, r12; x597 <- x592&0xffffffffffffff
mov rdi, rcx; x607, copying x601 here, cause x601 is needed in a reg for other than x607, namely all: , x607, x606, size: 2
and rdi, r12; x607 <- x601&0xffffffffffffff
mov [ r13 + 0x38 ], r11; out1[7] = x597
mov r9, [ rsp + 0x1e8 ]; x599, copying x595 here, cause x595 is needed in a reg for other than x599, namely all: , x599, size: 1
and r9, r12; x599 <- x595&0xffffffffffffff
add rbx, [ rsp + 0x240 ]
mov r8, rbx; x603, copying x602 here, cause x602 is needed in a reg for other than x603, namely all: , x604, x603, size: 2
shr r8, 56; x603 <- x602>> 56
mov [ r13 + 0x0 ], rdi; out1[0] = x607
and rbx, r12; x604 <- x602&0xffffffffffffff
shr rcx, 56; x606 <- x601>> 56
mov [ r13 + 0x20 ], rbx; out1[4] = x604
lea rcx, [ rcx + r14 ]
mov [ r13 + 0x8 ], rcx; out1[1] = x608
lea r8, [ r8 + rbp ]
mov [ r13 + 0x18 ], r9; out1[3] = x599
mov [ r13 + 0x28 ], r8; out1[5] = x605
mov rbx, [ rsp + 0x480 ]; restoring from stack
mov rbp, [ rsp + 0x488 ]; restoring from stack
mov r12, [ rsp + 0x490 ]; restoring from stack
mov r13, [ rsp + 0x498 ]; restoring from stack
mov r14, [ rsp + 0x4a0 ]; restoring from stack
mov r15, [ rsp + 0x4a8 ]; restoring from stack
add rsp, 0x4b0 
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; clocked at 2200 MHz
; first cyclecount 437, best 318.04347826086956, lastGood 327.95652173913044
; seed 3148466208367815 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 6931789 ms / 60000 runs=> 115.52981666666666ms/run
; Time spent for assembling and measureing (initial batch_size=45, initial num_batches=101): 360592 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.052020048504073046
; number reverted permutation/ tried permutation: 19574 / 30086 =65.060%
; number reverted decision/ tried decision: 16246 / 29915 =54.307%