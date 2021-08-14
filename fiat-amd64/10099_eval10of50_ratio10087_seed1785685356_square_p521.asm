SECTION .text
	GLOBAL square_p521
square_p521:
sub rsp, 0x180
mov rax, [ rsi + 0x40 ]; load m64 x1 to register64
imul r10, rax, 0x2; x10000 <- x1 * 0x2
imul rax, rax, 0x2; x2 <- x1 * 0x2
imul rax, rax, 0x2; x10001 <- x2 * 0x2
mov r11, [ rsi + 0x38 ]; load m64 x4 to register64
imul rdx, r11, 0x2; x10002 <- x4 * 0x2
imul r11, r11, 0x2; x5 <- x4 * 0x2
imul r11, r11, 0x2; x10003 <- x5 * 0x2
mov rcx, [ rsi + 0x30 ]; load m64 x7 to register64
imul r8, rcx, 0x2; x10004 <- x7 * 0x2
imul rcx, rcx, 0x2; x8 <- x7 * 0x2
imul rcx, rcx, 0x2; x10005 <- x8 * 0x2
mov r9, [ rsi + 0x28 ]; load m64 x10 to register64
mov [ rsp + 0x0 ], r15; spilling callerSaver15 to mem
imul r15, r9, 0x2; x10006 <- x10 * 0x2
imul r9, r9, 0x2; x11 <- x10 * 0x2
imul r9, r9, 0x2; x10007 <- x11 * 0x2
mov [ rsp + 0x8 ], r14; spilling callerSaver14 to mem
imul r14, [ rsi + 0x40 ], 0x2; x3 <- arg1[8] * 0x2
mov [ rsp + 0x10 ], r13; spilling callerSaver13 to mem
imul r13, [ rsi + 0x38 ], 0x2; x6 <- arg1[7] * 0x2
mov [ rsp + 0x18 ], r12; spilling callerSaver12 to mem
imul r12, [ rsi + 0x30 ], 0x2; x9 <- arg1[6] * 0x2
mov [ rsp + 0x20 ], rbp; spilling callerSaverbp to mem
imul rbp, [ rsi + 0x28 ], 0x2; x12 <- arg1[5] * 0x2
mov [ rsp + 0x28 ], rbx; spilling callerSaverbx to mem
imul rbx, [ rsi + 0x20 ], 0x2; x13 <- arg1[4] * 0x2
mov [ rsp + 0x30 ], rdi; spilling out1 to mem
imul rdi, [ rsi + 0x18 ], 0x2; x14 <- arg1[3] * 0x2
mov [ rsp + 0x38 ], r14; spilling x3 to mem
imul r14, [ rsi + 0x10 ], 0x2; x15 <- arg1[2] * 0x2
mov [ rsp + 0x40 ], r10; spilling x10000 to mem
imul r10, [ rsi + 0x8 ], 0x2; x16 <- arg1[1] * 0x2
mov [ rsp + 0x48 ], r13; spilling x6 to mem
mov r13, rdx; preserving value of x10002 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x50 ], r12; spilling x9 to mem
mov [ rsp + 0x58 ], rbp; spilling x12 to mem
mulx r12, rbp, [ rsi + 0x0 ]; x106, x105<- arg1[0] * arg1[0]
mov rdx, rax; x10001 to rdx
mov [ rsp + 0x60 ], r13; spilling x10002 to mem
mulx rax, r13, [ rsi + 0x8 ]; x74, x73<- arg1[1] * x10001
xchg rdx, r11; x10003, swapping with x10001, which is currently in rdx
mov [ rsp + 0x68 ], rbx; spilling x13 to mem
mov [ rsp + 0x70 ], r8; spilling x10004 to mem
mulx rbx, r8, [ rsi + 0x10 ]; x62, x61<- arg1[2] * x10003
xchg rdx, rcx; x10005, swapping with x10003, which is currently in rdx
mov [ rsp + 0x78 ], rdi; spilling x14 to mem
mov [ rsp + 0x80 ], r14; spilling x15 to mem
mulx rdi, r14, [ rsi + 0x18 ]; x52, x51<- arg1[3] * x10005
mov [ rsp + 0x88 ], r15; spilling x10006 to mem
mov r15, rdx; preserving value of x10005 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x90 ], r10; spilling x16 to mem
mulx r9, r10, r9; x44, x43<- arg1[4] * x10007
add r10, r14; could be done better, if r0 has been u8 as well
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r10, r8
setc r8b; spill CF x108 to reg (r8)
clc;
adcx r10, r13
seto r13b; spill OF x112 to reg (r13)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r10, rbp
movzx r8, r8b
lea rdi, [ rdi + r9 ]
lea rdi, [ rdi + r8 ]
movzx r13, r13b
lea rbx, [ rbx + rdi ]
lea rbx, [ rbx + r13 ]
adcx rax, rbx
adox r12, rax
mov rbp, r10; x123, copying x119 here, cause x119 is needed in a reg for other than x123, namely all: , x123, x125, size: 2
shrd rbp, r12, 58; x123 <- x121||x119 >> 58
shr r12, 58; x124 <- x121>> 58
mov r14, 0x3ffffffffffffff ; moving imm to reg
and r10, r14; x125 <- x119&0x3ffffffffffffff
mov r9, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsp + 0x90 ]; saving x16 in rdx.
mulx rdx, r8, [ rsi + 0x0 ]; x104, x103<- arg1[0] * x16
mov r13, rdx; preserving value of x104 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx rdi, rbx, r11; x60, x59<- arg1[2] * x10001
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rax, r9, rcx; x50, x49<- arg1[3] * x10003
mov rdx, r15; x10005 to rdx
mov [ rsp + 0x98 ], r10; spilling x125 to mem
mulx r14, r10, [ rsi + 0x20 ]; x42, x41<- arg1[4] * x10005
mov [ rsp + 0xa0 ], r12; spilling x124 to mem
mov r12, rdx; preserving value of x10005 into a new reg
mov rdx, [ rsp + 0x88 ]; saving x10006 in rdx.
mov [ rsp + 0xa8 ], r13; spilling x104 to mem
mulx rdx, r13, [ rsi + 0x28 ]; x36, x35<- arg1[5] * x10006
adox r13, r10
adcx r13, r9
setc r9b; spill CF x243 to reg (r9)
clc;
adcx r13, rbx
setc bl; spill CF x247 to reg (rbx)
clc;
adcx r13, r8
seto r8b; spill OF x239 to reg (r8)
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, rbp
movzx r8, r8b
lea r14, [ r14 + rdx ]
lea r14, [ r14 + r8 ]
movzx r9, r9b
lea rax, [ rax + r14 ]
lea rax, [ rax + r9 ]
movzx rbx, bl
lea rdi, [ rdi + rax ]
lea rdi, [ rdi + rbx ]
adcx rdi, [ rsp + 0xa8 ]
adox rdi, [ rsp + 0xa0 ]
mov rbp, r13; x258, copying x254 here, cause x254 is needed in a reg for other than x258, namely all: , x258, x260, size: 2
shrd rbp, rdi, 58; x258 <- x256||x254 >> 58
shr rdi, 58; x259 <- x256>> 58
mov rdx, 0x3ffffffffffffff ; moving imm to reg
and r13, rdx; x260 <- x254&0x3ffffffffffffff
mov r8, rdx; preserving value of 0x3ffffffffffffff into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r9, rbx, [ rsp + 0x80 ]; x102, x101<- arg1[0] * x15
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r14, rax, [ rsi + 0x8 ]; x88, x87<- arg1[1] * arg1[1]
mov rdx, r11; x10001 to rdx
mulx r11, r10, [ rsi + 0x18 ]; x48, x47<- arg1[3] * x10001
mov r8, rdx; preserving value of x10001 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0xb0 ], r13; spilling x260 to mem
mov [ rsp + 0xb8 ], rdi; spilling x259 to mem
mulx r13, rdi, rcx; x40, x39<- arg1[4] * x10003
mov rdx, r12; x10005 to rdx
mov [ rsp + 0xc0 ], r9; spilling x102 to mem
mulx rdx, r9, [ rsi + 0x28 ]; x34, x33<- arg1[5] * x10005
adox r9, rdi
adcx r9, r10
seto r10b; spill OF x223 to reg (r10)
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r9, rax
setc al; spill CF x227 to reg (rax)
clc;
adcx r9, rbx
setc bl; spill CF x235 to reg (rbx)
clc;
adcx r9, rbp
movzx r10, r10b
lea r13, [ r13 + rdx ]
lea r13, [ r13 + r10 ]
movzx rax, al
lea r11, [ r11 + r13 ]
lea r11, [ r11 + rax ]
adox r14, r11
movzx rbx, bl
lea r14, [ rbx + r14 ]
mov rbx, [ rsp + 0xc0 ]
lea r14, [rbx+r14]
adcx r14, [ rsp + 0xb8 ]
mov rbp, r9; x265, copying x261 here, cause x261 is needed in a reg for other than x265, namely all: , x265, x267, size: 2
shrd rbp, r14, 58; x265 <- x263||x261 >> 58
shr r14, 58; x266 <- x263>> 58
mov rdx, 0x3a ; moving imm to reg
bzhi r9, r9, rdx; x267 <- x261 (only least 0x3a bits)
mov rdx, [ rsp + 0x78 ]; x14 to rdx
mulx r10, rax, [ rsi + 0x0 ]; x100, x99<- arg1[0] * x14
mov rbx, rdx; preserving value of x14 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r13, r11, [ rsp + 0x80 ]; x86, x85<- arg1[1] * x15
mov rdx, r8; x10001 to rdx
mulx r8, rdi, [ rsi + 0x20 ]; x38, x37<- arg1[4] * x10001
xchg rdx, rcx; x10003, swapping with x10001, which is currently in rdx
mov [ rsp + 0xc8 ], r9; spilling x267 to mem
mov [ rsp + 0xd0 ], r14; spilling x266 to mem
mulx r9, r14, [ rsi + 0x28 ]; x32, x31<- arg1[5] * x10003
mov [ rsp + 0xd8 ], r10; spilling x100 to mem
mov r10, rdx; preserving value of x10003 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0xe0 ], r13; spilling x86 to mem
mov [ rsp + 0xe8 ], r8; spilling x38 to mem
mulx r13, r8, [ rsp + 0x70 ]; x28, x27<- arg1[6] * x10004
adox r8, r14
clc;
adcx r8, rdi
setc dl; spill CF x211 to reg (rdx)
clc;
adcx r8, r11
setc r11b; spill CF x215 to reg (r11)
clc;
adcx r8, rax
seto al; spill OF x207 to reg (rax)
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, rbp
movzx rax, al
lea r9, [ r9 + r13 ]
lea r9, [ r9 + rax ]
movzx rdx, dl
lea r9, [ rdx + r9 ]
mov rdx, [ rsp + 0xe8 ]
lea r9, [rdx+r9]
movzx r11, r11b
lea r9, [ r11 + r9 ]
mov r11, [ rsp + 0xe0 ]
lea r9, [r11+r9]
adcx r9, [ rsp + 0xd8 ]
adox r9, [ rsp + 0xd0 ]
mov rbp, r8; x272, copying x268 here, cause x268 is needed in a reg for other than x272, namely all: , x272, x274, size: 2
shrd rbp, r9, 58; x272 <- x270||x268 >> 58
shr r9, 58; x273 <- x270>> 58
mov r14, 0x3a ; moving imm to reg
bzhi r8, r8, r14; x274 <- x268 (only least 0x3a bits)
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r13, rax, [ rsp + 0x68 ]; x98, x97<- arg1[0] * x13
mov rdx, rbx; x14 to rdx
mulx r11, r14, [ rsi + 0x8 ]; x84, x83<- arg1[1] * x14
xchg rdx, rcx; x10001, swapping with x14, which is currently in rdx
mov [ rsp + 0xf0 ], r8; spilling x274 to mem
mulx rdi, r8, [ rsi + 0x28 ]; x30, x29<- arg1[5] * x10001
mov [ rsp + 0xf8 ], r9; spilling x273 to mem
mov r9, rdx; preserving value of x10001 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x100 ], r13; spilling x98 to mem
mov [ rsp + 0x108 ], r11; spilling x84 to mem
mulx r13, r11, [ rsi + 0x10 ]; x72, x71<- arg1[2] * arg1[2]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x110 ], r13; spilling x72 to mem
mulx r10, r13, r10; x26, x25<- arg1[6] * x10003
adox r13, r8
clc;
adcx r13, r11
setc dl; spill CF x195 to reg (rdx)
clc;
adcx r13, r14
seto r14b; spill OF x191 to reg (r14)
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, rax
seto al; spill OF x203 to reg (rax)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r13, rbp
movzx r14, r14b
lea rdi, [ rdi + r10 ]
lea rdi, [ rdi + r14 ]
movzx rdx, dl
lea rdi, [ rdx + rdi ]
mov rdx, [ rsp + 0x110 ]
lea rdi, [rdx+rdi]
adcx rdi, [ rsp + 0x108 ]
movzx rax, al
lea rdi, [ rax + rdi ]
mov rax, [ rsp + 0x100 ]
lea rdi, [rax+rdi]
adox rdi, [ rsp + 0xf8 ]
mov rbp, r13; x279, copying x275 here, cause x275 is needed in a reg for other than x279, namely all: , x279, x281, size: 2
shrd rbp, rdi, 58; x279 <- x277||x275 >> 58
shr rdi, 58; x280 <- x277>> 58
mov r11, 0x3a ; moving imm to reg
bzhi r13, r13, r11; x281 <- x275 (only least 0x3a bits)
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r10, r14, [ rsp + 0x58 ]; x96, x95<- arg1[0] * x12
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rax, r8, [ rsp + 0x68 ]; x82, x81<- arg1[1] * x13
mov rdx, rcx; x14 to rdx
mulx rdx, rcx, [ rsi + 0x10 ]; x70, x69<- arg1[2] * x14
mov r11, rdx; preserving value of x70 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0x118 ], r13; spilling x281 to mem
mov [ rsp + 0x120 ], rdi; spilling x280 to mem
mulx r13, rdi, r9; x24, x23<- arg1[6] * x10001
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x128 ], r10; spilling x96 to mem
mov [ rsp + 0x130 ], rax; spilling x82 to mem
mulx r10, rax, [ rsp + 0x60 ]; x22, x21<- arg1[7] * x10002
adox rax, rdi
clc;
adcx rax, rcx
seto dl; spill OF x175 to reg (rdx)
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rax, r8
setc r8b; spill CF x179 to reg (r8)
clc;
adcx rax, r14
seto r14b; spill OF x183 to reg (r14)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rax, rbp
movzx rdx, dl
lea r13, [ r13 + r10 ]
lea r13, [ r13 + rdx ]
movzx r8, r8b
lea r11, [ r11 + r13 ]
lea r11, [ r11 + r8 ]
movzx r14, r14b
lea r11, [ r14 + r11 ]
mov r14, [ rsp + 0x130 ]
lea r11, [r14+r11]
adcx r11, [ rsp + 0x128 ]
adox r11, [ rsp + 0x120 ]
mov rbp, rax; x286, copying x282 here, cause x282 is needed in a reg for other than x286, namely all: , x286, x288, size: 2
shrd rbp, r11, 58; x286 <- x284||x282 >> 58
shr r11, 58; x287 <- x284>> 58
mov rdi, 0x3ffffffffffffff ; moving imm to reg
and rax, rdi; x288 <- x282&0x3ffffffffffffff
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r10, r8, [ rsp + 0x50 ]; x94, x93<- arg1[0] * x9
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r14, r13, [ rsp + 0x58 ]; x80, x79<- arg1[1] * x12
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rcx, rdi, [ rsp + 0x68 ]; x68, x67<- arg1[2] * x13
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x138 ], rax; spilling x288 to mem
mov [ rsp + 0x140 ], r11; spilling x287 to mem
mulx rax, r11, [ rsi + 0x18 ]; x58, x57<- arg1[3] * arg1[3]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x148 ], r10; spilling x94 to mem
mulx r9, r10, r9; x20, x19<- arg1[7] * x10001
adox r10, r11
adcx r10, rdi
seto dl; spill OF x159 to reg (rdx)
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r10, r13
seto r13b; spill OF x167 to reg (r13)
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r10, r8
setc r8b; spill CF x163 to reg (r8)
clc;
adcx r10, rbp
movzx rdx, dl
lea rax, [ rax + r9 ]
lea rax, [ rax + rdx ]
movzx r8, r8b
lea rcx, [ rcx + rax ]
lea rcx, [ rcx + r8 ]
movzx r13, r13b
lea r14, [ r14 + rcx ]
lea r14, [ r14 + r13 ]
adox r14, [ rsp + 0x148 ]
adcx r14, [ rsp + 0x140 ]
mov rbp, r10; x293, copying x289 here, cause x289 is needed in a reg for other than x293, namely all: , x293, x295, size: 2
shrd rbp, r14, 58; x293 <- x291||x289 >> 58
shr r14, 58; x294 <- x291>> 58
mov r11, 0x3ffffffffffffff ; moving imm to reg
and r10, r11; x295 <- x289&0x3ffffffffffffff
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r9, r8, [ rsp + 0x48 ]; x92, x91<- arg1[0] * x6
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r13, rax, [ rsp + 0x50 ]; x78, x77<- arg1[1] * x9
mov rdx, [ rsp + 0x58 ]; x12 to rdx
mulx rcx, rdi, [ rsi + 0x10 ]; x66, x65<- arg1[2] * x12
mov r11, rdx; preserving value of x12 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x150 ], r10; spilling x295 to mem
mov [ rsp + 0x158 ], r14; spilling x294 to mem
mulx r10, r14, [ rsp + 0x68 ]; x56, x55<- arg1[3] * x13
mov rdx, [ rsp + 0x40 ]; x10000 to rdx
mov [ rsp + 0x160 ], r9; spilling x92 to mem
mulx rdx, r9, [ rsi + 0x40 ]; x18, x17<- arg1[8] * x10000
adox r9, r14
adcx r9, rdi
setc dil; spill CF x147 to reg (rdi)
clc;
adcx r9, rax
seto al; spill OF x143 to reg (rax)
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r9, r8
setc r8b; spill CF x151 to reg (r8)
clc;
adcx r9, rbp
movzx rax, al
lea r10, [ r10 + rdx ]
lea r10, [ r10 + rax ]
movzx rdi, dil
lea rcx, [ rcx + r10 ]
lea rcx, [ rcx + rdi ]
movzx r8, r8b
lea r13, [ r13 + rcx ]
lea r13, [ r13 + r8 ]
adox r13, [ rsp + 0x160 ]
adcx r13, [ rsp + 0x158 ]
mov rbp, r9; x300, copying x296 here, cause x296 is needed in a reg for other than x300, namely all: , x300, x302, size: 2
shrd rbp, r13, 58; x300 <- x298||x296 >> 58
shr r13, 58; x301 <- x298>> 58
mov rdx, 0x3ffffffffffffff ; moving imm to reg
and r9, rdx; x302 <- x296&0x3ffffffffffffff
mov rax, rdx; preserving value of 0x3ffffffffffffff into a new reg
mov rdx, [ rsp + 0x38 ]; saving x3 in rdx.
mulx rdx, rdi, [ rsi + 0x0 ]; x90, x89<- arg1[0] * x3
mov r8, rdx; preserving value of x90 into a new reg
mov rdx, [ rsp + 0x48 ]; saving x6 in rdx.
mulx rdx, r10, [ rsi + 0x8 ]; x76, x75<- arg1[1] * x6
mov rcx, rdx; preserving value of x76 into a new reg
mov rdx, [ rsp + 0x50 ]; saving x9 in rdx.
mulx rdx, r14, [ rsi + 0x10 ]; x64, x63<- arg1[2] * x9
xchg rdx, r11; x12, swapping with x64, which is currently in rdx
mulx rdx, rax, [ rsi + 0x18 ]; x54, x53<- arg1[3] * x12
mov [ rsp + 0x168 ], r9; spilling x302 to mem
mov r9, rdx; preserving value of x54 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x170 ], r13; spilling x301 to mem
mov [ rsp + 0x178 ], r8; spilling x90 to mem
mulx r13, r8, [ rsi + 0x20 ]; x46, x45<- arg1[4] * arg1[4]
adox r8, rax
adcx r8, r14
seto dl; spill OF x127 to reg (rdx)
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, r10
seto r10b; spill OF x135 to reg (r10)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r8, rdi
seto dil; spill OF x139 to reg (rdi)
mov rax, -0x3 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r8, rbp
movzx rdx, dl
lea r9, [ r9 + r13 ]
lea r9, [ r9 + rdx ]
adcx r11, r9
movzx r10, r10b
lea rcx, [ rcx + r11 ]
lea rcx, [ rcx + r10 ]
movzx rdi, dil
lea rcx, [ rdi + rcx ]
mov rdi, [ rsp + 0x178 ]
lea rcx, [rdi+rcx]
adox rcx, [ rsp + 0x170 ]
mov rbp, r8; x307, copying x303 here, cause x303 is needed in a reg for other than x307, namely all: , x307, x309, size: 2
shrd rbp, rcx, 57; x307 <- x305||x303 >> 57
shr rcx, 57; x308 <- x305>> 57
mov r13, 0x1ffffffffffffff ; moving imm to reg
and r8, r13; x309 <- x303&0x1ffffffffffffff
adox rbp, [ rsp + 0x98 ]
adox rcx, r14
mov rdx, rbp; x313, copying x310 here, cause x310 is needed in a reg for other than x313, namely all: , x313, x314, size: 2
shrd rdx, rcx, 58; x313 <- x312||x310 >> 58
mov r10, 0x3a ; moving imm to reg
bzhi rbp, rbp, r10; x314 <- x310 (only least 0x3a bits)
add rdx, [ rsp + 0xb0 ]
mov rdi, rdx; x316, copying x315 here, cause x315 is needed in a reg for other than x316, namely all: , x316, x317, size: 2
shr rdi, 58; x316 <- x315>> 58
bzhi rdx, rdx, r10; x317 <- x315 (only least 0x3a bits)
add rdi, [ rsp + 0xc8 ]
mov r9, [ rsp + 0x30 ]; load m64 out1 to register64
mov [ r9 + 0x0 ], rbp; out1[0] = x314
mov [ r9 + 0x8 ], rdx; out1[1] = x317
mov [ r9 + 0x10 ], rdi; out1[2] = x318
mov r11, [ rsp + 0xf0 ]; TMP = x274
mov [ r9 + 0x18 ], r11; out1[3] = TMP
mov r11, [ rsp + 0x118 ]; TMP = x281
mov [ r9 + 0x20 ], r11; out1[4] = TMP
mov r11, [ rsp + 0x138 ]; TMP = x288
mov [ r9 + 0x28 ], r11; out1[5] = TMP
mov r11, [ rsp + 0x150 ]; TMP = x295
mov [ r9 + 0x30 ], r11; out1[6] = TMP
mov r11, [ rsp + 0x168 ]; TMP = x302
mov [ r9 + 0x38 ], r11; out1[7] = TMP
mov [ r9 + 0x40 ], r8; out1[8] = x309
mov r15, [ rsp + 0x0 ] ; pop
mov r14, [ rsp + 0x8 ] ; pop
mov r13, [ rsp + 0x10 ] ; pop
mov r12, [ rsp + 0x18 ] ; pop
mov rbp, [ rsp + 0x20 ] ; pop
mov rbx, [ rsp + 0x28 ] ; pop
add rsp, 0x180 
ret
; cpu Intel(R) Core(TM) i5-8265U CPU @ 1.60GHz
; ratio 1.0087
; seed 1785685356 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1625 ms / 10 evals=> 162.5ms/eval
; Time spent for assembling and measureing (initial batch_size=50, initial num_batches=31): 69 ms
; number of used evaluations: 10
; Ratio (time for assembling + measure)/(total runtime for 10 evals): 0.04246153846153846
; number reverted permutation/ tried permutation: 5 / 5 =100.000%
; number reverted decision/ tried decision: 2 / 5 =40.000%