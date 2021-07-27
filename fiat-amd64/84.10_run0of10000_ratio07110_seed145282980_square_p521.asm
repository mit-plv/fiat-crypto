SECTION .text
	GLOBAL square_p521
square_p521:
sub rsp, 0x1a0 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x170 ], rbx; saving to stack
mov [ rsp + 0x178 ], rbp; saving to stack
mov [ rsp + 0x180 ], r12; saving to stack
mov [ rsp + 0x188 ], r13; saving to stack
mov [ rsp + 0x190 ], r14; saving to stack
mov [ rsp + 0x198 ], r15; saving to stack
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rax, r10, [ rsi + 0x0 ]; x106, x105<- arg1[0] * arg1[0]
mov r11, [ rsi + 0x40 ]; load m64 x1 to register64
imul rbx, r11, 0x2; x2 <- x1 * 0x2
imul rbx, rbx, 0x2; x10001 <- x2 * 0x2
mov rdx, rbx; x10001 to rdx
mulx rbx, rbp, [ rsi + 0x8 ]; x74, x73<- arg1[1] * x10001
mov r12, [ rsi + 0x38 ]; load m64 x4 to register64
imul r13, r12, 0x2; x5 <- x4 * 0x2
imul r13, r13, 0x2; x10003 <- x5 * 0x2
xchg rdx, r13; x10003, swapping with x10001, which is currently in rdx
mulx r14, r15, [ rsi + 0x10 ]; x62, x61<- arg1[2] * x10003
mov rcx, [ rsi + 0x30 ]; load m64 x7 to register64
imul r8, rcx, 0x2; x8 <- x7 * 0x2
imul r8, r8, 0x2; x10005 <- x8 * 0x2
mov r9, rdx; preserving value of x10003 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov [ rsp + 0x8 ], r11; spilling x1 to mem
mulx rdi, r11, r8; x52, x51<- arg1[3] * x10005
mov rdx, [ rsi + 0x28 ]; load m64 x10 to register64
mov [ rsp + 0x10 ], r13; spilling x10001 to mem
imul r13, rdx, 0x2; x11 <- x10 * 0x2
imul r13, r13, 0x2; x10007 <- x11 * 0x2
xchg rdx, r13; x10007, swapping with x10, which is currently in rdx
mov [ rsp + 0x18 ], r12; spilling x4 to mem
mulx rdx, r12, [ rsi + 0x20 ]; x44, x43<- arg1[4] * x10007
test al, al
adox r12, r11
adcx r12, r15
seto r15b; spill OF x108 to reg (r15)
mov r11, -0x2 ; moving imm to reg
inc r11; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, rbp
seto bpl; spill OF x116 to reg (rbp)
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r12, r10
movzx r15, r15b
lea rdi, [ rdi + rdx ]
lea rdi, [ rdi + r15 ]
adcx r14, rdi
movzx rbp, bpl
lea rbx, [ rbx + r14 ]
lea rbx, [ rbx + rbp ]
adox rax, rbx
mov r10, r12; x123, copying x119 here, cause x119 is needed in a reg for other than x123, namely all: , x123, x125, size: 2
shrd r10, rax, 58; x123 <- x121||x119 >> 58
imul rdx, [ rsi + 0x8 ], 0x2; x16 <- arg1[1] * 0x2
mulx rdx, r15, [ rsi + 0x0 ]; x104, x103<- arg1[0] * x16
mov rbp, rdx; preserving value of x104 into a new reg
mov rdx, [ rsp + 0x10 ]; saving x10001 in rdx.
mulx rdi, r14, [ rsi + 0x10 ]; x60, x59<- arg1[2] * x10001
xchg rdx, r9; x10003, swapping with x10001, which is currently in rdx
mulx rbx, r11, [ rsi + 0x18 ]; x50, x49<- arg1[3] * x10003
mov [ rsp + 0x20 ], rcx; spilling x7 to mem
mov rcx, rdx; preserving value of x10003 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x28 ], rbp; spilling x104 to mem
mov [ rsp + 0x30 ], rdi; spilling x60 to mem
mulx rbp, rdi, r8; x42, x41<- arg1[4] * x10005
imul r13, r13, 0x2; x10006 <- x10 * 0x2
mov rdx, r13; x10006 to rdx
mulx rdx, r13, [ rsi + 0x28 ]; x36, x35<- arg1[5] * x10006
add r13, rdi; could be done better, if r0 has been u8 as well
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, r11
seto r11b; spill OF x243 to reg (r11)
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r13, r14
seto r14b; spill OF x247 to reg (r14)
mov [ rsp + 0x38 ], rbx; spilling x50 to mem
mov rbx, -0x3 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r13, r15
setc r15b; spill CF x239 to reg (r15)
clc;
adcx r13, r10
setc r10b; spill CF x255 to reg (r10)
seto dil; spill OF x251 to reg (rdi)
shr rax, 58; x124 <- x121>> 58
sar  r15b, 1
adcx rbp, rdx
sar  r11b, 1
adcx rbp, [ rsp + 0x38 ]
sar  r14b, 1
adcx rbp, [ rsp + 0x30 ]
sar  dil, 1
adcx rbp, [ rsp + 0x28 ]
sar  r10b, 1
adcx rax, rbp
mov rdx, r13; x258, copying x254 here, cause x254 is needed in a reg for other than x258, namely all: , x260, x258, size: 2
shrd rdx, rax, 58; x258 <- x256||x254 >> 58
imul r15, [ rsi + 0x10 ], 0x2; x15 <- arg1[2] * 0x2
xchg rdx, r15; x15, swapping with x258, which is currently in rdx
mulx r11, r14, [ rsi + 0x0 ]; x102, x101<- arg1[0] * x15
mov rdi, rdx; preserving value of x15 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r10, rbp, [ rsi + 0x8 ]; x88, x87<- arg1[1] * arg1[1]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x40 ], r11; spilling x102 to mem
mulx rbx, r11, r9; x48, x47<- arg1[3] * x10001
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x48 ], r10; spilling x88 to mem
mov [ rsp + 0x50 ], rbx; spilling x48 to mem
mulx r10, rbx, rcx; x40, x39<- arg1[4] * x10003
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x58 ], r10; spilling x40 to mem
mulx r8, r10, r8; x34, x33<- arg1[5] * x10005
test al, al
adox r10, rbx
adcx r10, r11
setc dl; spill CF x227 to reg (rdx)
clc;
adcx r10, rbp
setc bpl; spill CF x231 to reg (rbp)
clc;
adcx r10, r14
setc r14b; spill CF x235 to reg (r14)
clc;
adcx r10, r15
setc r15b; spill CF x262 to reg (r15)
seto r11b; spill OF x223 to reg (r11)
shr rax, 58; x259 <- x256>> 58
sar  r11b, 1
adcx r8, [ rsp + 0x58 ]
sar  dl, 1
adcx r8, [ rsp + 0x50 ]
sar  bpl, 1
adcx r8, [ rsp + 0x48 ]
sar  r14b, 1
adcx r8, [ rsp + 0x40 ]
sar  r15b, 1
adcx rax, r8
mov rbx, r10; x265, copying x261 here, cause x261 is needed in a reg for other than x265, namely all: , x265, x267, size: 2
shrd rbx, rax, 58; x265 <- x263||x261 >> 58
imul r11, [ rsi + 0x18 ], 0x2; x14 <- arg1[3] * 0x2
mov rdx, r11; x14 to rdx
mulx r11, rbp, [ rsi + 0x0 ]; x100, x99<- arg1[0] * x14
xchg rdx, rdi; x15, swapping with x14, which is currently in rdx
mulx rdx, r14, [ rsi + 0x8 ]; x86, x85<- arg1[1] * x15
xchg rdx, r9; x10001, swapping with x86, which is currently in rdx
mulx r15, r8, [ rsi + 0x20 ]; x38, x37<- arg1[4] * x10001
xchg rdx, rcx; x10003, swapping with x10001, which is currently in rdx
mov [ rsp + 0x60 ], r12; spilling x119 to mem
mov [ rsp + 0x68 ], r11; spilling x100 to mem
mulx r12, r11, [ rsi + 0x28 ]; x32, x31<- arg1[5] * x10003
mov [ rsp + 0x70 ], r9; spilling x86 to mem
imul r9, [ rsp + 0x20 ], 0x2; x10004 <- x7 * 0x2
mov [ rsp + 0x78 ], r15; spilling x38 to mem
mov r15, rdx; preserving value of x10003 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0x80 ], r12; spilling x32 to mem
mulx r9, r12, r9; x28, x27<- arg1[6] * x10004
xor rdx, rdx
adox r12, r11
adcx r12, r8
setc r8b; spill CF x211 to reg (r8)
clc;
adcx r12, r14
seto r14b; spill OF x207 to reg (r14)
mov r11, -0x3 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r12, rbp
setc bpl; spill CF x215 to reg (rbp)
clc;
adcx r12, rbx
setc bl; spill CF x269 to reg (rbx)
seto dl; spill OF x219 to reg (rdx)
shr rax, 58; x266 <- x263>> 58
sar  r14b, 1
adcx r9, [ rsp + 0x80 ]
sar  r8b, 1
adcx r9, [ rsp + 0x78 ]
sar  bpl, 1
adcx r9, [ rsp + 0x70 ]
sar  dl, 1
adcx r9, [ rsp + 0x68 ]
sar  bl, 1
adcx rax, r9
mov r14, r12; x272, copying x268 here, cause x268 is needed in a reg for other than x272, namely all: , x272, x274, size: 2
shrd r14, rax, 58; x272 <- x270||x268 >> 58
imul r8, [ rsi + 0x20 ], 0x2; x13 <- arg1[4] * 0x2
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rbp, rbx, r8; x98, x97<- arg1[0] * x13
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r9, r11, rdi; x84, x83<- arg1[1] * x14
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x88 ], rbp; spilling x98 to mem
mov [ rsp + 0x90 ], r9; spilling x84 to mem
mulx rbp, r9, [ rsi + 0x10 ]; x72, x71<- arg1[2] * arg1[2]
mov rdx, rcx; x10001 to rdx
mov [ rsp + 0x98 ], rbp; spilling x72 to mem
mulx rcx, rbp, [ rsi + 0x28 ]; x30, x29<- arg1[5] * x10001
mov [ rsp + 0xa0 ], rcx; spilling x30 to mem
mov rcx, rdx; preserving value of x10001 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0xa8 ], r14; spilling x272 to mem
mulx r15, r14, r15; x26, x25<- arg1[6] * x10003
xor rdx, rdx
adox r14, rbp
adcx r14, r9
seto r9b; spill OF x191 to reg (r9)
mov rbp, -0x3 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r14, r11
seto r11b; spill OF x199 to reg (r11)
mov rbp, -0x3 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r14, rbx
setc bl; spill CF x195 to reg (rbx)
clc;
adcx r14, [ rsp + 0xa8 ]
setc dl; spill CF x276 to reg (rdx)
seto bpl; spill OF x203 to reg (rbp)
shr rax, 58; x273 <- x270>> 58
sar  r9b, 1
adcx r15, [ rsp + 0xa0 ]
sar  bl, 1
adcx r15, [ rsp + 0x98 ]
sar  r11b, 1
adcx r15, [ rsp + 0x90 ]
sar  bpl, 1
adcx r15, [ rsp + 0x88 ]
sar  dl, 1
adcx rax, r15
mov r9, r14; x279, copying x275 here, cause x275 is needed in a reg for other than x279, namely all: , x279, x281, size: 2
shrd r9, rax, 58; x279 <- x277||x275 >> 58
mov rbx, 0x3ffffffffffffff ; moving imm to reg
and r13, rbx; x260 <- x254&0x3ffffffffffffff
imul r11, [ rsi + 0x28 ], 0x2; x12 <- arg1[5] * 0x2
mov rdx, r11; x12 to rdx
mulx r11, rbp, [ rsi + 0x0 ]; x96, x95<- arg1[0] * x12
xchg rdx, r8; x13, swapping with x12, which is currently in rdx
mulx r15, rbx, [ rsi + 0x8 ]; x82, x81<- arg1[1] * x13
xchg rdx, rdi; x14, swapping with x13, which is currently in rdx
mov [ rsp + 0xb0 ], r13; spilling x260 to mem
mulx rdx, r13, [ rsi + 0x10 ]; x70, x69<- arg1[2] * x14
mov [ rsp + 0xb8 ], r11; spilling x96 to mem
mov r11, rdx; preserving value of x70 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0xc0 ], r15; spilling x82 to mem
mov [ rsp + 0xc8 ], r9; spilling x279 to mem
mulx r15, r9, rcx; x24, x23<- arg1[6] * x10001
imul rdx, [ rsp + 0x18 ], 0x2; x10002 <- x4 * 0x2
mov [ rsp + 0xd0 ], r11; spilling x70 to mem
mulx rdx, r11, [ rsi + 0x38 ]; x22, x21<- arg1[7] * x10002
test al, al
adox r11, r9
adcx r11, r13
setc r13b; spill CF x179 to reg (r13)
clc;
adcx r11, rbx
seto bl; spill OF x175 to reg (rbx)
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, rbp
seto bpl; spill OF x187 to reg (rbp)
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r11, [ rsp + 0xc8 ]
setc r9b; spill CF x183 to reg (r9)
mov [ rsp + 0xd8 ], r11; spilling x282 to mem
seto r11b; spill OF x283 to reg (r11)
shr rax, 58; x280 <- x277>> 58
sar  bl, 1
adcx r15, rdx
sar  r13b, 1
adcx r15, [ rsp + 0xd0 ]
sar  r9b, 1
adcx r15, [ rsp + 0xc0 ]
sar  bpl, 1
adcx r15, [ rsp + 0xb8 ]
sar  r11b, 1
adcx rax, r15
mov rdx, [ rsp + 0xd8 ]; load m64 x282 to register64
mov rbx, rdx; x286, copying x282 here, cause x282 is needed in a reg for other than x286, namely all: , x286, x288, size: 2
shrd rbx, rax, 58; x286 <- x284||x282 >> 58
imul r13, [ rsi + 0x30 ], 0x2; x9 <- arg1[6] * 0x2
mov r9, rdx; preserving value of x282 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx rbp, r11, r13; x94, x93<- arg1[0] * x9
mov rdx, r8; x12 to rdx
mulx r8, r15, [ rsi + 0x8 ]; x80, x79<- arg1[1] * x12
mov [ rsp + 0xe0 ], rbp; spilling x94 to mem
mov rbp, rdx; preserving value of x12 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0xe8 ], r8; spilling x80 to mem
mov [ rsp + 0xf0 ], rbx; spilling x286 to mem
mulx r8, rbx, rdi; x68, x67<- arg1[2] * x13
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0xf8 ], r8; spilling x68 to mem
mov [ rsp + 0x100 ], r11; spilling x93 to mem
mulx r8, r11, [ rsi + 0x18 ]; x58, x57<- arg1[3] * arg1[3]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x108 ], r8; spilling x58 to mem
mulx rcx, r8, rcx; x20, x19<- arg1[7] * x10001
add r8, r11; could be done better, if r0 has been u8 as well
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, rbx
seto bl; spill OF x163 to reg (rbx)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r8, r15
setc r15b; spill CF x159 to reg (r15)
clc;
adcx r8, [ rsp + 0x100 ]
seto r11b; spill OF x167 to reg (r11)
mov byte [ rsp + 0x110 ], bl; spilling byte x163 to mem
mov rbx, -0x3 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r8, [ rsp + 0xf0 ]
setc dl; spill CF x171 to reg (rdx)
seto bl; spill OF x290 to reg (rbx)
shr rax, 58; x287 <- x284>> 58
sar  r15b, 1
adcx rcx, [ rsp + 0x108 ]
sar byte [ rsp + 0x110 ], 1
adcx rcx, [ rsp + 0xf8 ]
sar  r11b, 1
adcx rcx, [ rsp + 0xe8 ]
sar  dl, 1
adcx rcx, [ rsp + 0xe0 ]
sar  bl, 1
adcx rax, rcx
mov r15, rax; x294, copying x291 here, cause x291 is needed in a reg for other than x294, namely all: , x294, x293, size: 2
shr r15, 58; x294 <- x291>> 58
mov r11, r8; x293, copying x289 here, cause x289 is needed in a reg for other than x293, namely all: , x293, x295, size: 2
shrd r11, rax, 58; x293 <- x291||x289 >> 58
imul rdx, [ rsi + 0x38 ], 0x2; x6 <- arg1[7] * 0x2
mulx rbx, rcx, [ rsi + 0x0 ]; x92, x91<- arg1[0] * x6
mov rax, rdx; preserving value of x6 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x118 ], r15; spilling x294 to mem
mov [ rsp + 0x120 ], rbx; spilling x92 to mem
mulx r15, rbx, r13; x78, x77<- arg1[1] * x9
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x128 ], r15; spilling x78 to mem
mov [ rsp + 0x130 ], r11; spilling x293 to mem
mulx r15, r11, rbp; x66, x65<- arg1[2] * x12
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x138 ], r15; spilling x66 to mem
mulx rdi, r15, rdi; x56, x55<- arg1[3] * x13
imul rdx, [ rsp + 0x8 ], 0x2; x10000 <- x1 * 0x2
mov [ rsp + 0x140 ], rdi; spilling x56 to mem
mulx rdx, rdi, [ rsi + 0x40 ]; x18, x17<- arg1[8] * x10000
test al, al
adox rdi, r15
adcx rdi, r11
seto r11b; spill OF x143 to reg (r11)
mov r15, -0x2 ; moving imm to reg
inc r15; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rdi, rbx
seto bl; spill OF x151 to reg (rbx)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rdi, rcx
setc cl; spill CF x147 to reg (rcx)
clc;
adcx rdi, [ rsp + 0x130 ]
movzx r11, r11b
lea rdx, [ r11 + rdx ]
mov r11, [ rsp + 0x140 ]
lea rdx, [r11+rdx]
movzx rcx, cl
lea rdx, [ rcx + rdx ]
mov rcx, [ rsp + 0x138 ]
lea rdx, [rcx+rdx]
movzx rbx, bl
lea rdx, [ rbx + rdx ]
mov rbx, [ rsp + 0x128 ]
lea rdx, [rbx+rdx]
adox rdx, [ rsp + 0x120 ]
adcx rdx, [ rsp + 0x118 ]
mov r11, rdi; x300, copying x296 here, cause x296 is needed in a reg for other than x300, namely all: , x300, x302, size: 2
shrd r11, rdx, 58; x300 <- x298||x296 >> 58
imul rcx, [ rsi + 0x40 ], 0x2; x3 <- arg1[8] * 0x2
xchg rdx, rcx; x3, swapping with x298, which is currently in rdx
mulx rdx, rbx, [ rsi + 0x0 ]; x90, x89<- arg1[0] * x3
mov r15, rdx; preserving value of x90 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x148 ], r11; spilling x300 to mem
mulx rax, r11, rax; x76, x75<- arg1[1] * x6
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x150 ], r15; spilling x90 to mem
mulx r13, r15, r13; x64, x63<- arg1[2] * x9
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x158 ], rax; spilling x76 to mem
mulx rbp, rax, rbp; x54, x53<- arg1[3] * x12
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x160 ], r13; spilling x64 to mem
mov [ rsp + 0x168 ], rbp; spilling x54 to mem
mulx r13, rbp, [ rsi + 0x20 ]; x46, x45<- arg1[4] * arg1[4]
xor rdx, rdx
adox rbp, rax
adcx rbp, r15
setc r15b; spill CF x131 to reg (r15)
clc;
adcx rbp, r11
setc r11b; spill CF x135 to reg (r11)
clc;
adcx rbp, rbx
setc bl; spill CF x139 to reg (rbx)
clc;
adcx rbp, [ rsp + 0x148 ]
setc al; spill CF x304 to reg (rax)
seto dl; spill OF x127 to reg (rdx)
shr rcx, 58; x301 <- x298>> 58
sar  dl, 1
adcx r13, [ rsp + 0x168 ]
sar  r15b, 1
adcx r13, [ rsp + 0x160 ]
sar  r11b, 1
adcx r13, [ rsp + 0x158 ]
sar  bl, 1
adcx r13, [ rsp + 0x150 ]
sar  al, 1
adcx rcx, r13
mov rdx, rcx; x308, copying x305 here, cause x305 is needed in a reg for other than x308, namely all: , x308, x307, size: 2
shr rdx, 57; x308 <- x305>> 57
mov r15, 0x3a ; moving imm to reg
bzhi r12, r12, r15; x274 <- x268 (only least 0x3a bits)
mov r11, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r11 + 0x18 ], r12; out1[3] = x274
bzhi r15, [ rsp + 0x60 ], r15; x125 <- x119 (only least 0x3a bits)
mov rbx, rbp; x307, copying x303 here, cause x303 is needed in a reg for other than x307, namely all: , x309, x307, size: 2
shrd rbx, rcx, 57; x307 <- x305||x303 >> 57
test al, al
adox rbx, r15
mov rax, 0x3ffffffffffffff ; moving imm to reg
seto r13b; spill OF x311 to reg (r13)
mov rcx, rbx; x314, copying x310 here, cause x310 is needed in a reg for other than x314, namely all: , x314, x313, size: 2
and rcx, rax; x314 <- x310&0x3ffffffffffffff
movzx r12, r13b; x312, copying x311 here, cause x311 is needed in a reg for other than x312, namely all: , x312, size: 1
lea r12, [ r12 + rdx ]
shrd rbx, r12, 58; x313 <- x312||x310 >> 58
add rbx, [ rsp + 0xb0 ]
mov rdx, rbx; x317, copying x315 here, cause x315 is needed in a reg for other than x317, namely all: , x317, x316, size: 2
and rdx, rax; x317 <- x315&0x3ffffffffffffff
mov r15, 0x3a ; moving imm to reg
bzhi r9, r9, r15; x288 <- x282 (only least 0x3a bits)
mov [ r11 + 0x28 ], r9; out1[5] = x288
shr rbx, 58; x316 <- x315>> 58
bzhi r10, r10, r15; x267 <- x261 (only least 0x3a bits)
lea rbx, [ rbx + r10 ]
mov [ r11 + 0x8 ], rdx; out1[1] = x317
mov [ r11 + 0x10 ], rbx; out1[2] = x318
mov r13, 0x39 ; moving imm to reg
bzhi rbp, rbp, r13; x309 <- x303 (only least 0x39 bits)
bzhi rdi, rdi, r15; x302 <- x296 (only least 0x3a bits)
mov [ r11 + 0x38 ], rdi; out1[7] = x302
bzhi r14, r14, r15; x281 <- x275 (only least 0x3a bits)
mov [ r11 + 0x20 ], r14; out1[4] = x281
bzhi r8, r8, r15; x295 <- x289 (only least 0x3a bits)
mov [ r11 + 0x30 ], r8; out1[6] = x295
mov [ r11 + 0x40 ], rbp; out1[8] = x309
mov [ r11 + 0x0 ], rcx; out1[0] = x314
mov rbx, [ rsp + 0x170 ]; restoring from stack
mov rbp, [ rsp + 0x178 ]; restoring from stack
mov r12, [ rsp + 0x180 ]; restoring from stack
mov r13, [ rsp + 0x188 ]; restoring from stack
mov r14, [ rsp + 0x190 ]; restoring from stack
mov r15, [ rsp + 0x198 ]; restoring from stack
add rsp, 0x1a0 
ret
; cpu Intel(R) Core(TM) i5-8265U CPU @ 1.60GHz
; clocked at 1800 MHz
; first cyclecount 84.11, best 84.1025, lastGood 84.1025
; seed 145282980 
; CC / CFLAGS gcc / -march=native -mtune=native -O3 
; time needed: 192 ms / 0 runs=> Infinityms/run
; Time spent for assembling and measureing (initial batch_size=168, initial num_batches=101): 17 ms
; Ratio (time for assembling + measure)/(total runtime for 0runs): 0.08854166666666667
; number reverted permutation/ tried permutation: 0 / 0 =NaN%
; number reverted decision/ tried decision: 0 / 1 =0.000%