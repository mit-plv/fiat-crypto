SECTION .text
	GLOBAL square_p521
square_p521:
sub rsp, 0x138 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x108 ], rbx; saving to stack
mov [ rsp + 0x110 ], rbp; saving to stack
mov [ rsp + 0x118 ], r12; saving to stack
mov [ rsp + 0x120 ], r13; saving to stack
mov [ rsp + 0x128 ], r14; saving to stack
mov [ rsp + 0x130 ], r15; saving to stack
mov rax, [ rsi + 0x40 ]; load m64 x1 to register64
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r11, rbx, [ rsi + 0x0 ]; x106, x105<- arg1[0] * arg1[0]
mov rbp, [ rsi + 0x30 ]; load m64 x7 to register64
imul r12, rbp, 0x2; x8 <- x7 * 0x2

; old
; imul r10, rax, 0x2; x2 <- x1 * 0x2
; imul r10, r10, 0x2; x10001 <- x2 * 0x2
shlx r10, [ rsi + 0x40 ], 0x2 ; x10001 <- x1 (x1==arg1[8]) * 2 * 2 (by shlx'ing from memory by 2)
; this tests, if the shl-mul-rewrite occurs before the constant-folding

imul r12, r12, 0x2; x10005 <- x8 * 0x2
mov r13, [ rsi + 0x28 ]; load m64 x10 to register64
imul r14, r13, 0x2; x11 <- x10 * 0x2
imul r14, r14, 0x2; x10007 <- x11 * 0x2
mov r15, [ rsi + 0x38 ]; load m64 x4 to register64
mov rdx, r10; x10001 to rdx
mulx r10, rcx, [ rsi + 0x8 ]; x74, x73<- arg1[1] * x10001
mov r8, rdx; preserving value of x10001 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r9, rdi, r12; x52, x51<- arg1[3] * x10005
imul rdx, r15, 0x2; x5 <- x4 * 0x2
xchg rdx, r14; x10007, swapping with x5, which is currently in rdx
mov [ rsp + 0x8 ], rax; spilling x1 to mem
mulx rdx, rax, [ rsi + 0x20 ]; x44, x43<- arg1[4] * x10007
imul r14, r14, 0x2; x10003 <- x5 * 0x2
add rax, rdi; could be done better, if r0 has been u8 as well
adcx r9, rdx
mov rdx, r14; x10003 to rdx
mulx r14, rdi, [ rsi + 0x10 ]; x62, x61<- arg1[2] * x10003
add rax, rdi; could be done better, if r0 has been u8 as well
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rax, rcx
adcx r14, r9
seto cl; spill OF x116 to reg (rcx)
imul r9, [ rsi + 0x8 ], 0x2; x16 <- arg1[1] * 0x2
sar  cl, 1
adcx r10, r14
xchg rdx, r8; x10001, swapping with x10003, which is currently in rdx
mulx rcx, r14, [ rsi + 0x10 ]; x60, x59<- arg1[2] * x10001
xchg rdx, r8; x10003, swapping with x10001, which is currently in rdx
mov [ rsp + 0x10 ], rbp; spilling x7 to mem
mulx rdi, rbp, [ rsi + 0x18 ]; x50, x49<- arg1[3] * x10003
mov [ rsp + 0x18 ], rcx; spilling x60 to mem
mov rcx, rdx; preserving value of x10003 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x20 ], rdi; spilling x50 to mem
mulx r9, rdi, r9; x104, x103<- arg1[0] * x16
adox rax, rbx
adox r11, r10
imul r13, r13, 0x2; x10006 <- x10 * 0x2
mov rdx, r12; x10005 to rdx
mulx r12, rbx, [ rsi + 0x20 ]; x42, x41<- arg1[4] * x10005
mov r10, rdx; preserving value of x10005 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x28 ], r15; spilling x4 to mem
mulx r13, r15, r13; x36, x35<- arg1[5] * x10006
mov rdx, rax; x123, copying x119 here, cause x119 is needed in a reg for other than x123, namely all: , x123, x125, size: 2
shrd rdx, r11, 58; x123 <- x121||x119 >> 58
test al, al
adox r15, rbx
adcx r15, rbp
adox r12, r13
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, r14
seto r14b; spill OF x247 to reg (r14)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r15, rdi
adcx r12, [ rsp + 0x20 ]
movzx r14, r14b
lea r12, [ r14 + r12 ]
mov r14, [ rsp + 0x18 ]
lea r12, [r14+r12]
clc;
adcx r15, rdx
adox r9, r12
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mulx r10, rdi, r10; x34, x33<- arg1[5] * x10005
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rbx, r13, r8; x48, x47<- arg1[3] * x10001
setc dl; spill CF x255 to reg (rdx)
shr r11, 58; x124 <- x121>> 58
sar  dl, 1
adcx r11, r9
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r14, r12, [ rsi + 0x8 ]; x88, x87<- arg1[1] * arg1[1]
mov rdx, r15; x258, copying x254 here, cause x254 is needed in a reg for other than x258, namely all: , x260, x258, size: 2
shrd rdx, r11, 58; x258 <- x256||x254 >> 58
mov r9, rdx; preserving value of x258 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x30 ], r14; spilling x88 to mem
mulx rbp, r14, rcx; x40, x39<- arg1[4] * x10003
shr r11, 58; x259 <- x256>> 58
imul rdx, [ rsi + 0x10 ], 0x2; x15 <- arg1[2] * 0x2
test al, al
adox rdi, r14
adcx rdi, r13
mulx r13, r14, [ rsi + 0x0 ]; x102, x101<- arg1[0] * x15
xchg rdx, r8; x10001, swapping with x15, which is currently in rdx
mov [ rsp + 0x38 ], r11; spilling x259 to mem
mov [ rsp + 0x40 ], r13; spilling x102 to mem
mulx r11, r13, [ rsi + 0x20 ]; x38, x37<- arg1[4] * x10001
adox rbp, r10
adcx rbx, rbp
xor r10, r10
adox rdi, r12
xchg rdx, r8; x15, swapping with x10001, which is currently in rdx
mulx rdx, r12, [ rsi + 0x8 ]; x86, x85<- arg1[1] * x15
adox rbx, [ rsp + 0x30 ]
imul rbp, [ rsp + 0x10 ], 0x2; x10004 <- x7 * 0x2
mov [ rsp + 0x48 ], rdx; spilling x86 to mem
xor rdx, rdx
adox rdi, r14
adcx rdi, r9
mov r10, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mulx rbp, r9, rbp; x28, x27<- arg1[6] * x10004
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mulx r14, r10, rcx; x32, x31<- arg1[5] * x10003
adox rbx, [ rsp + 0x40 ]
adcx rbx, [ rsp + 0x38 ]
add r9, r10; could be done better, if r0 has been u8 as well
adcx r14, rbp
imul rdx, [ rsi + 0x18 ], 0x2; x14 <- arg1[3] * 0x2
xor rbp, rbp
adox r9, r13
adox r11, r14
mov r13, rdi; x265, copying x261 here, cause x261 is needed in a reg for other than x265, namely all: , x265, x267, size: 2
shrd r13, rbx, 58; x265 <- x263||x261 >> 58
xor r10, r10
adox r9, r12
mulx rbp, r12, [ rsi + 0x0 ]; x100, x99<- arg1[0] * x14
adox r11, [ rsp + 0x48 ]
adcx r9, r12
adcx rbp, r11
mulx r14, r12, [ rsi + 0x8 ]; x84, x83<- arg1[1] * x14
shr rbx, 58; x266 <- x263>> 58
xchg rdx, r8; x10001, swapping with x14, which is currently in rdx
mulx r11, r10, [ rsi + 0x28 ]; x30, x29<- arg1[5] * x10001
test al, al
adox r9, r13
seto r13b; spill OF x269 to reg (r13)
mov [ rsp + 0x50 ], r14; spilling x84 to mem
imul r14, [ rsi + 0x20 ], 0x2; x13 <- arg1[4] * 0x2
sar  r13b, 1
adcx rbx, rbp
mov rbp, rbx; x273, copying x270 here, cause x270 is needed in a reg for other than x273, namely all: , x273, x272, size: 2
shr rbp, 58; x273 <- x270>> 58
mov r13, rdx; preserving value of x10001 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x58 ], rax; spilling x119 to mem
mov [ rsp + 0x60 ], rbp; spilling x273 to mem
mulx rax, rbp, r14; x82, x81<- arg1[1] * x13
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x68 ], rax; spilling x82 to mem
mulx rcx, rax, rcx; x26, x25<- arg1[6] * x10003
mov rdx, r14; x13 to rdx
mov [ rsp + 0x70 ], rbp; spilling x81 to mem
mulx r14, rbp, [ rsi + 0x0 ]; x98, x97<- arg1[0] * x13
add rax, r10; could be done better, if r0 has been u8 as well
adcx r11, rcx
imul r10, [ rsi + 0x28 ], 0x2; x12 <- arg1[5] * 0x2
mov rcx, rdx; preserving value of x13 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x78 ], r14; spilling x98 to mem
mov [ rsp + 0x80 ], rbp; spilling x97 to mem
mulx r14, rbp, [ rsi + 0x10 ]; x72, x71<- arg1[2] * arg1[2]
mov rdx, r9; x272, copying x268 here, cause x268 is needed in a reg for other than x272, namely all: , x272, x274, size: 2
shrd rdx, rbx, 58; x272 <- x270||x268 >> 58
add rax, rbp; could be done better, if r0 has been u8 as well
xchg rdx, r8; x14, swapping with x272, which is currently in rdx
mulx rdx, rbx, [ rsi + 0x10 ]; x70, x69<- arg1[2] * x14
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rax, r12
adcx r14, r11
xchg rdx, r10; x12, swapping with x70, which is currently in rdx
mulx r12, r11, [ rsi + 0x0 ]; x96, x95<- arg1[0] * x12
clc;
adcx rax, [ rsp + 0x80 ]
adox r14, [ rsp + 0x50 ]
adcx r14, [ rsp + 0x78 ]
imul rbp, [ rsp + 0x28 ], 0x2; x10002 <- x4 * 0x2
mov [ rsp + 0x88 ], r12; spilling x96 to mem
xor r12, r12
adox rax, r8
mov r8, rdx; preserving value of x12 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0x90 ], r11; spilling x95 to mem
mulx r12, r11, r13; x24, x23<- arg1[6] * x10001
mov rdx, rbp; x10002 to rdx
mulx rdx, rbp, [ rsi + 0x38 ]; x22, x21<- arg1[7] * x10002
adox r14, [ rsp + 0x60 ]
mov [ rsp + 0x98 ], r10; spilling x70 to mem
mov r10, r14; x280, copying x277 here, cause x277 is needed in a reg for other than x280, namely all: , x279, x280, size: 2
shr r10, 58; x280 <- x277>> 58
add rbp, r11; could be done better, if r0 has been u8 as well
setc r11b; spill CF x175 to reg (r11)
mov [ rsp + 0xa0 ], r10; spilling x280 to mem
mov r10, rax; x279, copying x275 here, cause x275 is needed in a reg for other than x279, namely all: , x281, x279, size: 2
shrd r10, r14, 58; x279 <- x277||x275 >> 58
xor r14, r14
adox rbp, rbx
adcx rbp, [ rsp + 0x70 ]
movzx r11, r11b
lea r12, [ r12 + rdx ]
lea r12, [ r12 + r11 ]
adox r12, [ rsp + 0x98 ]
adcx r12, [ rsp + 0x68 ]
imul rbx, [ rsi + 0x30 ], 0x2; x9 <- arg1[6] * 0x2
mov rdx, r13; x10001 to rdx
mulx rdx, r13, [ rsi + 0x38 ]; x20, x19<- arg1[7] * x10001
xor r11, r11
adox rbp, [ rsp + 0x90 ]
adcx rbp, r10
adox r12, [ rsp + 0x88 ]
xchg rdx, rbx; x9, swapping with x20, which is currently in rdx
mulx r14, r10, [ rsi + 0x0 ]; x94, x93<- arg1[0] * x9
mov r11, rdx; preserving value of x9 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0xa8 ], r14; spilling x94 to mem
mov [ rsp + 0xb0 ], r10; spilling x93 to mem
mulx r14, r10, [ rsi + 0x18 ]; x58, x57<- arg1[3] * arg1[3]
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, r10
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0xb8 ], rbp; spilling x282 to mem
mulx r10, rbp, rcx; x68, x67<- arg1[2] * x13
setc dl; spill CF x283 to reg (rdx)
clc;
adcx r13, rbp
movzx rdx, dl
lea r12, [ rdx + r12 ]
mov rdx, [ rsp + 0xa0 ]
lea r12, [rdx+r12]
adox r14, rbx
mov rdx, r11; x9 to rdx
mulx r11, rbx, [ rsi + 0x8 ]; x78, x77<- arg1[1] * x9
adcx r10, r14
mov rbp, [ rsp + 0xb8 ]; load m64 x282 to register64
mov r14, rbp; x286, copying x282 here, cause x282 is needed in a reg for other than x286, namely all: , x288, x286, size: 2
shrd r14, r12, 58; x286 <- x284||x282 >> 58
mov [ rsp + 0xc0 ], r11; spilling x78 to mem
mov r11, 0x3ffffffffffffff ; moving imm to reg
and rdi, r11; x267 <- x261&0x3ffffffffffffff
mov r11, rdx; preserving value of x9 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0xc8 ], rdi; spilling x267 to mem
mov [ rsp + 0xd0 ], r15; spilling x254 to mem
mulx rdi, r15, r8; x80, x79<- arg1[1] * x12
adox r13, r15
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0xd8 ], rbx; spilling x77 to mem
mulx r15, rbx, r8; x66, x65<- arg1[2] * x12
seto dl; spill OF x167 to reg (rdx)
shr r12, 58; x287 <- x284>> 58
sar  dl, 1
adcx rdi, r10
imul r10, [ rsi + 0x38 ], 0x2; x6 <- arg1[7] * 0x2
add r13, [ rsp + 0xb0 ]; could be done better, if r0 has been u8 as well
setc dl; spill CF x171 to reg (rdx)
mov [ rsp + 0xe0 ], r15; spilling x66 to mem
imul r15, [ rsp + 0x8 ], 0x2; x10000 <- x1 * 0x2
sar  dl, 1
adcx rdi, [ rsp + 0xa8 ]
mov rdx, [ rsi + 0x40 ]; arg1[8] to rdx
mov [ rsp + 0xe8 ], rbx; spilling x65 to mem
mulx r15, rbx, r15; x18, x17<- arg1[8] * x10000
mov rdx, rcx; x13 to rdx
mulx rdx, rcx, [ rsi + 0x18 ]; x56, x55<- arg1[3] * x13
adox rbx, rcx
clc;
adcx r13, r14
adcx r12, rdi
mov r14, rdx; preserving value of x56 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx rdi, rcx, r10; x92, x91<- arg1[0] * x6
clc;
adcx rbx, [ rsp + 0xe8 ]
adox r14, r15
setc dl; spill CF x147 to reg (rdx)
mov r15, r13; x293, copying x289 here, cause x289 is needed in a reg for other than x293, namely all: , x293, x295, size: 2
shrd r15, r12, 58; x293 <- x291||x289 >> 58
add rbx, [ rsp + 0xd8 ]; could be done better, if r0 has been u8 as well
movzx rdx, dl
lea r14, [ rdx + r14 ]
mov rdx, [ rsp + 0xe0 ]
lea r14, [rdx+r14]
adcx r14, [ rsp + 0xc0 ]
add rbx, rcx; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r11, rcx, r11; x64, x63<- arg1[2] * x9
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0xf0 ], r11; spilling x64 to mem
mov [ rsp + 0xf8 ], rcx; spilling x63 to mem
mulx r11, rcx, [ rsi + 0x20 ]; x46, x45<- arg1[4] * arg1[4]
adcx rdi, r14
shr r12, 58; x294 <- x291>> 58
add rbx, r15; could be done better, if r0 has been u8 as well
adcx r12, rdi
mov rdx, 0x3ffffffffffffff ; moving imm to reg
mov r15, rbx; x302, copying x296 here, cause x296 is needed in a reg for other than x302, namely all: , x300, x302, size: 2
and r15, rdx; x302 <- x296&0x3ffffffffffffff
xchg rdx, r8; x12, swapping with 0x3ffffffffffffff, which is currently in rdx
mulx rdx, r14, [ rsi + 0x18 ]; x54, x53<- arg1[3] * x12
imul rdi, [ rsi + 0x40 ], 0x2; x3 <- arg1[8] * 0x2
shrd rbx, r12, 58; x300 <- x298||x296 >> 58
test al, al
adox rcx, r14
mov r14, rdx; preserving value of x54 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r10, r8, r10; x76, x75<- arg1[1] * x6
adcx rcx, [ rsp + 0xf8 ]
adox r14, r11
adcx r14, [ rsp + 0xf0 ]
mov rdx, rdi; x3 to rdx
mulx rdx, r11, [ rsi + 0x0 ]; x90, x89<- arg1[0] * x3
add rcx, r8; could be done better, if r0 has been u8 as well
mov r8, 0x3ffffffffffffff ; moving imm to reg
mov [ rsp + 0x100 ], r15; spilling x302 to mem
setc r15b; spill CF x135 to reg (r15)
and rbp, r8; x288 <- x282&0x3ffffffffffffff
adox rcx, r11
adcx rcx, rbx
movzx r15, r15b
lea r10, [ r10 + r14 ]
lea r10, [ r10 + r15 ]
setc bl; spill CF x304 to reg (rbx)
seto r14b; spill OF x139 to reg (r14)
shr r12, 58; x301 <- x298>> 58
sar  r14b, 1
adcx rdx, r10
mov r11, [ rsp + 0x0 ]; load m64 out1 to register64
mov r15, [ rsp + 0x100 ]; TMP = x302
mov [ r11 + 0x38 ], r15; out1[7] = TMP
sar  bl, 1
adcx r12, rdx
mov r15, [ rsp + 0xd0 ]; x260, copying x254 here, cause x254 is needed in a reg for other than x260, namely all: , x260, size: 1
and r15, r8; x260 <- x254&0x3ffffffffffffff
mov r14, r12; x308, copying x305 here, cause x305 is needed in a reg for other than x308, namely all: , x308, x307, size: 2
shr r14, 57; x308 <- x305>> 57
mov rbx, rcx; x307, copying x303 here, cause x303 is needed in a reg for other than x307, namely all: , x309, x307, size: 2
shrd rbx, r12, 57; x307 <- x305||x303 >> 57
mov r10, [ rsp + 0x58 ]; x125, copying x119 here, cause x119 is needed in a reg for other than x125, namely all: , x125, size: 1
and r10, r8; x125 <- x119&0x3ffffffffffffff
mov rdx, 0x1ffffffffffffff ; moving imm to reg
and rcx, rdx; x309 <- x303&0x1ffffffffffffff
adox rbx, r10
mov r12, 0x0 ; moving imm to reg
adox r14, r12
mov r10, rbx; x313, copying x310 here, cause x310 is needed in a reg for other than x313, namely all: , x313, x314, size: 2
shrd r10, r14, 58; x313 <- x312||x310 >> 58
mov [ r11 + 0x40 ], rcx; out1[8] = x309
and rbx, r8; x314 <- x310&0x3ffffffffffffff
lea r10, [ r10 + r15 ]
mov r15, r10; x317, copying x315 here, cause x315 is needed in a reg for other than x317, namely all: , x316, x317, size: 2
and r15, r8; x317 <- x315&0x3ffffffffffffff
shr r10, 58; x316 <- x315>> 58
and r13, r8; x295 <- x289&0x3ffffffffffffff
add r10, [ rsp + 0xc8 ]
and r9, r8; x274 <- x268&0x3ffffffffffffff
mov [ r11 + 0x30 ], r13; out1[6] = x295
mov [ r11 + 0x8 ], r15; out1[1] = x317
mov [ r11 + 0x18 ], r9; out1[3] = x274
and rax, r8; x281 <- x275&0x3ffffffffffffff
mov [ r11 + 0x10 ], r10; out1[2] = x318
mov [ r11 + 0x28 ], rbp; out1[5] = x288
mov [ r11 + 0x20 ], rax; out1[4] = x281
mov [ r11 + 0x0 ], rbx; out1[0] = x314
mov rbx, [ rsp + 0x108 ]; restoring from stack
mov rbp, [ rsp + 0x110 ]; restoring from stack
mov r12, [ rsp + 0x118 ]; restoring from stack
mov r13, [ rsp + 0x120 ]; restoring from stack
mov r14, [ rsp + 0x128 ]; restoring from stack
mov r15, [ rsp + 0x130 ]; restoring from stack
add rsp, 0x138 
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; clocked at 2200 MHz
; first cyclecount 121.41, best 87.78, lastGood 90.44
; seed 2001410703584519 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1224091 ms / 60000 runs=> 20.401516666666666ms/run
; Time spent for assembling and measureing (initial batch_size=97, initial num_batches=101): 142079 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.11606898506728666
; number reverted permutation/ tried permutation: 23138 / 29945 =77.268%
; number reverted decision/ tried decision: 21176 / 30056 =70.455%
