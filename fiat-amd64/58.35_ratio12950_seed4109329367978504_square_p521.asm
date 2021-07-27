SECTION .text
	GLOBAL square_p521
square_p521:
sub rsp, 0x128 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0xf8 ], rbx; saving to stack
mov [ rsp + 0x100 ], rbp; saving to stack
mov [ rsp + 0x108 ], r12; saving to stack
mov [ rsp + 0x110 ], r13; saving to stack
mov [ rsp + 0x118 ], r14; saving to stack
mov [ rsp + 0x120 ], r15; saving to stack
mov rax, [ rsi + 0x40 ]; load m64 x1 to register64
imul r10, rax, 0x2; x2 <- x1 * 0x2
mov r11, [ rsi + 0x38 ]; load m64 x4 to register64
imul r10, r10, 0x2; x10001 <- x2 * 0x2
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbx, rbp, r10; x74, x73<- arg1[1] * x10001
imul r12, r11, 0x2; x5 <- x4 * 0x2
imul r12, r12, 0x2; x10003 <- x5 * 0x2
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r13, r14, [ rsi + 0x0 ]; x106, x105<- arg1[0] * arg1[0]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r15, rcx, r12; x62, x61<- arg1[2] * x10003
mov rdx, [ rsi + 0x30 ]; load m64 x7 to register64
imul r8, rdx, 0x2; x8 <- x7 * 0x2
mov r9, [ rsi + 0x28 ]; load m64 x10 to register64
imul r8, r8, 0x2; x10005 <- x8 * 0x2
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov rdi, rdx; preserving value of x7 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x8 ], rax; spilling x1 to mem
mov [ rsp + 0x10 ], r11; spilling x4 to mem
mulx rax, r11, r8; x52, x51<- arg1[3] * x10005
imul rdx, r9, 0x2; x11 <- x10 * 0x2
imul rdx, rdx, 0x2; x10007 <- x11 * 0x2
mov [ rsp + 0x18 ], r10; spilling x10001 to mem
mulx rdx, r10, [ rsi + 0x20 ]; x44, x43<- arg1[4] * x10007
add r10, r11; could be done better, if r0 has been u8 as well
adcx rax, rdx
add r10, rcx; could be done better, if r0 has been u8 as well
adcx r15, rax
xor rcx, rcx
adox r10, rbp
adox rbx, r15
adcx r10, r14
adcx r13, rbx
imul rbp, [ rsi + 0x8 ], 0x2; x16 <- arg1[1] * 0x2
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rbp, r14, rbp; x104, x103<- arg1[0] * x16
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r11, rax, r12; x50, x49<- arg1[3] * x10003
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r15, rbx, r8; x42, x41<- arg1[4] * x10005
imul r9, r9, 0x2; x10006 <- x10 * 0x2
mov rdx, r10; x123, copying x119 here, cause x119 is needed in a reg for other than x123, namely all: , x125, x123, size: 2
shrd rdx, r13, 58; x123 <- x121||x119 >> 58
mov rcx, rdx; preserving value of x123 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x20 ], rdi; spilling x7 to mem
mov [ rsp + 0x28 ], rbp; spilling x104 to mem
mulx rdi, rbp, [ rsp + 0x18 ]; x60, x59<- arg1[2] * x10001
mov rdx, r9; x10006 to rdx
mulx rdx, r9, [ rsi + 0x28 ]; x36, x35<- arg1[5] * x10006
test al, al
adox r9, rbx
adox r15, rdx
adcx r9, rax
mov rax, -0x2 ; moving imm to reg
inc rax; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r9, rbp
setc bl; spill CF x243 to reg (rbx)
clc;
adcx r9, r14
setc r14b; spill CF x251 to reg (r14)
clc;
adcx r9, rcx
setc cl; spill CF x255 to reg (rcx)
seto bpl; spill OF x247 to reg (rbp)
imul rdx, [ rsi + 0x10 ], 0x2; x15 <- arg1[2] * 0x2
sar  bl, 1
adcx r11, r15
sar  bpl, 1
adcx rdi, r11
sar  r14b, 1
adcx rdi, [ rsp + 0x28 ]
mulx r15, rbx, [ rsi + 0x0 ]; x102, x101<- arg1[0] * x15
shr r13, 58; x124 <- x121>> 58
sar  cl, 1
adcx r13, rdi
mov rbp, r9; x258, copying x254 here, cause x254 is needed in a reg for other than x258, namely all: , x260, x258, size: 2
shrd rbp, r13, 58; x258 <- x256||x254 >> 58
mov r14, rdx; preserving value of x15 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx rcx, r11, r12; x40, x39<- arg1[4] * x10003
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rdi, rax, [ rsp + 0x18 ]; x48, x47<- arg1[3] * x10001
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x30 ], r15; spilling x102 to mem
mov [ rsp + 0x38 ], rdi; spilling x48 to mem
mulx r15, rdi, [ rsi + 0x8 ]; x88, x87<- arg1[1] * arg1[1]
mov rdx, r8; x10005 to rdx
mulx rdx, r8, [ rsi + 0x28 ]; x34, x33<- arg1[5] * x10005
mov [ rsp + 0x40 ], r15; spilling x88 to mem
imul r15, [ rsi + 0x40 ], 0x2; x3 <- arg1[8] * 0x2
add r8, r11; could be done better, if r0 has been u8 as well
adcx rcx, rdx
xor r11, r11
adox r8, rax
adcx r8, rdi
setc al; spill CF x231 to reg (rax)
clc;
adcx r8, rbx
setc bl; spill CF x235 to reg (rbx)
clc;
adcx r8, rbp
adox rcx, [ rsp + 0x38 ]
setc bpl; spill CF x262 to reg (rbp)
shr r13, 58; x259 <- x256>> 58
imul rdi, [ rsi + 0x18 ], 0x2; x14 <- arg1[3] * 0x2
mov rdx, 0x3ffffffffffffff ; moving imm to reg
mov r11, r8; x267, copying x261 here, cause x261 is needed in a reg for other than x267, namely all: , x267, x265, size: 2
and r11, rdx; x267 <- x261&0x3ffffffffffffff
sar  al, 1
adcx rcx, [ rsp + 0x40 ]
mov rax, rdx; preserving value of 0x3ffffffffffffff into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x48 ], r11; spilling x267 to mem
mov [ rsp + 0x50 ], r15; spilling x3 to mem
mulx r11, r15, [ rsp + 0x18 ]; x38, x37<- arg1[4] * x10001
sar  bl, 1
adcx rcx, [ rsp + 0x30 ]
sar  bpl, 1
adcx r13, rcx
shrd r8, r13, 58; x265 <- x263||x261 >> 58
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r14, rbx, r14; x86, x85<- arg1[1] * x15
shr r13, 58; x266 <- x263>> 58
and r10, rax; x125 <- x119&0x3ffffffffffffff
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rbp, rcx, rdi; x100, x99<- arg1[0] * x14
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x58 ], r10; spilling x125 to mem
mulx rax, r10, r12; x32, x31<- arg1[5] * x10003
imul rdx, [ rsp + 0x20 ], 0x2; x10004 <- x7 * 0x2
mov [ rsp + 0x60 ], r13; spilling x266 to mem
mulx rdx, r13, [ rsi + 0x30 ]; x28, x27<- arg1[6] * x10004
test al, al
adox r13, r10
adox rax, rdx
adcx r13, r15
adcx r11, rax
xor r15, r15
adox r13, rbx
adox r14, r11
adcx r13, rcx
adcx rbp, r14
add r13, r8; could be done better, if r0 has been u8 as well
adcx rbp, [ rsp + 0x60 ]
mov r8, r13; x272, copying x268 here, cause x268 is needed in a reg for other than x272, namely all: , x274, x272, size: 2
shrd r8, rbp, 58; x272 <- x270||x268 >> 58
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mulx rbx, rcx, [ rsp + 0x18 ]; x30, x29<- arg1[5] * x10001
imul rdx, [ rsi + 0x20 ], 0x2; x13 <- arg1[4] * 0x2
mulx r10, rax, [ rsi + 0x0 ]; x98, x97<- arg1[0] * x13
mov r11, rdx; preserving value of x13 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r14, r15, [ rsi + 0x10 ]; x72, x71<- arg1[2] * arg1[2]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x68 ], r10; spilling x98 to mem
mov [ rsp + 0x70 ], r14; spilling x72 to mem
mulx r10, r14, rdi; x84, x83<- arg1[1] * x14
mov rdx, r12; x10003 to rdx
mulx rdx, r12, [ rsi + 0x30 ]; x26, x25<- arg1[6] * x10003
test al, al
adox r12, rcx
adcx r12, r15
setc cl; spill CF x195 to reg (rcx)
clc;
adcx r12, r14
setc r15b; spill CF x199 to reg (r15)
clc;
adcx r12, rax
setc al; spill CF x203 to reg (rax)
clc;
adcx r12, r8
adox rbx, rdx
setc r8b; spill CF x276 to reg (r8)
shr rbp, 58; x273 <- x270>> 58
sar  cl, 1
adcx rbx, [ rsp + 0x70 ]
sar  r15b, 1
adcx r10, rbx
sar  al, 1
adcx r10, [ rsp + 0x68 ]
sar  r8b, 1
adcx rbp, r10
mov r14, r12; x279, copying x275 here, cause x275 is needed in a reg for other than x279, namely all: , x281, x279, size: 2
shrd r14, rbp, 58; x279 <- x277||x275 >> 58
imul rdx, [ rsi + 0x28 ], 0x2; x12 <- arg1[5] * 0x2
mulx rcx, r15, [ rsi + 0x0 ]; x96, x95<- arg1[0] * x12
mov rax, rdx; preserving value of x12 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r8, rbx, r11; x82, x81<- arg1[1] * x13
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x78 ], rcx; spilling x96 to mem
mulx r10, rcx, [ rsp + 0x18 ]; x24, x23<- arg1[6] * x10001
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x80 ], r8; spilling x82 to mem
mulx rdi, r8, rdi; x70, x69<- arg1[2] * x14
imul rdx, [ rsp + 0x10 ], 0x2; x10002 <- x4 * 0x2
mov [ rsp + 0x88 ], rdi; spilling x70 to mem
mulx rdx, rdi, [ rsi + 0x38 ]; x22, x21<- arg1[7] * x10002
test al, al
adox rdi, rcx
adcx rdi, r8
setc cl; spill CF x179 to reg (rcx)
clc;
adcx rdi, rbx
setc bl; spill CF x183 to reg (rbx)
clc;
adcx rdi, r15
setc r15b; spill CF x187 to reg (r15)
clc;
adcx rdi, r14
adox r10, rdx
setc r14b; spill CF x283 to reg (r14)
imul r8, [ rsi + 0x30 ], 0x2; x9 <- arg1[6] * 0x2
sar  cl, 1
adcx r10, [ rsp + 0x88 ]
sar  bl, 1
adcx r10, [ rsp + 0x80 ]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rcx, rbx, [ rsi + 0x18 ]; x58, x57<- arg1[3] * arg1[3]
sar  r15b, 1
adcx r10, [ rsp + 0x78 ]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x90 ], rcx; spilling x58 to mem
mulx r15, rcx, r11; x68, x67<- arg1[2] * x13
shr rbp, 58; x280 <- x277>> 58
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x98 ], r15; spilling x68 to mem
mov [ rsp + 0xa0 ], rcx; spilling x67 to mem
mulx r15, rcx, rax; x80, x79<- arg1[1] * x12
sar  r14b, 1
adcx rbp, r10
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx r14, r10, [ rsp + 0x18 ]; x20, x19<- arg1[7] * x10001
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0xa8 ], r9; spilling x254 to mem
mov [ rsp + 0xb0 ], r15; spilling x80 to mem
mulx r9, r15, r8; x94, x93<- arg1[0] * x9
mov rdx, rdi; x286, copying x282 here, cause x282 is needed in a reg for other than x286, namely all: , x286, x288, size: 2
shrd rdx, rbp, 58; x286 <- x284||x282 >> 58
test al, al
adox r10, rbx
adcx r10, [ rsp + 0xa0 ]
setc bl; spill CF x163 to reg (rbx)
clc;
adcx r10, rcx
setc cl; spill CF x167 to reg (rcx)
clc;
adcx r10, r15
setc r15b; spill CF x171 to reg (r15)
clc;
adcx r10, rdx
adox r14, [ rsp + 0x90 ]
setc dl; spill CF x290 to reg (rdx)
shr rbp, 58; x287 <- x284>> 58
sar  bl, 1
adcx r14, [ rsp + 0x98 ]
sar  cl, 1
adcx r14, [ rsp + 0xb0 ]
sar  r15b, 1
adcx r9, r14
imul rbx, [ rsp + 0x8 ], 0x2; x10000 <- x1 * 0x2
sar  dl, 1
adcx rbp, r9
mov rcx, r10; x293, copying x289 here, cause x289 is needed in a reg for other than x293, namely all: , x295, x293, size: 2
shrd rcx, rbp, 58; x293 <- x291||x289 >> 58
imul r15, [ rsi + 0x38 ], 0x2; x6 <- arg1[7] * 0x2
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r14, r9, r8; x78, x77<- arg1[1] * x9
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0xb8 ], r14; spilling x78 to mem
mov [ rsp + 0xc0 ], rcx; spilling x293 to mem
mulx r14, rcx, rax; x66, x65<- arg1[2] * x12
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0xc8 ], r14; spilling x66 to mem
mov [ rsp + 0xd0 ], r9; spilling x77 to mem
mulx r14, r9, r15; x92, x91<- arg1[0] * x6
mov rdx, r11; x13 to rdx
mulx rdx, r11, [ rsi + 0x18 ]; x56, x55<- arg1[3] * x13
xchg rdx, rbx; x10000, swapping with x56, which is currently in rdx
mov [ rsp + 0xd8 ], r14; spilling x92 to mem
mulx rdx, r14, [ rsi + 0x40 ]; x18, x17<- arg1[8] * x10000
test al, al
adox r14, r11
adcx r14, rcx
setc cl; spill CF x147 to reg (rcx)
clc;
adcx r14, [ rsp + 0xd0 ]
setc r11b; spill CF x151 to reg (r11)
clc;
adcx r14, r9
setc r9b; spill CF x155 to reg (r9)
clc;
adcx r14, [ rsp + 0xc0 ]
adox rbx, rdx
setc dl; spill CF x297 to reg (rdx)
shr rbp, 58; x294 <- x291>> 58
sar  cl, 1
adcx rbx, [ rsp + 0xc8 ]
sar  r11b, 1
adcx rbx, [ rsp + 0xb8 ]
sar  r9b, 1
adcx rbx, [ rsp + 0xd8 ]
mov cl, dl; preserving value of x297 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r15, r11, r15; x76, x75<- arg1[1] * x6
sar  cl, 1
adcx rbp, rbx
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r9, rcx, [ rsp + 0x50 ]; x90, x89<- arg1[0] * x3
mov rdx, r14; x300, copying x296 here, cause x296 is needed in a reg for other than x300, namely all: , x300, x302, size: 2
shrd rdx, rbp, 58; x300 <- x298||x296 >> 58
mov rbx, rdx; preserving value of x300 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0xe0 ], r9; spilling x90 to mem
mulx r8, r9, r8; x64, x63<- arg1[2] * x9
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0xe8 ], r15; spilling x76 to mem
mov [ rsp + 0xf0 ], r8; spilling x64 to mem
mulx r15, r8, [ rsi + 0x20 ]; x46, x45<- arg1[4] * arg1[4]
mov rdx, rax; x12 to rdx
mulx rdx, rax, [ rsi + 0x18 ]; x54, x53<- arg1[3] * x12
test al, al
adox r8, rax
adcx r8, r9
setc r9b; spill CF x131 to reg (r9)
clc;
adcx r8, r11
setc r11b; spill CF x135 to reg (r11)
clc;
adcx r8, rcx
setc cl; spill CF x139 to reg (rcx)
clc;
adcx r8, rbx
adox rdx, r15
movzx r9, r9b
lea rdx, [ r9 + rdx ]
mov r9, [ rsp + 0xf0 ]
lea rdx, [r9+rdx]
setc bl; spill CF x304 to reg (rbx)
shr rbp, 58; x301 <- x298>> 58
sar  r11b, 1
adcx rdx, [ rsp + 0xe8 ]
sar  cl, 1
adcx rdx, [ rsp + 0xe0 ]
sar  bl, 1
adcx rbp, rdx
mov r15, r8; x307, copying x303 here, cause x303 is needed in a reg for other than x307, namely all: , x307, x309, size: 2
shrd r15, rbp, 57; x307 <- x305||x303 >> 57
shr rbp, 57; x308 <- x305>> 57
xor rax, rax
adox r15, [ rsp + 0x58 ]
adox rbp, rax
mov r9, 0x3ffffffffffffff ; moving imm to reg
mov r11, [ rsp + 0xa8 ]; x260, copying x254 here, cause x254 is needed in a reg for other than x260, namely all: , x260, size: 1
and r11, r9; x260 <- x254&0x3ffffffffffffff
mov rcx, r15; x313, copying x310 here, cause x310 is needed in a reg for other than x313, namely all: , x313, x314, size: 2
shrd rcx, rbp, 58; x313 <- x312||x310 >> 58
lea rcx, [ rcx + r11 ]
mov rbx, rcx; x316, copying x315 here, cause x315 is needed in a reg for other than x316, namely all: , x316, x317, size: 2
shr rbx, 58; x316 <- x315>> 58
and r12, r9; x281 <- x275&0x3ffffffffffffff
add rbx, [ rsp + 0x48 ]
and r14, r9; x302 <- x296&0x3ffffffffffffff
mov rdx, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rdx + 0x20 ], r12; out1[4] = x281
and r13, r9; x274 <- x268&0x3ffffffffffffff
mov rbp, 0x1ffffffffffffff ; moving imm to reg
and r8, rbp; x309 <- x303&0x1ffffffffffffff
and rdi, r9; x288 <- x282&0x3ffffffffffffff
and r15, r9; x314 <- x310&0x3ffffffffffffff
mov [ rdx + 0x28 ], rdi; out1[5] = x288
mov [ rdx + 0x18 ], r13; out1[3] = x274
mov [ rdx + 0x38 ], r14; out1[7] = x302
mov [ rdx + 0x0 ], r15; out1[0] = x314
mov [ rdx + 0x10 ], rbx; out1[2] = x318
and r10, r9; x295 <- x289&0x3ffffffffffffff
mov [ rdx + 0x40 ], r8; out1[8] = x309
and rcx, r9; x317 <- x315&0x3ffffffffffffff
mov [ rdx + 0x30 ], r10; out1[6] = x295
mov [ rdx + 0x8 ], rcx; out1[1] = x317
mov rbx, [ rsp + 0xf8 ]; restoring from stack
mov rbp, [ rsp + 0x100 ]; restoring from stack
mov r12, [ rsp + 0x108 ]; restoring from stack
mov r13, [ rsp + 0x110 ]; restoring from stack
mov r14, [ rsp + 0x118 ]; restoring from stack
mov r15, [ rsp + 0x120 ]; restoring from stack
add rsp, 0x128 
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; clocked at 1600 MHz
; first cyclecount 74.025, best 56.3609022556391, lastGood 58.3515625
; seed 4109329367978504 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1828517 ms / 60000 runs=> 30.475283333333334ms/run
; Time spent for assembling and measureing (initial batch_size=128, initial num_batches=101): 253568 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.13867412772208298
; number reverted permutation/ tried permutation: 25828 / 29927 =86.303%
; number reverted decision/ tried decision: 23640 / 30074 =78.606%