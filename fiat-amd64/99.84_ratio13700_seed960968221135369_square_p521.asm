SECTION .text
	GLOBAL square_p521
square_p521:
sub rsp, 0x120 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0xf0 ], rbx; saving to stack
mov [ rsp + 0xf8 ], rbp; saving to stack
mov [ rsp + 0x100 ], r12; saving to stack
mov [ rsp + 0x108 ], r13; saving to stack
mov [ rsp + 0x110 ], r14; saving to stack
mov [ rsp + 0x118 ], r15; saving to stack
mov rax, [ rsi + 0x40 ]; load m64 x1 to register64
imul r10, rax, 0x2; x2 <- x1 * 0x2
imul r10, r10, 0x2; x10001 <- x2 * 0x2
mov r11, [ rsi + 0x38 ]; load m64 x4 to register64
imul rbx, r11, 0x2; x5 <- x4 * 0x2
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbp, r12, r10; x74, x73<- arg1[1] * x10001
mov r13, [ rsi + 0x30 ]; load m64 x7 to register64
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r14, r15, [ rsi + 0x0 ]; x106, x105<- arg1[0] * arg1[0]
imul rdx, r13, 0x2; x8 <- x7 * 0x2
mov rcx, [ rsi + 0x28 ]; load m64 x10 to register64
imul rdx, rdx, 0x2; x10005 <- x8 * 0x2
imul r8, rcx, 0x2; x11 <- x10 * 0x2
imul r8, r8, 0x2; x10007 <- x11 * 0x2
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r9, rdi, [ rsi + 0x18 ]; x52, x51<- arg1[3] * x10005
imul rbx, rbx, 0x2; x10003 <- x5 * 0x2
mov [ rsp + 0x8 ], rax; spilling x1 to mem
mov rax, rdx; preserving value of x10005 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x10 ], r11; spilling x4 to mem
mov [ rsp + 0x18 ], r10; spilling x10001 to mem
mulx r11, r10, rbx; x62, x61<- arg1[2] * x10003
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x20 ], r14; spilling x106 to mem
mulx r8, r14, r8; x44, x43<- arg1[4] * x10007
add r14, rdi; could be done better, if r0 has been u8 as well
adcx r9, r8
add r14, r10; could be done better, if r0 has been u8 as well
adcx r11, r9
add r14, r12; could be done better, if r0 has been u8 as well
mov rdx, rax; x10005 to rdx
mulx rax, r12, [ rsi + 0x20 ]; x42, x41<- arg1[4] * x10005
adcx rbp, r11
add r14, r15; could be done better, if r0 has been u8 as well
adcx rbp, [ rsp + 0x20 ]
imul r15, [ rsi + 0x8 ], 0x2; x16 <- arg1[1] * 0x2
mov rdi, r14; x123, copying x119 here, cause x119 is needed in a reg for other than x123, namely all: , x125, x123, size: 2
shrd rdi, rbp, 58; x123 <- x121||x119 >> 58
mov r10, rdx; preserving value of x10005 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r15, r8, r15; x104, x103<- arg1[0] * x16
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r9, r11, rbx; x50, x49<- arg1[3] * x10003
imul rcx, rcx, 0x2; x10006 <- x10 * 0x2
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x28 ], r13; spilling x7 to mem
mulx rcx, r13, rcx; x36, x35<- arg1[5] * x10006
test al, al
adox r13, r12
adcx r13, r11
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r12, r11, [ rsp + 0x18 ]; x60, x59<- arg1[2] * x10001
adox rax, rcx
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, r11
adcx r9, rax
clc;
adcx r13, r8
adox r12, r9
adcx r15, r12
shr rbp, 58; x124 <- x121>> 58
imul r8, [ rsi + 0x10 ], 0x2; x15 <- arg1[2] * 0x2
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mulx r10, rcx, r10; x34, x33<- arg1[5] * x10005
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r11, rax, [ rsi + 0x8 ]; x88, x87<- arg1[1] * arg1[1]
add r13, rdi; could be done better, if r0 has been u8 as well
adcx rbp, r15
mov rdx, r13; x258, copying x254 here, cause x254 is needed in a reg for other than x258, namely all: , x258, x260, size: 2
shrd rdx, rbp, 58; x258 <- x256||x254 >> 58
mov rdi, rdx; preserving value of x258 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r9, r12, rbx; x40, x39<- arg1[4] * x10003
test al, al
adox rcx, r12
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r15, r12, [ rsp + 0x18 ]; x48, x47<- arg1[3] * x10001
mov rdx, r8; x15 to rdx
mov [ rsp + 0x30 ], r11; spilling x88 to mem
mulx r8, r11, [ rsi + 0x0 ]; x102, x101<- arg1[0] * x15
adcx rcx, r12
setc r12b; spill CF x227 to reg (r12)
clc;
adcx rcx, rax
setc al; spill CF x231 to reg (rax)
clc;
adcx rcx, r11
setc r11b; spill CF x235 to reg (r11)
clc;
adcx rcx, rdi
adox r9, r10
setc r10b; spill CF x262 to reg (r10)
imul rdi, [ rsi + 0x18 ], 0x2; x14 <- arg1[3] * 0x2
sar  r12b, 1
adcx r15, r9
shr rbp, 58; x259 <- x256>> 58
sar  al, 1
adcx r15, [ rsp + 0x30 ]
imul r12, [ rsi + 0x40 ], 0x2; x3 <- arg1[8] * 0x2
sar  r11b, 1
adcx r8, r15
mov rax, 0x3ffffffffffffff ; moving imm to reg
mov r11, rcx; x267, copying x261 here, cause x261 is needed in a reg for other than x267, namely all: , x265, x267, size: 2
and r11, rax; x267 <- x261&0x3ffffffffffffff
mov r9, rdx; preserving value of x15 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r15, rax, [ rsp + 0x18 ]; x38, x37<- arg1[4] * x10001
sar  r10b, 1
adcx rbp, r8
shrd rcx, rbp, 58; x265 <- x263||x261 >> 58
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r9, r10, r9; x86, x85<- arg1[1] * x15
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x38 ], r11; spilling x267 to mem
mulx r8, r11, rdi; x100, x99<- arg1[0] * x14
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x40 ], r12; spilling x3 to mem
mov [ rsp + 0x48 ], r8; spilling x100 to mem
mulx r12, r8, rbx; x32, x31<- arg1[5] * x10003
imul rdx, [ rsp + 0x28 ], 0x2; x10004 <- x7 * 0x2
mov [ rsp + 0x50 ], r14; spilling x119 to mem
mulx rdx, r14, [ rsi + 0x30 ]; x28, x27<- arg1[6] * x10004
add r14, r8; could be done better, if r0 has been u8 as well
adcx r12, rdx
add r14, rax; could be done better, if r0 has been u8 as well
adcx r15, r12
xor rax, rax
adox r14, r10
adcx r14, r11
setc r10b; spill CF x219 to reg (r10)
clc;
adcx r14, rcx
adox r9, r15
setc cl; spill CF x269 to reg (rcx)
shr rbp, 58; x266 <- x263>> 58
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r11, r8, rdi; x84, x83<- arg1[1] * x14
mov rdx, [ rsp + 0x18 ]; x10001 to rdx
mulx r12, r15, [ rsi + 0x28 ]; x30, x29<- arg1[5] * x10001
imul rax, [ rsi + 0x20 ], 0x2; x13 <- arg1[4] * 0x2
mov [ rsp + 0x58 ], r11; spilling x84 to mem
mov r11, rdx; preserving value of x10001 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x60 ], r8; spilling x83 to mem
mov [ rsp + 0x68 ], r12; spilling x30 to mem
mulx r8, r12, [ rsi + 0x10 ]; x72, x71<- arg1[2] * arg1[2]
sar  r10b, 1
adcx r9, [ rsp + 0x48 ]
sar  cl, 1
adcx rbp, r9
mov rdx, r14; x272, copying x268 here, cause x268 is needed in a reg for other than x272, namely all: , x274, x272, size: 2
shrd rdx, rbp, 58; x272 <- x270||x268 >> 58
mov r10, rdx; preserving value of x272 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx rcx, r9, rax; x98, x97<- arg1[0] * x13
mov rdx, rbx; x10003 to rdx
mulx rdx, rbx, [ rsi + 0x30 ]; x26, x25<- arg1[6] * x10003
add rbx, r15; could be done better, if r0 has been u8 as well
adcx rdx, [ rsp + 0x68 ]
shr rbp, 58; x273 <- x270>> 58
add rbx, r12; could be done better, if r0 has been u8 as well
adcx r8, rdx
add rbx, [ rsp + 0x60 ]; could be done better, if r0 has been u8 as well
adcx r8, [ rsp + 0x58 ]
imul r15, [ rsi + 0x28 ], 0x2; x12 <- arg1[5] * 0x2
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x70 ], r15; spilling x12 to mem
mulx r12, r15, r11; x24, x23<- arg1[6] * x10001
test al, al
adox rbx, r9
adox rcx, r8
adcx rbx, r10
adcx rbp, rcx
mov rdx, rax; x13 to rdx
mulx rax, r10, [ rsi + 0x8 ]; x82, x81<- arg1[1] * x13
mov r9, rdx; preserving value of x13 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r8, rcx, [ rsp + 0x70 ]; x96, x95<- arg1[0] * x12
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x78 ], r8; spilling x96 to mem
mulx rdi, r8, rdi; x70, x69<- arg1[2] * x14
imul rdx, [ rsp + 0x10 ], 0x2; x10002 <- x4 * 0x2
mov [ rsp + 0x80 ], rcx; spilling x95 to mem
mulx rdx, rcx, [ rsi + 0x38 ]; x22, x21<- arg1[7] * x10002
mov [ rsp + 0x88 ], rax; spilling x82 to mem
mov rax, rbx; x279, copying x275 here, cause x275 is needed in a reg for other than x279, namely all: , x281, x279, size: 2
shrd rax, rbp, 58; x279 <- x277||x275 >> 58
test al, al
adox rcx, r15
adox r12, rdx
adcx rcx, r8
adcx rdi, r12
test al, al
adox rcx, r10
adox rdi, [ rsp + 0x88 ]
adcx rcx, [ rsp + 0x80 ]
adcx rdi, [ rsp + 0x78 ]
xor r15, r15
adox rcx, rax
seto r10b; spill OF x283 to reg (r10)
imul r8, [ rsi + 0x30 ], 0x2; x9 <- arg1[6] * 0x2
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rax, r12, [ rsp + 0x70 ]; x80, x79<- arg1[1] * x12
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x90 ], rax; spilling x80 to mem
mulx r15, rax, r9; x68, x67<- arg1[2] * x13
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x98 ], r15; spilling x68 to mem
mov [ rsp + 0xa0 ], r12; spilling x79 to mem
mulx r15, r12, [ rsi + 0x18 ]; x58, x57<- arg1[3] * arg1[3]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0xa8 ], r15; spilling x58 to mem
mov [ rsp + 0xb0 ], rax; spilling x67 to mem
mulx r15, rax, r8; x94, x93<- arg1[0] * x9
shr rbp, 58; x280 <- x277>> 58
mov rdx, r11; x10001 to rdx
mulx rdx, r11, [ rsi + 0x38 ]; x20, x19<- arg1[7] * x10001
sar  r10b, 1
adcx rbp, rdi
mov rdi, rcx; x286, copying x282 here, cause x282 is needed in a reg for other than x286, namely all: , x288, x286, size: 2
shrd rdi, rbp, 58; x286 <- x284||x282 >> 58
xor r10, r10
adox r11, r12
adcx r11, [ rsp + 0xb0 ]
setc r12b; spill CF x163 to reg (r12)
clc;
adcx r11, [ rsp + 0xa0 ]
mov [ rsp + 0xb8 ], r13; spilling x254 to mem
setc r13b; spill CF x167 to reg (r13)
clc;
adcx r11, rax
setc al; spill CF x171 to reg (rax)
clc;
adcx r11, rdi
adox rdx, [ rsp + 0xa8 ]
setc dil; spill CF x290 to reg (rdi)
imul r10, [ rsi + 0x38 ], 0x2; x6 <- arg1[7] * 0x2
sar  r12b, 1
adcx rdx, [ rsp + 0x98 ]
sar  r13b, 1
adcx rdx, [ rsp + 0x90 ]
sar  al, 1
adcx r15, rdx
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r9, r12, r9; x56, x55<- arg1[3] * x13
shr rbp, 58; x287 <- x284>> 58
mov rdx, r8; x9 to rdx
mulx r8, r13, [ rsi + 0x8 ]; x78, x77<- arg1[1] * x9
imul rax, [ rsp + 0x8 ], 0x2; x10000 <- x1 * 0x2
sar  dil, 1
adcx rbp, r15
mov rdi, r11; x293, copying x289 here, cause x289 is needed in a reg for other than x293, namely all: , x295, x293, size: 2
shrd rdi, rbp, 58; x293 <- x291||x289 >> 58
mov r15, rdx; preserving value of x9 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0xc0 ], r8; spilling x78 to mem
mov [ rsp + 0xc8 ], rdi; spilling x293 to mem
mulx r8, rdi, r10; x92, x91<- arg1[0] * x6
mov rdx, [ rsi + 0x40 ]; arg1[8] to rdx
mov [ rsp + 0xd0 ], r8; spilling x92 to mem
mulx rdx, r8, rax; x18, x17<- arg1[8] * x10000
add r8, r12; could be done better, if r0 has been u8 as well
adcx r9, rdx
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r12, rax, [ rsp + 0x70 ]; x66, x65<- arg1[2] * x12
xor rdx, rdx
adox r8, rax
adcx r8, r13
setc r13b; spill CF x151 to reg (r13)
clc;
adcx r8, rdi
setc dil; spill CF x155 to reg (rdi)
clc;
adcx r8, [ rsp + 0xc8 ]
setc al; spill CF x297 to reg (rax)
seto dl; spill OF x147 to reg (rdx)
shr rbp, 58; x294 <- x291>> 58
sar  dl, 1
adcx r12, r9
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r15, r9, r15; x64, x63<- arg1[2] * x9
sar  r13b, 1
adcx r12, [ rsp + 0xc0 ]
sar  dil, 1
adcx r12, [ rsp + 0xd0 ]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r13, rdi, [ rsp + 0x40 ]; x90, x89<- arg1[0] * x3
sar  al, 1
adcx rbp, r12
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r10, rax, r10; x76, x75<- arg1[1] * x6
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0xd8 ], r13; spilling x90 to mem
mulx r12, r13, [ rsi + 0x20 ]; x46, x45<- arg1[4] * arg1[4]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0xe0 ], r10; spilling x76 to mem
mov [ rsp + 0xe8 ], rdi; spilling x89 to mem
mulx r10, rdi, [ rsp + 0x70 ]; x54, x53<- arg1[3] * x12
mov rdx, r8; x300, copying x296 here, cause x296 is needed in a reg for other than x300, namely all: , x302, x300, size: 2
shrd rdx, rbp, 58; x300 <- x298||x296 >> 58
add r13, rdi; could be done better, if r0 has been u8 as well
adcx r10, r12
add r13, r9; could be done better, if r0 has been u8 as well
adcx r15, r10
mov r9, 0x3ffffffffffffff ; moving imm to reg
mov r12, [ rsp + 0x50 ]; x125, copying x119 here, cause x119 is needed in a reg for other than x125, namely all: , x125, size: 1
and r12, r9; x125 <- x119&0x3ffffffffffffff
adox r13, rax
seto al; spill OF x135 to reg (rax)
and r14, r9; x274 <- x268&0x3ffffffffffffff
adox r13, [ rsp + 0xe8 ]
adcx r13, rdx
setc dil; spill CF x304 to reg (rdi)
seto dl; spill OF x139 to reg (rdx)
shr rbp, 58; x301 <- x298>> 58
and r8, r9; x302 <- x296&0x3ffffffffffffff
sar  al, 1
adcx r15, [ rsp + 0xe0 ]
sar  dl, 1
adcx r15, [ rsp + 0xd8 ]
sar  dil, 1
adcx rbp, r15
mov r10, 0x1ffffffffffffff ; moving imm to reg
mov rax, r13; x309, copying x303 here, cause x303 is needed in a reg for other than x309, namely all: , x307, x309, size: 2
and rax, r10; x309 <- x303&0x1ffffffffffffff
mov rdx, rbp; x308, copying x305 here, cause x305 is needed in a reg for other than x308, namely all: , x308, x307, size: 2
shr rdx, 57; x308 <- x305>> 57
shrd r13, rbp, 57; x307 <- x305||x303 >> 57
mov rdi, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rdi + 0x18 ], r14; out1[3] = x274
xor r15, r15
adox r13, r12
adox rdx, r15
mov [ rdi + 0x40 ], rax; out1[8] = x309
mov r12, [ rsp + 0xb8 ]; x260, copying x254 here, cause x254 is needed in a reg for other than x260, namely all: , x260, size: 1
and r12, r9; x260 <- x254&0x3ffffffffffffff
and rbx, r9; x281 <- x275&0x3ffffffffffffff
mov rbp, r13; x313, copying x310 here, cause x310 is needed in a reg for other than x313, namely all: , x313, x314, size: 2
shrd rbp, rdx, 58; x313 <- x312||x310 >> 58
lea rbp, [ rbp + r12 ]
mov r14, rbp; x316, copying x315 here, cause x315 is needed in a reg for other than x316, namely all: , x316, x317, size: 2
shr r14, 58; x316 <- x315>> 58
add r14, [ rsp + 0x38 ]
and r11, r9; x295 <- x289&0x3ffffffffffffff
and rbp, r9; x317 <- x315&0x3ffffffffffffff
and rcx, r9; x288 <- x282&0x3ffffffffffffff
mov [ rdi + 0x20 ], rbx; out1[4] = x281
mov [ rdi + 0x30 ], r11; out1[6] = x295
mov [ rdi + 0x28 ], rcx; out1[5] = x288
mov [ rdi + 0x10 ], r14; out1[2] = x318
and r13, r9; x314 <- x310&0x3ffffffffffffff
mov [ rdi + 0x38 ], r8; out1[7] = x302
mov [ rdi + 0x8 ], rbp; out1[1] = x317
mov [ rdi + 0x0 ], r13; out1[0] = x314
mov rbx, [ rsp + 0xf0 ]; restoring from stack
mov rbp, [ rsp + 0xf8 ]; restoring from stack
mov r12, [ rsp + 0x100 ]; restoring from stack
mov r13, [ rsp + 0x108 ]; restoring from stack
mov r14, [ rsp + 0x110 ]; restoring from stack
mov r15, [ rsp + 0x118 ]; restoring from stack
add rsp, 0x120 
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; clocked at 2600 MHz
; first cyclecount 116.49, best 98.5, lastGood 99.83783783783784
; seed 960968221135369 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1872892 ms / 60000 runs=> 31.214866666666666ms/run
; Time spent for assembling and measureing (initial batch_size=72, initial num_batches=101): 183570 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.09801419409127703
; number reverted permutation/ tried permutation: 24222 / 30066 =80.563%
; number reverted decision/ tried decision: 23144 / 29935 =77.314%