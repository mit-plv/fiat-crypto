SECTION .text
	GLOBAL square_p521
square_p521:
sub rsp, 0x108 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0xd8 ], rbx; saving to stack
mov [ rsp + 0xe0 ], rbp; saving to stack
mov [ rsp + 0xe8 ], r12; saving to stack
mov [ rsp + 0xf0 ], r13; saving to stack
mov [ rsp + 0xf8 ], r14; saving to stack
mov [ rsp + 0x100 ], r15; saving to stack
mov rax, [ rsi + 0x30 ]; load m64 x7 to register64
mov r10, [ rsi + 0x38 ]; load m64 x4 to register64
mov r11, [ rsi + 0x40 ]; load m64 x1 to register64
imul rbx, rax, 0x2; x8 <- x7 * 0x2
imul rbp, r10, 0x2; x5 <- x4 * 0x2
imul r12, r11, 0x2; x2 <- x1 * 0x2
imul rbp, rbp, 0x2; x10003 <- x5 * 0x2
imul r12, r12, 0x2; x10001 <- x2 * 0x2
imul rbx, rbx, 0x2; x10005 <- x8 * 0x2
mov r13, [ rsi + 0x28 ]; load m64 x10 to register64
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r14, r15, r12; x74, x73<- arg1[1] * x10001
mov rdx, rbp; x10003 to rdx
mulx rbp, rcx, [ rsi + 0x10 ]; x62, x61<- arg1[2] * x10003
mov r8, rdx; preserving value of x10003 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r9, rdi, [ rsi + 0x0 ]; x106, x105<- arg1[0] * arg1[0]
imul rdx, r13, 0x2; x11 <- x10 * 0x2
imul rdx, rdx, 0x2; x10007 <- x11 * 0x2
mov [ rsp + 0x8 ], r11; spilling x1 to mem
mulx rdx, r11, [ rsi + 0x20 ]; x44, x43<- arg1[4] * x10007
mov [ rsp + 0x10 ], r10; spilling x4 to mem
mov r10, rdx; preserving value of x44 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x18 ], rax; spilling x7 to mem
mov [ rsp + 0x20 ], r9; spilling x106 to mem
mulx rax, r9, rbx; x52, x51<- arg1[3] * x10005
xor rdx, rdx
adox r11, r9
adox rax, r10
adcx r11, rcx
mov rcx, -0x3 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r11, r15
adcx rbp, rax
clc;
adcx r11, rdi
adox r14, rbp
setc r15b; spill CF x120 to reg (r15)
imul r13, r13, 0x2; x10006 <- x10 * 0x2
mov rdi, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx r13, r10, r13; x36, x35<- arg1[5] * x10006
sar  r15b, 1
adcx r14, [ rsp + 0x20 ]
mov rdx, rbx; x10005 to rdx
mulx rbx, r9, [ rsi + 0x20 ]; x42, x41<- arg1[4] * x10005
mov rax, r11; x123, copying x119 here, cause x119 is needed in a reg for other than x123, namely all: , x125, x123, size: 2
shrd rax, r14, 58; x123 <- x121||x119 >> 58
mov rbp, rdx; preserving value of x10005 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r15, rdi, r12; x60, x59<- arg1[2] * x10001
imul rdx, [ rsi + 0x8 ], 0x2; x16 <- arg1[1] * 0x2
xor rcx, rcx
adox r10, r9
mov r9, rdx; preserving value of x16 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x28 ], rax; spilling x123 to mem
mulx rcx, rax, r8; x50, x49<- arg1[3] * x10003
adcx r10, rax
adox rbx, r13
mov rdx, r9; x16 to rdx
mulx rdx, r9, [ rsi + 0x0 ]; x104, x103<- arg1[0] * x16
adcx rcx, rbx
imul r13, [ rsi + 0x10 ], 0x2; x15 <- arg1[2] * 0x2
shr r14, 58; x124 <- x121>> 58
xor rax, rax
adox r10, rdi
adox r15, rcx
adcx r10, r9
mov rdi, rdx; preserving value of x104 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx rbx, r9, r13; x102, x101<- arg1[0] * x15
mov rdx, r8; x10003 to rdx
mulx r8, rcx, [ rsi + 0x20 ]; x40, x39<- arg1[4] * x10003
adcx rdi, r15
mov r15, rdx; preserving value of x10003 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx rbp, rax, rbp; x34, x33<- arg1[5] * x10005
add rax, rcx; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x30 ], rbx; spilling x102 to mem
mulx rcx, rbx, [ rsi + 0x8 ]; x88, x87<- arg1[1] * arg1[1]
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r10, [ rsp + 0x28 ]
adox r14, rdi
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x38 ], r9; spilling x101 to mem
mulx rdi, r9, r12; x48, x47<- arg1[3] * x10001
setc dl; spill CF x223 to reg (rdx)
mov [ rsp + 0x40 ], rcx; spilling x88 to mem
mov rcx, r10; x258, copying x254 here, cause x254 is needed in a reg for other than x258, namely all: , x258, x260, size: 2
shrd rcx, r14, 58; x258 <- x256||x254 >> 58
sar  dl, 1
adcx r8, rbp
adox rax, r9
adox rdi, r8
xor rbp, rbp
adox rax, rbx
adox rdi, [ rsp + 0x40 ]
adcx rax, [ rsp + 0x38 ]
mov rdx, r15; x10003 to rdx
mulx r15, rbx, [ rsi + 0x28 ]; x32, x31<- arg1[5] * x10003
mov r9, rdx; preserving value of x10003 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r13, r8, r13; x86, x85<- arg1[1] * x15
adcx rdi, [ rsp + 0x30 ]
imul rdx, [ rsi + 0x18 ], 0x2; x14 <- arg1[3] * 0x2
shr r14, 58; x259 <- x256>> 58
mov [ rsp + 0x48 ], r13; spilling x86 to mem
xor r13, r13
adox rax, rcx
seto bpl; spill OF x262 to reg (rbp)
imul rcx, [ rsp + 0x18 ], 0x2; x10004 <- x7 * 0x2
sar  bpl, 1
adcx r14, rdi
xchg rdx, rcx; x10004, swapping with x14, which is currently in rdx
mulx rdx, rdi, [ rsi + 0x30 ]; x28, x27<- arg1[6] * x10004
adox rdi, rbx
mov rbx, rdx; preserving value of x28 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx rbp, r13, r12; x38, x37<- arg1[4] * x10001
adox r15, rbx
xor rdx, rdx
adox rdi, r13
adcx rdi, r8
adox rbp, r15
mov r8, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx rbx, r13, rcx; x100, x99<- arg1[0] * x14
setc dl; spill CF x215 to reg (rdx)
mov r15, rax; x265, copying x261 here, cause x261 is needed in a reg for other than x265, namely all: , x267, x265, size: 2
shrd r15, r14, 58; x265 <- x263||x261 >> 58
imul r8, [ rsi + 0x20 ], 0x2; x13 <- arg1[4] * 0x2
sar  dl, 1
adcx rbp, [ rsp + 0x48 ]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x50 ], r11; spilling x119 to mem
mov [ rsp + 0x58 ], r8; spilling x13 to mem
mulx r11, r8, r12; x30, x29<- arg1[5] * x10001
adox rdi, r13
adox rbx, rbp
shr r14, 58; x266 <- x263>> 58
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r13, rbp, [ rsi + 0x10 ]; x72, x71<- arg1[2] * arg1[2]
xor rdx, rdx
adox rdi, r15
mov r15, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0x60 ], r13; spilling x72 to mem
mulx r9, r13, r9; x26, x25<- arg1[6] * x10003
adcx r13, r8
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r8, r15, [ rsp + 0x58 ]; x98, x97<- arg1[0] * x13
adcx r11, r9
mov rdx, rcx; x14 to rdx
mulx rcx, r9, [ rsi + 0x8 ]; x84, x83<- arg1[1] * x14
clc;
adcx r13, rbp
adox r14, rbx
mov rbx, 0x3ffffffffffffff ; moving imm to reg
setc bpl; spill CF x195 to reg (rbp)
mov [ rsp + 0x68 ], r8; spilling x98 to mem
mov r8, [ rsp + 0x50 ]; x125, copying x119 here, cause x119 is needed in a reg for other than x125, namely all: , x125, size: 1
and r8, rbx; x125 <- x119&0x3ffffffffffffff
mov rbx, rdi; x272, copying x268 here, cause x268 is needed in a reg for other than x272, namely all: , x274, x272, size: 2
shrd rbx, r14, 58; x272 <- x270||x268 >> 58
mov [ rsp + 0x70 ], r8; spilling x125 to mem
xor r8, r8
adox r13, r9
movzx rbp, bpl
lea r11, [ rbp + r11 ]
adcx r11, [ rsp + 0x60 ]
clc;
adcx r13, r15
setc r15b; spill CF x203 to reg (r15)
seto r9b; spill OF x199 to reg (r9)
shr r14, 58; x273 <- x270>> 58
xor rbp, rbp
adox r13, rbx
mov r8, 0x3ffffffffffffff ; moving imm to reg
seto bl; spill OF x276 to reg (rbx)
mov rbp, r13; x281, copying x275 here, cause x275 is needed in a reg for other than x281, namely all: , x281, x279, size: 2
and rbp, r8; x281 <- x275&0x3ffffffffffffff
mov r8, rdx; preserving value of x14 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0x78 ], rbp; spilling x281 to mem
mov [ rsp + 0x80 ], r14; spilling x273 to mem
mulx rbp, r14, r12; x24, x23<- arg1[6] * x10001
sar  r9b, 1
adcx rcx, r11
mov rdx, r8; x14 to rdx
mulx rdx, r8, [ rsi + 0x10 ]; x70, x69<- arg1[2] * x14
sar  r15b, 1
adcx rcx, [ rsp + 0x68 ]
sar  bl, 1
adcx rcx, [ rsp + 0x80 ]
imul r9, [ rsp + 0x10 ], 0x2; x10002 <- x4 * 0x2
mov r11, rdx; preserving value of x70 into a new reg
mov rdx, [ rsi + 0x38 ]; saving arg1[7] in rdx.
mulx r9, r15, r9; x22, x21<- arg1[7] * x10002
shrd r13, rcx, 58; x279 <- x277||x275 >> 58
imul rdx, [ rsi + 0x28 ], 0x2; x12 <- arg1[5] * 0x2
test al, al
adox r15, r14
adcx r15, r8
adox rbp, r9
mov rbx, rdx; preserving value of x12 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r14, r8, [ rsp + 0x58 ]; x82, x81<- arg1[1] * x13
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx r12, r9, r12; x20, x19<- arg1[7] * x10001
adcx r11, rbp
mov rdx, rbx; x12 to rdx
mulx rbx, rbp, [ rsi + 0x0 ]; x96, x95<- arg1[0] * x12
add r15, r8; could be done better, if r0 has been u8 as well
adcx r14, r11
shr rcx, 58; x280 <- x277>> 58
xor r8, r8
adox r15, rbp
adox rbx, r14
mov r11, rdx; preserving value of x12 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx rbp, r14, [ rsi + 0x18 ]; x58, x57<- arg1[3] * arg1[3]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x88 ], r12; spilling x20 to mem
mulx r8, r12, r11; x80, x79<- arg1[1] * x12
adcx r15, r13
adcx rcx, rbx
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r13, rbx, [ rsp + 0x58 ]; x68, x67<- arg1[2] * x13
imul rdx, [ rsi + 0x30 ], 0x2; x9 <- arg1[6] * 0x2
mov [ rsp + 0x90 ], r8; spilling x80 to mem
xor r8, r8
adox r9, r14
adcx r9, rbx
mulx r14, rbx, [ rsi + 0x0 ]; x94, x93<- arg1[0] * x9
mov [ rsp + 0x98 ], r14; spilling x94 to mem
setc r14b; spill CF x163 to reg (r14)
clc;
adcx r9, r12
setc r12b; spill CF x167 to reg (r12)
clc;
adcx r9, rbx
adox rbp, [ rsp + 0x88 ]
setc bl; spill CF x171 to reg (rbx)
mov r8, r15; x286, copying x282 here, cause x282 is needed in a reg for other than x286, namely all: , x286, x288, size: 2
shrd r8, rcx, 58; x286 <- x284||x282 >> 58
shr rcx, 58; x287 <- x284>> 58
sar  r14b, 1
adcx r13, rbp
adox r9, r8
seto r14b; spill OF x290 to reg (r14)
imul rbp, [ rsp + 0x8 ], 0x2; x10000 <- x1 * 0x2
sar  r12b, 1
adcx r13, [ rsp + 0x90 ]
sar  bl, 1
adcx r13, [ rsp + 0x98 ]
sar  r14b, 1
adcx rcx, r13
imul r12, [ rsi + 0x38 ], 0x2; x6 <- arg1[7] * 0x2
mov rbx, rdx; preserving value of x9 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r8, r14, r11; x66, x65<- arg1[2] * x12
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0xa0 ], r8; spilling x66 to mem
mulx r13, r8, [ rsp + 0x58 ]; x56, x55<- arg1[3] * x13
mov rdx, r12; x6 to rdx
mov [ rsp + 0xa8 ], r10; spilling x254 to mem
mulx r12, r10, [ rsi + 0x0 ]; x92, x91<- arg1[0] * x6
mov [ rsp + 0xb0 ], r12; spilling x92 to mem
mov r12, rdx; preserving value of x6 into a new reg
mov rdx, [ rsi + 0x40 ]; saving arg1[8] in rdx.
mov [ rsp + 0xb8 ], r10; spilling x91 to mem
mulx rbp, r10, rbp; x18, x17<- arg1[8] * x10000
mov rdx, rcx; x294, copying x291 here, cause x291 is needed in a reg for other than x294, namely all: , x293, x294, size: 2
shr rdx, 58; x294 <- x291>> 58
mov [ rsp + 0xc0 ], rdx; spilling x294 to mem
mov rdx, r9; x293, copying x289 here, cause x289 is needed in a reg for other than x293, namely all: , x295, x293, size: 2
shrd rdx, rcx, 58; x293 <- x291||x289 >> 58
add r10, r8; could be done better, if r0 has been u8 as well
adcx r13, rbp
xor rcx, rcx
adox r10, r14
mov r14, rdx; preserving value of x293 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx r11, r8, r11; x54, x53<- arg1[3] * x12
adox r13, [ rsp + 0xa0 ]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbp, rcx, rbx; x78, x77<- arg1[1] * x9
imul rdx, [ rsi + 0x40 ], 0x2; x3 <- arg1[8] * 0x2
add r10, rcx; could be done better, if r0 has been u8 as well
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r10, [ rsp + 0xb8 ]
adcx rbp, r13
adox rbp, [ rsp + 0xb0 ]
mov r13, rdx; preserving value of x3 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0xc8 ], r11; spilling x54 to mem
mulx rcx, r11, [ rsi + 0x20 ]; x46, x45<- arg1[4] * arg1[4]
test al, al
adox r10, r14
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r12, r14, r12; x76, x75<- arg1[1] * x6
adcx r11, r8
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r13, r8, r13; x90, x89<- arg1[0] * x3
adox rbp, [ rsp + 0xc0 ]
mov rdx, rbx; x9 to rdx
mulx rdx, rbx, [ rsi + 0x10 ]; x64, x63<- arg1[2] * x9
adcx rcx, [ rsp + 0xc8 ]
mov [ rsp + 0xd0 ], r13; spilling x90 to mem
xor r13, r13
adox r11, rbx
mov rbx, [ rsp + 0x0 ]; load m64 out1 to register64
mov r13, [ rsp + 0x78 ]; TMP = x281
mov [ rbx + 0x20 ], r13; out1[4] = TMP
adox rdx, rcx
adcx r11, r14
setc r13b; spill CF x135 to reg (r13)
mov r14, r10; x300, copying x296 here, cause x296 is needed in a reg for other than x300, namely all: , x300, x302, size: 2
shrd r14, rbp, 58; x300 <- x298||x296 >> 58
sar  r13b, 1
adcx r12, rdx
adox r11, r8
clc;
adcx r11, r14
adox r12, [ rsp + 0xd0 ]
setc r8b; spill CF x304 to reg (r8)
shr rbp, 58; x301 <- x298>> 58
sar  r8b, 1
adcx rbp, r12
mov rcx, r11; x307, copying x303 here, cause x303 is needed in a reg for other than x307, namely all: , x309, x307, size: 2
shrd rcx, rbp, 57; x307 <- x305||x303 >> 57
shr rbp, 57; x308 <- x305>> 57
xor rdx, rdx
adox rcx, [ rsp + 0x70 ]
adox rbp, rdx
mov r13, rcx; x313, copying x310 here, cause x310 is needed in a reg for other than x313, namely all: , x313, x314, size: 2
shrd r13, rbp, 58; x313 <- x312||x310 >> 58
mov r14, 0x3ffffffffffffff ; moving imm to reg
mov r8, [ rsp + 0xa8 ]; x260, copying x254 here, cause x254 is needed in a reg for other than x260, namely all: , x260, size: 1
and r8, r14; x260 <- x254&0x3ffffffffffffff
lea r13, [ r13 + r8 ]
and rax, r14; x267 <- x261&0x3ffffffffffffff
and r15, r14; x288 <- x282&0x3ffffffffffffff
mov r12, r13; x317, copying x315 here, cause x315 is needed in a reg for other than x317, namely all: , x317, x316, size: 2
and r12, r14; x317 <- x315&0x3ffffffffffffff
and rcx, r14; x314 <- x310&0x3ffffffffffffff
and rdi, r14; x274 <- x268&0x3ffffffffffffff
and r10, r14; x302 <- x296&0x3ffffffffffffff
mov [ rbx + 0x8 ], r12; out1[1] = x317
and r9, r14; x295 <- x289&0x3ffffffffffffff
mov [ rbx + 0x18 ], rdi; out1[3] = x274
shr r13, 58; x316 <- x315>> 58
lea r13, [ r13 + rax ]
mov rbp, 0x1ffffffffffffff ; moving imm to reg
and r11, rbp; x309 <- x303&0x1ffffffffffffff
mov [ rbx + 0x30 ], r9; out1[6] = x295
mov [ rbx + 0x10 ], r13; out1[2] = x318
mov [ rbx + 0x28 ], r15; out1[5] = x288
mov [ rbx + 0x40 ], r11; out1[8] = x309
mov [ rbx + 0x38 ], r10; out1[7] = x302
mov [ rbx + 0x0 ], rcx; out1[0] = x314
mov rbx, [ rsp + 0xd8 ]; restoring from stack
mov rbp, [ rsp + 0xe0 ]; restoring from stack
mov r12, [ rsp + 0xe8 ]; restoring from stack
mov r13, [ rsp + 0xf0 ]; restoring from stack
mov r14, [ rsp + 0xf8 ]; restoring from stack
mov r15, [ rsp + 0x100 ]; restoring from stack
add rsp, 0x108 
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; clocked at 3600 MHz
; first cyclecount 93.835, best 73.47126436781609, lastGood 73.48863636363636
; seed 3258432306148663 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1097842 ms / 60000 runs=> 18.297366666666665ms/run
; Time spent for assembling and measureing (initial batch_size=86, initial num_batches=101): 114514 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.10430827022467713
; number reverted permutation/ tried permutation: 22914 / 30128 =76.055%
; number reverted decision/ tried decision: 22497 / 29873 =75.309%