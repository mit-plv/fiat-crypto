SECTION .text
	GLOBAL square_p521
square_p521:
sub rsp, 0x148 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x118 ], rbx; saving to stack
mov [ rsp + 0x120 ], rbp; saving to stack
mov [ rsp + 0x128 ], r12; saving to stack
mov [ rsp + 0x130 ], r13; saving to stack
mov [ rsp + 0x138 ], r14; saving to stack
mov [ rsp + 0x140 ], r15; saving to stack
mov rax, [ rsi + 0x40 ]; load m64 x1 to register64

; works
; imul r10, rax, 0x2; x2 <- x1 * 0x2
; imul r10, r10, 0x2; x10001 <- x2 * 0x2

; does not work
imul r10, rax, 0x4; x10001 <- x1 * 0x4

mov r11, [ rsi + 0x28 ]; load m64 x10 to register64
mov rbx, [ rsi + 0x38 ]; load m64 x4 to register64
mov rbp, [ rsi + 0x30 ]; load m64 x7 to register64
mov rdx, r10; x10001 to rdx
mulx r10, r12, [ rsi + 0x8 ]; x74, x73<- arg1[1] * x10001
imul r13, r11, 0x2; x11 <- x10 * 0x2
imul r14, rbp, 0x2; x8 <- x7 * 0x2
imul r15, rbx, 0x2; x5 <- x4 * 0x2
imul r15, r15, 0x2; x10003 <- x5 * 0x2
xchg rdx, r15; x10003, swapping with x10001, which is currently in rdx
mulx rcx, r8, [ rsi + 0x10 ]; x62, x61<- arg1[2] * x10003
imul r14, r14, 0x2; x10005 <- x8 * 0x2
imul rbx, rbx, 0x2; x10002 <- x4 * 0x2
mov r9, rdx; preserving value of x10003 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov [ rsp + 0x8 ], rax; spilling x1 to mem
mulx rdi, rax, [ rsi + 0x0 ]; x106, x105<- arg1[0] * arg1[0]
imul r13, r13, 0x2; x10007 <- x11 * 0x2
mov rdx, r13; x10007 to rdx
mulx rdx, r13, [ rsi + 0x20 ]; x44, x43<- arg1[4] * x10007
mov [ rsp + 0x10 ], rbx; spilling x10002 to mem
mov rbx, rdx; preserving value of x44 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x18 ], r15; spilling x10001 to mem
mov [ rsp + 0x20 ], rdi; spilling x106 to mem
mulx r15, rdi, r14; x52, x51<- arg1[3] * x10005
add r13, rdi; could be done better, if r0 has been u8 as well
adcx r15, rbx
test al, al
adox r13, r8
adcx r13, r12
adox rcx, r15
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, rax
adcx r10, rcx
adox r10, [ rsp + 0x20 ]
imul r11, r11, 0x2; x10006 <- x10 * 0x2
mov r12, r13; x123, copying x119 here, cause x119 is needed in a reg for other than x123, namely all: , x125, x123, size: 2
shrd r12, r10, 58; x123 <- x121||x119 >> 58
mov rdx, r14; x10005 to rdx
mulx r14, r8, [ rsi + 0x20 ]; x42, x41<- arg1[4] * x10005
mov rax, rdx; preserving value of x10005 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx r11, rbx, r11; x36, x35<- arg1[5] * x10006
imul rdx, [ rsi + 0x8 ], 0x2; x16 <- arg1[1] * 0x2
add rbx, r8; could be done better, if r0 has been u8 as well
mov rdi, rdx; preserving value of x16 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r15, rcx, [ rsp + 0x18 ]; x60, x59<- arg1[2] * x10001
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rdi, r8, rdi; x104, x103<- arg1[0] * x16
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x28 ], rbp; spilling x7 to mem
mov [ rsp + 0x30 ], r12; spilling x123 to mem
mulx rbp, r12, r9; x50, x49<- arg1[3] * x10003
adcx r14, r11
add rbx, r12; could be done better, if r0 has been u8 as well
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, rcx
setc r11b; spill CF x243 to reg (r11)
seto cl; spill OF x247 to reg (rcx)
imul r12, [ rsi + 0x10 ], 0x2; x15 <- arg1[2] * 0x2
sar  r11b, 1
adcx rbp, r14
mov rdx, rax; x10005 to rdx
mulx rdx, rax, [ rsi + 0x28 ]; x34, x33<- arg1[5] * x10005
sar  cl, 1
adcx r15, rbp
adox rbx, r8
mov r8, rdx; preserving value of x34 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx r14, r11, [ rsp + 0x18 ]; x48, x47<- arg1[3] * x10001
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx rcx, rbp, r9; x40, x39<- arg1[4] * x10003
adox rdi, r15
shr r10, 58; x124 <- x121>> 58
xor rdx, rdx
adox rax, rbp
adcx rbx, [ rsp + 0x30 ]
mov r15, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x38 ], r12; spilling x15 to mem
mulx rbp, r12, [ rsi + 0x8 ]; x88, x87<- arg1[1] * arg1[1]
adcx r10, rdi
adox rcx, r8
mov rdx, r10; x259, copying x256 here, cause x256 is needed in a reg for other than x259, namely all: , x259, x258, size: 2
shr rdx, 58; x259 <- x256>> 58
mov r8, rbx; x258, copying x254 here, cause x254 is needed in a reg for other than x258, namely all: , x260, x258, size: 2
shrd r8, r10, 58; x258 <- x256||x254 >> 58
xor rdi, rdi
adox rax, r11
adox r14, rcx
mov r15, rdx; preserving value of x259 into a new reg
mov rdx, [ rsp + 0x38 ]; saving x15 in rdx.
mulx r11, r10, [ rsi + 0x0 ]; x102, x101<- arg1[0] * x15
adcx rax, r12
setc r12b; spill CF x231 to reg (r12)
imul rcx, [ rsp + 0x28 ], 0x2; x10004 <- x7 * 0x2
imul rdi, [ rsi + 0x18 ], 0x2; x14 <- arg1[3] * 0x2
sar  r12b, 1
adcx rbp, r14
adox rax, r10
mov r14, rdx; preserving value of x15 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r10, r12, [ rsp + 0x18 ]; x38, x37<- arg1[4] * x10001
adox r11, rbp
test al, al
adox rax, r8
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mulx rcx, r8, rcx; x28, x27<- arg1[6] * x10004
mov rdx, r9; x10003 to rdx
mulx r9, rbp, [ rsi + 0x28 ]; x32, x31<- arg1[5] * x10003
adox r15, r11
adcx r8, rbp
mov r11, rdx; preserving value of x10003 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x40 ], r13; spilling x119 to mem
mulx rbp, r13, rdi; x100, x99<- arg1[0] * x14
adcx r9, rcx
mov rdx, rax; x265, copying x261 here, cause x261 is needed in a reg for other than x265, namely all: , x265, x267, size: 2
shrd rdx, r15, 58; x265 <- x263||x261 >> 58
xor rcx, rcx
adox r8, r12
mov r12, rdx; preserving value of x265 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r14, rcx, r14; x86, x85<- arg1[1] * x15
adox r10, r9
adcx r8, rcx
adcx r14, r10
test al, al
adox r8, r13
adox rbp, r14
imul rdx, [ rsi + 0x30 ], 0x2; x9 <- arg1[6] * 0x2
imul r13, [ rsi + 0x20 ], 0x2; x13 <- arg1[4] * 0x2
mov r9, 0x3ffffffffffffff ; moving imm to reg
mov rcx, [ rsp + 0x40 ]; x125, copying x119 here, cause x119 is needed in a reg for other than x125, namely all: , x125, size: 1
and rcx, r9; x125 <- x119&0x3ffffffffffffff
xchg rdx, r11; x10003, swapping with x9, which is currently in rdx
mulx rdx, r10, [ rsi + 0x30 ]; x26, x25<- arg1[6] * x10003
mov r14, rdx; preserving value of x26 into a new reg
mov rdx, [ rsp + 0x18 ]; saving x10001 in rdx.
mov [ rsp + 0x48 ], rcx; spilling x125 to mem
mulx r9, rcx, [ rsi + 0x28 ]; x30, x29<- arg1[5] * x10001
shr r15, 58; x266 <- x263>> 58
add r8, r12; could be done better, if r0 has been u8 as well
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r10, rcx
adcx r15, rbp
seto bpl; spill OF x191 to reg (rbp)
mov rcx, r8; x272, copying x268 here, cause x268 is needed in a reg for other than x272, namely all: , x274, x272, size: 2
shrd rcx, r15, 58; x272 <- x270||x268 >> 58
imul r12, [ rsi + 0x28 ], 0x2; x12 <- arg1[5] * 0x2
shr r15, 58; x273 <- x270>> 58
mov [ rsp + 0x50 ], r11; spilling x9 to mem
mov r11, rdx; preserving value of x10001 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x58 ], r15; spilling x273 to mem
mov [ rsp + 0x60 ], r12; spilling x12 to mem
mulx r15, r12, r13; x98, x97<- arg1[0] * x13
sar  bpl, 1
adcx r9, r14
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r14, rbp, [ rsi + 0x10 ]; x72, x71<- arg1[2] * arg1[2]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x68 ], r15; spilling x98 to mem
mov [ rsp + 0x70 ], rcx; spilling x272 to mem
mulx r15, rcx, rdi; x84, x83<- arg1[1] * x14
adox r10, rbp
adox r14, r9
add r10, rcx; could be done better, if r0 has been u8 as well
adcx r15, r14
mov rdx, r11; x10001 to rdx
mulx r11, r9, [ rsi + 0x30 ]; x24, x23<- arg1[6] * x10001
xor rbp, rbp
adox r10, r12
adcx r10, [ rsp + 0x70 ]
mov r12, rdx; preserving value of x10001 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx rcx, r14, [ rsp + 0x60 ]; x96, x95<- arg1[0] * x12
adox r15, [ rsp + 0x68 ]
mov rdx, [ rsp + 0x10 ]; x10002 to rdx
mulx rdx, rbp, [ rsi + 0x38 ]; x22, x21<- arg1[7] * x10002
mov [ rsp + 0x78 ], rcx; spilling x96 to mem
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, r9
adcx r15, [ rsp + 0x58 ]
adox r11, rdx
mov r9, r10; x279, copying x275 here, cause x275 is needed in a reg for other than x279, namely all: , x281, x279, size: 2
shrd r9, r15, 58; x279 <- x277||x275 >> 58
mov rdx, rdi; x14 to rdx
mulx rdx, rcx, [ rsi + 0x10 ]; x70, x69<- arg1[2] * x14
add rbp, rcx; could be done better, if r0 has been u8 as well
xchg rdx, r13; x13, swapping with x70, which is currently in rdx
mov [ rsp + 0x80 ], r9; spilling x279 to mem
mulx rcx, r9, [ rsi + 0x8 ]; x82, x81<- arg1[1] * x13
adcx r13, r11
shr r15, 58; x280 <- x277>> 58
mov [ rsp + 0x88 ], r15; spilling x280 to mem
mulx r11, r15, [ rsi + 0x10 ]; x68, x67<- arg1[2] * x13
test al, al
adox rbp, r9
mov r9, rdx; preserving value of x13 into a new reg
mov rdx, [ rsi + 0x38 ]; saving arg1[7] in rdx.
mov [ rsp + 0x90 ], r11; spilling x68 to mem
mulx r12, r11, r12; x20, x19<- arg1[7] * x10001
adcx rbp, r14
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x98 ], r15; spilling x67 to mem
mulx r14, r15, [ rsp + 0x50 ]; x94, x93<- arg1[0] * x9
adox rcx, r13
adcx rcx, [ rsp + 0x78 ]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0xa0 ], r14; spilling x94 to mem
mulx r13, r14, [ rsi + 0x18 ]; x58, x57<- arg1[3] * arg1[3]
xor rdx, rdx
adox r11, r14
adcx rbp, [ rsp + 0x80 ]
adcx rcx, [ rsp + 0x88 ]
adox r13, r12
xor r12, r12
adox r11, [ rsp + 0x98 ]
mov rdx, [ rsp + 0x60 ]; x12 to rdx
mulx r14, r12, [ rsi + 0x8 ]; x80, x79<- arg1[1] * x12
adox r13, [ rsp + 0x90 ]
adcx r11, r12
adcx r14, r13
test al, al
adox r11, r15
seto r15b; spill OF x171 to reg (r15)
mov r12, rcx; x287, copying x284 here, cause x284 is needed in a reg for other than x287, namely all: , x286, x287, size: 2
shr r12, 58; x287 <- x284>> 58
mov r13, rbp; x286, copying x282 here, cause x282 is needed in a reg for other than x286, namely all: , x286, x288, size: 2
shrd r13, rcx, 58; x286 <- x284||x282 >> 58
xor rcx, rcx
adox r11, r13
mulx r13, rcx, [ rsi + 0x10 ]; x66, x65<- arg1[2] * x12
mov [ rsp + 0xa8 ], r13; spilling x66 to mem
mov r13, rdx; preserving value of x12 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0xb0 ], rcx; spilling x65 to mem
mov [ rsp + 0xb8 ], r11; spilling x289 to mem
mulx rcx, r11, [ rsp + 0x50 ]; x78, x77<- arg1[1] * x9
movzx r15, r15b
lea r14, [ r15 + r14 ]
adcx r14, [ rsp + 0xa0 ]
seto dl; spill OF x290 to reg (rdx)
imul r15, [ rsp + 0x8 ], 0x2; x10000 <- x1 * 0x2
sar  dl, 1
adcx r12, r14
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r9, r14, r9; x56, x55<- arg1[3] * x13
mov rdx, r15; x10000 to rdx
mulx rdx, r15, [ rsi + 0x40 ]; x18, x17<- arg1[8] * x10000
mov [ rsp + 0xc0 ], rcx; spilling x78 to mem
imul rcx, [ rsi + 0x38 ], 0x2; x6 <- arg1[7] * 0x2
mov [ rsp + 0xc8 ], r11; spilling x77 to mem
mov r11, r12; x294, copying x291 here, cause x291 is needed in a reg for other than x294, namely all: , x294, x293, size: 2
shr r11, 58; x294 <- x291>> 58
mov [ rsp + 0xd0 ], r11; spilling x294 to mem
xor r11, r11
adox r15, r14
adox r9, rdx
mov r14, [ rsp + 0xb8 ]; load m64 x289 to register64
mov rdx, r14; x293, copying x289 here, cause x289 is needed in a reg for other than x293, namely all: , x295, x293, size: 2
shrd rdx, r12, 58; x293 <- x291||x289 >> 58
test al, al
adox r15, [ rsp + 0xb0 ]
mov r12, rdx; preserving value of x293 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0xd8 ], rbx; spilling x254 to mem
mulx r11, rbx, rcx; x92, x91<- arg1[0] * x6
adcx r15, [ rsp + 0xc8 ]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0xe0 ], r12; spilling x293 to mem
mov [ rsp + 0xe8 ], r11; spilling x92 to mem
mulx r12, r11, [ rsi + 0x20 ]; x46, x45<- arg1[4] * arg1[4]
adox r9, [ rsp + 0xa8 ]
adcx r9, [ rsp + 0xc0 ]
mov rdx, r13; x12 to rdx
mulx rdx, r13, [ rsi + 0x18 ]; x54, x53<- arg1[3] * x12
add r15, rbx; could be done better, if r0 has been u8 as well
adcx r9, [ rsp + 0xe8 ]
add r15, [ rsp + 0xe0 ]; could be done better, if r0 has been u8 as well
adcx r9, [ rsp + 0xd0 ]
mov rbx, rdx; preserving value of x54 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0xf0 ], r12; spilling x46 to mem
mulx rcx, r12, rcx; x76, x75<- arg1[1] * x6
imul rdx, [ rsi + 0x40 ], 0x2; x3 <- arg1[8] * 0x2
mov [ rsp + 0xf8 ], rcx; spilling x76 to mem
mov rcx, r15; x300, copying x296 here, cause x296 is needed in a reg for other than x300, namely all: , x302, x300, size: 2
shrd rcx, r9, 58; x300 <- x298||x296 >> 58
mov [ rsp + 0x100 ], rcx; spilling x300 to mem
xor rcx, rcx
adox r11, r13
mulx rdx, r13, [ rsi + 0x0 ]; x90, x89<- arg1[0] * x3
adox rbx, [ rsp + 0xf0 ]
mov rcx, rdx; preserving value of x90 into a new reg
mov rdx, [ rsp + 0x50 ]; saving x9 in rdx.
mov [ rsp + 0x108 ], r13; spilling x89 to mem
mulx rdx, r13, [ rsi + 0x10 ]; x64, x63<- arg1[2] * x9
shr r9, 58; x301 <- x298>> 58
mov [ rsp + 0x110 ], r9; spilling x301 to mem
xor r9, r9
adox r11, r13
adcx r11, r12
adox rdx, rbx
mov r12, -0x3 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r11, [ rsp + 0x108 ]
adcx rdx, [ rsp + 0xf8 ]
adox rcx, rdx
test al, al
adox r11, [ rsp + 0x100 ]
adox rcx, [ rsp + 0x110 ]
mov rbx, r11; x307, copying x303 here, cause x303 is needed in a reg for other than x307, namely all: , x307, x309, size: 2
shrd rbx, rcx, 57; x307 <- x305||x303 >> 57
mov r13, 0x3ffffffffffffff ; moving imm to reg
mov rdx, [ rsp + 0xd8 ]; x260, copying x254 here, cause x254 is needed in a reg for other than x260, namely all: , x260, size: 1
and rdx, r13; x260 <- x254&0x3ffffffffffffff
shr rcx, 57; x308 <- x305>> 57
xor r12, r12
adox rbx, [ rsp + 0x48 ]
adox rcx, r12
mov r9, rbx; x313, copying x310 here, cause x310 is needed in a reg for other than x313, namely all: , x313, x314, size: 2
shrd r9, rcx, 58; x313 <- x312||x310 >> 58
mov rcx, 0x1ffffffffffffff ; moving imm to reg
and r11, rcx; x309 <- x303&0x1ffffffffffffff
mov r12, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r12 + 0x40 ], r11; out1[8] = x309
and rbx, r13; x314 <- x310&0x3ffffffffffffff
lea r9, [ r9 + rdx ]
and r15, r13; x302 <- x296&0x3ffffffffffffff
mov [ r12 + 0x38 ], r15; out1[7] = x302
mov rdx, r9; x316, copying x315 here, cause x315 is needed in a reg for other than x316, namely all: , x316, x317, size: 2
shr rdx, 58; x316 <- x315>> 58
and rbp, r13; x288 <- x282&0x3ffffffffffffff
and rax, r13; x267 <- x261&0x3ffffffffffffff
mov [ r12 + 0x0 ], rbx; out1[0] = x314
and r9, r13; x317 <- x315&0x3ffffffffffffff
mov [ r12 + 0x28 ], rbp; out1[5] = x288
and r14, r13; x295 <- x289&0x3ffffffffffffff
mov [ r12 + 0x8 ], r9; out1[1] = x317
lea rdx, [ rdx + rax ]
and r10, r13; x281 <- x275&0x3ffffffffffffff
mov [ r12 + 0x20 ], r10; out1[4] = x281
mov [ r12 + 0x10 ], rdx; out1[2] = x318
and r8, r13; x274 <- x268&0x3ffffffffffffff
mov [ r12 + 0x30 ], r14; out1[6] = x295
mov [ r12 + 0x18 ], r8; out1[3] = x274
mov rbx, [ rsp + 0x118 ]; restoring from stack
mov rbp, [ rsp + 0x120 ]; restoring from stack
mov r12, [ rsp + 0x128 ]; restoring from stack
mov r13, [ rsp + 0x130 ]; restoring from stack
mov r14, [ rsp + 0x138 ]; restoring from stack
mov r15, [ rsp + 0x140 ]; restoring from stack
add rsp, 0x148 
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; clocked at 2200 MHz
; first cyclecount 193.04, best 140.4848484848485, lastGood 141.3125
; seed 3277703234885713 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1804300 ms / 60000 runs=> 30.071666666666665ms/run
; Time spent for assembling and measureing (initial batch_size=65, initial num_batches=101): 203377 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.11271795156016183
; number reverted permutation/ tried permutation: 25167 / 29961 =83.999%
; number reverted decision/ tried decision: 23002 / 30040 =76.571%
