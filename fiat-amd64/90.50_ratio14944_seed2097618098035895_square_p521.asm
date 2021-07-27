SECTION .text
	GLOBAL square_p521
square_p521:
sub rsp, 0xe0 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0xb0 ], rbx; saving to stack
mov [ rsp + 0xb8 ], rbp; saving to stack
mov [ rsp + 0xc0 ], r12; saving to stack
mov [ rsp + 0xc8 ], r13; saving to stack
mov [ rsp + 0xd0 ], r14; saving to stack
mov [ rsp + 0xd8 ], r15; saving to stack
mov rax, [ rsi + 0x38 ]; load m64 x4 to register64
imul r10, rax, 0x2; x5 <- x4 * 0x2
mov r11, [ rsi + 0x30 ]; load m64 x7 to register64
mov rbx, [ rsi + 0x40 ]; load m64 x1 to register64
imul rbp, rbx, 0x2; x2 <- x1 * 0x2
imul r12, r11, 0x2; x8 <- x7 * 0x2
imul r12, r12, 0x2; x10005 <- x8 * 0x2
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r13, r14, [ rsi + 0x0 ]; x106, x105<- arg1[0] * arg1[0]
mov r15, [ rsi + 0x28 ]; load m64 x10 to register64
imul r10, r10, 0x2; x10003 <- x5 * 0x2
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rcx, r8, r12; x52, x51<- arg1[3] * x10005
imul rbp, rbp, 0x2; x10001 <- x2 * 0x2
mov rdx, r10; x10003 to rdx
mulx r10, r9, [ rsi + 0x10 ]; x62, x61<- arg1[2] * x10003
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov rdi, rdx; preserving value of x10003 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x8 ], rbx; spilling x1 to mem
mov [ rsp + 0x10 ], rax; spilling x4 to mem
mulx rbx, rax, rbp; x74, x73<- arg1[1] * x10001
imul rdx, r15, 0x2; x11 <- x10 * 0x2
imul rdx, rdx, 0x2; x10007 <- x11 * 0x2
mov [ rsp + 0x18 ], r11; spilling x7 to mem
mulx rdx, r11, [ rsi + 0x20 ]; x44, x43<- arg1[4] * x10007
test al, al
adox r11, r8
adox rcx, rdx
adcx r11, r9
adcx r10, rcx
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r8, r9, rbp; x60, x59<- arg1[2] * x10001
mov rdx, r12; x10005 to rdx
mulx r12, rcx, [ rsi + 0x20 ]; x42, x41<- arg1[4] * x10005
test al, al
adox r11, rax
adcx r11, r14
adox rbx, r10
adcx r13, rbx
imul r14, [ rsi + 0x8 ], 0x2; x16 <- arg1[1] * 0x2
mov rax, rdx; preserving value of x10005 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx r10, rbx, rdi; x50, x49<- arg1[3] * x10003
imul r15, r15, 0x2; x10006 <- x10 * 0x2
mov rdx, r15; x10006 to rdx
mulx rdx, r15, [ rsi + 0x28 ]; x36, x35<- arg1[5] * x10006
test al, al
adox r15, rcx
adcx r15, rbx
adox r12, rdx
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, r9
adcx r10, r12
adox r8, r10
mov r9, r13; x124, copying x121 here, cause x121 is needed in a reg for other than x124, namely all: , x124, x123, size: 2
shr r9, 58; x124 <- x121>> 58
mov rdx, rbp; x10001 to rdx
mulx rbp, rbx, [ rsi + 0x18 ]; x48, x47<- arg1[3] * x10001
mov r12, rdx; preserving value of x10001 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r14, r10, r14; x104, x103<- arg1[0] * x16
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x20 ], rbp; spilling x48 to mem
mulx rcx, rbp, rdi; x40, x39<- arg1[4] * x10003
mov rdx, r11; x123, copying x119 here, cause x119 is needed in a reg for other than x123, namely all: , x125, x123, size: 2
shrd rdx, r13, 58; x123 <- x121||x119 >> 58
test al, al
adox r15, r10
adox r14, r8
imul r13, [ rsi + 0x10 ], 0x2; x15 <- arg1[2] * 0x2
add r15, rdx; could be done better, if r0 has been u8 as well
adcx r9, r14
mov r8, r15; x258, copying x254 here, cause x254 is needed in a reg for other than x258, namely all: , x258, x260, size: 2
shrd r8, r9, 58; x258 <- x256||x254 >> 58
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r10, r14, [ rsi + 0x8 ]; x88, x87<- arg1[1] * arg1[1]
mov rdx, rax; x10005 to rdx
mulx rdx, rax, [ rsi + 0x28 ]; x34, x33<- arg1[5] * x10005
add rax, rbp; could be done better, if r0 has been u8 as well
adcx rcx, rdx
xor rbp, rbp
adox rax, rbx
adcx rax, r14
adox rcx, [ rsp + 0x20 ]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbx, r14, r13; x86, x85<- arg1[1] * x15
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x28 ], rbx; spilling x86 to mem
mulx rbp, rbx, rdi; x32, x31<- arg1[5] * x10003
adcx r10, rcx
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r13, rcx, r13; x102, x101<- arg1[0] * x15
test al, al
adox rax, rcx
adox r13, r10
shr r9, 58; x259 <- x256>> 58
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r10, rcx, r12; x38, x37<- arg1[4] * x10001
imul rdx, [ rsi + 0x28 ], 0x2; x12 <- arg1[5] * 0x2
mov [ rsp + 0x30 ], rdx; spilling x12 to mem
imul rdx, [ rsp + 0x18 ], 0x2; x10004 <- x7 * 0x2
mov [ rsp + 0x38 ], r10; spilling x38 to mem
imul r10, [ rsi + 0x18 ], 0x2; x14 <- arg1[3] * 0x2
add rax, r8; could be done better, if r0 has been u8 as well
adcx r9, r13
mulx rdx, r8, [ rsi + 0x30 ]; x28, x27<- arg1[6] * x10004
mov r13, rax; x265, copying x261 here, cause x261 is needed in a reg for other than x265, namely all: , x265, x267, size: 2
shrd r13, r9, 58; x265 <- x263||x261 >> 58
add r8, rbx; could be done better, if r0 has been u8 as well
adcx rbp, rdx
shr r9, 58; x266 <- x263>> 58
mov rbx, 0x3ffffffffffffff ; moving imm to reg
and r11, rbx; x125 <- x119&0x3ffffffffffffff
mov rdx, r10; x14 to rdx
mulx r10, rbx, [ rsi + 0x0 ]; x100, x99<- arg1[0] * x14
adox r8, rcx
mov rcx, rdx; preserving value of x14 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0x40 ], r11; spilling x125 to mem
mulx rdi, r11, rdi; x26, x25<- arg1[6] * x10003
adcx r8, r14
adox rbp, [ rsp + 0x38 ]
adcx rbp, [ rsp + 0x28 ]
add r8, rbx; could be done better, if r0 has been u8 as well
adcx r10, rbp
xor rdx, rdx
adox r8, r13
mov r14, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx r13, rbx, r12; x30, x29<- arg1[5] * x10001
adox r9, r10
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rbp, r10, [ rsi + 0x10 ]; x72, x71<- arg1[2] * arg1[2]
mov rdx, 0x3ffffffffffffff ; moving imm to reg
mov r14, r8; x274, copying x268 here, cause x268 is needed in a reg for other than x274, namely all: , x274, x272, size: 2
and r14, rdx; x274 <- x268&0x3ffffffffffffff
mov rdx, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rdx + 0x18 ], r14; out1[3] = x274
imul r14, [ rsi + 0x20 ], 0x2; x13 <- arg1[4] * 0x2
shrd r8, r9, 58; x272 <- x270||x268 >> 58
mov [ rsp + 0x0 ], rdx; spilling out1 to mem
xor rdx, rdx
adox r11, rbx
adcx r11, r10
adox r13, rdi
adcx rbp, r13
mov rdi, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx rbx, r10, [ rsp + 0x30 ]; x96, x95<- arg1[0] * x12
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r13, rdi, rcx; x84, x83<- arg1[1] * x14
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x48 ], rbx; spilling x96 to mem
mov [ rsp + 0x50 ], r10; spilling x95 to mem
mulx rbx, r10, r14; x82, x81<- arg1[1] * x13
add r11, rdi; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x58 ], rbx; spilling x82 to mem
mulx rdi, rbx, r14; x98, x97<- arg1[0] * x13
adcx r13, rbp
shr r9, 58; x273 <- x270>> 58
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x60 ], r10; spilling x81 to mem
mulx rbp, r10, r12; x24, x23<- arg1[6] * x10001
add r11, rbx; could be done better, if r0 has been u8 as well
adcx rdi, r13
imul rdx, [ rsp + 0x10 ], 0x2; x10002 <- x4 * 0x2
mulx rdx, rbx, [ rsi + 0x38 ]; x22, x21<- arg1[7] * x10002
test al, al
adox r11, r8
adcx rbx, r10
adox r9, rdi
adcx rbp, rdx
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rcx, r8, rcx; x70, x69<- arg1[2] * x14
xor rdx, rdx
adox rbx, r8
adox rcx, rbp
imul r13, [ rsi + 0x30 ], 0x2; x9 <- arg1[6] * 0x2
mov r10, r11; x279, copying x275 here, cause x275 is needed in a reg for other than x279, namely all: , x281, x279, size: 2
shrd r10, r9, 58; x279 <- x277||x275 >> 58
add rbx, [ rsp + 0x60 ]; could be done better, if r0 has been u8 as well
adcx rcx, [ rsp + 0x58 ]
shr r9, 58; x280 <- x277>> 58
mov rdi, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx rbp, r8, r13; x94, x93<- arg1[0] * x9
add rbx, [ rsp + 0x50 ]; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx r12, rdi, r12; x20, x19<- arg1[7] * x10001
adcx rcx, [ rsp + 0x48 ]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x68 ], rbp; spilling x94 to mem
mov [ rsp + 0x70 ], r8; spilling x93 to mem
mulx rbp, r8, [ rsi + 0x18 ]; x58, x57<- arg1[3] * arg1[3]
add rbx, r10; could be done better, if r0 has been u8 as well
adcx r9, rcx
add rdi, r8; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r10, rcx, r14; x68, x67<- arg1[2] * x13
adcx rbp, r12
test al, al
adox rdi, rcx
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r12, r8, [ rsp + 0x30 ]; x80, x79<- arg1[1] * x12
adox r10, rbp
mov rdx, rbx; x286, copying x282 here, cause x282 is needed in a reg for other than x286, namely all: , x288, x286, size: 2
shrd rdx, r9, 58; x286 <- x284||x282 >> 58
xor rcx, rcx
adox rdi, r8
mov rbp, rdx; preserving value of x286 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx r14, r8, r14; x56, x55<- arg1[3] * x13
adcx rdi, [ rsp + 0x70 ]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x78 ], r15; spilling x254 to mem
mulx rcx, r15, r13; x78, x77<- arg1[1] * x9
adox r12, r10
adcx r12, [ rsp + 0x68 ]
shr r9, 58; x287 <- x284>> 58
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x80 ], rcx; spilling x78 to mem
mulx r10, rcx, [ rsp + 0x30 ]; x66, x65<- arg1[2] * x12
add rdi, rbp; could be done better, if r0 has been u8 as well
adcx r9, r12
mov rdx, rdi; x293, copying x289 here, cause x289 is needed in a reg for other than x293, namely all: , x293, x295, size: 2
shrd rdx, r9, 58; x293 <- x291||x289 >> 58
imul rbp, [ rsp + 0x8 ], 0x2; x10000 <- x1 * 0x2
imul r12, [ rsi + 0x38 ], 0x2; x6 <- arg1[7] * 0x2
mov [ rsp + 0x88 ], r15; spilling x77 to mem
mov r15, rdx; preserving value of x293 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x90 ], r10; spilling x66 to mem
mulx r13, r10, r13; x64, x63<- arg1[2] * x9
mov rdx, [ rsi + 0x40 ]; arg1[8] to rdx
mov [ rsp + 0x98 ], r13; spilling x64 to mem
mulx rbp, r13, rbp; x18, x17<- arg1[8] * x10000
mov rdx, r12; x6 to rdx
mov [ rsp + 0xa0 ], r10; spilling x63 to mem
mulx r12, r10, [ rsi + 0x0 ]; x92, x91<- arg1[0] * x6
test al, al
adox r13, r8
adox r14, rbp
adcx r13, rcx
adcx r14, [ rsp + 0x90 ]
xor r8, r8
adox r13, [ rsp + 0x88 ]
adox r14, [ rsp + 0x80 ]
imul rcx, [ rsi + 0x40 ], 0x2; x3 <- arg1[8] * 0x2
shr r9, 58; x294 <- x291>> 58
add r13, r10; could be done better, if r0 has been u8 as well
adcx r12, r14
mov rbp, rdx; preserving value of x6 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx rcx, r10, rcx; x90, x89<- arg1[0] * x3
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r14, r8, [ rsi + 0x20 ]; x46, x45<- arg1[4] * arg1[4]
add r13, r15; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbp, r15, rbp; x76, x75<- arg1[1] * x6
mov rdx, [ rsp + 0x30 ]; x12 to rdx
mov [ rsp + 0xa8 ], rcx; spilling x90 to mem
mulx rdx, rcx, [ rsi + 0x18 ]; x54, x53<- arg1[3] * x12
adcx r9, r12
mov r12, r13; x300, copying x296 here, cause x296 is needed in a reg for other than x300, namely all: , x302, x300, size: 2
shrd r12, r9, 58; x300 <- x298||x296 >> 58
test al, al
adox r8, rcx
adox rdx, r14
adcx r8, [ rsp + 0xa0 ]
adcx rdx, [ rsp + 0x98 ]
add r8, r15; could be done better, if r0 has been u8 as well
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, r10
adcx rbp, rdx
adox rbp, [ rsp + 0xa8 ]
shr r9, 58; x301 <- x298>> 58
xor r10, r10
adox r8, r12
adox r9, rbp
mov r15, r9; x308, copying x305 here, cause x305 is needed in a reg for other than x308, namely all: , x308, x307, size: 2
shr r15, 57; x308 <- x305>> 57
mov rcx, 0x3ffffffffffffff ; moving imm to reg
and rax, rcx; x267 <- x261&0x3ffffffffffffff
mov r12, r8; x307, copying x303 here, cause x303 is needed in a reg for other than x307, namely all: , x307, x309, size: 2
shrd r12, r9, 57; x307 <- x305||x303 >> 57
xor rdx, rdx
adox r12, [ rsp + 0x40 ]
adox r15, rdx
mov r10, r12; x313, copying x310 here, cause x310 is needed in a reg for other than x313, namely all: , x314, x313, size: 2
shrd r10, r15, 58; x313 <- x312||x310 >> 58
mov rbp, [ rsp + 0x78 ]; x260, copying x254 here, cause x254 is needed in a reg for other than x260, namely all: , x260, size: 1
and rbp, rcx; x260 <- x254&0x3ffffffffffffff
and r12, rcx; x314 <- x310&0x3ffffffffffffff
lea r10, [ r10 + rbp ]
and r13, rcx; x302 <- x296&0x3ffffffffffffff
mov r9, r10; x316, copying x315 here, cause x315 is needed in a reg for other than x316, namely all: , x317, x316, size: 2
shr r9, 58; x316 <- x315>> 58
lea r9, [ r9 + rax ]
mov rax, 0x1ffffffffffffff ; moving imm to reg
and r8, rax; x309 <- x303&0x1ffffffffffffff
and rdi, rcx; x295 <- x289&0x3ffffffffffffff
mov r15, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r15 + 0x38 ], r13; out1[7] = x302
mov [ r15 + 0x10 ], r9; out1[2] = x318
and r11, rcx; x281 <- x275&0x3ffffffffffffff
mov [ r15 + 0x40 ], r8; out1[8] = x309
mov [ r15 + 0x0 ], r12; out1[0] = x314
mov [ r15 + 0x20 ], r11; out1[4] = x281
mov [ r15 + 0x30 ], rdi; out1[6] = x295
and rbx, rcx; x288 <- x282&0x3ffffffffffffff
mov [ r15 + 0x28 ], rbx; out1[5] = x288
and r10, rcx; x317 <- x315&0x3ffffffffffffff
mov [ r15 + 0x8 ], r10; out1[1] = x317
mov rbx, [ rsp + 0xb0 ]; restoring from stack
mov rbp, [ rsp + 0xb8 ]; restoring from stack
mov r12, [ rsp + 0xc0 ]; restoring from stack
mov r13, [ rsp + 0xc8 ]; restoring from stack
mov r14, [ rsp + 0xd0 ]; restoring from stack
mov r15, [ rsp + 0xd8 ]; restoring from stack
add rsp, 0xe0 
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; clocked at 4801 MHz
; first cyclecount 120.735, best 88.64864864864865, lastGood 90.5
; seed 2097618098035895 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1393629 ms / 60000 runs=> 23.22715ms/run
; Time spent for assembling and measureing (initial batch_size=73, initial num_batches=101): 110802 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.0795060952376852
; number reverted permutation/ tried permutation: 22627 / 29866 =75.762%
; number reverted decision/ tried decision: 22276 / 30135 =73.921%