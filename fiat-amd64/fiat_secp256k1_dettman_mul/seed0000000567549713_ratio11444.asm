SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
mov rax, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x0 ]; saving arg2[0] in rdx.
mulx r11, r10, [ rsi + 0x18 ]; x10003_1, x10003_0<- arg1[3] * arg2[0] (_0*_0)
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx r8, rcx, [ rsi + 0x10 ]; x10002_1, x10002_0<- arg1[2] * arg2[1] (_0*_0)
xor rdx, rdx
adox r10, rcx
adox r8, r11
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx r11, r9, [ rsi + 0x20 ]; x1_1, x1_0<- arg1[4] * arg2[4] (_0*_0)
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp - 0x80 ], rbx; spilling calSv-rbx to mem
mulx rbx, rcx, [ rax + 0x8 ]; x10011_1, x10011_0<- arg1[3] * arg2[1] (_0*_0)
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp - 0x78 ], rbp; spilling calSv-rbp to mem
mov [ rsp - 0x70 ], r12; spilling calSv-r12 to mem
mulx r12, rbp, [ rax + 0x18 ]; x10031_1, x10031_0<- arg1[3] * arg2[3] (_0*_0)
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp - 0x68 ], r13; spilling calSv-r13 to mem
mov [ rsp - 0x60 ], r14; spilling calSv-r14 to mem
mulx r14, r13, [ rsi + 0x8 ]; x10001_1, x10001_0<- arg1[1] * arg2[2] (_0*_0)
adcx r10, r13
adcx r14, r8
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r13, r8, [ rax + 0x18 ]; x10000_1, x10000_0<- arg1[0] * arg2[3] (_0*_0)
test al, al
adox r10, r8
adox r13, r14
mov rdx, 0x1000003d10 ; moving imm to reg
mulx r8, r14, r9; x10007_1, x10007_0<- x3 * 0x1000003d10 (_0*_0)
adcx r14, r10
adcx r13, r8
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx r9, r10, [ rsi + 0x20 ]; x10012_1, x10012_0<- arg1[4] * arg2[0] (_0*_0)
xor rdx, rdx
adox r10, rcx
adox rbx, r9
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r8, rcx, [ rax + 0x10 ]; x10043_1, x10043_0<- arg1[0] * arg2[2] (_0*_0)
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp - 0x58 ], r15; spilling calSv-r15 to mem
mulx r15, r9, [ rax + 0x10 ]; x10010_1, x10010_0<- arg1[2] * arg2[2] (_0*_0)
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp - 0x50 ], rdi; spilling out1 to mem
mov [ rsp - 0x48 ], r8; spilling x10043_1 to mem
mulx r8, rdi, [ rax + 0x20 ]; x10008_1, x10008_0<- arg1[0] * arg2[4] (_0*_0)
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp - 0x40 ], rcx; spilling x10043_0 to mem
mov [ rsp - 0x38 ], r12; spilling x10031_1 to mem
mulx r12, rcx, [ rsi + 0x8 ]; x10009_1, x10009_0<- arg1[1] * arg2[3] (_0*_0)
adcx r10, r9
adcx r15, rbx
add r10, rcx; could be done better, if r0 has been u8 as well
adcx r12, r15
mov rdx, r14;
shrd rdx, r13, 52; x5 <- x4_1||x4_0 >> 52
mov r13, 0xfffffffffffff ; moving imm to reg
and r14, r13; x6 <- x4_0&0xfffffffffffff
adox r10, rdi
adox r8, r12
adcx rdx, r10
adc r8, 0x0; add CF to r0's alloc
mov rbx, rdx; preserving value of x10017_0 into a new reg
mov rdx, [ rax + 0x10 ]; saving arg2[2] in rdx.
mulx rdi, r9, [ rsi + 0x18 ]; x10021_1, x10021_0<- arg1[3] * arg2[2] (_0*_0)
mov rdx, 0x1000003d10000 ; moving imm to reg
mulx r15, rcx, r11; x10018_1, x10018_0<- x2 * 0x1000003d10000 (_0*_0)
add rcx, rbx; could be done better, if r0 has been u8 as well
adcx r8, r15
mov r11, rcx;
and r11, r13; x9 <- x7_0&0xfffffffffffff
shrd rcx, r8, 52; x8 <- x7_1||x7_0 >> 52
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx r10, r12, [ rsi + 0x8 ]; x10019_1, x10019_0<- arg1[1] * arg2[4] (_0*_0)
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r15, rbx, [ rax + 0x8 ]; x10022_1, x10022_0<- arg1[4] * arg2[1] (_0*_0)
add rbx, r9; could be done better, if r0 has been u8 as well
adcx rdi, r15
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r8, r9, [ rax + 0x18 ]; x10020_1, x10020_0<- arg1[2] * arg2[3] (_0*_0)
xor rdx, rdx
adox rbx, r9
adox r8, rdi
adcx rbx, r12
adcx r10, r8
xor r12, r12
adox rcx, rbx
adox r10, r12
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx rdi, r15, [ rsi + 0x20 ]; x10032_1, x10032_0<- arg1[4] * arg2[2] (_0*_0)
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx r8, r9, [ rsi + 0x10 ]; x10030_1, x10030_0<- arg1[2] * arg2[4] (_0*_0)
mov rdx, rcx;
and rdx, r13; x14 <- x12_0&0xfffffffffffff
mov rbx, 0xffffffffffff ; moving imm to reg
mov r12, r11;
and r12, rbx; x11 <- x9&0xffffffffffff
shl rdx, 4; x10027 <- x14<< 4
shrd rcx, r10, 52; x13 <- x12_1||x12_0 >> 52
shr r11, 48; x10 <- x9>> 48
mov r10, rdx; preserving value of x10027 into a new reg
mov rdx, [ rax + 0x0 ]; saving arg2[0] in rdx.
mulx r13, rbx, [ rsi + 0x0 ]; x10026_1, x10026_0<- arg1[0] * arg2[0] (_0*_0)
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp - 0x30 ], r12; spilling x11 to mem
mov [ rsp - 0x28 ], r14; spilling x6 to mem
mulx r14, r12, [ rsi + 0x18 ]; x10040_1, x10040_0<- arg1[3] * arg2[4] (_0*_0)
lea r10, [ r10 + r11 ]
xor rdx, rdx
adox r15, rbp
adox rdi, [ rsp - 0x38 ]
adcx r15, r9
adcx r8, rdi
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r9, rbp, [ rax + 0x18 ]; x10041_1, x10041_0<- arg1[4] * arg2[3] (_0*_0)
xor rdx, rdx
adox rbp, r12
adox r14, r9
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx r12, r11, [ rsi + 0x10 ]; x10045_1, x10045_0<- arg1[2] * arg2[0] (_0*_0)
mov rdx, 0x1000003d1 ; moving imm to reg
mulx r9, rdi, r10; x10029_1, x10029_0<- x10028 * 0x1000003d1 (_0*_0)
adcx rdi, rbx
adcx r13, r9
add rcx, r15; could be done better, if r0 has been u8 as well
adc r8, 0x0; add CF to r0's alloc
mov rbx, rdi;
shrd rbx, r13, 52; x16 <- x15_1||x15_0 >> 52
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r15, r10, [ rax + 0x8 ]; x10044_1, x10044_0<- arg1[1] * arg2[1] (_0*_0)
mov rdx, rcx;
shrd rdx, r8, 52; x19 <- x18_1||x18_0 >> 52
xor r9, r9
adox rdx, rbp
adox r14, r9
adcx r11, r10
adcx r15, r12
mov rbp, rdx; preserving value of x24_0 into a new reg
mov rdx, [ rax + 0x0 ]; saving arg2[0] in rdx.
mulx r13, r12, [ rsi + 0x8 ]; x10036_1, x10036_0<- arg1[1] * arg2[0] (_0*_0)
test al, al
adox r11, [ rsp - 0x40 ]
adox r15, [ rsp - 0x48 ]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r10, r8, [ rax + 0x8 ]; x10035_1, x10035_0<- arg1[0] * arg2[1] (_0*_0)
mov rdx, 0x1000003d10 ; moving imm to reg
mov [ rsp - 0x20 ], r15; spilling x10047_1 to mem
mulx r15, r9, rbp; x10049_1, x10049_0<- x26 * 0x1000003d10 (_0*_0)
adcx r12, r8
adcx r10, r13
xor r13, r13
adox rbx, r12
adox r10, r13
mov rbp, 0xfffffffffffff ; moving imm to reg
and rcx, rbp; x20 <- x18_0&0xfffffffffffff
mulx r12, r8, rcx; x10039_1, x10039_0<- x20 * 0x1000003d10 (_0*_0)
adox r8, rbx
adox r10, r12
mov rbx, r8;
shrd rbx, r10, 52; x22 <- x21_1||x21_0 >> 52
and r8, rbp; x23 <- x21_0&0xfffffffffffff
adox rbx, r11
mov rcx, [ rsp - 0x20 ];
adox rcx, r13
adcx r9, rbx
adcx rcx, r15
mov r11, r9;
shrd r11, rcx, 52; x28 <- x27_1||x27_0 >> 52
and r9, rbp; x29 <- x27_0&0xfffffffffffff
add r11, [ rsp - 0x28 ]
mov r15, 0x1000003d10000 ; moving imm to reg
mov rdx, r15; 0x1000003d10000 to rdx
mulx r12, r15, r14; x10051_1, x10051_0<- x25 * 0x1000003d10000 (_0*_0)
xor r10, r10
adox r15, r11
adox r12, r10
mov r13, r15;
shrd r13, r12, 52; x31 <- x30_1||x30_0 >> 52
add r13, [ rsp - 0x30 ]
and rdi, rbp; x17 <- x15_0&0xfffffffffffff
mov rbx, [ rsp - 0x50 ]; load m64 out1 to register64
mov [ rbx + 0x20 ], r13; out1[4] = x33
mov [ rbx + 0x0 ], rdi; out1[0] = x17
mov [ rbx + 0x10 ], r9; out1[2] = x29
and r15, rbp; x32 <- x30_0&0xfffffffffffff
mov [ rbx + 0x8 ], r8; out1[1] = x23
mov [ rbx + 0x18 ], r15; out1[3] = x32
mov rbx, [ rsp - 0x80 ]; pop
mov rbp, [ rsp - 0x78 ]; pop
mov r12, [ rsp - 0x70 ]; pop
mov r13, [ rsp - 0x68 ]; pop
mov r14, [ rsp - 0x60 ]; pop
mov r15, [ rsp - 0x58 ]; pop
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.1444
; seed 2016940727727389 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1494164 ms on 270000 evaluations.
; Time spent for assembling and measuring (initial batch_size=288, initial num_batches=31): 140939 ms
; number of used evaluations: 270000
; Ratio (time for assembling + measure)/(total runtime for 270000 evals): 0.09432632562422867
; number reverted permutation / tried permutation: 99139 / 135478 =73.177%
; number reverted decision / tried decision: 77995 / 134521 =57.980%
; validated in 0.294s
