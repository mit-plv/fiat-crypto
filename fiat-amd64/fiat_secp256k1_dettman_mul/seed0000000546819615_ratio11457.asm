SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
mov rax, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x10 ]; saving arg2[2] in rdx.
mulx r11, r10, [ rsi + 0x8 ]; x10001_1, x10001_0<- arg1[1] * arg2[2] (_0*_0)
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r8, rcx, [ rax + 0x20 ]; x10008_1, x10008_0<- arg1[0] * arg2[4] (_0*_0)
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp - 0x80 ], rbx; spilling calSv-rbx to mem
mulx rbx, r9, [ rax + 0x10 ]; x10043_1, x10043_0<- arg1[0] * arg2[2] (_0*_0)
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mov [ rsp - 0x78 ], rbp; spilling calSv-rbp to mem
mov [ rsp - 0x70 ], r12; spilling calSv-r12 to mem
mulx r12, rbp, [ rsi + 0x18 ]; x10003_1, x10003_0<- arg1[3] * arg2[0] (_0*_0)
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp - 0x68 ], r13; spilling calSv-r13 to mem
mov [ rsp - 0x60 ], r14; spilling calSv-r14 to mem
mulx r14, r13, [ rax + 0x8 ]; x10002_1, x10002_0<- arg1[2] * arg2[1] (_0*_0)
xor rdx, rdx
adox rbp, r13
adox r14, r12
adcx rbp, r10
adcx r11, r14
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mulx r12, r10, [ rsi + 0x0 ]; x10000_1, x10000_0<- arg1[0] * arg2[3] (_0*_0)
xor rdx, rdx
adox rbp, r10
adox r12, r11
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx r14, r13, [ rsi + 0x20 ]; x1_1, x1_0<- arg1[4] * arg2[4] (_0*_0)
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx r10, r11, [ rsi + 0x18 ]; x10011_1, x10011_0<- arg1[3] * arg2[1] (_0*_0)
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mov [ rsp - 0x58 ], r15; spilling calSv-r15 to mem
mov [ rsp - 0x50 ], rdi; spilling out1 to mem
mulx rdi, r15, [ rsi + 0x20 ]; x10012_1, x10012_0<- arg1[4] * arg2[0] (_0*_0)
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp - 0x48 ], rbx; spilling x10043_1 to mem
mov [ rsp - 0x40 ], r9; spilling x10043_0 to mem
mulx r9, rbx, [ rsi + 0x10 ]; x10010_1, x10010_0<- arg1[2] * arg2[2] (_0*_0)
adcx r15, r11
adcx r10, rdi
add r15, rbx; could be done better, if r0 has been u8 as well
adcx r9, r10
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mulx rdi, r11, [ rsi + 0x8 ]; x10009_1, x10009_0<- arg1[1] * arg2[3] (_0*_0)
mov rdx, 0x1000003d10 ; moving imm to reg
mulx r10, rbx, r13; x10007_1, x10007_0<- x3 * 0x1000003d10 (_0*_0)
add rbx, rbp; could be done better, if r0 has been u8 as well
adcx r12, r10
test al, al
adox r15, r11
adox rdi, r9
adcx r15, rcx
adcx r8, rdi
mov rcx, rbx;
shrd rcx, r12, 52; x5 <- x4_1||x4_0 >> 52
xor rbp, rbp
adox rcx, r15
adox r8, rbp
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mulx r9, r13, [ rsi + 0x10 ]; x10020_1, x10020_0<- arg1[2] * arg2[3] (_0*_0)
mov rdx, 0x1000003d10000 ; moving imm to reg
mulx r10, r11, r14; x10018_1, x10018_0<- x2 * 0x1000003d10000 (_0*_0)
adcx r11, rcx
adcx r8, r10
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx rdi, r12, [ rsi + 0x20 ]; x10022_1, x10022_0<- arg1[4] * arg2[1] (_0*_0)
mov rdx, 0xfffffffffffff ; moving imm to reg
mov r15, r11;
and r15, rdx; x9 <- x7_0&0xfffffffffffff
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rcx, r14, [ rax + 0x10 ]; x10021_1, x10021_0<- arg1[3] * arg2[2] (_0*_0)
shrd r11, r8, 52; x8 <- x7_1||x7_0 >> 52
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx r8, r10, [ rsi + 0x8 ]; x10019_1, x10019_0<- arg1[1] * arg2[4] (_0*_0)
add r12, r14; could be done better, if r0 has been u8 as well
adcx rcx, rdi
test al, al
adox r12, r13
adox r9, rcx
adcx r12, r10
adcx r8, r9
test al, al
adox r11, r12
adox r8, rbp
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mulx rdi, r13, [ rsi + 0x18 ]; x10031_1, x10031_0<- arg1[3] * arg2[3] (_0*_0)
mov rdx, 0xfffffffffffff ; moving imm to reg
mov r14, r11;
and r14, rdx; x14 <- x12_0&0xfffffffffffff
shl r14, 4; x10027 <- x14<< 4
shrd r11, r8, 52; x13 <- x12_1||x12_0 >> 52
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx rcx, r10, [ rsi + 0x20 ]; x10032_1, x10032_0<- arg1[4] * arg2[2] (_0*_0)
add r10, r13; could be done better, if r0 has been u8 as well
adcx rdi, rcx
mov rdx, r15;
shr rdx, 48; x10 <- x9>> 48
lea r14, [ r14 + rdx ]
mov r9, 0xffffffffffff ; moving imm to reg
and r15, r9; x11 <- x9&0xffffffffffff
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r8, r12, [ rax + 0x20 ]; x10030_1, x10030_0<- arg1[2] * arg2[4] (_0*_0)
mov rdx, 0x1000003d1 ; moving imm to reg
mulx rcx, r13, r14; x10029_1, x10029_0<- x10028 * 0x1000003d1 (_0*_0)
adox r10, r12
adox r8, rdi
adcx r11, r10
adc r8, 0x0; add CF to r0's alloc
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx r14, rdi, [ rsi + 0x0 ]; x10026_1, x10026_0<- arg1[0] * arg2[0] (_0*_0)
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r10, r12, [ rax + 0x20 ]; x10040_1, x10040_0<- arg1[3] * arg2[4] (_0*_0)
add r13, rdi; could be done better, if r0 has been u8 as well
adcx r14, rcx
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rdi, rcx, [ rax + 0x8 ]; x10044_1, x10044_0<- arg1[1] * arg2[1] (_0*_0)
mov rdx, r13;
shrd rdx, r14, 52; x16 <- x15_1||x15_0 >> 52
mov r14, rdx; preserving value of x16 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r9, rbp, [ rax + 0x18 ]; x10041_1, x10041_0<- arg1[4] * arg2[3] (_0*_0)
mov rdx, r11;
shrd rdx, r8, 52; x19 <- x18_1||x18_0 >> 52
test al, al
adox rbp, r12
adox r10, r9
adcx rdx, rbp
adc r10, 0x0; add CF to r0's alloc
mov r8, rdx; preserving value of x24_0 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r9, r12, [ rax + 0x0 ]; x10045_1, x10045_0<- arg1[2] * arg2[0] (_0*_0)
mov rdx, 0x1000003d10000 ; moving imm to reg
mov [ rsp - 0x38 ], r15; spilling x11 to mem
mulx r15, rbp, r10; x10051_1, x10051_0<- x25 * 0x1000003d10000 (_0*_0)
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp - 0x30 ], r15; spilling x10051_1 to mem
mulx r15, r10, [ rax + 0x0 ]; x10036_1, x10036_0<- arg1[1] * arg2[0] (_0*_0)
xor rdx, rdx
adox r12, rcx
adox rdi, r9
mov rcx, 0xfffffffffffff ; moving imm to reg
and r13, rcx; x17 <- x15_0&0xfffffffffffff
and r11, rcx; x20 <- x18_0&0xfffffffffffff
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rcx, r9, [ rax + 0x8 ]; x10035_1, x10035_0<- arg1[0] * arg2[1] (_0*_0)
adox r10, r9
adox rcx, r15
mov rdx, 0x1000003d10 ; moving imm to reg
mulx r9, r15, r11; x10039_1, x10039_0<- x20 * 0x1000003d10 (_0*_0)
mov r11, [ rsp - 0x50 ]; load m64 out1 to register64
mov [ r11 + 0x0 ], r13; out1[0] = x17
adcx r14, r10
adc rcx, 0x0; add CF to r0's alloc
xor r13, r13
adox r15, r14
adox rcx, r9
mov r10, 0xfffffffffffff ; moving imm to reg
mov r9, r15;
and r9, r10; x23 <- x21_0&0xfffffffffffff
mov [ r11 + 0x8 ], r9; out1[1] = x23
shrd r15, rcx, 52; x22 <- x21_1||x21_0 >> 52
mulx rcx, r14, r8; x10049_1, x10049_0<- x26 * 0x1000003d10 (_0*_0)
test al, al
adox r12, [ rsp - 0x40 ]
adox rdi, [ rsp - 0x48 ]
adcx r15, r12
adc rdi, 0x0; add CF to r0's alloc
and rbx, r10; x6 <- x4_0&0xfffffffffffff
adox r14, r15
adox rdi, rcx
mov r9, r14;
shrd r9, rdi, 52; x28 <- x27_1||x27_0 >> 52
and r14, r10; x29 <- x27_0&0xfffffffffffff
lea rbx, [ rbx + r9 ]
adox rbp, rbx
mov r8, [ rsp - 0x30 ];
adox r8, r13
mov rcx, rbp;
and rcx, r10; x32 <- x30_0&0xfffffffffffff
shrd rbp, r8, 52; x31 <- x30_1||x30_0 >> 52
add rbp, [ rsp - 0x38 ]
mov [ r11 + 0x20 ], rbp; out1[4] = x33
mov [ r11 + 0x18 ], rcx; out1[3] = x32
mov [ r11 + 0x10 ], r14; out1[2] = x29
mov rbx, [ rsp - 0x80 ]; pop
mov rbp, [ rsp - 0x78 ]; pop
mov r12, [ rsp - 0x70 ]; pop
mov r13, [ rsp - 0x68 ]; pop
mov r14, [ rsp - 0x60 ]; pop
mov r15, [ rsp - 0x58 ]; pop
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.1457
; seed 3723633933296103 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1524788 ms on 270000 evaluations.
; Time spent for assembling and measuring (initial batch_size=300, initial num_batches=31): 141202 ms
; number of used evaluations: 270000
; Ratio (time for assembling + measure)/(total runtime for 270000 evals): 0.09260434893244175
; number reverted permutation / tried permutation: 97325 / 135466 =71.845%
; number reverted decision / tried decision: 78133 / 134533 =58.077%
; validated in 0.276s
