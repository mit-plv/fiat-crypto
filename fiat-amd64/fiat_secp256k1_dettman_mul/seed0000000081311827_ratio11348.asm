SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
mov rax, rdx; preserving value of arg2 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r11, r10, [ rax + 0x0 ]; x10012_1, x10012_0<- arg1[4] * arg2[0] (_0*_0)
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx r8, rcx, [ rsi + 0x18 ]; x10003_1, x10003_0<- arg1[3] * arg2[0] (_0*_0)
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp - 0x80 ], rbx; spilling calSv-rbx to mem
mulx rbx, r9, [ rax + 0x10 ]; x10010_1, x10010_0<- arg1[2] * arg2[2] (_0*_0)
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp - 0x78 ], rbp; spilling calSv-rbp to mem
mov [ rsp - 0x70 ], r12; spilling calSv-r12 to mem
mulx r12, rbp, [ rsi + 0x10 ]; x10002_1, x10002_0<- arg1[2] * arg2[1] (_0*_0)
xor rdx, rdx
adox rcx, rbp
adox r12, r8
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx rbp, r8, [ rax + 0x20 ]; x1_1, x1_0<- arg1[4] * arg2[4] (_0*_0)
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp - 0x68 ], r13; spilling calSv-r13 to mem
mov [ rsp - 0x60 ], r14; spilling calSv-r14 to mem
mulx r14, r13, [ rsi + 0x18 ]; x10011_1, x10011_0<- arg1[3] * arg2[1] (_0*_0)
adcx r10, r13
adcx r14, r11
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r13, r11, [ rax + 0x10 ]; x10001_1, x10001_0<- arg1[1] * arg2[2] (_0*_0)
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp - 0x58 ], r15; spilling calSv-r15 to mem
mov [ rsp - 0x50 ], rdi; spilling out1 to mem
mulx rdi, r15, [ rsi + 0x0 ]; x10000_1, x10000_0<- arg1[0] * arg2[3] (_0*_0)
add rcx, r11; could be done better, if r0 has been u8 as well
adcx r13, r12
add rcx, r15; could be done better, if r0 has been u8 as well
adcx rdi, r13
mov rdx, 0x1000003d10 ; moving imm to reg
mulx r11, r12, r8; x10007_1, x10007_0<- x3 * 0x1000003d10 (_0*_0)
add r12, rcx; could be done better, if r0 has been u8 as well
adcx rdi, r11
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mulx r13, r15, [ rsi + 0x8 ]; x10009_1, x10009_0<- arg1[1] * arg2[3] (_0*_0)
mov rdx, r12;
shrd rdx, rdi, 52; x5 <- x4_1||x4_0 >> 52
xor r8, r8
adox r10, r9
adox rbx, r14
adcx r10, r15
adcx r13, rbx
mov r9, rdx; preserving value of x5 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx rcx, r14, [ rax + 0x20 ]; x10008_1, x10008_0<- arg1[0] * arg2[4] (_0*_0)
xor rdx, rdx
adox r10, r14
adox rcx, r13
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx r11, r8, [ rsi + 0x20 ]; x10022_1, x10022_0<- arg1[4] * arg2[1] (_0*_0)
adcx r9, r10
adc rcx, 0x0; add CF to r0's alloc
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx r15, rdi, [ rsi + 0x18 ]; x10021_1, x10021_0<- arg1[3] * arg2[2] (_0*_0)
test al, al
adox r8, rdi
adox r15, r11
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r13, rbx, [ rax + 0x18 ]; x10020_1, x10020_0<- arg1[2] * arg2[3] (_0*_0)
mov rdx, 0x1000003d10000 ; moving imm to reg
mulx r10, r14, rbp; x10018_1, x10018_0<- x2 * 0x1000003d10000 (_0*_0)
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r11, rbp, [ rax + 0x20 ]; x10019_1, x10019_0<- arg1[1] * arg2[4] (_0*_0)
adcx r14, r9
adcx rcx, r10
mov rdx, 0xfffffffffffff ; moving imm to reg
mov r9, r14;
and r9, rdx; x9 <- x7_0&0xfffffffffffff
adox r8, rbx
adox r13, r15
mov rdi, 0xffffffffffff ; moving imm to reg
mov r15, r9;
and r15, rdi; x11 <- x9&0xffffffffffff
adox r8, rbp
adox r11, r13
shrd r14, rcx, 52; x8 <- x7_1||x7_0 >> 52
test al, al
adox r14, r8
mov rbx, 0x0 ; moving imm to reg
adox r11, rbx
mov r10, r14;
and r10, rdx; x14 <- x12_0&0xfffffffffffff
shl r10, 4; x10027 <- x14<< 4
shr r9, 48; x10 <- x9>> 48
lea r10, [ r10 + r9 ]
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx rcx, rbp, [ rsi + 0x0 ]; x10026_1, x10026_0<- arg1[0] * arg2[0] (_0*_0)
mov rdx, 0x1000003d1 ; moving imm to reg
mulx r8, r13, r10; x10029_1, x10029_0<- x10028 * 0x1000003d1 (_0*_0)
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mulx r10, r9, [ rsi + 0x18 ]; x10031_1, x10031_0<- arg1[3] * arg2[3] (_0*_0)
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx rdi, rbx, [ rax + 0x10 ]; x10032_1, x10032_0<- arg1[4] * arg2[2] (_0*_0)
xor rdx, rdx
adox rbx, r9
adox r10, rdi
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx rdi, r9, [ rsi + 0x10 ]; x10030_1, x10030_0<- arg1[2] * arg2[4] (_0*_0)
adcx rbx, r9
adcx rdi, r10
shrd r14, r11, 52; x13 <- x12_1||x12_0 >> 52
add r14, rbx; could be done better, if r0 has been u8 as well
adc rdi, 0x0; add CF to r0's alloc
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx r10, r11, [ rsi + 0x8 ]; x10036_1, x10036_0<- arg1[1] * arg2[0] (_0*_0)
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rbx, r9, [ rax + 0x8 ]; x10035_1, x10035_0<- arg1[0] * arg2[1] (_0*_0)
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp - 0x48 ], r15; spilling x11 to mem
mov [ rsp - 0x40 ], rdi; spilling x18_1 to mem
mulx rdi, r15, [ rax + 0x0 ]; x10045_1, x10045_0<- arg1[2] * arg2[0] (_0*_0)
xor rdx, rdx
adox r11, r9
adox rbx, r10
adcx r13, rbp
adcx rcx, r8
mov rbp, [ rsp - 0x40 ]; load m64 x18_1 to register64
mov r8, r14;
shrd r8, rbp, 52; x19 <- x18_1||x18_0 >> 52
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx r10, rbp, [ rsi + 0x8 ]; x10044_1, x10044_0<- arg1[1] * arg2[1] (_0*_0)
mov rdx, r13;
shrd rdx, rcx, 52; x16 <- x15_1||x15_0 >> 52
xor r9, r9
adox rdx, r11
adox rbx, r9
mov r11, rdx; preserving value of x10038_0 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx r9, rcx, [ rax + 0x20 ]; x10040_1, x10040_0<- arg1[3] * arg2[4] (_0*_0)
adcx r15, rbp
adcx r10, rdi
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mulx rbp, rdi, [ rsi + 0x20 ]; x10041_1, x10041_0<- arg1[4] * arg2[3] (_0*_0)
xor rdx, rdx
adox rdi, rcx
adox r9, rbp
adcx r8, rdi
adc r9, 0x0; add CF to r0's alloc
mov rcx, 0xfffffffffffff ; moving imm to reg
and r14, rcx; x20 <- x18_0&0xfffffffffffff
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx rdi, rbp, [ rsi + 0x0 ]; x10043_1, x10043_0<- arg1[0] * arg2[2] (_0*_0)
adox r15, rbp
adox rdi, r10
mov rdx, 0x1000003d10 ; moving imm to reg
mulx rbp, r10, r14; x10039_1, x10039_0<- x20 * 0x1000003d10 (_0*_0)
adcx r10, r11
adcx rbx, rbp
mov r11, r10;
shrd r11, rbx, 52; x22 <- x21_1||x21_0 >> 52
and r10, rcx; x23 <- x21_0&0xfffffffffffff
mulx rbp, r14, r8; x10049_1, x10049_0<- x26 * 0x1000003d10 (_0*_0)
mov r8, 0x1000003d10000 ; moving imm to reg
mov rdx, r9; x25 to rdx
mulx rbx, r9, r8; x10051_1, x10051_0<- x25 * 0x1000003d10000 (_0*_0)
adox r11, r15
mov rdx, 0x0 ; moving imm to reg
adox rdi, rdx
adcx r14, r11
adcx rdi, rbp
mov r15, r14;
shrd r15, rdi, 52; x28 <- x27_1||x27_0 >> 52
mov rbp, [ rsp - 0x50 ]; load m64 out1 to register64
mov [ rbp + 0x8 ], r10; out1[1] = x23
and r12, rcx; x6 <- x4_0&0xfffffffffffff
lea r12, [ r12 + r15 ]
adox r9, r12
adox rbx, rdx
and r13, rcx; x17 <- x15_0&0xfffffffffffff
mov [ rbp + 0x0 ], r13; out1[0] = x17
and r14, rcx; x29 <- x27_0&0xfffffffffffff
mov r10, r9;
shrd r10, rbx, 52; x31 <- x30_1||x30_0 >> 52
mov [ rbp + 0x10 ], r14; out1[2] = x29
add r10, [ rsp - 0x48 ]
and r9, rcx; x32 <- x30_0&0xfffffffffffff
mov [ rbp + 0x20 ], r10; out1[4] = x33
mov [ rbp + 0x18 ], r9; out1[3] = x32
mov rbx, [ rsp - 0x80 ]; pop
mov rbp, [ rsp - 0x78 ]; pop
mov r12, [ rsp - 0x70 ]; pop
mov r13, [ rsp - 0x68 ]; pop
mov r14, [ rsp - 0x60 ]; pop
mov r15, [ rsp - 0x58 ]; pop
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.1348
; seed 2894912397212679 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1205169 ms on 270000 evaluations.
; Time spent for assembling and measuring (initial batch_size=266, initial num_batches=31): 117178 ms
; number of used evaluations: 270000
; Ratio (time for assembling + measure)/(total runtime for 270000 evals): 0.09722951718804583
; number reverted permutation / tried permutation: 103911 / 134966 =76.991%
; number reverted decision / tried decision: 79370 / 135033 =58.778%
; validated in 0.243s
