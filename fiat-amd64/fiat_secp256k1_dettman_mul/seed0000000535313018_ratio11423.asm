SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
mov rax, rdx; preserving value of arg2 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r11, r10, [ rax + 0x8 ]; x10002_1, x10002_0<- arg1[2] * arg2[1] (_0*_0)
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r8, rcx, [ rax + 0x18 ]; x10000_1, x10000_0<- arg1[0] * arg2[3] (_0*_0)
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp - 0x80 ], rbx; spilling calSv-rbx to mem
mulx rbx, r9, [ rax + 0x20 ]; x1_1, x1_0<- arg1[4] * arg2[4] (_0*_0)
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp - 0x78 ], rbp; spilling calSv-rbp to mem
mov [ rsp - 0x70 ], r12; spilling calSv-r12 to mem
mulx r12, rbp, [ rax + 0x0 ]; x10003_1, x10003_0<- arg1[3] * arg2[0] (_0*_0)
xor rdx, rdx
adox rbp, r10
adox r11, r12
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx r12, r10, [ rsi + 0x8 ]; x10001_1, x10001_0<- arg1[1] * arg2[2] (_0*_0)
adcx rbp, r10
adcx r12, r11
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r10, r11, [ rax + 0x20 ]; x10019_1, x10019_0<- arg1[1] * arg2[4] (_0*_0)
test al, al
adox rbp, rcx
adox r8, r12
mov rdx, 0x1000003d10 ; moving imm to reg
mulx r12, rcx, r9; x10007_1, x10007_0<- x3 * 0x1000003d10 (_0*_0)
adcx rcx, rbp
adcx r8, r12
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbp, r9, [ rax + 0x18 ]; x10009_1, x10009_0<- arg1[1] * arg2[3] (_0*_0)
mov rdx, rcx;
shrd rdx, r8, 52; x5 <- x4_1||x4_0 >> 52
mov r12, rdx; preserving value of x5 into a new reg
mov rdx, [ rax + 0x0 ]; saving arg2[0] in rdx.
mov [ rsp - 0x68 ], r13; spilling calSv-r13 to mem
mulx r13, r8, [ rsi + 0x20 ]; x10012_1, x10012_0<- arg1[4] * arg2[0] (_0*_0)
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp - 0x60 ], r14; spilling calSv-r14 to mem
mov [ rsp - 0x58 ], r15; spilling calSv-r15 to mem
mulx r15, r14, [ rsi + 0x18 ]; x10011_1, x10011_0<- arg1[3] * arg2[1] (_0*_0)
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp - 0x50 ], rdi; spilling out1 to mem
mov [ rsp - 0x48 ], r10; spilling x10019_1 to mem
mulx r10, rdi, [ rsi + 0x10 ]; x10010_1, x10010_0<- arg1[2] * arg2[2] (_0*_0)
add r8, r14; could be done better, if r0 has been u8 as well
adcx r15, r13
xor rdx, rdx
adox r8, rdi
adox r10, r15
adcx r8, r9
adcx rbp, r10
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx r13, r9, [ rsi + 0x0 ]; x10008_1, x10008_0<- arg1[0] * arg2[4] (_0*_0)
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx rdi, r14, [ rsi + 0x20 ]; x10022_1, x10022_0<- arg1[4] * arg2[1] (_0*_0)
add r8, r9; could be done better, if r0 has been u8 as well
adcx r13, rbp
xor rdx, rdx
adox r12, r8
adox r13, rdx
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx r10, r15, [ rsi + 0x18 ]; x10021_1, x10021_0<- arg1[3] * arg2[2] (_0*_0)
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r9, rbp, [ rax + 0x18 ]; x10020_1, x10020_0<- arg1[2] * arg2[3] (_0*_0)
adcx r14, r15
adcx r10, rdi
xor rdx, rdx
adox r14, rbp
adox r9, r10
mov rdi, 0x1000003d10000 ; moving imm to reg
mov rdx, rbx; x2 to rdx
mulx r8, rbx, rdi; x10018_1, x10018_0<- x2 * 0x1000003d10000 (_0*_0)
adcx rbx, r12
adcx r13, r8
mov r12, rbx;
shrd r12, r13, 52; x8 <- x7_1||x7_0 >> 52
mov rdx, 0xfffffffffffff ; moving imm to reg
and rbx, rdx; x9 <- x7_0&0xfffffffffffff
mov r15, rbx;
shr r15, 48; x10 <- x9>> 48
test al, al
adox r14, r11
adox r9, [ rsp - 0x48 ]
adcx r12, r14
adc r9, 0x0; add CF to r0's alloc
mov r11, r12;
and r11, rdx; x14 <- x12_0&0xfffffffffffff
shl r11, 4; x10027 <- x14<< 4
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx r10, rbp, [ rsi + 0x20 ]; x10032_1, x10032_0<- arg1[4] * arg2[2] (_0*_0)
mov rdx, 0xffffffffffff ; moving imm to reg
and rbx, rdx; x11 <- x9&0xffffffffffff
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r13, r8, [ rax + 0x18 ]; x10031_1, x10031_0<- arg1[3] * arg2[3] (_0*_0)
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx rdi, r14, [ rsi + 0x10 ]; x10045_1, x10045_0<- arg1[2] * arg2[0] (_0*_0)
shrd r12, r9, 52; x13 <- x12_1||x12_0 >> 52
xor rdx, rdx
adox rbp, r8
adox r13, r10
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r10, r9, [ rax + 0x20 ]; x10030_1, x10030_0<- arg1[2] * arg2[4] (_0*_0)
adcx rbp, r9
adcx r10, r13
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r13, r8, [ rax + 0x18 ]; x10041_1, x10041_0<- arg1[4] * arg2[3] (_0*_0)
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp - 0x40 ], rbx; spilling x11 to mem
mulx rbx, r9, [ rax + 0x20 ]; x10040_1, x10040_0<- arg1[3] * arg2[4] (_0*_0)
xor rdx, rdx
adox r12, rbp
adox r10, rdx
mov rbp, r12;
shrd rbp, r10, 52; x19 <- x18_1||x18_0 >> 52
test al, al
adox r8, r9
adox rbx, r13
adcx rbp, r8
adc rbx, 0x0; add CF to r0's alloc
lea r11, [ r11 + r15 ]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx r13, r15, [ rsi + 0x8 ]; x10044_1, x10044_0<- arg1[1] * arg2[1] (_0*_0)
mov rdx, 0x1000003d1 ; moving imm to reg
mulx r10, r9, r11; x10029_1, x10029_0<- x10028 * 0x1000003d1 (_0*_0)
xor r8, r8
adox r14, r15
adox r13, rdi
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r11, rdi, [ rax + 0x0 ]; x10026_1, x10026_0<- arg1[0] * arg2[0] (_0*_0)
adcx r9, rdi
adcx r11, r10
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx r10, r15, [ rsi + 0x8 ]; x10036_1, x10036_0<- arg1[1] * arg2[0] (_0*_0)
mov rdx, 0x1000003d10 ; moving imm to reg
mulx r8, rdi, rbp; x10049_1, x10049_0<- x26 * 0x1000003d10 (_0*_0)
mov rbp, 0xfffffffffffff ; moving imm to reg
and r12, rbp; x20 <- x18_0&0xfffffffffffff
mov rbp, r9;
shrd rbp, r11, 52; x16 <- x15_1||x15_0 >> 52
mov [ rsp - 0x38 ], rbx; spilling x25 to mem
mulx rbx, r11, r12; x10039_1, x10039_0<- x20 * 0x1000003d10 (_0*_0)
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp - 0x30 ], r8; spilling x10049_1 to mem
mulx r8, r12, [ rsi + 0x0 ]; x10035_1, x10035_0<- arg1[0] * arg2[1] (_0*_0)
xor rdx, rdx
adox r15, r12
adox r8, r10
adcx rbp, r15
adc r8, 0x0; add CF to r0's alloc
xor r10, r10
adox r11, rbp
adox r8, rbx
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r12, rbx, [ rax + 0x10 ]; x10043_1, x10043_0<- arg1[0] * arg2[2] (_0*_0)
mov rdx, 0xfffffffffffff ; moving imm to reg
mov r15, r11;
and r15, rdx; x23 <- x21_0&0xfffffffffffff
and rcx, rdx; x6 <- x4_0&0xfffffffffffff
adox r14, rbx
adox r12, r13
shrd r11, r8, 52; x22 <- x21_1||x21_0 >> 52
xor r13, r13
adox r11, r14
adox r12, r13
adcx rdi, r11
adcx r12, [ rsp - 0x30 ]
mov r10, rdi;
shrd r10, r12, 52; x28 <- x27_1||x27_0 >> 52
and rdi, rdx; x29 <- x27_0&0xfffffffffffff
mov rbp, [ rsp - 0x50 ]; load m64 out1 to register64
mov [ rbp + 0x10 ], rdi; out1[2] = x29
lea rcx, [ rcx + r10 ]
mov r8, 0x1000003d10000 ; moving imm to reg
mov rdx, r8; 0x1000003d10000 to rdx
mulx rbx, r8, [ rsp - 0x38 ]; x10051_1, x10051_0<- x25 * 0x1000003d10000 (_0*_0)
adox r8, rcx
adox rbx, r13
mov r14, 0xfffffffffffff ; moving imm to reg
mov r11, r8;
and r11, r14; x32 <- x30_0&0xfffffffffffff
shrd r8, rbx, 52; x31 <- x30_1||x30_0 >> 52
add r8, [ rsp - 0x40 ]
and r9, r14; x17 <- x15_0&0xfffffffffffff
mov [ rbp + 0x0 ], r9; out1[0] = x17
mov [ rbp + 0x20 ], r8; out1[4] = x33
mov [ rbp + 0x18 ], r11; out1[3] = x32
mov [ rbp + 0x8 ], r15; out1[1] = x23
mov rbx, [ rsp - 0x80 ]; pop
mov rbp, [ rsp - 0x78 ]; pop
mov r12, [ rsp - 0x70 ]; pop
mov r13, [ rsp - 0x68 ]; pop
mov r14, [ rsp - 0x60 ]; pop
mov r15, [ rsp - 0x58 ]; pop
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.1423
; seed 1104056933168302 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1488477 ms on 270000 evaluations.
; Time spent for assembling and measuring (initial batch_size=281, initial num_batches=31): 138241 ms
; number of used evaluations: 270000
; Ratio (time for assembling + measure)/(total runtime for 270000 evals): 0.09287412570029634
; number reverted permutation / tried permutation: 99088 / 135520 =73.117%
; number reverted decision / tried decision: 78262 / 134479 =58.196%
; validated in 0.291s
