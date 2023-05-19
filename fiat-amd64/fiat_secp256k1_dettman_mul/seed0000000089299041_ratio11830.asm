SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
mov rax, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x0 ]; saving arg2[0] in rdx.
mulx r11, r10, [ rsi + 0x18 ]; x10003_1, x10003_0<- arg1[3] * arg2[0] (_0*_0)
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx r8, rcx, [ rsi + 0x10 ]; x10002_1, x10002_0<- arg1[2] * arg2[1] (_0*_0)
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp - 0x80 ], rbx; spilling calSv-rbx to mem
mulx rbx, r9, [ rsi + 0x20 ]; x1_1, x1_0<- arg1[4] * arg2[4] (_0*_0)
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp - 0x78 ], rbp; spilling calSv-rbp to mem
mov [ rsp - 0x70 ], r12; spilling calSv-r12 to mem
mulx r12, rbp, [ rsi + 0x8 ]; x10009_1, x10009_0<- arg1[1] * arg2[3] (_0*_0)
mov rdx, 0x1000003d10 ; moving imm to reg
mov [ rsp - 0x68 ], r13; spilling calSv-r13 to mem
mov [ rsp - 0x60 ], r14; spilling calSv-r14 to mem
mulx r14, r13, r9; x10007_1, x10007_0<- x3 * 0x1000003d10 (_0*_0)
test al, al
adox r10, rcx
adox r8, r11
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rcx, r11, [ rax + 0x10 ]; x10001_1, x10001_0<- arg1[1] * arg2[2] (_0*_0)
adcx r10, r11
adcx rcx, r8
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r8, r9, [ rax + 0x18 ]; x10000_1, x10000_0<- arg1[0] * arg2[3] (_0*_0)
xor rdx, rdx
adox r10, r9
adox r8, rcx
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rcx, r11, [ rax + 0x8 ]; x10011_1, x10011_0<- arg1[3] * arg2[1] (_0*_0)
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp - 0x58 ], r15; spilling calSv-r15 to mem
mulx r15, r9, [ rax + 0x0 ]; x10012_1, x10012_0<- arg1[4] * arg2[0] (_0*_0)
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp - 0x50 ], rdi; spilling out1 to mem
mov [ rsp - 0x48 ], r12; spilling x10009_1 to mem
mulx r12, rdi, [ rsi + 0x10 ]; x10010_1, x10010_0<- arg1[2] * arg2[2] (_0*_0)
adcx r9, r11
adcx rcx, r15
test al, al
adox r9, rdi
adox r12, rcx
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r15, r11, [ rax + 0x10 ]; x10043_1, x10043_0<- arg1[0] * arg2[2] (_0*_0)
mov rdx, 0x1000003d10000 ; moving imm to reg
mulx rcx, rdi, rbx; x10018_1, x10018_0<- x2 * 0x1000003d10000 (_0*_0)
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp - 0x40 ], r15; spilling x10043_1 to mem
mulx r15, rbx, [ rsi + 0x0 ]; x10008_1, x10008_0<- arg1[0] * arg2[4] (_0*_0)
adcx r13, r10
adcx r8, r14
mov rdx, r13;
shrd rdx, r8, 52; x5 <- x4_1||x4_0 >> 52
xor r14, r14
adox r9, rbp
adox r12, [ rsp - 0x48 ]
adcx r9, rbx
adcx r15, r12
add rdx, r9; could be done better, if r0 has been u8 as well
adc r15, 0x0; add CF to r0's alloc
add rdi, rdx; could be done better, if r0 has been u8 as well
adcx r15, rcx
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r10, rbp, [ rax + 0x18 ]; x10020_1, x10020_0<- arg1[2] * arg2[3] (_0*_0)
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rbx, rcx, [ rax + 0x10 ]; x10021_1, x10021_0<- arg1[3] * arg2[2] (_0*_0)
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r12, r8, [ rax + 0x8 ]; x10022_1, x10022_0<- arg1[4] * arg2[1] (_0*_0)
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r14, r9, [ rax + 0x20 ]; x10019_1, x10019_0<- arg1[1] * arg2[4] (_0*_0)
xor rdx, rdx
adox r8, rcx
adox rbx, r12
adcx r8, rbp
adcx r10, rbx
mov rbp, rdi;
shrd rbp, r15, 52; x8 <- x7_1||x7_0 >> 52
xor r15, r15
adox r8, r9
adox r14, r10
adcx rbp, r8
adc r14, 0x0; add CF to r0's alloc
mov rdx, 0xfffffffffffff ; moving imm to reg
and rdi, rdx; x9 <- x7_0&0xfffffffffffff
mov rcx, rbp;
and rcx, rdx; x14 <- x12_0&0xfffffffffffff
mov r12, rdi;
shr r12, 48; x10 <- x9>> 48
shl rcx, 4; x10027 <- x14<< 4
mov r9, 0xffffffffffff ; moving imm to reg
and rdi, r9; x11 <- x9&0xffffffffffff
lea rcx, [ rcx + r12 ]
mov rbx, 0x1000003d1 ; moving imm to reg
mov rdx, rcx; x10028 to rdx
mulx r10, rcx, rbx; x10029_1, x10029_0<- x10028 * 0x1000003d1 (_0*_0)
shrd rbp, r14, 52; x13 <- x12_1||x12_0 >> 52
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r14, r8, [ rax + 0x10 ]; x10032_1, x10032_0<- arg1[4] * arg2[2] (_0*_0)
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r15, r12, [ rax + 0x18 ]; x10031_1, x10031_0<- arg1[3] * arg2[3] (_0*_0)
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx r9, rbx, [ rsi + 0x10 ]; x10030_1, x10030_0<- arg1[2] * arg2[4] (_0*_0)
add r8, r12; could be done better, if r0 has been u8 as well
adcx r15, r14
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r12, r14, [ rax + 0x0 ]; x10026_1, x10026_0<- arg1[0] * arg2[0] (_0*_0)
xor rdx, rdx
adox rcx, r14
adox r12, r10
mov r10, 0xfffffffffffff ; moving imm to reg
mov r14, rcx;
and r14, r10; x17 <- x15_0&0xfffffffffffff
shrd rcx, r12, 52; x16 <- x15_1||x15_0 >> 52
test al, al
adox r8, rbx
adox r9, r15
adcx rbp, r8
adc r9, 0x0; add CF to r0's alloc
mov rbx, rbp;
shrd rbx, r9, 52; x19 <- x18_1||x18_0 >> 52
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mulx r12, r15, [ rsi + 0x20 ]; x10041_1, x10041_0<- arg1[4] * arg2[3] (_0*_0)
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r9, r8, [ rax + 0x8 ]; x10035_1, x10035_0<- arg1[0] * arg2[1] (_0*_0)
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp - 0x38 ], rdi; spilling x11 to mem
mulx rdi, r10, [ rax + 0x20 ]; x10040_1, x10040_0<- arg1[3] * arg2[4] (_0*_0)
xor rdx, rdx
adox r15, r10
adox rdi, r12
adcx rbx, r15
adc rdi, 0x0; add CF to r0's alloc
mov r12, [ rsp - 0x50 ]; load m64 out1 to register64
mov [ r12 + 0x0 ], r14; out1[0] = x17
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx r10, r14, [ rsi + 0x8 ]; x10036_1, x10036_0<- arg1[1] * arg2[0] (_0*_0)
xor rdx, rdx
adox r14, r8
adox r9, r10
adcx rcx, r14
adc r9, 0x0; add CF to r0's alloc
mov r8, 0xfffffffffffff ; moving imm to reg
and rbp, r8; x20 <- x18_0&0xfffffffffffff
mov r15, 0x1000003d10 ; moving imm to reg
mov rdx, rbp; x20 to rdx
mulx r10, rbp, r15; x10039_1, x10039_0<- x20 * 0x1000003d10 (_0*_0)
adox rbp, rcx
adox r9, r10
mov r14, rbp;
and r14, r8; x23 <- x21_0&0xfffffffffffff
shrd rbp, r9, 52; x22 <- x21_1||x21_0 >> 52
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx r10, rcx, [ rsi + 0x10 ]; x10045_1, x10045_0<- arg1[2] * arg2[0] (_0*_0)
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx r15, r9, [ rsi + 0x8 ]; x10044_1, x10044_0<- arg1[1] * arg2[1] (_0*_0)
mov [ r12 + 0x8 ], r14; out1[1] = x23
and r13, r8; x6 <- x4_0&0xfffffffffffff
adox rcx, r9
adox r15, r10
mov rdx, 0x1000003d10 ; moving imm to reg
mulx r10, r14, rbx; x10049_1, x10049_0<- x26 * 0x1000003d10 (_0*_0)
adcx rcx, r11
adcx r15, [ rsp - 0x40 ]
xor r11, r11
adox rbp, rcx
adox r15, r11
adcx r14, rbp
adcx r15, r10
mov r9, r14;
shrd r9, r15, 52; x28 <- x27_1||x27_0 >> 52
lea r13, [ r13 + r9 ]
mov rbx, 0x1000003d10000 ; moving imm to reg
mov rdx, rdi; x25 to rdx
mulx r10, rdi, rbx; x10051_1, x10051_0<- x25 * 0x1000003d10000 (_0*_0)
and r14, r8; x29 <- x27_0&0xfffffffffffff
adox rdi, r13
adox r10, r11
mov rdx, rdi;
and rdx, r8; x32 <- x30_0&0xfffffffffffff
shrd rdi, r10, 52; x31 <- x30_1||x30_0 >> 52
add rdi, [ rsp - 0x38 ]
mov [ r12 + 0x18 ], rdx; out1[3] = x32
mov [ r12 + 0x10 ], r14; out1[2] = x29
mov [ r12 + 0x20 ], rdi; out1[4] = x33
mov rbx, [ rsp - 0x80 ]; pop
mov rbp, [ rsp - 0x78 ]; pop
mov r12, [ rsp - 0x70 ]; pop
mov r13, [ rsp - 0x68 ]; pop
mov r14, [ rsp - 0x60 ]; pop
mov r15, [ rsp - 0x58 ]; pop
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.1830
; seed 2855002300978685 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1212939 ms on 270000 evaluations.
; Time spent for assembling and measuring (initial batch_size=368, initial num_batches=31): 118076 ms
; number of used evaluations: 270000
; Ratio (time for assembling + measure)/(total runtime for 270000 evals): 0.09734702239766385
; number reverted permutation / tried permutation: 102230 / 134445 =76.039%
; number reverted decision / tried decision: 78953 / 135554 =58.245%
; validated in 0.244s
