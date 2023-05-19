SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
mov rax, rdx; preserving value of arg2 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r11, r10, [ rax + 0x20 ]; x1_1, x1_0<- arg1[4] * arg2[4] (_0*_0)
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx r8, rcx, [ rsi + 0x8 ]; x10001_1, x10001_0<- arg1[1] * arg2[2] (_0*_0)
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp - 0x80 ], rbx; spilling calSv-rbx to mem
mulx rbx, r9, [ rax + 0x0 ]; x10036_1, x10036_0<- arg1[1] * arg2[0] (_0*_0)
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp - 0x78 ], rbp; spilling calSv-rbp to mem
mov [ rsp - 0x70 ], r12; spilling calSv-r12 to mem
mulx r12, rbp, [ rsi + 0x18 ]; x10040_1, x10040_0<- arg1[3] * arg2[4] (_0*_0)
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp - 0x68 ], r13; spilling calSv-r13 to mem
mov [ rsp - 0x60 ], r14; spilling calSv-r14 to mem
mulx r14, r13, [ rax + 0x0 ]; x10003_1, x10003_0<- arg1[3] * arg2[0] (_0*_0)
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp - 0x58 ], r15; spilling calSv-r15 to mem
mov [ rsp - 0x50 ], rdi; spilling out1 to mem
mulx rdi, r15, [ rax + 0x0 ]; x10012_1, x10012_0<- arg1[4] * arg2[0] (_0*_0)
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp - 0x48 ], rbx; spilling x10036_1 to mem
mov [ rsp - 0x40 ], r9; spilling x10036_0 to mem
mulx r9, rbx, [ rsi + 0x18 ]; x10011_1, x10011_0<- arg1[3] * arg2[1] (_0*_0)
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp - 0x38 ], r12; spilling x10040_1 to mem
mov [ rsp - 0x30 ], rbp; spilling x10040_0 to mem
mulx rbp, r12, [ rax + 0x0 ]; x10026_1, x10026_0<- arg1[0] * arg2[0] (_0*_0)
xor rdx, rdx
adox r15, rbx
adox r9, rdi
mov rdi, 0x1000003d10 ; moving imm to reg
mov rdx, rdi; 0x1000003d10 to rdx
mulx rbx, rdi, r10; x10007_1, x10007_0<- x3 * 0x1000003d10 (_0*_0)
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp - 0x28 ], rbp; spilling x10026_1 to mem
mulx rbp, r10, [ rsi + 0x10 ]; x10002_1, x10002_0<- arg1[2] * arg2[1] (_0*_0)
adcx r13, r10
adcx rbp, r14
test al, al
adox r13, rcx
adox r8, rbp
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r14, rcx, [ rax + 0x18 ]; x10000_1, x10000_0<- arg1[0] * arg2[3] (_0*_0)
adcx r13, rcx
adcx r14, r8
xor rdx, rdx
adox rdi, r13
adox r14, rbx
mov rbx, 0xfffffffffffff ; moving imm to reg
mov r10, rdi;
and r10, rbx; x6 <- x4_0&0xfffffffffffff
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx r8, rbp, [ rsi + 0x10 ]; x10010_1, x10010_0<- arg1[2] * arg2[2] (_0*_0)
adox r15, rbp
adox r8, r9
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mulx rcx, r9, [ rsi + 0x8 ]; x10009_1, x10009_0<- arg1[1] * arg2[3] (_0*_0)
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx rbp, r13, [ rsi + 0x0 ]; x10008_1, x10008_0<- arg1[0] * arg2[4] (_0*_0)
adcx r15, r9
adcx rcx, r8
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r9, r8, [ rax + 0x10 ]; x10021_1, x10021_0<- arg1[3] * arg2[2] (_0*_0)
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp - 0x20 ], r10; spilling x6 to mem
mulx r10, rbx, [ rax + 0x18 ]; x10020_1, x10020_0<- arg1[2] * arg2[3] (_0*_0)
test al, al
adox r15, r13
adox rbp, rcx
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx rcx, r13, [ rax + 0x8 ]; x10022_1, x10022_0<- arg1[4] * arg2[1] (_0*_0)
adcx r13, r8
adcx r9, rcx
shrd rdi, r14, 52; x5 <- x4_1||x4_0 >> 52
add rdi, r15; could be done better, if r0 has been u8 as well
adc rbp, 0x0; add CF to r0's alloc
xor rdx, rdx
adox r13, rbx
adox r10, r9
mov r14, 0x1000003d10000 ; moving imm to reg
mov rdx, r11; x2 to rdx
mulx r8, r11, r14; x10018_1, x10018_0<- x2 * 0x1000003d10000 (_0*_0)
adcx r11, rdi
adcx rbp, r8
mov rbx, r11;
shrd rbx, rbp, 52; x8 <- x7_1||x7_0 >> 52
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rcx, r15, [ rax + 0x20 ]; x10019_1, x10019_0<- arg1[1] * arg2[4] (_0*_0)
mov rdx, 0xfffffffffffff ; moving imm to reg
and r11, rdx; x9 <- x7_0&0xfffffffffffff
adox r13, r15
adox rcx, r10
adcx rbx, r13
adc rcx, 0x0; add CF to r0's alloc
mov r9, rbx;
and r9, rdx; x14 <- x12_0&0xfffffffffffff
shl r9, 4; x10027 <- x14<< 4
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r10, rdi, [ rax + 0x10 ]; x10032_1, x10032_0<- arg1[4] * arg2[2] (_0*_0)
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx rbp, r8, [ rsi + 0x10 ]; x10030_1, x10030_0<- arg1[2] * arg2[4] (_0*_0)
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r13, r15, [ rax + 0x18 ]; x10031_1, x10031_0<- arg1[3] * arg2[3] (_0*_0)
test al, al
adox rdi, r15
adox r13, r10
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r15, r10, [ rax + 0x18 ]; x10041_1, x10041_0<- arg1[4] * arg2[3] (_0*_0)
adcx rdi, r8
adcx rbp, r13
mov rdx, r11;
shr rdx, 48; x10 <- x9>> 48
mov r8, rdx; preserving value of x10 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r14, r13, [ rax + 0x8 ]; x10035_1, x10035_0<- arg1[0] * arg2[1] (_0*_0)
lea r9, [ r9 + r8 ]
shrd rbx, rcx, 52; x13 <- x12_1||x12_0 >> 52
mov rdx, 0x1000003d1 ; moving imm to reg
mulx r8, rcx, r9; x10029_1, x10029_0<- x10028 * 0x1000003d1 (_0*_0)
xor r9, r9
adox rcx, r12
adox r8, [ rsp - 0x28 ]
mov r12, rcx;
shrd r12, r8, 52; x16 <- x15_1||x15_0 >> 52
test al, al
adox rbx, rdi
adox rbp, r9
adcx r10, [ rsp - 0x30 ]
adcx r15, [ rsp - 0x38 ]
mov rdi, rbx;
shrd rdi, rbp, 52; x19 <- x18_1||x18_0 >> 52
test al, al
adox rdi, r10
adox r15, r9
mov r8, 0x1000003d10 ; moving imm to reg
mov rdx, r8; 0x1000003d10 to rdx
mulx rbp, r8, rdi; x10049_1, x10049_0<- x26 * 0x1000003d10 (_0*_0)
mov r10, r13;
adcx r10, [ rsp - 0x40 ]
adcx r14, [ rsp - 0x48 ]
test al, al
adox r12, r10
adox r14, r9
mov r13, 0xfffffffffffff ; moving imm to reg
and rcx, r13; x17 <- x15_0&0xfffffffffffff
mov rdi, [ rsp - 0x50 ]; load m64 out1 to register64
mov [ rdi + 0x0 ], rcx; out1[0] = x17
and rbx, r13; x20 <- x18_0&0xfffffffffffff
mulx rcx, r10, rbx; x10039_1, x10039_0<- x20 * 0x1000003d10 (_0*_0)
adox r10, r12
adox r14, rcx
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbx, r12, [ rax + 0x8 ]; x10044_1, x10044_0<- arg1[1] * arg2[1] (_0*_0)
mov rdx, r10;
shrd rdx, r14, 52; x22 <- x21_1||x21_0 >> 52
mov rcx, rdx; preserving value of x22 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r9, r14, [ rax + 0x10 ]; x10043_1, x10043_0<- arg1[0] * arg2[2] (_0*_0)
and r10, r13; x23 <- x21_0&0xfffffffffffff
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx rdi, r13, [ rsi + 0x10 ]; x10045_1, x10045_0<- arg1[2] * arg2[0] (_0*_0)
mov rdx, 0xffffffffffff ; moving imm to reg
and r11, rdx; x11 <- x9&0xffffffffffff
adox r13, r12
adox rbx, rdi
adcx r13, r14
adcx r9, rbx
add rcx, r13; could be done better, if r0 has been u8 as well
adc r9, 0x0; add CF to r0's alloc
xor r12, r12
adox r8, rcx
adox r9, rbp
mov rbp, r8;
shrd rbp, r9, 52; x28 <- x27_1||x27_0 >> 52
add rbp, [ rsp - 0x20 ]
mov r14, 0x1000003d10000 ; moving imm to reg
mov rdx, r14; 0x1000003d10000 to rdx
mulx rdi, r14, r15; x10051_1, x10051_0<- x25 * 0x1000003d10000 (_0*_0)
xor rbx, rbx
adox r14, rbp
adox rdi, rbx
mov r12, 0xfffffffffffff ; moving imm to reg
mov r13, r14;
and r13, r12; x32 <- x30_0&0xfffffffffffff
shrd r14, rdi, 52; x31 <- x30_1||x30_0 >> 52
and r8, r12; x29 <- x27_0&0xfffffffffffff
mov rcx, [ rsp - 0x50 ]; load m64 out1 to register64
mov [ rcx + 0x10 ], r8; out1[2] = x29
mov [ rcx + 0x18 ], r13; out1[3] = x32
lea r11, [ r11 + r14 ]
mov [ rcx + 0x20 ], r11; out1[4] = x33
mov [ rcx + 0x8 ], r10; out1[1] = x23
mov rbx, [ rsp - 0x80 ]; pop
mov rbp, [ rsp - 0x78 ]; pop
mov r12, [ rsp - 0x70 ]; pop
mov r13, [ rsp - 0x68 ]; pop
mov r14, [ rsp - 0x60 ]; pop
mov r15, [ rsp - 0x58 ]; pop
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.0616
; seed 1444059844171592 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1999346 ms on 270000 evaluations.
; Time spent for assembling and measuring (initial batch_size=176, initial num_batches=31): 112866 ms
; number of used evaluations: 270000
; Ratio (time for assembling + measure)/(total runtime for 270000 evals): 0.056451459627298126
; number reverted permutation / tried permutation: 100989 / 135089 =74.757%
; number reverted decision / tried decision: 64123 / 134910 =47.530%
; validated in 0.337s
