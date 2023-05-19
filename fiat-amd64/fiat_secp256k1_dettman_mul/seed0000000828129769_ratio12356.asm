SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
mov rax, rdx; preserving value of arg2 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r11, r10, [ rax + 0x10 ]; x10032_1, x10032_0<- arg1[4] * arg2[2] (_0*_0)
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r8, rcx, [ rax + 0x18 ]; x10031_1, x10031_0<- arg1[3] * arg2[3] (_0*_0)
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp - 0x80 ], rbx; spilling calSv-rbx to mem
mulx rbx, r9, [ rsi + 0x20 ]; x10022_1, x10022_0<- arg1[4] * arg2[1] (_0*_0)
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp - 0x78 ], rbp; spilling calSv-rbp to mem
mov [ rsp - 0x70 ], r12; spilling calSv-r12 to mem
mulx r12, rbp, [ rax + 0x20 ]; x1_1, x1_0<- arg1[4] * arg2[4] (_0*_0)
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp - 0x68 ], r13; spilling calSv-r13 to mem
mov [ rsp - 0x60 ], r14; spilling calSv-r14 to mem
mulx r14, r13, [ rax + 0x0 ]; x10012_1, x10012_0<- arg1[4] * arg2[0] (_0*_0)
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp - 0x58 ], r15; spilling calSv-r15 to mem
mov [ rsp - 0x50 ], rdi; spilling out1 to mem
mulx rdi, r15, [ rax + 0x10 ]; x10010_1, x10010_0<- arg1[2] * arg2[2] (_0*_0)
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp - 0x48 ], rdi; spilling x10010_1 to mem
mov [ rsp - 0x40 ], r15; spilling x10010_0 to mem
mulx r15, rdi, [ rsi + 0x0 ]; x10008_1, x10008_0<- arg1[0] * arg2[4] (_0*_0)
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp - 0x38 ], r15; spilling x10008_1 to mem
mov [ rsp - 0x30 ], rdi; spilling x10008_0 to mem
mulx rdi, r15, [ rax + 0x10 ]; x10021_1, x10021_0<- arg1[3] * arg2[2] (_0*_0)
test al, al
adox r9, r15
adox rdi, rbx
adcx r10, rcx
adcx r8, r11
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mulx rcx, r11, [ rsi + 0x10 ]; x10020_1, x10020_0<- arg1[2] * arg2[3] (_0*_0)
xor rdx, rdx
adox r9, r11
adox rcx, rdi
mov rbx, 0x1000003d10000 ; moving imm to reg
mov rdx, rbx; 0x1000003d10000 to rdx
mulx r15, rbx, r12; x10018_1, x10018_0<- x2 * 0x1000003d10000 (_0*_0)
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx rdi, r12, [ rsi + 0x10 ]; x10002_1, x10002_0<- arg1[2] * arg2[1] (_0*_0)
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mov [ rsp - 0x28 ], r8; spilling x10033_1 to mem
mulx r8, r11, [ rsi + 0x18 ]; x10003_1, x10003_0<- arg1[3] * arg2[0] (_0*_0)
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp - 0x20 ], r10; spilling x10033_0 to mem
mov [ rsp - 0x18 ], rcx; spilling x10024_1 to mem
mulx rcx, r10, [ rsi + 0x8 ]; x10001_1, x10001_0<- arg1[1] * arg2[2] (_0*_0)
adcx r11, r12
adcx rdi, r8
test al, al
adox r11, r10
adox rcx, rdi
mov rdx, 0x1000003d10 ; moving imm to reg
mulx r8, r12, rbp; x10007_1, x10007_0<- x3 * 0x1000003d10 (_0*_0)
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mulx r10, rbp, [ rsi + 0x0 ]; x10000_1, x10000_0<- arg1[0] * arg2[3] (_0*_0)
adcx r11, rbp
adcx r10, rcx
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx rcx, rdi, [ rsi + 0x18 ]; x10011_1, x10011_0<- arg1[3] * arg2[1] (_0*_0)
test al, al
adox r13, rdi
adox rcx, r14
adcx r12, r11
adcx r10, r8
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mulx r8, r14, [ rsi + 0x8 ]; x10009_1, x10009_0<- arg1[1] * arg2[3] (_0*_0)
test al, al
adox r13, [ rsp - 0x40 ]
adox rcx, [ rsp - 0x48 ]
mov rdx, r12;
shrd rdx, r10, 52; x5 <- x4_1||x4_0 >> 52
test al, al
adox r13, r14
adox r8, rcx
adcx r13, [ rsp - 0x30 ]
adcx r8, [ rsp - 0x38 ]
xor rbp, rbp
adox rdx, r13
adox r8, rbp
adcx rbx, rdx
adcx r8, r15
mov r15, rbx;
shrd r15, r8, 52; x8 <- x7_1||x7_0 >> 52
mov r11, 0xfffffffffffff ; moving imm to reg
and rbx, r11; x9 <- x7_0&0xfffffffffffff
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx r10, rdi, [ rsi + 0x8 ]; x10019_1, x10019_0<- arg1[1] * arg2[4] (_0*_0)
mov rdx, rbx;
shr rdx, 48; x10 <- x9>> 48
test al, al
adox r9, rdi
adox r10, [ rsp - 0x18 ]
adcx r15, r9
adc r10, 0x0; add CF to r0's alloc
mov r14, r15;
shrd r14, r10, 52; x13 <- x12_1||x12_0 >> 52
and r15, r11; x14 <- x12_0&0xfffffffffffff
and r12, r11; x6 <- x4_0&0xfffffffffffff
shl r15, 4; x10027 <- x14<< 4
lea r15, [ r15 + rdx ]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r13, rcx, [ rax + 0x20 ]; x10030_1, x10030_0<- arg1[2] * arg2[4] (_0*_0)
mov rdx, rcx;
xor r8, r8
adox rdx, [ rsp - 0x20 ]
adox r13, [ rsp - 0x28 ]
adcx r14, rdx
adc r13, 0x0; add CF to r0's alloc
mov rbp, r14;
shrd rbp, r13, 52; x19 <- x18_1||x18_0 >> 52
and r14, r11; x20 <- x18_0&0xfffffffffffff
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r9, rdi, [ rax + 0x0 ]; x10026_1, x10026_0<- arg1[0] * arg2[0] (_0*_0)
mov rdx, 0x1000003d1 ; moving imm to reg
mulx rcx, r10, r15; x10029_1, x10029_0<- x10028 * 0x1000003d1 (_0*_0)
adox r10, rdi
adox r9, rcx
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx r13, r15, [ rsi + 0x0 ]; x10035_1, x10035_0<- arg1[0] * arg2[1] (_0*_0)
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx rcx, rdi, [ rax + 0x18 ]; x10041_1, x10041_0<- arg1[4] * arg2[3] (_0*_0)
mov rdx, 0x1000003d10 ; moving imm to reg
mulx r11, r8, r14; x10039_1, x10039_0<- x20 * 0x1000003d10 (_0*_0)
mov r14, r10;
shrd r14, r9, 52; x16 <- x15_1||x15_0 >> 52
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp - 0x10 ], r12; spilling x6 to mem
mulx r12, r9, [ rax + 0x20 ]; x10040_1, x10040_0<- arg1[3] * arg2[4] (_0*_0)
test al, al
adox rdi, r9
adox r12, rcx
adcx rbp, rdi
adc r12, 0x0; add CF to r0's alloc
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx r9, rcx, [ rsi + 0x8 ]; x10036_1, x10036_0<- arg1[1] * arg2[0] (_0*_0)
test al, al
adox rcx, r15
adox r13, r9
adcx r14, rcx
adc r13, 0x0; add CF to r0's alloc
xor rdx, rdx
adox r8, r14
adox r13, r11
mov r15, r8;
shrd r15, r13, 52; x22 <- x21_1||x21_0 >> 52
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx rdi, r11, [ rsi + 0x10 ]; x10045_1, x10045_0<- arg1[2] * arg2[0] (_0*_0)
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx rcx, r9, [ rsi + 0x8 ]; x10044_1, x10044_0<- arg1[1] * arg2[1] (_0*_0)
test al, al
adox r11, r9
adox rcx, rdi
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx r13, r14, [ rsi + 0x0 ]; x10043_1, x10043_0<- arg1[0] * arg2[2] (_0*_0)
adcx r11, r14
adcx r13, rcx
mov rdx, 0x1000003d10 ; moving imm to reg
mulx r9, rdi, rbp; x10049_1, x10049_0<- x26 * 0x1000003d10 (_0*_0)
xor rcx, rcx
adox r15, r11
adox r13, rcx
adcx rdi, r15
adcx r13, r9
mov r14, 0x34 ; moving imm to reg
bzhi rbp, rdi, r14; x29 <- x27_0 (only least 0x34 bits)
shrd rdi, r13, 52; x28 <- x27_1||x27_0 >> 52
add rdi, [ rsp - 0x10 ]
mov r11, 0x30 ; moving imm to reg
bzhi r9, rbx, r11; x11 <- x9 (only least 0x30 bits)
mov rbx, [ rsp - 0x50 ]; load m64 out1 to register64
mov [ rbx + 0x10 ], rbp; out1[2] = x29
mov r15, 0x1000003d10000 ; moving imm to reg
mov rdx, r15; 0x1000003d10000 to rdx
mulx r13, r15, r12; x10051_1, x10051_0<- x25 * 0x1000003d10000 (_0*_0)
adox r15, rdi
adox r13, rcx
bzhi r12, r15, r14; x32 <- x30_0 (only least 0x34 bits)
shrd r15, r13, 52; x31 <- x30_1||x30_0 >> 52
lea r9, [ r9 + r15 ]
bzhi rbp, r10, r14; x17 <- x15_0 (only least 0x34 bits)
mov [ rbx + 0x18 ], r12; out1[3] = x32
bzhi r10, r8, r14; x23 <- x21_0 (only least 0x34 bits)
mov [ rbx + 0x8 ], r10; out1[1] = x23
mov [ rbx + 0x20 ], r9; out1[4] = x33
mov [ rbx + 0x0 ], rbp; out1[0] = x17
mov rbx, [ rsp - 0x80 ]; pop
mov rbp, [ rsp - 0x78 ]; pop
mov r12, [ rsp - 0x70 ]; pop
mov r13, [ rsp - 0x68 ]; pop
mov r14, [ rsp - 0x60 ]; pop
mov r15, [ rsp - 0x58 ]; pop
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.2356
; seed 2249846679398311 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3339906 ms on 270000 evaluations.
; Time spent for assembling and measuring (initial batch_size=176, initial num_batches=31): 162832 ms
; number of used evaluations: 270000
; Ratio (time for assembling + measure)/(total runtime for 270000 evals): 0.048753467911971174
; number reverted permutation / tried permutation: 94662 / 135107 =70.064%
; number reverted decision / tried decision: 52024 / 134892 =38.567%
; validated in 0.414s
