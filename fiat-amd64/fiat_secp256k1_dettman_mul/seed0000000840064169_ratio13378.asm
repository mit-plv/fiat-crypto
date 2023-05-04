SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
mov rax, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x8 ]; saving arg2[1] in rdx.
mulx r11, r10, [ rsi + 0x10 ]; x10002_1, x10002_0<- arg1[2] * arg2[1] (_0*_0)
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx r8, rcx, [ rsi + 0x8 ]; x10001_1, x10001_0<- arg1[1] * arg2[2] (_0*_0)
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp - 0x80 ], rbx; spilling calSv-rbx to mem
mulx rbx, r9, [ rax + 0x8 ]; x10022_1, x10022_0<- arg1[4] * arg2[1] (_0*_0)
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp - 0x78 ], rbp; spilling calSv-rbp to mem
mov [ rsp - 0x70 ], r12; spilling calSv-r12 to mem
mulx r12, rbp, [ rax + 0x0 ]; x10003_1, x10003_0<- arg1[3] * arg2[0] (_0*_0)
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp - 0x68 ], r13; spilling calSv-r13 to mem
mov [ rsp - 0x60 ], r14; spilling calSv-r14 to mem
mulx r14, r13, [ rsi + 0x20 ]; x10041_1, x10041_0<- arg1[4] * arg2[3] (_0*_0)
xor rdx, rdx
adox rbp, r10
adox r11, r12
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r12, r10, [ rax + 0x18 ]; x10031_1, x10031_0<- arg1[3] * arg2[3] (_0*_0)
adcx rbp, rcx
adcx r8, r11
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r11, rcx, [ rax + 0x18 ]; x10000_1, x10000_0<- arg1[0] * arg2[3] (_0*_0)
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp - 0x58 ], r15; spilling calSv-r15 to mem
mov [ rsp - 0x50 ], rdi; spilling out1 to mem
mulx rdi, r15, [ rsi + 0x20 ]; x1_1, x1_0<- arg1[4] * arg2[4] (_0*_0)
xor rdx, rdx
adox rbp, rcx
adox r11, r8
mov r8, 0x1000003d10000 ; moving imm to reg
mov rdx, r8; 0x1000003d10000 to rdx
mulx rcx, r8, rdi; x10018_1, x10018_0<- x2 * 0x1000003d10000 (_0*_0)
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp - 0x48 ], r14; spilling x10041_1 to mem
mulx r14, rdi, [ rsi + 0x18 ]; x10011_1, x10011_0<- arg1[3] * arg2[1] (_0*_0)
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp - 0x40 ], r13; spilling x10041_0 to mem
mov [ rsp - 0x38 ], r12; spilling x10031_1 to mem
mulx r12, r13, [ rax + 0x0 ]; x10012_1, x10012_0<- arg1[4] * arg2[0] (_0*_0)
mov rdx, 0x1000003d10 ; moving imm to reg
mov [ rsp - 0x30 ], r10; spilling x10031_0 to mem
mov [ rsp - 0x28 ], rcx; spilling x10018_1 to mem
mulx rcx, r10, r15; x10007_1, x10007_0<- x3 * 0x1000003d10 (_0*_0)
adcx r10, rbp
adcx r11, rcx
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx rbp, r15, [ rsi + 0x10 ]; x10010_1, x10010_0<- arg1[2] * arg2[2] (_0*_0)
test al, al
adox r13, rdi
adox r14, r12
adcx r13, r15
adcx rbp, r14
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r12, rdi, [ rax + 0x20 ]; x10008_1, x10008_0<- arg1[0] * arg2[4] (_0*_0)
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r15, rcx, [ rax + 0x18 ]; x10009_1, x10009_0<- arg1[1] * arg2[3] (_0*_0)
xor rdx, rdx
adox r13, rcx
adox r15, rbp
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rbp, r14, [ rax + 0x10 ]; x10021_1, x10021_0<- arg1[3] * arg2[2] (_0*_0)
mov rdx, r10;
shrd rdx, r11, 52; x5 <- x4_1||x4_0 >> 52
test al, al
adox r9, r14
adox rbp, rbx
adcx r13, rdi
adcx r12, r15
test al, al
adox rdx, r13
mov rbx, 0x0 ; moving imm to reg
adox r12, rbx
adcx r8, rdx
adcx r12, [ rsp - 0x28 ]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rdi, r11, [ rax + 0x18 ]; x10020_1, x10020_0<- arg1[2] * arg2[3] (_0*_0)
test al, al
adox r9, r11
adox rdi, rbp
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx r15, rcx, [ rsi + 0x8 ]; x10019_1, x10019_0<- arg1[1] * arg2[4] (_0*_0)
adcx r9, rcx
adcx r15, rdi
mov rdx, r8;
shrd rdx, r12, 52; x8 <- x7_1||x7_0 >> 52
xor r14, r14
adox rdx, r9
adox r15, r14
mov rbx, rdx;
shrd rbx, r15, 52; x13 <- x12_1||x12_0 >> 52
mov rbp, 0xfffffffffffff ; moving imm to reg
and r8, rbp; x9 <- x7_0&0xfffffffffffff
mov r13, r8;
shr r13, 48; x10 <- x9>> 48
mov r12, rdx; preserving value of x12_0 into a new reg
mov rdx, [ rax + 0x10 ]; saving arg2[2] in rdx.
mulx rdi, r11, [ rsi + 0x20 ]; x10032_1, x10032_0<- arg1[4] * arg2[2] (_0*_0)
test al, al
adox r11, [ rsp - 0x30 ]
adox rdi, [ rsp - 0x38 ]
and r12, rbp; x14 <- x12_0&0xfffffffffffff
mov rdx, 0xffffffffffff ; moving imm to reg
and r8, rdx; x11 <- x9&0xffffffffffff
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r9, rcx, [ rax + 0x0 ]; x10026_1, x10026_0<- arg1[0] * arg2[0] (_0*_0)
shl r12, 4; x10027 <- x14<< 4
lea r12, [ r12 + r13 ]
mov rdx, 0x1000003d1 ; moving imm to reg
mulx r13, r15, r12; x10029_1, x10029_0<- x10028 * 0x1000003d1 (_0*_0)
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r14, r12, [ rax + 0x20 ]; x10030_1, x10030_0<- arg1[2] * arg2[4] (_0*_0)
xor rdx, rdx
adox r11, r12
adox r14, rdi
adcx r15, rcx
adcx r9, r13
mov rdi, r15;
shrd rdi, r9, 52; x16 <- x15_1||x15_0 >> 52
test al, al
adox rbx, r11
adox r14, rdx
mov rcx, rbx;
shrd rcx, r14, 52; x19 <- x18_1||x18_0 >> 52
and rbx, rbp; x20 <- x18_0&0xfffffffffffff
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r12, r13, [ rax + 0x8 ]; x10035_1, x10035_0<- arg1[0] * arg2[1] (_0*_0)
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx r9, r11, [ rsi + 0x18 ]; x10040_1, x10040_0<- arg1[3] * arg2[4] (_0*_0)
mov rdx, r11;
adox rdx, [ rsp - 0x40 ]
adox r9, [ rsp - 0x48 ]
adcx rcx, rdx
adc r9, 0x0; add CF to r0's alloc
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r11, r14, [ rax + 0x0 ]; x10036_1, x10036_0<- arg1[1] * arg2[0] (_0*_0)
mov rdx, 0x1000003d10 ; moving imm to reg
mov [ rsp - 0x20 ], r8; spilling x11 to mem
mulx r8, rbp, rcx; x10049_1, x10049_0<- x26 * 0x1000003d10 (_0*_0)
xor rcx, rcx
adox r14, r13
adox r12, r11
adcx rdi, r14
adc r12, 0x0; add CF to r0's alloc
mulx r11, r13, rbx; x10039_1, x10039_0<- x20 * 0x1000003d10 (_0*_0)
mov rbx, 0x34 ; moving imm to reg
bzhi r14, r10, rbx; x6 <- x4_0 (only least 0x34 bits)
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rcx, r10, [ rax + 0x0 ]; x10045_1, x10045_0<- arg1[2] * arg2[0] (_0*_0)
adox r13, rdi
adox r12, r11
mov rdx, r13;
shrd rdx, r12, 52; x22 <- x21_1||x21_0 >> 52
mov rdi, rdx; preserving value of x22 into a new reg
mov rdx, [ rax + 0x8 ]; saving arg2[1] in rdx.
mulx r12, r11, [ rsi + 0x8 ]; x10044_1, x10044_0<- arg1[1] * arg2[1] (_0*_0)
test al, al
adox r10, r11
adox r12, rcx
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx r11, rcx, [ rsi + 0x0 ]; x10043_1, x10043_0<- arg1[0] * arg2[2] (_0*_0)
adcx r10, rcx
adcx r11, r12
add rdi, r10; could be done better, if r0 has been u8 as well
adc r11, 0x0; add CF to r0's alloc
add rbp, rdi; could be done better, if r0 has been u8 as well
adcx r11, r8
mov rdx, rbp;
shrd rdx, r11, 52; x28 <- x27_1||x27_0 >> 52
mov r8, 0x1000003d10000 ; moving imm to reg
xchg rdx, r8; 0x1000003d10000, swapping with x28, which is currently in rdx
mulx rcx, r12, r9; x10051_1, x10051_0<- x25 * 0x1000003d10000 (_0*_0)
lea r14, [ r14 + r8 ]
add r12, r14; could be done better, if r0 has been u8 as well
adc rcx, 0x0; add CF to r0's alloc
mov r10, r12;
shrd r10, rcx, 52; x31 <- x30_1||x30_0 >> 52
add r10, [ rsp - 0x20 ]
bzhi rdi, r12, rbx; x32 <- x30_0 (only least 0x34 bits)
mov r9, [ rsp - 0x50 ]; load m64 out1 to register64
mov [ r9 + 0x20 ], r10; out1[4] = x33
bzhi r11, r15, rbx; x17 <- x15_0 (only least 0x34 bits)
bzhi r15, rbp, rbx; x29 <- x27_0 (only least 0x34 bits)
mov [ r9 + 0x10 ], r15; out1[2] = x29
mov [ r9 + 0x0 ], r11; out1[0] = x17
bzhi rbp, r13, rbx; x23 <- x21_0 (only least 0x34 bits)
mov [ r9 + 0x8 ], rbp; out1[1] = x23
mov [ r9 + 0x18 ], rdi; out1[3] = x32
mov rbx, [ rsp - 0x80 ]; pop
mov rbp, [ rsp - 0x78 ]; pop
mov r12, [ rsp - 0x70 ]; pop
mov r13, [ rsp - 0x68 ]; pop
mov r14, [ rsp - 0x60 ]; pop
mov r15, [ rsp - 0x58 ]; pop
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.3378
; seed 0017315411065161 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3329101 ms on 270000 evaluations.
; Time spent for assembling and measuring (initial batch_size=168, initial num_batches=31): 163727 ms
; number of used evaluations: 270000
; Ratio (time for assembling + measure)/(total runtime for 270000 evals): 0.04918054453739914
; number reverted permutation / tried permutation: 96324 / 135048 =71.326%
; number reverted decision / tried decision: 52273 / 134951 =38.735%
; validated in 0.426s
