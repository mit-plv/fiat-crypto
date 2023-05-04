SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
sub rsp, 144
mov rax, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x10 ]; saving arg2[2] in rdx.
mulx r11, r10, [ rsi + 0x8 ]; x10001_1, x10001_0<- arg1[1] * arg2[2] (_0*_0)
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx r8, rcx, [ rsi + 0x0 ]; x10043_1, x10043_0<- arg1[0] * arg2[2] (_0*_0)
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp - 0x80 ], rbx; spilling calSv-rbx to mem
mulx rbx, r9, [ rsi + 0x18 ]; x10021_1, x10021_0<- arg1[3] * arg2[2] (_0*_0)
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp - 0x78 ], rbp; spilling calSv-rbp to mem
mov [ rsp - 0x70 ], r12; spilling calSv-r12 to mem
mulx r12, rbp, [ rax + 0x20 ]; x1_1, x1_0<- arg1[4] * arg2[4] (_0*_0)
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp - 0x68 ], r13; spilling calSv-r13 to mem
mov [ rsp - 0x60 ], r14; spilling calSv-r14 to mem
mulx r14, r13, [ rax + 0x18 ]; x10020_1, x10020_0<- arg1[2] * arg2[3] (_0*_0)
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp - 0x58 ], r15; spilling calSv-r15 to mem
mov [ rsp - 0x50 ], rdi; spilling out1 to mem
mulx rdi, r15, [ rax + 0x8 ]; x10022_1, x10022_0<- arg1[4] * arg2[1] (_0*_0)
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mov [ rsp - 0x48 ], r8; spilling x10043_1 to mem
mov [ rsp - 0x40 ], rcx; spilling x10043_0 to mem
mulx rcx, r8, [ rsi + 0x18 ]; x10003_1, x10003_0<- arg1[3] * arg2[0] (_0*_0)
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp - 0x38 ], r14; spilling x10020_1 to mem
mov [ rsp - 0x30 ], r13; spilling x10020_0 to mem
mulx r13, r14, [ rax + 0x8 ]; x10035_1, x10035_0<- arg1[0] * arg2[1] (_0*_0)
test al, al
adox r15, r9
adox rbx, rdi
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx rdi, r9, [ rsi + 0x10 ]; x10002_1, x10002_0<- arg1[2] * arg2[1] (_0*_0)
mov rdx, 0x1000003d10 ; moving imm to reg
mov [ rsp - 0x28 ], r13; spilling x10035_1 to mem
mov [ rsp - 0x20 ], r14; spilling x10035_0 to mem
mulx r14, r13, rbp; x10007_1, x10007_0<- x3 * 0x1000003d10 (_0*_0)
adcx r8, r9
adcx rdi, rcx
xor rbp, rbp
adox r8, r10
adox r11, rdi
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rcx, r10, [ rax + 0x18 ]; x10000_1, x10000_0<- arg1[0] * arg2[3] (_0*_0)
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx rdi, r9, [ rsi + 0x18 ]; x10011_1, x10011_0<- arg1[3] * arg2[1] (_0*_0)
adcx r8, r10
adcx rcx, r11
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r10, r11, [ rax + 0x0 ]; x10012_1, x10012_0<- arg1[4] * arg2[0] (_0*_0)
xor rdx, rdx
adox r11, r9
adox rdi, r10
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r9, rbp, [ rax + 0x18 ]; x10041_1, x10041_0<- arg1[4] * arg2[3] (_0*_0)
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp - 0x18 ], r9; spilling x10041_1 to mem
mulx r9, r10, [ rax + 0x10 ]; x10010_1, x10010_0<- arg1[2] * arg2[2] (_0*_0)
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp - 0x10 ], rbp; spilling x10041_0 to mem
mov [ rsp - 0x8 ], rbx; spilling x10023_1 to mem
mulx rbx, rbp, [ rsi + 0x20 ]; x10032_1, x10032_0<- arg1[4] * arg2[2] (_0*_0)
adcx r11, r10
adcx r9, rdi
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r10, rdi, [ rax + 0x18 ]; x10009_1, x10009_0<- arg1[1] * arg2[3] (_0*_0)
xor rdx, rdx
adox r13, r8
adox rcx, r14
adcx r11, rdi
adcx r10, r9
mov r14, r13;
shrd r14, rcx, 52; x5 <- x4_1||x4_0 >> 52
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx r9, r8, [ rsi + 0x0 ]; x10008_1, x10008_0<- arg1[0] * arg2[4] (_0*_0)
xor rdx, rdx
adox r11, r8
adox r9, r10
adcx r15, [ rsp - 0x30 ]
mov rdi, [ rsp - 0x38 ]; load m64 x10020_1 to register64
adcx rdi, [ rsp - 0x8 ]
mov rcx, 0x1000003d10000 ; moving imm to reg
mov rdx, r12; x2 to rdx
mulx r10, r12, rcx; x10018_1, x10018_0<- x2 * 0x1000003d10000 (_0*_0)
test al, al
adox r14, r11
mov r8, 0x0 ; moving imm to reg
adox r9, r8
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r8, r11, [ rax + 0x0 ]; x10045_1, x10045_0<- arg1[2] * arg2[0] (_0*_0)
adcx r12, r14
adcx r9, r10
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r14, r10, [ rax + 0x20 ]; x10019_1, x10019_0<- arg1[1] * arg2[4] (_0*_0)
mov rdx, 0x34 ; moving imm to reg
bzhi rcx, r12, rdx; x9 <- x7_0 (only least 0x34 bits)
shrd r12, r9, 52; x8 <- x7_1||x7_0 >> 52
xor r9, r9
adox r15, r10
adox r14, rdi
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx r10, rdi, [ rsi + 0x8 ]; x10044_1, x10044_0<- arg1[1] * arg2[1] (_0*_0)
adcx r11, rdi
adcx r10, r8
mov rdx, 0xffffffffffff ; moving imm to reg
mov r8, rcx;
and r8, rdx; x11 <- x9&0xffffffffffff
adox r12, r15
adox r14, r9
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rdi, r15, [ rax + 0x18 ]; x10031_1, x10031_0<- arg1[3] * arg2[3] (_0*_0)
mov rdx, r12;
shrd rdx, r14, 52; x13 <- x12_1||x12_0 >> 52
mov r14, 0xfffffffffffff ; moving imm to reg
and r12, r14; x14 <- x12_0&0xfffffffffffff
adox rbp, r15
adox rdi, rbx
mov rbx, rdx; preserving value of x13 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r9, r15, [ rax + 0x20 ]; x10030_1, x10030_0<- arg1[2] * arg2[4] (_0*_0)
adcx rbp, r15
adcx r9, rdi
xor rdx, rdx
adox rbx, rbp
adox r9, rdx
mov rdi, rbx;
shrd rdi, r9, 52; x19 <- x18_1||x18_0 >> 52
shr rcx, 48; x10 <- x9>> 48
test al, al
adox r11, [ rsp - 0x40 ]
adox r10, [ rsp - 0x48 ]
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx rbp, r15, [ rsi + 0x8 ]; x10036_1, x10036_0<- arg1[1] * arg2[0] (_0*_0)
shl r12, 4; x10027 <- x14<< 4
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r14, r9, [ rax + 0x20 ]; x10040_1, x10040_0<- arg1[3] * arg2[4] (_0*_0)
lea r12, [ r12 + rcx ]
mov rdx, 0x1000003d1 ; moving imm to reg
mov [ rsp + 0x0 ], r8; spilling x11 to mem
mulx r8, rcx, r12; x10029_1, x10029_0<- x10028 * 0x1000003d1 (_0*_0)
mov r12, r9;
xor rdx, rdx
adox r12, [ rsp - 0x10 ]
adox r14, [ rsp - 0x18 ]
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x8 ], r10; spilling x10047_1 to mem
mulx r10, r9, [ rsi + 0x0 ]; x10026_1, x10026_0<- arg1[0] * arg2[0] (_0*_0)
adcx rdi, r12
adc r14, 0x0; add CF to r0's alloc
mov rdx, 0xfffffffffffff ; moving imm to reg
and rbx, rdx; x20 <- x18_0&0xfffffffffffff
adox r15, [ rsp - 0x20 ]
adox rbp, [ rsp - 0x28 ]
adcx rcx, r9
adcx r10, r8
mov r8, rcx;
shrd r8, r10, 52; x16 <- x15_1||x15_0 >> 52
mov r12, 0x1000003d10000 ; moving imm to reg
mov rdx, r14; x25 to rdx
mulx r9, r14, r12; x10051_1, x10051_0<- x25 * 0x1000003d10000 (_0*_0)
xor r10, r10
adox r8, r15
adox rbp, r10
mov r15, 0x1000003d10 ; moving imm to reg
mov rdx, r15; 0x1000003d10 to rdx
mulx r10, r15, rbx; x10039_1, x10039_0<- x20 * 0x1000003d10 (_0*_0)
adcx r15, r8
adcx rbp, r10
mov rbx, 0xfffffffffffff ; moving imm to reg
and rcx, rbx; x17 <- x15_0&0xfffffffffffff
mov r8, r15;
and r8, rbx; x23 <- x21_0&0xfffffffffffff
and r13, rbx; x6 <- x4_0&0xfffffffffffff
mov r10, [ rsp - 0x50 ]; load m64 out1 to register64
mov [ r10 + 0x0 ], rcx; out1[0] = x17
mov [ r10 + 0x8 ], r8; out1[1] = x23
shrd r15, rbp, 52; x22 <- x21_1||x21_0 >> 52
mulx rcx, rbp, rdi; x10049_1, x10049_0<- x26 * 0x1000003d10 (_0*_0)
xor r8, r8
adox r15, r11
mov rdi, [ rsp + 0x8 ];
adox rdi, r8
adcx rbp, r15
adcx rdi, rcx
mov r11, rbp;
shrd r11, rdi, 52; x28 <- x27_1||x27_0 >> 52
lea r13, [ r13 + r11 ]
add r14, r13; could be done better, if r0 has been u8 as well
adc r9, 0x0; add CF to r0's alloc
mov rcx, r14;
and rcx, rbx; x32 <- x30_0&0xfffffffffffff
and rbp, rbx; x29 <- x27_0&0xfffffffffffff
mov [ r10 + 0x10 ], rbp; out1[2] = x29
shrd r14, r9, 52; x31 <- x30_1||x30_0 >> 52
add r14, [ rsp + 0x0 ]
mov [ r10 + 0x18 ], rcx; out1[3] = x32
mov [ r10 + 0x20 ], r14; out1[4] = x33
mov rbx, [ rsp - 0x80 ]; pop
mov rbp, [ rsp - 0x78 ]; pop
mov r12, [ rsp - 0x70 ]; pop
mov r13, [ rsp - 0x68 ]; pop
mov r14, [ rsp - 0x60 ]; pop
mov r15, [ rsp - 0x58 ]; pop
add rsp, 144
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.2375
; seed 0840662850038204 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 20193 ms on 1500 evaluations.
; Time spent for assembling and measuring (initial batch_size=153, initial num_batches=31): 947 ms
; number of used evaluations: 1500
; Ratio (time for assembling + measure)/(total runtime for 1500 evals): 0.0468974397068291
; number reverted permutation / tried permutation: 450 / 717 =62.762%
; number reverted decision / tried decision: 323 / 782 =41.304%
; validated in 0.565s
