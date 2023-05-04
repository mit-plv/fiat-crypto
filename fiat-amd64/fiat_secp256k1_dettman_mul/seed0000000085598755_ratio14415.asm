SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
mov rax, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x0 ]; saving arg2[0] in rdx.
mulx r11, r10, [ rsi + 0x20 ]; x10012_1, x10012_0<- arg1[4] * arg2[0] (_0*_0)
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r8, rcx, [ rax + 0x8 ]; x10011_1, x10011_0<- arg1[3] * arg2[1] (_0*_0)
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp - 0x80 ], rbx; spilling calSv-rbx to mem
mulx rbx, r9, [ rax + 0x8 ]; x10022_1, x10022_0<- arg1[4] * arg2[1] (_0*_0)
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp - 0x78 ], rbp; spilling calSv-rbp to mem
mov [ rsp - 0x70 ], r12; spilling calSv-r12 to mem
mulx r12, rbp, [ rsi + 0x20 ]; x1_1, x1_0<- arg1[4] * arg2[4] (_0*_0)
add r10, rcx; could be done better, if r0 has been u8 as well
adcx r8, r11
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx rcx, r11, [ rsi + 0x10 ]; x10002_1, x10002_0<- arg1[2] * arg2[1] (_0*_0)
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp - 0x68 ], r13; spilling calSv-r13 to mem
mov [ rsp - 0x60 ], r14; spilling calSv-r14 to mem
mulx r14, r13, [ rax + 0x0 ]; x10003_1, x10003_0<- arg1[3] * arg2[0] (_0*_0)
add r13, r11; could be done better, if r0 has been u8 as well
adcx rcx, r14
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r14, r11, [ rax + 0x10 ]; x10001_1, x10001_0<- arg1[1] * arg2[2] (_0*_0)
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp - 0x58 ], r15; spilling calSv-r15 to mem
mov [ rsp - 0x50 ], rdi; spilling out1 to mem
mulx rdi, r15, [ rsi + 0x10 ]; x10010_1, x10010_0<- arg1[2] * arg2[2] (_0*_0)
test al, al
adox r10, r15
adox rdi, r8
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r15, r8, [ rax + 0x18 ]; x10000_1, x10000_0<- arg1[0] * arg2[3] (_0*_0)
mov rdx, 0x1000003d10000 ; moving imm to reg
mov [ rsp - 0x48 ], rbx; spilling x10022_1 to mem
mov [ rsp - 0x40 ], r9; spilling x10022_0 to mem
mulx r9, rbx, r12; x10018_1, x10018_0<- x2 * 0x1000003d10000 (_0*_0)
adcx r13, r11
adcx r14, rcx
xor r12, r12
adox r13, r8
adox r15, r14
mov rcx, 0x1000003d10 ; moving imm to reg
mov rdx, rcx; 0x1000003d10 to rdx
mulx r11, rcx, rbp; x10007_1, x10007_0<- x3 * 0x1000003d10 (_0*_0)
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx rbp, r8, [ rsi + 0x18 ]; x10021_1, x10021_0<- arg1[3] * arg2[2] (_0*_0)
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r12, r14, [ rax + 0x18 ]; x10009_1, x10009_0<- arg1[1] * arg2[3] (_0*_0)
adcx r10, r14
adcx r12, rdi
add rcx, r13; could be done better, if r0 has been u8 as well
adcx r15, r11
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx r13, rdi, [ rsi + 0x0 ]; x10008_1, x10008_0<- arg1[0] * arg2[4] (_0*_0)
xor rdx, rdx
adox r10, rdi
adox r13, r12
mov r11, rcx;
shrd r11, r15, 52; x5 <- x4_1||x4_0 >> 52
add r11, r10; could be done better, if r0 has been u8 as well
adc r13, 0x0; add CF to r0's alloc
test al, al
adox rbx, r11
adox r13, r9
mov r9, 0xfffffffffffff ; moving imm to reg
mov r14, rbx;
and r14, r9; x9 <- x7_0&0xfffffffffffff
shrd rbx, r13, 52; x8 <- x7_1||x7_0 >> 52
mov r12, r14;
shr r12, 48; x10 <- x9>> 48
mov r15, r8;
xor rdi, rdi
adox r15, [ rsp - 0x40 ]
adox rbp, [ rsp - 0x48 ]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r10, r8, [ rax + 0x18 ]; x10020_1, x10020_0<- arg1[2] * arg2[3] (_0*_0)
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r13, r11, [ rax + 0x20 ]; x10019_1, x10019_0<- arg1[1] * arg2[4] (_0*_0)
adcx r15, r8
adcx r10, rbp
mov rdx, 0xffffffffffff ; moving imm to reg
and r14, rdx; x11 <- x9&0xffffffffffff
adox r15, r11
adox r13, r10
adcx rbx, r15
adc r13, 0x0; add CF to r0's alloc
mov rbp, rbx;
and rbp, r9; x14 <- x12_0&0xfffffffffffff
shrd rbx, r13, 52; x13 <- x12_1||x12_0 >> 52
shl rbp, 4; x10027 <- x14<< 4
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx r11, r8, [ rsi + 0x10 ]; x10030_1, x10030_0<- arg1[2] * arg2[4] (_0*_0)
lea rbp, [ rbp + r12 ]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx r10, r12, [ rsi + 0x20 ]; x10032_1, x10032_0<- arg1[4] * arg2[2] (_0*_0)
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mulx r13, r15, [ rsi + 0x18 ]; x10031_1, x10031_0<- arg1[3] * arg2[3] (_0*_0)
xor rdx, rdx
adox r12, r15
adox r13, r10
adcx r12, r8
adcx r11, r13
add rbx, r12; could be done better, if r0 has been u8 as well
adc r11, 0x0; add CF to r0's alloc
mov rdi, rbx;
shrd rdi, r11, 52; x19 <- x18_1||x18_0 >> 52
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx r10, r8, [ rsi + 0x0 ]; x10026_1, x10026_0<- arg1[0] * arg2[0] (_0*_0)
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r13, r15, [ rax + 0x20 ]; x10040_1, x10040_0<- arg1[3] * arg2[4] (_0*_0)
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r11, r12, [ rax + 0x18 ]; x10041_1, x10041_0<- arg1[4] * arg2[3] (_0*_0)
test al, al
adox r12, r15
adox r13, r11
adcx rdi, r12
adc r13, 0x0; add CF to r0's alloc
mov rdx, 0x1000003d1 ; moving imm to reg
mulx r11, r15, rbp; x10029_1, x10029_0<- x10028 * 0x1000003d1 (_0*_0)
and rbx, r9; x20 <- x18_0&0xfffffffffffff
adox r15, r8
adox r10, r11
mov rbp, 0x1000003d10 ; moving imm to reg
mov rdx, rbx; x20 to rdx
mulx r8, rbx, rbp; x10039_1, x10039_0<- x20 * 0x1000003d10 (_0*_0)
mov r12, r15;
and r12, r9; x17 <- x15_0&0xfffffffffffff
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r9, r11, [ rax + 0x8 ]; x10035_1, x10035_0<- arg1[0] * arg2[1] (_0*_0)
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mov [ rsp - 0x38 ], r14; spilling x11 to mem
mulx r14, rbp, [ rsi + 0x8 ]; x10036_1, x10036_0<- arg1[1] * arg2[0] (_0*_0)
adox rbp, r11
adox r9, r14
mov rdx, [ rsp - 0x50 ]; load m64 out1 to register64
mov [ rdx + 0x0 ], r12; out1[0] = x17
shrd r15, r10, 52; x16 <- x15_1||x15_0 >> 52
xor r10, r10
adox r15, rbp
adox r9, r10
adcx rbx, r15
adcx r9, r8
mov r8, 0xfffffffffffff ; moving imm to reg
mov r12, rbx;
and r12, r8; x23 <- x21_0&0xfffffffffffff
shrd rbx, r9, 52; x22 <- x21_1||x21_0 >> 52
mov r11, rdx; preserving value of out1 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx rbp, r14, [ rax + 0x8 ]; x10044_1, x10044_0<- arg1[1] * arg2[1] (_0*_0)
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r9, r15, [ rax + 0x0 ]; x10045_1, x10045_0<- arg1[2] * arg2[0] (_0*_0)
xor rdx, rdx
adox r15, r14
adox rbp, r9
mov [ r11 + 0x8 ], r12; out1[1] = x23
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx r12, r10, [ rsi + 0x0 ]; x10043_1, x10043_0<- arg1[0] * arg2[2] (_0*_0)
adcx r15, r10
adcx r12, rbp
and rcx, r8; x6 <- x4_0&0xfffffffffffff
mov rdx, 0x1000003d10 ; moving imm to reg
mulx r9, r14, rdi; x10049_1, x10049_0<- x26 * 0x1000003d10 (_0*_0)
adox rbx, r15
mov rbp, 0x0 ; moving imm to reg
adox r12, rbp
adcx r14, rbx
adcx r12, r9
mov rdi, 0x1000003d10000 ; moving imm to reg
mov rdx, r13; x25 to rdx
mulx r10, r13, rdi; x10051_1, x10051_0<- x25 * 0x1000003d10000 (_0*_0)
mov rdx, r14;
shrd rdx, r12, 52; x28 <- x27_1||x27_0 >> 52
lea rcx, [ rcx + rdx ]
xor r15, r15
adox r13, rcx
adox r10, r15
mov rbp, r13;
shrd rbp, r10, 52; x31 <- x30_1||x30_0 >> 52
add rbp, [ rsp - 0x38 ]
and r14, r8; x29 <- x27_0&0xfffffffffffff
mov [ r11 + 0x10 ], r14; out1[2] = x29
and r13, r8; x32 <- x30_0&0xfffffffffffff
mov [ r11 + 0x18 ], r13; out1[3] = x32
mov [ r11 + 0x20 ], rbp; out1[4] = x33
mov rbx, [ rsp - 0x80 ]; pop
mov rbp, [ rsp - 0x78 ]; pop
mov r12, [ rsp - 0x70 ]; pop
mov r13, [ rsp - 0x68 ]; pop
mov r14, [ rsp - 0x60 ]; pop
mov r15, [ rsp - 0x58 ]; pop
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.4415
; seed 0264257440107563 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1209347 ms on 270000 evaluations.
; Time spent for assembling and measuring (initial batch_size=304, initial num_batches=31): 118109 ms
; number of used evaluations: 270000
; Ratio (time for assembling + measure)/(total runtime for 270000 evals): 0.09766344977909566
; number reverted permutation / tried permutation: 104399 / 134989 =77.339%
; number reverted decision / tried decision: 79910 / 135010 =59.188%
; validated in 0.246s
