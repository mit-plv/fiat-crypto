SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rax, 0x1 ; moving imm to reg
shlx r10, [ rsi + 0x10 ], rax; x2 <- arg1[2] * 0x2 (shlx does not change the flags)
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx rcx, r11, rdx; x5_1, x5_0<- arg1[4]^2
mov rdx, [ rsi + 0x0 ]; load m64 arg1[0] to register64
mov r8, rdx; load m64 x4 to register64
shl r8, 0x1; x4 <- arg1[0] * 0x2
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rax, r9, r8; x10000_1, x10000_0<- x4 * arg1[3] (_0*_0)
mov rdx, 0x1000003d10 ; moving imm to reg
mov [ rsp - 0x80 ], rbx; spilling calSv-rbx to mem
mov [ rsp - 0x78 ], rbp; spilling calSv-rbp to mem
mulx rbp, rbx, r11; x10003_1, x10003_0<- x7 * 0x1000003d10 (_0*_0)
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp - 0x70 ], r12; spilling calSv-r12 to mem
mulx r12, r11, rdx; x10026_1, x10026_0<- arg1[1]^2
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp - 0x68 ], r13; spilling calSv-r13 to mem
mov [ rsp - 0x60 ], r14; spilling calSv-r14 to mem
mulx r14, r13, r8; x10021_1, x10021_0<- x4 * arg1[1] (_0*_0)
mov rdx, [ rsi + 0x8 ]; load m64 arg1[1] to register64
mov [ rsp - 0x58 ], r15; spilling calSv-r15 to mem
lea r15, [rdx + rdx]; x3 <- arg1[1] * 2 
mov rdx, r15; x3 to rdx
mov [ rsp - 0x50 ], rdi; spilling out1 to mem
mulx rdi, r15, [ rsi + 0x10 ]; x10001_1, x10001_0<- x3 * arg1[2] (_0*_0)
mov [ rsp - 0x48 ], r12; spilling x10026_1 to mem
xor r12, r12
adox r15, r9
adox rax, rdi
adcx rbx, r15
adcx rax, rbp
mulx rbp, r9, [ rsi + 0x20 ]; x10011_1, x10011_0<- x3 * arg1[4] (_0*_0)
mov rdi, rbx;
shrd rdi, rax, 52; x9 <- x8_1||x8_0 >> 52
mov r15, rdx; preserving value of x3 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r12, rax, rdx; x10006_1, x10006_0<- arg1[2]^2
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp - 0x40 ], r11; spilling x10026_0 to mem
mov [ rsp - 0x38 ], r14; spilling x10021_1 to mem
mulx r14, r11, r15; x10005_1, x10005_0<- x3 * arg1[3] (_0*_0)
xor rdx, rdx
adox rax, r11
adox r14, r12
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r12, r15, r8; x10004_1, x10004_0<- x4 * arg1[4] (_0*_0)
adcx rax, r15
adcx r12, r14
xor rdx, rdx
adox rdi, rax
adox r12, rdx
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r14, r11, r10; x10012_1, x10012_0<- x2 * arg1[3] (_0*_0)
mov rdx, 0x1000003d10000 ; moving imm to reg
mulx rax, r15, rcx; x10010_1, x10010_0<- x6 * 0x1000003d10000 (_0*_0)
adcx r15, rdi
adcx r12, rax
mov rcx, r15;
shrd rcx, r12, 52; x12 <- x11_1||x11_0 >> 52
mov rdi, 0x34 ; moving imm to reg
bzhi rax, r15, rdi; x13 <- x11_0 (only least 0x34 bits)
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r12, r15, rdx; x10019_1, x10019_0<- arg1[3]^2
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp - 0x30 ], r13; spilling x10021_0 to mem
mulx r13, rdi, r10; x10018_1, x10018_0<- x2 * arg1[4] (_0*_0)
adox r15, rdi
adox r13, r12
xor rdx, rdx
adox r11, r9
adox rbp, r14
adcx rcx, r11
adc rbp, 0x0; add CF to r0's alloc
mov r10, rcx;
shrd r10, rbp, 52; x17 <- x16_1||x16_0 >> 52
mov r9, 0xfffffffffffff ; moving imm to reg
and rcx, r9; x18 <- x16_0&0xfffffffffffff
shl rcx, 4; x10015 <- x18<< 4
mov r14, rax;
shr r14, 48; x14 <- x13>> 48
xor r12, r12
adox r10, r15
adox r13, r12
lea rcx, [ rcx + r14 ]
mov rdx, 0x1000003d1 ; moving imm to reg
mulx r15, rdi, rcx; x10017_1, x10017_0<- x10016 * 0x1000003d1 (_0*_0)
mov r11, r10;
shrd r11, r13, 52; x23 <- x22_1||x22_0 >> 52
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r14, rbp, rdx; x10014_1, x10014_0<- arg1[0]^2
mov rdx, [ rsi + 0x18 ]; load m64 arg1[3] to register64
lea r13, [rdx + rdx]; x1 <- arg1[3] * 2 
test al, al
adox rdi, rbp
adox r14, r15
mov rdx, r13; x1 to rdx
mulx rcx, r13, [ rsi + 0x20 ]; x10024_1, x10024_0<- x1 * arg1[4] (_0*_0)
adcx r11, r13
adc rcx, 0x0; add CF to r0's alloc
mov r15, rdi;
shrd r15, r14, 52; x20 <- x19_1||x19_0 >> 52
mov rbp, 0x1000003d10000 ; moving imm to reg
mov rdx, rcx; x29 to rdx
mulx r14, rcx, rbp; x10031_1, x10031_0<- x29 * 0x1000003d10000 (_0*_0)
mov r13, 0x30 ; moving imm to reg
bzhi rdx, rax, r13; x15 <- x13 (only least 0x30 bits)
adox r15, [ rsp - 0x30 ]
mov rax, [ rsp - 0x38 ];
adox rax, r12
and r10, r9; x24 <- x22_0&0xfffffffffffff
and rdi, r9; x21 <- x19_0&0xfffffffffffff
xchg rdx, r8; x4, swapping with x15, which is currently in rdx
mulx r13, r12, [ rsi + 0x10 ]; x10025_1, x10025_0<- x4 * arg1[2] (_0*_0)
mov rdx, [ rsp - 0x50 ]; load m64 out1 to register64
mov [ rdx + 0x0 ], rdi; out1[0] = x21
mov rdi, r12;
adox rdi, [ rsp - 0x40 ]
adox r13, [ rsp - 0x48 ]
mov r12, 0x1000003d10 ; moving imm to reg
xchg rdx, r10; x24, swapping with out1, which is currently in rdx
mulx rbp, r9, r12; x10023_1, x10023_0<- x24 * 0x1000003d10 (_0*_0)
adcx r9, r15
adcx rax, rbp
mov r15, r9;
shrd r15, rax, 52; x26 <- x25_1||x25_0 >> 52
xor rdx, rdx
adox r15, rdi
adox r13, rdx
mov rdx, r12; 0x1000003d10 to rdx
mulx rdi, r12, r11; x10029_1, x10029_0<- x30 * 0x1000003d10 (_0*_0)
adcx r12, r15
adcx r13, rdi
mov r11, 0xfffffffffffff ; moving imm to reg
mov rbp, r12;
and rbp, r11; x33 <- x31_0&0xfffffffffffff
and r9, r11; x27 <- x25_0&0xfffffffffffff
shrd r12, r13, 52; x32 <- x31_1||x31_0 >> 52
and rbx, r11; x10 <- x8_0&0xfffffffffffff
lea rbx, [ rbx + r12 ]
mov [ r10 + 0x8 ], r9; out1[1] = x27
mov [ r10 + 0x10 ], rbp; out1[2] = x33
adox rcx, rbx
mov rax, 0x0 ; moving imm to reg
adox r14, rax
mov r15, rcx;
shrd r15, r14, 52; x35 <- x34_1||x34_0 >> 52
lea r8, [ r8 + r15 ]
mov [ r10 + 0x20 ], r8; out1[4] = x37
and rcx, r11; x36 <- x34_0&0xfffffffffffff
mov [ r10 + 0x18 ], rcx; out1[3] = x36
mov rbx, [ rsp - 0x80 ]; pop
mov rbp, [ rsp - 0x78 ]; pop
mov r12, [ rsp - 0x70 ]; pop
mov r13, [ rsp - 0x68 ]; pop
mov r14, [ rsp - 0x60 ]; pop
mov r15, [ rsp - 0x58 ]; pop
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.0650
; seed 2684978780257334 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2274474 ms on 270000 evaluations.
; Time spent for assembling and measuring (initial batch_size=264, initial num_batches=31): 154929 ms
; number of used evaluations: 270000
; Ratio (time for assembling + measure)/(total runtime for 270000 evals): 0.06811640845311927
; number reverted permutation / tried permutation: 107102 / 134739 =79.488%
; number reverted decision / tried decision: 80799 / 135260 =59.736%
; validated in 0.268s
