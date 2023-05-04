SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r10, rax, rdx; x10006_1, x10006_0<- arg1[2]^2
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx rcx, r11, rdx; x5_1, x5_0<- arg1[4]^2
mov rdx, [ rsi + 0x8 ]; load m64 arg1[1] to register64
mov r8, rdx; load m64 x3 to register64
shl r8, 0x1; x3 <- arg1[1] * 0x2
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp - 0x80 ], rbx; spilling calSv-rbx to mem
mulx rbx, r9, r8; x10001_1, x10001_0<- x3 * arg1[2] (_0*_0)
mov rdx, r8; x3 to rdx
mov [ rsp - 0x78 ], rbp; spilling calSv-rbp to mem
mulx rbp, r8, [ rsi + 0x18 ]; x10005_1, x10005_0<- x3 * arg1[3] (_0*_0)
add rax, r8; could be done better, if r0 has been u8 as well
adcx rbp, r10
mov r10, 0x1000003d10 ; moving imm to reg
xchg rdx, r11; x7, swapping with x3, which is currently in rdx
mov [ rsp - 0x70 ], r12; spilling calSv-r12 to mem
mulx r12, r8, r10; x10003_1, x10003_0<- x7 * 0x1000003d10 (_0*_0)
mov rdx, [ rsi + 0x10 ]; load m64 arg1[2] to register64
mov [ rsp - 0x68 ], r13; spilling calSv-r13 to mem
mov r13, rdx; load m64 x2 to register64
shl r13, 0x1; x2 <- arg1[2] * 0x2
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp - 0x60 ], r14; spilling calSv-r14 to mem
mov [ rsp - 0x58 ], r15; spilling calSv-r15 to mem
mulx r15, r14, r13; x10018_1, x10018_0<- x2 * arg1[4] (_0*_0)
mov rdx, 0x1 ; moving imm to reg
shlx r10, [ rsi + 0x0 ], rdx; x4 <- arg1[0] * 0x2 (shlx does not change the flags)
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp - 0x50 ], rdi; spilling out1 to mem
mov [ rsp - 0x48 ], rcx; spilling x6 to mem
mulx rcx, rdi, rdx; x10019_1, x10019_0<- arg1[3]^2
xor rdx, rdx
adox rdi, r14
adox r15, rcx
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rcx, r14, r10; x10021_1, x10021_0<- x4 * arg1[1] (_0*_0)
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp - 0x40 ], rcx; spilling x10021_1 to mem
mov [ rsp - 0x38 ], r14; spilling x10021_0 to mem
mulx r14, rcx, r10; x10000_1, x10000_0<- x4 * arg1[3] (_0*_0)
adcx r9, rcx
adcx r14, rbx
xor rdx, rdx
adox r8, r9
adox r14, r12
mov rbx, r8;
shrd rbx, r14, 52; x9 <- x8_1||x8_0 >> 52
mov rdx, r11; x3 to rdx
mulx r12, r11, [ rsi + 0x20 ]; x10011_1, x10011_0<- x3 * arg1[4] (_0*_0)
mov rdx, r10; x4 to rdx
mulx rcx, r10, [ rsi + 0x20 ]; x10004_1, x10004_0<- x4 * arg1[4] (_0*_0)
xor r9, r9
adox rax, r10
adox rcx, rbp
adcx rbx, rax
adc rcx, 0x0; add CF to r0's alloc
mov rbp, rdx; preserving value of x4 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx r10, r14, r13; x10012_1, x10012_0<- x2 * arg1[3] (_0*_0)
xor rdx, rdx
adox r14, r11
adox r12, r10
mov r9, 0x1000003d10000 ; moving imm to reg
mov rdx, r9; 0x1000003d10000 to rdx
mulx r13, r9, [ rsp - 0x48 ]; x10010_1, x10010_0<- x6 * 0x1000003d10000 (_0*_0)
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rax, r11, rdx; x10026_1, x10026_0<- arg1[1]^2
adcx r9, rbx
adcx rcx, r13
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r10, rbx, rbp; x10025_1, x10025_0<- x4 * arg1[2] (_0*_0)
mov rdx, r9;
shrd rdx, rcx, 52; x12 <- x11_1||x11_0 >> 52
add r11, rbx; could be done better, if r0 has been u8 as well
adcx r10, rax
mov rbp, 0xfffffffffffff ; moving imm to reg
and r8, rbp; x10 <- x8_0&0xfffffffffffff
adox rdx, r14
mov r13, 0x0 ; moving imm to reg
adox r12, r13
mov r14, rdx;
and r14, rbp; x18 <- x16_0&0xfffffffffffff
shrd rdx, r12, 52; x17 <- x16_1||x16_0 >> 52
xor rax, rax
adox rdx, rdi
adox r15, rax
mov r13, rdx;
shrd r13, r15, 52; x23 <- x22_1||x22_0 >> 52
shl r14, 4; x10015 <- x18<< 4
mov rdi, [ rsi + 0x18 ]; load m64 arg1[3] to register64
mov rcx, rdi; load m64 x1 to register64
shl rcx, 0x1; x1 <- arg1[3] * 0x2
mov rdi, rdx; preserving value of x22_0 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r12, rbx, rcx; x10024_1, x10024_0<- x1 * arg1[4] (_0*_0)
and rdi, rbp; x24 <- x22_0&0xfffffffffffff
adox r13, rbx
adox r12, rax
and r9, rbp; x13 <- x11_0&0xfffffffffffff
mov rdx, r9;
shr rdx, 48; x14 <- x13>> 48
lea r14, [ r14 + rdx ]
mov r15, 0x1000003d1 ; moving imm to reg
mov rdx, r14; x10016 to rdx
mulx rcx, r14, r15; x10017_1, x10017_0<- x10016 * 0x1000003d1 (_0*_0)
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rax, rbx, rdx; x10014_1, x10014_0<- arg1[0]^2
xor rdx, rdx
adox r14, rbx
adox rax, rcx
mov rcx, r14;
and rcx, rbp; x21 <- x19_0&0xfffffffffffff
shrd r14, rax, 52; x20 <- x19_1||x19_0 >> 52
mov rbx, 0x1000003d10 ; moving imm to reg
mov rdx, r13; x30 to rdx
mulx rax, r13, rbx; x10029_1, x10029_0<- x30 * 0x1000003d10 (_0*_0)
mov rdx, rdi; x24 to rdx
mulx r15, rdi, rbx; x10023_1, x10023_0<- x24 * 0x1000003d10 (_0*_0)
xor rdx, rdx
adox r14, [ rsp - 0x38 ]
mov rbx, [ rsp - 0x40 ];
adox rbx, rdx
adcx rdi, r14
adcx rbx, r15
mov r15, rdi;
shrd r15, rbx, 52; x26 <- x25_1||x25_0 >> 52
and rdi, rbp; x27 <- x25_0&0xfffffffffffff
mov r14, [ rsp - 0x50 ]; load m64 out1 to register64
mov [ r14 + 0x8 ], rdi; out1[1] = x27
adox r15, r11
adox r10, rdx
adcx r13, r15
adcx r10, rax
mov r11, r13;
and r11, rbp; x33 <- x31_0&0xfffffffffffff
mov rax, 0x1000003d10000 ; moving imm to reg
mov rdx, rax; 0x1000003d10000 to rdx
mulx rbx, rax, r12; x10031_1, x10031_0<- x29 * 0x1000003d10000 (_0*_0)
shrd r13, r10, 52; x32 <- x31_1||x31_0 >> 52
lea r8, [ r8 + r13 ]
mov [ r14 + 0x10 ], r11; out1[2] = x33
xor rdi, rdi
adox rax, r8
adox rbx, rdi
mov r15, rax;
and r15, rbp; x36 <- x34_0&0xfffffffffffff
mov r10, 0xffffffffffff ; moving imm to reg
and r9, r10; x15 <- x13&0xffffffffffff
mov [ r14 + 0x18 ], r15; out1[3] = x36
mov [ r14 + 0x0 ], rcx; out1[0] = x21
shrd rax, rbx, 52; x35 <- x34_1||x34_0 >> 52
lea r9, [ r9 + rax ]
mov [ r14 + 0x20 ], r9; out1[4] = x37
mov rbx, [ rsp - 0x80 ]; pop
mov rbp, [ rsp - 0x78 ]; pop
mov r12, [ rsp - 0x70 ]; pop
mov r13, [ rsp - 0x68 ]; pop
mov r14, [ rsp - 0x60 ]; pop
mov r15, [ rsp - 0x58 ]; pop
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 0.9910
; seed 3939486227538568 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 9302 ms on 1500 evaluations.
; Time spent for assembling and measuring (initial batch_size=244, initial num_batches=31): 646 ms
; number of used evaluations: 1500
; Ratio (time for assembling + measure)/(total runtime for 1500 evals): 0.0694474306600731
; number reverted permutation / tried permutation: 579 / 764 =75.785%
; number reverted decision / tried decision: 453 / 735 =61.633%
; validated in 0.22s
