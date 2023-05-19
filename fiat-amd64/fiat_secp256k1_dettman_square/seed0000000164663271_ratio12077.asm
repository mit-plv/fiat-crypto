SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rax, [ rsi + 0x8 ]; load m64 arg1[1] to register64
lea r10, [rax + rax]; x3 <- arg1[1] * 2 
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r11, rax, rdx; x5_1, x5_0<- arg1[4]^2
mov rdx, [ rsi + 0x0 ]; load m64 arg1[0] to register64
mov rcx, rdx; load m64 x4 to register64
shl rcx, 0x1; x4 <- arg1[0] * 0x2
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r9, r8, r10; x10001_1, x10001_0<- x3 * arg1[2] (_0*_0)
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp - 0x80 ], rbx; spilling calSv-rbx to mem
mov [ rsp - 0x78 ], rbp; spilling calSv-rbp to mem
mulx rbp, rbx, rcx; x10000_1, x10000_0<- x4 * arg1[3] (_0*_0)
xor rdx, rdx
adox r8, rbx
adox rbp, r9
mov r9, 0x1000003d10 ; moving imm to reg
mov rdx, rax; x7 to rdx
mulx rbx, rax, r9; x10003_1, x10003_0<- x7 * 0x1000003d10 (_0*_0)
adcx rax, r8
adcx rbp, rbx
mov r8, rax;
shrd r8, rbp, 52; x9 <- x8_1||x8_0 >> 52
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rbp, rbx, rdx; x10006_1, x10006_0<- arg1[2]^2
mov rdx, r10; x3 to rdx
mov [ rsp - 0x70 ], r12; spilling calSv-r12 to mem
mulx r12, r10, [ rsi + 0x18 ]; x10005_1, x10005_0<- x3 * arg1[3] (_0*_0)
mov [ rsp - 0x68 ], r13; spilling calSv-r13 to mem
xor r13, r13
adox rbx, r10
adox r12, rbp
mov rbp, rdx; preserving value of x3 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r13, r10, rcx; x10004_1, x10004_0<- x4 * arg1[4] (_0*_0)
adcx rbx, r10
adcx r13, r12
mov rdx, 0x1000003d10000 ; moving imm to reg
mulx r10, r12, r11; x10010_1, x10010_0<- x6 * 0x1000003d10000 (_0*_0)
mov rdx, rbp; x3 to rdx
mulx r11, rbp, [ rsi + 0x20 ]; x10011_1, x10011_0<- x3 * arg1[4] (_0*_0)
add r8, rbx; could be done better, if r0 has been u8 as well
adc r13, 0x0; add CF to r0's alloc
mov rdx, [ rsi + 0x10 ]; load m64 arg1[2] to register64
lea rbx, [rdx + rdx]; x2 <- arg1[2] * 2 
mov rdx, rbx; x2 to rdx
mov [ rsp - 0x60 ], r14; spilling calSv-r14 to mem
mulx r14, rbx, [ rsi + 0x20 ]; x10018_1, x10018_0<- x2 * arg1[4] (_0*_0)
mov [ rsp - 0x58 ], r15; spilling calSv-r15 to mem
xor r15, r15
adox r12, r8
adox r13, r10
mulx r8, r10, [ rsi + 0x18 ]; x10012_1, x10012_0<- x2 * arg1[3] (_0*_0)
adcx r10, rbp
adcx r11, r8
mov rbp, r12;
shrd rbp, r13, 52; x12 <- x11_1||x11_0 >> 52
add rbp, r10; could be done better, if r0 has been u8 as well
adc r11, 0x0; add CF to r0's alloc
mov rdx, 0xfffffffffffff ; moving imm to reg
mov r13, rbp;
and r13, rdx; x18 <- x16_0&0xfffffffffffff
shl r13, 4; x10015 <- x18<< 4
and r12, rdx; x13 <- x11_0&0xfffffffffffff
mov r8, r12;
shr r8, 48; x14 <- x13>> 48
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r15, r10, rdx; x10019_1, x10019_0<- arg1[3]^2
lea r13, [ r13 + r8 ]
shrd rbp, r11, 52; x17 <- x16_1||x16_0 >> 52
xor rdx, rdx
adox r10, rbx
adox r14, r15
adcx rbp, r10
adc r14, 0x0; add CF to r0's alloc
imul rbx, [ rsi + 0x18 ], 0x2; x1 <- arg1[3] * 0x2
mov r11, rbp;
shrd r11, r14, 52; x23 <- x22_1||x22_0 >> 52
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r15, r8, rdx; x10014_1, x10014_0<- arg1[0]^2
mov rdx, 0x1000003d1 ; moving imm to reg
mulx r14, r10, r13; x10017_1, x10017_0<- x10016 * 0x1000003d1 (_0*_0)
mov rdx, rbx; x1 to rdx
mulx r13, rbx, [ rsi + 0x20 ]; x10024_1, x10024_0<- x1 * arg1[4] (_0*_0)
xor rdx, rdx
adox r11, rbx
adox r13, rdx
adcx r10, r8
adcx r15, r14
mov r8, 0xfffffffffffff ; moving imm to reg
and rbp, r8; x24 <- x22_0&0xfffffffffffff
mov rdx, rbp; x24 to rdx
mulx r14, rbp, r9; x10023_1, x10023_0<- x24 * 0x1000003d10 (_0*_0)
mov rbx, r10;
shrd rbx, r15, 52; x20 <- x19_1||x19_0 >> 52
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r9, r15, rcx; x10021_1, x10021_0<- x4 * arg1[1] (_0*_0)
add rbx, r15; could be done better, if r0 has been u8 as well
adc r9, 0x0; add CF to r0's alloc
xor rdx, rdx
adox rbp, rbx
adox r9, r14
mov r14, rbp;
shrd r14, r9, 52; x26 <- x25_1||x25_0 >> 52
mov rdx, rcx; x4 to rdx
mulx r15, rcx, [ rsi + 0x10 ]; x10025_1, x10025_0<- x4 * arg1[2] (_0*_0)
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r9, rbx, rdx; x10026_1, x10026_0<- arg1[1]^2
add rbx, rcx; could be done better, if r0 has been u8 as well
adcx r15, r9
add r14, rbx; could be done better, if r0 has been u8 as well
adc r15, 0x0; add CF to r0's alloc
mov rdx, 0x1000003d10 ; moving imm to reg
mulx r9, rcx, r11; x10029_1, x10029_0<- x30 * 0x1000003d10 (_0*_0)
xor r11, r11
adox rcx, r14
adox r15, r9
mov rbx, rcx;
shrd rbx, r15, 52; x32 <- x31_1||x31_0 >> 52
and rcx, r8; x33 <- x31_0&0xfffffffffffff
and rax, r8; x10 <- x8_0&0xfffffffffffff
mov [ rdi + 0x10 ], rcx; out1[2] = x33
lea rax, [ rax + rbx ]
mov r14, 0xffffffffffff ; moving imm to reg
and r12, r14; x15 <- x13&0xffffffffffff
and rbp, r8; x27 <- x25_0&0xfffffffffffff
mov [ rdi + 0x8 ], rbp; out1[1] = x27
mov r9, 0x1000003d10000 ; moving imm to reg
mov rdx, r9; 0x1000003d10000 to rdx
mulx r15, r9, r13; x10031_1, x10031_0<- x29 * 0x1000003d10000 (_0*_0)
adox r9, rax
adox r15, r11
and r10, r8; x21 <- x19_0&0xfffffffffffff
mov r13, r9;
shrd r13, r15, 52; x35 <- x34_1||x34_0 >> 52
and r9, r8; x36 <- x34_0&0xfffffffffffff
lea r12, [ r12 + r13 ]
mov [ rdi + 0x20 ], r12; out1[4] = x37
mov [ rdi + 0x0 ], r10; out1[0] = x21
mov [ rdi + 0x18 ], r9; out1[3] = x36
mov rbx, [ rsp - 0x80 ]; pop
mov rbp, [ rsp - 0x78 ]; pop
mov r12, [ rsp - 0x70 ]; pop
mov r13, [ rsp - 0x68 ]; pop
mov r14, [ rsp - 0x60 ]; pop
mov r15, [ rsp - 0x58 ]; pop
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.2077
; seed 2273745575360676 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1103260 ms on 270000 evaluations.
; Time spent for assembling and measuring (initial batch_size=373, initial num_batches=31): 126292 ms
; number of used evaluations: 270000
; Ratio (time for assembling + measure)/(total runtime for 270000 evals): 0.11447165672642895
; number reverted permutation / tried permutation: 106016 / 135090 =78.478%
; number reverted decision / tried decision: 99678 / 134909 =73.885%
; validated in 0.181s
