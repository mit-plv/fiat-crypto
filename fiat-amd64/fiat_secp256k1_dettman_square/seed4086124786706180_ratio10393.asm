SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r10, rax, rdx; x5_1, x5_0<- arg1[4]^2
imul r11, [ rsi + 0x8 ], 0x2; x3 <- arg1[1] * 0x2
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r8, rcx, rdx; x10014_1, x10014_0<- arg1[0]^2
mov rdx, [ rsi + 0x10 ]; load m64 arg1[2] to register64
lea r9, [rdx + rdx]; x2 <- arg1[2] * 2 
mov rdx, 0x1 ; moving imm to reg
mov [ rsp - 0x80 ], rbx; spilling calSv-rbx to mem
shlx rbx, [ rsi + 0x0 ], rdx; x4 <- arg1[0] * 0x2 (shlx does not change the flags)
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp - 0x78 ], rbp; spilling calSv-rbp to mem
mov [ rsp - 0x70 ], r12; spilling calSv-r12 to mem
mulx r12, rbp, rbx; x10000_1, x10000_0<- x4 * arg1[3] (_0*_0)
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp - 0x68 ], r13; spilling calSv-r13 to mem
mov [ rsp - 0x60 ], r14; spilling calSv-r14 to mem
mulx r14, r13, r11; x10001_1, x10001_0<- x3 * arg1[2] (_0*_0)
xor rdx, rdx
adox r13, rbp
adox r12, r14
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r14, rbp, rbx; x10004_1, x10004_0<- x4 * arg1[4] (_0*_0)
mov rdx, 0x1000003d10 ; moving imm to reg
mov [ rsp - 0x58 ], r15; spilling calSv-r15 to mem
mov [ rsp - 0x50 ], rdi; spilling out1 to mem
mulx rdi, r15, rax; x10003_1, x10003_0<- x7 * 0x1000003d10 (_0*_0)
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp - 0x48 ], r8; spilling x10014_1 to mem
mulx r8, rax, rdx; x10006_1, x10006_0<- arg1[2]^2
adcx r15, r13
adcx r12, rdi
mov rdx, r11; x3 to rdx
mulx r13, r11, [ rsi + 0x20 ]; x10011_1, x10011_0<- x3 * arg1[4] (_0*_0)
mov [ rsp - 0x40 ], rcx; spilling x10014_0 to mem
mulx rcx, rdi, [ rsi + 0x18 ]; x10005_1, x10005_0<- x3 * arg1[3] (_0*_0)
xor rdx, rdx
adox rax, rdi
adox rcx, r8
adcx rax, rbp
adcx r14, rcx
mov rbp, 0x1000003d10000 ; moving imm to reg
mov rdx, r10; x6 to rdx
mulx r8, r10, rbp; x10010_1, x10010_0<- x6 * 0x1000003d10000 (_0*_0)
mov rdx, r15;
shrd rdx, r12, 52; x9 <- x8_1||x8_0 >> 52
add rdx, rax; could be done better, if r0 has been u8 as well
adc r14, 0x0; add CF to r0's alloc
xor r12, r12
adox r10, rdx
adox r14, r8
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rcx, rdi, rdx; x10019_1, x10019_0<- arg1[3]^2
mov rdx, r9; x2 to rdx
mulx rax, r9, [ rsi + 0x20 ]; x10018_1, x10018_0<- x2 * arg1[4] (_0*_0)
mov r8, 0x34 ; moving imm to reg
bzhi r12, r10, r8; x13 <- x11_0 (only least 0x34 bits)
adox rdi, r9
adox rax, rcx
mulx r9, rcx, [ rsi + 0x18 ]; x10012_1, x10012_0<- x2 * arg1[3] (_0*_0)
add rcx, r11; could be done better, if r0 has been u8 as well
adcx r13, r9
mov rdx, r12;
shr rdx, 48; x14 <- x13>> 48
mov r11, 0xffffffffffff ; moving imm to reg
and r12, r11; x15 <- x13&0xffffffffffff
shrd r10, r14, 52; x12 <- x11_1||x11_0 >> 52
add r10, rcx; could be done better, if r0 has been u8 as well
adc r13, 0x0; add CF to r0's alloc
bzhi r14, r10, r8; x18 <- x16_0 (only least 0x34 bits)
shrd r10, r13, 52; x17 <- x16_1||x16_0 >> 52
add r10, rdi; could be done better, if r0 has been u8 as well
adc rax, 0x0; add CF to r0's alloc
mov rdi, [ rsi + 0x18 ]; load m64 arg1[3] to register64
lea r9, [rdi + rdi]; x1 <- arg1[3] * 2 
mov rdi, rdx; preserving value of x14 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r13, rcx, r9; x10024_1, x10024_0<- x1 * arg1[4] (_0*_0)
shl r14, 4; x10015 <- x18<< 4
lea r14, [ r14 + rdi ]
bzhi rdx, r10, r8; x24 <- x22_0 (only least 0x34 bits)
shrd r10, rax, 52; x23 <- x22_1||x22_0 >> 52
mov rdi, 0x1000003d10 ; moving imm to reg
mulx r9, rax, rdi; x10023_1, x10023_0<- x24 * 0x1000003d10 (_0*_0)
add r10, rcx; could be done better, if r0 has been u8 as well
adc r13, 0x0; add CF to r0's alloc
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r8, rcx, rdx; x10026_1, x10026_0<- arg1[1]^2
mov rdx, 0x1000003d1 ; moving imm to reg
mulx rbp, r11, r14; x10017_1, x10017_0<- x10016 * 0x1000003d1 (_0*_0)
add r11, [ rsp - 0x40 ]; could be done better, if r0 has been u8 as well
adcx rbp, [ rsp - 0x48 ]
mov r14, 0x34 ; moving imm to reg
bzhi rdx, r11, r14; x21 <- x19_0 (only least 0x34 bits)
mov r14, 0x1000003d10000 ; moving imm to reg
xchg rdx, r14; 0x1000003d10000, swapping with x21, which is currently in rdx
mov [ rsp - 0x38 ], r14; spilling x21 to mem
mulx r14, rdi, r13; x10031_1, x10031_0<- x29 * 0x1000003d10000 (_0*_0)
shrd r11, rbp, 52; x20 <- x19_1||x19_0 >> 52
mov rdx, rbx; x4 to rdx
mulx rbp, rbx, [ rsi + 0x8 ]; x10021_1, x10021_0<- x4 * arg1[1] (_0*_0)
xor r13, r13
adox r11, rbx
adox rbp, r13
adcx rax, r11
adcx rbp, r9
mov r9, rax;
shrd r9, rbp, 52; x26 <- x25_1||x25_0 >> 52
mulx r11, rbx, [ rsi + 0x10 ]; x10025_1, x10025_0<- x4 * arg1[2] (_0*_0)
mov rdx, 0x1000003d10 ; moving imm to reg
mulx r13, rbp, r10; x10029_1, x10029_0<- x30 * 0x1000003d10 (_0*_0)
add rcx, rbx; could be done better, if r0 has been u8 as well
adcx r11, r8
xor r10, r10
adox r9, rcx
adox r11, r10
adcx rbp, r9
adcx r11, r13
mov r8, rbp;
shrd r8, r11, 52; x32 <- x31_1||x31_0 >> 52
mov rbx, 0xfffffffffffff ; moving imm to reg
and r15, rbx; x10 <- x8_0&0xfffffffffffff
and rax, rbx; x27 <- x25_0&0xfffffffffffff
lea r15, [ r15 + r8 ]
adox rdi, r15
adox r14, r10
mov r13, rdi;
and r13, rbx; x36 <- x34_0&0xfffffffffffff
shrd rdi, r14, 52; x35 <- x34_1||x34_0 >> 52
lea r12, [ r12 + rdi ]
mov rcx, [ rsp - 0x50 ]; load m64 out1 to register64
mov [ rcx + 0x20 ], r12; out1[4] = x37
mov r9, [ rsp - 0x38 ]; load m64 x21 to register64
mov [ rcx + 0x0 ], r9; out1[0] = x21
and rbp, rbx; x33 <- x31_0&0xfffffffffffff
mov [ rcx + 0x10 ], rbp; out1[2] = x33
mov [ rcx + 0x18 ], r13; out1[3] = x36
mov [ rcx + 0x8 ], rax; out1[1] = x27
mov rbx, [ rsp - 0x80 ]; pop
mov rbp, [ rsp - 0x78 ]; pop
mov r12, [ rsp - 0x70 ]; pop
mov r13, [ rsp - 0x68 ]; pop
mov r14, [ rsp - 0x60 ]; pop
mov r15, [ rsp - 0x58 ]; pop
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.0393
; seed 4086124786706180 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 15046 ms on 1500 evaluations.
; Time spent for assembling and measuring (initial batch_size=399, initial num_batches=31): 1392 ms
; number of used evaluations: 1500
; Ratio (time for assembling + measure)/(total runtime for 1500 evals): 0.09251628339758075
; number reverted permutation / tried permutation: 618 / 782 =79.028%
; number reverted decision / tried decision: 515 / 717 =71.827%
; validated in 0.511s
