SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
imul rax, [ rsi + 0x0 ], 0x2; x4 <- arg1[0] * 0x2
imul r10, [ rsi + 0x8 ], 0x2; x3 <- arg1[1] * 0x2
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rcx, r11, rdx; x10006_1, x10006_0<- arg1[2]^2
mov rdx, [ rsi + 0x10 ]; load m64 arg1[2] to register64
lea r8, [rdx + rdx]; x2 <- arg1[2] * 2 
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp - 0x80 ], rbx; spilling calSv-rbx to mem
mulx rbx, r9, rdx; x5_1, x5_0<- arg1[4]^2
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp - 0x78 ], rbp; spilling calSv-rbp to mem
mov [ rsp - 0x70 ], r12; spilling calSv-r12 to mem
mulx r12, rbp, r10; x10001_1, x10001_0<- x3 * arg1[2] (_0*_0)
mov rdx, 0x1000003d10 ; moving imm to reg
mov [ rsp - 0x68 ], r13; spilling calSv-r13 to mem
mov [ rsp - 0x60 ], r14; spilling calSv-r14 to mem
mulx r14, r13, r9; x10003_1, x10003_0<- x7 * 0x1000003d10 (_0*_0)
mov rdx, r8; x2 to rdx
mulx r9, r8, [ rsi + 0x18 ]; x10012_1, x10012_0<- x2 * arg1[3] (_0*_0)
mov [ rsp - 0x58 ], r15; spilling calSv-r15 to mem
mov r15, rdx; preserving value of x2 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp - 0x50 ], rdi; spilling out1 to mem
mov [ rsp - 0x48 ], r9; spilling x10012_1 to mem
mulx r9, rdi, rax; x10000_1, x10000_0<- x4 * arg1[3] (_0*_0)
add rbp, rdi; could be done better, if r0 has been u8 as well
adcx r9, r12
xor rdx, rdx
adox r13, rbp
adox r9, r14
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r14, r12, r10; x10005_1, x10005_0<- x3 * arg1[3] (_0*_0)
adcx r11, r12
adcx r14, rcx
mov rdx, r13;
shrd rdx, r9, 52; x9 <- x8_1||x8_0 >> 52
mov rcx, rdx; preserving value of x9 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx rbp, rdi, rax; x10004_1, x10004_0<- x4 * arg1[4] (_0*_0)
test al, al
adox r11, rdi
adox rbp, r14
adcx rcx, r11
adc rbp, 0x0; add CF to r0's alloc
mov rdx, 0x1000003d10000 ; moving imm to reg
mulx r12, r9, rbx; x10010_1, x10010_0<- x6 * 0x1000003d10000 (_0*_0)
test al, al
adox r9, rcx
adox rbp, r12
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r14, rbx, r10; x10011_1, x10011_0<- x3 * arg1[4] (_0*_0)
mov rdx, r9;
shrd rdx, rbp, 52; x12 <- x11_1||x11_0 >> 52
xor r10, r10
adox r8, rbx
adox r14, [ rsp - 0x48 ]
adcx rdx, r8
adc r14, 0x0; add CF to r0's alloc
mov rdi, 0xfffffffffffff ; moving imm to reg
and r9, rdi; x13 <- x11_0&0xfffffffffffff
mov r11, rdx; preserving value of x16_0 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r12, rcx, r15; x10018_1, x10018_0<- x2 * arg1[4] (_0*_0)
mov rdx, r11;
and rdx, rdi; x18 <- x16_0&0xfffffffffffff
mov r15, r9;
shr r15, 48; x14 <- x13>> 48
shl rdx, 4; x10015 <- x18<< 4
lea rdx, [ rdx + r15 ]
mov rbp, 0x1000003d1 ; moving imm to reg
mulx r8, rbx, rbp; x10017_1, x10017_0<- x10016 * 0x1000003d1 (_0*_0)
mov r15, 0x1 ; moving imm to reg
shlx rdx, [ rsi + 0x18 ], r15; x1 <- arg1[3] * 0x2 (shlx does not change the flags)
mulx r15, r10, [ rsi + 0x20 ]; x10024_1, x10024_0<- x1 * arg1[4] (_0*_0)
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rdi, rbp, rdx; x10014_1, x10014_0<- arg1[0]^2
xor rdx, rdx
adox rbx, rbp
adox rdi, r8
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rbp, r8, rdx; x10019_1, x10019_0<- arg1[3]^2
shrd r11, r14, 52; x17 <- x16_1||x16_0 >> 52
xor rdx, rdx
adox r8, rcx
adox r12, rbp
adcx r11, r8
adc r12, 0x0; add CF to r0's alloc
mov r14, 0xfffffffffffff ; moving imm to reg
mov rcx, r11;
and rcx, r14; x24 <- x22_0&0xfffffffffffff
shrd r11, r12, 52; x23 <- x22_1||x22_0 >> 52
add r11, r10; could be done better, if r0 has been u8 as well
adc r15, 0x0; add CF to r0's alloc
mov r10, rbx;
shrd r10, rdi, 52; x20 <- x19_1||x19_0 >> 52
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbp, rdi, rax; x10021_1, x10021_0<- x4 * arg1[1] (_0*_0)
mov rdx, 0x1000003d10 ; moving imm to reg
mulx r12, r8, rcx; x10023_1, x10023_0<- x24 * 0x1000003d10 (_0*_0)
xor rcx, rcx
adox r10, rdi
adox rbp, rcx
adcx r8, r10
adcx rbp, r12
mov rdi, r8;
shrd rdi, rbp, 52; x26 <- x25_1||x25_0 >> 52
mov rdx, rax; x4 to rdx
mulx r12, rax, [ rsi + 0x10 ]; x10025_1, x10025_0<- x4 * arg1[2] (_0*_0)
and r8, r14; x27 <- x25_0&0xfffffffffffff
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbp, r10, rdx; x10026_1, x10026_0<- arg1[1]^2
adox r10, rax
adox r12, rbp
adcx rdi, r10
adc r12, 0x0; add CF to r0's alloc
mov rdx, 0x1000003d10 ; moving imm to reg
mulx rbp, rax, r11; x10029_1, x10029_0<- x30 * 0x1000003d10 (_0*_0)
and r13, r14; x10 <- x8_0&0xfffffffffffff
mov r10, 0xffffffffffff ; moving imm to reg
and r9, r10; x15 <- x13&0xffffffffffff
adox rax, rdi
adox r12, rbp
mov rdi, rax;
shrd rdi, r12, 52; x32 <- x31_1||x31_0 >> 52
mov r11, 0x1000003d10000 ; moving imm to reg
mov rdx, r15; x29 to rdx
mulx rbp, r15, r11; x10031_1, x10031_0<- x29 * 0x1000003d10000 (_0*_0)
and rax, r14; x33 <- x31_0&0xfffffffffffff
lea r13, [ r13 + rdi ]
adox r15, r13
adox rbp, rcx
mov rdx, r15;
and rdx, r14; x36 <- x34_0&0xfffffffffffff
mov r12, [ rsp - 0x50 ]; load m64 out1 to register64
mov [ r12 + 0x18 ], rdx; out1[3] = x36
and rbx, r14; x21 <- x19_0&0xfffffffffffff
shrd r15, rbp, 52; x35 <- x34_1||x34_0 >> 52
lea r9, [ r9 + r15 ]
mov [ r12 + 0x8 ], r8; out1[1] = x27
mov [ r12 + 0x0 ], rbx; out1[0] = x21
mov [ r12 + 0x10 ], rax; out1[2] = x33
mov [ r12 + 0x20 ], r9; out1[4] = x37
mov rbx, [ rsp - 0x80 ]; pop
mov rbp, [ rsp - 0x78 ]; pop
mov r12, [ rsp - 0x70 ]; pop
mov r13, [ rsp - 0x68 ]; pop
mov r14, [ rsp - 0x60 ]; pop
mov r15, [ rsp - 0x58 ]; pop
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.3621
; seed 1737016938714990 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1701813 ms on 270000 evaluations.
; Time spent for assembling and measuring (initial batch_size=167, initial num_batches=31): 124313 ms
; number of used evaluations: 270000
; Ratio (time for assembling + measure)/(total runtime for 270000 evals): 0.07304739122336003
; number reverted permutation / tried permutation: 106670 / 134893 =79.077%
; number reverted decision / tried decision: 94546 / 135106 =69.979%
; validated in 0.367s
