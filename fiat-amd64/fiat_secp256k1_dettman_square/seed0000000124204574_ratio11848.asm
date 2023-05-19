SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rax, [ rsi + 0x0 ]; load m64 arg1[0] to register64
lea r10, [rax + rax]; x4 <- arg1[0] * 2 
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r11, rax, rdx; x5_1, x5_0<- arg1[4]^2
mov rdx, [ rsi + 0x8 ]; load m64 arg1[1] to register64
lea rcx, [rdx + rdx]; x3 <- arg1[1] * 2 
mov rdx, r10; x4 to rdx
mulx r8, r10, [ rsi + 0x18 ]; x10000_1, x10000_0<- x4 * arg1[3] (_0*_0)
mov r9, rdx; preserving value of x4 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp - 0x80 ], rbx; spilling calSv-rbx to mem
mov [ rsp - 0x78 ], rbp; spilling calSv-rbp to mem
mulx rbp, rbx, rcx; x10001_1, x10001_0<- x3 * arg1[2] (_0*_0)
xor rdx, rdx
adox rbx, r10
adox r8, rbp
mov r10, 0x1000003d10 ; moving imm to reg
mov rdx, rax; x7 to rdx
mulx rbp, rax, r10; x10003_1, x10003_0<- x7 * 0x1000003d10 (_0*_0)
adcx rax, rbx
adcx r8, rbp
mov rdx, rax;
shrd rdx, r8, 52; x9 <- x8_1||x8_0 >> 52
mov rbx, rdx; preserving value of x9 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r8, rbp, rdx; x10006_1, x10006_0<- arg1[2]^2
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp - 0x70 ], r12; spilling calSv-r12 to mem
mov [ rsp - 0x68 ], r13; spilling calSv-r13 to mem
mulx r13, r12, rcx; x10005_1, x10005_0<- x3 * arg1[3] (_0*_0)
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp - 0x60 ], r14; spilling calSv-r14 to mem
mov [ rsp - 0x58 ], r15; spilling calSv-r15 to mem
mulx r15, r14, r9; x10004_1, x10004_0<- x4 * arg1[4] (_0*_0)
add rbp, r12; could be done better, if r0 has been u8 as well
adcx r13, r8
xor rdx, rdx
adox rbp, r14
adox r15, r13
imul r8, [ rsi + 0x10 ], 0x2; x2 <- arg1[2] * 0x2
xor r12, r12
adox rbx, rbp
adox r15, r12
mov rdx, r8; x2 to rdx
mulx r14, r8, [ rsi + 0x18 ]; x10012_1, x10012_0<- x2 * arg1[3] (_0*_0)
mulx rbp, r13, [ rsi + 0x20 ]; x10018_1, x10018_0<- x2 * arg1[4] (_0*_0)
mov rdx, 0x1000003d10000 ; moving imm to reg
mulx r10, r12, r11; x10010_1, x10010_0<- x6 * 0x1000003d10000 (_0*_0)
adcx r12, rbx
adcx r15, r10
mov r11, r12;
shrd r11, r15, 52; x12 <- x11_1||x11_0 >> 52
mov rbx, 0xfffffffffffff ; moving imm to reg
and r12, rbx; x13 <- x11_0&0xfffffffffffff
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r15, r10, rcx; x10011_1, x10011_0<- x3 * arg1[4] (_0*_0)
adox r8, r10
adox r15, r14
adcx r11, r8
adc r15, 0x0; add CF to r0's alloc
mov rdx, r11;
and rdx, rbx; x18 <- x16_0&0xfffffffffffff
mov rcx, rdx; preserving value of x18 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx r10, r14, rdx; x10019_1, x10019_0<- arg1[3]^2
shrd r11, r15, 52; x17 <- x16_1||x16_0 >> 52
shl rcx, 4; x10015 <- x18<< 4
xor rdx, rdx
adox r14, r13
adox rbp, r10
adcx r11, r14
adc rbp, 0x0; add CF to r0's alloc
mov r13, r11;
shrd r13, rbp, 52; x23 <- x22_1||x22_0 >> 52
and r11, rbx; x24 <- x22_0&0xfffffffffffff
mov r8, r12;
shr r8, 48; x14 <- x13>> 48
mov r15, 0x1 ; moving imm to reg
shlx r10, [ rsi + 0x18 ], r15; x1 <- arg1[3] * 0x2 (shlx does not change the flags)
lea rcx, [ rcx + r8 ]
mov r14, 0x1000003d1 ; moving imm to reg
mov rdx, r14; 0x1000003d1 to rdx
mulx rbp, r14, rcx; x10017_1, x10017_0<- x10016 * 0x1000003d1 (_0*_0)
mov rdx, r10; x1 to rdx
mulx r8, r10, [ rsi + 0x20 ]; x10024_1, x10024_0<- x1 * arg1[4] (_0*_0)
xor rdx, rdx
adox r13, r10
adox r8, rdx
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r10, rcx, rdx; x10014_1, x10014_0<- arg1[0]^2
adcx r14, rcx
adcx r10, rbp
mov rdx, r14;
and rdx, rbx; x21 <- x19_0&0xfffffffffffff
mov [ rdi + 0x0 ], rdx; out1[0] = x21
mov rdx, r9; x4 to rdx
mulx rbp, r9, [ rsi + 0x10 ]; x10025_1, x10025_0<- x4 * arg1[2] (_0*_0)
shrd r14, r10, 52; x20 <- x19_1||x19_0 >> 52
mulx r10, rcx, [ rsi + 0x8 ]; x10021_1, x10021_0<- x4 * arg1[1] (_0*_0)
xor rdx, rdx
adox r14, rcx
adox r10, rdx
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r15, rcx, rdx; x10026_1, x10026_0<- arg1[1]^2
adcx rcx, r9
adcx rbp, r15
mov rdx, 0x1000003d10 ; moving imm to reg
mulx r15, r9, r11; x10023_1, x10023_0<- x24 * 0x1000003d10 (_0*_0)
add r9, r14; could be done better, if r0 has been u8 as well
adcx r10, r15
mov r11, r9;
shrd r11, r10, 52; x26 <- x25_1||x25_0 >> 52
xor r14, r14
adox r11, rcx
adox rbp, r14
and r9, rbx; x27 <- x25_0&0xfffffffffffff
mulx r15, rcx, r13; x10029_1, x10029_0<- x30 * 0x1000003d10 (_0*_0)
mov [ rdi + 0x8 ], r9; out1[1] = x27
and rax, rbx; x10 <- x8_0&0xfffffffffffff
adox rcx, r11
adox rbp, r15
mov r13, rcx;
shrd r13, rbp, 52; x32 <- x31_1||x31_0 >> 52
and rcx, rbx; x33 <- x31_0&0xfffffffffffff
mov [ rdi + 0x10 ], rcx; out1[2] = x33
mov r10, 0x1000003d10000 ; moving imm to reg
mov rdx, r10; 0x1000003d10000 to rdx
mulx r11, r10, r8; x10031_1, x10031_0<- x29 * 0x1000003d10000 (_0*_0)
lea rax, [ rax + r13 ]
adox r10, rax
adox r11, r14
mov r8, r10;
shrd r8, r11, 52; x35 <- x34_1||x34_0 >> 52
and r10, rbx; x36 <- x34_0&0xfffffffffffff
mov [ rdi + 0x18 ], r10; out1[3] = x36
mov r9, 0xffffffffffff ; moving imm to reg
and r12, r9; x15 <- x13&0xffffffffffff
lea r12, [ r12 + r8 ]
mov [ rdi + 0x20 ], r12; out1[4] = x37
mov rbx, [ rsp - 0x80 ]; pop
mov rbp, [ rsp - 0x78 ]; pop
mov r12, [ rsp - 0x70 ]; pop
mov r13, [ rsp - 0x68 ]; pop
mov r14, [ rsp - 0x60 ]; pop
mov r15, [ rsp - 0x58 ]; pop
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.1848
; seed 1144608591132494 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1095512 ms on 270000 evaluations.
; Time spent for assembling and measuring (initial batch_size=369, initial num_batches=31): 127993 ms
; number of used evaluations: 270000
; Ratio (time for assembling + measure)/(total runtime for 270000 evals): 0.11683395526475292
; number reverted permutation / tried permutation: 106286 / 135006 =78.727%
; number reverted decision / tried decision: 99444 / 134993 =73.666%
; validated in 0.181s
