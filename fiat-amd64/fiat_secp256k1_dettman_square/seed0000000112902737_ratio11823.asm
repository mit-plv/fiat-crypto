SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rax, [ rsi + 0x8 ]; load m64 arg1[1] to register64
lea r10, [rax + rax]; x3 <- arg1[1] * 2 
mov rax, 0x1 ; moving imm to reg
shlx r11, [ rsi + 0x0 ], rax; x4 <- arg1[0] * 0x2 (shlx does not change the flags)
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r8, rcx, rdx; x5_1, x5_0<- arg1[4]^2
mov rdx, r11; x4 to rdx
mulx r9, r11, [ rsi + 0x18 ]; x10000_1, x10000_0<- x4 * arg1[3] (_0*_0)
mov rax, rdx; preserving value of x4 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp - 0x80 ], rbx; spilling calSv-rbx to mem
mov [ rsp - 0x78 ], rbp; spilling calSv-rbp to mem
mulx rbp, rbx, r10; x10001_1, x10001_0<- x3 * arg1[2] (_0*_0)
xor rdx, rdx
adox rbx, r11
adox r9, rbp
mov r11, 0x1000003d10 ; moving imm to reg
mov rdx, rcx; x7 to rdx
mulx rbp, rcx, r11; x10003_1, x10003_0<- x7 * 0x1000003d10 (_0*_0)
adcx rcx, rbx
adcx r9, rbp
mov rbx, rcx;
shrd rbx, r9, 52; x9 <- x8_1||x8_0 >> 52
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r9, rbp, r10; x10005_1, x10005_0<- x3 * arg1[3] (_0*_0)
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp - 0x70 ], r12; spilling calSv-r12 to mem
mov [ rsp - 0x68 ], r13; spilling calSv-r13 to mem
mulx r13, r12, rdx; x10006_1, x10006_0<- arg1[2]^2
xor rdx, rdx
adox r12, rbp
adox r9, r13
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r13, rbp, rax; x10004_1, x10004_0<- x4 * arg1[4] (_0*_0)
mov rdx, 0x1000003d10000 ; moving imm to reg
mov [ rsp - 0x60 ], r14; spilling calSv-r14 to mem
mov [ rsp - 0x58 ], r15; spilling calSv-r15 to mem
mulx r15, r14, r8; x10010_1, x10010_0<- x6 * 0x1000003d10000 (_0*_0)
adcx r12, rbp
adcx r13, r9
xor r9, r9
adox rbx, r12
adox r13, r9
adcx r14, rbx
adcx r13, r15
mov r8, [ rsi + 0x10 ]; load m64 arg1[2] to register64
mov rbp, r8; load m64 x2 to register64
shl rbp, 0x1; x2 <- arg1[2] * 0x2
mov r8, r14;
shrd r8, r13, 52; x12 <- x11_1||x11_0 >> 52
mov rdx, r10; x3 to rdx
mulx r15, r10, [ rsi + 0x20 ]; x10011_1, x10011_0<- x3 * arg1[4] (_0*_0)
mov rdx, rbp; x2 to rdx
mulx r12, rbp, [ rsi + 0x18 ]; x10012_1, x10012_0<- x2 * arg1[3] (_0*_0)
add rbp, r10; could be done better, if r0 has been u8 as well
adcx r15, r12
xor rbx, rbx
adox r8, rbp
adox r15, rbx
mov r9, r8;
shrd r9, r15, 52; x17 <- x16_1||x16_0 >> 52
mov r13, 0xfffffffffffff ; moving imm to reg
and r8, r13; x18 <- x16_0&0xfffffffffffff
shl r8, 4; x10015 <- x18<< 4
mov r10, rdx; preserving value of x2 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx rbp, r12, rdx; x10019_1, x10019_0<- arg1[3]^2
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx rbx, r15, r10; x10018_1, x10018_0<- x2 * arg1[4] (_0*_0)
xor rdx, rdx
adox r12, r15
adox rbx, rbp
and r14, r13; x13 <- x11_0&0xfffffffffffff
adox r9, r12
adox rbx, rdx
mov r10, r14;
shr r10, 48; x14 <- x13>> 48
lea r8, [ r8 + r10 ]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r15, rbp, rdx; x10014_1, x10014_0<- arg1[0]^2
mov rdx, 0x1000003d1 ; moving imm to reg
mulx r10, r12, r8; x10017_1, x10017_0<- x10016 * 0x1000003d1 (_0*_0)
add r12, rbp; could be done better, if r0 has been u8 as well
adcx r15, r10
mov r8, r12;
shrd r8, r15, 52; x20 <- x19_1||x19_0 >> 52
and r12, r13; x21 <- x19_0&0xfffffffffffff
mov rbp, [ rsi + 0x18 ]; load m64 arg1[3] to register64
lea r10, [rbp + rbp]; x1 <- arg1[3] * 2 
mov rdx, r10; x1 to rdx
mulx rbp, r10, [ rsi + 0x20 ]; x10024_1, x10024_0<- x1 * arg1[4] (_0*_0)
mov [ rdi + 0x0 ], r12; out1[0] = x21
mov r15, r9;
shrd r15, rbx, 52; x23 <- x22_1||x22_0 >> 52
xor rbx, rbx
adox r15, r10
adox rbp, rbx
and r9, r13; x24 <- x22_0&0xfffffffffffff
mov rdx, r9; x24 to rdx
mulx r12, r9, r11; x10023_1, x10023_0<- x24 * 0x1000003d10 (_0*_0)
mov rdx, rax; x4 to rdx
mulx r10, rax, [ rsi + 0x8 ]; x10021_1, x10021_0<- x4 * arg1[1] (_0*_0)
adox r8, rax
adox r10, rbx
adcx r9, r8
adcx r10, r12
mov r12, r9;
and r12, r13; x27 <- x25_0&0xfffffffffffff
shrd r9, r10, 52; x26 <- x25_1||x25_0 >> 52
mulx r8, rax, [ rsi + 0x10 ]; x10025_1, x10025_0<- x4 * arg1[2] (_0*_0)
mov [ rdi + 0x8 ], r12; out1[1] = x27
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r12, r10, rdx; x10026_1, x10026_0<- arg1[1]^2
test al, al
adox r10, rax
adox r8, r12
adcx r9, r10
adc r8, 0x0; add CF to r0's alloc
mov rdx, r15; x30 to rdx
mulx rax, r15, r11; x10029_1, x10029_0<- x30 * 0x1000003d10 (_0*_0)
add r15, r9; could be done better, if r0 has been u8 as well
adcx r8, rax
mov r12, r15;
shrd r12, r8, 52; x32 <- x31_1||x31_0 >> 52
mov rdx, 0x1000003d10000 ; moving imm to reg
mulx r9, r10, rbp; x10031_1, x10031_0<- x29 * 0x1000003d10000 (_0*_0)
and rcx, r13; x10 <- x8_0&0xfffffffffffff
lea rcx, [ rcx + r12 ]
adox r10, rcx
adox r9, rbx
mov rax, r10;
and rax, r13; x36 <- x34_0&0xfffffffffffff
shrd r10, r9, 52; x35 <- x34_1||x34_0 >> 52
mov [ rdi + 0x18 ], rax; out1[3] = x36
mov rbp, 0xffffffffffff ; moving imm to reg
and r14, rbp; x15 <- x13&0xffffffffffff
and r15, r13; x33 <- x31_0&0xfffffffffffff
mov [ rdi + 0x10 ], r15; out1[2] = x33
lea r14, [ r14 + r10 ]
mov [ rdi + 0x20 ], r14; out1[4] = x37
mov rbx, [ rsp - 0x80 ]; pop
mov rbp, [ rsp - 0x78 ]; pop
mov r12, [ rsp - 0x70 ]; pop
mov r13, [ rsp - 0x68 ]; pop
mov r14, [ rsp - 0x60 ]; pop
mov r15, [ rsp - 0x58 ]; pop
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.1823
; seed 0612062176262815 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1107256 ms on 270000 evaluations.
; Time spent for assembling and measuring (initial batch_size=381, initial num_batches=31): 126977 ms
; number of used evaluations: 270000
; Ratio (time for assembling + measure)/(total runtime for 270000 evals): 0.1146771839574588
; number reverted permutation / tried permutation: 105075 / 135426 =77.588%
; number reverted decision / tried decision: 98887 / 134573 =73.482%
; validated in 0.181s
