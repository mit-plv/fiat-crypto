SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rax, [ rsi + 0x8 ]; load m64 arg1[1] to register64
lea r10, [rax + rax]; x3 <- arg1[1] * 2 
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r11, rax, rdx; x5_1, x5_0<- arg1[4]^2
mov rdx, [ rsi + 0x0 ]; load m64 arg1[0] to register64
lea rcx, [rdx + rdx]; x4 <- arg1[0] * 2 
mov rdx, rcx; x4 to rdx
mulx r8, rcx, [ rsi + 0x18 ]; x10000_1, x10000_0<- x4 * arg1[3] (_0*_0)
mov r9, rdx; preserving value of x4 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp - 0x80 ], rbx; spilling calSv-rbx to mem
mov [ rsp - 0x78 ], rbp; spilling calSv-rbp to mem
mulx rbp, rbx, r10; x10001_1, x10001_0<- x3 * arg1[2] (_0*_0)
mov rdx, 0x1000003d10 ; moving imm to reg
mov [ rsp - 0x70 ], r12; spilling calSv-r12 to mem
mov [ rsp - 0x68 ], r13; spilling calSv-r13 to mem
mulx r13, r12, rax; x10003_1, x10003_0<- x7 * 0x1000003d10 (_0*_0)
xor rax, rax
adox rbx, rcx
adox r8, rbp
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rbp, rcx, rdx; x10006_1, x10006_0<- arg1[2]^2
adcx r12, rbx
adcx r8, r13
mov rdx, r10; x3 to rdx
mulx r13, r10, [ rsi + 0x18 ]; x10005_1, x10005_0<- x3 * arg1[3] (_0*_0)
add rcx, r10; could be done better, if r0 has been u8 as well
adcx r13, rbp
mov rbx, r12;
shrd rbx, r8, 52; x9 <- x8_1||x8_0 >> 52
mov rbp, rdx; preserving value of x3 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r10, r8, r9; x10004_1, x10004_0<- x4 * arg1[4] (_0*_0)
xor rdx, rdx
adox rcx, r8
adox r10, r13
mov rax, 0x1000003d10000 ; moving imm to reg
mov rdx, rax; 0x1000003d10000 to rdx
mulx r13, rax, r11; x10010_1, x10010_0<- x6 * 0x1000003d10000 (_0*_0)
adcx rbx, rcx
adc r10, 0x0; add CF to r0's alloc
add rax, rbx; could be done better, if r0 has been u8 as well
adcx r10, r13
mov r8, rax;
shrd r8, r10, 52; x12 <- x11_1||x11_0 >> 52
mov r11, [ rsi + 0x10 ]; load m64 arg1[2] to register64
lea rcx, [r11 + r11]; x2 <- arg1[2] * 2 
mov r11, 0xfffffffffffff ; moving imm to reg
and rax, r11; x13 <- x11_0&0xfffffffffffff
mov rdx, rcx; x2 to rdx
mulx r13, rcx, [ rsi + 0x20 ]; x10018_1, x10018_0<- x2 * arg1[4] (_0*_0)
mulx r10, rbx, [ rsi + 0x18 ]; x10012_1, x10012_0<- x2 * arg1[3] (_0*_0)
mov rdx, rbp; x3 to rdx
mov [ rsp - 0x60 ], r14; spilling calSv-r14 to mem
mulx r14, rbp, [ rsi + 0x20 ]; x10011_1, x10011_0<- x3 * arg1[4] (_0*_0)
adox rbx, rbp
adox r14, r10
adcx r8, rbx
adc r14, 0x0; add CF to r0's alloc
mov rdx, r8;
shrd rdx, r14, 52; x17 <- x16_1||x16_0 >> 52
and r8, r11; x18 <- x16_0&0xfffffffffffff
shl r8, 4; x10015 <- x18<< 4
mov r10, rax;
shr r10, 48; x14 <- x13>> 48
mov rbp, rdx; preserving value of x17 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx r14, rbx, rdx; x10019_1, x10019_0<- arg1[3]^2
lea r8, [ r8 + r10 ]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp - 0x58 ], r15; spilling calSv-r15 to mem
mulx r15, r10, rdx; x10014_1, x10014_0<- arg1[0]^2
add rbx, rcx; could be done better, if r0 has been u8 as well
adcx r13, r14
mov rdx, 0x1000003d1 ; moving imm to reg
mulx r14, rcx, r8; x10017_1, x10017_0<- x10016 * 0x1000003d1 (_0*_0)
xor r8, r8
adox rcx, r10
adox r15, r14
mov r10, rcx;
shrd r10, r15, 52; x20 <- x19_1||x19_0 >> 52
and rcx, r11; x21 <- x19_0&0xfffffffffffff
adox rbp, rbx
adox r13, r8
mov [ rdi + 0x0 ], rcx; out1[0] = x21
mov rbx, rbp;
and rbx, r11; x24 <- x22_0&0xfffffffffffff
mov r14, 0x1000003d10 ; moving imm to reg
mov rdx, rbx; x24 to rdx
mulx r15, rbx, r14; x10023_1, x10023_0<- x24 * 0x1000003d10 (_0*_0)
mov rdx, r9; x4 to rdx
mulx rcx, r9, [ rsi + 0x8 ]; x10021_1, x10021_0<- x4 * arg1[1] (_0*_0)
adox r10, r9
adox rcx, r8
adcx rbx, r10
adcx rcx, r15
mov r15, rbx;
shrd r15, rcx, 52; x26 <- x25_1||x25_0 >> 52
mulx r10, r9, [ rsi + 0x10 ]; x10025_1, x10025_0<- x4 * arg1[2] (_0*_0)
and rbx, r11; x27 <- x25_0&0xfffffffffffff
shrd rbp, r13, 52; x23 <- x22_1||x22_0 >> 52
mov [ rdi + 0x8 ], rbx; out1[1] = x27
imul rdx, [ rsi + 0x18 ], 0x2; x1 <- arg1[3] * 0x2
mov r13, rdx; preserving value of x1 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx rbx, rcx, rdx; x10026_1, x10026_0<- arg1[1]^2
xor rdx, rdx
adox rcx, r9
adox r10, rbx
mov rdx, r13; x1 to rdx
mulx r13, r8, [ rsi + 0x20 ]; x10024_1, x10024_0<- x1 * arg1[4] (_0*_0)
adcx rbp, r8
adc r13, 0x0; add CF to r0's alloc
xor r9, r9
adox r15, rcx
adox r10, r9
mov rdx, r14; 0x1000003d10 to rdx
mulx rbx, r14, rbp; x10029_1, x10029_0<- x30 * 0x1000003d10 (_0*_0)
mov rcx, 0xffffffffffff ; moving imm to reg
and rax, rcx; x15 <- x13&0xffffffffffff
adox r14, r15
adox r10, rbx
mov r8, r14;
shrd r8, r10, 52; x32 <- x31_1||x31_0 >> 52
and r12, r11; x10 <- x8_0&0xfffffffffffff
lea r12, [ r12 + r8 ]
mov rbp, 0x1000003d10000 ; moving imm to reg
mov rdx, rbp; 0x1000003d10000 to rdx
mulx r15, rbp, r13; x10031_1, x10031_0<- x29 * 0x1000003d10000 (_0*_0)
adox rbp, r12
adox r15, r9
mov r13, rbp;
shrd r13, r15, 52; x35 <- x34_1||x34_0 >> 52
lea rax, [ rax + r13 ]
and rbp, r11; x36 <- x34_0&0xfffffffffffff
and r14, r11; x33 <- x31_0&0xfffffffffffff
mov [ rdi + 0x10 ], r14; out1[2] = x33
mov [ rdi + 0x18 ], rbp; out1[3] = x36
mov [ rdi + 0x20 ], rax; out1[4] = x37
mov rbx, [ rsp - 0x80 ]; pop
mov rbp, [ rsp - 0x78 ]; pop
mov r12, [ rsp - 0x70 ]; pop
mov r13, [ rsp - 0x68 ]; pop
mov r14, [ rsp - 0x60 ]; pop
mov r15, [ rsp - 0x58 ]; pop
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.2004
; seed 0570095454324679 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 949699 ms on 270000 evaluations.
; Time spent for assembling and measuring (initial batch_size=479, initial num_batches=31): 117428 ms
; number of used evaluations: 270000
; Ratio (time for assembling + measure)/(total runtime for 270000 evals): 0.12364759781783491
; number reverted permutation / tried permutation: 105572 / 134882 =78.270%
; number reverted decision / tried decision: 98845 / 135117 =73.155%
; validated in 0.159s
