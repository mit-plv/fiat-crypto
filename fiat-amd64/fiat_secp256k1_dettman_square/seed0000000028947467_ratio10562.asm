SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rax, [ rsi + 0x0 ]; load m64 arg1[0] to register64
mov r10, rax; load m64 x4 to register64
shl r10, 0x1; x4 <- arg1[0] * 0x2
mov rax, [ rsi + 0x8 ]; load m64 arg1[1] to register64
lea r11, [rax + rax]; x3 <- arg1[1] * 2 
mov rax, 0x1 ; moving imm to reg
shlx rdx, [ rsi + 0x10 ], rax; x2 <- arg1[2] * 0x2 (shlx does not change the flags)
mov rcx, rdx; preserving value of x2 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r9, r8, rdx; x5_1, x5_0<- arg1[4]^2
mov rdx, r10; x4 to rdx
mulx rax, r10, [ rsi + 0x18 ]; x10000_1, x10000_0<- x4 * arg1[3] (_0*_0)
mov [ rsp - 0x80 ], rbx; spilling calSv-rbx to mem
mov rbx, rdx; preserving value of x4 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp - 0x78 ], rbp; spilling calSv-rbp to mem
mov [ rsp - 0x70 ], r12; spilling calSv-r12 to mem
mulx r12, rbp, rdx; x10006_1, x10006_0<- arg1[2]^2
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp - 0x68 ], r13; spilling calSv-r13 to mem
mov [ rsp - 0x60 ], r14; spilling calSv-r14 to mem
mulx r14, r13, rbx; x10025_1, x10025_0<- x4 * arg1[2] (_0*_0)
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp - 0x58 ], r15; spilling calSv-r15 to mem
mov [ rsp - 0x50 ], rdi; spilling out1 to mem
mulx rdi, r15, rcx; x10012_1, x10012_0<- x2 * arg1[3] (_0*_0)
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp - 0x48 ], rdi; spilling x10012_1 to mem
mov [ rsp - 0x40 ], r15; spilling x10012_0 to mem
mulx r15, rdi, rdx; x10026_1, x10026_0<- arg1[1]^2
xor rdx, rdx
adox rdi, r13
adox r14, r15
mov rdx, r11; x3 to rdx
mulx r13, r11, [ rsi + 0x18 ]; x10005_1, x10005_0<- x3 * arg1[3] (_0*_0)
adcx rbp, r11
adcx r13, r12
mulx r15, r12, [ rsi + 0x10 ]; x10001_1, x10001_0<- x3 * arg1[2] (_0*_0)
mov r11, 0x1000003d10 ; moving imm to reg
xchg rdx, r8; x7, swapping with x3, which is currently in rdx
mov [ rsp - 0x38 ], r14; spilling x10027_1 to mem
mov [ rsp - 0x30 ], rdi; spilling x10027_0 to mem
mulx rdi, r14, r11; x10003_1, x10003_0<- x7 * 0x1000003d10 (_0*_0)
xor rdx, rdx
adox r12, r10
adox rax, r15
adcx r14, r12
adcx rax, rdi
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r15, r10, rbx; x10004_1, x10004_0<- x4 * arg1[4] (_0*_0)
xor rdx, rdx
adox rbp, r10
adox r15, r13
mov r13, r14;
shrd r13, rax, 52; x9 <- x8_1||x8_0 >> 52
mov rdx, rcx; x2 to rdx
mulx rdi, rcx, [ rsi + 0x20 ]; x10018_1, x10018_0<- x2 * arg1[4] (_0*_0)
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rax, r12, rdx; x10019_1, x10019_0<- arg1[3]^2
xor rdx, rdx
adox r12, rcx
adox rdi, rax
adcx r13, rbp
adc r15, 0x0; add CF to r0's alloc
mov r10, 0x1000003d10000 ; moving imm to reg
mov rdx, r9; x6 to rdx
mulx rbp, r9, r10; x10010_1, x10010_0<- x6 * 0x1000003d10000 (_0*_0)
test al, al
adox r9, r13
adox r15, rbp
mov rdx, r9;
shrd rdx, r15, 52; x12 <- x11_1||x11_0 >> 52
mov rcx, rdx; preserving value of x12 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r13, rax, r8; x10011_1, x10011_0<- x3 * arg1[4] (_0*_0)
mov rdx, rax;
test al, al
adox rdx, [ rsp - 0x40 ]
adox r13, [ rsp - 0x48 ]
adcx rcx, rdx
adc r13, 0x0; add CF to r0's alloc
mov r8, [ rsi + 0x18 ]; load m64 arg1[3] to register64
lea rbp, [r8 + r8]; x1 <- arg1[3] * 2 
mov r8, rcx;
shrd r8, r13, 52; x17 <- x16_1||x16_0 >> 52
mov r15, 0xfffffffffffff ; moving imm to reg
and rcx, r15; x18 <- x16_0&0xfffffffffffff
shl rcx, 4; x10015 <- x18<< 4
and r9, r15; x13 <- x11_0&0xfffffffffffff
mov rax, r9;
shr rax, 48; x14 <- x13>> 48
xor rdx, rdx
adox r8, r12
adox rdi, rdx
mov r12, r8;
shrd r12, rdi, 52; x23 <- x22_1||x22_0 >> 52
mov rdx, rbp; x1 to rdx
mulx r13, rbp, [ rsi + 0x20 ]; x10024_1, x10024_0<- x1 * arg1[4] (_0*_0)
lea rcx, [ rcx + rax ]
and r8, r15; x24 <- x22_0&0xfffffffffffff
adox r12, rbp
mov rdx, 0x0 ; moving imm to reg
adox r13, rdx
mov rax, 0x1000003d1 ; moving imm to reg
mov rdx, rax; 0x1000003d1 to rdx
mulx rdi, rax, rcx; x10017_1, x10017_0<- x10016 * 0x1000003d1 (_0*_0)
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rcx, rbp, rdx; x10014_1, x10014_0<- arg1[0]^2
adcx rax, rbp
adcx rcx, rdi
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbp, rdi, rbx; x10021_1, x10021_0<- x4 * arg1[1] (_0*_0)
mov rdx, rax;
and rdx, r15; x21 <- x19_0&0xfffffffffffff
shrd rax, rcx, 52; x20 <- x19_1||x19_0 >> 52
xor rbx, rbx
adox rax, rdi
adox rbp, rbx
mov rcx, [ rsp - 0x50 ]; load m64 out1 to register64
mov [ rcx + 0x0 ], rdx; out1[0] = x21
mov rdx, r11; 0x1000003d10 to rdx
mulx rdi, r11, r8; x10023_1, x10023_0<- x24 * 0x1000003d10 (_0*_0)
adcx r11, rax
adcx rbp, rdi
mov r8, r11;
shrd r8, rbp, 52; x26 <- x25_1||x25_0 >> 52
test al, al
adox r8, [ rsp - 0x30 ]
mov rax, [ rsp - 0x38 ];
adox rax, rbx
and r14, r15; x10 <- x8_0&0xfffffffffffff
and r11, r15; x27 <- x25_0&0xfffffffffffff
mulx rbp, rdi, r12; x10029_1, x10029_0<- x30 * 0x1000003d10 (_0*_0)
adox rdi, r8
adox rax, rbp
mov r12, rdi;
and r12, r15; x33 <- x31_0&0xfffffffffffff
shrd rdi, rax, 52; x32 <- x31_1||x31_0 >> 52
mov rdx, r13; x29 to rdx
mulx r8, r13, r10; x10031_1, x10031_0<- x29 * 0x1000003d10000 (_0*_0)
lea r14, [ r14 + rdi ]
test al, al
adox r13, r14
adox r8, rbx
mov rdx, r13;
shrd rdx, r8, 52; x35 <- x34_1||x34_0 >> 52
mov [ rcx + 0x10 ], r12; out1[2] = x33
and r13, r15; x36 <- x34_0&0xfffffffffffff
mov rbp, 0x30 ; moving imm to reg
bzhi rax, r9, rbp; x15 <- x13 (only least 0x30 bits)
mov [ rcx + 0x18 ], r13; out1[3] = x36
lea rax, [ rax + rdx ]
mov [ rcx + 0x8 ], r11; out1[1] = x27
mov [ rcx + 0x20 ], rax; out1[4] = x37
mov rbx, [ rsp - 0x80 ]; pop
mov rbp, [ rsp - 0x78 ]; pop
mov r12, [ rsp - 0x70 ]; pop
mov r13, [ rsp - 0x68 ]; pop
mov r14, [ rsp - 0x60 ]; pop
mov r15, [ rsp - 0x58 ]; pop
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.0562
; seed 2448470037697871 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1467878 ms on 270000 evaluations.
; Time spent for assembling and measuring (initial batch_size=239, initial num_batches=31): 125840 ms
; number of used evaluations: 270000
; Ratio (time for assembling + measure)/(total runtime for 270000 evals): 0.08572919547809832
; number reverted permutation / tried permutation: 104159 / 134946 =77.186%
; number reverted decision / tried decision: 77313 / 135053 =57.246%
; validated in 0.269s
