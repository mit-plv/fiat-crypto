SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rax, [ rsi + 0x0 ]; load m64 arg1[0] to register64
lea r10, [rax + rax]; x4 <- arg1[0] * 2 
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r11, rax, rdx; x10026_1, x10026_0<- arg1[1]^2
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r8, rcx, rdx; x10019_1, x10019_0<- arg1[3]^2
mov rdx, 0x1 ; moving imm to reg
shlx r9, [ rsi + 0x8 ], rdx; x3 <- arg1[1] * 0x2 (shlx does not change the flags)
imul rdx, [ rsi + 0x18 ], 0x2; x1 <- arg1[3] * 0x2
mov [ rsp - 0x80 ], rbx; spilling calSv-rbx to mem
mov rbx, rdx; preserving value of x1 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp - 0x78 ], rbp; spilling calSv-rbp to mem
mov [ rsp - 0x70 ], r12; spilling calSv-r12 to mem
mulx r12, rbp, rdx; x5_1, x5_0<- arg1[4]^2
mov rdx, r9; x3 to rdx
mov [ rsp - 0x68 ], r13; spilling calSv-r13 to mem
mulx r13, r9, [ rsi + 0x20 ]; x10011_1, x10011_0<- x3 * arg1[4] (_0*_0)
mov [ rsp - 0x60 ], r14; spilling calSv-r14 to mem
mov [ rsp - 0x58 ], r15; spilling calSv-r15 to mem
mulx r15, r14, [ rsi + 0x18 ]; x10005_1, x10005_0<- x3 * arg1[3] (_0*_0)
mov [ rsp - 0x50 ], rdi; spilling out1 to mem
mov [ rsp - 0x48 ], r11; spilling x10026_1 to mem
mulx r11, rdi, [ rsi + 0x10 ]; x10001_1, x10001_0<- x3 * arg1[2] (_0*_0)
mov rdx, 0x1000003d10000 ; moving imm to reg
mov [ rsp - 0x40 ], rax; spilling x10026_0 to mem
mov [ rsp - 0x38 ], rbx; spilling x1 to mem
mulx rbx, rax, r12; x10010_1, x10010_0<- x6 * 0x1000003d10000 (_0*_0)
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp - 0x30 ], r13; spilling x10011_1 to mem
mulx r13, r12, r10; x10000_1, x10000_0<- x4 * arg1[3] (_0*_0)
add rdi, r12; could be done better, if r0 has been u8 as well
adcx r13, r11
mov rdx, 0x1000003d10 ; moving imm to reg
mulx r12, r11, rbp; x10003_1, x10003_0<- x7 * 0x1000003d10 (_0*_0)
xor rbp, rbp
adox r11, rdi
adox r13, r12
mov rdi, 0x34 ; moving imm to reg
bzhi r12, r11, rdi; x10 <- x8_0 (only least 0x34 bits)
shrd r11, r13, 52; x9 <- x8_1||x8_0 >> 52
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx rbp, r13, r10; x10004_1, x10004_0<- x4 * arg1[4] (_0*_0)
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp - 0x28 ], r12; spilling x10 to mem
mulx r12, rdi, rdx; x10006_1, x10006_0<- arg1[2]^2
test al, al
adox rdi, r14
adox r15, r12
adcx rdi, r13
adcx rbp, r15
imul rdx, [ rsi + 0x10 ], 0x2; x2 <- arg1[2] * 0x2
mulx r13, r14, [ rsi + 0x20 ]; x10018_1, x10018_0<- x2 * arg1[4] (_0*_0)
xor r12, r12
adox r11, rdi
adox rbp, r12
adcx rcx, r14
adcx r13, r8
mulx r15, r8, [ rsi + 0x18 ]; x10012_1, x10012_0<- x2 * arg1[3] (_0*_0)
xor rdi, rdi
adox rax, r11
adox rbp, rbx
mov r12, rax;
shrd r12, rbp, 52; x12 <- x11_1||x11_0 >> 52
xor rbx, rbx
adox r8, r9
adox r15, [ rsp - 0x30 ]
mov rdi, 0xfffffffffffff ; moving imm to reg
and rax, rdi; x13 <- x11_0&0xfffffffffffff
adox r12, r8
adox r15, rbx
mov r9, r12;
shrd r9, r15, 52; x17 <- x16_1||x16_0 >> 52
and r12, rdi; x18 <- x16_0&0xfffffffffffff
mov rdx, 0x30 ; moving imm to reg
bzhi r14, rax, rdx; x15 <- x13 (only least 0x30 bits)
adox r9, rcx
adox r13, rbx
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rcx, r11, r10; x10025_1, x10025_0<- x4 * arg1[2] (_0*_0)
mov rdx, r9;
shrd rdx, r13, 52; x23 <- x22_1||x22_0 >> 52
and r9, rdi; x24 <- x22_0&0xfffffffffffff
shl r12, 4; x10015 <- x18<< 4
shr rax, 48; x14 <- x13>> 48
lea r12, [ r12 + rax ]
mov rbp, rdx; preserving value of x23 into a new reg
mov rdx, [ rsp - 0x38 ]; saving x1 in rdx.
mulx r15, r8, [ rsi + 0x20 ]; x10024_1, x10024_0<- x1 * arg1[4] (_0*_0)
xor rdx, rdx
adox rbp, r8
adox r15, rdx
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r13, rbx, rdx; x10014_1, x10014_0<- arg1[0]^2
mov rdx, 0x1000003d1 ; moving imm to reg
mulx r8, rax, r12; x10017_1, x10017_0<- x10016 * 0x1000003d1 (_0*_0)
adcx rax, rbx
adcx r13, r8
mov r12, rax;
shrd r12, r13, 52; x20 <- x19_1||x19_0 >> 52
mov rbx, r11;
xor r8, r8
adox rbx, [ rsp - 0x40 ]
adox rcx, [ rsp - 0x48 ]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r13, r11, r10; x10021_1, x10021_0<- x4 * arg1[1] (_0*_0)
and rax, rdi; x21 <- x19_0&0xfffffffffffff
adox r12, r11
adox r13, r8
mov rdx, 0x1000003d10 ; moving imm to reg
mulx r11, r10, r9; x10023_1, x10023_0<- x24 * 0x1000003d10 (_0*_0)
adcx r10, r12
adcx r13, r11
mov r9, r10;
shrd r9, r13, 52; x26 <- x25_1||x25_0 >> 52
and r10, rdi; x27 <- x25_0&0xfffffffffffff
mulx r11, r12, rbp; x10029_1, x10029_0<- x30 * 0x1000003d10 (_0*_0)
adox r9, rbx
adox rcx, r8
mov rbx, 0x1000003d10000 ; moving imm to reg
mov rdx, r15; x29 to rdx
mulx r13, r15, rbx; x10031_1, x10031_0<- x29 * 0x1000003d10000 (_0*_0)
mov rbp, [ rsp - 0x50 ]; load m64 out1 to register64
mov [ rbp + 0x8 ], r10; out1[1] = x27
adcx r12, r9
adcx rcx, r11
mov r10, r12;
shrd r10, rcx, 52; x32 <- x31_1||x31_0 >> 52
add r10, [ rsp - 0x28 ]
xor r11, r11
adox r15, r10
adox r13, r11
mov r8, r15;
and r8, rdi; x36 <- x34_0&0xfffffffffffff
shrd r15, r13, 52; x35 <- x34_1||x34_0 >> 52
mov [ rbp + 0x0 ], rax; out1[0] = x21
lea r14, [ r14 + r15 ]
and r12, rdi; x33 <- x31_0&0xfffffffffffff
mov [ rbp + 0x20 ], r14; out1[4] = x37
mov [ rbp + 0x10 ], r12; out1[2] = x33
mov [ rbp + 0x18 ], r8; out1[3] = x36
mov rbx, [ rsp - 0x80 ]; pop
mov rbp, [ rsp - 0x78 ]; pop
mov r12, [ rsp - 0x70 ]; pop
mov r13, [ rsp - 0x68 ]; pop
mov r14, [ rsp - 0x60 ]; pop
mov r15, [ rsp - 0x58 ]; pop
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.0503
; seed 3853660286578150 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1722035 ms on 270000 evaluations.
; Time spent for assembling and measuring (initial batch_size=235, initial num_batches=31): 134165 ms
; number of used evaluations: 270000
; Ratio (time for assembling + measure)/(total runtime for 270000 evals): 0.0779107277145935
; number reverted permutation / tried permutation: 110084 / 134906 =81.601%
; number reverted decision / tried decision: 97612 / 135093 =72.255%
; validated in 0.357s
