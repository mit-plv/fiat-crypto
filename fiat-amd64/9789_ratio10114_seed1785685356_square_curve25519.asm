SECTION .text
	GLOBAL square_curve25519
square_curve25519:
sub rsp, 0x98
mov rax, [ rsi + 0x8 ]; load m64 arg1[1] to register64
mov r10, rax; load m64 x8 to register64
shl r10, 0x1; x8 <- arg1[1] * 0x2
imul rax, [ rsi + 0x18 ], 0x26; x5 <- arg1[3] * 0x26
mov r11, [ rsi + 0x10 ]; load m64 arg1[2] to register64
lea rdx, [r11 + r11]; x7 <- arg1[2] * 2 
mov r11, rdx; preserving value of x7 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r8, rcx, rdx; x23_1, x23_0<- arg1[0]^2
mov rdx, [ rsi + 0x20 ]; load m64 arg1[4] to register64
mov [ rsp + 0x0 ], rbx; spilling calSv-rbx to mem

; imul rbx, rdx, 0x13

lea r9, [rdx + 8 * rdx]; TMP <- arg1[4] * 9
lea rbx, [rdx + 2 * r9]; x1 <- arg1[4]*19: arg1[4] + 2 * TMP = arg1[4] + 2 * 9 * arg1[4]

mov rdx, rbx; x1 to rdx
mulx rbx, r9, [ rsi + 0x20 ]; x9_1, x9_0<- arg1[4] * x1 (_0*_0)
imul rdx, [ rsi + 0x18 ], 0x13; x4 <- arg1[3] * 0x13
mov [ rsp + 0x8 ], rbp; spilling calSv-rbp to mem
mov rbp, rdx; preserving value of x4 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x10 ], r12; spilling calSv-r12 to mem
mov [ rsp + 0x18 ], r13; spilling calSv-r13 to mem
mulx r13, r12, r11; x21_1, x21_0<- arg1[0] * x7 (_0*_0)
mov rdx, rbp; x4 to rdx
mov [ rsp + 0x20 ], r14; spilling calSv-r14 to mem
mulx r14, rbp, [ rsi + 0x18 ]; x11_1, x11_0<- arg1[3] * x4 (_0*_0)
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x28 ], r15; spilling calSv-r15 to mem
mov [ rsp + 0x30 ], rdi; spilling out1 to mem
mulx rdi, r15, rdx; x18_1, x18_0<- arg1[1]^2
mov rdx, [ rsi + 0x20 ]; load m64 arg1[4] to register64
mov [ rsp + 0x38 ], r14; spilling x11_1 to mem
lea r14, [rdx + rdx]; x3 <- arg1[4] * 2 
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x40 ], rbp; spilling x11_0 to mem
mov [ rsp + 0x48 ], r8; spilling x23_1 to mem
mulx r8, rbp, r11; x17_1, x17_0<- arg1[1] * x7 (_0*_0)
mov rdx, r10; x8 to rdx
mulx r11, r10, [ rsi + 0x0 ]; x22_1, x22_0<- arg1[0] * x8 (_0*_0)
xor rdx, rdx
adox r9, rbp
adox r8, rbx
mov rbx, [ rsi + 0x18 ]; load m64 arg1[3] to register64
mov rbp, rbx; load m64 x6 to register64
shl rbp, 0x1; x6 <- arg1[3] * 0x2
mov rdx, rbp; x6 to rdx
mulx rbp, rbx, [ rsi + 0x0 ]; x20_1, x20_0<- arg1[0] * x6 (_0*_0)
mov [ rsp + 0x50 ], r8; spilling x10002_1 to mem
mov r8, rdx; preserving value of x6 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x58 ], r9; spilling x10002_0 to mem
mov [ rsp + 0x60 ], rbp; spilling x20_1 to mem
mulx rbp, r9, r14; x19_1, x19_0<- arg1[0] * x3 (_0*_0)
imul rdx, [ rsi + 0x20 ], 0x26; x2 <- arg1[4] * 0x26
mov [ rsp + 0x68 ], rbx; spilling x20_0 to mem
mulx rbx, r14, [ rsi + 0x18 ]; x10_1, x10_0<- arg1[3] * x2 (_0*_0)
mov [ rsp + 0x70 ], r11; spilling x22_1 to mem
mov [ rsp + 0x78 ], r10; spilling x22_0 to mem
mulx r10, r11, [ rsi + 0x8 ]; x15_1, x15_0<- arg1[1] * x2 (_0*_0)
mov [ rsp + 0x80 ], rcx; spilling x23_0 to mem
mov [ rsp + 0x88 ], r10; spilling x15_1 to mem
mulx r10, rcx, [ rsi + 0x10 ]; x12_1, x12_0<- arg1[2] * x2 (_0*_0)
test al, al
adox r14, r15
adox rdi, rbx
mov rdx, rax; x5 to rdx
mulx r15, rax, [ rsi + 0x10 ]; x13_1, x13_0<- arg1[2] * x5 (_0*_0)
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x90 ], r10; spilling x12_1 to mem
mulx r10, rbx, rdx; x14_1, x14_0<- arg1[2]^2
adcx r14, r12
adcx r13, rdi
mov rdx, r8; x6 to rdx
mulx r12, r8, [ rsi + 0x8 ]; x16_1, x16_0<- arg1[1] * x6 (_0*_0)
test al, al
adox rbx, r8
adox r12, r10
adcx rbx, r9
adcx rbp, r12
xor rdx, rdx
adox rax, r11
adox r15, [ rsp + 0x88 ]
adcx rax, [ rsp + 0x80 ]
adcx r15, [ rsp + 0x48 ]
mov r9, rax;x25, copying x24_0 here, cause x24_0 is needed in a reg. It has those deps: "x25, x26, size: 2", current hard deps: ""
shrd r9, r15, 51; x25 <- x24_1||x24_0 >> 51
mov r11, rcx;x10004_0, copying x12_0 here, cause x12_0 is needed in a reg. It has those deps: "", current hard deps: "x12_0"
add r11, [ rsp + 0x40 ]; could be done better, if r0 has been u8 as well
mov rdi, [ rsp + 0x38 ]; load m64 x11_1 to register64
adcx rdi, [ rsp + 0x90 ]
xor rcx, rcx
adox r11, [ rsp + 0x78 ]
adox rdi, [ rsp + 0x70 ]
adcx r11, r9
adc rdi, 0x0; add CF to r0's alloc
mov rdx, r11;x32, copying x31_0 here, cause x31_0 is needed in a reg. It has those deps: "x32, x33, size: 2", current hard deps: ""
shrd rdx, rdi, 51; x32 <- x31_1||x31_0 >> 51
test al, al
adox r14, rdx
adox r13, rcx
mov r10, [ rsp + 0x58 ]; load m64 x10002_0 to register64
adcx r10, [ rsp + 0x68 ]
mov r8, [ rsp + 0x50 ]; load m64 x10002_1 to register64
adcx r8, [ rsp + 0x60 ]
mov r12, r14;x35, copying x34_0 here, cause x34_0 is needed in a reg. It has those deps: "x35, x36, size: 2", current hard deps: ""
shrd r12, r13, 51; x35 <- x34_1||x34_0 >> 51
xor r15, r15
adox r10, r12
adox r8, r15
mov rcx, r10;x38, copying x37_0 here, cause x37_0 is needed in a reg. It has those deps: "x38, x39, size: 2", current hard deps: ""
shrd rcx, r8, 51; x38 <- x37_1||x37_0 >> 51
xor r9, r9
adox rbx, rcx
adox rbp, r9
mov r15, 0x33 ; moving imm to reg
bzhi rdi, r10, r15; x39 <- x37_0 (only least 0x33 bits)
mov rdx, rbx;x41, copying x40_0 here, cause x40_0 is needed in a reg. It has those deps: "x41, x42, size: 2", current hard deps: ""
shrd rdx, rbp, 51; x41 <- x40_1||x40_0 >> 51
bzhi r13, rbx, r15; x42 <- x40_0 (only least 0x33 bits)
bzhi r12, rax, r15; x26 <- x24_0 (only least 0x33 bits)
mov rax, [ rsp + 0x30 ]; load m64 out1 to register64
mov [ rax + 0x20 ], r13; out1[4] = x42

; using imul works
; imul r8, rdx, 0x13

; this does not.
lea r10, [rdx + 8 * rdx]; TMP <- x41 * 9
lea r8, [rdx + 2 * r10]; x43 <- x41*19: x41 + 2 * TMP = x41 + 2 * 9 * x41


lea r12, [ r12 + r8 ]
bzhi r10, r11, r15; x33 <- x31_0 (only least 0x33 bits)
bzhi r11, r12, r15; x46 <- x44 (only least 0x33 bits)
shr r12, 51; x45 <- x44>> 51
lea r12, [ r12 + r10 ]
mov rcx, r12;x48, copying x47 here, cause x47 is needed in a reg. It has those deps: "x48, x49, size: 2", current hard deps: ""
shr rcx, 51; x48 <- x47>> 51
bzhi rbx, r14, r15; x36 <- x34_0 (only least 0x33 bits)
mov [ rax + 0x0 ], r11; out1[0] = x46
lea rcx, [ rcx + rbx ]
mov [ rax + 0x10 ], rcx; out1[2] = x50
bzhi r14, r12, r15; x49 <- x47 (only least 0x33 bits)
mov [ rax + 0x18 ], rdi; out1[3] = x39
mov [ rax + 0x8 ], r14; out1[1] = x49
mov rbx, [ rsp + 0x0 ] ; pop
mov rbp, [ rsp + 0x8 ] ; pop
mov r12, [ rsp + 0x10 ] ; pop
mov r13, [ rsp + 0x18 ] ; pop
mov r14, [ rsp + 0x20 ] ; pop
mov r15, [ rsp + 0x28 ] ; pop
add rsp, 0x98 
ret
; cpu Intel(R) Core(TM) i5-8265U CPU @ 1.60GHz
; ratio 1.0114
; seed 1785685356 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1758 ms / 100 evals=> 17.58ms/eval
; Time spent for assembling and measureing (initial batch_size=161, initial num_batches=31): 101 ms
; number of used evaluations: 100
; Ratio (time for assembling + measure)/(total runtime for 100 evals): 0.05745164960182025
; number reverted permutation/ tried permutation: 15 / 51 =29.412%
; number reverted decision/ tried decision: 15 / 48 =31.250%
