SECTION .text
	GLOBAL square_curve25519
square_curve25519:
sub rsp, 0x30 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x0 ], rbx; saving to stack
mov [ rsp + 0x8 ], rbp; saving to stack
mov [ rsp + 0x10 ], r12; saving to stack
mov [ rsp + 0x18 ], r13; saving to stack
mov [ rsp + 0x20 ], r14; saving to stack
mov [ rsp + 0x28 ], r15; saving to stack
imul rax, [ rsi + 0x20 ], 0x13; x1 <- arg1[4] * 0x13
imul r10, [ rsi + 0x18 ], 0x13; x4 <- arg1[3] * 0x13
imul r11, r10, 0x2; x5 <- x4 * 0x2
imul rbx, rax, 0x2; x2 <- x1 * 0x2
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbp, r12, rbx; x22, x21<- arg1[1] * x2
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r13, r14, [ rsi + 0x0 ]; x38, x37<- arg1[0] * arg1[0]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r11, r15, r11; x18, x17<- arg1[2] * x5
add r15, r12; could be done better, if r0 has been u8 as well
adcx rbp, r11
add r15, r14; could be done better, if r0 has been u8 as well
adcx r13, rbp
imul rdx, [ rsi + 0x8 ], 0x2; x8 <- arg1[1] * 0x2
mov rcx, r15; x47, copying x43 here, cause x43 is needed in a reg for other than x47, namely all: , x47, x48, size: 2
shrd rcx, r13, 51; x47 <- x45||x43 >> 51
mulx rdx, r8, [ rsi + 0x0 ]; x36, x35<- arg1[0] * x8
mov r9, rdx; preserving value of x36 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r12, r14, rbx; x16, x15<- arg1[2] * x2
mov rdx, r10; x4 to rdx
mulx rdx, r10, [ rsi + 0x18 ]; x14, x13<- arg1[3] * x4
xor r11, r11
adox r10, r14
adox r12, rdx
adcx r10, r8
adcx r9, r12
xor rbp, rbp
adox r10, rcx
adox r9, rbp
imul r11, [ rsi + 0x10 ], 0x2; x7 <- arg1[2] * 0x2
mov r13, r10; x84, copying x81 here, cause x81 is needed in a reg for other than x84, namely all: , x84, x85, size: 2
shrd r13, r9, 51; x84 <- x83||x81 >> 51
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rbx, rcx, rbx; x12, x11<- arg1[3] * x2
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r8, r14, [ rsi + 0x8 ]; x28, x27<- arg1[1] * arg1[1]
mov rdx, r11; x7 to rdx
mulx r11, r12, [ rsi + 0x0 ]; x34, x33<- arg1[0] * x7
add rcx, r14; could be done better, if r0 has been u8 as well
adcx r8, rbx
xor r9, r9
adox rcx, r12
adcx rcx, r13
adox r11, r8
adc r11, 0x0
imul rbp, [ rsi + 0x18 ], 0x2; x6 <- arg1[3] * 0x2
mov r13, 0x7ffffffffffff ; moving imm to reg
mov rbx, rcx; x90, copying x86 here, cause x86 is needed in a reg for other than x90, namely all: , x90, x89, size: 2
and rbx, r13; x90 <- x86&0x7ffffffffffff
mulx rdx, r14, [ rsi + 0x8 ]; x26, x25<- arg1[1] * x7
shrd rcx, r11, 51; x89 <- x88||x86 >> 51
mov r12, rdx; preserving value of x26 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r8, r11, rbp; x32, x31<- arg1[0] * x6
and r15, r13; x48 <- x43&0x7ffffffffffff
mov rdx, rax; x1 to rdx
mulx rdx, rax, [ rsi + 0x20 ]; x10, x9<- arg1[4] * x1
adox rax, r14
adcx rax, r11
adox r12, rdx
adcx r8, r12
add rax, rcx; could be done better, if r0 has been u8 as well
adc r8, 0x0
imul r14, [ rsi + 0x20 ], 0x2; x3 <- arg1[4] * 0x2
mov rcx, rax; x94, copying x91 here, cause x91 is needed in a reg for other than x94, namely all: , x94, x95, size: 2
shrd rcx, r8, 51; x94 <- x93||x91 >> 51
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r11, r12, [ rsi + 0x10 ]; x20, x19<- arg1[2] * arg1[2]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbp, r8, rbp; x24, x23<- arg1[1] * x6
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r14, r9, r14; x30, x29<- arg1[0] * x3
add r12, r8; could be done better, if r0 has been u8 as well
adcx rbp, r11
test al, al
adox r12, r9
adcx r12, rcx
adox r14, rbp
adc r14, 0x0
mov rdx, 0x33 ; moving imm to reg
bzhi r10, r10, rdx; x85 <- x81 (only least 0x33 bits)
bzhi rax, rax, rdx; x95 <- x91 (only least 0x33 bits)
mov rcx, r12; x99, copying x96 here, cause x96 is needed in a reg for other than x99, namely all: , x100, x99, size: 2
shrd rcx, r14, 51; x99 <- x98||x96 >> 51
imul rcx, rcx, 0x13; x101 <- x99 * 0x13
bzhi r12, r12, rdx; x100 <- x96 (only least 0x33 bits)
mov [ rdi + 0x20 ], r12; out1[4] = x100
lea r15, [ r15 + rcx ]
bzhi rdx, r15, rdx; x104 <- x102 (only least 0x33 bits)
shr r15, 51; x103 <- x102>> 51
lea r15, [ r15 + r10 ]
mov r11, r15; x106, copying x105 here, cause x105 is needed in a reg for other than x106, namely all: , x106, x107, size: 2
shr r11, 51; x106 <- x105>> 51
mov [ rdi + 0x0 ], rdx; out1[0] = x104
and r15, r13; x107 <- x105&0x7ffffffffffff
mov [ rdi + 0x18 ], rax; out1[3] = x95
lea r11, [ r11 + rbx ]
mov [ rdi + 0x10 ], r11; out1[2] = x108
mov [ rdi + 0x8 ], r15; out1[1] = x107
mov rbx, [ rsp + 0x0 ]; restoring from stack
mov rbp, [ rsp + 0x8 ]; restoring from stack
mov r12, [ rsp + 0x10 ]; restoring from stack
mov r13, [ rsp + 0x18 ]; restoring from stack
mov r14, [ rsp + 0x20 ]; restoring from stack
mov r15, [ rsp + 0x28 ]; restoring from stack
add rsp, 0x30 
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; clocked at 1600 MHz
; first cyclecount 23.615, best 15.624750499001996, lastGood 16.01996007984032
; seed 4460917673401922 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1176112 ms / 60000 runs=> 19.601866666666666ms/run
; Time spent for assembling and measureing (initial batch_size=501, initial num_batches=101): 898507 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.7639638061681201
; number reverted permutation/ tried permutation: 25557 / 30044 =85.065%
; number reverted decision/ tried decision: 22541 / 29957 =75.245%