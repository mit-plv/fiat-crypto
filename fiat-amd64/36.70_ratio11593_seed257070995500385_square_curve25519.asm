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
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rax, r10, [ rsi + 0x0 ]; x38, x37<- arg1[0] * arg1[0]
imul r11, [ rsi + 0x20 ], 0x13; x1 <- arg1[4] * 0x13
imul rbx, [ rsi + 0x18 ], 0x13; x4 <- arg1[3] * 0x13
imul rbp, rbx, 0x2; x5 <- x4 * 0x2
imul r12, r11, 0x2; x2 <- x1 * 0x2
mov rdx, rbp; x5 to rdx
mulx rdx, rbp, [ rsi + 0x10 ]; x18, x17<- arg1[2] * x5
xchg rdx, r12; x2, swapping with x18, which is currently in rdx
mulx r13, r14, [ rsi + 0x8 ]; x22, x21<- arg1[1] * x2
test al, al
adox rbp, r14
adcx rbp, r10
adox r13, r12
adcx rax, r13
mov r15, 0x33 ; moving imm to reg
bzhi r15, rbp, r15; x48 <- x43 (only least 0x33 bits)
shrd rbp, rax, 51; x47 <- x45||x43 >> 51
imul rcx, [ rsi + 0x8 ], 0x2; x8 <- arg1[1] * 0x2
xchg rdx, rcx; x8, swapping with x2, which is currently in rdx
mulx rdx, r8, [ rsi + 0x0 ]; x36, x35<- arg1[0] * x8
xchg rdx, rbx; x4, swapping with x36, which is currently in rdx
mulx rdx, r9, [ rsi + 0x18 ]; x14, x13<- arg1[3] * x4
mov r10, rdx; preserving value of x14 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r12, r14, rcx; x16, x15<- arg1[2] * x2
test al, al
adox r9, r14
adcx r9, r8
adox r12, r10
adcx rbx, r12
xor rdx, rdx
adox r9, rbp
adox rbx, rdx
mov r13, r9; x84, copying x81 here, cause x81 is needed in a reg for other than x84, namely all: , x84, x85, size: 2
shrd r13, rbx, 51; x84 <- x83||x81 >> 51
imul rax, [ rsi + 0x10 ], 0x2; x7 <- arg1[2] * 0x2
xchg rdx, rax; x7, swapping with 0x0, which is currently in rdx
mulx rbp, r8, [ rsi + 0x0 ]; x34, x33<- arg1[0] * x7
xchg rdx, rcx; x2, swapping with x7, which is currently in rdx
mulx rdx, r10, [ rsi + 0x18 ]; x12, x11<- arg1[3] * x2
mov r14, rdx; preserving value of x12 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r12, rbx, [ rsi + 0x8 ]; x28, x27<- arg1[1] * arg1[1]
test al, al
adox r10, rbx
adox r12, r14
adcx r10, r8
adcx rbp, r12
xor rdx, rdx
adox r10, r13
adox rbp, rdx
mov rax, r10; x89, copying x86 here, cause x86 is needed in a reg for other than x89, namely all: , x89, x90, size: 2
shrd rax, rbp, 51; x89 <- x88||x86 >> 51
mov r13, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r11, r8, r11; x10, x9<- arg1[4] * x1
imul rdx, [ rsi + 0x18 ], 0x2; x6 <- arg1[3] * 0x2
xchg rdx, rcx; x7, swapping with x6, which is currently in rdx
mulx rdx, r14, [ rsi + 0x8 ]; x26, x25<- arg1[1] * x7
add r8, r14; could be done better, if r0 has been u8 as well
mov rbx, rdx; preserving value of x26 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r12, rbp, rcx; x32, x31<- arg1[0] * x6
adcx rbx, r11
xor rdx, rdx
adox r8, rbp
adcx r8, rax
adox r12, rbx
adc r12, 0x0
imul r13, [ rsi + 0x20 ], 0x2; x3 <- arg1[4] * 0x2
mov rax, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r11, r14, [ rsi + 0x10 ]; x20, x19<- arg1[2] * arg1[2]
mov rdx, r8; x94, copying x91 here, cause x91 is needed in a reg for other than x94, namely all: , x95, x94, size: 2
shrd rdx, r12, 51; x94 <- x93||x91 >> 51
mov rbp, rdx; preserving value of x94 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r13, rbx, r13; x30, x29<- arg1[0] * x3
mov rdx, rcx; x6 to rdx
mulx rdx, rcx, [ rsi + 0x8 ]; x24, x23<- arg1[1] * x6
add r14, rcx; could be done better, if r0 has been u8 as well
mov r12, -0x3 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r14, rbx
setc bl; spill CF x50 to reg (rbx)
clc;
adcx r14, rbp
movzx rbx, bl
lea rdx, [ rdx + r11 ]
lea rdx, [ rdx + rbx ]
adox r13, rdx
adc r13, 0x0
mov r11, r14; x99, copying x96 here, cause x96 is needed in a reg for other than x99, namely all: , x100, x99, size: 2
shrd r11, r13, 51; x99 <- x98||x96 >> 51
imul r11, r11, 0x13; x101 <- x99 * 0x13
mov rbp, 0x33 ; moving imm to reg
bzhi r8, r8, rbp; x95 <- x91 (only least 0x33 bits)
lea r15, [ r15 + r11 ]
mov [ rdi + 0x18 ], r8; out1[3] = x95
mov rcx, r15; x103, copying x102 here, cause x102 is needed in a reg for other than x103, namely all: , x104, x103, size: 2
shr rcx, 51; x103 <- x102>> 51
mov rbx, 0x7ffffffffffff ; moving imm to reg
and r15, rbx; x104 <- x102&0x7ffffffffffff
and r14, rbx; x100 <- x96&0x7ffffffffffff
bzhi r9, r9, rbp; x85 <- x81 (only least 0x33 bits)
lea rcx, [ rcx + r9 ]
mov rdx, rcx; x106, copying x105 here, cause x105 is needed in a reg for other than x106, namely all: , x106, x107, size: 2
shr rdx, 51; x106 <- x105>> 51
and rcx, rbx; x107 <- x105&0x7ffffffffffff
bzhi r10, r10, rbp; x90 <- x86 (only least 0x33 bits)
mov [ rdi + 0x20 ], r14; out1[4] = x100
mov [ rdi + 0x8 ], rcx; out1[1] = x107
mov [ rdi + 0x0 ], r15; out1[0] = x104
lea rdx, [ rdx + r10 ]
mov [ rdi + 0x10 ], rdx; out1[2] = x108
mov rbx, [ rsp + 0x0 ]; restoring from stack
mov rbp, [ rsp + 0x8 ]; restoring from stack
mov r12, [ rsp + 0x10 ]; restoring from stack
mov r13, [ rsp + 0x18 ]; restoring from stack
mov r14, [ rsp + 0x20 ]; restoring from stack
mov r15, [ rsp + 0x28 ]; restoring from stack
add rsp, 0x30 
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; clocked at 2200 MHz
; first cyclecount 43.51, best 36.36206896551724, lastGood 36.7008547008547
; seed 257070995500385 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4463 ms / 500 runs=> 8.926ms/run
; Time spent for assembling and measureing (initial batch_size=232, initial num_batches=101): 2372 ms
; Ratio (time for assembling + measure)/(total runtime for 500runs): 0.5314810665471655
; number reverted permutation/ tried permutation: 159 / 240 =66.250%
; number reverted decision/ tried decision: 163 / 261 =62.452%