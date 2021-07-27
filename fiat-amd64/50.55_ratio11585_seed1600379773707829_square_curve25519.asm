SECTION .text
	GLOBAL square_curve25519
square_curve25519:
sub rsp, 0x38 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x8 ], rbx; saving to stack
mov [ rsp + 0x10 ], rbp; saving to stack
mov [ rsp + 0x18 ], r12; saving to stack
mov [ rsp + 0x20 ], r13; saving to stack
mov [ rsp + 0x28 ], r14; saving to stack
mov [ rsp + 0x30 ], r15; saving to stack
imul rax, [ rsi + 0x18 ], 0x13; x4 <- arg1[3] * 0x13
imul r10, rax, 0x2; x5 <- x4 * 0x2
imul r11, [ rsi + 0x20 ], 0x13; x1 <- arg1[4] * 0x13
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r10, rbx, r10; x18, x17<- arg1[2] * x5
imul rbp, r11, 0x2; x2 <- x1 * 0x2
mov rdx, rbp; x2 to rdx
mulx rbp, r12, [ rsi + 0x8 ]; x22, x21<- arg1[1] * x2
add rbx, r12; could be done better, if r0 has been u8 as well
mov r13, rdx; preserving value of x2 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r14, r15, [ rsi + 0x0 ]; x38, x37<- arg1[0] * arg1[0]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rcx, r8, r13; x16, x15<- arg1[2] * x2
adcx rbp, r10
test al, al
adox rbx, r15
mov rdx, rax; x4 to rdx
mulx rdx, rax, [ rsi + 0x18 ]; x14, x13<- arg1[3] * x4
adox r14, rbp
imul r9, [ rsi + 0x8 ], 0x2; x8 <- arg1[1] * 0x2
imul r10, [ rsi + 0x10 ], 0x2; x7 <- arg1[2] * 0x2
mov r12, rdx; preserving value of x14 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx r13, r15, r13; x12, x11<- arg1[3] * x2
xor rdx, rdx
adox rax, r8
mov r8, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r9, rbp, r9; x36, x35<- arg1[0] * x8
adox rcx, r12
mov rdx, rbx; x47, copying x43 here, cause x43 is needed in a reg for other than x47, namely all: , x47, x48, size: 2
shrd rdx, r14, 51; x47 <- x45||x43 >> 51
mov r12, rdx; preserving value of x47 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r14, r8, r10; x34, x33<- arg1[0] * x7
test al, al
adox rax, rbp
adcx rax, r12
adox r9, rcx
adc r9, 0x0
mov rdx, rax; x84, copying x81 here, cause x81 is needed in a reg for other than x84, namely all: , x85, x84, size: 2
shrd rdx, r9, 51; x84 <- x83||x81 >> 51
mov rbp, rdx; preserving value of x84 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx rcx, r12, [ rsi + 0x8 ]; x28, x27<- arg1[1] * arg1[1]
add r15, r12; could be done better, if r0 has been u8 as well
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, r8
adcx rcx, r13
mov rdx, r11; x1 to rdx
mulx rdx, r11, [ rsi + 0x20 ]; x10, x9<- arg1[4] * x1
clc;
adcx r15, rbp
adox r14, rcx
adc r14, 0x0
imul r13, [ rsi + 0x18 ], 0x2; x6 <- arg1[3] * 0x2
xchg rdx, r13; x6, swapping with x10, which is currently in rdx
mulx r8, r9, [ rsi + 0x0 ]; x32, x31<- arg1[0] * x6
mov rbp, rdx; preserving value of x6 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r10, r12, r10; x26, x25<- arg1[1] * x7
mov rdx, r15; x89, copying x86 here, cause x86 is needed in a reg for other than x89, namely all: , x90, x89, size: 2
shrd rdx, r14, 51; x89 <- x88||x86 >> 51
xor rcx, rcx
adox r11, r12
mov r14, rdx; preserving value of x89 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r12, rcx, [ rsi + 0x10 ]; x20, x19<- arg1[2] * arg1[2]
adox r10, r13
imul rdx, [ rsi + 0x20 ], 0x2; x3 <- arg1[4] * 0x2
mov r13, rdx; preserving value of x3 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx rbp, rdi, rbp; x24, x23<- arg1[1] * x6
xor rdx, rdx
adox r11, r9
adox r8, r10
adcx r11, r14
adc r8, 0x0
xchg rdx, r13; x3, swapping with 0x0, which is currently in rdx
mulx rdx, r9, [ rsi + 0x0 ]; x30, x29<- arg1[0] * x3
add rcx, rdi; could be done better, if r0 has been u8 as well
adcx rbp, r12
mov r14, r11; x94, copying x91 here, cause x91 is needed in a reg for other than x94, namely all: , x94, x95, size: 2
shrd r14, r8, 51; x94 <- x93||x91 >> 51
add rcx, r9; could be done better, if r0 has been u8 as well
adcx rdx, rbp
xor r12, r12
adox rcx, r14
adox rdx, r12
mov r13, rcx; x99, copying x96 here, cause x96 is needed in a reg for other than x99, namely all: , x100, x99, size: 2
shrd r13, rdx, 51; x99 <- x98||x96 >> 51
imul r13, r13, 0x13; x101 <- x99 * 0x13
mov r10, 0x7ffffffffffff ; moving imm to reg
and rbx, r10; x48 <- x43&0x7ffffffffffff
lea rbx, [ rbx + r13 ]
and rcx, r10; x100 <- x96&0x7ffffffffffff
mov rdi, rbx; x103, copying x102 here, cause x102 is needed in a reg for other than x103, namely all: , x104, x103, size: 2
shr rdi, 51; x103 <- x102>> 51
mov r8, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r8 + 0x20 ], rcx; out1[4] = x100
mov r9, 0x33 ; moving imm to reg
bzhi rbx, rbx, r9; x104 <- x102 (only least 0x33 bits)
and rax, r10; x85 <- x81&0x7ffffffffffff
lea rdi, [ rdi + rax ]
bzhi r9, rdi, r9; x107 <- x105 (only least 0x33 bits)
mov [ r8 + 0x8 ], r9; out1[1] = x107
shr rdi, 51; x106 <- x105>> 51
and r15, r10; x90 <- x86&0x7ffffffffffff
mov [ r8 + 0x0 ], rbx; out1[0] = x104
mov rbp, 0x33 ; moving imm to reg
bzhi r11, r11, rbp; x95 <- x91 (only least 0x33 bits)
mov [ r8 + 0x18 ], r11; out1[3] = x95
lea rdi, [ rdi + r15 ]
mov [ r8 + 0x10 ], rdi; out1[2] = x108
mov rbx, [ rsp + 0x8 ]; restoring from stack
mov rbp, [ rsp + 0x10 ]; restoring from stack
mov r12, [ rsp + 0x18 ]; restoring from stack
mov r13, [ rsp + 0x20 ]; restoring from stack
mov r14, [ rsp + 0x28 ]; restoring from stack
mov r15, [ rsp + 0x30 ]; restoring from stack
add rsp, 0x38 
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; clocked at 2200 MHz
; first cyclecount 55.86, best 49.903614457831324, lastGood 50.55357142857143
; seed 1600379773707829 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 607954 ms / 60000 runs=> 10.132566666666667ms/run
; Time spent for assembling and measureing (initial batch_size=169, initial num_batches=101): 329439 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.5418814581366354
; number reverted permutation/ tried permutation: 26463 / 30131 =87.826%
; number reverted decision/ tried decision: 22175 / 29870 =74.238%