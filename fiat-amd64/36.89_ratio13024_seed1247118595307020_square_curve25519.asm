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
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r10, r11, [ rsi + 0x0 ]; x38, x37<- arg1[0] * arg1[0]
imul rbx, rax, 0x2; x2 <- x1 * 0x2
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbp, r12, rbx; x22, x21<- arg1[1] * x2
imul r13, [ rsi + 0x18 ], 0x13; x4 <- arg1[3] * 0x13
imul r14, r13, 0x2; x5 <- x4 * 0x2
mov rdx, r14; x5 to rdx
mulx rdx, r14, [ rsi + 0x10 ]; x18, x17<- arg1[2] * x5
xor r15, r15
adox r14, r12
adox rbp, rdx
adcx r14, r11
adcx r10, rbp
imul rcx, [ rsi + 0x8 ], 0x2; x8 <- arg1[1] * 0x2
mov r8, 0x7ffffffffffff ; moving imm to reg
mov r9, r14; x48, copying x43 here, cause x43 is needed in a reg for other than x48, namely all: , x47, x48, size: 2
and r9, r8; x48 <- x43&0x7ffffffffffff
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r11, r12, rbx; x16, x15<- arg1[2] * x2
shrd r14, r10, 51; x47 <- x45||x43 >> 51
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rcx, rbp, rcx; x36, x35<- arg1[0] * x8
mov rdx, r13; x4 to rdx
mulx rdx, r13, [ rsi + 0x18 ]; x14, x13<- arg1[3] * x4
xor r10, r10
adox r13, r12
adcx r13, rbp
adox r11, rdx
adcx rcx, r11
xor r15, r15
adox r13, r14
adox rcx, r15
mov r10, r13; x84, copying x81 here, cause x81 is needed in a reg for other than x84, namely all: , x84, x85, size: 2
shrd r10, rcx, 51; x84 <- x83||x81 >> 51
imul r12, [ rsi + 0x10 ], 0x2; x7 <- arg1[2] * 0x2
mov rdx, r12; x7 to rdx
mulx r12, r14, [ rsi + 0x0 ]; x34, x33<- arg1[0] * x7
mov rbp, rdx; preserving value of x7 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r11, rcx, [ rsi + 0x8 ]; x28, x27<- arg1[1] * arg1[1]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rbx, r15, rbx; x12, x11<- arg1[3] * x2
add r15, rcx; could be done better, if r0 has been u8 as well
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, r14
adcx r11, rbx
adox r12, r11
xor r14, r14
adox r15, r10
adox r12, r14
mov r10, r15; x89, copying x86 here, cause x86 is needed in a reg for other than x89, namely all: , x89, x90, size: 2
shrd r10, r12, 51; x89 <- x88||x86 >> 51
imul rcx, [ rsi + 0x18 ], 0x2; x6 <- arg1[3] * 0x2
mov rdx, rcx; x6 to rdx
mulx rcx, rbx, [ rsi + 0x0 ]; x32, x31<- arg1[0] * x6
mov r11, rdx; preserving value of x6 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx rbp, r12, rbp; x26, x25<- arg1[1] * x7
mov rdx, rax; x1 to rdx
mulx rdx, rax, [ rsi + 0x20 ]; x10, x9<- arg1[4] * x1
add rax, r12; could be done better, if r0 has been u8 as well
mov r12, -0x3 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rax, rbx
setc bl; spill CF x58 to reg (rbx)
clc;
adcx rax, r10
movzx rbx, bl
lea rbp, [ rbp + rdx ]
lea rbp, [ rbp + rbx ]
adox rcx, rbp
adc rcx, 0x0
mov r10, rax; x94, copying x91 here, cause x91 is needed in a reg for other than x94, namely all: , x94, x95, size: 2
shrd r10, rcx, 51; x94 <- x93||x91 >> 51
imul rdx, [ rsi + 0x20 ], 0x2; x3 <- arg1[4] * 0x2
mulx rdx, rbx, [ rsi + 0x0 ]; x30, x29<- arg1[0] * x3
mov rbp, rdx; preserving value of x30 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx rcx, r14, [ rsi + 0x10 ]; x20, x19<- arg1[2] * arg1[2]
mov rdx, r11; x6 to rdx
mulx rdx, r11, [ rsi + 0x8 ]; x24, x23<- arg1[1] * x6
add r14, r11; could be done better, if r0 has been u8 as well
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, rbx
adcx rdx, rcx
clc;
adcx r14, r10
adox rbp, rdx
adc rbp, 0x0
mov r10, r14; x99, copying x96 here, cause x96 is needed in a reg for other than x99, namely all: , x100, x99, size: 2
shrd r10, rbp, 51; x99 <- x98||x96 >> 51
imul r10, r10, 0x13; x101 <- x99 * 0x13
lea r9, [ r9 + r10 ]
mov rbx, 0x33 ; moving imm to reg
bzhi r13, r13, rbx; x85 <- x81 (only least 0x33 bits)
mov rcx, r9; x103, copying x102 here, cause x102 is needed in a reg for other than x103, namely all: , x104, x103, size: 2
shr rcx, 51; x103 <- x102>> 51
lea rcx, [ rcx + r13 ]
mov r11, rcx; x106, copying x105 here, cause x105 is needed in a reg for other than x106, namely all: , x106, x107, size: 2
shr r11, 51; x106 <- x105>> 51
and rcx, r8; x107 <- x105&0x7ffffffffffff
mov [ rdi + 0x8 ], rcx; out1[1] = x107
bzhi r15, r15, rbx; x90 <- x86 (only least 0x33 bits)
lea r11, [ r11 + r15 ]
mov [ rdi + 0x10 ], r11; out1[2] = x108
bzhi r9, r9, rbx; x104 <- x102 (only least 0x33 bits)
bzhi r14, r14, rbx; x100 <- x96 (only least 0x33 bits)
mov [ rdi + 0x0 ], r9; out1[0] = x104
bzhi rax, rax, rbx; x95 <- x91 (only least 0x33 bits)
mov [ rdi + 0x18 ], rax; out1[3] = x95
mov [ rdi + 0x20 ], r14; out1[4] = x100
mov rbx, [ rsp + 0x0 ]; restoring from stack
mov rbp, [ rsp + 0x8 ]; restoring from stack
mov r12, [ rsp + 0x10 ]; restoring from stack
mov r13, [ rsp + 0x18 ]; restoring from stack
mov r14, [ rsp + 0x20 ]; restoring from stack
mov r15, [ rsp + 0x28 ]; restoring from stack
add rsp, 0x30 
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; clocked at 4600 MHz
; first cyclecount 46.325, best 36.83168316831683, lastGood 36.8921568627451
; seed 1247118595307020 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4351 ms / 500 runs=> 8.702ms/run
; Time spent for assembling and measureing (initial batch_size=203, initial num_batches=101): 1741 ms
; Ratio (time for assembling + measure)/(total runtime for 500runs): 0.40013789933348654
; number reverted permutation/ tried permutation: 190 / 246 =77.236%
; number reverted decision/ tried decision: 184 / 255 =72.157%