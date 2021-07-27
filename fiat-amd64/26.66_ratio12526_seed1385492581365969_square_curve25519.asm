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
imul rbp, r11, 0x2; x2 <- x1 * 0x2
imul r12, rbx, 0x2; x5 <- x4 * 0x2
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r12, r13, r12; x18, x17<- arg1[2] * x5
mov rdx, rbp; x2 to rdx
mulx rbp, r14, [ rsi + 0x8 ]; x22, x21<- arg1[1] * x2
xor r15, r15
adox r13, r14
adcx r13, r10
adox rbp, r12
adcx rax, rbp
imul rcx, [ rsi + 0x8 ], 0x2; x8 <- arg1[1] * 0x2
mov r8, 0x7ffffffffffff ; moving imm to reg
mov r9, r13; x48, copying x43 here, cause x43 is needed in a reg for other than x48, namely all: , x48, x47, size: 2
and r9, r8; x48 <- x43&0x7ffffffffffff
shrd r13, rax, 51; x47 <- x45||x43 >> 51
mulx r10, r12, [ rsi + 0x10 ]; x16, x15<- arg1[2] * x2
mov r14, rdx; preserving value of x2 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx rbx, rbp, rbx; x14, x13<- arg1[3] * x4
mov rdx, rcx; x8 to rdx
mulx rdx, rcx, [ rsi + 0x0 ]; x36, x35<- arg1[0] * x8
xor rax, rax
adox rbp, r12
adcx rbp, rcx
adox r10, rbx
mov r15, -0x3 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbp, r13
adcx rdx, r10
adox rdx, rax
mov r13, rbp; x84, copying x81 here, cause x81 is needed in a reg for other than x84, namely all: , x84, x85, size: 2
shrd r13, rdx, 51; x84 <- x83||x81 >> 51
imul r12, [ rsi + 0x10 ], 0x2; x7 <- arg1[2] * 0x2
mov rdx, r12; x7 to rdx
mulx r12, rbx, [ rsi + 0x0 ]; x34, x33<- arg1[0] * x7
mov rcx, rdx; preserving value of x7 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx r14, r10, r14; x12, x11<- arg1[3] * x2
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rax, r15, [ rsi + 0x8 ]; x28, x27<- arg1[1] * arg1[1]
add r10, r15; could be done better, if r0 has been u8 as well
adcx rax, r14
test al, al
adox r10, rbx
adox r12, rax
adcx r10, r13
adc r12, 0x0
imul rdx, [ rsi + 0x18 ], 0x2; x6 <- arg1[3] * 0x2
mulx r13, rbx, [ rsi + 0x0 ]; x32, x31<- arg1[0] * x6
mov r14, rdx; preserving value of x6 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx rcx, r15, rcx; x26, x25<- arg1[1] * x7
mov rdx, r10; x89, copying x86 here, cause x86 is needed in a reg for other than x89, namely all: , x90, x89, size: 2
shrd rdx, r12, 51; x89 <- x88||x86 >> 51
mov rax, rdx; preserving value of x89 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r11, r12, r11; x10, x9<- arg1[4] * x1
xor rdx, rdx
adox r12, r15
adox rcx, r11
adcx r12, rbx
mov rbx, -0x3 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r12, rax
adcx r13, rcx
adox r13, rdx
imul r15, [ rsi + 0x20 ], 0x2; x3 <- arg1[4] * 0x2
mov rax, r12; x94, copying x91 here, cause x91 is needed in a reg for other than x94, namely all: , x95, x94, size: 2
shrd rax, r13, 51; x94 <- x93||x91 >> 51
mov r11, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r14, rcx, r14; x24, x23<- arg1[1] * x6
mov rdx, r15; x3 to rdx
mulx rdx, r15, [ rsi + 0x0 ]; x30, x29<- arg1[0] * x3
mov r13, rdx; preserving value of x30 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r11, rbx, [ rsi + 0x10 ]; x20, x19<- arg1[2] * arg1[2]
xor rdx, rdx
adox rbx, rcx
adcx rbx, r15
adox r14, r11
mov rcx, -0x3 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbx, rax
adcx r13, r14
adox r13, rdx
mov rax, rbx; x99, copying x96 here, cause x96 is needed in a reg for other than x99, namely all: , x99, x100, size: 2
shrd rax, r13, 51; x99 <- x98||x96 >> 51
imul rax, rax, 0x13; x101 <- x99 * 0x13
lea r9, [ r9 + rax ]
mov r15, r9; x104, copying x102 here, cause x102 is needed in a reg for other than x104, namely all: , x104, x103, size: 2
and r15, r8; x104 <- x102&0x7ffffffffffff
and rbp, r8; x85 <- x81&0x7ffffffffffff
mov [ rdi + 0x0 ], r15; out1[0] = x104
shr r9, 51; x103 <- x102>> 51
and r10, r8; x90 <- x86&0x7ffffffffffff
lea r9, [ r9 + rbp ]
mov r11, r9; x106, copying x105 here, cause x105 is needed in a reg for other than x106, namely all: , x107, x106, size: 2
shr r11, 51; x106 <- x105>> 51
mov r14, 0x33 ; moving imm to reg
bzhi r9, r9, r14; x107 <- x105 (only least 0x33 bits)
lea r11, [ r11 + r10 ]
mov [ rdi + 0x10 ], r11; out1[2] = x108
and rbx, r8; x100 <- x96&0x7ffffffffffff
and r12, r8; x95 <- x91&0x7ffffffffffff
mov [ rdi + 0x20 ], rbx; out1[4] = x100
mov [ rdi + 0x8 ], r9; out1[1] = x107
mov [ rdi + 0x18 ], r12; out1[3] = x95
mov rbx, [ rsp + 0x0 ]; restoring from stack
mov rbp, [ rsp + 0x8 ]; restoring from stack
mov r12, [ rsp + 0x10 ]; restoring from stack
mov r13, [ rsp + 0x18 ]; restoring from stack
mov r14, [ rsp + 0x20 ]; restoring from stack
mov r15, [ rsp + 0x28 ]; restoring from stack
add rsp, 0x30 
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; clocked at 3600 MHz
; first cyclecount 36.04, best 26.583050847457628, lastGood 26.662207357859533
; seed 1385492581365969 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4814 ms / 500 runs=> 9.628ms/run
; Time spent for assembling and measureing (initial batch_size=299, initial num_batches=101): 2628 ms
; Ratio (time for assembling + measure)/(total runtime for 500runs): 0.5459077690070627
; number reverted permutation/ tried permutation: 172 / 241 =71.369%
; number reverted decision/ tried decision: 184 / 260 =70.769%