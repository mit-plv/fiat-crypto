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
imul r10, rax, 0x2; x2 <- x1 * 0x2
imul r11, [ rsi + 0x18 ], 0x13; x4 <- arg1[3] * 0x13
imul rbx, r11, 0x2; x5 <- x4 * 0x2
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbp, r12, r10; x22, x21<- arg1[1] * x2
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rbx, r13, rbx; x18, x17<- arg1[2] * x5
test al, al
adox r13, r12
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r11, r14, r11; x14, x13<- arg1[3] * x4
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r15, rcx, [ rsi + 0x0 ]; x38, x37<- arg1[0] * arg1[0]
adcx r13, rcx
adox rbp, rbx
adcx r15, rbp
imul rdx, [ rsi + 0x8 ], 0x2; x8 <- arg1[1] * 0x2
mulx rdx, r8, [ rsi + 0x0 ]; x36, x35<- arg1[0] * x8
mov r9, 0x7ffffffffffff ; moving imm to reg
mov r12, r13; x48, copying x43 here, cause x43 is needed in a reg for other than x48, namely all: , x48, x47, size: 2
and r12, r9; x48 <- x43&0x7ffffffffffff
shrd r13, r15, 51; x47 <- x45||x43 >> 51
mov rbx, rdx; preserving value of x36 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx rcx, rbp, r10; x16, x15<- arg1[2] * x2
add r14, rbp; could be done better, if r0 has been u8 as well
adcx rcx, r11
add r14, r8; could be done better, if r0 has been u8 as well
adcx rbx, rcx
add r14, r13; could be done better, if r0 has been u8 as well
adc rbx, 0x0
imul rdx, [ rsi + 0x10 ], 0x2; x7 <- arg1[2] * 0x2
mov r11, r14; x84, copying x81 here, cause x81 is needed in a reg for other than x84, namely all: , x84, x85, size: 2
shrd r11, rbx, 51; x84 <- x83||x81 >> 51
mulx r15, r8, [ rsi + 0x0 ]; x34, x33<- arg1[0] * x7
mov r13, rdx; preserving value of x7 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx r10, rbp, r10; x12, x11<- arg1[3] * x2
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rcx, rbx, [ rsi + 0x8 ]; x28, x27<- arg1[1] * arg1[1]
add rbp, rbx; could be done better, if r0 has been u8 as well
mov rdx, r13; x7 to rdx
mulx rdx, r13, [ rsi + 0x8 ]; x26, x25<- arg1[1] * x7
adcx rcx, r10
test al, al
adox rbp, r8
adox r15, rcx
adcx rbp, r11
adc r15, 0x0
mov r11, rbp; x89, copying x86 here, cause x86 is needed in a reg for other than x89, namely all: , x89, x90, size: 2
shrd r11, r15, 51; x89 <- x88||x86 >> 51
imul r8, [ rsi + 0x18 ], 0x2; x6 <- arg1[3] * 0x2
mov r10, rdx; preserving value of x26 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx rax, rbx, rax; x10, x9<- arg1[4] * x1
add rbx, r13; could be done better, if r0 has been u8 as well
mov rdx, r8; x6 to rdx
mulx r8, r13, [ rsi + 0x0 ]; x32, x31<- arg1[0] * x6
adcx r10, rax
add rbx, r13; could be done better, if r0 has been u8 as well
adcx r8, r10
add rbx, r11; could be done better, if r0 has been u8 as well
adc r8, 0x0
mov rcx, rbx; x94, copying x91 here, cause x91 is needed in a reg for other than x94, namely all: , x94, x95, size: 2
shrd rcx, r8, 51; x94 <- x93||x91 >> 51
mulx rdx, r15, [ rsi + 0x8 ]; x24, x23<- arg1[1] * x6
mov r11, rdx; preserving value of x24 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx rax, r13, [ rsi + 0x10 ]; x20, x19<- arg1[2] * arg1[2]
imul rdx, [ rsi + 0x20 ], 0x2; x3 <- arg1[4] * 0x2
xor r10, r10
adox r13, r15
adox r11, rax
mulx rdx, r8, [ rsi + 0x0 ]; x30, x29<- arg1[0] * x3
adcx r13, r8
adcx rdx, r11
add r13, rcx; could be done better, if r0 has been u8 as well
adc rdx, 0x0
mov rcx, r13; x99, copying x96 here, cause x96 is needed in a reg for other than x99, namely all: , x99, x100, size: 2
shrd rcx, rdx, 51; x99 <- x98||x96 >> 51
imul rcx, rcx, 0x13; x101 <- x99 * 0x13
and r14, r9; x85 <- x81&0x7ffffffffffff
lea r12, [ r12 + rcx ]
mov r15, r12; x104, copying x102 here, cause x102 is needed in a reg for other than x104, namely all: , x103, x104, size: 2
and r15, r9; x104 <- x102&0x7ffffffffffff
and r13, r9; x100 <- x96&0x7ffffffffffff
mov [ rdi + 0x20 ], r13; out1[4] = x100
shr r12, 51; x103 <- x102>> 51
lea r12, [ r12 + r14 ]
mov rax, r12; x107, copying x105 here, cause x105 is needed in a reg for other than x107, namely all: , x106, x107, size: 2
and rax, r9; x107 <- x105&0x7ffffffffffff
mov [ rdi + 0x0 ], r15; out1[0] = x104
and rbp, r9; x90 <- x86&0x7ffffffffffff
shr r12, 51; x106 <- x105>> 51
lea r12, [ r12 + rbp ]
mov r11, 0x33 ; moving imm to reg
bzhi rbx, rbx, r11; x95 <- x91 (only least 0x33 bits)
mov [ rdi + 0x10 ], r12; out1[2] = x108
mov [ rdi + 0x18 ], rbx; out1[3] = x95
mov [ rdi + 0x8 ], rax; out1[1] = x107
mov rbx, [ rsp + 0x0 ]; restoring from stack
mov rbp, [ rsp + 0x8 ]; restoring from stack
mov r12, [ rsp + 0x10 ]; restoring from stack
mov r13, [ rsp + 0x18 ]; restoring from stack
mov r14, [ rsp + 0x20 ]; restoring from stack
mov r15, [ rsp + 0x28 ]; restoring from stack
add rsp, 0x30 
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; clocked at 2600 MHz
; first cyclecount 40.915, best 29.503649635036496, lastGood 29.692307692307693
; seed 2886888088419340 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 809420 ms / 60000 runs=> 13.490333333333334ms/run
; Time spent for assembling and measureing (initial batch_size=273, initial num_batches=101): 516506 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.6381186528625435
; number reverted permutation/ tried permutation: 25886 / 30063 =86.106%
; number reverted decision/ tried decision: 22036 / 29938 =73.605%