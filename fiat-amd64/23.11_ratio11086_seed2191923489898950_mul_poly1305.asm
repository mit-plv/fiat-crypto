SECTION .text
	GLOBAL mul_poly1305
mul_poly1305:
sub rsp, 0x30 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x0 ], rbx; saving to stack
mov [ rsp + 0x8 ], rbp; saving to stack
mov [ rsp + 0x10 ], r12; saving to stack
mov [ rsp + 0x18 ], r13; saving to stack
mov [ rsp + 0x20 ], r14; saving to stack
mov [ rsp + 0x28 ], r15; saving to stack
mov rax, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x0 ]; saving arg2[0] in rdx.
mulx r10, r11, [ rsi + 0x0 ]; x18, x17<- arg1[0] * arg2[0]
imul rbx, [ rax + 0x10 ], 0xa; x10002 <- arg2[2] * 0xa
imul rbp, [ rax + 0x8 ], 0xa; x10001 <- arg2[1] * 0xa
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbx, r12, rbx; x6, x5<- arg1[1] * x10002
mov rdx, rbp; x10001 to rdx
mulx rdx, rbp, [ rsi + 0x10 ]; x4, x3<- arg1[2] * x10001
test al, al
adox rbp, r12
adox rbx, rdx
adcx rbp, r11
adcx r10, rbx
mov r13, rbp; x27, copying x23 here, cause x23 is needed in a reg for other than x27, namely all: , x27, x28, size: 2
shrd r13, r10, 44; x27 <- x25||x23 >> 44
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx r14, r15, [ rsi + 0x8 ]; x12, x11<- arg1[1] * arg2[0]
imul rcx, [ rax + 0x10 ], 0x5; x10000 <- arg2[2] * 0x5
mov rdx, rcx; x10000 to rdx
mulx rdx, rcx, [ rsi + 0x10 ]; x2, x1<- arg1[2] * x10000
mov r8, rdx; preserving value of x2 into a new reg
mov rdx, [ rax + 0x8 ]; saving arg2[1] in rdx.
mulx r9, r11, [ rsi + 0x0 ]; x16, x15<- arg1[0] * arg2[1]
test al, al
adox rcx, r15
adox r14, r8
adcx rcx, r11
adcx r9, r14
add rcx, r13; could be done better, if r0 has been u8 as well
adc r9, 0x0
imul r12, [ rax + 0x8 ], 0x2; x10003 <- arg2[1] * 0x2
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r12, rbx, r12; x10, x9<- arg1[1] * x10003
mov r10, rcx; x48, copying x45 here, cause x45 is needed in a reg for other than x48, namely all: , x48, x49, size: 2
shrd r10, r9, 43; x48 <- x47||x45 >> 43
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r13, r15, [ rax + 0x0 ]; x8, x7<- arg1[2] * arg2[0]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r8, r11, [ rax + 0x10 ]; x14, x13<- arg1[0] * arg2[2]
add r15, rbx; could be done better, if r0 has been u8 as well
adcx r12, r13
test al, al
adox r15, r11
adox r8, r12
adcx r15, r10
adc r8, 0x0
mov r14, 0xfffffffffff ; moving imm to reg
and rbp, r14; x28 <- x23&0xfffffffffff
mov r9, r15; x53, copying x50 here, cause x50 is needed in a reg for other than x53, namely all: , x54, x53, size: 2
shrd r9, r8, 43; x53 <- x52||x50 >> 43
imul r9, r9, 0x5; x55 <- x53 * 0x5
mov rbx, 0x7ffffffffff ; moving imm to reg
and rcx, rbx; x49 <- x45&0x7ffffffffff
lea rbp, [ rbp + r9 ]
mov r10, rbp; x57, copying x56 here, cause x56 is needed in a reg for other than x57, namely all: , x57, x58, size: 2
shr r10, 44; x57 <- x56>> 44
lea r10, [ r10 + rcx ]
mov r13, r10; x60, copying x59 here, cause x59 is needed in a reg for other than x60, namely all: , x60, x61, size: 2
shr r13, 43; x60 <- x59>> 43
and r15, rbx; x54 <- x50&0x7ffffffffff
lea r13, [ r13 + r15 ]
and r10, rbx; x61 <- x59&0x7ffffffffff
and rbp, r14; x58 <- x56&0xfffffffffff
mov [ rdi + 0x10 ], r13; out1[2] = x62
mov [ rdi + 0x8 ], r10; out1[1] = x61
mov [ rdi + 0x0 ], rbp; out1[0] = x58
mov rbx, [ rsp + 0x0 ]; restoring from stack
mov rbp, [ rsp + 0x8 ]; restoring from stack
mov r12, [ rsp + 0x10 ]; restoring from stack
mov r13, [ rsp + 0x18 ]; restoring from stack
mov r14, [ rsp + 0x20 ]; restoring from stack
mov r15, [ rsp + 0x28 ]; restoring from stack
add rsp, 0x30 
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; clocked at 3198 MHz
; first cyclecount 30.25, best 22.265984654731458, lastGood 23.114058355437667
; seed 2191923489898950 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 9328 ms / 500 runs=> 18.656ms/run
; Time spent for assembling and measureing (initial batch_size=378, initial num_batches=101): 7015 ms
; Ratio (time for assembling + measure)/(total runtime for 500runs): 0.7520368782161235
; number reverted permutation/ tried permutation: 184 / 233 =78.970%
; number reverted decision/ tried decision: 211 / 268 =78.731%