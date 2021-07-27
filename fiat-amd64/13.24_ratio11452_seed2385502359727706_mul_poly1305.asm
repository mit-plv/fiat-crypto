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
imul rax, [ rdx + 0x8 ], 0xa; x10001 <- arg2[1] * 0xa
imul r10, [ rdx + 0x10 ], 0xa; x10002 <- arg2[2] * 0xa
mov r11, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x0 ]; saving arg2[0] in rdx.
mulx rbx, rbp, [ rsi + 0x0 ]; x18, x17<- arg1[0] * arg2[0]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r10, r12, r10; x6, x5<- arg1[1] * x10002
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rax, r13, rax; x4, x3<- arg1[2] * x10001
xor r14, r14
adox r13, r12
adox r10, rax
adcx r13, rbp
adcx rbx, r10
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r15, rcx, [ r11 + 0x0 ]; x12, x11<- arg1[1] * arg2[0]
mov r8, r13; x27, copying x23 here, cause x23 is needed in a reg for other than x27, namely all: , x28, x27, size: 2
shrd r8, rbx, 44; x27 <- x25||x23 >> 44
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r9, rbp, [ r11 + 0x8 ]; x16, x15<- arg1[0] * arg2[1]
imul r12, [ r11 + 0x10 ], 0x5; x10000 <- arg2[2] * 0x5
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r12, rax, r12; x2, x1<- arg1[2] * x10000
xor r10, r10
adox rax, rcx
adcx rax, rbp
adox r15, r12
mov r14, -0x3 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rax, r8
adcx r9, r15
adox r9, r10
mov rbx, rax; x48, copying x45 here, cause x45 is needed in a reg for other than x48, namely all: , x48, x49, size: 2
shrd rbx, r9, 43; x48 <- x47||x45 >> 43
imul rcx, [ r11 + 0x8 ], 0x2; x10003 <- arg2[1] * 0x2
mov rdx, rcx; x10003 to rdx
mulx rdx, rcx, [ rsi + 0x8 ]; x10, x9<- arg1[1] * x10003
mov r8, rdx; preserving value of x10 into a new reg
mov rdx, [ r11 + 0x0 ]; saving arg2[0] in rdx.
mulx rbp, r12, [ rsi + 0x10 ]; x8, x7<- arg1[2] * arg2[0]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r15, r9, [ r11 + 0x10 ]; x14, x13<- arg1[0] * arg2[2]
add r12, rcx; could be done better, if r0 has been u8 as well
adcx r8, rbp
xor rcx, rcx
adox r12, r9
adox r15, r8
adcx r12, rbx
adc r15, 0x0
mov r10, r12; x53, copying x50 here, cause x50 is needed in a reg for other than x53, namely all: , x53, x54, size: 2
shrd r10, r15, 43; x53 <- x52||x50 >> 43
imul r10, r10, 0x5; x55 <- x53 * 0x5
mov rbx, 0xfffffffffff ; moving imm to reg
and r13, rbx; x28 <- x23&0xfffffffffff
lea r13, [ r13 + r10 ]
mov rbp, r13; x57, copying x56 here, cause x56 is needed in a reg for other than x57, namely all: , x57, x58, size: 2
shr rbp, 44; x57 <- x56>> 44
mov r9, 0x7ffffffffff ; moving imm to reg
and rax, r9; x49 <- x45&0x7ffffffffff
lea rbp, [ rbp + rax ]
and r12, r9; x54 <- x50&0x7ffffffffff
mov r8, rbp; x60, copying x59 here, cause x59 is needed in a reg for other than x60, namely all: , x60, x61, size: 2
shr r8, 43; x60 <- x59>> 43
lea r8, [ r8 + r12 ]
mov [ rdi + 0x10 ], r8; out1[2] = x62
and rbp, r9; x61 <- x59&0x7ffffffffff
mov [ rdi + 0x8 ], rbp; out1[1] = x61
and r13, rbx; x58 <- x56&0xfffffffffff
mov [ rdi + 0x0 ], r13; out1[0] = x58
mov rbx, [ rsp + 0x0 ]; restoring from stack
mov rbp, [ rsp + 0x8 ]; restoring from stack
mov r12, [ rsp + 0x10 ]; restoring from stack
mov r13, [ rsp + 0x18 ]; restoring from stack
mov r14, [ rsp + 0x20 ]; restoring from stack
mov r15, [ rsp + 0x28 ]; restoring from stack
add rsp, 0x30 
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; clocked at 3500 MHz
; first cyclecount 19.365, best 13.24074074074074, lastGood 13.24074074074074
; seed 2385502359727706 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 12882 ms / 500 runs=> 25.764ms/run
; Time spent for assembling and measureing (initial batch_size=648, initial num_batches=101): 10571 ms
; Ratio (time for assembling + measure)/(total runtime for 500runs): 0.820602390933085
; number reverted permutation/ tried permutation: 233 / 266 =87.594%
; number reverted decision/ tried decision: 183 / 235 =77.872%