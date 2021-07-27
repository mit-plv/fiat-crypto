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
imul rax, [ rdx + 0x10 ], 0xa; x10002 <- arg2[2] * 0xa
imul r10, [ rdx + 0x8 ], 0xa; x10001 <- arg2[1] * 0xa
mov r11, rdx; preserving value of arg2 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r10, rbx, r10; x4, x3<- arg1[2] * x10001
mov rdx, [ r11 + 0x0 ]; arg2[0] to rdx
mulx rbp, r12, [ rsi + 0x0 ]; x18, x17<- arg1[0] * arg2[0]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rax, r13, rax; x6, x5<- arg1[1] * x10002
add rbx, r13; could be done better, if r0 has been u8 as well
adcx rax, r10
add rbx, r12; could be done better, if r0 has been u8 as well
mov rdx, [ r11 + 0x8 ]; arg2[1] to rdx
mulx r14, r15, [ rsi + 0x0 ]; x16, x15<- arg1[0] * arg2[1]
adcx rbp, rax
mov rcx, rbx; x27, copying x23 here, cause x23 is needed in a reg for other than x27, namely all: , x27, x28, size: 2
shrd rcx, rbp, 44; x27 <- x25||x23 >> 44
imul r8, [ r11 + 0x10 ], 0x5; x10000 <- arg2[2] * 0x5
mov rdx, [ r11 + 0x0 ]; arg2[0] to rdx
mulx r9, r10, [ rsi + 0x8 ]; x12, x11<- arg1[1] * arg2[0]
mov rdx, r8; x10000 to rdx
mulx rdx, r8, [ rsi + 0x10 ]; x2, x1<- arg1[2] * x10000
xor r12, r12
adox r8, r10
adox r9, rdx
adcx r8, r15
adcx r14, r9
add r8, rcx; could be done better, if r0 has been u8 as well
adc r14, 0x0
mov r13, r8; x48, copying x45 here, cause x45 is needed in a reg for other than x48, namely all: , x48, x49, size: 2
shrd r13, r14, 43; x48 <- x47||x45 >> 43
mov rax, 0xfffffffffff ; moving imm to reg
and rbx, rax; x28 <- x23&0xfffffffffff
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r15, rbp, [ r11 + 0x10 ]; x14, x13<- arg1[0] * arg2[2]
imul rcx, [ r11 + 0x8 ], 0x2; x10003 <- arg2[1] * 0x2
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rcx, r10, rcx; x10, x9<- arg1[1] * x10003
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r9, r14, [ r11 + 0x0 ]; x8, x7<- arg1[2] * arg2[0]
add r14, r10; could be done better, if r0 has been u8 as well
adcx rcx, r9
test al, al
adox r14, rbp
adcx r14, r13
adox r15, rcx
adc r15, 0x0
mov r13, r14; x53, copying x50 here, cause x50 is needed in a reg for other than x53, namely all: , x54, x53, size: 2
shrd r13, r15, 43; x53 <- x52||x50 >> 43
imul r13, r13, 0x5; x55 <- x53 * 0x5
lea rbx, [ rbx + r13 ]
mov rbp, rbx; x57, copying x56 here, cause x56 is needed in a reg for other than x57, namely all: , x58, x57, size: 2
shr rbp, 44; x57 <- x56>> 44
mov r10, 0x7ffffffffff ; moving imm to reg
and r14, r10; x54 <- x50&0x7ffffffffff
and r8, r10; x49 <- x45&0x7ffffffffff
lea rbp, [ rbp + r8 ]
mov r9, rbp; x61, copying x59 here, cause x59 is needed in a reg for other than x61, namely all: , x61, x60, size: 2
and r9, r10; x61 <- x59&0x7ffffffffff
shr rbp, 43; x60 <- x59>> 43
and rbx, rax; x58 <- x56&0xfffffffffff
mov [ rdi + 0x8 ], r9; out1[1] = x61
lea rbp, [ rbp + r14 ]
mov [ rdi + 0x10 ], rbp; out1[2] = x62
mov [ rdi + 0x0 ], rbx; out1[0] = x58
mov rbx, [ rsp + 0x0 ]; restoring from stack
mov rbp, [ rsp + 0x8 ]; restoring from stack
mov r12, [ rsp + 0x10 ]; restoring from stack
mov r13, [ rsp + 0x18 ]; restoring from stack
mov r14, [ rsp + 0x20 ]; restoring from stack
mov r15, [ rsp + 0x28 ]; restoring from stack
add rsp, 0x30 
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; clocked at 4647 MHz
; first cyclecount 30.24, best 22.626038781163434, lastGood 22.65745856353591
; seed 3867572441203858 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4764 ms / 500 runs=> 9.528ms/run
; Time spent for assembling and measureing (initial batch_size=362, initial num_batches=101): 2945 ms
; Ratio (time for assembling + measure)/(total runtime for 500runs): 0.6181780016792612
; number reverted permutation/ tried permutation: 191 / 257 =74.319%
; number reverted decision/ tried decision: 172 / 244 =70.492%