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
mov r10, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x0 ]; saving arg2[0] in rdx.
mulx r11, rbx, [ rsi + 0x8 ]; x12, x11<- arg1[1] * arg2[0]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rax, rbp, rax; x6, x5<- arg1[1] * x10002
mov rdx, [ r10 + 0x0 ]; arg2[0] to rdx
mulx r12, r13, [ rsi + 0x0 ]; x18, x17<- arg1[0] * arg2[0]
imul r14, [ r10 + 0x8 ], 0xa; x10001 <- arg2[1] * 0xa
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r14, r15, r14; x4, x3<- arg1[2] * x10001
xor rcx, rcx
adox r15, rbp
adox rax, r14
adcx r15, r13
adcx r12, rax
imul r8, [ r10 + 0x10 ], 0x5; x10000 <- arg2[2] * 0x5
mov r9, r15; x27, copying x23 here, cause x23 is needed in a reg for other than x27, namely all: , x27, x28, size: 2
shrd r9, r12, 44; x27 <- x25||x23 >> 44
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rbp, r13, [ r10 + 0x8 ]; x16, x15<- arg1[0] * arg2[1]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r8, r14, r8; x2, x1<- arg1[2] * x10000
add r14, rbx; could be done better, if r0 has been u8 as well
adcx r11, r8
add r14, r13; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rbx, rax, [ r10 + 0x0 ]; x8, x7<- arg1[2] * arg2[0]
adcx rbp, r11
xor r12, r12
adox r14, r9
adox rbp, r12
mov rcx, r14; x48, copying x45 here, cause x45 is needed in a reg for other than x48, namely all: , x48, x49, size: 2
shrd rcx, rbp, 43; x48 <- x47||x45 >> 43
imul r9, [ r10 + 0x8 ], 0x2; x10003 <- arg2[1] * 0x2
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r13, r8, [ r10 + 0x10 ]; x14, x13<- arg1[0] * arg2[2]
mov r11, 0xfffffffffff ; moving imm to reg
and r15, r11; x28 <- x23&0xfffffffffff
mov rdx, r9; x10003 to rdx
mulx rdx, r9, [ rsi + 0x8 ]; x10, x9<- arg1[1] * x10003
adox rax, r9
adox rdx, rbx
adcx rax, r8
adcx r13, rdx
add rax, rcx; could be done better, if r0 has been u8 as well
adc r13, 0x0
mov rbx, rax; x53, copying x50 here, cause x50 is needed in a reg for other than x53, namely all: , x53, x54, size: 2
shrd rbx, r13, 43; x53 <- x52||x50 >> 43
imul rbx, rbx, 0x5; x55 <- x53 * 0x5
lea r15, [ r15 + rbx ]
mov rbp, r15; x58, copying x56 here, cause x56 is needed in a reg for other than x58, namely all: , x57, x58, size: 2
and rbp, r11; x58 <- x56&0xfffffffffff
shr r15, 44; x57 <- x56>> 44
mov [ rdi + 0x0 ], rbp; out1[0] = x58
mov rcx, 0x7ffffffffff ; moving imm to reg
and r14, rcx; x49 <- x45&0x7ffffffffff
lea r15, [ r15 + r14 ]
mov r8, r15; x61, copying x59 here, cause x59 is needed in a reg for other than x61, namely all: , x60, x61, size: 2
and r8, rcx; x61 <- x59&0x7ffffffffff
mov [ rdi + 0x8 ], r8; out1[1] = x61
and rax, rcx; x54 <- x50&0x7ffffffffff
shr r15, 43; x60 <- x59>> 43
lea r15, [ r15 + rax ]
mov [ rdi + 0x10 ], r15; out1[2] = x62
mov rbx, [ rsp + 0x0 ]; restoring from stack
mov rbp, [ rsp + 0x8 ]; restoring from stack
mov r12, [ rsp + 0x10 ]; restoring from stack
mov r13, [ rsp + 0x18 ]; restoring from stack
mov r14, [ rsp + 0x20 ]; restoring from stack
mov r15, [ rsp + 0x28 ]; restoring from stack
add rsp, 0x30 
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; clocked at 2200 MHz
; first cyclecount 22.27, best 17.487571701720842, lastGood 17.713740458015266
; seed 3175310705764234 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1518394 ms / 60000 runs=> 25.306566666666665ms/run
; Time spent for assembling and measureing (initial batch_size=525, initial num_batches=101): 1403430 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.9242857914348976
; number reverted permutation/ tried permutation: 23740 / 29903 =79.390%
; number reverted decision/ tried decision: 19605 / 30098 =65.137%