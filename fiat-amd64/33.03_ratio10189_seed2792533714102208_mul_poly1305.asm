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
mulx r11, rbx, [ rsi + 0x0 ]; x18, x17<- arg1[0] * arg2[0]
imul rbp, [ r10 + 0x8 ], 0xa; x10001 <- arg2[1] * 0xa
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rax, r12, rax; x6, x5<- arg1[1] * x10002
mov rdx, rbp; x10001 to rdx
mulx rdx, rbp, [ rsi + 0x10 ]; x4, x3<- arg1[2] * x10001
xor r13, r13
adox rbp, r12
adcx rbp, rbx
adox rax, rdx
adcx r11, rax
imul r14, [ r10 + 0x10 ], 0x5; x10000 <- arg2[2] * 0x5
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r15, rcx, [ r10 + 0x8 ]; x16, x15<- arg1[0] * arg2[1]
mov r8, rbp; x27, copying x23 here, cause x23 is needed in a reg for other than x27, namely all: , x27, x28, size: 2
shrd r8, r11, 44; x27 <- x25||x23 >> 44
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r14, r9, r14; x2, x1<- arg1[2] * x10000
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbx, r12, [ r10 + 0x0 ]; x12, x11<- arg1[1] * arg2[0]
add r9, r12; could be done better, if r0 has been u8 as well
mov rax, -0x3 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r9, rcx
adcx rbx, r14
clc;
adcx r9, r8
adox r15, rbx
adc r15, 0x0
mov r11, 0xfffffffffff ; moving imm to reg
and rbp, r11; x28 <- x23&0xfffffffffff
mov rcx, r9; x48, copying x45 here, cause x45 is needed in a reg for other than x48, namely all: , x48, x49, size: 2
shrd rcx, r15, 43; x48 <- x47||x45 >> 43
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r8, r14, [ r10 + 0x10 ]; x14, x13<- arg1[0] * arg2[2]
imul r12, [ r10 + 0x8 ], 0x2; x10003 <- arg2[1] * 0x2
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rbx, r15, [ r10 + 0x0 ]; x8, x7<- arg1[2] * arg2[0]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r12, r13, r12; x10, x9<- arg1[1] * x10003
test al, al
adox r15, r13
adox r12, rbx
adcx r15, r14
adcx r8, r12
test al, al
adox r15, rcx
mov rcx, 0x0 ; moving imm to reg
adox r8, rcx
mov r14, r15; x53, copying x50 here, cause x50 is needed in a reg for other than x53, namely all: , x53, x54, size: 2
shrd r14, r8, 43; x53 <- x52||x50 >> 43
imul r14, r14, 0x5; x55 <- x53 * 0x5
lea rbp, [ rbp + r14 ]
mov rbx, rbp; x57, copying x56 here, cause x56 is needed in a reg for other than x57, namely all: , x57, x58, size: 2
shr rbx, 44; x57 <- x56>> 44
mov r13, 0x7ffffffffff ; moving imm to reg
and r9, r13; x49 <- x45&0x7ffffffffff
lea rbx, [ rbx + r9 ]
and r15, r13; x54 <- x50&0x7ffffffffff
mov r12, rbx; x60, copying x59 here, cause x59 is needed in a reg for other than x60, namely all: , x60, x61, size: 2
shr r12, 43; x60 <- x59>> 43
and rbx, r13; x61 <- x59&0x7ffffffffff
lea r12, [ r12 + r15 ]
mov [ rdi + 0x8 ], rbx; out1[1] = x61
and rbp, r11; x58 <- x56&0xfffffffffff
mov [ rdi + 0x10 ], r12; out1[2] = x62
mov [ rdi + 0x0 ], rbp; out1[0] = x58
mov rbx, [ rsp + 0x0 ]; restoring from stack
mov rbp, [ rsp + 0x8 ]; restoring from stack
mov r12, [ rsp + 0x10 ]; restoring from stack
mov r13, [ rsp + 0x18 ]; restoring from stack
mov r14, [ rsp + 0x20 ]; restoring from stack
mov r15, [ rsp + 0x28 ]; restoring from stack
add rsp, 0x30 
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; clocked at 2200 MHz
; first cyclecount 40.47, best 33.02684563758389, lastGood 33.02684563758389
; seed 2792533714102208 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 7804 ms / 500 runs=> 15.608ms/run
; Time spent for assembling and measureing (initial batch_size=298, initial num_batches=101): 5320 ms
; Ratio (time for assembling + measure)/(total runtime for 500runs): 0.681701691440287
; number reverted permutation/ tried permutation: 202 / 248 =81.452%
; number reverted decision/ tried decision: 153 / 253 =60.474%