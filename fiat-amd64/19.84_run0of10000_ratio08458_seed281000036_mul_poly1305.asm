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
mov rdx, rbx; x10002 to rdx
mulx rdx, rbx, [ rsi + 0x8 ]; x6, x5<- arg1[1] * x10002
imul rbp, [ rax + 0x8 ], 0xa; x10001 <- arg2[1] * 0xa
mov r12, rdx; preserving value of x6 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx rbp, r13, rbp; x4, x3<- arg1[2] * x10001
xor r14, r14
adox r13, rbx
adcx r13, r11
mov r15, 0xfffffffffff ; moving imm to reg
setc cl; spill CF x24 to reg (rcx)
seto r8b; spill OF x20 to reg (r8)
mov r9, r13; x28, copying x23 here, cause x23 is needed in a reg for other than x28, namely all: , x27, x28, size: 2
and r9, r15; x28 <- x23&0xfffffffffff
sar  r8b, 1
adcx r12, rbp
sar  cl, 1
adcx r10, r12
shrd r13, r10, 44; x27 <- x25||x23 >> 44
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r11, rbx, [ rax + 0x8 ]; x16, x15<- arg1[0] * arg2[1]
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx rbp, r8, [ rsi + 0x8 ]; x12, x11<- arg1[1] * arg2[0]
imul rcx, [ rax + 0x10 ], 0x5; x10000 <- arg2[2] * 0x5
mov rdx, rcx; x10000 to rdx
mulx rdx, rcx, [ rsi + 0x10 ]; x2, x1<- arg1[2] * x10000
test al, al
adox rcx, r8
adcx rcx, rbx
setc r12b; spill CF x42 to reg (r12)
clc;
adcx rcx, r13
adox rbp, rdx
movzx r12, r12b
lea r11, [ r11 + rbp ]
lea r11, [ r11 + r12 ]
adc r11, 0x0
mov r10, rcx; x48, copying x45 here, cause x45 is needed in a reg for other than x48, namely all: , x49, x48, size: 2
shrd r10, r11, 43; x48 <- x47||x45 >> 43
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx rdx, r13, [ rsi + 0x0 ]; x14, x13<- arg1[0] * arg2[2]
imul rbx, [ rax + 0x8 ], 0x2; x10003 <- arg2[1] * 0x2
mov r8, rdx; preserving value of x14 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx rbx, r12, rbx; x10, x9<- arg1[1] * x10003
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx rbp, r11, [ rsi + 0x10 ]; x8, x7<- arg1[2] * arg2[0]
test al, al
adox r11, r12
adcx r11, r13
seto r13b; spill OF x30 to reg (r13)
mov r12, -0x3 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r11, r10
movzx r13, r13b
lea rbx, [ rbx + rbp ]
lea rbx, [ rbx + r13 ]
adcx r8, rbx
adox r8, r14
mov r10, r11; x53, copying x50 here, cause x50 is needed in a reg for other than x53, namely all: , x54, x53, size: 2
shrd r10, r8, 43; x53 <- x52||x50 >> 43
imul r10, r10, 0x5; x55 <- x53 * 0x5
lea r9, [ r9 + r10 ]
mov rbp, r9; x57, copying x56 here, cause x56 is needed in a reg for other than x57, namely all: , x58, x57, size: 2
shr rbp, 44; x57 <- x56>> 44
mov r13, 0x2b ; moving imm to reg
bzhi rcx, rcx, r13; x49 <- x45 (only least 0x2b bits)
lea rbp, [ rbp + rcx ]
mov rbx, rbp; x60, copying x59 here, cause x59 is needed in a reg for other than x60, namely all: , x60, x61, size: 2
shr rbx, 43; x60 <- x59>> 43
bzhi r11, r11, r13; x54 <- x50 (only least 0x2b bits)
lea rbx, [ rbx + r11 ]
mov r8, 0x2c ; moving imm to reg
bzhi r9, r9, r8; x58 <- x56 (only least 0x2c bits)
mov [ rdi + 0x0 ], r9; out1[0] = x58
mov [ rdi + 0x10 ], rbx; out1[2] = x62
mov r10, 0x7ffffffffff ; moving imm to reg
and rbp, r10; x61 <- x59&0x7ffffffffff
mov [ rdi + 0x8 ], rbp; out1[1] = x61
mov rbx, [ rsp + 0x0 ]; restoring from stack
mov rbp, [ rsp + 0x8 ]; restoring from stack
mov r12, [ rsp + 0x10 ]; restoring from stack
mov r13, [ rsp + 0x18 ]; restoring from stack
mov r14, [ rsp + 0x20 ]; restoring from stack
mov r15, [ rsp + 0x28 ]; restoring from stack
add rsp, 0x30 
ret
; cpu Intel(R) Core(TM) i5-8265U CPU @ 1.60GHz
; clocked at 1800 MHz
; first cyclecount 19.855, best 19.845, lastGood 19.845
; seed 281000036 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 40 ms / 0 runs=> Infinityms/run
; Time spent for assembling and measureing (initial batch_size=596, initial num_batches=101): 6 ms
; Ratio (time for assembling + measure)/(total runtime for 0runs): 0.15
; number reverted permutation/ tried permutation: 0 / 0 =NaN%
; number reverted decision/ tried decision: 0 / 1 =0.000%