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
imul rbx, [ rax + 0x8 ], 0xa; x10001 <- arg2[1] * 0xa
imul rbp, [ rax + 0x10 ], 0xa; x10002 <- arg2[2] * 0xa
mov rdx, rbx; x10001 to rdx
mulx rdx, rbx, [ rsi + 0x10 ]; x4, x3<- arg1[2] * x10001
xchg rdx, rbp; x10002, swapping with x4, which is currently in rdx
mulx rdx, r12, [ rsi + 0x8 ]; x6, x5<- arg1[1] * x10002
test al, al
adox rbx, r12
adcx rbx, r11
adox rdx, rbp
adcx r10, rdx
mov r13, 0xfffffffffff ; moving imm to reg
mov r14, rbx; x28, copying x23 here, cause x23 is needed in a reg for other than x28, namely all: , x28, x27, size: 2
and r14, r13; x28 <- x23&0xfffffffffff
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r15, rcx, [ rax + 0x8 ]; x16, x15<- arg1[0] * arg2[1]
shrd rbx, r10, 44; x27 <- x25||x23 >> 44
imul r8, [ rax + 0x10 ], 0x5; x10000 <- arg2[2] * 0x5
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx r9, r11, [ rsi + 0x8 ]; x12, x11<- arg1[1] * arg2[0]
mov rdx, r8; x10000 to rdx
mulx rdx, r8, [ rsi + 0x10 ]; x2, x1<- arg1[2] * x10000
add r8, r11; could be done better, if r0 has been u8 as well
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, rcx
adcx r9, rdx
adox r15, r9
xor r12, r12
adox r8, rbx
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx rdx, r10, [ rsi + 0x0 ]; x14, x13<- arg1[0] * arg2[2]
adox r15, r12
imul rcx, [ rax + 0x8 ], 0x2; x10003 <- arg2[1] * 0x2
mov rbx, r8; x48, copying x45 here, cause x45 is needed in a reg for other than x48, namely all: , x48, x49, size: 2
shrd rbx, r15, 43; x48 <- x47||x45 >> 43
mov r11, rdx; preserving value of x14 into a new reg
mov rdx, [ rax + 0x0 ]; saving arg2[0] in rdx.
mulx r9, r15, [ rsi + 0x10 ]; x8, x7<- arg1[2] * arg2[0]
mov rdx, rcx; x10003 to rdx
mulx rdx, rcx, [ rsi + 0x8 ]; x10, x9<- arg1[1] * x10003
add r15, rcx; could be done better, if r0 has been u8 as well
adcx rdx, r9
test al, al
adox r15, r10
adox r11, rdx
adcx r15, rbx
adc r11, 0x0
mov r10, r15; x53, copying x50 here, cause x50 is needed in a reg for other than x53, namely all: , x54, x53, size: 2
shrd r10, r11, 43; x53 <- x52||x50 >> 43
imul r10, r10, 0x5; x55 <- x53 * 0x5
lea r14, [ r14 + r10 ]
mov rbx, r14; x57, copying x56 here, cause x56 is needed in a reg for other than x57, namely all: , x58, x57, size: 2
shr rbx, 44; x57 <- x56>> 44
mov r9, 0x7ffffffffff ; moving imm to reg
and r8, r9; x49 <- x45&0x7ffffffffff
lea rbx, [ rbx + r8 ]
mov rcx, rbx; x61, copying x59 here, cause x59 is needed in a reg for other than x61, namely all: , x61, x60, size: 2
and rcx, r9; x61 <- x59&0x7ffffffffff
shr rbx, 43; x60 <- x59>> 43
and r15, r9; x54 <- x50&0x7ffffffffff
mov [ rdi + 0x8 ], rcx; out1[1] = x61
and r14, r13; x58 <- x56&0xfffffffffff
lea rbx, [ rbx + r15 ]
mov [ rdi + 0x10 ], rbx; out1[2] = x62
mov [ rdi + 0x0 ], r14; out1[0] = x58
mov rbx, [ rsp + 0x0 ]; restoring from stack
mov rbp, [ rsp + 0x8 ]; restoring from stack
mov r12, [ rsp + 0x10 ]; restoring from stack
mov r13, [ rsp + 0x18 ]; restoring from stack
mov r14, [ rsp + 0x20 ]; restoring from stack
mov r15, [ rsp + 0x28 ]; restoring from stack
add rsp, 0x30 
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; clocked at 2200 MHz
; first cyclecount 28.12, best 22.515, lastGood 23.085
; seed 2825755522683576 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5423 ms / 500 runs=> 10.846ms/run
; Time spent for assembling and measureing (initial batch_size=398, initial num_batches=101): 4020 ms
; Ratio (time for assembling + measure)/(total runtime for 500runs): 0.7412871104554675
; number reverted permutation/ tried permutation: 201 / 254 =79.134%
; number reverted decision/ tried decision: 166 / 247 =67.206%