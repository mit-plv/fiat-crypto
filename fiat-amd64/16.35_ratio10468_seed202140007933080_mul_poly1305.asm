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
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r10, r11, [ rax + 0x0 ]; x18, x17<- arg1[0] * arg2[0]
imul rbx, [ rax + 0x10 ], 0xa; x10002 <- arg2[2] * 0xa
imul rbp, [ rax + 0x8 ], 0xa; x10001 <- arg2[1] * 0xa
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rbp, r12, rbp; x4, x3<- arg1[2] * x10001
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbx, r13, rbx; x6, x5<- arg1[1] * x10002
xor r14, r14
adox r12, r13
adox rbx, rbp
adcx r12, r11
adcx r10, rbx
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r15, rcx, [ rax + 0x8 ]; x16, x15<- arg1[0] * arg2[1]
mov r8, r12; x27, copying x23 here, cause x23 is needed in a reg for other than x27, namely all: , x27, x28, size: 2
shrd r8, r10, 44; x27 <- x25||x23 >> 44
imul r9, [ rax + 0x10 ], 0x5; x10000 <- arg2[2] * 0x5
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx r11, rbp, [ rsi + 0x8 ]; x12, x11<- arg1[1] * arg2[0]
mov rdx, r9; x10000 to rdx
mulx rdx, r9, [ rsi + 0x10 ]; x2, x1<- arg1[2] * x10000
add r9, rbp; could be done better, if r0 has been u8 as well
adcx r11, rdx
xor r13, r13
adox r9, rcx
adox r15, r11
adcx r9, r8
adc r15, 0x0
mov r14, 0xfffffffffff ; moving imm to reg
and r12, r14; x28 <- x23&0xfffffffffff
imul rbx, [ rax + 0x8 ], 0x2; x10003 <- arg2[1] * 0x2
mov r10, r9; x48, copying x45 here, cause x45 is needed in a reg for other than x48, namely all: , x48, x49, size: 2
shrd r10, r15, 43; x48 <- x47||x45 >> 43
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx rcx, r8, [ rsi + 0x10 ]; x8, x7<- arg1[2] * arg2[0]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rbp, r11, [ rax + 0x10 ]; x14, x13<- arg1[0] * arg2[2]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbx, r15, rbx; x10, x9<- arg1[1] * x10003
test al, al
adox r8, r15
adcx r8, r11
adox rbx, rcx
adcx rbp, rbx
test al, al
adox r8, r10
adox rbp, r13
mov r10, r8; x53, copying x50 here, cause x50 is needed in a reg for other than x53, namely all: , x54, x53, size: 2
shrd r10, rbp, 43; x53 <- x52||x50 >> 43
imul r10, r10, 0x5; x55 <- x53 * 0x5
mov rcx, 0x7ffffffffff ; moving imm to reg
and r9, rcx; x49 <- x45&0x7ffffffffff
lea r12, [ r12 + r10 ]
mov r11, r12; x57, copying x56 here, cause x56 is needed in a reg for other than x57, namely all: , x57, x58, size: 2
shr r11, 44; x57 <- x56>> 44
lea r11, [ r11 + r9 ]
mov r15, r11; x61, copying x59 here, cause x59 is needed in a reg for other than x61, namely all: , x61, x60, size: 2
and r15, rcx; x61 <- x59&0x7ffffffffff
and r8, rcx; x54 <- x50&0x7ffffffffff
shr r11, 43; x60 <- x59>> 43
mov [ rdi + 0x8 ], r15; out1[1] = x61
and r12, r14; x58 <- x56&0xfffffffffff
mov [ rdi + 0x0 ], r12; out1[0] = x58
lea r11, [ r11 + r8 ]
mov [ rdi + 0x10 ], r11; out1[2] = x62
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
; first cyclecount 21.48, best 16.327345309381236, lastGood 16.34623217922607
; seed 202140007933080 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 6538 ms / 500 runs=> 13.076ms/run
; Time spent for assembling and measureing (initial batch_size=492, initial num_batches=101): 4969 ms
; Ratio (time for assembling + measure)/(total runtime for 500runs): 0.7600183542367697
; number reverted permutation/ tried permutation: 162 / 245 =66.122%
; number reverted decision/ tried decision: 170 / 256 =66.406%