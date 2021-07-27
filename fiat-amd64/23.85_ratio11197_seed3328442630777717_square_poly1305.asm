SECTION .text
	GLOBAL square_poly1305
square_poly1305:
sub rsp, 0x30 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x0 ], rbx; saving to stack
mov [ rsp + 0x8 ], rbp; saving to stack
mov [ rsp + 0x10 ], r12; saving to stack
mov [ rsp + 0x18 ], r13; saving to stack
mov [ rsp + 0x20 ], r14; saving to stack
mov [ rsp + 0x28 ], r15; saving to stack
imul rax, [ rsi + 0x10 ], 0x5; x1 <- arg1[2] * 0x5
imul r10, rax, 0x2; x2 <- x1 * 0x2
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r11, rbx, [ rsi + 0x0 ]; x16, x15<- arg1[0] * arg1[0]
imul r10, r10, 0x2; x10000 <- x2 * 0x2
mov rdx, r10; x10000 to rdx
mulx rdx, r10, [ rsi + 0x8 ]; x8, x7<- arg1[1] * x10000
test al, al
adox r10, rbx
adox r11, rdx
mov rbp, 0xfffffffffff ; moving imm to reg
mov r12, r10; x22, copying x17 here, cause x17 is needed in a reg for other than x22, namely all: , x22, x21, size: 2
and r12, rbp; x22 <- x17&0xfffffffffff
shrd r10, r11, 44; x21 <- x19||x17 >> 44
mov rdx, rax; x1 to rdx
mulx rdx, rax, [ rsi + 0x10 ]; x6, x5<- arg1[2] * x1
imul r13, [ rsi + 0x8 ], 0x2; x4 <- arg1[1] * 0x2
xchg rdx, r13; x4, swapping with x6, which is currently in rdx
mulx rdx, r14, [ rsi + 0x0 ]; x14, x13<- arg1[0] * x4
xor r15, r15
adox rax, r14
adcx rax, r10
adox rdx, r13
adc rdx, 0x0
mov rcx, rax; x34, copying x31 here, cause x31 is needed in a reg for other than x34, namely all: , x34, x35, size: 2
shrd rcx, rdx, 43; x34 <- x33||x31 >> 43
imul r8, [ rsi + 0x10 ], 0x2; x3 <- arg1[2] * 0x2
imul r9, [ rsi + 0x8 ], 0x2; x10001 <- arg1[1] * 0x2
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r8, rbx, r8; x12, x11<- arg1[0] * x3
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r9, r11, r9; x10, x9<- arg1[1] * x10001
xor rdx, rdx
adox r11, rbx
adcx r11, rcx
adox r8, r9
adc r8, 0x0
mov r15, r11; x39, copying x36 here, cause x36 is needed in a reg for other than x39, namely all: , x40, x39, size: 2
shrd r15, r8, 43; x39 <- x38||x36 >> 43
imul r15, r15, 0x5; x41 <- x39 * 0x5
lea r12, [ r12 + r15 ]
mov r10, r12; x43, copying x42 here, cause x42 is needed in a reg for other than x43, namely all: , x43, x44, size: 2
shr r10, 44; x43 <- x42>> 44
mov r13, 0x7ffffffffff ; moving imm to reg
and rax, r13; x35 <- x31&0x7ffffffffff
lea r10, [ r10 + rax ]
mov r14, r10; x46, copying x45 here, cause x45 is needed in a reg for other than x46, namely all: , x47, x46, size: 2
shr r14, 43; x46 <- x45>> 43
and r11, r13; x40 <- x36&0x7ffffffffff
and r12, rbp; x44 <- x42&0xfffffffffff
lea r14, [ r14 + r11 ]
and r10, r13; x47 <- x45&0x7ffffffffff
mov [ rdi + 0x10 ], r14; out1[2] = x48
mov [ rdi + 0x8 ], r10; out1[1] = x47
mov [ rdi + 0x0 ], r12; out1[0] = x44
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
; first cyclecount 25.84, best 21.517808219178082, lastGood 23.846575342465755
; seed 3328442630777717 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 6088 ms / 500 runs=> 12.176ms/run
; Time spent for assembling and measureing (initial batch_size=371, initial num_batches=101): 4774 ms
; Ratio (time for assembling + measure)/(total runtime for 500runs): 0.7841655716162943
; number reverted permutation/ tried permutation: 228 / 263 =86.692%
; number reverted decision/ tried decision: 182 / 238 =76.471%