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
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r10, r11, [ rsi + 0x0 ]; x16, x15<- arg1[0] * arg1[0]
imul rbx, rax, 0x2; x2 <- x1 * 0x2
imul rbx, rbx, 0x2; x10000 <- x2 * 0x2
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbx, rbp, rbx; x8, x7<- arg1[1] * x10000
add rbp, r11; could be done better, if r0 has been u8 as well
adcx r10, rbx
mov r12, rbp; x21, copying x17 here, cause x17 is needed in a reg for other than x21, namely all: , x22, x21, size: 2
shrd r12, r10, 44; x21 <- x19||x17 >> 44
mov r13, 0xfffffffffff ; moving imm to reg
and rbp, r13; x22 <- x17&0xfffffffffff
imul r14, [ rsi + 0x8 ], 0x2; x4 <- arg1[1] * 0x2
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rax, r15, rax; x6, x5<- arg1[2] * x1
mov rdx, r14; x4 to rdx
mulx rdx, r14, [ rsi + 0x0 ]; x14, x13<- arg1[0] * x4
xor rcx, rcx
adox r15, r14
adox rdx, rax
adcx r15, r12
adc rdx, 0x0
mov r8, r15; x34, copying x31 here, cause x31 is needed in a reg for other than x34, namely all: , x34, x35, size: 2
shrd r8, rdx, 43; x34 <- x33||x31 >> 43
imul r9, [ rsi + 0x10 ], 0x2; x3 <- arg1[2] * 0x2
imul r11, [ rsi + 0x8 ], 0x2; x10001 <- arg1[1] * 0x2
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r11, rbx, r11; x10, x9<- arg1[1] * x10001
mov rdx, r9; x3 to rdx
mulx rdx, r9, [ rsi + 0x0 ]; x12, x11<- arg1[0] * x3
xor r10, r10
adox rbx, r9
adcx rbx, r8
adox rdx, r11
adc rdx, 0x0
mov rcx, rbx; x39, copying x36 here, cause x36 is needed in a reg for other than x39, namely all: , x39, x40, size: 2
shrd rcx, rdx, 43; x39 <- x38||x36 >> 43
imul rcx, rcx, 0x5; x41 <- x39 * 0x5
lea rbp, [ rbp + rcx ]
mov r12, rbp; x43, copying x42 here, cause x42 is needed in a reg for other than x43, namely all: , x43, x44, size: 2
shr r12, 44; x43 <- x42>> 44
mov rax, 0x7ffffffffff ; moving imm to reg
and r15, rax; x35 <- x31&0x7ffffffffff
and rbx, rax; x40 <- x36&0x7ffffffffff
lea r12, [ r12 + r15 ]
mov r14, r12; x46, copying x45 here, cause x45 is needed in a reg for other than x46, namely all: , x46, x47, size: 2
shr r14, 43; x46 <- x45>> 43
lea r14, [ r14 + rbx ]
mov [ rdi + 0x10 ], r14; out1[2] = x48
and rbp, r13; x44 <- x42&0xfffffffffff
and r12, rax; x47 <- x45&0x7ffffffffff
mov [ rdi + 0x0 ], rbp; out1[0] = x44
mov [ rdi + 0x8 ], r12; out1[1] = x47
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
; first cyclecount 35.34, best 32.4180790960452, lastGood 33.706214689265536
; seed 267833281830466 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4098 ms / 500 runs=> 8.196ms/run
; Time spent for assembling and measureing (initial batch_size=177, initial num_batches=101): 2292 ms
; Ratio (time for assembling + measure)/(total runtime for 500runs): 0.5592972181551976
; number reverted permutation/ tried permutation: 217 / 255 =85.098%
; number reverted decision/ tried decision: 185 / 246 =75.203%