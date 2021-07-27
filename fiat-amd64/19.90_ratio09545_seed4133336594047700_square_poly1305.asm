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
mov rdx, rbx; x10000 to rdx
mulx rdx, rbx, [ rsi + 0x8 ]; x8, x7<- arg1[1] * x10000
add rbx, r11; could be done better, if r0 has been u8 as well
adcx r10, rdx
mov rbp, rbx; x21, copying x17 here, cause x17 is needed in a reg for other than x21, namely all: , x21, x22, size: 2
shrd rbp, r10, 44; x21 <- x19||x17 >> 44
imul r12, [ rsi + 0x8 ], 0x2; x4 <- arg1[1] * 0x2
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rax, r13, rax; x6, x5<- arg1[2] * x1
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r12, r14, r12; x14, x13<- arg1[0] * x4
xor r15, r15
adox r13, r14
adcx r13, rbp
adox r12, rax
mov rdx, 0xfffffffffff ; moving imm to reg
setc cl; spill CF x32 to reg (rcx)
and rbx, rdx; x22 <- x17&0xfffffffffff
movzx r8, cl; x33, copying x32 here, cause x32 is needed in a reg for other than x33, namely all: , x33, size: 1
lea r8, [ r8 + r12 ]
mov r9, r13; x34, copying x31 here, cause x31 is needed in a reg for other than x34, namely all: , x34, x35, size: 2
shrd r9, r8, 43; x34 <- x33||x31 >> 43
imul r11, [ rsi + 0x8 ], 0x2; x10001 <- arg1[1] * 0x2
xchg rdx, r11; x10001, swapping with 0xfffffffffff, which is currently in rdx
mulx rdx, r10, [ rsi + 0x8 ]; x10, x9<- arg1[1] * x10001
imul rbp, [ rsi + 0x10 ], 0x2; x3 <- arg1[2] * 0x2
xchg rdx, rbp; x3, swapping with x10, which is currently in rdx
mulx rdx, rax, [ rsi + 0x0 ]; x12, x11<- arg1[0] * x3
test al, al
adox r10, rax
adcx r10, r9
adox rdx, rbp
adc rdx, 0x0
mov r14, r10; x39, copying x36 here, cause x36 is needed in a reg for other than x39, namely all: , x40, x39, size: 2
shrd r14, rdx, 43; x39 <- x38||x36 >> 43
imul r14, r14, 0x5; x41 <- x39 * 0x5
lea rbx, [ rbx + r14 ]
mov rcx, rbx; x43, copying x42 here, cause x42 is needed in a reg for other than x43, namely all: , x44, x43, size: 2
shr rcx, 44; x43 <- x42>> 44
mov r12, 0x7ffffffffff ; moving imm to reg
and r13, r12; x35 <- x31&0x7ffffffffff
lea rcx, [ rcx + r13 ]
and r10, r12; x40 <- x36&0x7ffffffffff
mov r8, rcx; x46, copying x45 here, cause x45 is needed in a reg for other than x46, namely all: , x46, x47, size: 2
shr r8, 43; x46 <- x45>> 43
and rcx, r12; x47 <- x45&0x7ffffffffff
lea r8, [ r8 + r10 ]
and rbx, r11; x44 <- x42&0xfffffffffff
mov [ rdi + 0x0 ], rbx; out1[0] = x44
mov [ rdi + 0x8 ], rcx; out1[1] = x47
mov [ rdi + 0x10 ], r8; out1[2] = x48
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
; first cyclecount 23.75, best 19.866920152091254, lastGood 19.904761904761905
; seed 4133336594047700 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5965 ms / 500 runs=> 11.93ms/run
; Time spent for assembling and measureing (initial batch_size=526, initial num_batches=101): 4674 ms
; Ratio (time for assembling + measure)/(total runtime for 500runs): 0.7835708298407377
; number reverted permutation/ tried permutation: 192 / 247 =77.733%
; number reverted decision/ tried decision: 194 / 254 =76.378%