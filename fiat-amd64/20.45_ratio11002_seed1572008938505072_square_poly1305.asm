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
xor rbp, rbp
adox rbx, r11
adox r10, rdx
imul r12, [ rsi + 0x8 ], 0x2; x4 <- arg1[1] * 0x2
mov r13, rbx; x21, copying x17 here, cause x17 is needed in a reg for other than x21, namely all: , x22, x21, size: 2
shrd r13, r10, 44; x21 <- x19||x17 >> 44
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rax, r14, rax; x6, x5<- arg1[2] * x1
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r12, r15, r12; x14, x13<- arg1[0] * x4
xor rdx, rdx
adox r14, r15
adcx r14, r13
adox r12, rax
adc r12, 0x0
mov rbp, r14; x34, copying x31 here, cause x31 is needed in a reg for other than x34, namely all: , x34, x35, size: 2
shrd rbp, r12, 43; x34 <- x33||x31 >> 43
imul rcx, [ rsi + 0x8 ], 0x2; x10001 <- arg1[1] * 0x2
mov r8, 0xfffffffffff ; moving imm to reg
and rbx, r8; x22 <- x17&0xfffffffffff
imul r9, [ rsi + 0x10 ], 0x2; x3 <- arg1[2] * 0x2
mov r11, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx rcx, r10, rcx; x10, x9<- arg1[1] * x10001
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r9, r13, r9; x12, x11<- arg1[0] * x3
add r10, r13; could be done better, if r0 has been u8 as well
adcx r9, rcx
xor rdx, rdx
adox r10, rbp
adox r9, rdx
mov r11, r10; x39, copying x36 here, cause x36 is needed in a reg for other than x39, namely all: , x40, x39, size: 2
shrd r11, r9, 43; x39 <- x38||x36 >> 43
imul r11, r11, 0x5; x41 <- x39 * 0x5
lea rbx, [ rbx + r11 ]
mov rax, rbx; x43, copying x42 here, cause x42 is needed in a reg for other than x43, namely all: , x43, x44, size: 2
shr rax, 44; x43 <- x42>> 44
mov r15, 0x7ffffffffff ; moving imm to reg
and r14, r15; x35 <- x31&0x7ffffffffff
and r10, r15; x40 <- x36&0x7ffffffffff
lea rax, [ rax + r14 ]
and rbx, r8; x44 <- x42&0xfffffffffff
mov r12, rax; x46, copying x45 here, cause x45 is needed in a reg for other than x46, namely all: , x46, x47, size: 2
shr r12, 43; x46 <- x45>> 43
lea r12, [ r12 + r10 ]
mov [ rdi + 0x10 ], r12; out1[2] = x48
mov [ rdi + 0x0 ], rbx; out1[0] = x44
and rax, r15; x47 <- x45&0x7ffffffffff
mov [ rdi + 0x8 ], rax; out1[1] = x47
mov rbx, [ rsp + 0x0 ]; restoring from stack
mov rbp, [ rsp + 0x8 ]; restoring from stack
mov r12, [ rsp + 0x10 ]; restoring from stack
mov r13, [ rsp + 0x18 ]; restoring from stack
mov r14, [ rsp + 0x20 ]; restoring from stack
mov r15, [ rsp + 0x28 ]; restoring from stack
add rsp, 0x30 
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; clocked at 4799 MHz
; first cyclecount 26.79, best 20.42247191011236, lastGood 20.44943820224719
; seed 1572008938505072 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5102 ms / 500 runs=> 10.204ms/run
; Time spent for assembling and measureing (initial batch_size=445, initial num_batches=101): 3709 ms
; Ratio (time for assembling + measure)/(total runtime for 500runs): 0.726969815758526
; number reverted permutation/ tried permutation: 190 / 252 =75.397%
; number reverted decision/ tried decision: 183 / 249 =73.494%