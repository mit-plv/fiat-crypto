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
xor rbp, rbp
adox r10, rbx
adox r11, rdx
imul r12, [ rsi + 0x8 ], 0x2; x4 <- arg1[1] * 0x2
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r12, r13, r12; x14, x13<- arg1[0] * x4
mov r14, 0xfffffffffff ; moving imm to reg
mov r15, r10; x22, copying x17 here, cause x17 is needed in a reg for other than x22, namely all: , x21, x22, size: 2
and r15, r14; x22 <- x17&0xfffffffffff
shrd r10, r11, 44; x21 <- x19||x17 >> 44
mov rdx, rax; x1 to rdx
mulx rdx, rax, [ rsi + 0x10 ]; x6, x5<- arg1[2] * x1
xor rcx, rcx
adox rax, r13
adcx rax, r10
adox r12, rdx
adc r12, 0x0
imul rbp, [ rsi + 0x8 ], 0x2; x10001 <- arg1[1] * 0x2
imul r8, [ rsi + 0x10 ], 0x2; x3 <- arg1[2] * 0x2
mov r9, rax; x34, copying x31 here, cause x31 is needed in a reg for other than x34, namely all: , x35, x34, size: 2
shrd r9, r12, 43; x34 <- x33||x31 >> 43
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbp, rbx, rbp; x10, x9<- arg1[1] * x10001
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r8, r11, r8; x12, x11<- arg1[0] * x3
xor rdx, rdx
adox rbx, r11
adox r8, rbp
adcx rbx, r9
adc r8, 0x0
mov rcx, 0x7ffffffffff ; moving imm to reg
and rax, rcx; x35 <- x31&0x7ffffffffff
mov r13, rbx; x39, copying x36 here, cause x36 is needed in a reg for other than x39, namely all: , x40, x39, size: 2
shrd r13, r8, 43; x39 <- x38||x36 >> 43
imul r13, r13, 0x5; x41 <- x39 * 0x5
lea r15, [ r15 + r13 ]
mov r10, r15; x43, copying x42 here, cause x42 is needed in a reg for other than x43, namely all: , x44, x43, size: 2
shr r10, 44; x43 <- x42>> 44
lea r10, [ r10 + rax ]
and r15, r14; x44 <- x42&0xfffffffffff
mov r12, r10; x46, copying x45 here, cause x45 is needed in a reg for other than x46, namely all: , x47, x46, size: 2
shr r12, 43; x46 <- x45>> 43
and rbx, rcx; x40 <- x36&0x7ffffffffff
and r10, rcx; x47 <- x45&0x7ffffffffff
lea r12, [ r12 + rbx ]
mov [ rdi + 0x0 ], r15; out1[0] = x44
mov [ rdi + 0x10 ], r12; out1[2] = x48
mov [ rdi + 0x8 ], r10; out1[1] = x47
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
; first cyclecount 17.135, best 13.883683360258482, lastGood 13.884244372990354
; seed 989931496276831 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 6222 ms / 500 runs=> 12.444ms/run
; Time spent for assembling and measureing (initial batch_size=617, initial num_batches=101): 4946 ms
; Ratio (time for assembling + measure)/(total runtime for 500runs): 0.7949212471873995
; number reverted permutation/ tried permutation: 164 / 242 =67.769%
; number reverted decision/ tried decision: 184 / 259 =71.042%