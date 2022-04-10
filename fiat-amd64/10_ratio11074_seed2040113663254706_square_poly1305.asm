SECTION .text
	GLOBAL square_poly1305
square_poly1305:
sub rsp, 0x30 ; last 0x30 (6) for Caller - save regs 

;instead of 
; mov [ rsp + 0x0 ], rbx; saving to stack

; we also want to use
mov [ rsp ], rbx; saving to stack

mov [ rsp + 0x8 ], rbp; saving to stack
mov [ rsp + 0x10 ], r12; saving to stack
mov [ rsp + 0x18 ], r13; saving to stack
mov [ rsp + 0x20 ], r14; saving to stack
mov [ rsp + 0x28 ], r15; saving to stack

; instead of 
;imul rax, [ rsi + 0x10 ], 0x5; x1 <- arg1[2] * 0x5

; we want also to use 
mov rax, [ rsi + 0x10 ]
lea rax, [ rax + 4 * rax ]

; instead of 
;imul r10, rax, 0x2; x2 <- x1 * 0x2

; we also want to use
lea r10, [ 2 * rax]

mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r11, rbx, [ rsi + 0x0 ]; x16, x15<- arg1[0] * arg1[0]

; instead of 
; imul r10, r10, 0x2; x10000 <- x2 * 0x2

;we want to use 
lea r10, [r10 + r10]

; we also still need to support basic addressing with REG+off
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx

mulx r10, rbp, r10; x8, x7<- arg1[1] * x10000
xor r12, r12
adox rbp, rbx
adox r11, r10
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rax, r13, rax; x6, x5<- arg1[2] * x1
mov r14, 0xfffffffffff ; moving imm to reg
mov r15, rbp; x22, copying x17 here, cause x17 is needed in a reg for other than x22, namely all: , x21, x22, size: 2
and r15, r14; x22 <- x17&0xfffffffffff
imul rdx, [ rsi + 0x8 ], 0x2; x4 <- arg1[1] * 0x2
mulx rdx, rcx, [ rsi + 0x0 ]; x14, x13<- arg1[0] * x4
shrd rbp, r11, 44; x21 <- x19||x17 >> 44
xor r8, r8
adox r13, rcx
adox rdx, rax
adcx r13, rbp
adc rdx, 0x0
imul r12, [ rsi + 0x8 ], 0x2; x10001 <- arg1[1] * 0x2
mov r9, r13; x34, copying x31 here, cause x31 is needed in a reg for other than x34, namely all: , x34, x35, size: 2
shrd r9, rdx, 43; x34 <- x33||x31 >> 43
imul rbx, [ rsi + 0x10 ], 0x2; x3 <- arg1[2] * 0x2
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r12, r10, r12; x10, x9<- arg1[1] * x10001
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rbx, r11, rbx; x12, x11<- arg1[0] * x3
xor rdx, rdx
adox r10, r11
adox rbx, r12
adcx r10, r9
adc rbx, 0x0
mov r8, r10; x39, copying x36 here, cause x36 is needed in a reg for other than x39, namely all: , x39, x40, size: 2
shrd r8, rbx, 43; x39 <- x38||x36 >> 43
imul r8, r8, 0x5; x41 <- x39 * 0x5
mov rax, 0x7ffffffffff ; moving imm to reg
and r13, rax; x35 <- x31&0x7ffffffffff
lea r15, [ r15 + r8 ]
mov rcx, r15; x44, copying x42 here, cause x42 is needed in a reg for other than x44, namely all: , x44, x43, size: 2
and rcx, r14; x44 <- x42&0xfffffffffff
shr r15, 44; x43 <- x42>> 44
lea r15, [ r15 + r13 ]
mov rbp, r15; x47, copying x45 here, cause x45 is needed in a reg for other than x47, namely all: , x47, x46, size: 2
and rbp, rax; x47 <- x45&0x7ffffffffff
shr r15, 43; x46 <- x45>> 43
and r10, rax; x40 <- x36&0x7ffffffffff
mov [ rdi + 0x8 ], rbp; out1[1] = x47
lea r15, [ r15 + r10 ]
mov [ rdi + 0x0 ], rcx; out1[0] = x44
mov [ rdi + 0x10 ], r15; out1[2] = x48
mov rbx, [ rsp + 0x0 ]; restoring from stack
mov rbp, [ rsp + 0x8 ]; restoring from stack
mov r12, [ rsp + 0x10 ]; restoring from stack
mov r13, [ rsp + 0x18 ]; restoring from stack
mov r14, [ rsp + 0x20 ]; restoring from stack
mov r15, [ rsp + 0x28 ]; restoring from stack
add rsp, 0x30 
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; clocked at 1600 MHz
; first cyclecount 15.38, best 10.657863145258103, lastGood 10.66546329723225
; seed 2040113663254706 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 15590 ms / 500 runs=> 31.18ms/run
; Time spent for assembling and measureing (initial batch_size=833, initial num_batches=101): 13489 ms
; Ratio (time for assembling + measure)/(total runtime for 500runs): 0.8652341244387428
; number reverted permutation/ tried permutation: 221 / 270 =81.852%
; number reverted decision/ tried decision: 169 / 231 =73.160%
