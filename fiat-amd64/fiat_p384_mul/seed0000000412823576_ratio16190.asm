SECTION .text
	GLOBAL fiat_p384_mul
fiat_p384_mul:
sub rsp, 360
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x28 ]
mov rdx, [ rax + 0x18 ]
mulx r8, rcx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x28 ]
test al, al
adox rbp, r11
adox r15, r12
adox rcx, rdi
mov rdx, [ rsi + 0x10 ]
mulx r12, r11, [ rax + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], rcx
mulx rcx, rdi, [ rax + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x40 ], r15
mov [ rsp - 0x38 ], rbp
mulx rbp, r15, [ rax + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x30 ], r10
mov [ rsp - 0x28 ], r15
mulx r15, r10, [ rax + 0x20 ]
adcx rdi, rbp
adcx r11, rcx
adox r10, r8
mov rdx, [ rax + 0x10 ]
mulx rcx, r8, [ rsi + 0x20 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x20 ], r10
mulx r10, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x18 ], r11
mov [ rsp - 0x10 ], rdi
mulx rdi, r11, [ rax + 0x28 ]
adcx rbp, r12
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x8 ], rbp
mulx rbp, r12, [ rsi + 0x10 ]
adcx r12, r10
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x0 ], r12
mulx r12, r10, [ rax + 0x28 ]
adcx r10, rbp
adox r11, r15
mov rdx, [ rax + 0x8 ]
mulx rbp, r15, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x8 ], r11
mov [ rsp + 0x10 ], r10
mulx r10, r11, [ rax + 0x10 ]
mov rdx, 0x0 
adox rdi, rdx
adc r12, 0x0
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x18 ], rdi
mov [ rsp + 0x20 ], r12
mulx r12, rdi, [ rax + 0x18 ]
xor rdx, rdx
adox r15, rbx
adox r11, rbp
mov rdx, [ rax + 0x0 ]
mulx rbp, rbx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x28 ], rbx
mov [ rsp + 0x30 ], r11
mulx r11, rbx, [ rax + 0x8 ]
adox rdi, r10
adcx rbx, rbp
mov rdx, [ rax + 0x18 ]
mulx rbp, r10, [ rsi + 0x18 ]
adcx r13, r11
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x38 ], r13
mulx r13, r11, [ rax + 0x20 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x40 ], rbx
mov [ rsp + 0x48 ], rdi
mulx rdi, rbx, [ rsi + 0x8 ]
adcx r10, r14
adcx r11, rbp
mov rdx, [ rax + 0x0 ]
mulx rbp, r14, [ rsi + 0x0 ]
mov rdx, 0x100000001 
mov [ rsp + 0x50 ], r11
mov [ rsp + 0x58 ], r10
mulx r10, r11, r14
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x60 ], r15
mulx r15, r10, [ rsi + 0x8 ]
adox r10, r12
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x68 ], r10
mulx r10, r12, [ rsi + 0x18 ]
adcx r12, r13
adox rbx, r15
mov rdx, 0x0 
adcx r10, rdx
mov rdx, [ rax + 0x0 ]
mulx r15, r13, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x70 ], r13
mov [ rsp + 0x78 ], r10
mulx r10, r13, [ rax + 0x8 ]
mov rdx, 0x0 
adox rdi, rdx
mov [ rsp + 0x80 ], r12
xor r12, r12
adox r13, r15
adox r8, r10
mov rdx, [ rsi + 0x0 ]
mulx r10, r15, [ rax + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x88 ], r8
mulx r8, r12, [ rax + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x90 ], r13
mov [ rsp + 0x98 ], rdi
mulx rdi, r13, [ rax + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xa0 ], rbx
mov [ rsp + 0xa8 ], r9
mulx r9, rbx, [ rax + 0x18 ]
adcx r13, rbp
adcx r15, rdi
mov rdx, [ rax + 0x20 ]
mulx rdi, rbp, [ rsi + 0x20 ]
adox r12, rcx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xb0 ], r12
mulx r12, rcx, [ rax + 0x28 ]
adox rbp, r8
adox rcx, rdi
adcx rbx, r10
mov rdx, [ rsi + 0x0 ]
mulx r8, r10, [ rax + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xb8 ], rcx
mulx rcx, rdi, [ rax + 0x20 ]
adcx rdi, r9
mov rdx, 0xffffffff 
mov [ rsp + 0xc0 ], rbp
mulx rbp, r9, r11
mov rdx, 0x0 
adox r12, rdx
adcx r10, rcx
adc r8, 0x0
mov rcx, 0xfffffffffffffffe 
mov rdx, r11
mov [ rsp + 0xc8 ], r12
mulx r12, r11, rcx
test al, al
adox r9, r14
mov r9, 0xffffffff00000000 
mulx rcx, r14, r9
adcx r14, rbp
adox r14, r13
adcx r11, rcx
adox r11, r15
mov r13, 0xffffffffffffffff 
mulx rbp, r15, r13
mov rdx, r15
adcx rdx, r12
adox rdx, rbx
mov rbx, r15
adcx rbx, rbp
adox rbx, rdi
adcx r15, rbp
adox r15, r10
mov rdi, 0x0 
adcx rbp, rdi
clc
adcx r14, [ rsp + 0xa8 ]
adcx r11, [ rsp + 0x60 ]
mov r10, 0x100000001 
xchg rdx, r10
mulx rcx, r12, r14
mov rcx, 0xffffffff 
mov rdx, r12
mulx rdi, r12, rcx
adcx r10, [ rsp + 0x30 ]
adcx rbx, [ rsp + 0x48 ]
adcx r15, [ rsp + 0x68 ]
mulx rcx, r13, r9
adox rbp, r8
seto r8b
mov r9, -0x2 
inc r9
adox r13, rdi
adcx rbp, [ rsp + 0xa0 ]
setc dil
clc
adcx r12, r14
adcx r13, r11
mov r12, 0xfffffffffffffffe 
mulx r11, r14, r12
adox r14, rcx
mov rcx, 0xffffffffffffffff 
mulx r12, r9, rcx
mov rdx, r9
adox rdx, r11
adcx r14, r10
adcx rdx, rbx
mov r10, r9
adox r10, r12
adox r9, r12
adcx r10, r15
mov rbx, 0x0 
adox r12, rbx
mov r15, -0x3 
inc r15
adox r13, [ rsp - 0x28 ]
adox r14, [ rsp - 0x10 ]
mov r11, 0x100000001 
xchg rdx, r11
mulx r15, rbx, r13
adcx r9, rbp
adox r11, [ rsp - 0x18 ]
adox r10, [ rsp - 0x8 ]
adox r9, [ rsp + 0x0 ]
movzx r15, r8b
seto bpl
mov rcx, 0x0 
dec rcx
movzx rdi, dil
adox rdi, rcx
adox r15, [ rsp + 0x98 ]
adcx r12, r15
seto r8b
adc r8b, 0x0
movzx r8, r8b
mov rdi, 0xffffffff 
mov rdx, rbx
mulx r15, rbx, rdi
adox rbx, r13
mov rbx, 0xffffffff00000000 
mulx rcx, r13, rbx
adcx r13, r15
adox r13, r14
mov r14, 0xfffffffffffffffe 
mulx rbx, r15, r14
adcx r15, rcx
adox r15, r11
mov r11, 0xffffffffffffffff 
mulx r14, rcx, r11
mov rdx, rcx
adcx rdx, rbx
adox rdx, r10
mov r10, rcx
adcx r10, r14
adcx rcx, r14
adox r10, r9
setc r9b
clc
adcx r13, [ rsp + 0x28 ]
adcx r15, [ rsp + 0x40 ]
setc bl
clc
mov r11, -0x1 
movzx rbp, bpl
adcx rbp, r11
adcx r12, [ rsp + 0x10 ]
adox rcx, r12
movzx r8, r8b
movzx rbp, r8b
adcx rbp, [ rsp + 0x20 ]
movzx r8, r9b
lea r8, [ r8 + r14 ]
adox r8, rbp
mov r14, 0x100000001 
xchg rdx, r14
mulx r12, r9, r13
mov rdx, r9
mulx r12, r9, rdi
seto bpl
adc bpl, 0x0
movzx rbp, bpl
add bl, 0x7F
adox r14, [ rsp + 0x38 ]
adox r10, [ rsp + 0x58 ]
adox rcx, [ rsp + 0x50 ]
adox r8, [ rsp + 0x80 ]
adcx r9, r13
mov r9, 0xffffffff00000000 
mulx rbx, r13, r9
movzx rbp, bpl
movzx r11, bpl
adox r11, [ rsp + 0x78 ]
seto bpl
mov r9, -0x2 
inc r9
adox r13, r12
mov r12, 0xfffffffffffffffe 
mulx rdi, r9, r12
adcx r13, r15
adox r9, rbx
mov r15, 0xffffffffffffffff 
mulx r12, rbx, r15
mov rdx, rbx
adox rdx, rdi
mov rdi, rbx
adox rdi, r12
adox rbx, r12
adcx r9, r14
adcx rdx, r10
mov r14, 0x0 
adox r12, r14
adcx rdi, rcx
adcx rbx, r8
adcx r12, r11
movzx r10, bpl
adc r10, 0x0
test al, al
adox r13, [ rsp + 0x70 ]
mov rcx, 0x100000001 
xchg rdx, rcx
mulx rbp, r8, r13
mov rbp, 0xffffffff00000000 
mov rdx, r8
mulx r11, r8, rbp
mov r14, 0xffffffff 
mulx rbp, r15, r14
adox r9, [ rsp + 0x90 ]
adox rcx, [ rsp + 0x88 ]
adcx r15, r13
adox rdi, [ rsp + 0xb0 ]
adox rbx, [ rsp + 0xc0 ]
adox r12, [ rsp + 0xb8 ]
adox r10, [ rsp + 0xc8 ]
seto r15b
mov r13, -0x2 
inc r13
adox r8, rbp
mov rbp, 0xfffffffffffffffe 
mulx r14, r13, rbp
adox r13, r11
adcx r8, r9
adcx r13, rcx
mov r11, 0xffffffffffffffff 
mulx rcx, r9, r11
mov rdx, r9
adox rdx, r14
mov r14, r9
adox r14, rcx
adox r9, rcx
adcx rdx, rdi
mov rdi, 0x0 
adox rcx, rdi
mov r11, -0x3 
inc r11
adox r8, [ rsp - 0x30 ]
mov rdi, 0x100000001 
xchg rdx, rdi
mulx rbp, r11, r8
adcx r14, rbx
adcx r9, r12
adcx rcx, r10
mov rbp, 0xffffffff 
mov rdx, rbp
mulx rbx, rbp, r11
movzx r12, r15b
mov r10, 0x0 
adcx r12, r10
adox r13, [ rsp - 0x38 ]
mov r15, 0xfffffffffffffffe 
mov rdx, r11
mulx r10, r11, r15
adox rdi, [ rsp - 0x40 ]
adox r14, [ rsp - 0x48 ]
mov r15, 0xffffffff00000000 
mov [ rsp + 0xd0 ], r14
mov [ rsp + 0xd8 ], rdi
mulx rdi, r14, r15
adox r9, [ rsp - 0x20 ]
adox rcx, [ rsp + 0x8 ]
adox r12, [ rsp + 0x18 ]
clc
adcx r14, rbx
adcx r11, rdi
mov rbx, 0xffffffffffffffff 
mulx r15, rdi, rbx
mov rdx, rdi
adcx rdx, r10
mov r10, rdi
adcx r10, r15
adcx rdi, r15
mov rbx, 0x0 
adcx r15, rbx
clc
adcx rbp, r8
adcx r14, r13
adcx r11, [ rsp + 0xd8 ]
adcx rdx, [ rsp + 0xd0 ]
adcx r10, r9
adcx rdi, rcx
adcx r15, r12
seto bpl
adc bpl, 0x0
movzx rbp, bpl
mov r8, r14
mov r13, 0xffffffff 
sub r8, r13
mov r9, r11
mov rcx, 0xffffffff00000000 
sbb r9, rcx
mov r12, rdx
mov rbx, 0xfffffffffffffffe 
sbb r12, rbx
mov rcx, r10
mov rbx, 0xffffffffffffffff 
sbb rcx, rbx
mov r13, rdi
sbb r13, rbx
mov [ rsp + 0xe0 ], r8
mov r8, r15
sbb r8, rbx
movzx rbx, bpl
sbb rbx, 0x00000000
cmovc r13, rdi
cmovc r9, r11
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x20 ], r13
cmovc r8, r15
cmovc rcx, r10
mov [ rbx + 0x28 ], r8
mov [ rbx + 0x18 ], rcx
cmovc r12, rdx
mov [ rbx + 0x10 ], r12
mov [ rbx + 0x8 ], r9
mov r11, [ rsp + 0xe0 ]
cmovc r11, r14
mov [ rbx + 0x0 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 360
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.6190
; seed 3738027071457832 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 6812921 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=43, initial num_batches=31): 190105 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.027903596709840023
; number reverted permutation / tried permutation: 72207 / 90254 =80.004%
; number reverted decision / tried decision: 62413 / 89745 =69.545%
; validated in 46.711s
