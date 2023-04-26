SECTION .text
	GLOBAL fiat_p384_mul
fiat_p384_mul:
sub rsp, 584
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rax + 0x20 ]
mulx r8, rcx, [ rsi + 0x8 ]
mov rdx, 0x100000001 
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, r10
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x8 ]
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, r9
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r8
mulx r8, rdi, [ rax + 0x0 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x40 ], rdi
mov [ rsp - 0x38 ], r8
mulx r8, rdi, [ rsi + 0x28 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x30 ], r8
mov [ rsp - 0x28 ], rdi
mulx rdi, r8, [ rsi + 0x20 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x20 ], rdi
mov [ rsp - 0x18 ], r8
mulx r8, rdi, r9
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x10 ], rcx
mov [ rsp - 0x8 ], r13
mulx r13, rcx, [ rsi + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x0 ], r13
mov [ rsp + 0x8 ], rcx
mulx rcx, r13, [ rsi + 0x20 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x10 ], rcx
mov [ rsp + 0x18 ], r13
mulx r13, rcx, [ rsi + 0x10 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x20 ], r13
mov [ rsp + 0x28 ], r12
mulx r12, r13, r9
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x30 ], rcx
mov [ rsp + 0x38 ], rbp
mulx rbp, rcx, r9
xor r9, r9
adox r13, r10
mov rdx, [ rax + 0x20 ]
mulx r10, r13, [ rsi + 0x28 ]
adcx r14, r12
adcx rcx, r15
mov rdx, rdi
adcx rdx, rbp
mov r15, rdi
adcx r15, r8
mov r12, rdx
mov rdx, [ rsi + 0x0 ]
mulx r9, rbp, [ rax + 0x18 ]
adcx rdi, r8
mov rdx, 0x0 
adcx r8, rdx
clc
adcx rbx, r11
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x40 ], r10
mulx r10, r11, [ rsi + 0x0 ]
adcx r11, [ rsp + 0x38 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x48 ], r13
mov [ rsp + 0x50 ], r8
mulx r8, r13, [ rax + 0x10 ]
adox r14, rbx
adcx rbp, r10
mov rdx, [ rsi + 0x0 ]
mulx r10, rbx, [ rax + 0x28 ]
adox rcx, r11
adox r12, rbp
mov rdx, [ rax + 0x20 ]
mulx rbp, r11, [ rsi + 0x0 ]
adcx r11, r9
adox r15, r11
adcx rbx, rbp
mov rdx, [ rsi + 0x18 ]
mulx rbp, r9, [ rax + 0x8 ]
adox rdi, rbx
mov rdx, [ rax + 0x0 ]
mulx rbx, r11, [ rsi + 0x18 ]
mov rdx, 0x0 
adcx r10, rdx
clc
adcx r9, rbx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x58 ], r8
mulx r8, rbx, [ rax + 0x10 ]
adcx rbx, rbp
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x60 ], r13
mulx r13, rbp, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x68 ], rbx
mov [ rsp + 0x70 ], r9
mulx r9, rbx, [ rax + 0x20 ]
adcx rbp, r8
adcx rbx, r13
mov rdx, [ rsi + 0x10 ]
mulx r13, r8, [ rax + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x78 ], rbx
mov [ rsp + 0x80 ], rbp
mulx rbp, rbx, [ rax + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x88 ], r11
mov [ rsp + 0x90 ], r8
mulx r8, r11, [ rax + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x98 ], rdi
mov [ rsp + 0xa0 ], r15
mulx r15, rdi, [ rax + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xa8 ], r12
mov [ rsp + 0xb0 ], rcx
mulx rcx, r12, [ rax + 0x8 ]
adcx rbx, r9
adox r10, [ rsp + 0x50 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0xb8 ], rbx
mulx rbx, r9, [ rsi + 0x8 ]
setc dl
clc
adcx r12, r13
seto r13b
mov [ rsp + 0xc0 ], r12
mov r12, -0x2 
inc r12
adox r11, rbx
mov bl, dl
mov rdx, [ rax + 0x10 ]
mov byte [ rsp + 0xc8 ], r13b
mulx r13, r12, [ rsi + 0x8 ]
adcx rdi, rcx
adcx r15, [ rsp + 0x30 ]
adox r12, r8
adox r13, [ rsp + 0x28 ]
mov rdx, [ rax + 0x28 ]
mulx rcx, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xd0 ], r15
mov [ rsp + 0xd8 ], rdi
mulx rdi, r15, [ rax + 0x20 ]
adcx r15, [ rsp + 0x20 ]
adcx r8, rdi
mov rdx, [ rsp - 0x8 ]
adox rdx, [ rsp - 0x10 ]
mov rdi, 0x0 
adcx rcx, rdi
clc
adcx r9, r14
movzx r14, bl
lea r14, [ r14 + rbp ]
mov rbp, [ rsp + 0x8 ]
adox rbp, [ rsp - 0x48 ]
mov rbx, 0x100000001 
xchg rdx, rbx
mov [ rsp + 0xe0 ], r14
mulx r14, rdi, r9
mov r14, 0xffffffff00000000 
mov rdx, r14
mov [ rsp + 0xe8 ], rcx
mulx rcx, r14, rdi
adcx r11, [ rsp + 0xb0 ]
adcx r12, [ rsp + 0xa8 ]
adcx r13, [ rsp + 0xa0 ]
adcx rbx, [ rsp + 0x98 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0xf0 ], r8
mov [ rsp + 0xf8 ], r15
mulx r15, r8, rdi
mov rdx, [ rsp + 0x0 ]
mov [ rsp + 0x100 ], rbx
mov rbx, 0x0 
adox rdx, rbx
adcx rbp, r10
mov r10, 0xfffffffffffffffe 
xchg rdx, rdi
mov [ rsp + 0x108 ], rbp
mulx rbp, rbx, r10
movzx r10, byte [ rsp + 0xc8 ]
adcx r10, rdi
mov rdi, 0xffffffff 
mov [ rsp + 0x110 ], r10
mov [ rsp + 0x118 ], r13
mulx r13, r10, rdi
mov rdx, -0x2 
inc rdx
adox r14, r13
adox rbx, rcx
mov rcx, r8
adox rcx, rbp
mov rbp, r8
adox rbp, r15
adox r8, r15
setc r13b
clc
adcx r10, r9
adcx r14, r11
mov r10, 0x0 
adox r15, r10
adcx rbx, r12
mov r9, -0x3 
inc r9
adox r14, [ rsp + 0x90 ]
adcx rcx, [ rsp + 0x118 ]
mov r11, 0x100000001 
mov rdx, r14
mulx r12, r14, r11
xchg rdx, r14
mulx r10, r12, rdi
adcx rbp, [ rsp + 0x100 ]
adcx r8, [ rsp + 0x108 ]
adcx r15, [ rsp + 0x110 ]
mov r9, 0xffffffff00000000 
mulx r11, rdi, r9
movzx r9, r13b
mov [ rsp + 0x120 ], r12
mov r12, 0x0 
adcx r9, r12
adox rbx, [ rsp + 0xc0 ]
mov r13, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x128 ], rbx
mulx rbx, r12, [ rax + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x130 ], rbx
mov [ rsp + 0x138 ], r12
mulx r12, rbx, [ rax + 0x8 ]
adox rcx, [ rsp + 0xd8 ]
adox rbp, [ rsp + 0xd0 ]
adox r8, [ rsp + 0xf8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x140 ], r8
mov [ rsp + 0x148 ], rbp
mulx rbp, r8, [ rax + 0x0 ]
adox r15, [ rsp + 0xf0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x150 ], r8
mov [ rsp + 0x158 ], r15
mulx r15, r8, [ rax + 0x18 ]
adox r9, [ rsp + 0xe8 ]
clc
adcx rdi, r10
seto dl
mov r10, -0x2 
inc r10
adox rbx, rbp
mov rbp, 0xfffffffffffffffe 
xchg rdx, r13
mov [ rsp + 0x160 ], rbx
mulx rbx, r10, rbp
adcx r10, r11
adox r12, [ rsp + 0x138 ]
adox r8, [ rsp + 0x130 ]
adox r15, [ rsp + 0x48 ]
mov r11, [ rsp + 0x40 ]
adox r11, [ rsp - 0x28 ]
mov rbp, 0xffffffffffffffff 
mov [ rsp + 0x168 ], r11
mov [ rsp + 0x170 ], r15
mulx r15, r11, rbp
mov rdx, r11
adcx rdx, rbx
mov rbx, [ rsp - 0x30 ]
mov rbp, 0x0 
adox rbx, rbp
mov [ rsp + 0x178 ], rbx
mov rbx, -0x3 
inc rbx
adox r14, [ rsp + 0x120 ]
adox rdi, [ rsp + 0x128 ]
adox r10, rcx
mov r14, r11
adcx r14, r15
adcx r11, r15
adox rdx, [ rsp + 0x148 ]
adcx r15, rbp
clc
adcx rdi, [ rsp + 0x88 ]
mov rcx, 0x100000001 
xchg rdx, rdi
mulx rbx, rbp, rcx
adcx r10, [ rsp + 0x70 ]
adcx rdi, [ rsp + 0x68 ]
mov rbx, 0xffffffff 
xchg rdx, rbp
mov [ rsp + 0x180 ], r8
mulx r8, rcx, rbx
adox r14, [ rsp + 0x140 ]
adox r11, [ rsp + 0x158 ]
adcx r14, [ rsp + 0x80 ]
adox r15, r9
adcx r11, [ rsp + 0x78 ]
adcx r15, [ rsp + 0xb8 ]
seto r9b
mov rbx, -0x2 
inc rbx
adox rcx, rbp
movzx rcx, r9b
movzx r13, r13b
lea rcx, [ rcx + r13 ]
mov r13, 0xffffffff00000000 
mulx r9, rbp, r13
adcx rcx, [ rsp + 0xe0 ]
setc bl
clc
adcx rbp, r8
mov r8, 0xfffffffffffffffe 
mov [ rsp + 0x188 ], r12
mulx r12, r13, r8
adcx r13, r9
mov r9, 0xffffffffffffffff 
mov byte [ rsp + 0x190 ], bl
mulx rbx, r8, r9
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x198 ], rcx
mulx rcx, r9, [ rsi + 0x20 ]
mov rdx, r8
adcx rdx, r12
adox rbp, r10
adox r13, rdi
mov r10, rdx
mov rdx, [ rsi + 0x20 ]
mulx r12, rdi, [ rax + 0x20 ]
adox r10, r14
mov rdx, [ rsp - 0x38 ]
seto r14b
mov [ rsp + 0x1a0 ], r15
mov r15, -0x2 
inc r15
adox rdx, [ rsp - 0x18 ]
mov r15, r8
adcx r15, rbx
adcx r8, rbx
mov [ rsp + 0x1a8 ], r8
mov r8, 0x0 
adcx rbx, r8
mov r8, [ rsp - 0x20 ]
adox r8, [ rsp + 0x60 ]
mov [ rsp + 0x1b0 ], rbx
mov rbx, [ rsp + 0x58 ]
adox rbx, [ rsp + 0x18 ]
adox rdi, [ rsp + 0x10 ]
adox r9, r12
mov r12, 0x0 
adox rcx, r12
test al, al
adox rbp, [ rsp - 0x40 ]
adox rdx, r13
adox r8, r10
mov r13, -0x1 
movzx r14, r14b
adcx r14, r13
adcx r11, r15
mov r14, [ rsp + 0x1a8 ]
adcx r14, [ rsp + 0x1a0 ]
mov r10, [ rsp + 0x198 ]
adcx r10, [ rsp + 0x1b0 ]
adox rbx, r11
adox rdi, r14
movzx r15, byte [ rsp + 0x190 ]
adcx r15, r12
adox r9, r10
adox rcx, r15
mov r11, 0x100000001 
xchg rdx, rbp
mulx r10, r14, r11
mov r10, 0xffffffff00000000 
xchg rdx, r14
mulx r12, r15, r10
mov r13, 0xffffffff 
mulx r11, r10, r13
clc
adcx r15, r11
seto r11b
mov r13, -0x2 
inc r13
adox r10, r14
adox r15, rbp
mov r10, 0xfffffffffffffffe 
mulx rbp, r14, r10
adcx r14, r12
adox r14, r8
mov r8, 0xffffffffffffffff 
mulx r13, r12, r8
mov rdx, r12
adcx rdx, rbp
adox rdx, rbx
mov rbx, r12
adcx rbx, r13
adcx r12, r13
mov rbp, 0x0 
adcx r13, rbp
adox rbx, rdi
clc
adcx r15, [ rsp + 0x150 ]
adox r12, r9
mov rdi, 0x100000001 
xchg rdx, r15
mulx rbp, r9, rdi
adcx r14, [ rsp + 0x160 ]
adcx r15, [ rsp + 0x188 ]
adox r13, rcx
adcx rbx, [ rsp + 0x180 ]
adcx r12, [ rsp + 0x170 ]
adcx r13, [ rsp + 0x168 ]
mov rbp, 0xffffffff00000000 
xchg rdx, rbp
mulx r10, rcx, r9
mov r8, 0xffffffff 
mov rdx, r9
mulx rdi, r9, r8
movzx r8, r11b
mov [ rsp + 0x1b8 ], r13
mov r13, 0x0 
adox r8, r13
mov r11, -0x3 
inc r11
adox rcx, rdi
mov rdi, 0xfffffffffffffffe 
mulx r11, r13, rdi
adox r13, r10
adcx r8, [ rsp + 0x178 ]
setc r10b
clc
adcx r9, rbp
adcx rcx, r14
adcx r13, r15
mov r9, 0xffffffffffffffff 
mulx r14, rbp, r9
mov rdx, rbp
adox rdx, r11
mov r15, rbp
adox r15, r14
adox rbp, r14
adcx rdx, rbx
adcx r15, r12
adcx rbp, [ rsp + 0x1b8 ]
mov rbx, 0x0 
adox r14, rbx
adcx r14, r8
movzx r12, r10b
adc r12, 0x0
mov r11, rcx
mov r10, 0xffffffff 
sub r11, r10
mov r8, r13
mov rbx, 0xffffffff00000000 
sbb r8, rbx
mov r10, rdx
sbb r10, rdi
mov rdi, r15
sbb rdi, r9
mov rbx, rbp
sbb rbx, r9
mov [ rsp + 0x1c0 ], rdi
mov rdi, r14
sbb rdi, r9
sbb r12, 0x00000000
cmovc r8, r13
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x8 ], r8
cmovc r10, rdx
cmovc r11, rcx
cmovc rbx, rbp
cmovc rdi, r14
mov [ r12 + 0x28 ], rdi
mov [ r12 + 0x20 ], rbx
mov rcx, [ rsp + 0x1c0 ]
cmovc rcx, r15
mov [ r12 + 0x0 ], r11
mov [ r12 + 0x10 ], r10
mov [ r12 + 0x18 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 584
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.6611
; seed 0111997662088914 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5174057 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=60, initial num_batches=31): 134106 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.02591892590282635
; number reverted permutation / tried permutation: 63083 / 90157 =69.970%
; number reverted decision / tried decision: 46519 / 89842 =51.779%
; validated in 33.889s
