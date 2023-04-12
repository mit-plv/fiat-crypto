SECTION .text
	GLOBAL fiat_p384_mul
fiat_p384_mul:
sub rsp, 520
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x10 ]
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x10 ]
mov rdx, 0x100000001 
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rcx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rax + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r14
mulx r14, rdi, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x40 ], r10
mov [ rsp - 0x38 ], r14
mulx r14, r10, [ rax + 0x20 ]
xor rdx, rdx
adox r9, r11
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], r9
mulx r9, r11, [ rax + 0x10 ]
adox r11, rbx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], r11
mulx r11, rbx, [ rax + 0x18 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x20 ], r14
mov [ rsp - 0x18 ], r10
mulx r10, r14, r13
adox rbx, r9
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x10 ], rbx
mulx rbx, r9, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x8 ], r9
mov [ rsp + 0x0 ], r10
mulx r10, r9, [ rax + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x8 ], r14
mov [ rsp + 0x10 ], r12
mulx r12, r14, [ rax + 0x8 ]
adcx r14, rbx
adox r9, r11
mov rdx, [ rsi + 0x10 ]
mulx rbx, r11, [ rax + 0x28 ]
adox r11, r10
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x18 ], r14
mulx r14, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x20 ], r11
mov [ rsp + 0x28 ], r9
mulx r9, r11, [ rax + 0x10 ]
mov rdx, 0x0 
adox rbx, rdx
mov [ rsp + 0x30 ], rbx
mov rbx, -0x3 
inc rbx
adox r10, r8
adox r11, r14
mov rdx, [ rsi + 0x20 ]
mulx r14, r8, [ rax + 0x10 ]
adcx r8, r12
mov rdx, [ rax + 0x18 ]
mulx rbx, r12, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x38 ], r8
mov [ rsp + 0x40 ], r11
mulx r11, r8, [ rax + 0x20 ]
adox r12, r9
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x48 ], r12
mulx r12, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x50 ], r10
mov [ rsp + 0x58 ], rcx
mulx rcx, r10, [ rax + 0x0 ]
adox r8, rbx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x60 ], r10
mulx r10, rbx, [ rsi + 0x28 ]
seto dl
mov [ rsp + 0x68 ], r8
mov r8, -0x2 
inc r8
adox r9, r15
adcx rdi, r14
seto r15b
inc r8
adox rbx, rcx
adox rbp, r10
mov r14b, dl
mov rdx, [ rax + 0x0 ]
mulx r10, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x70 ], rbp
mulx rbp, r8, [ rax + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x78 ], rbx
mov [ rsp + 0x80 ], rdi
mulx rdi, rbx, [ rsi + 0x28 ]
setc dl
clc
adcx r8, r10
adox rbx, [ rsp + 0x10 ]
mov r10b, dl
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x88 ], rbx
mov [ rsp + 0x90 ], r9
mulx r9, rbx, [ rsi + 0x8 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x98 ], r8
mov [ rsp + 0xa0 ], rcx
mulx rcx, r8, [ rsi + 0x28 ]
adox rdi, [ rsp - 0x18 ]
adox r8, [ rsp - 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xa8 ], r8
mov [ rsp + 0xb0 ], rdi
mulx rdi, r8, [ rax + 0x10 ]
adcx r8, rbp
adcx rbx, rdi
mov rdx, [ rsi + 0x8 ]
mulx rdi, rbp, [ rax + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xb8 ], rdi
mov [ rsp + 0xc0 ], rbx
mulx rbx, rdi, [ rax + 0x20 ]
adcx rdi, r9
adcx rbp, rbx
mov rdx, 0xffffffff 
mulx rbx, r9, r13
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0xc8 ], rbp
mov [ rsp + 0xd0 ], rdi
mulx rdi, rbp, r13
mov rdx, 0xffffffff00000000 
mov [ rsp + 0xd8 ], r8
mov byte [ rsp + 0xe0 ], r10b
mulx r10, r8, r13
setc r13b
clc
adcx r8, rbx
adcx rbp, r10
mov rdx, [ rax + 0x28 ]
mulx r10, rbx, [ rsi + 0x0 ]
adcx rdi, [ rsp + 0x8 ]
setc dl
clc
mov byte [ rsp + 0xe8 ], r13b
mov r13, -0x1 
movzx r14, r14b
adcx r14, r13
adcx r11, rbx
mov r14, 0x0 
adcx r10, r14
mov bl, dl
mov rdx, [ rax + 0x10 ]
mulx r13, r14, [ rsi + 0x18 ]
mov rdx, 0x0 
adox rcx, rdx
add r15b, 0xFF
adcx r12, r14
adox r9, [ rsp + 0x58 ]
adox r8, [ rsp + 0x50 ]
mov rdx, [ rax + 0x20 ]
mulx r15, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xf0 ], rcx
mulx rcx, r14, [ rax + 0x18 ]
adcx r14, r13
adcx r9, rcx
mov rdx, [ rsi + 0x18 ]
mulx rcx, r13, [ rax + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xf8 ], r9
mov [ rsp + 0x100 ], r14
mulx r14, r9, [ rax + 0x28 ]
adox rbp, [ rsp + 0x40 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x108 ], r12
mov [ rsp + 0x110 ], r10
mulx r10, r12, [ rsi + 0x20 ]
adox rdi, [ rsp + 0x48 ]
adcx r13, r15
mov rdx, 0x0 
adcx rcx, rdx
movzx r15, byte [ rsp + 0xe0 ]
clc
mov rdx, -0x1 
adcx r15, rdx
adcx r12, [ rsp - 0x38 ]
adcx r9, r10
mov r15, [ rsp + 0x0 ]
mov r10, r15
setc dl
clc
mov [ rsp + 0x118 ], r9
mov r9, -0x1 
movzx rbx, bl
adcx rbx, r9
adcx r10, [ rsp + 0x8 ]
mov rbx, r15
adcx rbx, [ rsp + 0x8 ]
movzx r9, dl
lea r9, [ r9 + r14 ]
mov r14, 0x0 
adcx r15, r14
clc
adcx r8, [ rsp + 0xa0 ]
adcx rbp, [ rsp + 0x98 ]
adcx rdi, [ rsp + 0xd8 ]
adox r10, [ rsp + 0x68 ]
adox rbx, r11
adox r15, [ rsp + 0x110 ]
adcx r10, [ rsp + 0xc0 ]
mov r11, 0x100000001 
mov rdx, r11
mulx r14, r11, r8
mov r14, 0xffffffff00000000 
mov rdx, r11
mov [ rsp + 0x120 ], r9
mulx r9, r11, r14
mov r14, 0xffffffffffffffff 
mov [ rsp + 0x128 ], r12
mov [ rsp + 0x130 ], rcx
mulx rcx, r12, r14
mov r14, 0xffffffff 
mov [ rsp + 0x138 ], r13
mov [ rsp + 0x140 ], r10
mulx r10, r13, r14
mov r14, 0xfffffffffffffffe 
mov [ rsp + 0x148 ], rdi
mov [ rsp + 0x150 ], rbp
mulx rbp, rdi, r14
adcx rbx, [ rsp + 0xd0 ]
adcx r15, [ rsp + 0xc8 ]
movzx rdx, byte [ rsp + 0xe8 ]
mov r14, [ rsp + 0xb8 ]
lea rdx, [ rdx + r14 ]
setc r14b
movzx r14, r14b
adox r14, rdx
clc
adcx r11, r10
adcx rdi, r9
mov r9, r12
adcx r9, rbp
mov r10, r12
adcx r10, rcx
adcx r12, rcx
mov rbp, 0x0 
adcx rcx, rbp
clc
adcx r13, r8
adcx r11, [ rsp + 0x150 ]
seto r13b
mov r8, -0x3 
inc r8
adox r11, [ rsp - 0x40 ]
mov rdx, 0x100000001 
mulx r8, rbp, r11
adcx rdi, [ rsp + 0x148 ]
adcx r9, [ rsp + 0x140 ]
adox rdi, [ rsp - 0x30 ]
mov r8, 0xffffffff 
mov rdx, rbp
mov [ rsp + 0x158 ], rdi
mulx rdi, rbp, r8
adcx r10, rbx
adox r9, [ rsp - 0x28 ]
adcx r12, r15
adox r10, [ rsp - 0x10 ]
adcx rcx, r14
adox r12, [ rsp + 0x28 ]
adox rcx, [ rsp + 0x20 ]
mov rbx, 0xffffffffffffffff 
mulx r14, r15, rbx
movzx rbx, r13b
mov r8, 0x0 
adcx rbx, r8
adox rbx, [ rsp + 0x30 ]
clc
adcx rbp, r11
mov rbp, 0xffffffff00000000 
mulx r11, r13, rbp
mov r8, 0xfffffffffffffffe 
mov [ rsp + 0x160 ], rbx
mulx rbx, rbp, r8
seto dl
mov r8, -0x2 
inc r8
adox r13, rdi
adcx r13, [ rsp + 0x158 ]
adox rbp, r11
mov rdi, r15
adox rdi, rbx
mov r11, r15
adox r11, r14
adcx rbp, r9
adox r15, r14
mov r9, 0x0 
adox r14, r9
mov rbx, -0x3 
inc rbx
adox r13, [ rsp - 0x48 ]
adcx rdi, r10
adcx r11, r12
adcx r15, rcx
adox rbp, [ rsp + 0x90 ]
adox rdi, [ rsp + 0x108 ]
adox r11, [ rsp + 0x100 ]
adcx r14, [ rsp + 0x160 ]
adox r15, [ rsp + 0xf8 ]
movzx r10, dl
adcx r10, r9
mov r12, 0x100000001 
mov rdx, r12
mulx rcx, r12, r13
mov rcx, 0xffffffff 
mov rdx, rcx
mulx r9, rcx, r12
adox r14, [ rsp + 0x138 ]
clc
adcx rcx, r13
mov rcx, 0xffffffff00000000 
mov rdx, rcx
mulx r13, rcx, r12
adox r10, [ rsp + 0x130 ]
seto bl
inc r8
adox rcx, r9
adcx rcx, rbp
mov rbp, 0xfffffffffffffffe 
mov rdx, r12
mulx r9, r12, rbp
adox r12, r13
mov r13, 0xffffffffffffffff 
mulx rbp, r8, r13
adcx r12, rdi
mov rdi, r8
adox rdi, r9
adcx rdi, r11
mov r11, r8
adox r11, rbp
adcx r11, r15
adox r8, rbp
mov r15, 0x0 
adox rbp, r15
adcx r8, r14
adcx rbp, r10
mov rdx, -0x3 
inc rdx
adox rcx, [ rsp - 0x8 ]
adox r12, [ rsp + 0x18 ]
adox rdi, [ rsp + 0x38 ]
adox r11, [ rsp + 0x80 ]
adox r8, [ rsp + 0x128 ]
movzx r14, bl
adcx r14, r15
adox rbp, [ rsp + 0x118 ]
mov rbx, 0x100000001 
mov rdx, rbx
mulx r10, rbx, rcx
adox r14, [ rsp + 0x120 ]
mov r10, 0xffffffff 
mov rdx, rbx
mulx r9, rbx, r10
clc
adcx rbx, rcx
mov rbx, 0xffffffff00000000 
mulx r15, rcx, rbx
mulx r10, rbx, r13
seto r13b
mov [ rsp + 0x168 ], r14
mov r14, -0x2 
inc r14
adox rcx, r9
adcx rcx, r12
mov r12, 0xfffffffffffffffe 
mulx r14, r9, r12
adox r9, r15
adcx r9, rdi
mov rdi, rbx
adox rdi, r14
adcx rdi, r11
mov r11, rbx
adox r11, r10
adox rbx, r10
mov rdx, 0x0 
adox r10, rdx
adcx r11, r8
adcx rbx, rbp
adcx r10, [ rsp + 0x168 ]
movzx r8, r13b
adc r8, 0x0
xor rbp, rbp
adox rcx, [ rsp + 0x60 ]
adox r9, [ rsp + 0x78 ]
mov rdx, 0x100000001 
mulx r15, r13, rcx
adox rdi, [ rsp + 0x70 ]
mov r15, 0xffffffff00000000 
mov rdx, r13
mulx r14, r13, r15
adox r11, [ rsp + 0x88 ]
mulx r15, rbp, r12
adox rbx, [ rsp + 0xb0 ]
adox r10, [ rsp + 0xa8 ]
adox r8, [ rsp + 0xf0 ]
mov r12, 0xffffffff 
mov [ rsp + 0x170 ], r8
mov [ rsp + 0x178 ], r10
mulx r10, r8, r12
adcx r8, rcx
seto r8b
mov rcx, -0x2 
inc rcx
adox r13, r10
adox rbp, r14
adcx r13, r9
mov r9, 0xffffffffffffffff 
mulx r10, r14, r9
mov rdx, r14
adox rdx, r15
mov r15, r14
adox r15, r10
adox r14, r10
mov rcx, 0x0 
adox r10, rcx
adcx rbp, rdi
adcx rdx, r11
adcx r15, rbx
adcx r14, [ rsp + 0x178 ]
adcx r10, [ rsp + 0x170 ]
movzx rdi, r8b
adc rdi, 0x0
mov r11, r13
sub r11, r12
mov rbx, rbp
mov r8, 0xffffffff00000000 
sbb rbx, r8
mov rcx, rdx
mov r9, 0xfffffffffffffffe 
sbb rcx, r9
mov r8, r15
mov r9, 0xffffffffffffffff 
sbb r8, r9
mov r12, r14
sbb r12, r9
mov [ rsp + 0x180 ], r11
mov r11, r10
sbb r11, r9
sbb rdi, 0x00000000
cmovc rbx, rbp
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x8 ], rbx
cmovc r12, r14
cmovc r11, r10
mov [ rdi + 0x20 ], r12
cmovc r8, r15
mov [ rdi + 0x28 ], r11
mov [ rdi + 0x18 ], r8
cmovc rcx, rdx
mov rbp, [ rsp + 0x180 ]
cmovc rbp, r13
mov [ rdi + 0x10 ], rcx
mov [ rdi + 0x0 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 520
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.5454
; seed 2212791632180848 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 7058397 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=88, initial num_batches=31): 208232 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.029501315950349632
; number reverted permutation / tried permutation: 76605 / 89503 =85.589%
; number reverted decision / tried decision: 70216 / 90496 =77.590%
; validated in 61.36s
