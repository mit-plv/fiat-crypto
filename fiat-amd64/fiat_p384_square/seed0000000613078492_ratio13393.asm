SECTION .text
	GLOBAL fiat_p384_square
fiat_p384_square:
sub rsp, 632
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mulx rcx, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbp
mulx rbp, rdi, rdx
mov rdx, 0x100000001 
mov [ rsp - 0x40 ], r15
mov [ rsp - 0x38 ], r14
mulx r14, r15, rdi
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x30 ], rbx
mulx rbx, r14, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], rcx
mov [ rsp - 0x20 ], r11
mulx r11, rcx, [ rsi + 0x20 ]
xor rdx, rdx
adox r14, r10
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], r11
mulx r11, r10, rdx
mov rdx, 0xfffffffffffffffe 
mov [ rsp - 0x10 ], r11
mov [ rsp - 0x8 ], rcx
mulx rcx, r11, r15
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x0 ], r10
mov [ rsp + 0x8 ], r14
mulx r14, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x10 ], rax
mov [ rsp + 0x18 ], r14
mulx r14, rax, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x20 ], r14
mov [ rsp + 0x28 ], rax
mulx rax, r14, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x30 ], rax
mov [ rsp + 0x38 ], r14
mulx r14, rax, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x40 ], r14
mov [ rsp + 0x48 ], rax
mulx rax, r14, [ rsi + 0x8 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x50 ], r10
mov [ rsp + 0x58 ], r9
mulx r9, r10, r15
adox r14, rbx
mov rbx, 0xffffffff00000000 
mov rdx, r15
mov [ rsp + 0x60 ], r14
mulx r14, r15, rbx
adcx r15, r9
mov r9, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x68 ], r8
mulx r8, rbx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x70 ], r8
mov [ rsp + 0x78 ], r13
mulx r13, r8, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x80 ], r13
mov [ rsp + 0x88 ], r8
mulx r8, r13, [ rsi + 0x18 ]
adox r13, rax
adcx r11, r14
mov rdx, 0xffffffffffffffff 
mulx r14, rax, r9
adox rbx, r8
mov r9, rax
adcx r9, rcx
mov rcx, rax
adcx rcx, r14
adcx rax, r14
mov r8, 0x0 
adcx r14, r8
clc
adcx r12, rbp
seto bpl
mov rdx, -0x3 
inc rdx
adox r10, rdi
adox r15, r12
mov rdx, [ rsi + 0x0 ]
mulx rdi, r10, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mulx r8, r12, [ rsi + 0x0 ]
adcx r12, [ rsp + 0x78 ]
adcx r10, r8
adcx rdi, [ rsp + 0x68 ]
adox r11, r12
adox r9, r10
mov rdx, [ rsp + 0x50 ]
adcx rdx, [ rsp + 0x58 ]
mov r8, rdx
mov rdx, [ rsi + 0x10 ]
mulx r10, r12, [ rsi + 0x0 ]
adox rcx, rdi
adox rax, r8
mov rdx, [ rsp + 0x18 ]
mov rdi, 0x0 
adcx rdx, rdi
clc
adcx r10, [ rsp + 0x28 ]
adox r14, rdx
seto r8b
mov rdx, -0x3 
inc rdx
adox r15, [ rsp + 0x10 ]
adox r11, [ rsp + 0x8 ]
mov rdi, 0x100000001 
mov rdx, r15
mov [ rsp + 0x90 ], r10
mulx r10, r15, rdi
mov r10, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x98 ], r12
mulx r12, rdi, [ rsi + 0x28 ]
mov rdx, [ rsp + 0x0 ]
adcx rdx, [ rsp + 0x20 ]
mov [ rsp + 0xa0 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xa8 ], r11
mov byte [ rsp + 0xb0 ], r8b
mulx r8, r11, [ rsi + 0x8 ]
setc dl
clc
adcx r11, r12
adox r9, [ rsp + 0x60 ]
mov r12b, dl
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xb8 ], r11
mov [ rsp + 0xc0 ], rdi
mulx rdi, r11, [ rsi + 0x28 ]
adcx r8, [ rsp - 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xc8 ], r8
mov byte [ rsp + 0xd0 ], r12b
mulx r12, r8, [ rsi + 0x8 ]
adcx r11, [ rsp - 0x28 ]
adox r13, rcx
adcx rdi, [ rsp - 0x30 ]
setc dl
clc
mov rcx, -0x1 
movzx rbp, bpl
adcx rbp, rcx
adcx r8, [ rsp + 0x70 ]
mov rbp, 0x0 
adcx r12, rbp
mov rbp, 0xffffffff00000000 
xchg rdx, r15
mov [ rsp + 0xd8 ], rdi
mulx rdi, rcx, rbp
adox rbx, rax
mov rax, 0xffffffff 
mov [ rsp + 0xe0 ], r11
mulx r11, rbp, rax
adox r8, r14
clc
adcx rcx, r11
movzx r14, byte [ rsp + 0xb0 ]
adox r14, r12
mov r12, 0xfffffffffffffffe 
mulx rax, r11, r12
seto r12b
mov byte [ rsp + 0xe8 ], r15b
mov r15, -0x2 
inc r15
adox rbp, r10
adox rcx, [ rsp + 0xa8 ]
adcx r11, rdi
adox r11, r9
mov rbp, 0xffffffffffffffff 
mulx r9, r10, rbp
mov rdx, r10
adcx rdx, rax
mov rdi, r10
adcx rdi, r9
adcx r10, r9
mov rax, 0x0 
adcx r9, rax
clc
adcx rcx, [ rsp + 0x98 ]
mov rax, 0x100000001 
xchg rdx, rax
mulx rbp, r15, rcx
adox rax, r13
adcx r11, [ rsp + 0x90 ]
adcx rax, [ rsp + 0xc0 ]
adox rdi, rbx
mov rdx, [ rsi + 0x0 ]
mulx r13, rbp, [ rsi + 0x20 ]
adox r10, r8
mov rdx, 0xffffffff 
mulx r8, rbx, r15
mov rdx, 0xffffffff00000000 
mov [ rsp + 0xf0 ], rbp
mov byte [ rsp + 0xf8 ], r12b
mulx r12, rbp, r15
adox r9, r14
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x100 ], r9
mulx r9, r14, [ rsi + 0x20 ]
setc dl
clc
adcx r14, r13
mov r13, 0xffffffffffffffff 
xchg rdx, r15
mov [ rsp + 0x108 ], r14
mov [ rsp + 0x110 ], r10
mulx r10, r14, r13
mov r13, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x118 ], r10
mov [ rsp + 0x120 ], r14
mulx r14, r10, [ rsi + 0x20 ]
adcx r9, [ rsp + 0x48 ]
mov rdx, [ rsp - 0x8 ]
adcx rdx, [ rsp + 0x40 ]
mov [ rsp + 0x128 ], r14
mov r14, 0xfffffffffffffffe 
xchg rdx, r13
mov [ rsp + 0x130 ], r13
mov [ rsp + 0x138 ], r9
mulx r9, r13, r14
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x140 ], r9
mulx r9, r14, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x148 ], r9
mov [ rsp + 0x150 ], rdi
mulx rdi, r9, rdx
adcx r9, [ rsp - 0x18 ]
seto dl
mov [ rsp + 0x158 ], r9
mov r9, -0x2 
inc r9
adox rbp, r8
adox r13, r12
adcx r10, rdi
setc r8b
clc
adcx rbx, rcx
adcx rbp, r11
adcx r13, rax
setc bl
clc
adcx r14, rbp
mov rcx, 0x100000001 
xchg rdx, rcx
mulx rax, r11, r14
mov rax, 0xffffffff 
mov rdx, rax
mulx r12, rax, r11
mov rdi, 0xfffffffffffffffe 
mov rdx, r11
mulx rbp, r11, rdi
setc r9b
clc
adcx rax, r14
mov rax, [ rsp - 0x38 ]
setc r14b
movzx rdi, byte [ rsp + 0xd0 ]
clc
mov [ rsp + 0x160 ], r10
mov r10, -0x1 
adcx rdi, r10
adcx rax, [ rsp - 0x10 ]
mov rdi, [ rsp - 0x40 ]
adcx rdi, [ rsp + 0x88 ]
setc r10b
clc
mov byte [ rsp + 0x168 ], r8b
mov r8, -0x1 
movzx r15, r15b
adcx r15, r8
adcx rax, [ rsp + 0x150 ]
mov r15, [ rsp + 0x140 ]
adox r15, [ rsp + 0x120 ]
mov r8, [ rsp + 0x118 ]
mov [ rsp + 0x170 ], rbp
mov rbp, r8
adox rbp, [ rsp + 0x120 ]
mov [ rsp + 0x178 ], r11
mov r11, rdx
mov rdx, [ rsi + 0x10 ]
mov byte [ rsp + 0x180 ], r14b
mov [ rsp + 0x188 ], r12
mulx r12, r14, [ rsi + 0x28 ]
mov rdx, r8
adox rdx, [ rsp + 0x120 ]
mov [ rsp + 0x190 ], r13
mov r13, 0x0 
adox r8, r13
adcx rdi, [ rsp + 0x110 ]
dec r13
movzx r10, r10b
adox r10, r13
adox r14, [ rsp + 0x80 ]
mov r10, rdx
mov rdx, [ rsi + 0x8 ]
mov byte [ rsp + 0x198 ], r9b
mulx r9, r13, [ rsi + 0x18 ]
mov rdx, 0x0 
adox r12, rdx
adcx r14, [ rsp + 0x100 ]
dec rdx
movzx rbx, bl
adox rbx, rdx
adox rax, r15
adox rbp, rdi
mov rdx, [ rsi + 0x18 ]
mulx r15, rbx, rdx
adox r10, r14
movzx rdx, cl
movzx rdi, byte [ rsp + 0xf8 ]
lea rdx, [ rdx + rdi ]
adcx r12, rdx
adox r8, r12
setc dil
clc
adcx r13, [ rsp + 0x148 ]
seto cl
movzx r14, byte [ rsp + 0x198 ]
mov rdx, 0x0 
dec rdx
adox r14, rdx
adox r13, [ rsp + 0x190 ]
mov rdx, [ rsi + 0x18 ]
mulx r12, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1a0 ], r13
mov [ rsp + 0x1a8 ], r8
mulx r8, r13, [ rsi + 0x28 ]
adcx r14, r9
adcx rbx, r12
movzx rdx, cl
movzx rdi, dil
lea rdx, [ rdx + rdi ]
adcx r15, [ rsp + 0x38 ]
adcx r13, [ rsp + 0x30 ]
adox r14, rax
adox rbx, rbp
adox r15, r10
adox r13, [ rsp + 0x1a8 ]
mov r9, 0xffffffff00000000 
xchg rdx, r11
mulx rbp, rax, r9
mov r10, 0x0 
adcx r8, r10
clc
adcx rax, [ rsp + 0x188 ]
mov rdi, 0xffffffffffffffff 
mulx r12, rcx, rdi
setc dl
movzx r10, byte [ rsp + 0x180 ]
clc
mov r9, -0x1 
adcx r10, r9
adcx rax, [ rsp + 0x1a0 ]
adox r8, r11
seto r10b
inc r9
adox rax, [ rsp + 0xf0 ]
seto r11b
dec r9
movzx rdx, dl
adox rdx, r9
adox rbp, [ rsp + 0x178 ]
mov rdx, rcx
adox rdx, [ rsp + 0x170 ]
mov r9, 0x100000001 
xchg rdx, r9
mov byte [ rsp + 0x1b0 ], r10b
mulx r10, rdi, rax
mov r10, rcx
adox r10, r12
mov rdx, 0xffffffff 
mov [ rsp + 0x1b8 ], r8
mov [ rsp + 0x1c0 ], r13
mulx r13, r8, rdi
adox rcx, r12
mov rdx, 0x0 
adox r12, rdx
adcx rbp, r14
adcx r9, rbx
adcx r10, r15
dec rdx
movzx r11, r11b
adox r11, rdx
adox rbp, [ rsp + 0x108 ]
adox r9, [ rsp + 0x138 ]
adcx rcx, [ rsp + 0x1c0 ]
adcx r12, [ rsp + 0x1b8 ]
adox r10, [ rsp + 0x130 ]
movzx r14, byte [ rsp + 0x1b0 ]
mov rbx, 0x0 
adcx r14, rbx
mov r15, 0xfffffffffffffffe 
mov rdx, r15
mulx r11, r15, rdi
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x1c8 ], r14
mulx r14, rbx, rdx
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x1d0 ], r14
mov [ rsp + 0x1d8 ], rbx
mulx rbx, r14, rdi
clc
adcx r14, r13
adcx r15, rbx
seto r13b
mov rbx, -0x2 
inc rbx
adox r8, rax
mov r8, 0xffffffffffffffff 
mov rdx, rdi
mulx rax, rdi, r8
adox r14, rbp
adox r15, r9
mov rdx, rdi
adcx rdx, r11
mov rbp, rdi
adcx rbp, rax
adox rdx, r10
movzx r9, byte [ rsp + 0x168 ]
mov r10, [ rsp + 0x128 ]
lea r9, [ r9 + r10 ]
seto r10b
inc rbx
mov r11, -0x1 
movzx r13, r13b
adox r13, r11
adox rcx, [ rsp + 0x158 ]
adox r12, [ rsp + 0x160 ]
adox r9, [ rsp + 0x1c8 ]
adcx rdi, rax
adcx rax, rbx
clc
movzx r10, r10b
adcx r10, r11
adcx rcx, rbp
adcx rdi, r12
adcx rax, r9
seto r13b
mov rbp, -0x3 
inc rbp
adox r14, [ rsp + 0xa0 ]
adox r15, [ rsp + 0xb8 ]
movzx r10, r13b
adcx r10, rbx
mov r12, 0x100000001 
xchg rdx, r12
mulx r9, r13, r14
mov r9, 0xffffffff 
mov rdx, r13
mulx rbx, r13, r9
clc
adcx r13, r14
mov r13, [ rsp - 0x48 ]
setc r14b
movzx rbp, byte [ rsp + 0xe8 ]
clc
adcx rbp, r11
adcx r13, [ rsp + 0x1d8 ]
mov rbp, [ rsp + 0x1d0 ]
mov r11, 0x0 
adcx rbp, r11
mov r11, 0xffffffff00000000 
mulx r9, r8, r11
clc
adcx r8, rbx
adox r12, [ rsp + 0xc8 ]
adox rcx, [ rsp + 0xe0 ]
mov rbx, 0xfffffffffffffffe 
mov [ rsp + 0x1e0 ], rbp
mulx rbp, r11, rbx
mov rbx, 0xffffffffffffffff 
mov [ rsp + 0x1e8 ], r10
mov [ rsp + 0x1f0 ], r13
mulx r13, r10, rbx
adox rdi, [ rsp + 0xd8 ]
adcx r11, r9
mov rdx, r10
adcx rdx, rbp
mov r9, r10
adcx r9, r13
adcx r10, r13
mov rbp, 0x0 
adcx r13, rbp
clc
mov rbp, -0x1 
movzx r14, r14b
adcx r14, rbp
adcx r15, r8
adcx r11, r12
adcx rdx, rcx
adox rax, [ rsp + 0x1f0 ]
mov r14, [ rsp + 0x1e8 ]
adox r14, [ rsp + 0x1e0 ]
adcx r9, rdi
adcx r10, rax
adcx r13, r14
seto r8b
adc r8b, 0x0
movzx r8, r8b
mov r12, r15
mov rcx, 0xffffffff 
sub r12, rcx
mov rdi, r11
mov rax, 0xffffffff00000000 
sbb rdi, rax
mov r14, rdx
mov rbp, 0xfffffffffffffffe 
sbb r14, rbp
mov rbp, r9
sbb rbp, rbx
mov rcx, r10
sbb rcx, rbx
mov rax, r13
sbb rax, rbx
movzx rbx, r8b
sbb rbx, 0x00000000
cmovc rdi, r11
cmovc rcx, r10
cmovc rax, r13
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x20 ], rcx
cmovc rbp, r9
mov [ rbx + 0x8 ], rdi
mov [ rbx + 0x18 ], rbp
cmovc r14, rdx
mov [ rbx + 0x10 ], r14
mov [ rbx + 0x28 ], rax
cmovc r12, r15
mov [ rbx + 0x0 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 632
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.3393
; seed 2218083722610333 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5072531 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=63, initial num_batches=31): 136324 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.026874946648921417
; number reverted permutation / tried permutation: 65447 / 90000 =72.719%
; number reverted decision / tried decision: 51121 / 89999 =56.802%
; validated in 30.51s
