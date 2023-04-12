SECTION .text
	GLOBAL fiat_p384_mul
fiat_p384_mul:
sub rsp, 808
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mulx r8, rcx, [ rax + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x18 ]
mov rdx, 0x100000001 
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, rbp
mov rdi, 0xfffffffffffffffe 
mov rdx, r15
mov [ rsp - 0x48 ], r8
mulx r8, r15, rdi
mov rdi, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x40 ], rcx
mov [ rsp - 0x38 ], r11
mulx r11, rcx, [ rsi + 0x8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x30 ], r10
mov [ rsp - 0x28 ], r11
mulx r11, r10, rdi
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x20 ], rcx
mov [ rsp - 0x18 ], r14
mulx r14, rcx, [ rax + 0x20 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x10 ], r14
mov [ rsp - 0x8 ], rcx
mulx rcx, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x0 ], rcx
mov [ rsp + 0x8 ], r14
mulx r14, rcx, [ rax + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x10 ], r14
mov [ rsp + 0x18 ], rcx
mulx rcx, r14, [ rax + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x20 ], rcx
mov [ rsp + 0x28 ], r14
mulx r14, rcx, [ rax + 0x8 ]
xor rdx, rdx
adox rcx, r12
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x30 ], rbx
mulx rbx, r12, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x38 ], rbx
mov [ rsp + 0x40 ], r12
mulx r12, rbx, [ rsi + 0x20 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x48 ], r12
mov [ rsp + 0x50 ], rbx
mulx rbx, r12, rdi
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x58 ], rcx
mov [ rsp + 0x60 ], r12
mulx r12, rcx, rdi
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x68 ], r13
mulx r13, rdi, [ rsi + 0x18 ]
adcx rcx, rbx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x70 ], r13
mulx r13, rbx, [ rax + 0x28 ]
adcx r15, r12
mov rdx, r10
adcx rdx, r8
mov r8, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x78 ], r13
mulx r13, r12, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x80 ], rbx
mov [ rsp + 0x88 ], rdi
mulx rdi, rbx, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x90 ], r8
mov [ rsp + 0x98 ], r15
mulx r15, r8, [ rsi + 0x8 ]
adox r9, r14
seto dl
mov r14, -0x2 
inc r14
adox r8, rdi
adox r12, r15
mov rdi, r10
adcx rdi, r11
adcx r10, r11
adox r13, [ rsp + 0x68 ]
mov r15, 0x0 
adcx r11, r15
clc
adcx rbp, [ rsp + 0x60 ]
adcx rcx, [ rsp + 0x58 ]
seto bpl
mov r14, -0x3 
inc r14
adox rbx, rcx
mov rcx, 0x100000001 
xchg rdx, rcx
mulx r14, r15, rbx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0xa0 ], r13
mulx r13, r14, [ rsi + 0x28 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0xa8 ], r14
mov [ rsp + 0xb0 ], r12
mulx r12, r14, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0xb8 ], r11
mov [ rsp + 0xc0 ], r8
mulx r8, r11, r15
seto dl
mov [ rsp + 0xc8 ], r8
mov r8, -0x1 
inc r8
mov r8, -0x1 
movzx rcx, cl
adox rcx, r8
adox r14, [ rsp + 0x30 ]
adox r12, [ rsp - 0x8 ]
mov cl, dl
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xd0 ], r11
mulx r11, r8, [ rsi + 0x8 ]
mov rdx, [ rsp - 0x10 ]
adox rdx, [ rsp + 0x8 ]
adcx r9, [ rsp + 0x98 ]
adcx r14, [ rsp + 0x90 ]
adcx rdi, r12
setc r12b
clc
mov [ rsp + 0xd8 ], rdi
mov rdi, -0x1 
movzx rbp, bpl
adcx rbp, rdi
adcx r8, [ rsp - 0x18 ]
adcx r11, [ rsp - 0x20 ]
mov rbp, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xe0 ], r11
mulx r11, rdi, [ rax + 0x8 ]
mov rdx, [ rsp + 0x0 ]
mov [ rsp + 0xe8 ], r11
mov r11, 0x0 
adox rdx, r11
mov [ rsp + 0xf0 ], r8
mov r8, -0x3 
inc r8
adox rdi, r13
setc r13b
clc
mov r11, -0x1 
movzx r12, r12b
adcx r12, r11
adcx rbp, r10
mov r10, 0xffffffff 
xchg rdx, r15
mulx r11, r12, r10
seto r8b
mov r10, -0x1 
inc r10
mov r10, -0x1 
movzx rcx, cl
adox rcx, r10
adox r9, [ rsp + 0xc0 ]
adcx r15, [ rsp + 0xb8 ]
mov rcx, 0xffffffff00000000 
mov byte [ rsp + 0xf8 ], r8b
mulx r8, r10, rcx
mov rcx, 0xfffffffffffffffe 
mov [ rsp + 0x100 ], rdi
mov byte [ rsp + 0x108 ], r13b
mulx r13, rdi, rcx
setc dl
clc
adcx r10, r11
adcx rdi, r8
adcx r13, [ rsp + 0xd0 ]
adox r14, [ rsp + 0xb0 ]
mov r11, [ rsp + 0xd8 ]
adox r11, [ rsp + 0xa0 ]
adox rbp, [ rsp + 0xf0 ]
setc r8b
clc
adcx r12, rbx
adox r15, [ rsp + 0xe0 ]
adcx r10, r9
mov r12b, dl
mov rdx, [ rsi + 0x10 ]
mulx r9, rbx, [ rax + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x110 ], r15
mulx r15, rcx, [ rax + 0x8 ]
setc dl
clc
adcx rbx, r10
mov r10, 0x100000001 
xchg rdx, r10
mov [ rsp + 0x118 ], rbp
mov [ rsp + 0x120 ], r13
mulx r13, rbp, rbx
setc r13b
clc
adcx rcx, r9
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x128 ], rcx
mulx rcx, r9, [ rsi + 0x10 ]
movzx rdx, byte [ rsp + 0x108 ]
mov byte [ rsp + 0x130 ], r13b
mov r13, [ rsp - 0x28 ]
lea rdx, [ rdx + r13 ]
mov r13, 0xffffffff 
xchg rdx, r13
mov [ rsp + 0x138 ], r11
mov [ rsp + 0x140 ], rdi
mulx rdi, r11, rbp
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x148 ], r11
mov [ rsp + 0x150 ], rdi
mulx rdi, r11, [ rsi + 0x10 ]
movzx rdx, r12b
adox rdx, r13
mov r12, [ rsp + 0xd0 ]
mov r13, r12
mov [ rsp + 0x158 ], rdx
seto dl
mov [ rsp + 0x160 ], r14
mov r14, 0x0 
dec r14
movzx r8, r8b
adox r8, r14
adox r13, [ rsp + 0xc8 ]
adcx r9, r15
mov r8b, dl
mov rdx, [ rax + 0x20 ]
mulx r14, r15, [ rsi + 0x10 ]
adox r12, [ rsp + 0xc8 ]
adcx r11, rcx
mov rdx, [ rsp + 0xc8 ]
mov rcx, 0x0 
adox rdx, rcx
mov rcx, rdx
mov rdx, [ rax + 0x28 ]
mov byte [ rsp + 0x168 ], r8b
mov [ rsp + 0x170 ], r11
mulx r11, r8, [ rsi + 0x10 ]
adcx r15, rdi
mov rdx, [ rsp + 0x140 ]
mov rdi, 0x0 
dec rdi
movzx r10, r10b
adox r10, rdi
adox rdx, [ rsp + 0x160 ]
adcx r8, r14
mov r10, [ rsp + 0x120 ]
adox r10, [ rsp + 0x138 ]
mov r14, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x178 ], r8
mulx r8, rdi, [ rax + 0x10 ]
mov rdx, 0x0 
adcx r11, rdx
adox r13, [ rsp + 0x118 ]
movzx rdx, byte [ rsp + 0x130 ]
clc
mov [ rsp + 0x180 ], r11
mov r11, -0x1 
adcx rdx, r11
adcx r14, [ rsp + 0x128 ]
adox r12, [ rsp + 0x110 ]
adox rcx, [ rsp + 0x158 ]
adcx r9, r10
adcx r13, [ rsp + 0x170 ]
adcx r15, r12
mov rdx, 0xfffffffffffffffe 
mulx r12, r10, rbp
mov r11, 0xffffffff00000000 
mov rdx, rbp
mov [ rsp + 0x188 ], rcx
mulx rcx, rbp, r11
setc r11b
clc
adcx rbp, [ rsp + 0x150 ]
mov byte [ rsp + 0x190 ], r11b
movzx r11, byte [ rsp + 0x168 ]
mov [ rsp + 0x198 ], r8
mov r8, 0x0 
adox r11, r8
adcx r10, rcx
mov rcx, 0xffffffffffffffff 
mov [ rsp + 0x1a0 ], r11
mulx r11, r8, rcx
mov rdx, -0x2 
inc rdx
adox rbx, [ rsp + 0x148 ]
adox rbp, r14
adox r10, r9
mov rbx, r8
adcx rbx, r12
adox rbx, r13
mov r14, r8
adcx r14, r11
adcx r8, r11
adox r14, r15
mov rdx, [ rsi + 0x18 ]
mulx r13, r9, [ rax + 0x8 ]
setc dl
clc
adcx rbp, [ rsp - 0x30 ]
mov r15b, dl
mov rdx, [ rax + 0x18 ]
mulx rcx, r12, [ rsi + 0x18 ]
movzx rdx, r15b
lea rdx, [ rdx + r11 ]
seto r11b
mov r15, -0x2 
inc r15
adox r9, [ rsp - 0x38 ]
adcx r9, r10
adox rdi, r13
adox r12, [ rsp + 0x198 ]
adcx rdi, rbx
mov r10, 0x100000001 
xchg rdx, r10
mulx r13, rbx, rbp
adcx r12, r14
mov rdx, [ rsi + 0x20 ]
mulx r14, r13, [ rax + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x1a8 ], r12
mulx r12, r15, rbx
mov rdx, 0xffffffff 
mov [ rsp + 0x1b0 ], r13
mov [ rsp + 0x1b8 ], rdi
mulx rdi, r13, rbx
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x1c0 ], r9
mov [ rsp + 0x1c8 ], r13
mulx r13, r9, rbx
adox rcx, [ rsp + 0x40 ]
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x1d0 ], rcx
mov [ rsp + 0x1d8 ], r10
mulx r10, rcx, rbx
mov rbx, [ rsp + 0x88 ]
adox rbx, [ rsp + 0x38 ]
mov rdx, [ rsp + 0x70 ]
mov [ rsp + 0x1e0 ], rbx
mov rbx, 0x0 
adox rdx, rbx
mov rbx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x1e8 ], r8
mov byte [ rsp + 0x1f0 ], r11b
mulx r11, r8, [ rax + 0x8 ]
mov rdx, -0x2 
inc rdx
adox r8, r14
adox r11, [ rsp + 0x50 ]
mov r14, [ rsp + 0x48 ]
adox r14, [ rsp + 0x18 ]
setc dl
clc
adcx r9, rdi
adcx rcx, r13
mov rdi, [ rsp - 0x40 ]
adox rdi, [ rsp + 0x10 ]
mov r13, r15
adcx r13, r10
mov r10, r15
adcx r10, r12
mov [ rsp + 0x1f8 ], rdi
mov rdi, [ rsp - 0x48 ]
adox rdi, [ rsp + 0x80 ]
mov [ rsp + 0x200 ], rdi
mov rdi, [ rsp + 0x188 ]
mov [ rsp + 0x208 ], r14
seto r14b
mov [ rsp + 0x210 ], r11
movzx r11, byte [ rsp + 0x190 ]
mov [ rsp + 0x218 ], r8
mov r8, -0x1 
inc r8
mov r8, -0x1 
adox r11, r8
adox rdi, [ rsp + 0x178 ]
mov r11, [ rsp + 0x1a0 ]
adox r11, [ rsp + 0x180 ]
seto r8b
mov byte [ rsp + 0x220 ], r14b
movzx r14, byte [ rsp + 0x1f0 ]
mov [ rsp + 0x228 ], r10
mov r10, -0x1 
inc r10
mov r10, -0x1 
adox r14, r10
adox rdi, [ rsp + 0x1e8 ]
adcx r15, r12
adox r11, [ rsp + 0x1d8 ]
mov r14, 0x0 
adcx r12, r14
movzx r14, r8b
mov r10, 0x0 
adox r14, r10
add dl, 0xFF
adcx rdi, [ rsp + 0x1d0 ]
adcx r11, [ rsp + 0x1e0 ]
adox rbp, [ rsp + 0x1c8 ]
adox r9, [ rsp + 0x1c0 ]
adcx rbx, r14
adox rcx, [ rsp + 0x1b8 ]
setc bpl
clc
adcx r9, [ rsp + 0x1b0 ]
mov rdx, 0x100000001 
mulx r14, r8, r9
mov r14, 0xfffffffffffffffe 
mov rdx, r14
mulx r10, r14, r8
adox r13, [ rsp + 0x1a8 ]
adox rdi, [ rsp + 0x228 ]
adcx rcx, [ rsp + 0x218 ]
adcx r13, [ rsp + 0x210 ]
adcx rdi, [ rsp + 0x208 ]
adox r15, r11
adox r12, rbx
adcx r15, [ rsp + 0x1f8 ]
movzx r11, bpl
mov rbx, 0x0 
adox r11, rbx
adcx r12, [ rsp + 0x200 ]
mov rdx, [ rsi + 0x28 ]
mulx rbx, rbp, [ rax + 0x18 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x230 ], r12
mov [ rsp + 0x238 ], rbx
mulx rbx, r12, r8
movzx rdx, byte [ rsp + 0x220 ]
mov [ rsp + 0x240 ], rbp
mov rbp, [ rsp + 0x78 ]
lea rdx, [ rdx + rbp ]
mov rbp, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x248 ], r15
mov [ rsp + 0x250 ], rdi
mulx rdi, r15, [ rsi + 0x28 ]
adcx rbp, r11
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x258 ], rbp
mulx rbp, r11, r8
mov rdx, -0x2 
inc rdx
adox r11, rbx
adox r14, rbp
mov rbx, 0xffffffffffffffff 
mov rdx, r8
mulx rbp, r8, rbx
setc dl
clc
adcx r12, r9
adcx r11, rcx
mov r12, r8
adox r12, r10
mov r9, r8
adox r9, rbp
adox r8, rbp
adcx r14, r13
adcx r12, [ rsp + 0x250 ]
adcx r9, [ rsp + 0x248 ]
mov r10b, dl
mov rdx, [ rsi + 0x28 ]
mulx r13, rcx, [ rax + 0x20 ]
setc dl
clc
adcx r11, [ rsp + 0xa8 ]
adcx r14, [ rsp + 0x100 ]
mov rbx, 0x100000001 
xchg rdx, rbx
mov [ rsp + 0x260 ], r14
mov byte [ rsp + 0x268 ], r10b
mulx r10, r14, r11
mov r10, [ rsp + 0x28 ]
seto dl
mov [ rsp + 0x270 ], rdi
movzx rdi, byte [ rsp + 0xf8 ]
mov [ rsp + 0x278 ], r8
mov r8, 0x0 
dec r8
adox rdi, r8
adox r10, [ rsp + 0xe8 ]
mov rdi, 0xffffffff 
xchg rdx, r14
mov byte [ rsp + 0x280 ], r14b
mulx r14, r8, rdi
mov rdi, [ rsp + 0x20 ]
adox rdi, [ rsp + 0x240 ]
adox rcx, [ rsp + 0x238 ]
adcx r10, r12
adcx rdi, r9
adox r15, r13
mov r12, [ rsp + 0x230 ]
setc r9b
clc
mov r13, -0x1 
movzx rbx, bl
adcx rbx, r13
adcx r12, [ rsp + 0x278 ]
mov rbx, [ rsp + 0x270 ]
mov r13, 0x0 
adox rbx, r13
movzx r13, byte [ rsp + 0x280 ]
lea rbp, [ rbp + r13 ]
adcx rbp, [ rsp + 0x258 ]
movzx r13, byte [ rsp + 0x268 ]
adc r13, 0x0
mov [ rsp + 0x288 ], rbx
mov rbx, 0xffffffff00000000 
mov [ rsp + 0x290 ], r13
mov [ rsp + 0x298 ], r15
mulx r15, r13, rbx
test al, al
adox r8, r11
adcx r13, r14
adox r13, [ rsp + 0x260 ]
mov r8, 0xfffffffffffffffe 
mulx r14, r11, r8
adcx r11, r15
adox r11, r10
mov r10, 0xffffffffffffffff 
mulx r8, r15, r10
mov rdx, r15
adcx rdx, r14
mov r14, r15
adcx r14, r8
adox rdx, rdi
adcx r15, r8
mov rdi, 0x0 
adcx r8, rdi
clc
mov rdi, -0x1 
movzx r9, r9b
adcx r9, rdi
adcx r12, rcx
adox r14, r12
adcx rbp, [ rsp + 0x298 ]
mov rcx, [ rsp + 0x290 ]
adcx rcx, [ rsp + 0x288 ]
adox r15, rbp
adox r8, rcx
setc r9b
seto r12b
mov rbp, r13
mov rcx, 0xffffffff 
sub rbp, rcx
movzx rdi, r12b
movzx r9, r9b
lea rdi, [ rdi + r9 ]
mov r9, r11
sbb r9, rbx
mov r12, rdx
mov rbx, 0xfffffffffffffffe 
sbb r12, rbx
mov rbx, r14
sbb rbx, r10
mov rcx, r15
sbb rcx, r10
mov [ rsp + 0x2a0 ], rbp
mov rbp, r8
sbb rbp, r10
sbb rdi, 0x00000000
cmovc rbp, r8
cmovc rbx, r14
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x28 ], rbp
cmovc r9, r11
cmovc r12, rdx
mov [ rdi + 0x10 ], r12
mov [ rdi + 0x8 ], r9
cmovc rcx, r15
mov [ rdi + 0x18 ], rbx
mov r11, [ rsp + 0x2a0 ]
cmovc r11, r13
mov [ rdi + 0x20 ], rcx
mov [ rdi + 0x0 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 808
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.2584
; seed 1034059598755007 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4465621 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=59, initial num_batches=31): 113555 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.025428714169876934
; number reverted permutation / tried permutation: 59623 / 90035 =66.222%
; number reverted decision / tried decision: 51793 / 89964 =57.571%
; validated in 26.9s
