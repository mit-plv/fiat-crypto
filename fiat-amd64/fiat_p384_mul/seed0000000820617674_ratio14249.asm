SECTION .text
	GLOBAL fiat_p384_mul
fiat_p384_mul:
sub rsp, 784
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, [ rax + 0x28 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x28 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x0 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x28 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x48 ], rdi
mov [ rsp - 0x40 ], r15
mulx r15, rdi, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], r12
mov [ rsp - 0x30 ], rbp
mulx rbp, r12, [ rax + 0x10 ]
mov rdx, 0x100000001 
mov [ rsp - 0x28 ], r14
mov [ rsp - 0x20 ], r13
mulx r13, r14, r10
mov r13, 0xffffffff 
mov rdx, r13
mov [ rsp - 0x18 ], r11
mulx r11, r13, r14
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x10 ], r13
mov [ rsp - 0x8 ], r8
mulx r8, r13, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x0 ], r8
mov [ rsp + 0x8 ], r13
mulx r13, r8, [ rsi + 0x10 ]
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x10 ], rcx
mov [ rsp + 0x18 ], rbx
mulx rbx, rcx, r14
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x20 ], r9
mov [ rsp + 0x28 ], r15
mulx r15, r9, [ rsi + 0x18 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x30 ], r15
mov [ rsp + 0x38 ], r9
mulx r9, r15, r14
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x40 ], r13
mov [ rsp + 0x48 ], r8
mulx r8, r13, [ rsi + 0x20 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x50 ], r8
mov [ rsp + 0x58 ], r13
mulx r13, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x60 ], r8
mov [ rsp + 0x68 ], r13
mulx r13, r8, [ rax + 0x10 ]
xor rdx, rdx
adox rcx, r11
mov r11, 0xfffffffffffffffe 
mov rdx, r14
mov [ rsp + 0x70 ], rcx
mulx rcx, r14, r11
adox r14, rbx
mov rdx, r15
adox rdx, rcx
mov rbx, r15
adox rbx, r9
mov rcx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x78 ], rbx
mulx rbx, r11, [ rax + 0x28 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x80 ], rbx
mov [ rsp + 0x88 ], r11
mulx r11, rbx, [ rsi + 0x8 ]
adox r15, r9
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x90 ], r15
mov [ rsp + 0x98 ], rcx
mulx rcx, r15, [ rax + 0x8 ]
adcx r15, r11
adcx r12, rcx
adcx rdi, rbp
mov rdx, [ rax + 0x0 ]
mulx r11, rbp, [ rsi + 0x20 ]
mov rdx, [ rsp + 0x68 ]
seto cl
mov [ rsp + 0xa0 ], r11
mov r11, -0x2 
inc r11
adox rdx, [ rsp + 0x48 ]
mov r11, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xa8 ], rbp
mov byte [ rsp + 0xb0 ], cl
mulx rcx, rbp, [ rax + 0x18 ]
adox r8, [ rsp + 0x40 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0xb8 ], r8
mov [ rsp + 0xc0 ], r11
mulx r11, r8, [ rsi + 0x20 ]
adox rbp, r13
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xc8 ], r11
mulx r11, r13, [ rax + 0x20 ]
adcx r13, [ rsp + 0x28 ]
adox rcx, [ rsp + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xd0 ], r8
mov [ rsp + 0xd8 ], rcx
mulx rcx, r8, [ rax + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xe0 ], rbp
mov [ rsp + 0xe8 ], r13
mulx r13, rbp, [ rax + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xf0 ], rdi
mov [ rsp + 0xf8 ], r12
mulx r12, rdi, [ rax + 0x10 ]
adox r8, [ rsp + 0x18 ]
adcx r11, [ rsp + 0x10 ]
mov rdx, 0x0 
adox rcx, rdx
mov rdx, [ rsp - 0x8 ]
adc rdx, 0x0
mov [ rsp + 0x100 ], rcx
mov rcx, [ rsp - 0x18 ]
mov [ rsp + 0x108 ], r8
xor r8, r8
adox rcx, [ rsp - 0x20 ]
adox rdi, [ rsp - 0x28 ]
adox rbp, r12
adox r13, [ rsp + 0x8 ]
mov r12, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x110 ], r11
mulx r11, r8, [ rsi + 0x0 ]
adcx r10, [ rsp - 0x10 ]
adcx rcx, [ rsp + 0x70 ]
adox r8, [ rsp + 0x0 ]
seto r10b
mov rdx, -0x2 
inc rdx
adox rbx, rcx
movzx rcx, r10b
lea rcx, [ rcx + r11 ]
mov r11, 0x100000001 
mov rdx, rbx
mulx r10, rbx, r11
adcx r14, rdi
mov r10, 0xfffffffffffffffe 
xchg rdx, rbx
mulx r11, rdi, r10
adcx rbp, [ rsp + 0x98 ]
adox r15, r14
mov r14, 0xffffffffffffffff 
mov [ rsp + 0x118 ], r11
mulx r11, r10, r14
adcx r13, [ rsp + 0x78 ]
adox rbp, [ rsp + 0xf8 ]
adox r13, [ rsp + 0xf0 ]
adcx r8, [ rsp + 0x90 ]
movzx r14, byte [ rsp + 0xb0 ]
lea r9, [ r9 + r14 ]
adcx r9, rcx
mov r14, 0xffffffff00000000 
mov [ rsp + 0x120 ], r13
mulx r13, rcx, r14
adox r8, [ rsp + 0xe8 ]
adox r9, [ rsp + 0x110 ]
mov r14, 0xffffffff 
mov [ rsp + 0x128 ], r9
mov [ rsp + 0x130 ], r8
mulx r8, r9, r14
setc dl
movzx rdx, dl
adox rdx, r12
clc
adcx rcx, r8
adcx rdi, r13
seto r12b
mov r13, -0x2 
inc r13
adox r9, rbx
adox rcx, r15
mov r9, r10
adcx r9, [ rsp + 0x118 ]
adox rdi, rbp
mov rbx, r10
adcx rbx, r11
adox r9, [ rsp + 0x120 ]
adcx r10, r11
setc r15b
clc
adcx rcx, [ rsp + 0x60 ]
movzx rbp, r15b
lea rbp, [ rbp + r11 ]
adcx rdi, [ rsp + 0xc0 ]
adcx r9, [ rsp + 0xb8 ]
adox rbx, [ rsp + 0x130 ]
adcx rbx, [ rsp + 0xe0 ]
adox r10, [ rsp + 0x128 ]
adox rbp, rdx
adcx r10, [ rsp + 0xd8 ]
adcx rbp, [ rsp + 0x108 ]
mov r11, 0x100000001 
mov rdx, rcx
mulx r8, rcx, r11
xchg rdx, rcx
mulx r15, r8, r14
movzx r13, r12b
mov r14, 0x0 
adox r13, r14
adcx r13, [ rsp + 0x100 ]
mov r12, -0x3 
inc r12
adox r8, rcx
mov r8, 0xffffffff00000000 
mulx r14, rcx, r8
mov r12, 0xfffffffffffffffe 
mulx r11, r8, r12
setc r12b
clc
adcx rcx, r15
adox rcx, rdi
adcx r8, r14
mov rdi, 0xffffffffffffffff 
mulx r14, r15, rdi
mov rdx, r15
adcx rdx, r11
adox r8, r9
adox rdx, rbx
mov r9, rdx
mov rdx, [ rax + 0x0 ]
mulx r11, rbx, [ rsi + 0x18 ]
mov rdx, r15
adcx rdx, r14
adcx r15, r14
adox rdx, r10
mov r10, rdx
mov rdx, [ rsi + 0x18 ]
mov byte [ rsp + 0x138 ], r12b
mulx r12, rdi, [ rax + 0x8 ]
seto dl
mov [ rsp + 0x140 ], r13
mov r13, -0x2 
inc r13
adox rdi, r11
mov r11b, dl
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x148 ], r15
mulx r15, r13, [ rsi + 0x18 ]
adox r13, r12
setc dl
clc
adcx rbx, rcx
adox r15, [ rsp + 0x38 ]
mov rcx, 0x100000001 
xchg rdx, rcx
mov [ rsp + 0x150 ], rbp
mulx rbp, r12, rbx
mov rbp, 0xffffffff00000000 
mov rdx, r12
mov byte [ rsp + 0x158 ], r11b
mulx r11, r12, rbp
mov rbp, 0xffffffffffffffff 
mov [ rsp + 0x160 ], r11
mov [ rsp + 0x168 ], r12
mulx r12, r11, rbp
mov rbp, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x170 ], r12
mov [ rsp + 0x178 ], r11
mulx r11, r12, [ rax + 0x0 ]
adcx rdi, r8
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x180 ], r11
mulx r11, r8, [ rax + 0x20 ]
adox r8, [ rsp + 0x30 ]
adcx r13, r9
adcx r15, r10
mov rdx, 0xffffffff 
mulx r10, r9, rbp
movzx rdx, cl
lea rdx, [ rdx + r14 ]
mov r14, 0xfffffffffffffffe 
xchg rdx, r14
mov [ rsp + 0x188 ], r8
mulx r8, rcx, rbp
setc bpl
clc
adcx r10, [ rsp + 0x168 ]
adcx rcx, [ rsp + 0x160 ]
adcx r8, [ rsp + 0x178 ]
adox r11, [ rsp - 0x30 ]
seto dl
mov [ rsp + 0x190 ], r11
mov r11, -0x2 
inc r11
adox r9, rbx
adox r10, rdi
adox rcx, r13
mov r9, [ rsp + 0x178 ]
mov rbx, r9
adcx rbx, [ rsp + 0x170 ]
mov dil, dl
mov rdx, [ rsi + 0x20 ]
mulx r11, r13, [ rax + 0x8 ]
adcx r9, [ rsp + 0x170 ]
adox r8, r15
seto dl
mov r15, -0x2 
inc r15
adox r10, [ rsp + 0xa8 ]
mov r15, [ rsp + 0x170 ]
mov [ rsp + 0x198 ], r9
mov r9, 0x0 
adcx r15, r9
mov r9, 0x100000001 
xchg rdx, r10
mov [ rsp + 0x1a0 ], r15
mov [ rsp + 0x1a8 ], rbx
mulx rbx, r15, r9
mov rbx, 0xffffffff 
xchg rdx, rbx
mov byte [ rsp + 0x1b0 ], r10b
mulx r10, r9, r15
mov rdx, 0xffffffffffffffff 
mov byte [ rsp + 0x1b8 ], dil
mov byte [ rsp + 0x1c0 ], bpl
mulx rbp, rdi, r15
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x1c8 ], rbp
mov [ rsp + 0x1d0 ], rdi
mulx rdi, rbp, r15
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x1d8 ], r14
mov [ rsp + 0x1e0 ], r12
mulx r12, r14, [ rsi + 0x20 ]
clc
adcx r13, [ rsp + 0xa0 ]
adcx r14, r11
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x1e8 ], rdi
mulx rdi, r11, r15
adcx r12, [ rsp + 0xd0 ]
mov r15, [ rsp + 0x58 ]
adcx r15, [ rsp + 0xc8 ]
adox r13, rcx
mov rcx, [ rsp + 0x50 ]
adcx rcx, [ rsp + 0x88 ]
adox r14, r8
seto r8b
mov rdx, -0x2 
inc rdx
adox r9, rbx
setc r9b
clc
adcx rbp, r10
adcx r11, [ rsp + 0x1e8 ]
adox rbp, r13
seto bl
inc rdx
adox rbp, [ rsp + 0x1e0 ]
mov r10, 0x100000001 
mov rdx, r10
mulx r13, r10, rbp
mov r13, [ rsp + 0x148 ]
seto dl
mov byte [ rsp + 0x1f0 ], r9b
movzx r9, byte [ rsp + 0x158 ]
mov [ rsp + 0x1f8 ], rcx
mov rcx, -0x1 
inc rcx
mov rcx, -0x1 
adox r9, rcx
adox r13, [ rsp + 0x150 ]
mov r9b, dl
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x200 ], r15
mulx r15, rcx, [ rsi + 0x28 ]
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x208 ], r15
mov [ rsp + 0x210 ], r12
mulx r12, r15, r10
seto dl
mov [ rsp + 0x218 ], r12
mov r12, -0x2 
inc r12
adox rcx, [ rsp + 0x180 ]
mov r12, [ rsp + 0x1d8 ]
mov [ rsp + 0x220 ], r15
seto r15b
mov byte [ rsp + 0x228 ], r8b
mov r8, 0x0 
dec r8
movzx rdx, dl
adox rdx, r8
adox r12, [ rsp + 0x140 ]
mov rdx, 0xffffffff 
mov byte [ rsp + 0x230 ], r15b
mulx r15, r8, r10
seto dl
mov [ rsp + 0x238 ], r8
movzx r8, byte [ rsp + 0x1c0 ]
mov [ rsp + 0x240 ], r15
mov r15, 0x0 
dec r15
adox r8, r15
adox r13, [ rsp + 0x188 ]
adox r12, [ rsp + 0x190 ]
movzx r8, byte [ rsp + 0x1b8 ]
mov r15, [ rsp - 0x38 ]
lea r8, [ r8 + r15 ]
mov r15b, dl
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x248 ], rcx
mov byte [ rsp + 0x250 ], r9b
mulx r9, rcx, [ rsi + 0x28 ]
adcx rdi, [ rsp + 0x1d0 ]
mov rdx, [ rsp + 0x1c8 ]
mov [ rsp + 0x258 ], r9
mov r9, rdx
adcx r9, [ rsp + 0x1d0 ]
mov [ rsp + 0x260 ], rcx
mov rcx, rdx
adcx rcx, [ rsp + 0x1d0 ]
mov [ rsp + 0x268 ], rcx
movzx rcx, r15b
mov [ rsp + 0x270 ], r9
movzx r9, byte [ rsp + 0x138 ]
lea rcx, [ rcx + r9 ]
adox r8, rcx
mov r9, 0x0 
adcx rdx, r9
movzx r15, byte [ rsp + 0x1b0 ]
clc
mov rcx, -0x1 
adcx r15, rcx
adcx r13, [ rsp + 0x1a8 ]
adcx r12, [ rsp + 0x198 ]
adcx r8, [ rsp + 0x1a0 ]
seto r15b
adc r15b, 0x0
movzx r15, r15b
add bl, 0x7F
adox r14, r11
movzx r11, byte [ rsp + 0x250 ]
adcx r11, rcx
adcx r14, [ rsp + 0x248 ]
setc bl
movzx r11, byte [ rsp + 0x228 ]
clc
adcx r11, rcx
adcx r13, [ rsp + 0x210 ]
adcx r12, [ rsp + 0x200 ]
adcx r8, [ rsp + 0x1f8 ]
mov r11, rdx
mov rdx, [ rsi + 0x28 ]
mulx rcx, r9, [ rax + 0x10 ]
adox rdi, r13
movzx rdx, byte [ rsp + 0x1f0 ]
mov r13, [ rsp + 0x80 ]
lea rdx, [ rdx + r13 ]
adox r12, [ rsp + 0x270 ]
adox r8, [ rsp + 0x268 ]
movzx r13, r15b
adcx r13, rdx
adox r11, r13
seto r15b
movzx rdx, byte [ rsp + 0x230 ]
mov r13, -0x1 
inc r13
mov r13, -0x1 
adox rdx, r13
adox r9, [ rsp + 0x208 ]
movzx rdx, r15b
mov r13, 0x0 
adcx rdx, r13
clc
mov r15, -0x1 
movzx rbx, bl
adcx rbx, r15
adcx rdi, r9
adox rcx, [ rsp + 0x260 ]
adcx rcx, r12
mov rbx, [ rsp + 0x258 ]
adox rbx, [ rsp - 0x40 ]
mov r12, rdx
mov rdx, [ rsi + 0x28 ]
mulx r13, r9, [ rax + 0x28 ]
adox r9, [ rsp - 0x48 ]
mov rdx, 0x0 
adox r13, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x278 ], r13
mulx r13, r15, r10
adcx rbx, r8
mov r8, 0xffffffff00000000 
mov rdx, r8
mov [ rsp + 0x280 ], r12
mulx r12, r8, r10
mov r10, -0x2 
inc r10
adox r8, [ rsp + 0x240 ]
adcx r9, r11
adox r12, [ rsp + 0x220 ]
setc r11b
clc
adcx rbp, [ rsp + 0x238 ]
mov rbp, r15
adox rbp, [ rsp + 0x218 ]
mov r10, r15
adox r10, r13
adox r15, r13
adcx r8, r14
mov r14, 0x0 
adox r13, r14
adcx r12, rdi
adcx rbp, rcx
adcx r10, rbx
adcx r15, r9
mov rdi, [ rsp + 0x278 ]
dec r14
movzx r11, r11b
adox r11, r14
adox rdi, [ rsp + 0x280 ]
adcx r13, rdi
setc cl
seto bl
mov r11, r8
mov r9, 0xffffffff 
sub r11, r9
mov rdi, r12
sbb rdi, rdx
mov r14, rbp
mov r9, 0xfffffffffffffffe 
sbb r14, r9
mov rdx, r10
mov r9, 0xffffffffffffffff 
sbb rdx, r9
mov [ rsp + 0x288 ], rdx
mov rdx, r15
sbb rdx, r9
movzx r9, cl
movzx rbx, bl
lea r9, [ r9 + rbx ]
mov rbx, r13
mov rcx, 0xffffffffffffffff 
sbb rbx, rcx
sbb r9, 0x00000000
cmovc rbx, r13
cmovc r14, rbp
cmovc r11, r8
mov r9, [ rsp + 0x288 ]
cmovc r9, r10
cmovc rdi, r12
cmovc rdx, r15
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x28 ], rbx
mov [ r8 + 0x8 ], rdi
mov [ r8 + 0x20 ], rdx
mov [ r8 + 0x0 ], r11
mov [ r8 + 0x18 ], r9
mov [ r8 + 0x10 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 784
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.4249
; seed 1088034630982463 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5217800 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=54, initial num_batches=31): 132899 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.02547031315880256
; number reverted permutation / tried permutation: 60748 / 89938 =67.544%
; number reverted decision / tried decision: 49104 / 90061 =54.523%
; validated in 33.732s
