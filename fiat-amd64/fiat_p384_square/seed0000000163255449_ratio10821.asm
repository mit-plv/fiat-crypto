SECTION .text
	GLOBAL fiat_p384_square
fiat_p384_square:
sub rsp, 912
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbp
mulx rbp, rdi, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x40 ], rbx
mov [ rsp - 0x38 ], r13
mulx r13, rbx, [ rsi + 0x18 ]
mov rdx, 0x100000001 
mov [ rsp - 0x30 ], rbx
mov [ rsp - 0x28 ], r13
mulx r13, rbx, rdi
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x20 ], r12
mulx r12, r13, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], r8
mov [ rsp - 0x10 ], r10
mulx r10, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x8 ], r10
mov [ rsp + 0x0 ], r8
mulx r8, r10, [ rsi + 0x28 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x8 ], r8
mov [ rsp + 0x10 ], r10
mulx r10, r8, rbx
mov rdx, 0xffffffff 
mov [ rsp + 0x18 ], rax
mov [ rsp + 0x20 ], r12
mulx r12, rax, rbx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x28 ], rax
mov [ rsp + 0x30 ], r13
mulx r13, rax, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x38 ], r13
mov [ rsp + 0x40 ], rax
mulx rax, r13, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x48 ], rax
mov [ rsp + 0x50 ], r13
mulx r13, rax, [ rsi + 0x8 ]
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x58 ], r13
mov [ rsp + 0x60 ], rax
mulx rax, r13, rbx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x68 ], r9
mov [ rsp + 0x70 ], rcx
mulx rcx, r9, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x78 ], rcx
mov [ rsp + 0x80 ], r9
mulx r9, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x88 ], r9
mov [ rsp + 0x90 ], rcx
mulx rcx, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x98 ], rcx
mov [ rsp + 0xa0 ], r9
mulx r9, rcx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xa8 ], r9
mov [ rsp + 0xb0 ], rcx
mulx rcx, r9, [ rsi + 0x0 ]
xor rdx, rdx
adox r14, rbp
mov rbp, 0xfffffffffffffffe 
mov rdx, rbp
mov [ rsp + 0xb8 ], r14
mulx r14, rbp, rbx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xc0 ], r11
mulx r11, rbx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xc8 ], r11
mov [ rsp + 0xd0 ], rbx
mulx rbx, r11, [ rsi + 0x18 ]
adox r9, r15
adcx r13, r12
adcx rbp, rax
mov rdx, r8
adcx rdx, r14
mov r15, r8
adcx r15, r10
mov r12, rdx
mov rdx, [ rsi + 0x0 ]
mulx r14, rax, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xd8 ], rbx
mov [ rsp + 0xe0 ], r11
mulx r11, rbx, [ rsi + 0x0 ]
adcx r8, r10
adox rcx, [ rsp + 0xc0 ]
adox rax, [ rsp + 0x70 ]
adox rbx, r14
mov rdx, 0x0 
adcx r10, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xe8 ], r10
mulx r10, r14, [ rsi + 0x8 ]
mov rdx, [ rsp + 0x68 ]
clc
adcx rdx, [ rsp + 0x30 ]
mov [ rsp + 0xf0 ], r11
mov r11, [ rsp + 0x20 ]
adcx r11, [ rsp + 0x18 ]
mov [ rsp + 0xf8 ], r10
seto r10b
mov [ rsp + 0x100 ], r11
mov r11, -0x2 
inc r11
adox rdi, [ rsp + 0x28 ]
adcx r14, [ rsp - 0x10 ]
adox r13, [ rsp + 0xb8 ]
setc dil
clc
adcx r13, [ rsp - 0x18 ]
adox rbp, r9
mov r9, 0x100000001 
xchg rdx, r9
mov byte [ rsp + 0x108 ], r10b
mulx r10, r11, r13
mov r10, 0xffffffff 
mov rdx, r11
mov byte [ rsp + 0x110 ], dil
mulx rdi, r11, r10
adox r12, rcx
adcx r9, rbp
adox r15, rax
adox r8, rbx
mov rcx, 0xffffffff00000000 
mulx rbx, rax, rcx
adcx r12, [ rsp + 0x100 ]
adcx r14, r15
setc bpl
clc
adcx rax, rdi
mov rdi, 0xfffffffffffffffe 
mulx rcx, r15, rdi
mov rdi, 0xffffffffffffffff 
mov [ rsp + 0x118 ], r14
mulx r14, r10, rdi
adcx r15, rbx
mov rdx, r10
adcx rdx, rcx
mov rbx, r10
adcx rbx, r14
adcx r10, r14
mov rcx, [ rsp + 0xf8 ]
seto dil
mov [ rsp + 0x120 ], r10
movzx r10, byte [ rsp + 0x110 ]
mov [ rsp + 0x128 ], rbx
mov rbx, 0x0 
dec rbx
adox r10, rbx
adox rcx, [ rsp + 0x50 ]
setc r10b
clc
adcx r11, r13
adcx rax, r9
movzx r11, r10b
lea r11, [ r11 + r14 ]
mov r13, rdx
mov rdx, [ rsi + 0x10 ]
mulx r14, r9, [ rsi + 0x0 ]
seto dl
inc rbx
adox r9, rax
mov r10, 0x100000001 
xchg rdx, r9
mulx rbx, rax, r10
adcx r15, r12
mov rbx, [ rsp + 0x48 ]
seto r12b
mov r10, -0x1 
inc r10
mov r10, -0x1 
movzx r9, r9b
adox r9, r10
adox rbx, [ rsp + 0x60 ]
mov r9, 0xffffffffffffffff 
xchg rdx, r9
mov [ rsp + 0x130 ], r11
mulx r11, r10, rax
seto dl
mov [ rsp + 0x138 ], r11
mov r11, 0x0 
dec r11
movzx rbp, bpl
adox rbp, r11
adox r8, rcx
mov rbp, 0xffffffff 
xchg rdx, rax
mulx r11, rcx, rbp
seto bpl
mov [ rsp + 0x140 ], r10
mov r10, -0x2 
inc r10
adox r14, [ rsp + 0x90 ]
adcx r13, [ rsp + 0x118 ]
mov r10, [ rsp + 0x80 ]
adox r10, [ rsp + 0x88 ]
mov [ rsp + 0x148 ], rcx
mov rcx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x150 ], r11
mov byte [ rsp + 0x158 ], al
mulx rax, r11, [ rsi + 0x10 ]
adcx r8, [ rsp + 0x128 ]
mov rdx, [ rsp + 0x78 ]
adox rdx, [ rsp + 0xa0 ]
mov [ rsp + 0x160 ], rdx
movzx rdx, byte [ rsp + 0x108 ]
mov [ rsp + 0x168 ], r8
mov r8, [ rsp + 0xf0 ]
lea rdx, [ rdx + r8 ]
adox r11, [ rsp + 0x98 ]
setc r8b
clc
mov [ rsp + 0x170 ], r11
mov r11, -0x1 
movzx r12, r12b
adcx r12, r11
adcx r15, r14
adcx r10, r13
mov r12, rdx
mov rdx, [ rsi + 0x8 ]
mulx r13, r14, [ rsi + 0x28 ]
setc dl
clc
movzx rdi, dil
adcx rdi, r11
adcx r12, [ rsp + 0xe8 ]
setc dil
clc
movzx rbp, bpl
adcx rbp, r11
adcx r12, rbx
adox rax, [ rsp + 0x40 ]
movzx rbx, byte [ rsp + 0x158 ]
mov rbp, [ rsp + 0x58 ]
lea rbx, [ rbx + rbp ]
seto bpl
inc r11
mov r11, -0x1 
movzx r8, r8b
adox r8, r11
adox r12, [ rsp + 0x120 ]
movzx r8, dil
adcx r8, rbx
movzx rdi, bpl
mov rbx, [ rsp + 0x38 ]
lea rdi, [ rdi + rbx ]
mov rbx, 0xffffffff00000000 
xchg rdx, rcx
mulx r11, rbp, rbx
mov rbx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x178 ], rdi
mov [ rsp + 0x180 ], r10
mulx r10, rdi, [ rsi + 0x28 ]
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x188 ], r15
mov [ rsp + 0x190 ], r11
mulx r11, r15, rbx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x198 ], r11
mulx r11, rbx, rdx
seto dl
mov [ rsp + 0x1a0 ], r11
mov r11, -0x2 
inc r11
adox rbp, [ rsp + 0x150 ]
setc r11b
clc
mov [ rsp + 0x1a8 ], rbp
mov rbp, -0x1 
movzx rdx, dl
adcx rdx, rbp
adcx r8, [ rsp + 0x130 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x1b0 ], r15
mulx r15, rbp, [ rsi + 0x0 ]
seto dl
mov [ rsp + 0x1b8 ], rbp
mov rbp, -0x2 
inc rbp
adox r14, r15
movzx r15, r11b
mov rbp, 0x0 
adcx r15, rbp
adox r13, [ rsp - 0x20 ]
mov r11, [ rsp + 0x168 ]
clc
mov rbp, -0x1 
movzx rcx, cl
adcx rcx, rbp
adcx r11, [ rsp + 0x160 ]
adcx r12, [ rsp + 0x170 ]
adox rdi, [ rsp - 0x38 ]
adcx rax, r8
adox r10, [ rsp + 0x10 ]
adox rbx, [ rsp + 0x8 ]
mov rcx, [ rsp + 0x190 ]
setc r8b
clc
movzx rdx, dl
adcx rdx, rbp
adcx rcx, [ rsp + 0x1b0 ]
seto dl
inc rbp
adox r9, [ rsp + 0x148 ]
mov r9, [ rsp + 0x198 ]
adcx r9, [ rsp + 0x140 ]
mov rbp, [ rsp + 0x188 ]
adox rbp, [ rsp + 0x1a8 ]
adox rcx, [ rsp + 0x180 ]
mov [ rsp + 0x1c0 ], rbx
mov rbx, [ rsp + 0x138 ]
mov [ rsp + 0x1c8 ], r10
mov r10, rbx
adcx r10, [ rsp + 0x140 ]
adox r9, r11
mov r11, rbx
adcx r11, [ rsp + 0x140 ]
adox r10, r12
mov r12, [ rsp - 0x28 ]
mov byte [ rsp + 0x1d0 ], dl
setc dl
clc
adcx r12, [ rsp + 0x0 ]
mov [ rsp + 0x1d8 ], rdi
seto dil
mov [ rsp + 0x1e0 ], r13
mov r13, -0x2 
inc r13
adox rbp, [ rsp - 0x30 ]
mov r13, 0x100000001 
xchg rdx, rbp
mov [ rsp + 0x1e8 ], r14
mov [ rsp + 0x1f0 ], r11
mulx r11, r14, r13
adox r12, rcx
mov r11, 0xffffffff00000000 
xchg rdx, r14
mulx r13, rcx, r11
mov r11, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x1f8 ], rax
mov byte [ rsp + 0x200 ], dil
mulx rdi, rax, [ rsi + 0x0 ]
mov rdx, [ rsp - 0x8 ]
adcx rdx, [ rsp + 0xe0 ]
adox rdx, r9
mov r9, [ rsp + 0xd8 ]
adcx r9, [ rsp + 0xd0 ]
adox r9, r10
mov r10, [ rsp + 0xc8 ]
adcx r10, [ rsp + 0xb0 ]
mov [ rsp + 0x208 ], r10
mov r10, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x210 ], r15
mov byte [ rsp + 0x218 ], r8b
mulx r8, r15, [ rsi + 0x20 ]
mov rdx, 0xffffffff 
mov byte [ rsp + 0x220 ], bpl
mov [ rsp + 0x228 ], r8
mulx r8, rbp, r11
setc dl
clc
adcx rbp, r14
mov bpl, dl
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x230 ], r15
mulx r15, r14, [ rsi + 0x28 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x238 ], r15
mov [ rsp + 0x240 ], r14
mulx r14, r15, r11
seto dl
mov byte [ rsp + 0x248 ], bpl
mov rbp, -0x2 
inc rbp
adox rcx, r8
mov r8, 0xfffffffffffffffe 
xchg rdx, r8
mov byte [ rsp + 0x250 ], r8b
mulx r8, rbp, r11
adox rbp, r13
adcx rcx, r12
adcx rbp, r10
mov r11, r15
adox r11, r8
mov rdx, [ rsi + 0x28 ]
mulx r13, r12, [ rsi + 0x20 ]
adcx r11, r9
mov rdx, [ rsi + 0x20 ]
mulx r9, r10, [ rsi + 0x18 ]
setc dl
clc
adcx rax, rcx
mov r8, 0x100000001 
xchg rdx, r8
mov byte [ rsp + 0x258 ], r8b
mulx r8, rcx, rax
mov r8, 0xffffffff 
mov rdx, rcx
mov [ rsp + 0x260 ], r11
mulx r11, rcx, r8
mov r8, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x268 ], rcx
mov [ rsp + 0x270 ], r11
mulx r11, rcx, [ rsi + 0x10 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x278 ], r13
mov [ rsp + 0x280 ], r12
mulx r12, r13, r8
mov rdx, r15
adox rdx, r14
adox r15, r14
mov [ rsp + 0x288 ], r15
seto r15b
mov [ rsp + 0x290 ], rdx
mov rdx, -0x2 
inc rdx
adox rdi, [ rsp + 0x230 ]
adcx rdi, rbp
adox rcx, [ rsp + 0x228 ]
adox r10, r11
adox r9, [ rsp - 0x40 ]
mov rbp, [ rsp - 0x48 ]
adox rbp, [ rsp + 0x280 ]
mov r11, 0xffffffff00000000 
mov rdx, r8
mov [ rsp + 0x298 ], rbp
mulx rbp, r8, r11
mov r11, [ rsp + 0x278 ]
mov [ rsp + 0x2a0 ], r9
mov r9, 0x0 
adox r11, r9
adcx rcx, [ rsp + 0x260 ]
mov [ rsp + 0x2a8 ], r11
mov r11, -0x3 
inc r11
adox r8, [ rsp + 0x270 ]
mov r9, 0xfffffffffffffffe 
mov [ rsp + 0x2b0 ], r10
mulx r10, r11, r9
adox r11, rbp
mov rdx, r13
adox rdx, r10
mov rbp, r13
adox rbp, r12
adox r13, r12
movzx r10, byte [ rsp + 0x220 ]
lea rbx, [ rbx + r10 ]
mov r10, [ rsp + 0x210 ]
seto r9b
mov [ rsp + 0x2b8 ], r13
movzx r13, byte [ rsp + 0x218 ]
mov [ rsp + 0x2c0 ], rbp
mov rbp, -0x1 
inc rbp
mov rbp, -0x1 
adox r13, rbp
adox r10, [ rsp + 0x178 ]
mov r13, [ rsp + 0x1f0 ]
seto bpl
mov [ rsp + 0x2c8 ], rdx
movzx rdx, byte [ rsp + 0x200 ]
mov byte [ rsp + 0x2d0 ], r15b
mov r15, -0x1 
inc r15
mov r15, -0x1 
adox rdx, r15
adox r13, [ rsp + 0x1f8 ]
mov rdx, [ rsp + 0xa8 ]
setc r15b
mov [ rsp + 0x2d8 ], r11
movzx r11, byte [ rsp + 0x248 ]
clc
mov [ rsp + 0x2e0 ], rcx
mov rcx, -0x1 
adcx r11, rcx
adcx rdx, [ rsp + 0x240 ]
setc r11b
movzx rcx, byte [ rsp + 0x250 ]
clc
mov byte [ rsp + 0x2e8 ], r15b
mov r15, -0x1 
adcx rcx, r15
adcx r13, [ rsp + 0x208 ]
adox rbx, r10
movzx rcx, bpl
mov r10, 0x0 
adox rcx, r10
adcx rdx, rbx
movzx rbp, r9b
lea rbp, [ rbp + r12 ]
movzx r12, r11b
mov r9, [ rsp + 0x238 ]
lea r12, [ r12 + r9 ]
mov r9, -0x3 
inc r9
adox rax, [ rsp + 0x268 ]
adcx r12, rcx
adox r8, rdi
setc al
movzx rdi, byte [ rsp + 0x258 ]
clc
adcx rdi, r15
adcx r13, [ rsp + 0x290 ]
adcx rdx, [ rsp + 0x288 ]
mov rdi, [ rsp + 0x2e0 ]
adox rdi, [ rsp + 0x2d8 ]
movzx r11, byte [ rsp + 0x2d0 ]
lea r14, [ r14 + r11 ]
seto r11b
mov rbx, -0x3 
inc rbx
adox r8, [ rsp + 0x1b8 ]
adcx r14, r12
movzx rbx, al
adcx rbx, r10
mov rcx, 0x100000001 
xchg rdx, r8
mulx r12, rax, rcx
mov r12, 0xfffffffffffffffe 
xchg rdx, r12
mulx r9, r10, rax
adox rdi, [ rsp + 0x1e8 ]
movzx r15, byte [ rsp + 0x2e8 ]
clc
mov rdx, -0x1 
adcx r15, rdx
adcx r13, [ rsp + 0x2b0 ]
adcx r8, [ rsp + 0x2a0 ]
adcx r14, [ rsp + 0x298 ]
adcx rbx, [ rsp + 0x2a8 ]
mov r15, 0xffffffffffffffff 
mov rdx, r15
mulx rcx, r15, rax
mov rdx, 0xffffffff 
mov [ rsp + 0x2f0 ], rcx
mov [ rsp + 0x2f8 ], rdi
mulx rdi, rcx, rax
setc dl
clc
mov [ rsp + 0x300 ], r15
mov r15, -0x1 
movzx r11, r11b
adcx r11, r15
adcx r13, [ rsp + 0x2c8 ]
adcx r8, [ rsp + 0x2c0 ]
adcx r14, [ rsp + 0x2b8 ]
adcx rbp, rbx
movzx r11, dl
mov rbx, 0x0 
adcx r11, rbx
adox r13, [ rsp + 0x1e0 ]
adox r8, [ rsp + 0x1d8 ]
movzx rdx, byte [ rsp + 0x1d0 ]
mov rbx, [ rsp + 0x1a0 ]
lea rdx, [ rdx + rbx ]
adox r14, [ rsp + 0x1c8 ]
adox rbp, [ rsp + 0x1c0 ]
mov rbx, 0xffffffff00000000 
xchg rdx, rbx
mov [ rsp + 0x308 ], rbp
mulx rbp, r15, rax
clc
adcx rcx, r12
seto cl
mov r12, -0x2 
inc r12
adox r15, rdi
adox r10, rbp
adox r9, [ rsp + 0x300 ]
setc al
clc
movzx rcx, cl
adcx rcx, r12
adcx r11, rbx
setc dil
clc
movzx rax, al
adcx rax, r12
adcx r15, [ rsp + 0x2f8 ]
adcx r10, r13
mov r13, [ rsp + 0x2f0 ]
mov rbx, r13
adox rbx, [ rsp + 0x300 ]
mov rcx, r13
adox rcx, [ rsp + 0x300 ]
adcx r9, r8
mov r8, 0x0 
adox r13, r8
adcx rbx, r14
adcx rcx, [ rsp + 0x308 ]
adcx r13, r11
movzx r14, dil
adc r14, 0x0
mov rbp, r15
mov rax, 0xffffffff 
sub rbp, rax
mov r11, r10
sbb r11, rdx
mov rdi, r9
mov r8, 0xfffffffffffffffe 
sbb rdi, r8
mov r12, rbx
mov r8, 0xffffffffffffffff 
sbb r12, r8
mov rdx, rcx
sbb rdx, r8
mov rax, r13
sbb rax, r8
sbb r14, 0x00000000
cmovc rdx, rcx
cmovc rax, r13
cmovc rdi, r9
cmovc r11, r10
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x10 ], rdi
mov [ r14 + 0x8 ], r11
cmovc rbp, r15
mov [ r14 + 0x0 ], rbp
cmovc r12, rbx
mov [ r14 + 0x18 ], r12
mov [ r14 + 0x28 ], rax
mov [ r14 + 0x20 ], rdx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 912
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.0821
; seed 1921764668155774 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4597455 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=65, initial num_batches=31): 116850 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.02541623572171995
; number reverted permutation / tried permutation: 63963 / 89731 =71.283%
; number reverted decision / tried decision: 55558 / 90268 =61.548%
; validated in 24.563s
