SECTION .text
	GLOBAL fiat_p384_square
fiat_p384_square:
sub rsp, 848
mov rdx, [ rsi + 0x28 ]
mulx r10, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r10
mulx r10, rdi, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x40 ], rax
mov [ rsp - 0x38 ], r10
mulx r10, rax, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x30 ], r10
mov [ rsp - 0x28 ], rax
mulx rax, r10, rdx
mov rdx, 0x100000001 
mov [ rsp - 0x20 ], rdi
mov [ rsp - 0x18 ], r9
mulx r9, rdi, r10
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], r8
mulx r8, r9, [ rsi + 0x0 ]
mov rdx, 0xfffffffffffffffe 
mov [ rsp - 0x8 ], r9
mov [ rsp + 0x0 ], r15
mulx r15, r9, rdi
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x8 ], r14
mov [ rsp + 0x10 ], r13
mulx r13, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x18 ], r13
mov [ rsp + 0x20 ], r14
mulx r14, r13, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x28 ], r14
mov [ rsp + 0x30 ], r13
mulx r13, r14, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x38 ], r13
mov [ rsp + 0x40 ], r14
mulx r14, r13, rdi
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x48 ], r12
mov [ rsp + 0x50 ], rcx
mulx rcx, r12, rdi
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x58 ], r11
mov [ rsp + 0x60 ], rbp
mulx rbp, r11, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x68 ], rbp
mov [ rsp + 0x70 ], r11
mulx r11, rbp, [ rsi + 0x28 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x78 ], r11
mov [ rsp + 0x80 ], rbp
mulx rbp, r11, rdi
add r12, rbp
adcx r9, rcx
mov rdx, [ rsi + 0x28 ]
mulx rcx, rdi, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x88 ], rcx
mulx rcx, rbp, [ rsi + 0x18 ]
mov rdx, r13
adcx rdx, r15
mov r15, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x90 ], rdi
mov [ rsp + 0x98 ], rcx
mulx rcx, rdi, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xa0 ], rbp
mov [ rsp + 0xa8 ], r15
mulx r15, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xb0 ], r15
mov [ rsp + 0xb8 ], rbx
mulx rbx, r15, [ rsi + 0x10 ]
mov rdx, -0x2 
inc rdx
adox rdi, rax
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xc0 ], rbx
mulx rbx, rax, [ rsi + 0x8 ]
setc dl
clc
adcx rax, r8
setc r8b
clc
adcx r11, r10
adcx r12, rdi
mov r11b, dl
mov rdx, [ rsi + 0x20 ]
mulx rdi, r10, [ rsi + 0x18 ]
adox rbp, rcx
adcx r9, rbp
mov rdx, r14
setc cl
clc
mov rbp, -0x1 
movzx r11, r11b
adcx r11, rbp
adcx rdx, r13
mov r11, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xc8 ], rdi
mulx rdi, rbp, [ rsi + 0x10 ]
adcx r13, r14
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xd0 ], r10
mov [ rsp + 0xd8 ], rbx
mulx rbx, r10, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov byte [ rsp + 0xe0 ], r8b
mov [ rsp + 0xe8 ], rax
mulx rax, r8, [ rsi + 0x8 ]
seto dl
mov [ rsp + 0xf0 ], r13
mov r13, -0x2 
inc r13
adox r8, r12
mov r12b, dl
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xf8 ], r9
mulx r9, r13, [ rsi + 0x10 ]
mov rdx, 0x100000001 
mov [ rsp + 0x100 ], r13
mov [ rsp + 0x108 ], r11
mulx r11, r13, r8
mov r11, 0xfffffffffffffffe 
mov rdx, r11
mov byte [ rsp + 0x110 ], cl
mulx rcx, r11, r13
setc dl
clc
adcx rbp, r9
mov r9, 0xffffffff 
xchg rdx, r9
mov [ rsp + 0x118 ], rbp
mov byte [ rsp + 0x120 ], r9b
mulx r9, rbp, r13
adcx rdi, [ rsp + 0xb8 ]
mov rdx, [ rsp + 0x60 ]
adcx rdx, [ rsp + 0x58 ]
adcx r10, [ rsp + 0x50 ]
mov [ rsp + 0x128 ], r10
mov r10, 0xffffffffffffffff 
xchg rdx, r13
mov [ rsp + 0x130 ], r13
mov [ rsp + 0x138 ], rdi
mulx rdi, r13, r10
adcx r15, rbx
mov rbx, 0xffffffff00000000 
mov [ rsp + 0x140 ], r15
mulx r15, r10, rbx
seto dl
mov rbx, -0x2 
inc rbx
adox rax, [ rsp + 0x70 ]
mov rbx, [ rsp + 0x48 ]
adox rbx, [ rsp + 0x68 ]
mov [ rsp + 0x148 ], rbp
setc bpl
clc
adcx r10, r9
mov r9b, dl
mov rdx, [ rsi + 0x28 ]
mov byte [ rsp + 0x150 ], bpl
mov [ rsp + 0x158 ], r10
mulx r10, rbp, [ rsi + 0x0 ]
adcx r11, r15
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x160 ], r11
mulx r11, r15, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x168 ], r11
mov [ rsp + 0x170 ], rbx
mulx rbx, r11, [ rsi + 0x18 ]
mov rdx, r13
adcx rdx, rcx
mov rcx, r13
adcx rcx, rdi
adox r11, [ rsp + 0x10 ]
mov [ rsp + 0x178 ], rcx
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x180 ], r11
mov [ rsp + 0x188 ], rax
mulx rax, r11, [ rsi + 0x18 ]
adcx r13, rdi
setc dl
clc
mov [ rsp + 0x190 ], r13
mov r13, -0x1 
movzx r12, r12b
adcx r12, r13
adcx r11, [ rsp + 0xb0 ]
adcx rax, [ rsp + 0x8 ]
adcx rbp, [ rsp + 0x0 ]
adox r15, rbx
mov r12, 0x0 
adcx r10, r12
movzx rbx, byte [ rsp + 0x110 ]
clc
adcx rbx, r13
adcx r11, [ rsp + 0xa8 ]
adcx rax, [ rsp + 0x108 ]
mov rbx, [ rsp + 0x188 ]
seto r12b
inc r13
mov r13, -0x1 
movzx r9, r9b
adox r9, r13
adox rbx, [ rsp + 0xf8 ]
movzx r9, byte [ rsp + 0x120 ]
lea r14, [ r14 + r9 ]
adcx rbp, [ rsp + 0xf0 ]
adox r11, [ rsp + 0x170 ]
adox rax, [ rsp + 0x180 ]
adox r15, rbp
movzx r9, dl
lea r9, [ r9 + rdi ]
adcx r14, r10
seto dil
inc r13
adox r8, [ rsp + 0x148 ]
adox rbx, [ rsp + 0x158 ]
adox r11, [ rsp + 0x160 ]
adox rcx, rax
adox r15, [ rsp + 0x178 ]
setc r8b
clc
adcx rbx, [ rsp + 0x100 ]
mov rdx, 0x100000001 
mulx rbp, r10, rbx
adcx r11, [ rsp + 0x118 ]
mov rbp, 0xffffffff00000000 
mov rdx, rbp
mulx rax, rbp, r10
mov r13, 0xffffffff 
mov rdx, r10
mov [ rsp + 0x198 ], r9
mulx r9, r10, r13
mov r13, 0xffffffffffffffff 
mov byte [ rsp + 0x1a0 ], r8b
mov [ rsp + 0x1a8 ], r14
mulx r14, r8, r13
mov r13, 0xfffffffffffffffe 
mov byte [ rsp + 0x1b0 ], dil
mov byte [ rsp + 0x1b8 ], r12b
mulx r12, rdi, r13
adcx rcx, [ rsp + 0x138 ]
seto dl
mov r13, -0x2 
inc r13
adox r10, rbx
adcx r15, [ rsp + 0x130 ]
setc r10b
clc
adcx rbp, r9
adcx rdi, rax
mov rbx, r8
adcx rbx, r12
mov rax, r8
adcx rax, r14
adox rbp, r11
adox rdi, rcx
setc r11b
clc
adcx rbp, [ rsp - 0x8 ]
adox rbx, r15
mov r9, 0x100000001 
xchg rdx, r9
mulx rcx, r12, rbp
mov rdx, [ rsi + 0x28 ]
mulx r15, rcx, [ rsi + 0x8 ]
seto dl
movzx r13, byte [ rsp + 0x1b8 ]
mov [ rsp + 0x1c0 ], rax
mov rax, 0x0 
dec rax
adox r13, rax
adox rcx, [ rsp + 0x168 ]
mov r13, 0xffffffff00000000 
xchg rdx, r12
mov byte [ rsp + 0x1c8 ], r12b
mulx r12, rax, r13
adcx rdi, [ rsp + 0xe8 ]
mov r13, 0xffffffff 
mov [ rsp + 0x1d0 ], rdi
mov [ rsp + 0x1d8 ], r12
mulx r12, rdi, r13
mov r13, [ rsp + 0xd8 ]
mov [ rsp + 0x1e0 ], rax
seto al
mov [ rsp + 0x1e8 ], r12
movzx r12, byte [ rsp + 0xe0 ]
mov [ rsp + 0x1f0 ], rdi
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
adox r12, rdi
adox r13, [ rsp - 0x10 ]
mov r12, [ rsp + 0x40 ]
adox r12, [ rsp - 0x18 ]
mov rdi, [ rsp + 0x38 ]
adox rdi, [ rsp + 0xa0 ]
adcx r13, rbx
mov rbx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x1f8 ], rdi
mov [ rsp + 0x200 ], r13
mulx r13, rdi, [ rsi + 0x8 ]
mov rdx, [ rsp + 0x90 ]
adox rdx, [ rsp + 0x98 ]
mov [ rsp + 0x208 ], r12
mov r12, rdx
mov rdx, [ rsi + 0x0 ]
mov byte [ rsp + 0x210 ], r11b
mov byte [ rsp + 0x218 ], r10b
mulx r10, r11, [ rsi + 0x20 ]
setc dl
clc
adcx rdi, r10
adcx r13, [ rsp + 0x30 ]
mov r10, [ rsp + 0x28 ]
adcx r10, [ rsp + 0xd0 ]
mov [ rsp + 0x220 ], r10
seto r10b
mov [ rsp + 0x228 ], r13
movzx r13, byte [ rsp + 0x1b0 ]
mov [ rsp + 0x230 ], rdi
mov rdi, 0x0 
dec rdi
adox r13, rdi
adox rcx, [ rsp + 0x1a8 ]
movzx r13, al
lea r13, [ r13 + r15 ]
movzx r15, byte [ rsp + 0x1a0 ]
adox r15, r13
mov al, dl
mov rdx, [ rsi + 0x20 ]
mulx rdi, r13, [ rsi + 0x28 ]
seto dl
mov [ rsp + 0x238 ], r12
mov r12, 0x0 
dec r12
movzx r9, r9b
adox r9, r12
adox rcx, [ rsp + 0x190 ]
adox r15, [ rsp + 0x198 ]
mov r9, [ rsp + 0xc8 ]
adcx r9, [ rsp - 0x20 ]
adcx r13, [ rsp - 0x38 ]
movzx r12, byte [ rsp + 0x150 ]
mov [ rsp + 0x240 ], r13
mov r13, [ rsp + 0xc0 ]
lea r12, [ r12 + r13 ]
setc r13b
mov [ rsp + 0x248 ], r9
movzx r9, byte [ rsp + 0x218 ]
clc
mov byte [ rsp + 0x250 ], r10b
mov r10, -0x1 
adcx r9, r10
adcx rcx, [ rsp + 0x128 ]
adcx r15, [ rsp + 0x140 ]
movzx r9, r13b
lea r9, [ r9 + rdi ]
movzx rdi, dl
mov r13, 0x0 
adox rdi, r13
adcx r12, rdi
mov rdx, r14
movzx rdi, byte [ rsp + 0x210 ]
dec r13
adox rdi, r13
adox rdx, r8
setc r10b
movzx r8, byte [ rsp + 0x1c8 ]
clc
adcx r8, r13
adcx rcx, [ rsp + 0x1c0 ]
mov rdi, 0x0 
adox r14, rdi
dec rdi
movzx rax, al
adox rax, rdi
adox rcx, [ rsp + 0x208 ]
adcx rdx, r15
seto r13b
inc rdi
adox rbp, [ rsp + 0x1f0 ]
adcx r14, r12
movzx rbp, r10b
adcx rbp, rdi
mov r8, [ rsp + 0x1e8 ]
clc
adcx r8, [ rsp + 0x1e0 ]
mov rax, 0xfffffffffffffffe 
xchg rdx, rax
mulx r10, r15, rbx
mov r12, 0xffffffffffffffff 
mov rdx, rbx
mulx rdi, rbx, r12
adcx r15, [ rsp + 0x1d8 ]
adox r8, [ rsp + 0x1d0 ]
adox r15, [ rsp + 0x200 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x258 ], r9
mulx r9, r12, rdx
mov rdx, rbx
adcx rdx, r10
mov r10, rbx
adcx r10, rdi
adcx rbx, rdi
mov [ rsp + 0x260 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x268 ], r9
mov [ rsp + 0x270 ], r12
mulx r12, r9, [ rsi + 0x0 ]
adox r15, rcx
mov rdx, 0x0 
adcx rdi, rdx
clc
adcx r11, r8
mov rcx, 0x100000001 
mov rdx, r11
mulx r8, r11, rcx
mov r8, 0xfffffffffffffffe 
xchg rdx, r11
mov [ rsp + 0x278 ], r9
mulx r9, rcx, r8
movzx r8, byte [ rsp + 0x250 ]
mov [ rsp + 0x280 ], r15
mov r15, [ rsp + 0x88 ]
lea r8, [ r8 + r15 ]
seto r15b
mov [ rsp + 0x288 ], rdi
mov rdi, 0x0 
dec rdi
movzx r13, r13b
adox r13, rdi
adox rax, [ rsp + 0x1f8 ]
setc r13b
clc
adcx r12, [ rsp - 0x40 ]
mov rdi, [ rsp + 0x20 ]
adcx rdi, [ rsp - 0x48 ]
mov [ rsp + 0x290 ], rdi
mov rdi, [ rsp + 0x80 ]
adcx rdi, [ rsp + 0x18 ]
mov [ rsp + 0x298 ], rdi
mov rdi, [ rsp + 0x78 ]
adcx rdi, [ rsp - 0x28 ]
adox r14, [ rsp + 0x238 ]
adox r8, rbp
seto bpl
mov [ rsp + 0x2a0 ], rdi
mov rdi, 0x0 
dec rdi
movzx r15, r15b
adox r15, rdi
adox rax, r10
adox rbx, r14
mov r10, [ rsp - 0x30 ]
adcx r10, [ rsp + 0x270 ]
mov r15, 0xffffffff 
mulx rdi, r14, r15
mov r15, [ rsp + 0x268 ]
mov [ rsp + 0x2a8 ], r10
mov r10, 0x0 
adcx r15, r10
mov r10, 0xffffffff00000000 
mov [ rsp + 0x2b0 ], r15
mov [ rsp + 0x2b8 ], r12
mulx r12, r15, r10
clc
adcx r15, rdi
adcx rcx, r12
mov rdi, 0xffffffffffffffff 
mulx r10, r12, rdi
mov rdx, r12
adcx rdx, r9
mov r9, r12
adcx r9, r10
adcx r12, r10
adox r8, [ rsp + 0x288 ]
movzx rdi, bpl
mov [ rsp + 0x2c0 ], r12
mov r12, 0x0 
adox rdi, r12
adc r10, 0x0
mov rbp, [ rsp + 0x260 ]
add r13b, 0xFF
adcx rbp, [ rsp + 0x230 ]
mov r13, [ rsp + 0x280 ]
adcx r13, [ rsp + 0x228 ]
adcx rax, [ rsp + 0x220 ]
adcx rbx, [ rsp + 0x248 ]
adox r14, r11
adox r15, rbp
adox rcx, r13
adox rdx, rax
seto r14b
mov r11, -0x3 
inc r11
adox r15, [ rsp + 0x278 ]
adox rcx, [ rsp + 0x2b8 ]
adox rdx, [ rsp + 0x290 ]
adcx r8, [ rsp + 0x240 ]
mov rbp, 0x100000001 
xchg rdx, rbp
mulx rax, r13, r15
adcx rdi, [ rsp + 0x258 ]
mov rax, 0xfffffffffffffffe 
mov rdx, rax
mulx r12, rax, r13
setc r11b
clc
mov rdx, -0x1 
movzx r14, r14b
adcx r14, rdx
adcx rbx, r9
adcx r8, [ rsp + 0x2c0 ]
adox rbx, [ rsp + 0x298 ]
adox r8, [ rsp + 0x2a0 ]
adcx r10, rdi
adox r10, [ rsp + 0x2a8 ]
movzx r9, r11b
mov r14, 0x0 
adcx r9, r14
adox r9, [ rsp + 0x2b0 ]
mov r11, 0xffffffff 
mov rdx, r11
mulx rdi, r11, r13
mov r14, 0xffffffffffffffff 
mov rdx, r14
mov [ rsp + 0x2c8 ], r9
mulx r9, r14, r13
clc
adcx r11, r15
mov r11, 0xffffffff00000000 
mov rdx, r13
mulx r15, r13, r11
seto dl
mov r11, -0x2 
inc r11
adox r13, rdi
adox rax, r15
mov rdi, r14
adox rdi, r12
mov r12, r14
adox r12, r9
adox r14, r9
mov r15, 0x0 
adox r9, r15
adcx r13, rcx
adcx rax, rbp
setc cl
mov rbp, r13
mov r11, 0xffffffff 
sub rbp, r11
dec r15
movzx rcx, cl
adox rcx, r15
adox rbx, rdi
adox r12, r8
adox r14, r10
adox r9, [ rsp + 0x2c8 ]
seto r8b
mov r10, rax
mov rdi, 0xffffffff00000000 
sbb r10, rdi
mov rcx, rbx
mov r15, 0xfffffffffffffffe 
sbb rcx, r15
movzx rdi, r8b
movzx rdx, dl
lea rdi, [ rdi + rdx ]
mov rdx, r12
mov r8, 0xffffffffffffffff 
sbb rdx, r8
mov r11, r14
sbb r11, r8
mov r15, r9
sbb r15, r8
sbb rdi, 0x00000000
cmovc r11, r14
cmovc rbp, r13
cmovc rdx, r12
cmovc rcx, rbx
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x10 ], rcx
cmovc r15, r9
cmovc r10, rax
mov [ rdi + 0x8 ], r10
mov [ rdi + 0x18 ], rdx
mov [ rdi + 0x28 ], r15
mov [ rdi + 0x0 ], rbp
mov [ rdi + 0x20 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 848
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.2347
; seed 0533096915742524 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5486838 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=59, initial num_batches=31): 142471 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.025965957077646543
; number reverted permutation / tried permutation: 62672 / 89911 =69.704%
; number reverted decision / tried decision: 49188 / 90088 =54.600%
; validated in 32.269s
