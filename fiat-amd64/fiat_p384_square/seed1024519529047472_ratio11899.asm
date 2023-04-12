SECTION .text
	GLOBAL fiat_p384_square
fiat_p384_square:
sub rsp, 856
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mulx r9, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r15
mulx r15, rdi, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x40 ], r15
mov [ rsp - 0x38 ], r14
mulx r14, r15, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], r9
mov [ rsp - 0x28 ], r8
mulx r8, r9, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x20 ], r8
mov [ rsp - 0x18 ], rdi
mulx rdi, r8, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x10 ], rdi
mov [ rsp - 0x8 ], r8
mulx r8, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x0 ], r8
mov [ rsp + 0x8 ], rdi
mulx rdi, r8, [ rsi + 0x28 ]
mov rdx, 0x100000001 
mov [ rsp + 0x10 ], rdi
mov [ rsp + 0x18 ], r8
mulx r8, rdi, rbx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x20 ], r14
mulx r14, r8, [ rsi + 0x8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x28 ], r15
mov [ rsp + 0x30 ], r9
mulx r9, r15, rdi
test al, al
adox r8, rbp
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x38 ], r9
mulx r9, rbp, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x40 ], r9
mov [ rsp + 0x48 ], r8
mulx r8, r9, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x50 ], rbp
mov [ rsp + 0x58 ], r8
mulx r8, rbp, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x60 ], r9
mov [ rsp + 0x68 ], r15
mulx r15, r9, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x70 ], r8
mov [ rsp + 0x78 ], rbp
mulx rbp, r8, [ rsi + 0x0 ]
adcx r9, rbp
adcx rax, r15
mov rdx, [ rsi + 0x28 ]
mulx rbp, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x80 ], r15
mov [ rsp + 0x88 ], rax
mulx rax, r15, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x90 ], rax
mov [ rsp + 0x98 ], r9
mulx r9, rax, [ rsi + 0x18 ]
mov rdx, 0xffffffff 
mov [ rsp + 0xa0 ], rax
mov [ rsp + 0xa8 ], r8
mulx r8, rax, rdi
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xb0 ], r15
mov [ rsp + 0xb8 ], rbp
mulx rbp, r15, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xc0 ], r9
mov [ rsp + 0xc8 ], rax
mulx rax, r9, [ rsi + 0x10 ]
adox r15, r14
mov rdx, 0xffffffff00000000 
mov [ rsp + 0xd0 ], r15
mulx r15, r14, rdi
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xd8 ], rax
mov [ rsp + 0xe0 ], r9
mulx r9, rax, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xe8 ], r9
mov [ rsp + 0xf0 ], rax
mulx rax, r9, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xf8 ], r9
mov [ rsp + 0x100 ], rax
mulx rax, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x108 ], r15
mov [ rsp + 0x110 ], rcx
mulx rcx, r15, [ rsi + 0x8 ]
adox r9, rbp
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x118 ], r9
mulx r9, rbp, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x120 ], rcx
mov [ rsp + 0x128 ], r15
mulx r15, rcx, [ rsi + 0x20 ]
adox rbp, rax
adox r12, r9
adcx r11, r10
mov rdx, 0x0 
adox r13, rdx
mov r10, 0xfffffffffffffffe 
mov rdx, rdi
mulx rax, rdi, r10
mov rdx, -0x2 
inc rdx
adox r14, r8
adcx rcx, [ rsp + 0x110 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x130 ], rcx
mulx rcx, r10, [ rsi + 0x8 ]
adox rdi, [ rsp + 0x108 ]
seto dl
mov [ rsp + 0x138 ], r13
mov r13, -0x2 
inc r13
adox rbx, [ rsp + 0xc8 ]
mov rbx, [ rsp + 0x78 ]
seto r13b
mov [ rsp + 0x140 ], r12
mov r12, -0x2 
inc r12
adox rbx, [ rsp + 0xc0 ]
mov r12b, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x148 ], rbx
mov [ rsp + 0x150 ], r11
mulx r11, rbx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x158 ], rbp
mov [ rsp + 0x160 ], rdi
mulx rdi, rbp, [ rsi + 0x0 ]
seto dl
mov [ rsp + 0x168 ], rbp
mov rbp, -0x2 
inc rbp
adox r10, rdi
adox rcx, [ rsp + 0x30 ]
setc dil
clc
movzx rdx, dl
adcx rdx, rbp
adcx rbx, [ rsp + 0x70 ]
seto dl
inc rbp
mov rbp, -0x1 
movzx rdi, dil
adox rdi, rbp
adox r15, [ rsp + 0x28 ]
adcx r8, r11
mov rdi, [ rsp + 0x20 ]
mov r11, 0x0 
adox rdi, r11
mov rbp, [ rsp + 0x100 ]
mov [ rsp + 0x170 ], r8
mov r8, -0x3 
inc r8
adox rbp, [ rsp + 0x128 ]
mov r11, [ rsp + 0x120 ]
adox r11, [ rsp + 0x8 ]
mov r8, [ rsp + 0x0 ]
adox r8, [ rsp - 0x18 ]
adcx r9, [ rsp - 0x28 ]
mov [ rsp + 0x178 ], r8
mov r8, [ rsp - 0x30 ]
adcx r8, [ rsp + 0x18 ]
mov [ rsp + 0x180 ], r11
seto r11b
mov [ rsp + 0x188 ], rbp
mov rbp, -0x1 
inc rbp
mov rbp, -0x1 
movzx r12, r12b
adox r12, rbp
adox rax, [ rsp + 0x68 ]
mov r12b, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x190 ], r8
mulx r8, rbp, [ rsi + 0x20 ]
mov rdx, [ rsp + 0xb8 ]
mov [ rsp + 0x198 ], r9
seto r9b
mov [ rsp + 0x1a0 ], rbx
mov rbx, -0x2 
inc rbx
adox rdx, [ rsp - 0x8 ]
mov rbx, [ rsp - 0x10 ]
adox rbx, [ rsp + 0xe0 ]
mov [ rsp + 0x1a8 ], rbx
mov rbx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x1b0 ], rdi
mov [ rsp + 0x1b8 ], rcx
mulx rcx, rdi, rdx
mov rdx, [ rsp + 0xd8 ]
adox rdx, [ rsp + 0x60 ]
mov [ rsp + 0x1c0 ], rbx
mov rbx, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x1c8 ], r10
mov [ rsp + 0x1d0 ], r15
mulx r15, r10, rdx
mov rdx, [ rsp + 0x10 ]
mov [ rsp + 0x1d8 ], rbx
mov rbx, 0x0 
adcx rdx, rbx
mov rbx, [ rsp + 0x58 ]
adox rbx, [ rsp - 0x38 ]
adox r10, [ rsp - 0x48 ]
mov [ rsp + 0x1e0 ], r10
mov r10, [ rsp + 0xf0 ]
clc
mov [ rsp + 0x1e8 ], rbx
mov rbx, -0x1 
movzx r12, r12b
adcx r12, rbx
adcx r10, [ rsp - 0x20 ]
adcx rbp, [ rsp + 0xe8 ]
setc r12b
clc
movzx r11, r11b
adcx r11, rbx
adcx rdi, [ rsp - 0x40 ]
adcx rcx, [ rsp + 0x50 ]
setc r11b
clc
movzx r13, r13b
adcx r13, rbx
adcx r14, [ rsp + 0x48 ]
mov r13, [ rsp + 0xd0 ]
adcx r13, [ rsp + 0x160 ]
mov rbx, [ rsp + 0x38 ]
mov [ rsp + 0x1f0 ], rcx
mov rcx, rbx
mov [ rsp + 0x1f8 ], rdi
seto dil
mov [ rsp + 0x200 ], rdx
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
movzx r9, r9b
adox r9, rdx
adox rcx, [ rsp + 0x68 ]
mov r9, rbx
adox r9, [ rsp + 0x68 ]
seto dl
mov [ rsp + 0x208 ], rbp
mov rbp, -0x1 
inc rbp
mov rbp, -0x1 
movzx r12, r12b
adox r12, rbp
adox r8, [ rsp + 0xb0 ]
setc r12b
clc
adcx r14, [ rsp + 0xa8 ]
adcx r13, [ rsp + 0x98 ]
seto bpl
mov [ rsp + 0x210 ], r8
mov r8, -0x1 
inc r8
mov r8, -0x1 
movzx r12, r12b
adox r12, r8
adox rax, [ rsp + 0x118 ]
movzx r12, dil
lea r12, [ r12 + r15 ]
movzx r15, bpl
mov rdi, [ rsp + 0x90 ]
lea r15, [ r15 + rdi ]
adox rcx, [ rsp + 0x158 ]
adcx rax, [ rsp + 0x88 ]
movzx rdi, r11b
mov rbp, [ rsp + 0x40 ]
lea rdi, [ rdi + rbp ]
adcx rcx, [ rsp + 0x150 ]
adox r9, [ rsp + 0x140 ]
movzx rbp, dl
lea rbp, [ rbp + rbx ]
adox rbp, [ rsp + 0x138 ]
adcx r9, [ rsp + 0x130 ]
adcx rbp, [ rsp + 0x1d0 ]
mov rbx, 0x100000001 
mov rdx, rbx
mulx r11, rbx, r14
mov r11, 0xfffffffffffffffe 
mov rdx, r11
mulx r8, r11, rbx
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x218 ], r12
mov [ rsp + 0x220 ], rdi
mulx rdi, r12, rbx
mov rdx, 0xffffffff 
mov [ rsp + 0x228 ], r15
mov [ rsp + 0x230 ], rbp
mulx rbp, r15, rbx
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x238 ], r10
mov [ rsp + 0x240 ], r9
mulx r9, r10, rbx
setc bl
clc
adcx r15, r14
seto r15b
mov r14, -0x2 
inc r14
adox r10, rbp
adox r11, r9
adcx r10, r13
adcx r11, rax
mov r13, r12
adox r13, r8
mov rax, r12
adox rax, rdi
adox r12, rdi
seto r8b
inc r14
adox r10, [ rsp + 0x168 ]
adox r11, [ rsp + 0x1c8 ]
adcx r13, rcx
adox r13, [ rsp + 0x1b8 ]
mov rcx, 0x100000001 
mov rdx, rcx
mulx rbp, rcx, r10
mov rbp, 0xffffffff 
mov rdx, rcx
mulx r9, rcx, rbp
adcx rax, [ rsp + 0x240 ]
adcx r12, [ rsp + 0x230 ]
mov r14, 0xfffffffffffffffe 
mov [ rsp + 0x248 ], r12
mulx r12, rbp, r14
adox rax, [ rsp + 0x238 ]
mov r14, 0xffffffff00000000 
mov [ rsp + 0x250 ], rax
mov [ rsp + 0x258 ], r12
mulx r12, rax, r14
seto r14b
mov [ rsp + 0x260 ], r13
mov r13, -0x2 
inc r13
adox rax, r9
setc r9b
clc
adcx rcx, r10
adcx rax, r11
movzx rcx, r15b
seto r10b
inc r13
mov r11, -0x1 
movzx rbx, bl
adox rbx, r11
adox rcx, [ rsp + 0x1b0 ]
movzx r15, r8b
lea r15, [ r15 + rdi ]
setc bl
clc
adcx rax, [ rsp + 0xa0 ]
seto dil
dec r13
movzx r10, r10b
adox r10, r13
adox r12, rbp
seto r11b
inc r13
mov r8, -0x1 
movzx r9, r9b
adox r9, r8
adox rcx, r15
setc r9b
clc
movzx rbx, bl
adcx rbx, r8
adcx r12, [ rsp + 0x260 ]
movzx rbp, dil
adox rbp, r13
mov r10, 0xffffffffffffffff 
mulx rdi, rbx, r10
inc r8
mov r13, -0x1 
movzx r9, r9b
adox r9, r13
adox r12, [ rsp + 0x148 ]
mov rdx, [ rsp + 0x208 ]
seto r15b
dec r8
movzx r14, r14b
adox r14, r8
adox rdx, [ rsp + 0x248 ]
adox rcx, [ rsp + 0x210 ]
mov r13, rbx
seto r14b
inc r8
mov r9, -0x1 
movzx r11, r11b
adox r11, r9
adox r13, [ rsp + 0x258 ]
mov r11, rbx
adox r11, rdi
mov r8, 0x100000001 
xchg rdx, r8
mulx r10, r9, rax
mov r10, 0xffffffff00000000 
mov rdx, r10
mov [ rsp + 0x268 ], r12
mulx r12, r10, r9
adox rbx, rdi
mov rdx, 0xffffffff 
mov [ rsp + 0x270 ], r12
mov [ rsp + 0x278 ], r10
mulx r10, r12, r9
mov rdx, 0x0 
adox rdi, rdx
adcx r13, [ rsp + 0x250 ]
mov [ rsp + 0x280 ], r10
mov r10, -0x3 
inc r10
adox r12, rax
adcx r11, r8
adcx rbx, rcx
setc r12b
clc
mov rax, -0x1 
movzx r15, r15b
adcx r15, rax
adcx r13, [ rsp + 0x1a0 ]
adcx r11, [ rsp + 0x170 ]
setc r15b
clc
movzx r14, r14b
adcx r14, rax
adcx rbp, [ rsp + 0x228 ]
seto r8b
dec rdx
movzx r12, r12b
adox r12, rdx
adox rbp, rdi
setc al
clc
movzx r15, r15b
adcx r15, rdx
adcx rbx, [ rsp + 0x198 ]
mov r14, 0xfffffffffffffffe 
mov rdx, r14
mulx rcx, r14, r9
adcx rbp, [ rsp + 0x190 ]
mov rdi, 0xffffffffffffffff 
mov rdx, rdi
mulx r12, rdi, r9
mov r9, [ rsp + 0x280 ]
seto r15b
inc r10
adox r9, [ rsp + 0x278 ]
adox r14, [ rsp + 0x270 ]
mov r10, rdi
adox r10, rcx
mov rcx, rdi
adox rcx, r12
adox rdi, r12
mov rdx, 0x0 
adox r12, rdx
dec rdx
movzx r8, r8b
adox r8, rdx
adox r9, [ rsp + 0x268 ]
adox r14, r13
adox r10, r11
movzx r8, r15b
movzx rax, al
lea r8, [ r8 + rax ]
adcx r8, [ rsp + 0x200 ]
adox rcx, rbx
setc r13b
clc
adcx r9, [ rsp + 0xf8 ]
mov r11, 0x100000001 
mov rdx, r11
mulx rax, r11, r9
adox rdi, rbp
adcx r14, [ rsp + 0x188 ]
mov rax, 0xffffffff00000000 
mov rdx, rax
mulx r15, rax, r11
adcx r10, [ rsp + 0x180 ]
mov rbx, 0xffffffff 
mov rdx, rbx
mulx rbp, rbx, r11
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x288 ], r10
mov [ rsp + 0x290 ], r14
mulx r14, r10, r11
adcx rcx, [ rsp + 0x178 ]
adox r12, r8
adcx rdi, [ rsp + 0x1f8 ]
adcx r12, [ rsp + 0x1f0 ]
movzx r8, r13b
mov rdx, 0x0 
adox r8, rdx
mov r13, -0x3 
inc r13
adox rax, rbp
adox r10, r15
setc r15b
clc
adcx rbx, r9
adcx rax, [ rsp + 0x290 ]
mov rbx, 0xffffffffffffffff 
mov rdx, r11
mulx r9, r11, rbx
mov rdx, r11
adox rdx, r14
seto bpl
inc r13
adox rax, [ rsp + 0x80 ]
setc r14b
clc
movzx r15, r15b
adcx r15, r13
adcx r8, [ rsp + 0x220 ]
mov r15, 0x100000001 
xchg rdx, r15
mulx rbx, r13, rax
mov rbx, 0xffffffff00000000 
mov rdx, r13
mov [ rsp + 0x298 ], r8
mulx r8, r13, rbx
mov rbx, r9
mov [ rsp + 0x2a0 ], r8
setc r8b
clc
mov [ rsp + 0x2a8 ], r12
mov r12, -0x1 
movzx rbp, bpl
adcx rbp, r12
adcx rbx, r11
mov rbp, 0xffffffff 
mov byte [ rsp + 0x2b0 ], r8b
mulx r8, r12, rbp
adcx r11, r9
setc bpl
clc
mov [ rsp + 0x2b8 ], r12
mov r12, -0x1 
movzx r14, r14b
adcx r14, r12
adcx r10, [ rsp + 0x288 ]
mov r14, 0xffffffffffffffff 
mov [ rsp + 0x2c0 ], r11
mulx r11, r12, r14
seto r14b
mov [ rsp + 0x2c8 ], r11
mov r11, -0x2 
inc r11
adox r13, r8
adcx r15, rcx
adcx rbx, rdi
setc cl
clc
movzx r14, r14b
adcx r14, r11
adcx r10, [ rsp + 0x1c0 ]
adcx r15, [ rsp + 0x1a8 ]
movzx rdi, bpl
lea rdi, [ rdi + r9 ]
mov r9, [ rsp + 0x2a8 ]
setc r14b
clc
movzx rcx, cl
adcx rcx, r11
adcx r9, [ rsp + 0x2c0 ]
adcx rdi, [ rsp + 0x298 ]
mov r8, 0xfffffffffffffffe 
mulx rcx, rbp, r8
adox rbp, [ rsp + 0x2a0 ]
movzx rdx, byte [ rsp + 0x2b0 ]
mov r11, 0x0 
adcx rdx, r11
clc
adcx rax, [ rsp + 0x2b8 ]
adcx r13, r10
mov rax, r12
adox rax, rcx
mov r10, r12
adox r10, [ rsp + 0x2c8 ]
adox r12, [ rsp + 0x2c8 ]
seto cl
dec r11
movzx r14, r14b
adox r14, r11
adox rbx, [ rsp + 0x1d8 ]
movzx r14, cl
mov r11, [ rsp + 0x2c8 ]
lea r14, [ r14 + r11 ]
adox r9, [ rsp + 0x1e8 ]
adox rdi, [ rsp + 0x1e0 ]
adcx rbp, r15
adox rdx, [ rsp + 0x218 ]
adcx rax, rbx
adcx r10, r9
setc r11b
seto r15b
mov rcx, r13
mov rbx, 0xffffffff 
sub rcx, rbx
mov r9, rbp
mov rbx, 0xffffffff00000000 
sbb r9, rbx
mov rbx, rax
sbb rbx, r8
mov r8, r10
mov [ rsp + 0x2d0 ], rcx
mov rcx, 0xffffffffffffffff 
sbb r8, rcx
mov rcx, 0x0 
dec rcx
movzx r11, r11b
adox r11, rcx
adox rdi, r12
adox r14, rdx
movzx r12, r15b
mov rdx, 0x0 
adox r12, rdx
mov r15, rdi
mov r11, 0xffffffffffffffff 
sbb r15, r11
mov rdx, r14
sbb rdx, r11
sbb r12, 0x00000000
cmovc rbx, rax
cmovc r9, rbp
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x8 ], r9
cmovc r15, rdi
mov [ r12 + 0x20 ], r15
cmovc r8, r10
mov [ r12 + 0x18 ], r8
cmovc rdx, r14
mov rbp, [ rsp + 0x2d0 ]
cmovc rbp, r13
mov [ r12 + 0x0 ], rbp
mov [ r12 + 0x10 ], rbx
mov [ r12 + 0x28 ], rdx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 856
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.1899
; seed 1024519529047472 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 26685 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=80, initial num_batches=31): 766 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.028705265130222972
; number reverted permutation / tried permutation: 311 / 497 =62.575%
; number reverted decision / tried decision: 292 / 502 =58.167%
; validated in 21.774s
