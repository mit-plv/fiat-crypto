SECTION .text
	GLOBAL fiat_p384_mul
fiat_p384_mul:
sub rsp, 776
mov rax, rdx
mov rdx, [ rdx + 0x10 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mulx r8, rcx, [ rax + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x28 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x48 ], rcx
mov [ rsp - 0x40 ], r8
mulx r8, rcx, [ rsi + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x38 ], r8
mov [ rsp - 0x30 ], rbx
mulx rbx, r8, [ rsi + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x28 ], r9
mov [ rsp - 0x20 ], rdi
mulx rdi, r9, [ rsi + 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x18 ], rdi
mov [ rsp - 0x10 ], r9
mulx r9, rdi, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x8 ], rcx
mov [ rsp + 0x0 ], r15
mulx r15, rcx, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x8 ], r15
mov [ rsp + 0x10 ], rcx
mulx rcx, r15, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x18 ], rcx
mov [ rsp + 0x20 ], r15
mulx r15, rcx, [ rax + 0x10 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x28 ], r15
mov [ rsp + 0x30 ], rcx
mulx rcx, r15, [ rsi + 0x10 ]
mov rdx, 0x100000001 
mov [ rsp + 0x38 ], rcx
mov [ rsp + 0x40 ], r15
mulx r15, rcx, r8
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x48 ], r12
mulx r12, r15, [ rax + 0x0 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x50 ], r15
mov [ rsp + 0x58 ], r12
mulx r12, r15, rcx
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x60 ], r12
mov [ rsp + 0x68 ], rbp
mulx rbp, r12, rcx
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x70 ], rbp
mov [ rsp + 0x78 ], r12
mulx r12, rbp, rcx
test al, al
adox r15, r8
mov r15, 0xffffffff00000000 
mov rdx, rcx
mulx r8, rcx, r15
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x80 ], r12
mulx r12, r15, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x88 ], r15
mov [ rsp + 0x90 ], r12
mulx r12, r15, [ rax + 0x28 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x98 ], r12
mov [ rsp + 0xa0 ], r15
mulx r15, r12, [ rsi + 0x0 ]
adcx r12, rbx
adcx r10, r15
adcx rdi, r11
adcx r13, r9
adcx r14, [ rsp + 0x68 ]
mov rdx, [ rsi + 0x18 ]
mulx rbx, r11, [ rax + 0x28 ]
mov rdx, [ rsp + 0x48 ]
mov r9, 0x0 
adcx rdx, r9
clc
adcx rcx, [ rsp + 0x60 ]
adox rcx, r12
adcx r8, [ rsp + 0x78 ]
mov r15, rbp
adcx r15, [ rsp + 0x70 ]
mov r12, rbp
adcx r12, [ rsp + 0x80 ]
adcx rbp, [ rsp + 0x80 ]
adox r8, r10
adox r15, rdi
adox r12, r13
mov r10, rdx
mov rdx, [ rsi + 0x28 ]
mulx r13, rdi, [ rax + 0x8 ]
mov rdx, [ rsp + 0x80 ]
adcx rdx, r9
mov r9, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xa8 ], rbx
mov [ rsp + 0xb0 ], r11
mulx r11, rbx, [ rax + 0x0 ]
clc
adcx rdi, r11
adox rbp, r14
mov rdx, [ rsi + 0x8 ]
mulx r11, r14, [ rax + 0x8 ]
adcx r13, [ rsp + 0x0 ]
setc dl
clc
adcx r14, [ rsp + 0x58 ]
adox r9, r10
seto r10b
mov [ rsp + 0xb8 ], r13
mov r13, -0x2 
inc r13
adox rcx, [ rsp + 0x50 ]
mov r13, 0x100000001 
xchg rdx, rcx
mov [ rsp + 0xc0 ], rdi
mov [ rsp + 0xc8 ], rbx
mulx rbx, rdi, r13
mov rbx, 0xffffffff00000000 
xchg rdx, rbx
mov byte [ rsp + 0xd0 ], r10b
mulx r10, r13, rdi
adox r14, r8
mov r8, 0xffffffff 
mov rdx, r8
mov [ rsp + 0xd8 ], r9
mulx r9, r8, rdi
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0xe0 ], rbp
mov [ rsp + 0xe8 ], r12
mulx r12, rbp, rdi
adcx r11, [ rsp - 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xf0 ], r14
mov [ rsp + 0xf8 ], r8
mulx r8, r14, [ rax + 0x8 ]
mov rdx, 0xfffffffffffffffe 
mov byte [ rsp + 0x100 ], cl
mov [ rsp + 0x108 ], r12
mulx r12, rcx, rdi
setc dil
clc
adcx r13, r9
adcx rcx, r10
mov rdx, [ rax + 0x10 ]
mulx r9, r10, [ rsi + 0x10 ]
adox r11, r15
seto dl
mov r15, -0x2 
inc r15
adox r14, [ rsp + 0x90 ]
adox r10, r8
mov r8b, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x110 ], r10
mulx r10, r15, [ rax + 0x18 ]
mov rdx, rbp
adcx rdx, r12
mov r12, rbp
adcx r12, [ rsp + 0x108 ]
adcx rbp, [ rsp + 0x108 ]
mov [ rsp + 0x118 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x120 ], r12
mov [ rsp + 0x128 ], r14
mulx r14, r12, [ rax + 0x20 ]
adox r15, r9
mov rdx, [ rsp - 0x20 ]
seto r9b
mov [ rsp + 0x130 ], r15
movzx r15, byte [ rsp + 0x100 ]
mov [ rsp + 0x138 ], rbp
mov rbp, 0x0 
dec rbp
adox r15, rbp
adox rdx, [ rsp - 0x28 ]
mov r15, rdx
mov rdx, [ rsi + 0x10 ]
mov byte [ rsp + 0x140 ], r8b
mulx r8, rbp, [ rax + 0x20 ]
adox r12, [ rsp - 0x30 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x148 ], r12
mov [ rsp + 0x150 ], r15
mulx r15, r12, [ rsi + 0x20 ]
mov rdx, [ rsp + 0x108 ]
mov [ rsp + 0x158 ], r12
mov r12, 0x0 
adcx rdx, r12
clc
mov r12, -0x1 
movzx r9, r9b
adcx r9, r12
adcx r10, rbp
adcx r8, [ rsp + 0x40 ]
mov r9, rdx
mov rdx, [ rax + 0x8 ]
mulx r12, rbp, [ rsi + 0x20 ]
mov rdx, [ rsp + 0x38 ]
mov [ rsp + 0x160 ], r8
mov r8, 0x0 
adcx rdx, r8
adox r14, [ rsp + 0xa0 ]
mov r8, [ rsp + 0x98 ]
mov [ rsp + 0x168 ], r14
mov r14, 0x0 
adox r8, r14
test al, al
adox rbp, r15
adox r12, [ rsp + 0x30 ]
mov r15, [ rsp + 0x28 ]
adox r15, [ rsp + 0x10 ]
mov r14, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x170 ], r8
mov [ rsp + 0x178 ], r15
mulx r15, r8, [ rsi + 0x20 ]
adox r8, [ rsp + 0x8 ]
adcx rbx, [ rsp + 0xf8 ]
adcx r13, [ rsp + 0xf0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x180 ], r8
mulx r8, rbx, [ rax + 0x28 ]
adcx rcx, r11
setc dl
clc
adcx r13, [ rsp + 0x88 ]
mov r11, 0x100000001 
xchg rdx, r11
mov [ rsp + 0x188 ], r8
mov [ rsp + 0x190 ], r12
mulx r12, r8, r13
adox rbx, r15
mov r12, 0xffffffffffffffff 
mov rdx, r12
mulx r15, r12, r8
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x198 ], rbx
mov [ rsp + 0x1a0 ], rbp
mulx rbp, rbx, r8
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x1a8 ], r14
mov [ rsp + 0x1b0 ], r15
mulx r15, r14, [ rax + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1b8 ], r12
mov [ rsp + 0x1c0 ], rbp
mulx rbp, r12, [ rax + 0x8 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x1c8 ], rbx
mov [ rsp + 0x1d0 ], r9
mulx r9, rbx, r8
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x1d8 ], r9
mov [ rsp + 0x1e0 ], rbx
mulx rbx, r9, [ rsi + 0x8 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x1e8 ], r10
mov byte [ rsp + 0x1f0 ], r11b
mulx r11, r10, [ rsi + 0x8 ]
setc dl
clc
mov [ rsp + 0x1f8 ], rcx
mov rcx, -0x1 
movzx rdi, dil
adcx rdi, rcx
adcx r14, [ rsp - 0x38 ]
seto dil
movzx rcx, byte [ rsp + 0x140 ]
mov byte [ rsp + 0x200 ], dl
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
adox rcx, rdx
adox r14, [ rsp + 0xe8 ]
adcx r10, r15
adcx r9, r11
mov rcx, 0x0 
adcx rbx, rcx
adox r10, [ rsp + 0xe0 ]
adox r9, [ rsp + 0xd8 ]
clc
adcx r12, [ rsp - 0x40 ]
adcx rbp, [ rsp + 0x20 ]
mov r15, [ rsp + 0x18 ]
adcx r15, [ rsp - 0x10 ]
mov rdx, [ rax + 0x20 ]
mulx rcx, r11, [ rsi + 0x18 ]
adcx r11, [ rsp - 0x18 ]
adcx rcx, [ rsp + 0xb0 ]
mov rdx, [ rsp + 0x1f8 ]
mov byte [ rsp + 0x208 ], dil
seto dil
mov [ rsp + 0x210 ], rcx
movzx rcx, byte [ rsp + 0x200 ]
mov [ rsp + 0x218 ], r11
mov r11, 0x0 
dec r11
adox rcx, r11
adox rdx, [ rsp + 0x128 ]
setc cl
movzx r11, byte [ rsp + 0x1f0 ]
clc
mov [ rsp + 0x220 ], r15
mov r15, -0x1 
adcx r11, r15
adcx r14, [ rsp + 0x138 ]
adcx r10, [ rsp + 0x120 ]
movzx r11, cl
mov r15, [ rsp + 0xa8 ]
lea r11, [ r11 + r15 ]
adox r14, [ rsp + 0x110 ]
adox r10, [ rsp + 0x130 ]
adcx r9, [ rsp + 0x118 ]
adox r9, [ rsp + 0x1e8 ]
seto r15b
mov rcx, 0x0 
dec rcx
mov [ rsp + 0x228 ], r11
movzx r11, byte [ rsp + 0xd0 ]
movzx rdi, dil
adox rdi, rcx
adox rbx, r11
mov r11, 0xfffffffffffffffe 
xchg rdx, r11
mulx rcx, rdi, r8
adcx rbx, [ rsp + 0x1d0 ]
setc r8b
clc
adcx r13, [ rsp + 0x1e0 ]
seto r13b
mov rdx, 0x0 
dec rdx
movzx r15, r15b
adox r15, rdx
adox rbx, [ rsp + 0x160 ]
mov r15, [ rsp + 0x1c8 ]
seto dl
mov byte [ rsp + 0x230 ], r13b
mov r13, -0x2 
inc r13
adox r15, [ rsp + 0x1d8 ]
adox rdi, [ rsp + 0x1c0 ]
adox rcx, [ rsp + 0x1b8 ]
mov r13, [ rsp + 0x1b8 ]
mov byte [ rsp + 0x238 ], dl
mov rdx, r13
adox rdx, [ rsp + 0x1b0 ]
adcx r15, r11
adcx rdi, r14
adcx rcx, r10
adox r13, [ rsp + 0x1b0 ]
seto r11b
mov r14, -0x2 
inc r14
adox r15, [ rsp - 0x48 ]
adox r12, rdi
mov r10, 0x100000001 
xchg rdx, r10
mulx r14, rdi, r15
mov r14, 0xfffffffffffffffe 
mov rdx, rdi
mov [ rsp + 0x240 ], r12
mulx r12, rdi, r14
mov r14, 0xffffffff 
mov [ rsp + 0x248 ], r12
mov [ rsp + 0x250 ], rdi
mulx rdi, r12, r14
adcx r10, r9
adcx r13, rbx
adox rbp, rcx
movzx r9, r8b
movzx rbx, byte [ rsp + 0x230 ]
lea r9, [ r9 + rbx ]
setc bl
movzx r8, byte [ rsp + 0x238 ]
clc
mov rcx, -0x1 
adcx r8, rcx
adcx r9, [ rsp + 0x1a8 ]
adox r10, [ rsp + 0x220 ]
movzx r8, r11b
mov rcx, [ rsp + 0x1b0 ]
lea r8, [ r8 + rcx ]
setc cl
clc
mov r11, -0x1 
movzx rbx, bl
adcx rbx, r11
adcx r9, r8
adox r13, [ rsp + 0x218 ]
movzx rbx, cl
mov r8, 0x0 
adcx rbx, r8
adox r9, [ rsp + 0x210 ]
mov rcx, 0xffffffffffffffff 
mulx r11, r8, rcx
clc
adcx r12, r15
mov r12, 0xffffffff00000000 
mulx rcx, r15, r12
setc dl
clc
adcx r15, rdi
adcx rcx, [ rsp + 0x250 ]
setc dil
clc
mov r14, -0x1 
movzx rdx, dl
adcx rdx, r14
adcx r15, [ rsp + 0x240 ]
seto dl
inc r14
adox r15, [ rsp + 0x158 ]
mov r14, r8
seto r12b
mov [ rsp + 0x258 ], r9
mov r9, 0x0 
dec r9
movzx rdi, dil
adox rdi, r9
adox r14, [ rsp + 0x248 ]
adcx rcx, rbp
mov rbp, 0x100000001 
xchg rdx, rbp
mulx r9, rdi, r15
adcx r14, r10
mov r9, r8
adox r9, r11
adcx r9, r13
adox r8, r11
mov r10, 0x0 
adox r11, r10
dec r10
movzx rbp, bpl
adox rbp, r10
adox rbx, [ rsp + 0x228 ]
adcx r8, [ rsp + 0x258 ]
adcx r11, rbx
setc r13b
clc
movzx r12, r12b
adcx r12, r10
adcx rcx, [ rsp + 0x1a0 ]
adcx r14, [ rsp + 0x190 ]
adcx r9, [ rsp + 0x178 ]
adcx r8, [ rsp + 0x180 ]
mov rbp, 0xffffffff 
mov rdx, rdi
mulx r12, rdi, rbp
movzx rbx, byte [ rsp + 0x208 ]
mov r10, [ rsp + 0x188 ]
lea rbx, [ rbx + r10 ]
adcx r11, [ rsp + 0x198 ]
movzx r10, r13b
mov rbp, 0x0 
adox r10, rbp
adcx rbx, r10
mov r13, -0x3 
inc r13
adox rdi, r15
mov rdi, 0xffffffff00000000 
mulx r10, r15, rdi
setc r13b
clc
adcx r15, r12
mov r12, 0xfffffffffffffffe 
mulx rdi, rbp, r12
adcx rbp, r10
adox r15, rcx
mov rcx, 0xffffffffffffffff 
mulx r12, r10, rcx
mov rdx, r10
adcx rdx, rdi
mov rdi, r10
adcx rdi, r12
adcx r10, r12
adox rbp, r14
mov r14, 0x0 
adcx r12, r14
adox rdx, r9
adox rdi, r8
adox r10, r11
clc
adcx r15, [ rsp + 0xc8 ]
adcx rbp, [ rsp + 0xc0 ]
adcx rdx, [ rsp + 0xb8 ]
adcx rdi, [ rsp + 0x150 ]
adcx r10, [ rsp + 0x148 ]
adox r12, rbx
mov r9, 0x100000001 
xchg rdx, r9
mulx r11, r8, r15
mov rdx, r8
mulx r8, r11, rcx
mov rbx, 0xfffffffffffffffe 
mulx rcx, r14, rbx
mov rbx, 0xffffffff 
mov byte [ rsp + 0x260 ], r13b
mov [ rsp + 0x268 ], r12
mulx r12, r13, rbx
mov rbx, 0xffffffff00000000 
mov [ rsp + 0x270 ], r10
mov [ rsp + 0x278 ], rdi
mulx rdi, r10, rbx
setc dl
clc
adcx r10, r12
seto r12b
mov rbx, -0x2 
inc rbx
adox r13, r15
adcx r14, rdi
mov r13, r11
adcx r13, rcx
adox r10, rbp
adox r14, r9
mov r15, r11
adcx r15, r8
adox r13, [ rsp + 0x278 ]
adcx r11, r8
mov rbp, 0x0 
adcx r8, rbp
adox r15, [ rsp + 0x270 ]
mov r9, [ rsp + 0x268 ]
clc
movzx rdx, dl
adcx rdx, rbx
adcx r9, [ rsp + 0x168 ]
adox r11, r9
movzx rdx, r12b
movzx rcx, byte [ rsp + 0x260 ]
lea rdx, [ rdx + rcx ]
adcx rdx, [ rsp + 0x170 ]
adox r8, rdx
setc cl
seto r12b
mov rdi, r10
mov r9, 0xffffffff 
sub rdi, r9
movzx rdx, r12b
movzx rcx, cl
lea rdx, [ rdx + rcx ]
mov rcx, r14
mov r12, 0xffffffff00000000 
sbb rcx, r12
mov rbp, r13
mov rbx, 0xfffffffffffffffe 
sbb rbp, rbx
mov rbx, r15
mov r9, 0xffffffffffffffff 
sbb rbx, r9
mov r12, r11
sbb r12, r9
mov [ rsp + 0x280 ], rdi
mov rdi, r8
sbb rdi, r9
sbb rdx, 0x00000000
cmovc rbp, r13
cmovc r12, r11
cmovc rbx, r15
cmovc rdi, r8
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x18 ], rbx
cmovc rcx, r14
mov [ rdx + 0x20 ], r12
mov r14, [ rsp + 0x280 ]
cmovc r14, r10
mov [ rdx + 0x0 ], r14
mov [ rdx + 0x8 ], rcx
mov [ rdx + 0x10 ], rbp
mov [ rdx + 0x28 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 776
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.3594
; seed 1437029778843617 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5238868 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=61, initial num_batches=31): 139629 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.02665251348192014
; number reverted permutation / tried permutation: 63307 / 89940 =70.388%
; number reverted decision / tried decision: 48739 / 90059 =54.119%
; validated in 34.516s
