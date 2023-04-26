SECTION .text
	GLOBAL fiat_p384_square
fiat_p384_square:
sub rsp, 672
mov rdx, [ rsi + 0x20 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rcx
mulx rcx, rdi, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x40 ], r11
mov [ rsp - 0x38 ], rcx
mulx rcx, r11, rdx
mov rdx, 0x100000001 
mov [ rsp - 0x30 ], rcx
mov [ rsp - 0x28 ], r11
mulx r11, rcx, r14
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x20 ], rdi
mulx rdi, r11, [ rsi + 0x20 ]
mov rdx, 0xffffffff 
mov [ rsp - 0x18 ], rdi
mov [ rsp - 0x10 ], r11
mulx r11, rdi, rcx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x8 ], r9
mov [ rsp + 0x0 ], r8
mulx r8, r9, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x8 ], r8
mov [ rsp + 0x10 ], r9
mulx r9, r8, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x18 ], r9
mov [ rsp + 0x20 ], r8
mulx r8, r9, [ rsi + 0x0 ]
test al, al
adox rdi, r14
mov rdx, [ rsi + 0x8 ]
mulx r14, rdi, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x28 ], r14
mov [ rsp + 0x30 ], rdi
mulx rdi, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x38 ], r14
mov [ rsp + 0x40 ], rdi
mulx rdi, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x48 ], r9
mov [ rsp + 0x50 ], r8
mulx r8, r9, [ rsi + 0x10 ]
adcx rbx, r15
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x58 ], r8
mulx r8, r15, [ rsi + 0x0 ]
adcx r14, rbp
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x60 ], r9
mulx r9, rbp, rcx
adcx r15, rdi
adcx rax, r8
mov rdi, 0xffffffff00000000 
mov rdx, rcx
mulx r8, rcx, rdi
adcx r12, r10
setc r10b
clc
adcx rcx, r11
adcx rbp, r8
movzx r11, r10b
lea r11, [ r11 + r13 ]
mov r13, 0xffffffffffffffff 
mulx r10, r8, r13
mov rdx, r8
adcx rdx, r9
mov r9, rdx
mov rdx, [ rsi + 0x20 ]
mulx rdi, r13, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x68 ], rdi
mov [ rsp + 0x70 ], r13
mulx r13, rdi, [ rsi + 0x8 ]
adox rcx, rbx
adox rbp, r14
adox r9, r15
mov rdx, r8
adcx rdx, r10
adcx r8, r10
adox rdx, rax
mov rbx, 0x0 
adcx r10, rbx
mov r14, rdx
mov rdx, [ rsi + 0x0 ]
mulx rax, r15, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x78 ], r15
mulx r15, rbx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x80 ], r15
mov [ rsp + 0x88 ], r14
mulx r14, r15, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x90 ], r9
mov [ rsp + 0x98 ], rbp
mulx rbp, r9, [ rsi + 0x10 ]
clc
adcx rax, [ rsp + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xa0 ], rax
mov [ rsp + 0xa8 ], rcx
mulx rcx, rax, [ rsi + 0x0 ]
adox r8, r12
adcx rbx, [ rsp + 0x18 ]
setc dl
clc
adcx rdi, rcx
adcx r15, r13
adox r10, r11
mov r12b, dl
mov rdx, [ rsi + 0x10 ]
mulx r13, r11, [ rsi + 0x18 ]
adcx r11, r14
mov rdx, [ rsi + 0x28 ]
mulx rcx, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xb0 ], rbx
mov byte [ rsp + 0xb8 ], r12b
mulx r12, rbx, [ rsi + 0x10 ]
adcx r9, r13
adcx r14, rbp
mov rdx, [ rsi + 0x8 ]
mulx r13, rbp, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xc0 ], r14
mov [ rsp + 0xc8 ], r9
mulx r9, r14, [ rsi + 0x8 ]
seto dl
mov [ rsp + 0xd0 ], r11
mov r11, -0x2 
inc r11
adox r14, [ rsp + 0xa8 ]
mov r11, 0x100000001 
xchg rdx, r14
mov [ rsp + 0xd8 ], r15
mov byte [ rsp + 0xe0 ], r14b
mulx r14, r15, r11
mov r14, 0x0 
adcx rcx, r14
mov r14, 0xffffffffffffffff 
xchg rdx, r14
mov [ rsp + 0xe8 ], rcx
mulx rcx, r11, r15
clc
adcx rbp, r9
adcx rbx, r13
adox rbp, [ rsp + 0x98 ]
adcx r12, [ rsp + 0x0 ]
mov r13, 0xffffffff 
mov rdx, r13
mulx r9, r13, r15
mov rdx, [ rsp - 0x10 ]
adcx rdx, [ rsp - 0x8 ]
mov [ rsp + 0xf0 ], rcx
mov rcx, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xf8 ], r11
mov [ rsp + 0x100 ], r10
mulx r10, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x108 ], r10
mov [ rsp + 0x110 ], rcx
mulx rcx, r10, [ rsi + 0x18 ]
adox rbx, [ rsp + 0x90 ]
adox r12, [ rsp + 0x88 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x118 ], r12
mov [ rsp + 0x120 ], r8
mulx r8, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x128 ], rdi
mov [ rsp + 0x130 ], rax
mulx rax, rdi, [ rsi + 0x18 ]
adcx r11, [ rsp - 0x18 ]
mov rdx, [ rsp - 0x20 ]
mov [ rsp + 0x138 ], r11
setc r11b
clc
adcx rdx, [ rsp + 0x50 ]
adcx r12, [ rsp - 0x38 ]
adcx r8, [ rsp - 0x40 ]
adcx r10, [ rsp - 0x48 ]
adcx rdi, rcx
mov rcx, 0xffffffff00000000 
xchg rdx, rcx
mov [ rsp + 0x140 ], rdi
mov [ rsp + 0x148 ], r10
mulx r10, rdi, r15
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x150 ], r8
mov [ rsp + 0x158 ], r12
mulx r12, r8, r15
setc r15b
clc
adcx rdi, r9
seto r9b
mov rdx, -0x2 
inc rdx
adox r13, r14
movzx r13, r15b
lea r13, [ r13 + rax ]
adox rdi, rbp
adcx r8, r10
adox r8, rbx
setc r14b
clc
adcx rdi, [ rsp + 0x130 ]
mov rbp, 0x100000001 
mov rdx, rbp
mulx rbx, rbp, rdi
adcx r8, [ rsp + 0x128 ]
mov rbx, 0xffffffff00000000 
mov rdx, rbp
mulx rax, rbp, rbx
mov r15, 0xffffffffffffffff 
mulx rbx, r10, r15
mov r15, 0xfffffffffffffffe 
mov [ rsp + 0x160 ], r13
mov [ rsp + 0x168 ], rcx
mulx rcx, r13, r15
mov r15, [ rsp + 0x120 ]
mov [ rsp + 0x170 ], rbx
setc bl
clc
mov [ rsp + 0x178 ], r10
mov r10, -0x1 
movzx r9, r9b
adcx r9, r10
adcx r15, [ rsp + 0x110 ]
mov r9, 0xffffffff 
mov [ rsp + 0x180 ], rcx
mulx rcx, r10, r9
movzx rdx, r11b
mov r9, [ rsp + 0x108 ]
lea rdx, [ rdx + r9 ]
mov r9, [ rsp + 0x100 ]
adcx r9, [ rsp + 0x138 ]
movzx r11, byte [ rsp + 0xe0 ]
adcx r11, rdx
setc dl
clc
mov [ rsp + 0x188 ], r8
mov r8, -0x1 
movzx r14, r14b
adcx r14, r8
adcx r12, [ rsp + 0xf8 ]
mov r14, [ rsp + 0xf0 ]
mov r8, r14
adcx r8, [ rsp + 0xf8 ]
mov [ rsp + 0x190 ], r13
mov r13, r14
adcx r13, [ rsp + 0xf8 ]
adox r12, [ rsp + 0x118 ]
adox r8, r15
mov r15, 0x0 
adcx r14, r15
adox r13, r9
clc
mov r9, -0x1 
movzx rbx, bl
adcx rbx, r9
adcx r12, [ rsp + 0xd8 ]
adcx r8, [ rsp + 0xd0 ]
adcx r13, [ rsp + 0xc8 ]
adox r14, r11
adcx r14, [ rsp + 0xc0 ]
movzx rbx, dl
adox rbx, r15
adcx rbx, [ rsp + 0xe8 ]
mov rdx, -0x3 
inc rdx
adox r10, rdi
setc r10b
clc
adcx rbp, rcx
adcx rax, [ rsp + 0x190 ]
mov rdx, [ rsi + 0x20 ]
mulx rcx, rdi, [ rsi + 0x18 ]
adox rbp, [ rsp + 0x188 ]
mov rdx, [ rsp + 0x180 ]
adcx rdx, [ rsp + 0x178 ]
adox rax, r12
adox rdx, r8
mov r11, [ rsp + 0x178 ]
mov r12, r11
adcx r12, [ rsp + 0x170 ]
adcx r11, [ rsp + 0x170 ]
adox r12, r13
setc r8b
clc
adcx rbp, [ rsp + 0x48 ]
adox r11, r14
adcx rax, [ rsp + 0x168 ]
adcx rdx, [ rsp + 0x158 ]
adcx r12, [ rsp + 0x150 ]
mov r13, 0x100000001 
xchg rdx, r13
mulx r15, r14, rbp
movzx r15, r8b
mov r9, [ rsp + 0x170 ]
lea r15, [ r15 + r9 ]
adcx r11, [ rsp + 0x148 ]
mov r9, 0xffffffffffffffff 
mov rdx, r14
mulx r8, r14, r9
adox r15, rbx
seto bl
movzx r9, byte [ rsp + 0xb8 ]
mov [ rsp + 0x198 ], r11
mov r11, 0x0 
dec r11
adox r9, r11
adox rdi, [ rsp + 0x80 ]
adox rcx, [ rsp - 0x28 ]
mov r9, 0xffffffff 
mov [ rsp + 0x1a0 ], rcx
mulx rcx, r11, r9
mov r9, 0xffffffff00000000 
mov [ rsp + 0x1a8 ], rdi
mov byte [ rsp + 0x1b0 ], r10b
mulx r10, rdi, r9
seto r9b
mov byte [ rsp + 0x1b8 ], bl
mov rbx, -0x2 
inc rbx
adox r11, rbp
setc r11b
clc
adcx rdi, rcx
adox rdi, rax
mov rbp, 0xfffffffffffffffe 
mulx rcx, rax, rbp
adcx rax, r10
adox rax, r13
mov r13, r14
adcx r13, rcx
mov rdx, r14
adcx rdx, r8
adox r13, r12
adcx r14, r8
mov r12, rdx
mov rdx, [ rsi + 0x18 ]
mulx rcx, r10, [ rsi + 0x28 ]
setc dl
clc
adcx rdi, [ rsp + 0x78 ]
adcx rax, [ rsp + 0xa0 ]
adcx r13, [ rsp + 0xb0 ]
mov rbx, 0x100000001 
xchg rdx, rdi
mov byte [ rsp + 0x1c0 ], r9b
mulx r9, rbp, rbx
mov r9, [ rsp + 0x40 ]
setc bl
clc
adcx r9, [ rsp + 0x30 ]
mov [ rsp + 0x1c8 ], r9
mov r9, [ rsp + 0x28 ]
adcx r9, [ rsp + 0x60 ]
adcx r10, [ rsp + 0x58 ]
adcx rcx, [ rsp + 0x70 ]
mov [ rsp + 0x1d0 ], rcx
mov rcx, [ rsp + 0x68 ]
adcx rcx, [ rsp + 0x10 ]
mov [ rsp + 0x1d8 ], rcx
setc cl
clc
mov [ rsp + 0x1e0 ], r10
mov r10, -0x1 
movzx r11, r11b
adcx r11, r10
adcx r15, [ rsp + 0x140 ]
mov r11, rdx
mov rdx, [ rsi + 0x20 ]
mov byte [ rsp + 0x1e8 ], cl
mulx rcx, r10, [ rsi + 0x28 ]
movzx rdx, byte [ rsp + 0x1b8 ]
mov [ rsp + 0x1f0 ], rcx
movzx rcx, byte [ rsp + 0x1b0 ]
lea rdx, [ rdx + rcx ]
adcx rdx, [ rsp + 0x160 ]
adox r12, [ rsp + 0x198 ]
adox r14, r15
movzx rcx, dil
lea rcx, [ rcx + r8 ]
mov r8, 0xffffffff 
xchg rdx, rbp
mulx r15, rdi, r8
adox rcx, rbp
seto bpl
mov r8, -0x2 
inc r8
adox rdi, r11
setc dil
clc
movzx rbx, bl
adcx rbx, r8
adcx r12, [ rsp + 0x1a8 ]
mov r11, 0xffffffffffffffff 
mulx r8, rbx, r11
movzx r11, bpl
movzx rdi, dil
lea r11, [ r11 + rdi ]
mov rdi, 0xffffffff00000000 
mov [ rsp + 0x1f8 ], r11
mulx r11, rbp, rdi
adcx r14, [ rsp + 0x1a0 ]
setc dil
clc
adcx rbp, r15
mov r15, 0xfffffffffffffffe 
mov [ rsp + 0x200 ], rcx
mov byte [ rsp + 0x208 ], dil
mulx rdi, rcx, r15
adcx rcx, r11
adox rbp, rax
adox rcx, r13
mov rax, rbx
adcx rax, rdi
adox rax, r12
mov r13, rbx
adcx r13, r8
adcx rbx, r8
adox r13, r14
seto dl
mov r12, -0x2 
inc r12
adox rbp, [ rsp + 0x38 ]
mov r11, 0x0 
adcx r8, r11
mov r14, 0x100000001 
xchg rdx, rbp
mulx r11, rdi, r14
mov r11, 0xffffffff 
xchg rdx, r11
mulx r15, r12, rdi
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x210 ], r12
mulx r12, r14, rdi
adox rcx, [ rsp + 0x1c8 ]
adox r9, rax
movzx rax, byte [ rsp + 0x1c0 ]
clc
mov rdx, -0x1 
adcx rax, rdx
adcx r10, [ rsp - 0x30 ]
mov rax, [ rsp + 0x1f0 ]
mov rdx, 0x0 
adcx rax, rdx
movzx rdx, byte [ rsp + 0x208 ]
clc
mov [ rsp + 0x218 ], r9
mov r9, -0x1 
adcx rdx, r9
adcx r10, [ rsp + 0x200 ]
adcx rax, [ rsp + 0x1f8 ]
setc dl
clc
movzx rbp, bpl
adcx rbp, r9
adcx r10, rbx
adcx r8, rax
adox r13, [ rsp + 0x1e0 ]
adox r10, [ rsp + 0x1d0 ]
seto bl
inc r9
adox r14, r15
setc bpl
clc
adcx r11, [ rsp + 0x210 ]
adcx r14, rcx
mov r11, 0xfffffffffffffffe 
xchg rdx, rdi
mulx rcx, r15, r11
adox r15, r12
movzx r12, bpl
movzx rdi, dil
lea r12, [ r12 + rdi ]
adcx r15, [ rsp + 0x218 ]
movzx rdi, byte [ rsp + 0x1e8 ]
mov rax, [ rsp + 0x8 ]
lea rdi, [ rdi + rax ]
seto al
dec r9
movzx rbx, bl
adox rbx, r9
adox r8, [ rsp + 0x1d8 ]
adox rdi, r12
mov rbp, 0xffffffffffffffff 
mulx r12, rbx, rbp
seto dl
inc r9
mov r9, -0x1 
movzx rax, al
adox rax, r9
adox rcx, rbx
mov rax, rbx
adox rax, r12
adox rbx, r12
adcx rcx, r13
mov r13, 0x0 
adox r12, r13
adcx rax, r10
adcx rbx, r8
adcx r12, rdi
setc r10b
mov r8, r14
mov rdi, 0xffffffff 
sub r8, rdi
mov r13, r15
mov r9, 0xffffffff00000000 
sbb r13, r9
movzx r11, r10b
movzx rdx, dl
lea r11, [ r11 + rdx ]
mov rdx, rcx
mov r10, 0xfffffffffffffffe 
sbb rdx, r10
mov r10, rax
sbb r10, rbp
mov r9, rbx
sbb r9, rbp
mov rdi, r12
sbb rdi, rbp
sbb r11, 0x00000000
cmovc r10, rax
cmovc r13, r15
cmovc r9, rbx
cmovc r8, r14
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x0 ], r8
cmovc rdi, r12
mov [ r11 + 0x28 ], rdi
mov [ r11 + 0x8 ], r13
mov [ r11 + 0x20 ], r9
cmovc rdx, rcx
mov [ r11 + 0x10 ], rdx
mov [ r11 + 0x18 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 672
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.2143
; seed 4470095822512224 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4110025 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=64, initial num_batches=31): 109866 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.02673122426262614
; number reverted permutation / tried permutation: 64787 / 90035 =71.958%
; number reverted decision / tried decision: 53568 / 89964 =59.544%
; validated in 24.175s
