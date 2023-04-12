SECTION .text
	GLOBAL fiat_p384_square
fiat_p384_square:
sub rsp, 704
mov rdx, [ rsi + 0x18 ]
mulx r10, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r12
mulx r12, rdi, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x40 ], r12
mov [ rsp - 0x38 ], r13
mulx r13, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x30 ], r12
mov [ rsp - 0x28 ], rdi
mulx rdi, r12, rdx
mov rdx, 0x100000001 
mov [ rsp - 0x20 ], rbp
mov [ rsp - 0x18 ], rbx
mulx rbx, rbp, r12
mov rbx, 0xffffffff00000000 
mov rdx, rbp
mov [ rsp - 0x10 ], r13
mulx r13, rbp, rbx
mov rbx, 0xffffffff 
mov [ rsp - 0x8 ], r11
mov [ rsp + 0x0 ], r9
mulx r9, r11, rbx
mov rbx, 0xfffffffffffffffe 
mov [ rsp + 0x8 ], r11
mov [ rsp + 0x10 ], r15
mulx r15, r11, rbx
mov rbx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x18 ], r8
mov [ rsp + 0x20 ], rdi
mulx rdi, r8, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x28 ], rdi
mov [ rsp + 0x30 ], r8
mulx r8, rdi, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x38 ], rdi
mov [ rsp + 0x40 ], r8
mulx r8, rdi, rbx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x48 ], r14
mulx r14, rbx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x50 ], r14
mov [ rsp + 0x58 ], rbx
mulx rbx, r14, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x60 ], r10
mov [ rsp + 0x68 ], r8
mulx r8, r10, [ rsi + 0x10 ]
test al, al
adox r14, rcx
adox r10, rbx
adcx rbp, r9
adox rax, r8
adcx r11, r13
mov rdx, rdi
adcx rdx, r15
mov rcx, rdi
adcx rcx, [ rsp + 0x68 ]
adcx rdi, [ rsp + 0x68 ]
mov r13, rdx
mov rdx, [ rsi + 0x28 ]
mulx r15, r9, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mulx r8, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x70 ], r8
mov [ rsp + 0x78 ], r9
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x80 ], rbx
mov [ rsp + 0x88 ], r15
mulx r15, rbx, [ rsi + 0x10 ]
mov rdx, [ rsp + 0x60 ]
adox rdx, [ rsp + 0x48 ]
mov [ rsp + 0x90 ], rdx
setc dl
clc
adcx r8, [ rsp + 0x20 ]
adcx rbx, r9
mov r9b, dl
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x98 ], rax
mov [ rsp + 0xa0 ], rdi
mulx rdi, rax, [ rsi + 0x18 ]
adcx rax, r15
mov rdx, [ rsi + 0x20 ]
mov byte [ rsp + 0xa8 ], r9b
mulx r9, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xb0 ], r10
mov [ rsp + 0xb8 ], r14
mulx r14, r10, [ rsi + 0x28 ]
adcx r15, rdi
adcx r9, [ rsp + 0x18 ]
adox r10, [ rsp + 0x10 ]
mov rdx, 0x0 
adox r14, rdx
mov rdi, -0x3 
inc rdi
adox r12, [ rsp + 0x8 ]
adox rbp, r8
mov r12, [ rsp + 0x0 ]
adcx r12, rdx
adox r11, rbx
adox r13, rax
adox rcx, r15
clc
adcx rbp, [ rsp - 0x8 ]
mov r8, 0x100000001 
mov rdx, rbp
mulx rbx, rbp, r8
mov rbx, 0xffffffffffffffff 
xchg rdx, rbp
mulx r15, rax, rbx
adcx r11, [ rsp + 0xb8 ]
adcx r13, [ rsp + 0xb0 ]
mov rdi, 0xffffffff00000000 
mulx r8, rbx, rdi
mov rdi, 0xffffffff 
mov [ rsp + 0xc0 ], r13
mov [ rsp + 0xc8 ], r11
mulx r11, r13, rdi
adox r9, [ rsp + 0xa0 ]
adcx rcx, [ rsp + 0x98 ]
movzx rdi, byte [ rsp + 0xa8 ]
mov [ rsp + 0xd0 ], rcx
mov rcx, [ rsp + 0x68 ]
lea rdi, [ rdi + rcx ]
adox rdi, r12
adcx r9, [ rsp + 0x90 ]
adcx r10, rdi
mov rcx, rdx
mov rdx, [ rsi + 0x10 ]
mulx rdi, r12, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xd8 ], r10
mov [ rsp + 0xe0 ], r9
mulx r9, r10, [ rsi + 0x10 ]
setc dl
clc
adcx rbx, r11
mov r11, 0xfffffffffffffffe 
xchg rdx, rcx
mov [ rsp + 0xe8 ], r9
mov [ rsp + 0xf0 ], r10
mulx r10, r9, r11
adcx r9, r8
mov rdx, rax
adcx rdx, r10
mov r8, rdx
mov rdx, [ rsi + 0x10 ]
mulx r11, r10, rdx
mov rdx, rax
adcx rdx, r15
mov [ rsp + 0xf8 ], r8
mov r8, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x100 ], rdi
mov [ rsp + 0x108 ], r12
mulx r12, rdi, [ rsi + 0x10 ]
movzx rdx, cl
adox rdx, r14
adcx rax, r15
mov r14, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x110 ], rax
mulx rax, rcx, [ rsi + 0x8 ]
mov rdx, 0x0 
adcx r15, rdx
clc
adcx rcx, [ rsp + 0x40 ]
mov [ rsp + 0x118 ], rcx
seto cl
mov [ rsp + 0x120 ], r15
mov r15, -0x3 
inc r15
adox r13, rbp
adox rbx, [ rsp + 0xc8 ]
adcx r10, rax
adox r9, [ rsp + 0xc0 ]
adcx rdi, r11
adcx r12, [ rsp + 0x108 ]
mov r13, [ rsp + 0x100 ]
adcx r13, [ rsp + 0xf0 ]
mov rbp, [ rsp + 0xe8 ]
adcx rbp, rdx
mov rdx, [ rsi + 0x18 ]
mulx rax, r11, rdx
mov rdx, [ rsp - 0x10 ]
clc
adcx rdx, [ rsp - 0x18 ]
mov r15, [ rsp + 0xd0 ]
adox r15, [ rsp + 0xf8 ]
adox r8, [ rsp + 0xe0 ]
mov [ rsp + 0x128 ], rdx
mov rdx, [ rsp + 0x110 ]
adox rdx, [ rsp + 0xd8 ]
mov [ rsp + 0x130 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x138 ], r13
mov [ rsp + 0x140 ], r12
mulx r12, r13, [ rsi + 0x18 ]
adox r14, [ rsp + 0x120 ]
adcx r13, [ rsp - 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x148 ], r13
mov [ rsp + 0x150 ], r14
mulx r14, r13, [ rsi + 0x18 ]
adcx r11, r12
adcx r13, rax
movzx rdx, cl
mov rax, 0x0 
adox rdx, rax
mov rcx, -0x3 
inc rcx
adox rbx, [ rsp + 0x38 ]
adox r9, [ rsp + 0x118 ]
adox r10, r15
mov r15, 0x100000001 
xchg rdx, r15
mulx rax, r12, rbx
mov rax, 0xffffffff 
mov rdx, r12
mulx rcx, r12, rax
mov rax, 0xffffffff00000000 
mov [ rsp + 0x158 ], r13
mov [ rsp + 0x160 ], r11
mulx r11, r13, rax
adox rdi, r8
adox rbp, [ rsp + 0x140 ]
adcx r14, [ rsp - 0x28 ]
mov r8, 0xfffffffffffffffe 
mov [ rsp + 0x168 ], r14
mulx r14, rax, r8
setc r8b
clc
adcx r13, rcx
adcx rax, r11
mov rcx, 0xffffffffffffffff 
mov byte [ rsp + 0x170 ], r8b
mulx r8, r11, rcx
mov rdx, r11
adcx rdx, r14
mov r14, r11
adcx r14, r8
adcx r11, r8
mov rcx, 0x0 
adcx r8, rcx
clc
adcx r12, rbx
adcx r13, r9
mov r12, [ rsp + 0x138 ]
adox r12, [ rsp + 0x150 ]
adox r15, [ rsp + 0x130 ]
adcx rax, r10
adcx rdx, rdi
mov rbx, rdx
mov rdx, [ rsi + 0x8 ]
mulx r10, r9, [ rsi + 0x20 ]
adcx r14, rbp
adcx r11, r12
adcx r8, r15
setc dl
clc
adcx r13, [ rsp - 0x30 ]
mov rdi, 0x100000001 
xchg rdx, r13
mulx r12, rbp, rdi
adcx rax, [ rsp + 0x128 ]
movzx r12, r13b
adox r12, rcx
mov r15, 0xffffffffffffffff 
xchg rdx, rbp
mulx rcx, r13, r15
mov r15, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x178 ], r10
mulx r10, rdi, [ rsi + 0x10 ]
adcx rbx, [ rsp + 0x148 ]
adcx r14, [ rsp + 0x160 ]
adcx r11, [ rsp + 0x158 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x180 ], r10
mov [ rsp + 0x188 ], rdi
mulx rdi, r10, r15
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x190 ], r11
mov [ rsp + 0x198 ], r14
mulx r14, r11, r15
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x1a0 ], r12
mov [ rsp + 0x1a8 ], r8
mulx r8, r12, r15
mov r15, -0x2 
inc r15
adox r11, rdi
adox r12, r14
mov rdi, r13
adox rdi, r8
mov r14, r13
adox r14, rcx
setc r8b
clc
adcx r9, [ rsp - 0x38 ]
setc r15b
clc
adcx r10, rbp
adcx r11, rax
adox r13, rcx
adcx r12, rbx
seto r10b
mov rbp, -0x2 
inc rbp
adox r11, [ rsp - 0x48 ]
mov rdx, [ rsi + 0x20 ]
mulx rbx, rax, [ rsi + 0x18 ]
mov rdx, 0x100000001 
mov byte [ rsp + 0x1b0 ], r10b
mulx r10, rbp, r11
movzx r10, byte [ rsp + 0x170 ]
mov rdx, [ rsp - 0x40 ]
lea r10, [ r10 + rdx ]
mov rdx, [ rsp + 0x1a8 ]
mov [ rsp + 0x1b8 ], rbx
seto bl
mov [ rsp + 0x1c0 ], rax
mov rax, 0x0 
dec rax
movzx r8, r8b
adox r8, rax
adox rdx, [ rsp + 0x168 ]
mov r8, 0xffffffff00000000 
xchg rdx, rbp
mov byte [ rsp + 0x1c8 ], r15b
mulx r15, rax, r8
adox r10, [ rsp + 0x1a0 ]
mov r8, 0xffffffffffffffff 
mov [ rsp + 0x1d0 ], r15
mov [ rsp + 0x1d8 ], r10
mulx r10, r15, r8
adcx rdi, [ rsp + 0x198 ]
adcx r14, [ rsp + 0x190 ]
adcx r13, rbp
seto bpl
mov r8, 0x0 
dec r8
movzx rbx, bl
adox rbx, r8
adox r12, r9
mov r9, [ rsp + 0x178 ]
setc bl
movzx r8, byte [ rsp + 0x1c8 ]
clc
mov [ rsp + 0x1e0 ], r10
mov r10, -0x1 
adcx r8, r10
adcx r9, [ rsp + 0x188 ]
adox r9, rdi
mov r8, [ rsp + 0x180 ]
adcx r8, [ rsp + 0x1c0 ]
mov rdi, [ rsp + 0x58 ]
adcx rdi, [ rsp + 0x1b8 ]
mov r10, [ rsp + 0x50 ]
adcx r10, [ rsp + 0x30 ]
adox r8, r14
adox rdi, r13
mov r14, [ rsp + 0x28 ]
mov r13, 0x0 
adcx r14, r13
mov r13, 0xffffffff 
mov [ rsp + 0x1e8 ], rdi
mov [ rsp + 0x1f0 ], r14
mulx r14, rdi, r13
clc
adcx rax, r14
movzx r14, byte [ rsp + 0x1b0 ]
lea rcx, [ rcx + r14 ]
seto r14b
mov r13, 0x0 
dec r13
movzx rbx, bl
adox rbx, r13
adox rcx, [ rsp + 0x1d8 ]
movzx rbx, bpl
mov r13, 0x0 
adox rbx, r13
mov rbp, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1f8 ], rbx
mulx rbx, r13, [ rsi + 0x28 ]
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x200 ], rbx
mov [ rsp + 0x208 ], r13
mulx r13, rbx, rbp
adcx rbx, [ rsp + 0x1d0 ]
mov rbp, -0x2 
inc rbp
adox rdi, r11
mov rdi, r15
adcx rdi, r13
mov rdx, [ rsi + 0x28 ]
mulx r13, r11, rdx
adox rax, r12
adox rbx, r9
adox rdi, r8
mov rdx, r15
adcx rdx, [ rsp + 0x1e0 ]
adcx r15, [ rsp + 0x1e0 ]
mov r12, rdx
mov rdx, [ rsi + 0x10 ]
mulx r8, r9, [ rsi + 0x28 ]
mov rdx, [ rsp + 0x1e0 ]
mov rbp, 0x0 
adcx rdx, rbp
mov [ rsp + 0x210 ], r13
mov r13, [ rsp + 0x88 ]
clc
adcx r13, [ rsp + 0x80 ]
mov [ rsp + 0x218 ], r11
setc r11b
clc
adcx rax, [ rsp + 0x78 ]
mov rbp, 0x100000001 
xchg rdx, rbp
mov [ rsp + 0x220 ], rdi
mov [ rsp + 0x228 ], r8
mulx r8, rdi, rax
mov r8, 0xffffffff 
mov rdx, rdi
mov [ rsp + 0x230 ], r9
mulx r9, rdi, r8
adcx r13, rbx
setc bl
clc
mov r8, -0x1 
movzx r14, r14b
adcx r14, r8
adcx rcx, r10
mov r10, [ rsp + 0x1f0 ]
adcx r10, [ rsp + 0x1f8 ]
adox r12, [ rsp + 0x1e8 ]
adox r15, rcx
adox rbp, r10
seto r14b
adc r14b, 0x0
movzx r14, r14b
mov rcx, [ rsp + 0x70 ]
add r11b, 0x7F
adox rcx, [ rsp + 0x230 ]
mov r11, [ rsp + 0x208 ]
adox r11, [ rsp + 0x228 ]
mov r10, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x238 ], r13
mulx r13, r8, [ rsi + 0x28 ]
mov rdx, -0x1 
movzx rbx, bl
adcx rbx, rdx
adcx rcx, [ rsp + 0x220 ]
adcx r11, r12
adox r8, [ rsp + 0x200 ]
adcx r8, r15
adox r13, [ rsp + 0x218 ]
adcx r13, rbp
mov rbx, 0xffffffff00000000 
mov rdx, rbx
mulx r12, rbx, r10
seto r15b
mov rbp, -0x2 
inc rbp
adox rbx, r9
movzx r9, r15b
mov rbp, [ rsp + 0x210 ]
lea r9, [ r9 + rbp ]
movzx rbp, r14b
adcx rbp, r9
mov r14, 0xfffffffffffffffe 
mov rdx, r14
mulx r15, r14, r10
adox r14, r12
mov r12, 0xffffffffffffffff 
mov rdx, r10
mulx r9, r10, r12
setc dl
clc
adcx rdi, rax
adcx rbx, [ rsp + 0x238 ]
mov rdi, r10
adox rdi, r15
adcx r14, rcx
mov rax, r10
adox rax, r9
adcx rdi, r11
adox r10, r9
adcx rax, r8
adcx r10, r13
mov rcx, 0x0 
adox r9, rcx
adcx r9, rbp
movzx r11, dl
adc r11, 0x0
mov r8, rbx
mov r13, 0xffffffff 
sub r8, r13
mov rdx, r14
mov rbp, 0xffffffff00000000 
sbb rdx, rbp
mov r15, rdi
mov rcx, 0xfffffffffffffffe 
sbb r15, rcx
mov rcx, rax
sbb rcx, r12
mov r13, r10
sbb r13, r12
mov rbp, r9
sbb rbp, r12
sbb r11, 0x00000000
cmovc rcx, rax
cmovc r13, r10
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x20 ], r13
mov [ r11 + 0x18 ], rcx
cmovc rbp, r9
cmovc rdx, r14
mov [ r11 + 0x8 ], rdx
cmovc r8, rbx
mov [ r11 + 0x28 ], rbp
cmovc r15, rdi
mov [ r11 + 0x0 ], r8
mov [ r11 + 0x10 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 704
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.4390
; seed 2679301255966924 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4921542 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=63, initial num_batches=31): 138764 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.028195228243505795
; number reverted permutation / tried permutation: 64866 / 90016 =72.061%
; number reverted decision / tried decision: 46487 / 89983 =51.662%
; validated in 32.534s
