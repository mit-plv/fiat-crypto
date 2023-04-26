SECTION .text
	GLOBAL fiat_p384_square
fiat_p384_square:
sub rsp, 664
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
mov rdx, 0x100000001 
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, r12
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], r13
mov [ rsp - 0x40 ], r9
mulx r9, r13, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x38 ], r9
mov [ rsp - 0x30 ], r8
mulx r8, r9, [ rsi + 0x8 ]
mov rdx, 0xffffffff 
mov [ rsp - 0x28 ], r8
mov [ rsp - 0x20 ], r9
mulx r9, r8, r14
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x18 ], r8
mov [ rsp - 0x10 ], r9
mulx r9, r8, [ rsi + 0x0 ]
add r11, r9
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x8 ], r11
mulx r11, r9, [ rsi + 0x28 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x0 ], r9
mov [ rsp + 0x8 ], r8
mulx r8, r9, r14
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x10 ], r11
mov [ rsp + 0x18 ], r8
mulx r8, r11, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x20 ], r9
mov [ rsp + 0x28 ], rbp
mulx rbp, r9, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x30 ], r13
mov [ rsp + 0x38 ], r10
mulx r10, r13, [ rsi + 0x0 ]
adcx r9, rcx
adcx r11, rbp
mov rdx, [ rsi + 0x20 ]
mulx rbp, rcx, rdx
adcx rcx, r8
mov rdx, -0x2 
inc rdx
adox r15, r10
mov rdx, [ rsi + 0x10 ]
mulx r10, r8, [ rsi + 0x8 ]
adox r8, rdi
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x40 ], rcx
mulx rcx, rdi, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x48 ], r11
mov [ rsp + 0x50 ], r9
mulx r9, r11, [ rsi + 0x8 ]
adox r11, r10
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x58 ], rcx
mulx rcx, r10, [ rsi + 0x28 ]
adcx r10, rbp
adox rax, r9
mov rdx, [ rsi + 0x0 ]
mulx r9, rbp, [ rsi + 0x10 ]
setc dl
clc
adcx rbx, r9
mov r9b, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x60 ], r10
mov [ rsp + 0x68 ], rdi
mulx rdi, r10, rdx
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x70 ], rbx
mov [ rsp + 0x78 ], rbp
mulx rbp, rbx, r14
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x80 ], rax
mov [ rsp + 0x88 ], r11
mulx r11, rax, r14
mov r14, [ rsp + 0x30 ]
adox r14, [ rsp + 0x38 ]
adcx r10, [ rsp + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x90 ], r10
mov [ rsp + 0x98 ], r14
mulx r14, r10, [ rsi + 0x18 ]
adcx r10, rdi
seto dl
mov rdi, -0x2 
inc rdi
adox rax, [ rsp - 0x10 ]
adcx r14, [ rsp - 0x30 ]
adox rbx, r11
adox rbp, [ rsp + 0x20 ]
mov r11, [ rsp + 0x18 ]
mov rdi, r11
adox rdi, [ rsp + 0x20 ]
mov [ rsp + 0xa0 ], r14
mov r14, r11
adox r14, [ rsp + 0x20 ]
mov [ rsp + 0xa8 ], r10
mov r10b, dl
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xb0 ], r8
mov [ rsp + 0xb8 ], r15
mulx r15, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov byte [ rsp + 0xc0 ], r10b
mov [ rsp + 0xc8 ], r13
mulx r13, r10, [ rsi + 0x28 ]
movzx rdx, r9b
lea rdx, [ rdx + rcx ]
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xd0 ], r13
mulx r13, r9, [ rsi + 0x10 ]
adcx r10, [ rsp - 0x40 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xd8 ], rcx
mov [ rsp + 0xe0 ], r10
mulx r10, rcx, [ rsi + 0x18 ]
setc dl
clc
adcx r8, [ rsp - 0x48 ]
mov [ rsp + 0xe8 ], r14
mov r14b, dl
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xf0 ], rdi
mov [ rsp + 0xf8 ], rbp
mulx rbp, rdi, [ rsi + 0x0 ]
adcx r9, r15
adcx rcx, r13
mov rdx, [ rsi + 0x0 ]
mulx r13, r15, [ rsi + 0x28 ]
adcx rdi, r10
adcx r15, rbp
setc dl
clc
adcx r12, [ rsp - 0x18 ]
movzx r12, dl
lea r12, [ r12 + r13 ]
adcx rax, r8
adcx rbx, r9
adcx rcx, [ rsp + 0xf8 ]
adcx rdi, [ rsp + 0xf0 ]
adcx r15, [ rsp + 0xe8 ]
mov r10, 0x0 
adox r11, r10
adcx r11, r12
mov r8, -0x3 
inc r8
adox rax, [ rsp + 0xc8 ]
mov rbp, 0x100000001 
mov rdx, rbp
mulx r9, rbp, rax
mov r9, 0xffffffff 
mov rdx, rbp
mulx r13, rbp, r9
mov r12, 0xffffffffffffffff 
mulx r8, r10, r12
mov r9, 0xffffffff00000000 
mov [ rsp + 0x100 ], r8
mulx r8, r12, r9
movzx r9, r14b
mov [ rsp + 0x108 ], r10
mov r10, [ rsp + 0xd0 ]
lea r9, [ r9 + r10 ]
setc r10b
clc
adcx r12, r13
adox rbx, [ rsp + 0xb8 ]
adox rcx, [ rsp + 0xb0 ]
adox rdi, [ rsp + 0x88 ]
adox r15, [ rsp + 0x80 ]
mov r14, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x110 ], r9
mulx r9, r13, [ rsi + 0x8 ]
movzx rdx, byte [ rsp + 0xc0 ]
mov [ rsp + 0x118 ], r9
mov r9, [ rsp - 0x38 ]
lea rdx, [ rdx + r9 ]
adox r11, [ rsp + 0x98 ]
movzx r9, r10b
adox r9, rdx
mov r10, 0xfffffffffffffffe 
mov rdx, r14
mov [ rsp + 0x120 ], r9
mulx r9, r14, r10
seto dl
mov r10, -0x2 
inc r10
adox rbp, rax
adox r12, rbx
adcx r14, r8
adcx r9, [ rsp + 0x108 ]
mov rbp, [ rsp + 0x100 ]
mov rax, rbp
adcx rax, [ rsp + 0x108 ]
adox r14, rcx
mov r8b, dl
mov rdx, [ rsi + 0x28 ]
mulx rcx, rbx, [ rsi + 0x10 ]
mov rdx, rbp
adcx rdx, [ rsp + 0x108 ]
adox r9, rdi
setc dil
clc
adcx r12, [ rsp + 0x78 ]
adcx r14, [ rsp + 0x70 ]
mov r10, rdx
mov rdx, [ rsi + 0x18 ]
mov byte [ rsp + 0x128 ], r8b
mov [ rsp + 0x130 ], r14
mulx r14, r8, [ rsi + 0x10 ]
adcx r9, [ rsp + 0x90 ]
adox rax, r15
movzx rdx, dil
lea rdx, [ rdx + rbp ]
adox r10, r11
mov rbp, rdx
mov rdx, [ rsi + 0x18 ]
mulx r11, r15, [ rsi + 0x28 ]
mov rdx, 0x100000001 
mov [ rsp + 0x138 ], rbp
mulx rbp, rdi, r12
adcx rax, [ rsp + 0xa8 ]
mov rbp, 0xffffffffffffffff 
mov rdx, rbp
mov [ rsp + 0x140 ], r10
mulx r10, rbp, rdi
mov rdx, [ rsp - 0x20 ]
mov [ rsp + 0x148 ], rax
setc al
clc
adcx rdx, [ rsp + 0x10 ]
mov [ rsp + 0x150 ], rdx
mov rdx, 0xffffffff00000000 
mov byte [ rsp + 0x158 ], al
mov [ rsp + 0x160 ], r9
mulx r9, rax, rdi
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x168 ], r10
mov [ rsp + 0x170 ], rbp
mulx rbp, r10, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x178 ], r10
mov [ rsp + 0x180 ], r9
mulx r9, r10, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x188 ], r9
mov [ rsp + 0x190 ], rax
mulx rax, r9, [ rsi + 0x28 ]
adcx rbx, [ rsp - 0x28 ]
seto dl
mov [ rsp + 0x198 ], rbx
mov rbx, -0x2 
inc rbx
adox r13, rbp
adcx r15, rcx
adcx r9, r11
mov cl, dl
mov rdx, [ rsi + 0x20 ]
mulx rbp, r11, [ rsi + 0x18 ]
adox r8, [ rsp + 0x118 ]
adox r14, [ rsp + 0x68 ]
adox r11, [ rsp + 0x58 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x1a0 ], r9
mulx r9, rbx, rdi
adcx r10, rax
setc al
clc
adcx r9, [ rsp + 0x190 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1a8 ], r10
mov [ rsp + 0x1b0 ], r15
mulx r15, r10, [ rsi + 0x28 ]
mov rdx, 0xfffffffffffffffe 
mov byte [ rsp + 0x1b8 ], al
mov [ rsp + 0x1c0 ], r11
mulx r11, rax, rdi
adcx rax, [ rsp + 0x180 ]
adox r10, rbp
seto dil
mov rbp, -0x2 
inc rbp
adox rbx, r12
adox r9, [ rsp + 0x130 ]
movzx rbx, dil
lea rbx, [ rbx + r15 ]
adcx r11, [ rsp + 0x170 ]
mov r12, [ rsp + 0x168 ]
mov r15, r12
adcx r15, [ rsp + 0x170 ]
mov rdi, r12
adcx rdi, [ rsp + 0x170 ]
adox rax, [ rsp + 0x160 ]
adox r11, [ rsp + 0x148 ]
mov rbp, [ rsp + 0x140 ]
setc dl
mov [ rsp + 0x1c8 ], rbx
movzx rbx, byte [ rsp + 0x158 ]
clc
mov [ rsp + 0x1d0 ], r10
mov r10, -0x1 
adcx rbx, r10
adcx rbp, [ rsp + 0xa0 ]
movzx rbx, dl
lea rbx, [ rbx + r12 ]
setc r12b
clc
adcx r9, [ rsp + 0x178 ]
mov rdx, 0x100000001 
mov [ rsp + 0x1d8 ], rbx
mulx rbx, r10, r9
adcx r13, rax
mov rbx, 0xfffffffffffffffe 
mov rdx, r10
mulx rax, r10, rbx
adcx r8, r11
mov r11, 0xffffffff 
mov [ rsp + 0x1e0 ], rdi
mulx rdi, rbx, r11
adox r15, rbp
mov rbp, 0xffffffff00000000 
mov byte [ rsp + 0x1e8 ], r12b
mulx r12, r11, rbp
adcx r14, r15
setc r15b
clc
adcx r11, rdi
mov rdi, 0xffffffffffffffff 
mov byte [ rsp + 0x1f0 ], r15b
mulx r15, rbp, rdi
adcx r10, r12
mov rdx, rbp
adcx rdx, rax
mov rax, [ rsp + 0x138 ]
seto r12b
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
movzx rcx, cl
adox rcx, rdi
adox rax, [ rsp + 0x120 ]
mov rcx, rbp
adcx rcx, r15
seto dil
mov [ rsp + 0x1f8 ], rcx
mov rcx, -0x2 
inc rcx
adox rbx, r9
adox r11, r13
adox r10, r8
adcx rbp, r15
setc bl
clc
adcx r11, [ rsp + 0x8 ]
movzx r9, bl
lea r9, [ r9 + r15 ]
adcx r10, [ rsp - 0x8 ]
mov r13, 0x100000001 
xchg rdx, r13
mulx r15, r8, r11
adox r13, r14
mov r15, 0xffffffffffffffff 
mov rdx, r8
mulx r14, r8, r15
seto bl
movzx rcx, byte [ rsp + 0x1e8 ]
mov r15, 0x0 
dec r15
adox rcx, r15
adox rax, [ rsp + 0xe0 ]
setc cl
clc
movzx r12, r12b
adcx r12, r15
adcx rax, [ rsp + 0x1e0 ]
movzx r12, dil
movzx r15, byte [ rsp + 0x128 ]
lea r12, [ r12 + r15 ]
adox r12, [ rsp + 0x110 ]
adcx r12, [ rsp + 0x1d8 ]
seto r15b
adc r15b, 0x0
movzx r15, r15b
add byte [ rsp + 0x1f0 ], 0xFF
adcx rax, [ rsp + 0x1c0 ]
mov rdi, -0x1 
movzx rbx, bl
adox rbx, rdi
adox rax, [ rsp + 0x1f8 ]
adcx r12, [ rsp + 0x1d0 ]
adox rbp, r12
movzx r15, r15b
movzx rbx, r15b
adcx rbx, [ rsp + 0x1c8 ]
adox r9, rbx
seto r15b
adc r15b, 0x0
movzx r15, r15b
add cl, 0x7F
adox r13, [ rsp + 0x50 ]
mov rcx, 0xffffffff 
mulx rbx, r12, rcx
adox rax, [ rsp + 0x48 ]
adox rbp, [ rsp + 0x40 ]
mov rdi, 0xffffffff00000000 
mov [ rsp + 0x200 ], rbp
mulx rbp, rcx, rdi
adox r9, [ rsp + 0x60 ]
adcx rcx, rbx
setc bl
clc
adcx r12, r11
mov r12, 0xfffffffffffffffe 
mulx rdi, r11, r12
movzx r15, r15b
movzx rdx, r15b
adox rdx, [ rsp + 0xd8 ]
adcx rcx, r10
seto r10b
mov r15, 0x0 
dec r15
movzx rbx, bl
adox rbx, r15
adox rbp, r11
adcx rbp, r13
mov r13, r8
adox r13, rdi
mov rbx, r8
adox rbx, r14
adox r8, r14
adcx r13, rax
adcx rbx, [ rsp + 0x200 ]
mov rax, 0x0 
adox r14, rax
mov r11, -0x3 
inc r11
adox rcx, [ rsp + 0x0 ]
mov rdi, 0x100000001 
xchg rdx, rdi
mulx r11, rax, rcx
adox rbp, [ rsp + 0x150 ]
mov r11, 0xffffffff00000000 
mov rdx, rax
mulx r15, rax, r11
mov r11, 0xffffffff 
mov [ rsp + 0x208 ], rbp
mulx rbp, r12, r11
adcx r8, r9
adcx r14, rdi
movzx r9, r10b
mov rdi, 0x0 
adcx r9, rdi
movzx r10, byte [ rsp + 0x1b8 ]
mov rdi, [ rsp + 0x188 ]
lea r10, [ r10 + rdi ]
adox r13, [ rsp + 0x198 ]
adox rbx, [ rsp + 0x1b0 ]
adox r8, [ rsp + 0x1a0 ]
clc
adcx rax, rbp
mov rdi, 0xfffffffffffffffe 
mulx r11, rbp, rdi
adcx rbp, r15
mov r15, 0xffffffffffffffff 
mov [ rsp + 0x210 ], r8
mulx r8, rdi, r15
adox r14, [ rsp + 0x1a8 ]
mov rdx, rdi
adcx rdx, r11
adox r10, r9
seto r9b
mov r11, -0x2 
inc r11
adox r12, rcx
adox rax, [ rsp + 0x208 ]
adox rbp, r13
mov r12, rdi
adcx r12, r8
adcx rdi, r8
adox rdx, rbx
adox r12, [ rsp + 0x210 ]
mov rcx, 0x0 
adcx r8, rcx
adox rdi, r14
adox r8, r10
movzx r13, r9b
adox r13, rcx
mov rbx, rax
mov r14, 0xffffffff 
sub rbx, r14
mov r9, rbp
mov r10, 0xffffffff00000000 
sbb r9, r10
mov rcx, rdx
mov r11, 0xfffffffffffffffe 
sbb rcx, r11
mov r14, r12
sbb r14, r15
mov r10, rdi
sbb r10, r15
mov r11, r8
sbb r11, r15
sbb r13, 0x00000000
cmovc r11, r8
cmovc r14, r12
cmovc rcx, rdx
cmovc r10, rdi
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x10 ], rcx
mov [ r13 + 0x20 ], r10
mov [ r13 + 0x28 ], r11
cmovc r9, rbp
cmovc rbx, rax
mov [ r13 + 0x0 ], rbx
mov [ r13 + 0x8 ], r9
mov [ r13 + 0x18 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 664
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.4219
; seed 1833930431116767 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3878265 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=87, initial num_batches=31): 118597 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.030579911377897076
; number reverted permutation / tried permutation: 70755 / 89951 =78.659%
; number reverted decision / tried decision: 64273 / 90048 =71.376%
; validated in 20.342s
