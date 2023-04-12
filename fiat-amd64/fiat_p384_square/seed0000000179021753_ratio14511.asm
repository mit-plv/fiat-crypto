SECTION .text
	GLOBAL fiat_p384_square
fiat_p384_square:
sub rsp, 576
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov r11, 0x100000001 
mov rdx, rax
mulx rcx, rax, r11
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
mov rdx, 0xffffffff 
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rax
mov [ rsp - 0x60 ], r14
mov r14, 0xfffffffffffffffe 
mov rdx, r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rax
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, r11, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x48 ], rbx
mov [ rsp - 0x40 ], rdi
mulx rdi, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x38 ], rbx
mov [ rsp - 0x30 ], rdi
mulx rdi, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], rdi
mov [ rsp - 0x20 ], rbx
mulx rbx, rdi, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x18 ], r11
mov [ rsp - 0x10 ], rbx
mulx rbx, r11, [ rsi + 0x20 ]
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x8 ], rbx
mov [ rsp + 0x0 ], r11
mulx r11, rbx, rax
xor rdx, rdx
adox rbx, r13
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x8 ], rdi
mulx rdi, r13, [ rsi + 0x8 ]
adox r14, r11
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x10 ], rdi
mulx rdi, r11, [ rsi + 0x28 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x18 ], r13
mov [ rsp + 0x20 ], rdi
mulx rdi, r13, rax
mov rax, r13
adox rax, r15
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x28 ], r11
mulx r11, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x30 ], r15
mov [ rsp + 0x38 ], rbp
mulx rbp, r15, [ rsi + 0x8 ]
adcx r15, r11
mov rdx, r13
adox rdx, rdi
adox r13, rdi
mov r11, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x40 ], r15
mov [ rsp + 0x48 ], r13
mulx r13, r15, [ rsi + 0x10 ]
mov rdx, 0x0 
adox rdi, rdx
adcx r15, rbp
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x50 ], r15
mulx r15, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x58 ], rdi
mov [ rsp + 0x60 ], r13
mulx r13, rdi, [ rsi + 0x18 ]
mov rdx, -0x2 
inc rdx
adox r12, rcx
setc r12b
clc
adcx rbp, r10
adox rbx, rbp
adcx r8, r15
adox r14, r8
mov rdx, [ rsi + 0x0 ]
mulx r10, rcx, [ rsi + 0x20 ]
adcx rdi, r9
adox rax, rdi
adcx rcx, r13
mov rdx, [ rsi + 0x0 ]
mulx r15, r9, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mulx rbp, r13, [ rsi + 0x18 ]
adcx r9, r10
mov rdx, [ rsi + 0x28 ]
mulx r10, r8, [ rsi + 0x18 ]
mov rdx, 0x0 
adcx r15, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x68 ], rax
mulx rax, rdi, rdx
adox r11, rcx
clc
mov rdx, -0x1 
movzx r12, r12b
adcx r12, rdx
adcx rdi, [ rsp + 0x60 ]
adcx r13, rax
adcx r8, rbp
adox r9, [ rsp + 0x48 ]
mov rdx, [ rsi + 0x18 ]
mulx rcx, r12, [ rsi + 0x8 ]
mov rdx, 0x0 
adcx r10, rdx
adox r15, [ rsp + 0x58 ]
mov rbp, [ rsp + 0x38 ]
clc
adcx rbp, [ rsp + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x70 ], r10
mulx r10, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x78 ], r8
mov [ rsp + 0x80 ], r13
mulx r13, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x88 ], rdi
mov [ rsp + 0x90 ], r8
mulx r8, rdi, [ rsi + 0x8 ]
adcx rdi, [ rsp - 0x10 ]
adcx r12, r8
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x98 ], r15
mulx r15, r8, rdx
seto dl
mov [ rsp + 0xa0 ], r9
mov r9, -0x2 
inc r9
adox rax, r13
adox r8, r10
mov r10b, dl
mov rdx, [ rsi + 0x10 ]
mulx r9, r13, [ rsi + 0x18 ]
adox r13, r15
adox r9, [ rsp - 0x18 ]
adcx rcx, [ rsp + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xa8 ], r9
mulx r9, r15, [ rsi + 0x28 ]
mov rdx, [ rsp - 0x20 ]
adcx rdx, [ rsp - 0x8 ]
adox r15, [ rsp - 0x40 ]
mov [ rsp + 0xb0 ], r15
seto r15b
mov [ rsp + 0xb8 ], r9
mov r9, -0x2 
inc r9
adox rbx, [ rsp - 0x48 ]
mov r9, 0x100000001 
xchg rdx, r9
mov byte [ rsp + 0xc0 ], r15b
mov [ rsp + 0xc8 ], r13
mulx r13, r15, rbx
mov r13, 0xffffffffffffffff 
mov rdx, r15
mov [ rsp + 0xd0 ], r8
mulx r8, r15, r13
adox rbp, r14
adox rdi, [ rsp + 0x68 ]
adox r12, r11
mov r14, [ rsp - 0x28 ]
mov r11, 0x0 
adcx r14, r11
adox rcx, [ rsp + 0xa0 ]
mov r11, 0xfffffffffffffffe 
mov [ rsp + 0xd8 ], rcx
mulx rcx, r13, r11
mov r11, 0xffffffff00000000 
mov [ rsp + 0xe0 ], rax
mov [ rsp + 0xe8 ], r12
mulx r12, rax, r11
mov r11, 0xffffffff 
mov [ rsp + 0xf0 ], rdi
mov [ rsp + 0xf8 ], rbp
mulx rbp, rdi, r11
clc
adcx rax, rbp
adcx r13, r12
mov rdx, r15
adcx rdx, rcx
mov rcx, r15
adcx rcx, r8
adcx r15, r8
adox r9, [ rsp + 0x98 ]
mov r12, 0x0 
adcx r8, r12
movzx rbp, r10b
adox rbp, r14
mov r10, rdx
mov rdx, [ rsi + 0x28 ]
mulx r12, r14, [ rsi + 0x10 ]
clc
adcx rdi, rbx
adcx rax, [ rsp + 0xf8 ]
adcx r13, [ rsp + 0xf0 ]
adcx r10, [ rsp + 0xe8 ]
seto dil
mov rdx, -0x2 
inc rdx
adox rax, [ rsp + 0x90 ]
mov rbx, 0x100000001 
mov rdx, rax
mulx r11, rax, rbx
adox r13, [ rsp + 0xe0 ]
adox r10, [ rsp + 0xd0 ]
adcx rcx, [ rsp + 0xd8 ]
adox rcx, [ rsp + 0xc8 ]
adcx r15, r9
mov r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx rbx, r9, [ rsi + 0x28 ]
adcx r8, rbp
adox r15, [ rsp + 0xa8 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x100 ], r15
mulx r15, rbp, rax
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x108 ], rcx
mov [ rsp + 0x110 ], r10
mulx r10, rcx, [ rsi + 0x28 ]
seto dl
mov [ rsp + 0x118 ], r13
mov r13, -0x2 
inc r13
adox r9, [ rsp - 0x30 ]
adox r14, rbx
adox rcx, r12
adox r10, [ rsp + 0x28 ]
mov r12, 0xfffffffffffffffe 
xchg rdx, rax
mulx r13, rbx, r12
mov r12, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x120 ], r10
mov [ rsp + 0x128 ], rcx
mulx rcx, r10, rdx
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x130 ], rcx
mov [ rsp + 0x138 ], r14
mulx r14, rcx, r12
adox r10, [ rsp + 0x20 ]
seto dl
mov [ rsp + 0x140 ], r10
mov r10, -0x2 
inc r10
adox rcx, r15
movzx r15, byte [ rsp + 0xc0 ]
mov r10, [ rsp + 0xb8 ]
lea r15, [ r15 + r10 ]
movzx r10, dil
mov byte [ rsp + 0x148 ], dl
mov rdx, 0x0 
adcx r10, rdx
adox rbx, r14
mov rdi, 0xffffffffffffffff 
mov rdx, rdi
mulx r14, rdi, r12
clc
mov r12, -0x1 
movzx rax, al
adcx rax, r12
adcx r8, [ rsp + 0xb0 ]
mov rax, rdi
adox rax, r13
adcx r15, r10
setc r13b
clc
adcx rbp, r11
adcx rcx, [ rsp + 0x118 ]
mov rbp, rdi
adox rbp, r14
adcx rbx, [ rsp + 0x110 ]
adcx rax, [ rsp + 0x108 ]
adcx rbp, [ rsp + 0x100 ]
adox rdi, r14
mov rdx, [ rsi + 0x20 ]
mulx r10, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x150 ], r9
mulx r9, r12, [ rsi + 0x0 ]
adcx rdi, r8
mov rdx, 0x0 
adox r14, rdx
adcx r14, r15
movzx r8, r13b
adc r8, 0x0
test al, al
adox rcx, [ rsp + 0x30 ]
adox rbx, [ rsp + 0x40 ]
adox rax, [ rsp + 0x50 ]
mov rdx, [ rsi + 0x20 ]
mulx r15, r13, [ rsi + 0x10 ]
adox rbp, [ rsp + 0x88 ]
adox rdi, [ rsp + 0x80 ]
adox r14, [ rsp + 0x78 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x158 ], r14
mov [ rsp + 0x160 ], rdi
mulx rdi, r14, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x168 ], rdi
mov [ rsp + 0x170 ], rbp
mulx rbp, rdi, rdx
adcx r9, [ rsp + 0x18 ]
adcx r13, [ rsp + 0x10 ]
adcx r11, r15
mov rdx, 0x100000001 
mov [ rsp + 0x178 ], r11
mulx r11, r15, rcx
adox r8, [ rsp + 0x70 ]
mov r11, 0xffffffff00000000 
mov rdx, r11
mov [ rsp + 0x180 ], r8
mulx r8, r11, r15
adcx rdi, r10
mov r10, 0xffffffff 
mov rdx, r10
mov [ rsp + 0x188 ], rdi
mulx rdi, r10, r15
seto dl
mov [ rsp + 0x190 ], r13
mov r13, -0x2 
inc r13
adox r10, rcx
adcx r14, rbp
mov r10, 0xfffffffffffffffe 
xchg rdx, r10
mulx rbp, rcx, r15
setc r13b
clc
adcx r11, rdi
adcx rcx, r8
mov r8, 0xffffffffffffffff 
mov rdx, r15
mulx rdi, r15, r8
mov rdx, r15
adcx rdx, rbp
mov rbp, r15
adcx rbp, rdi
adcx r15, rdi
mov r8, 0x0 
adcx rdi, r8
adox r11, rbx
adox rcx, rax
clc
adcx r12, r11
adox rdx, [ rsp + 0x170 ]
adox rbp, [ rsp + 0x160 ]
adox r15, [ rsp + 0x158 ]
mov rbx, 0x100000001 
xchg rdx, r12
mulx r11, rax, rbx
adcx r9, rcx
adcx r12, [ rsp + 0x190 ]
adcx rbp, [ rsp + 0x178 ]
adcx r15, [ rsp + 0x188 ]
adox rdi, [ rsp + 0x180 ]
movzx r11, r10b
adox r11, r8
adcx r14, rdi
mov r10, 0xffffffff00000000 
xchg rdx, rax
mulx rdi, rcx, r10
movzx r8, r13b
mov r10, [ rsp + 0x168 ]
lea r8, [ r8 + r10 ]
adcx r8, r11
mov r10, 0xffffffff 
mulx r11, r13, r10
mov r10, 0xfffffffffffffffe 
mov [ rsp + 0x198 ], r8
mulx r8, rbx, r10
mov r10, -0x2 
inc r10
adox r13, rax
setc r13b
clc
adcx rcx, r11
adox rcx, r9
adcx rbx, rdi
mov rax, 0xffffffffffffffff 
mulx rdi, r9, rax
adox rbx, r12
mov rdx, r9
adcx rdx, r8
mov r12, r9
adcx r12, rdi
adcx r9, rdi
mov r11, 0x0 
adcx rdi, r11
adox rdx, rbp
clc
adcx rcx, [ rsp - 0x38 ]
mov rbp, 0x100000001 
xchg rdx, rcx
mulx r11, r8, rbp
adox r12, r15
adox r9, r14
adox rdi, [ rsp + 0x198 ]
adcx rbx, [ rsp + 0x150 ]
movzx r11, r13b
mov r15, 0x0 
adox r11, r15
adcx rcx, [ rsp + 0x138 ]
adcx r12, [ rsp + 0x128 ]
adcx r9, [ rsp + 0x120 ]
movzx r14, byte [ rsp + 0x148 ]
mov r13, [ rsp + 0x130 ]
lea r14, [ r14 + r13 ]
adcx rdi, [ rsp + 0x140 ]
mov r13, 0xffffffff00000000 
xchg rdx, r8
mulx r10, r15, r13
mulx rbp, r13, rax
mov rax, 0xffffffff 
mov [ rsp + 0x1a0 ], rdi
mov [ rsp + 0x1a8 ], r9
mulx r9, rdi, rax
mov rax, 0xfffffffffffffffe 
mov [ rsp + 0x1b0 ], r14
mov [ rsp + 0x1b8 ], r11
mulx r11, r14, rax
mov rdx, -0x2 
inc rdx
adox r15, r9
adox r14, r10
setc r10b
clc
adcx rdi, r8
adcx r15, rbx
adcx r14, rcx
mov rdi, r13
adox rdi, r11
mov r8, r13
adox r8, rbp
adcx rdi, r12
adox r13, rbp
mov rbx, [ rsp + 0x1b8 ]
setc cl
clc
movzx r10, r10b
adcx r10, rdx
adcx rbx, [ rsp + 0x1b0 ]
seto r12b
inc rdx
mov r10, -0x1 
movzx rcx, cl
adox rcx, r10
adox r8, [ rsp + 0x1a8 ]
movzx r9, r12b
lea r9, [ r9 + rbp ]
adox r13, [ rsp + 0x1a0 ]
adox r9, rbx
seto bpl
adc bpl, 0x0
movzx rbp, bpl
mov r11, r15
mov rcx, 0xffffffff 
sub r11, rcx
mov r12, r14
mov rbx, 0xffffffff00000000 
sbb r12, rbx
mov rdx, rdi
sbb rdx, rax
mov r10, r8
mov rcx, 0xffffffffffffffff 
sbb r10, rcx
mov rbx, r13
sbb rbx, rcx
mov rax, r9
sbb rax, rcx
movzx rcx, bpl
sbb rcx, 0x00000000
cmovc rbx, r13
cmovc r11, r15
cmovc rdx, rdi
cmovc r12, r14
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x10 ], rdx
mov [ rcx + 0x8 ], r12
cmovc rax, r9
mov [ rcx + 0x20 ], rbx
mov [ rcx + 0x28 ], rax
cmovc r10, r8
mov [ rcx + 0x18 ], r10
mov [ rcx + 0x0 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 576
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.4511
; seed 0971580335559318 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4970963 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=58, initial num_batches=31): 127810 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.025711315895934048
; number reverted permutation / tried permutation: 65638 / 89943 =72.977%
; number reverted decision / tried decision: 48095 / 90056 =53.406%
; validated in 31.312s
