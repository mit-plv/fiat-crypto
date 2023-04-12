SECTION .text
	GLOBAL fiat_p384_square
fiat_p384_square:
sub rsp, 560
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov r11, 0x100000001 
mov rdx, rax
mulx rcx, rax, r11
mov rcx, rdx
mov rdx, [ rsi + 0x28 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x48 ], rdi
mov [ rsp - 0x40 ], r11
mulx r11, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x38 ], r13
mov [ rsp - 0x30 ], r12
mulx r12, r13, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x28 ], rbp
mov [ rsp - 0x20 ], rbx
mulx rbx, rbp, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x18 ], r9
mov [ rsp - 0x10 ], r15
mulx r15, r9, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x8 ], r14
mov [ rsp + 0x0 ], r12
mulx r12, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x8 ], r8
mov [ rsp + 0x10 ], r11
mulx r11, r8, [ rsi + 0x8 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x18 ], rdi
mov [ rsp + 0x20 ], r11
mulx r11, rdi, rax
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x28 ], r12
mov [ rsp + 0x30 ], r14
mulx r14, r12, [ rsi + 0x28 ]
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x38 ], r14
mov [ rsp + 0x40 ], r12
mulx r12, r14, rax
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x48 ], rbx
mov [ rsp + 0x50 ], rbp
mulx rbp, rbx, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x58 ], rbp
mov [ rsp + 0x60 ], rbx
mulx rbx, rbp, [ rsi + 0x0 ]
test al, al
adox rdi, rcx
mov rdi, 0xfffffffffffffffe 
mov rdx, rdi
mulx rcx, rdi, rax
adcx r14, r11
adcx rdi, r12
mov rdx, [ rsi + 0x0 ]
mulx r12, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x68 ], rbp
mov [ rsp + 0x70 ], rbx
mulx rbx, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x78 ], r11
mov [ rsp + 0x80 ], rdi
mulx rdi, r11, [ rsi + 0x0 ]
seto dl
mov [ rsp + 0x88 ], r11
mov r11, -0x2 
inc r11
adox r13, r12
seto r12b
inc r11
adox r8, rdi
seto dil
mov [ rsp + 0x90 ], r8
mov r8, -0x3 
inc r8
adox r9, r10
mov r10, 0xffffffffffffffff 
xchg rdx, rax
mulx r8, r11, r10
mov rdx, r11
adcx rdx, rcx
mov rcx, r11
adcx rcx, r8
adcx r11, r8
mov r10, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x98 ], r13
mov byte [ rsp + 0xa0 ], r12b
mulx r12, r13, [ rsi + 0x0 ]
adox rbp, r15
mov rdx, 0x0 
adcx r8, rdx
mov rdx, [ rsi + 0x0 ]
mov byte [ rsp + 0xa8 ], dil
mulx rdi, r15, [ rsi + 0x20 ]
adox rbx, [ rsp + 0x50 ]
adox r15, [ rsp + 0x48 ]
adox r13, rdi
mov rdx, 0x0 
adox r12, rdx
add al, 0xFF
adcx r9, r14
adcx rbp, [ rsp + 0x80 ]
adcx r10, rbx
mov rdx, [ rsi + 0x0 ]
mulx r14, rax, [ rsi + 0x8 ]
adox rax, r9
adcx rcx, r15
mov rdx, [ rsi + 0x8 ]
mulx rbx, rdi, rdx
mov rdx, 0x100000001 
mulx r9, r15, rax
adcx r11, r13
mov r9, 0xffffffffffffffff 
mov rdx, r15
mulx r13, r15, r9
adcx r8, r12
mov r12, 0xfffffffffffffffe 
mov [ rsp + 0xb0 ], r13
mulx r13, r9, r12
setc r12b
clc
adcx rdi, r14
mov r14, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xb8 ], r15
mov [ rsp + 0xc0 ], r13
mulx r13, r15, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov byte [ rsp + 0xc8 ], r12b
mov [ rsp + 0xd0 ], r9
mulx r9, r12, [ rsi + 0x8 ]
adcx rbx, [ rsp + 0x30 ]
adcx r15, [ rsp + 0x28 ]
adox rdi, rbp
adox rbx, r10
adox r15, rcx
mov rdx, [ rsi + 0x8 ]
mulx r10, rbp, [ rsi + 0x20 ]
adcx rbp, r13
adox rbp, r11
adcx r12, r10
mov rdx, 0x0 
adcx r9, rdx
adox r12, r8
mov rcx, 0xffffffff 
mov rdx, rcx
mulx r11, rcx, r14
mov r8, 0xffffffff00000000 
mov rdx, r8
mulx r13, r8, r14
clc
adcx r8, r11
adcx r13, [ rsp + 0xd0 ]
movzx r14, byte [ rsp + 0xc8 ]
adox r14, r9
mov r10, [ rsp + 0xc0 ]
adcx r10, [ rsp + 0xb8 ]
mov r9, [ rsp + 0xb8 ]
mov r11, r9
adcx r11, [ rsp + 0xb0 ]
seto dl
mov [ rsp + 0xd8 ], r14
mov r14, -0x2 
inc r14
adox rcx, rax
adox r8, rdi
adcx r9, [ rsp + 0xb0 ]
setc cl
clc
adcx r8, [ rsp + 0x78 ]
mov rax, 0x100000001 
xchg rdx, rax
mulx r14, rdi, r8
adox r13, rbx
adox r10, r15
mov rdx, [ rsi + 0x10 ]
mulx rbx, r14, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0xe0 ], r10
mulx r10, r15, rdi
adox r11, rbp
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xe8 ], r11
mulx r11, rbp, [ rsi + 0x20 ]
adox r9, r12
movzx rdx, cl
mov r12, [ rsp + 0xb0 ]
lea rdx, [ rdx + r12 ]
mov r12, 0xffffffff 
xchg rdx, r12
mov [ rsp + 0xf0 ], r9
mulx r9, rcx, rdi
mov rdx, [ rsp + 0x20 ]
mov [ rsp + 0xf8 ], rcx
setc cl
mov [ rsp + 0x100 ], r13
movzx r13, byte [ rsp + 0xa8 ]
clc
mov [ rsp + 0x108 ], rbx
mov rbx, -0x1 
adcx r13, rbx
adcx rdx, [ rsp + 0x18 ]
adox r12, [ rsp + 0xd8 ]
adcx rbp, [ rsp + 0x10 ]
movzx r13, al
mov rbx, 0x0 
adox r13, rbx
adcx r11, [ rsp + 0x60 ]
mov rax, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x110 ], r11
mulx r11, rbx, [ rsi + 0x20 ]
adcx rbx, [ rsp + 0x58 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x118 ], rbx
mov [ rsp + 0x120 ], rbp
mulx rbp, rbx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x128 ], rax
mov [ rsp + 0x130 ], r13
mulx r13, rax, [ rsi + 0x10 ]
mov rdx, [ rsp + 0x70 ]
mov [ rsp + 0x138 ], r12
mov r12, -0x2 
inc r12
adox rdx, [ rsp + 0x40 ]
adox rax, [ rsp + 0x38 ]
mov r12, 0x0 
adcx r11, r12
mov r12, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x140 ], rax
mov [ rsp + 0x148 ], r11
mulx r11, rax, [ rsi + 0x20 ]
adox rbx, r13
adox rax, rbp
mov rdx, 0xfffffffffffffffe 
mulx r13, rbp, rdi
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x150 ], rax
mov [ rsp + 0x158 ], rbx
mulx rbx, rax, rdi
clc
adcx rax, r9
adcx rbp, rbx
mov rdi, r15
adcx rdi, r13
adox r11, [ rsp + 0x8 ]
mov r9, r15
adcx r9, r10
adcx r15, r10
mov r13, 0x0 
adcx r10, r13
movzx rbx, byte [ rsp + 0xa0 ]
clc
mov r13, -0x1 
adcx rbx, r13
adcx r14, [ rsp + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mulx r13, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x160 ], r11
mov [ rsp + 0x168 ], r12
mulx r12, r11, [ rsi + 0x10 ]
adcx r11, [ rsp + 0x108 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x170 ], r13
mov [ rsp + 0x178 ], rbx
mulx rbx, r13, [ rsi + 0x10 ]
adcx r13, r12
mov rdx, [ rsp + 0x100 ]
seto r12b
mov [ rsp + 0x180 ], r10
mov r10, 0x0 
dec r10
movzx rcx, cl
adox rcx, r10
adox rdx, [ rsp + 0x98 ]
adox r14, [ rsp + 0xe0 ]
adox r11, [ rsp + 0xe8 ]
adox r13, [ rsp + 0xf0 ]
adcx rbx, [ rsp - 0x8 ]
mov rcx, [ rsp - 0x10 ]
mov r10, 0x0 
adcx rcx, r10
adox rbx, [ rsp + 0x138 ]
adox rcx, [ rsp + 0x130 ]
clc
adcx r8, [ rsp + 0xf8 ]
adcx rax, rdx
adcx rbp, r14
adcx rdi, r11
adcx r9, r13
movzx r8, r12b
mov rdx, [ rsp - 0x18 ]
lea r8, [ r8 + rdx ]
adcx r15, rbx
adcx rcx, [ rsp + 0x180 ]
mov rdx, [ rsi + 0x8 ]
mulx r14, r12, [ rsi + 0x18 ]
seto dl
adc dl, 0x0
movzx rdx, dl
adox rax, [ rsp - 0x20 ]
mov r11, 0x100000001 
xchg rdx, r11
mulx rbx, r13, rax
adcx r12, [ rsp - 0x28 ]
mov rbx, 0xffffffff00000000 
mov rdx, rbx
mulx r10, rbx, r13
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x188 ], r8
mov byte [ rsp + 0x190 ], r11b
mulx r11, r8, [ rsi + 0x28 ]
adcx r14, [ rsp + 0x178 ]
adox r12, rbp
mov rdx, [ rsp - 0x30 ]
adcx rdx, [ rsp + 0x170 ]
adox r14, rdi
adox rdx, r9
mov rbp, [ rsp - 0x38 ]
adcx rbp, [ rsp - 0x40 ]
adcx r8, [ rsp - 0x48 ]
adox rbp, r15
mov rdi, 0xffffffff 
xchg rdx, r13
mulx r15, r9, rdi
mov rdi, 0x0 
adcx r11, rdi
adox r8, rcx
mov rcx, 0xfffffffffffffffe 
mov [ rsp + 0x198 ], r8
mulx r8, rdi, rcx
clc
adcx rbx, r15
adcx rdi, r10
mov r10, 0xffffffffffffffff 
mulx rcx, r15, r10
mov rdx, r15
adcx rdx, r8
mov r8, r15
adcx r8, rcx
adcx r15, rcx
movzx r10, byte [ rsp + 0x190 ]
adox r10, r11
mov r11, 0x0 
adcx rcx, r11
clc
adcx r9, rax
adcx rbx, r12
adcx rdi, r14
adcx rdx, r13
seto r9b
mov rax, -0x3 
inc rax
adox rbx, [ rsp + 0x88 ]
adox rdi, [ rsp + 0x90 ]
adcx r8, rbp
mov r12, 0x100000001 
xchg rdx, r12
mulx r13, r14, rbx
adcx r15, [ rsp + 0x198 ]
mov r13, 0xfffffffffffffffe 
mov rdx, r14
mulx rbp, r14, r13
adox r12, [ rsp + 0x128 ]
adcx rcx, r10
movzx r10, r9b
adcx r10, r11
adox r8, [ rsp + 0x120 ]
mov r9, 0xffffffff00000000 
mulx rax, r11, r9
mov r9, 0xffffffff 
mov [ rsp + 0x1a0 ], r8
mulx r8, r13, r9
clc
adcx r11, r8
mov r8, 0xffffffffffffffff 
mov [ rsp + 0x1a8 ], r12
mulx r12, r9, r8
adcx r14, rax
mov rdx, r9
adcx rdx, rbp
mov rbp, r9
adcx rbp, r12
adox r15, [ rsp + 0x110 ]
adcx r9, r12
adox rcx, [ rsp + 0x118 ]
seto al
mov r8, -0x2 
inc r8
adox r13, rbx
adox r11, rdi
setc r13b
clc
movzx rax, al
adcx rax, r8
adcx r10, [ rsp + 0x148 ]
setc bl
clc
adcx r11, [ rsp + 0x68 ]
mov rdi, 0x100000001 
xchg rdx, rdi
mulx r8, rax, r11
movzx r8, r13b
lea r8, [ r8 + r12 ]
adox r14, [ rsp + 0x1a8 ]
adox rdi, [ rsp + 0x1a0 ]
adox rbp, r15
adcx r14, [ rsp + 0x168 ]
adcx rdi, [ rsp + 0x140 ]
mov r12, 0xffffffff00000000 
mov rdx, rax
mulx r15, rax, r12
adox r9, rcx
adox r8, r10
mov r13, 0xffffffff 
mulx r10, rcx, r13
adcx rbp, [ rsp + 0x158 ]
setc r12b
clc
adcx rcx, r11
movzx rcx, bl
mov r11, 0x0 
adox rcx, r11
mov rbx, -0x3 
inc rbx
adox rax, r10
mov r10, 0xfffffffffffffffe 
mulx rbx, r11, r10
adox r11, r15
mov r15, 0xffffffffffffffff 
mulx r10, r13, r15
mov rdx, r13
adox rdx, rbx
adcx rax, r14
mov r14, r13
adox r14, r10
adcx r11, rdi
adox r13, r10
mov rdi, 0x0 
adox r10, rdi
dec rdi
movzx r12, r12b
adox r12, rdi
adox r9, [ rsp + 0x150 ]
adox r8, [ rsp + 0x160 ]
adox rcx, [ rsp + 0x188 ]
adcx rdx, rbp
adcx r14, r9
adcx r13, r8
adcx r10, rcx
seto r12b
adc r12b, 0x0
movzx r12, r12b
mov rbp, rax
mov rbx, 0xffffffff 
sub rbp, rbx
mov r9, r11
mov r8, 0xffffffff00000000 
sbb r9, r8
mov rcx, rdx
mov rdi, 0xfffffffffffffffe 
sbb rcx, rdi
mov r8, r14
sbb r8, r15
mov rbx, r13
sbb rbx, r15
mov rdi, r10
sbb rdi, r15
movzx r15, r12b
sbb r15, 0x00000000
cmovc rbp, rax
cmovc r9, r11
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x0 ], rbp
cmovc r8, r14
cmovc rdi, r10
cmovc rcx, rdx
cmovc rbx, r13
mov [ r15 + 0x10 ], rcx
mov [ r15 + 0x20 ], rbx
mov [ r15 + 0x18 ], r8
mov [ r15 + 0x28 ], rdi
mov [ r15 + 0x8 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 560
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.4180
; seed 2668771966588395 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5180209 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=57, initial num_batches=31): 132789 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.025633907821093704
; number reverted permutation / tried permutation: 63705 / 90079 =70.721%
; number reverted decision / tried decision: 48300 / 89920 =53.714%
; validated in 30.442s
