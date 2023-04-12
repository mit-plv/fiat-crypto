SECTION .text
	GLOBAL fiat_p384_mul
fiat_p384_mul:
sub rsp, 576
mov rax, rdx
mov rdx, [ rdx + 0x20 ]
mulx r11, r10, [ rsi + 0x20 ]
mov rdx, [ rax + 0x10 ]
mulx r8, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x48 ], r15
mov [ rsp - 0x40 ], rbx
mulx rbx, r15, [ rsi + 0x18 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x38 ], r15
mov [ rsp - 0x30 ], rbx
mulx rbx, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], rbx
mov [ rsp - 0x20 ], r15
mulx r15, rbx, [ rax + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x18 ], r15
mov [ rsp - 0x10 ], rbx
mulx rbx, r15, [ rax + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x8 ], rbp
mov [ rsp + 0x0 ], rbx
mulx rbx, rbp, [ rsi + 0x10 ]
test al, al
adox r13, rbx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x8 ], r13
mulx r13, rbx, [ rsi + 0x28 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x10 ], rbx
mov [ rsp + 0x18 ], rbp
mulx rbp, rbx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x20 ], r13
mov [ rsp + 0x28 ], r15
mulx r15, r13, [ rax + 0x28 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x30 ], r15
mov [ rsp + 0x38 ], r13
mulx r13, r15, [ rsi + 0x20 ]
adcx rbx, rdi
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x40 ], rbx
mulx rbx, rdi, [ rsi + 0x20 ]
adcx rdi, rbp
adcx r15, rbx
adcx r10, r13
adox rcx, r14
adox r9, r8
mov rdx, [ rax + 0x8 ]
mulx r14, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mulx r13, rbp, [ rax + 0x28 ]
adcx rbp, r11
mov rdx, [ rax + 0x8 ]
mulx rbx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x48 ], rbp
mov [ rsp + 0x50 ], r10
mulx r10, rbp, [ rax + 0x0 ]
setc dl
clc
adcx r8, r10
mov r10b, dl
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x58 ], r15
mov [ rsp + 0x60 ], rdi
mulx rdi, r15, [ rsi + 0x8 ]
seto dl
mov [ rsp + 0x68 ], r9
mov r9, -0x2 
inc r9
adox r11, r12
adcx r15, r14
adcx rdi, [ rsp + 0x28 ]
mov r12b, dl
mov rdx, [ rsi + 0x8 ]
mulx r9, r14, [ rax + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov byte [ rsp + 0x70 ], r12b
mov [ rsp + 0x78 ], rcx
mulx rcx, r12, [ rax + 0x10 ]
adcx r14, [ rsp + 0x0 ]
mov rdx, 0x100000001 
mov [ rsp + 0x80 ], r14
mov [ rsp + 0x88 ], rdi
mulx rdi, r14, [ rsp - 0x8 ]
mov rdi, 0xffffffff 
mov rdx, r14
mov [ rsp + 0x90 ], r15
mulx r15, r14, rdi
mov rdi, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x98 ], r8
mov [ rsp + 0xa0 ], rbp
mulx rbp, r8, [ rsi + 0x18 ]
adox r12, rbx
adcx r9, [ rsp + 0x38 ]
mov rdx, [ rsp + 0x30 ]
mov rbx, 0x0 
adcx rdx, rbx
mov rbx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xa8 ], r9
mov [ rsp + 0xb0 ], r12
mulx r12, r9, [ rax + 0x18 ]
clc
adcx r8, [ rsp - 0x30 ]
adcx rbp, [ rsp - 0x10 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xb8 ], rbp
mov [ rsp + 0xc0 ], r8
mulx r8, rbp, [ rsi + 0x0 ]
adox r9, rcx
adox rbp, r12
mov rdx, 0xfffffffffffffffe 
mulx r12, rcx, rdi
adox r8, [ rsp - 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xc8 ], rbx
mov [ rsp + 0xd0 ], r8
mulx r8, rbx, [ rax + 0x18 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0xd8 ], rbp
mov [ rsp + 0xe0 ], r9
mulx r9, rbp, rdi
mov rdx, 0xffffffff00000000 
mov [ rsp + 0xe8 ], r11
mov [ rsp + 0xf0 ], r14
mulx r14, r11, rdi
setc dil
clc
adcx r11, r15
adcx rcx, r14
mov r15, rbp
adcx r15, r12
mov r12, rbp
adcx r12, r9
adcx rbp, r9
movzx r14, r10b
lea r14, [ r14 + r13 ]
mov r13, 0x0 
adcx r9, r13
mov rdx, [ rsi + 0x18 ]
mulx r13, r10, [ rax + 0x20 ]
clc
mov rdx, -0x1 
movzx rdi, dil
adcx rdi, rdx
adcx rbx, [ rsp - 0x18 ]
adcx r10, r8
mov rdi, [ rsp + 0xf0 ]
seto r8b
inc rdx
adox rdi, [ rsp - 0x8 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xf8 ], r14
mulx r14, rdi, [ rsi + 0x18 ]
adcx rdi, r13
adox r11, [ rsp + 0xe8 ]
setc dl
clc
adcx r11, [ rsp + 0xa0 ]
adox rcx, [ rsp + 0xb0 ]
adcx rcx, [ rsp + 0x98 ]
adox r15, [ rsp + 0xe0 ]
adox r12, [ rsp + 0xd8 ]
movzx r13, dl
lea r13, [ r13 + r14 ]
adcx r15, [ rsp + 0x90 ]
adox rbp, [ rsp + 0xd0 ]
mov r14, 0x100000001 
mov rdx, r14
mov [ rsp + 0x100 ], r13
mulx r13, r14, r11
movzx r13, r8b
mov rdx, [ rsp - 0x28 ]
lea r13, [ r13 + rdx ]
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x108 ], rdi
mulx rdi, r8, r14
adcx r12, [ rsp + 0x88 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x110 ], r10
mov [ rsp + 0x118 ], rbx
mulx rbx, r10, r14
adcx rbp, [ rsp + 0x80 ]
adox r9, r13
adcx r9, [ rsp + 0xa8 ]
mov r13, 0xffffffff00000000 
mov rdx, r14
mov [ rsp + 0x120 ], r9
mulx r9, r14, r13
setc r13b
clc
adcx r14, rbx
adcx r8, r9
mov rbx, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x128 ], rbp
mulx rbp, r9, [ rax + 0x8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x130 ], rbp
mov [ rsp + 0x138 ], r9
mulx r9, rbp, rbx
mov rbx, rbp
adcx rbx, rdi
mov rdi, rbp
adcx rdi, r9
adcx rbp, r9
movzx r13, r13b
movzx rdx, r13b
adox rdx, [ rsp + 0xc8 ]
seto r13b
mov [ rsp + 0x140 ], rdx
mov rdx, -0x2 
inc rdx
adox r10, r11
adox r14, rcx
adox r8, r15
adox rbx, r12
adox rdi, [ rsp + 0x128 ]
mov r10, 0x0 
adcx r9, r10
mov rdx, [ rax + 0x10 ]
mulx rcx, r11, [ rsi + 0x28 ]
mov rdx, [ rsp + 0x20 ]
clc
adcx rdx, [ rsp + 0x138 ]
adcx r11, [ rsp + 0x130 ]
adox rbp, [ rsp + 0x120 ]
setc r15b
clc
adcx r14, [ rsp + 0x18 ]
adox r9, [ rsp + 0x140 ]
adcx r8, [ rsp + 0x8 ]
mov r12, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x148 ], rcx
mulx rcx, r10, [ rax + 0x28 ]
mov rdx, 0x100000001 
mov byte [ rsp + 0x150 ], r15b
mov [ rsp + 0x158 ], r11
mulx r11, r15, r14
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x160 ], r12
mulx r12, r11, [ rsi + 0x10 ]
adcx rbx, [ rsp + 0x78 ]
movzx rdx, r13b
mov [ rsp + 0x168 ], rbx
mov rbx, 0x0 
adox rdx, rbx
movzx r13, byte [ rsp + 0x70 ]
dec rbx
adox r13, rbx
adox r11, [ rsp - 0x40 ]
adcx rdi, [ rsp + 0x68 ]
adcx r11, rbp
adox r10, r12
adcx r10, r9
mov r13, 0xffffffffffffffff 
xchg rdx, r13
mulx r9, rbp, r15
mov r12, 0x0 
adox rcx, r12
adcx rcx, r13
mov r13, 0xffffffff 
mov rdx, r15
mulx r12, r15, r13
inc rbx
adox r15, r14
mov r15, 0xffffffff00000000 
mulx rbx, r14, r15
mov r15, 0xfffffffffffffffe 
mov [ rsp + 0x170 ], rcx
mulx rcx, r13, r15
setc dl
clc
adcx r14, r12
adox r14, r8
adcx r13, rbx
adox r13, [ rsp + 0x168 ]
mov r8, rbp
adcx r8, rcx
mov r12, rbp
adcx r12, r9
adox r8, rdi
adcx rbp, r9
adox r12, r11
adox rbp, r10
mov rdi, 0x0 
adcx r9, rdi
adox r9, [ rsp + 0x170 ]
clc
adcx r14, [ rsp - 0x38 ]
adcx r13, [ rsp + 0xc0 ]
movzx r11, dl
adox r11, rdi
mov r10, 0x100000001 
mov rdx, r10
mulx rbx, r10, r14
mov rdx, r10
mulx rbx, r10, r15
mov rcx, 0xffffffff 
mulx r15, rdi, rcx
adcx r8, [ rsp + 0xb8 ]
adcx r12, [ rsp + 0x118 ]
adcx rbp, [ rsp + 0x110 ]
adcx r9, [ rsp + 0x108 ]
mov rcx, -0x2 
inc rcx
adox rdi, r14
mov rdi, 0xffffffff00000000 
mulx rcx, r14, rdi
adcx r11, [ rsp + 0x100 ]
setc dil
clc
adcx r14, r15
adox r14, r13
adcx r10, rcx
adox r10, r8
mov r13, 0xffffffffffffffff 
mulx r8, r15, r13
mov rdx, r15
adcx rdx, rbx
mov rbx, r15
adcx rbx, r8
adox rdx, r12
adox rbx, rbp
adcx r15, r8
adox r15, r9
mov r12, 0x0 
adcx r8, r12
adox r8, r11
clc
adcx r14, [ rsp - 0x48 ]
mov rbp, 0x100000001 
xchg rdx, rbp
mulx rcx, r9, r14
mov rcx, 0xffffffff 
mov rdx, r9
mulx r11, r9, rcx
mulx rcx, r12, r13
adcx r10, [ rsp + 0x40 ]
adcx rbp, [ rsp + 0x60 ]
adcx rbx, [ rsp + 0x58 ]
adcx r15, [ rsp + 0x50 ]
adcx r8, [ rsp + 0x48 ]
movzx r13, dil
mov [ rsp + 0x178 ], r8
mov r8, 0x0 
adox r13, r8
adcx r13, [ rsp + 0xf8 ]
mov rdi, -0x3 
inc rdi
adox r9, r14
mov r9, rdx
mov rdx, [ rax + 0x28 ]
mulx r8, r14, [ rsi + 0x28 ]
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x180 ], r8
mulx r8, rdi, r9
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x188 ], r14
mov [ rsp + 0x190 ], r13
mulx r13, r14, r9
setc r9b
clc
adcx r14, r11
adcx rdi, r13
mov r11, r12
adcx r11, r8
mov r8, r12
adcx r8, rcx
adox r14, r10
adox rdi, rbp
adox r11, rbx
adox r8, r15
adcx r12, rcx
adox r12, [ rsp + 0x178 ]
mov r10, 0x0 
adcx rcx, r10
mov rdx, [ rsi + 0x28 ]
mulx rbx, rbp, [ rax + 0x18 ]
adox rcx, [ rsp + 0x190 ]
clc
adcx r14, [ rsp + 0x10 ]
adcx rdi, [ rsp + 0x160 ]
adcx r11, [ rsp + 0x158 ]
mov rdx, 0x100000001 
mulx r13, r15, r14
mov r13, 0xffffffff00000000 
mov rdx, r13
mulx r10, r13, r15
movzx rdx, r9b
mov [ rsp + 0x198 ], r11
mov r11, 0x0 
adox rdx, r11
mov r9, 0xfffffffffffffffe 
xchg rdx, r15
mov [ rsp + 0x1a0 ], r10
mulx r10, r11, r9
movzx r9, byte [ rsp + 0x150 ]
mov [ rsp + 0x1a8 ], r10
mov r10, 0x0 
dec r10
adox r9, r10
adox rbp, [ rsp + 0x148 ]
mov r9, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x1b0 ], r11
mulx r11, r10, [ rsi + 0x28 ]
adox r10, rbx
adcx rbp, r8
adox r11, [ rsp + 0x188 ]
adcx r10, r12
mov rdx, 0xffffffff 
mulx r12, r8, r9
adcx r11, rcx
mov rbx, [ rsp + 0x180 ]
mov rcx, 0x0 
adox rbx, rcx
mov rdx, -0x3 
inc rdx
adox r13, r12
adcx rbx, r15
setc r15b
clc
adcx r8, r14
mov r8, 0xffffffffffffffff 
mov rdx, r8
mulx r14, r8, r9
adcx r13, rdi
mov rdi, [ rsp + 0x1a0 ]
adox rdi, [ rsp + 0x1b0 ]
mov r9, r8
adox r9, [ rsp + 0x1a8 ]
mov r12, r8
adox r12, r14
adcx rdi, [ rsp + 0x198 ]
adcx r9, rbp
adox r8, r14
adcx r12, r10
adcx r8, r11
adox r14, rcx
adcx r14, rbx
setc bpl
mov r10, r13
mov r11, 0xffffffff 
sub r10, r11
movzx rbx, bpl
movzx r15, r15b
lea rbx, [ rbx + r15 ]
mov r15, rdi
mov rbp, 0xffffffff00000000 
sbb r15, rbp
mov rcx, r9
mov rbp, 0xfffffffffffffffe 
sbb rcx, rbp
mov rbp, r12
sbb rbp, rdx
mov r11, r8
sbb r11, rdx
mov [ rsp + 0x1b8 ], r15
mov r15, r14
sbb r15, rdx
sbb rbx, 0x00000000
cmovc rbp, r12
cmovc r11, r8
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x18 ], rbp
cmovc r15, r14
cmovc r10, r13
cmovc rcx, r9
mov [ rbx + 0x10 ], rcx
mov [ rbx + 0x20 ], r11
mov r13, [ rsp + 0x1b8 ]
cmovc r13, rdi
mov [ rbx + 0x8 ], r13
mov [ rbx + 0x28 ], r15
mov [ rbx + 0x0 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 576
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.5918
; seed 1837262882038504 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4338452 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=55, initial num_batches=31): 115946 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.026725200601504868
; number reverted permutation / tried permutation: 67031 / 89993 =74.485%
; number reverted decision / tried decision: 62649 / 90006 =69.605%
; validated in 39.641s
