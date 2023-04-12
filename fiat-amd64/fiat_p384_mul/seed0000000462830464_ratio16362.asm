SECTION .text
	GLOBAL fiat_p384_mul
fiat_p384_mul:
sub rsp, 552
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mulx r8, rcx, [ rax + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], r8
mov [ rsp - 0x40 ], r9
mulx r9, r8, [ rax + 0x10 ]
xor rdx, rdx
adox r13, rbx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], r13
mulx r13, rbx, [ rax + 0x0 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x30 ], rbx
mov [ rsp - 0x28 ], r11
mulx r11, rbx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x20 ], r10
mov [ rsp - 0x18 ], r12
mulx r12, r10, [ rax + 0x0 ]
mov rdx, 0x100000001 
mov [ rsp - 0x10 ], rbp
mov [ rsp - 0x8 ], r12
mulx r12, rbp, r10
mov r12, 0xffffffff 
mov rdx, r12
mov [ rsp + 0x0 ], r11
mulx r11, r12, rbp
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x8 ], r12
mov [ rsp + 0x10 ], rbx
mulx rbx, r12, rbp
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x18 ], r9
mov [ rsp + 0x20 ], r8
mulx r8, r9, rbp
adcx r12, r11
mov r11, 0xffffffffffffffff 
mov rdx, r11
mov [ rsp + 0x28 ], r12
mulx r12, r11, rbp
adcx r9, rbx
mov rbp, r11
adcx rbp, r8
mov rbx, r11
adcx rbx, r12
adcx r11, r12
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x30 ], r11
mulx r11, r8, [ rsi + 0x20 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x38 ], r11
mov [ rsp + 0x40 ], r8
mulx r8, r11, [ rsi + 0x10 ]
mov rdx, 0x0 
adcx r12, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x48 ], r12
mov [ rsp + 0x50 ], rbx
mulx rbx, r12, [ rax + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x58 ], rbp
mov [ rsp + 0x60 ], r9
mulx r9, rbp, [ rax + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x68 ], r9
mov [ rsp + 0x70 ], r13
mulx r13, r9, [ rax + 0x0 ]
adox r12, r14
adox r11, rbx
clc
adcx r15, r13
adcx rcx, rdi
mov rdx, [ rsi + 0x8 ]
mulx rdi, r14, [ rax + 0x8 ]
adox rbp, r8
mov rdx, [ rax + 0x20 ]
mulx rbx, r8, [ rsi + 0x8 ]
seto dl
mov r13, -0x2 
inc r13
adox r14, [ rsp + 0x70 ]
adox rdi, [ rsp + 0x20 ]
mov r13b, dl
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x78 ], rcx
mov [ rsp + 0x80 ], r15
mulx r15, rcx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x88 ], r9
mov [ rsp + 0x90 ], rbp
mulx rbp, r9, [ rax + 0x18 ]
adox r9, [ rsp + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x98 ], r11
mov [ rsp + 0xa0 ], r12
mulx r12, r11, [ rsi + 0x28 ]
setc dl
clc
adcx rcx, r12
mov r12b, dl
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xa8 ], rcx
mov [ rsp + 0xb0 ], r11
mulx r11, rcx, [ rax + 0x28 ]
adox r8, rbp
adox rcx, rbx
mov rdx, [ rax + 0x10 ]
mulx rbp, rbx, [ rsi + 0x28 ]
mov rdx, 0x0 
adox r11, rdx
adcx rbx, r15
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0xb8 ], rbx
mulx rbx, r15, [ rsi + 0x28 ]
adcx r15, rbp
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xc0 ], r15
mulx r15, rbp, [ rax + 0x28 ]
adcx rbx, [ rsp + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0xc8 ], r15
mov [ rsp + 0xd0 ], rbx
mulx rbx, r15, [ rsi + 0x0 ]
mov rdx, -0x2 
inc rdx
adox r10, [ rsp + 0x8 ]
adcx rbp, [ rsp + 0x0 ]
setc r10b
clc
adcx r15, [ rsp - 0x8 ]
adcx rbx, [ rsp - 0x10 ]
mov rdx, [ rax + 0x18 ]
mov byte [ rsp + 0xd8 ], r10b
mov [ rsp + 0xe0 ], rbp
mulx rbp, r10, [ rsi + 0x0 ]
adcx r10, [ rsp - 0x18 ]
adox r15, [ rsp + 0x28 ]
adox rbx, [ rsp + 0x60 ]
adox r10, [ rsp + 0x58 ]
adcx rbp, [ rsp - 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov byte [ rsp + 0xe8 ], r12b
mov [ rsp + 0xf0 ], r11
mulx r11, r12, [ rax + 0x28 ]
adcx r12, [ rsp - 0x28 ]
setc dl
clc
adcx r15, [ rsp - 0x30 ]
adcx r14, rbx
adcx rdi, r10
adox rbp, [ rsp + 0x50 ]
adcx r9, rbp
movzx rbx, dl
lea rbx, [ rbx + r11 ]
mov rdx, [ rsi + 0x10 ]
mulx r11, r10, [ rax + 0x28 ]
adox r12, [ rsp + 0x30 ]
adcx r8, r12
mov rdx, [ rax + 0x0 ]
mulx r12, rbp, [ rsi + 0x18 ]
adox rbx, [ rsp + 0x48 ]
mov rdx, 0x100000001 
mov [ rsp + 0xf8 ], rbp
mov [ rsp + 0x100 ], r8
mulx r8, rbp, r15
adcx rcx, rbx
setc r8b
clc
mov rbx, -0x1 
movzx r13, r13b
adcx r13, rbx
adcx r10, [ rsp + 0x68 ]
mov r13, 0x0 
adcx r11, r13
movzx r8, r8b
movzx r13, r8b
adox r13, [ rsp + 0xf0 ]
mov rdx, [ rsi + 0x18 ]
mulx rbx, r8, [ rax + 0x20 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x108 ], r11
mov [ rsp + 0x110 ], r10
mulx r10, r11, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x118 ], r13
mov [ rsp + 0x120 ], rcx
mulx rcx, r13, [ rsi + 0x18 ]
clc
adcx r11, r12
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x128 ], r11
mulx r11, r12, [ rsi + 0x18 ]
adcx r13, r10
adcx r12, rcx
adcx r8, r11
mov rdx, [ rsi + 0x18 ]
mulx rcx, r10, [ rax + 0x28 ]
adcx r10, rbx
mov rdx, 0xffffffff 
mulx r11, rbx, rbp
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x130 ], r10
mov [ rsp + 0x138 ], r8
mulx r8, r10, rbp
mov rdx, 0x0 
adcx rcx, rdx
clc
adcx r10, r11
seto r11b
mov [ rsp + 0x140 ], rcx
mov rcx, -0x3 
inc rcx
adox rbx, r15
adox r10, r14
mov rbx, 0xfffffffffffffffe 
mov rdx, rbx
mulx r15, rbx, rbp
mov r14, 0xffffffffffffffff 
mov rdx, r14
mulx rcx, r14, rbp
adcx rbx, r8
adox rbx, rdi
mov rdi, r14
adcx rdi, r15
mov rbp, r14
adcx rbp, rcx
adcx r14, rcx
adox rdi, r9
adox rbp, [ rsp + 0x100 ]
mov r9, 0x0 
adcx rcx, r9
adox r14, [ rsp + 0x120 ]
adox rcx, [ rsp + 0x118 ]
movzx r8, r11b
adox r8, r9
add r10, [ rsp - 0x40 ]
adcx rbx, [ rsp - 0x38 ]
adcx rdi, [ rsp + 0xa0 ]
adcx rbp, [ rsp + 0x98 ]
adcx r14, [ rsp + 0x90 ]
mov r11, 0x100000001 
mov rdx, r11
mulx r15, r11, r10
mov r15, 0xffffffff 
mov rdx, r11
mulx r9, r11, r15
adcx rcx, [ rsp + 0x110 ]
mov r15, 0xffffffff00000000 
mov [ rsp + 0x148 ], rcx
mov [ rsp + 0x150 ], r12
mulx r12, rcx, r15
mov r15, -0x2 
inc r15
adox r11, r10
adcx r8, [ rsp + 0x108 ]
setc r11b
clc
adcx rcx, r9
mov r10, 0xfffffffffffffffe 
mulx r15, r9, r10
adcx r9, r12
adox rcx, rbx
adox r9, rdi
mov rbx, 0xffffffffffffffff 
mulx r12, rdi, rbx
mov rdx, rdi
adcx rdx, r15
mov r15, rdi
adcx r15, r12
adcx rdi, r12
adox rdx, rbp
mov rbp, 0x0 
adcx r12, rbp
clc
adcx rcx, [ rsp + 0xf8 ]
adcx r9, [ rsp + 0x128 ]
adcx r13, rdx
mov rdx, [ rax + 0x28 ]
mulx rbx, rbp, [ rsi + 0x20 ]
adox r15, r14
adcx r15, [ rsp + 0x150 ]
mov rdx, 0x100000001 
mulx r10, r14, rcx
mov r10, 0xffffffff 
mov rdx, r10
mov [ rsp + 0x158 ], rbx
mulx rbx, r10, r14
adox rdi, [ rsp + 0x148 ]
adox r12, r8
movzx r8, r11b
mov rdx, 0x0 
adox r8, rdx
adcx rdi, [ rsp + 0x138 ]
adcx r12, [ rsp + 0x130 ]
adcx r8, [ rsp + 0x140 ]
mov r11, 0xffffffff00000000 
mov rdx, r11
mov [ rsp + 0x160 ], rbp
mulx rbp, r11, r14
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x168 ], r8
mov [ rsp + 0x170 ], r12
mulx r12, r8, r14
mov rdx, -0x2 
inc rdx
adox r10, rcx
setc r10b
clc
adcx r11, rbx
adox r11, r9
mov rcx, 0xfffffffffffffffe 
mov rdx, r14
mulx r9, r14, rcx
adcx r14, rbp
adox r14, r13
mov r13, r8
adcx r13, r9
mov rdx, r8
adcx rdx, r12
adcx r8, r12
mov rbx, 0x0 
adcx r12, rbx
mov rbp, rdx
mov rdx, [ rax + 0x20 ]
mulx rbx, r9, [ rsi + 0x20 ]
adox r13, r15
adox rbp, rdi
mov rdx, [ rsp - 0x48 ]
movzx r15, byte [ rsp + 0xe8 ]
clc
mov rdi, -0x1 
adcx r15, rdi
adcx rdx, [ rsp + 0x40 ]
adox r8, [ rsp + 0x170 ]
adox r12, [ rsp + 0x168 ]
movzx r15, r10b
mov rdi, 0x0 
adox r15, rdi
mov r10, -0x3 
inc r10
adox r11, [ rsp + 0x88 ]
mov rdi, 0x100000001 
xchg rdx, rdi
mulx rcx, r10, r11
mov rcx, 0xfffffffffffffffe 
mov rdx, r10
mov [ rsp + 0x178 ], r15
mulx r15, r10, rcx
adox r14, [ rsp + 0x80 ]
mov rcx, 0xffffffff 
mov [ rsp + 0x180 ], r15
mov [ rsp + 0x188 ], r14
mulx r14, r15, rcx
adox r13, [ rsp + 0x78 ]
adcx r9, [ rsp + 0x38 ]
adcx rbx, [ rsp + 0x160 ]
adox rdi, rbp
adox r9, r8
adox rbx, r12
mov rbp, [ rsp + 0x158 ]
mov r8, 0x0 
adcx rbp, r8
adox rbp, [ rsp + 0x178 ]
mov r12, 0xffffffff00000000 
mulx rcx, r8, r12
clc
adcx r15, r11
setc r15b
clc
adcx r8, r14
adcx r10, rcx
mov r11, 0xffffffffffffffff 
mulx rcx, r14, r11
seto dl
mov r11, 0x0 
dec r11
movzx r15, r15b
adox r15, r11
adox r8, [ rsp + 0x188 ]
mov r15, r14
adcx r15, [ rsp + 0x180 ]
mov r11, r14
adcx r11, rcx
adcx r14, rcx
adox r10, r13
setc r13b
clc
adcx r8, [ rsp + 0xb0 ]
adox r15, rdi
adox r11, r9
adox r14, rbx
adcx r10, [ rsp + 0xa8 ]
adcx r15, [ rsp + 0xb8 ]
adcx r11, [ rsp + 0xc0 ]
movzx rdi, r13b
lea rdi, [ rdi + rcx ]
adox rdi, rbp
adcx r14, [ rsp + 0xd0 ]
movzx r9, dl
mov rbx, 0x0 
adox r9, rbx
mov rdx, 0x100000001 
mulx rcx, rbp, r8
adcx rdi, [ rsp + 0xe0 ]
movzx rcx, byte [ rsp + 0xd8 ]
mov r13, [ rsp + 0xc8 ]
lea rcx, [ rcx + r13 ]
mov r13, 0xffffffff 
mov rdx, rbp
mulx rbx, rbp, r13
mov r12, -0x2 
inc r12
adox rbp, r8
adcx rcx, r9
mov rbp, 0xfffffffffffffffe 
mulx r9, r8, rbp
mov r12, 0xffffffff00000000 
mulx r13, rbp, r12
setc r12b
clc
adcx rbp, rbx
mov rbx, 0xffffffffffffffff 
mov byte [ rsp + 0x190 ], r12b
mov [ rsp + 0x198 ], rcx
mulx rcx, r12, rbx
adox rbp, r10
adcx r8, r13
adox r8, r15
mov r10, r12
adcx r10, r9
mov r15, r12
adcx r15, rcx
adcx r12, rcx
adox r10, r11
adox r15, r14
mov r11, 0x0 
adcx rcx, r11
adox r12, rdi
adox rcx, [ rsp + 0x198 ]
movzx r14, byte [ rsp + 0x190 ]
adox r14, r11
mov rdx, rbp
mov rdi, 0xffffffff 
sub rdx, rdi
mov r9, r8
mov r13, 0xffffffff00000000 
sbb r9, r13
mov r11, r10
mov rbx, 0xfffffffffffffffe 
sbb r11, rbx
mov rbx, r15
mov r13, 0xffffffffffffffff 
sbb rbx, r13
mov rdi, r12
sbb rdi, r13
mov [ rsp + 0x1a0 ], r9
mov r9, rcx
sbb r9, r13
sbb r14, 0x00000000
cmovc r11, r10
cmovc rdx, rbp
cmovc rbx, r15
cmovc rdi, r12
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x20 ], rdi
mov [ r14 + 0x18 ], rbx
cmovc r9, rcx
mov [ r14 + 0x28 ], r9
mov rbp, [ rsp + 0x1a0 ]
cmovc rbp, r8
mov [ r14 + 0x8 ], rbp
mov [ r14 + 0x10 ], r11
mov [ r14 + 0x0 ], rdx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 552
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.6362
; seed 3840347187016167 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4320003 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=56, initial num_batches=31): 115548 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.026747203647775244
; number reverted permutation / tried permutation: 65351 / 89800 =72.774%
; number reverted decision / tried decision: 61873 / 90199 =68.596%
; validated in 38.451s
