SECTION .text
	GLOBAL fiat_p384_square
fiat_p384_square:
sub rsp, 424
mov rdx, [ rsi + 0x18 ]
mulx r10, rax, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x20 ]
xor rdx, rdx
adox r11, rbp
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], r11
mov [ rsp - 0x40 ], rbx
mulx rbx, r11, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], r8
mov [ rsp - 0x30 ], rbx
mulx rbx, r8, [ rsi + 0x18 ]
adcx r8, r9
adcx rax, rbx
mov rdx, [ rsi + 0x20 ]
mulx rbx, r9, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], rax
mov [ rsp - 0x20 ], r8
mulx r8, rax, rdx
adcx rax, r10
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], rax
mulx rax, r10, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], r11
mov [ rsp - 0x8 ], rbx
mulx rbx, r11, [ rsi + 0x20 ]
adcx r11, r8
adox r10, rcx
adox r13, rax
mov rdx, 0x100000001 
mulx r8, rcx, r15
adcx rbp, rbx
mov rdx, [ rsi + 0x8 ]
mulx rax, r8, [ rsi + 0x0 ]
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x0 ], r13
mulx r13, rbx, rcx
mov rdx, 0xffffffff 
mov [ rsp + 0x8 ], r10
mov [ rsp + 0x10 ], rbp
mulx rbp, r10, rcx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x18 ], r11
mov [ rsp + 0x20 ], r9
mulx r9, r11, [ rsi + 0x0 ]
setc dl
clc
adcx r8, rdi
adcx r11, rax
movzx rdi, dl
lea rdi, [ rdi + r12 ]
setc r12b
clc
adcx rbx, rbp
mov rdx, 0xfffffffffffffffe 
mulx rbp, rax, rcx
adcx rax, r13
setc r13b
clc
adcx r10, r15
adcx rbx, r8
mov rdx, [ rsi + 0x8 ]
mulx r15, r10, [ rsi + 0x28 ]
adcx rax, r11
mov rdx, [ rsi + 0x20 ]
mulx r11, r8, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x28 ], rdi
mov [ rsp + 0x30 ], r11
mulx r11, rdi, [ rsi + 0x18 ]
adox r8, r14
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x38 ], r8
mulx r8, r14, [ rsi + 0x28 ]
setc dl
clc
adcx r10, r8
mov r8b, dl
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x40 ], r10
mov [ rsp + 0x48 ], r14
mulx r14, r10, [ rsi + 0x10 ]
adcx r10, r15
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x50 ], r10
mulx r10, r15, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x58 ], r11
mov byte [ rsp + 0x60 ], r8b
mulx r8, r11, rdx
adcx rdi, r14
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x68 ], rdi
mulx rdi, r14, [ rsi + 0x18 ]
setc dl
clc
adcx r11, r10
seto r10b
mov byte [ rsp + 0x70 ], dl
mov rdx, -0x2 
inc rdx
adox r15, rbx
adox r11, rax
seto bl
inc rdx
mov rax, -0x1 
movzx r12, r12b
adox r12, rax
adox r9, r14
mov rdx, [ rsi + 0x20 ]
mulx r14, r12, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov byte [ rsp + 0x78 ], bl
mulx rbx, rax, [ rsi + 0x10 ]
adox r12, rdi
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x80 ], r11
mulx r11, rdi, [ rsi + 0x18 ]
adcx rax, r8
adcx rdi, rbx
adcx r11, [ rsp + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mulx rbx, r8, [ rsi + 0x28 ]
adox r8, r14
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x88 ], r11
mulx r11, r14, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x90 ], rdi
mov [ rsp + 0x98 ], rax
mulx rax, rdi, [ rsi + 0x10 ]
mov rdx, 0x0 
adox rbx, rdx
adcx r14, [ rsp - 0x8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0xa0 ], r14
mov [ rsp + 0xa8 ], r15
mulx r15, r14, rcx
adc r11, 0x0
add r13b, 0xFF
adcx rbp, r14
mov rdx, [ rsi + 0x0 ]
mulx r13, rcx, [ rsi + 0x10 ]
adox rdi, r13
adox rax, [ rsp - 0x10 ]
mov rdx, r14
adcx rdx, r15
adcx r14, r15
mov r13, 0x0 
adcx r15, r13
mov r13, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xb0 ], rax
mov [ rsp + 0xb8 ], rdi
mulx rdi, rax, [ rsi + 0x28 ]
clc
mov rdx, -0x1 
movzx r10, r10b
adcx r10, rdx
adcx rax, [ rsp + 0x30 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xc0 ], rax
mulx rax, r10, [ rsi + 0x18 ]
adox r10, [ rsp - 0x30 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xc8 ], r10
mov [ rsp + 0xd0 ], rcx
mulx rcx, r10, [ rsi + 0x20 ]
mov rdx, 0x0 
adcx rdi, rdx
movzx rdx, byte [ rsp + 0x60 ]
clc
mov [ rsp + 0xd8 ], rdi
mov rdi, -0x1 
adcx rdx, rdi
adcx r9, rbp
adcx r13, r12
mov rdx, [ rsi + 0x20 ]
mulx rbp, r12, [ rsi + 0x28 ]
adcx r14, r8
mov rdx, [ rsi + 0x28 ]
mulx rdi, r8, [ rsi + 0x10 ]
adox r10, rax
adcx r15, rbx
adox r8, rcx
mov rdx, 0x100000001 
mulx rax, rbx, [ rsp + 0xa8 ]
setc al
movzx rcx, byte [ rsp + 0x70 ]
clc
mov rdx, -0x1 
adcx rcx, rdx
adcx r12, [ rsp + 0x58 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xe0 ], r12
mulx r12, rcx, rdx
adcx rcx, rbp
mov rdx, 0x0 
adox rdi, rdx
adc r12, 0x0
mov rbp, 0xffffffff00000000 
mov rdx, rbx
mov [ rsp + 0xe8 ], r12
mulx r12, rbx, rbp
mov rbp, 0xffffffff 
mov [ rsp + 0xf0 ], rcx
mov [ rsp + 0xf8 ], rdi
mulx rdi, rcx, rbp
test al, al
adox rbx, rdi
mov rdi, 0xfffffffffffffffe 
mov [ rsp + 0x100 ], r8
mulx r8, rbp, rdi
adox rbp, r12
mov r12, 0xffffffffffffffff 
mov [ rsp + 0x108 ], r10
mulx r10, rdi, r12
mov rdx, rdi
adox rdx, r8
mov r8, rdi
adox r8, r10
adox rdi, r10
adcx rcx, [ rsp + 0xa8 ]
mov rcx, 0x0 
adox r10, rcx
adcx rbx, [ rsp + 0x80 ]
movzx rcx, byte [ rsp + 0x78 ]
mov r12, 0x0 
dec r12
adox rcx, r12
adox r9, [ rsp + 0x98 ]
adox r13, [ rsp + 0x90 ]
adox r14, [ rsp + 0x88 ]
adox r15, [ rsp + 0xa0 ]
movzx rcx, al
adox rcx, r11
seto r11b
inc r12
adox rbx, [ rsp + 0xd0 ]
mov rax, 0x100000001 
xchg rdx, rbx
mov byte [ rsp + 0x110 ], r11b
mulx r11, r12, rax
adcx rbp, r9
adcx rbx, r13
mov r11, 0xfffffffffffffffe 
xchg rdx, r12
mulx r13, r9, r11
adox rbp, [ rsp + 0xb8 ]
adcx r8, r14
adox rbx, [ rsp + 0xb0 ]
adox r8, [ rsp + 0xc8 ]
adcx rdi, r15
adcx r10, rcx
movzx r14, byte [ rsp + 0x110 ]
mov r15, 0x0 
adcx r14, r15
adox rdi, [ rsp + 0x108 ]
adox r10, [ rsp + 0x100 ]
mov rcx, 0xffffffff 
mulx r11, r15, rcx
mov rcx, 0xffffffff00000000 
mov [ rsp + 0x118 ], r10
mulx r10, rax, rcx
adox r14, [ rsp + 0xf8 ]
clc
adcx rax, r11
mov r11, 0xffffffffffffffff 
mov [ rsp + 0x120 ], r14
mulx r14, rcx, r11
adcx r9, r10
mov rdx, rcx
adcx rdx, r13
mov r13, rcx
adcx r13, r14
adcx rcx, r14
mov r10, 0x0 
adcx r14, r10
clc
adcx r15, r12
adcx rax, rbp
adcx r9, rbx
adcx rdx, r8
adcx r13, rdi
adcx rcx, [ rsp + 0x118 ]
adcx r14, [ rsp + 0x120 ]
seto r15b
mov r12, -0x3 
inc r12
adox rax, [ rsp - 0x38 ]
adox r9, [ rsp - 0x20 ]
movzx rbp, r15b
adcx rbp, r10
mov rbx, 0x100000001 
xchg rdx, rbx
mulx rdi, r8, rax
mov rdi, 0xffffffff 
mov rdx, r8
mulx r15, r8, rdi
adox rbx, [ rsp - 0x28 ]
adox r13, [ rsp - 0x18 ]
adox rcx, [ rsp + 0x18 ]
adox r14, [ rsp + 0x10 ]
adox rbp, [ rsp + 0x28 ]
mulx r12, r10, r11
clc
adcx r8, rax
mov r8, 0xffffffff00000000 
mulx r11, rax, r8
seto dil
mov r8, -0x2 
inc r8
adox rax, r15
adcx rax, r9
mov r9, 0xfffffffffffffffe 
mulx r8, r15, r9
adox r15, r11
adcx r15, rbx
mov rdx, r10
adox rdx, r8
mov rbx, r10
adox rbx, r12
adcx rdx, r13
adox r10, r12
adcx rbx, rcx
adcx r10, r14
mov r13, 0x0 
adox r12, r13
adcx r12, rbp
movzx rcx, dil
adc rcx, 0x0
add rax, [ rsp - 0x40 ]
adcx r15, [ rsp - 0x48 ]
mov r14, 0x100000001 
xchg rdx, r14
mulx rbp, rdi, rax
mov rbp, 0xffffffff 
mov rdx, rdi
mulx r11, rdi, rbp
adcx r14, [ rsp + 0x8 ]
adcx rbx, [ rsp + 0x0 ]
adcx r10, [ rsp + 0x38 ]
mov r8, -0x3 
inc r8
adox rdi, rax
adcx r12, [ rsp + 0xc0 ]
mov rdi, 0xffffffff00000000 
mulx r13, rax, rdi
adcx rcx, [ rsp + 0xd8 ]
setc r8b
clc
adcx rax, r11
adox rax, r15
mulx r11, r15, r9
adcx r15, r13
adox r15, r14
mov r14, 0xffffffffffffffff 
mulx rbp, r13, r14
mov rdx, r13
adcx rdx, r11
adox rdx, rbx
mov rbx, r13
adcx rbx, rbp
adcx r13, rbp
adox rbx, r10
adox r13, r12
mov r10, 0x0 
adcx rbp, r10
adox rbp, rcx
movzx r12, r8b
adox r12, r10
add rax, [ rsp + 0x48 ]
adcx r15, [ rsp + 0x40 ]
mov r8, 0x100000001 
xchg rdx, rax
mulx r11, rcx, r8
xchg rdx, rcx
mulx r10, r11, rdi
adcx rax, [ rsp + 0x50 ]
mov rdi, 0xffffffff 
mulx r14, r8, rdi
adcx rbx, [ rsp + 0x68 ]
adcx r13, [ rsp + 0xe0 ]
adcx rbp, [ rsp + 0xf0 ]
adcx r12, [ rsp + 0xe8 ]
mov rdi, -0x2 
inc rdi
adox r11, r14
mulx rdi, r14, r9
setc r9b
clc
adcx r8, rcx
adcx r11, r15
adox r14, r10
mov r8, 0xffffffffffffffff 
mulx r15, rcx, r8
mov rdx, rcx
adox rdx, rdi
mov r10, rcx
adox r10, r15
adox rcx, r15
mov rdi, 0x0 
adox r15, rdi
adcx r14, rax
adcx rdx, rbx
adcx r10, r13
adcx rcx, rbp
adcx r15, r12
movzx rax, r9b
adc rax, 0x0
mov rbx, r11
mov r13, 0xffffffff 
sub rbx, r13
mov rbp, r14
mov r9, 0xffffffff00000000 
sbb rbp, r9
mov r12, rdx
mov rdi, 0xfffffffffffffffe 
sbb r12, rdi
mov rdi, r10
sbb rdi, r8
mov r13, rcx
sbb r13, r8
mov r9, r15
sbb r9, r8
sbb rax, 0x00000000
cmovc r13, rcx
cmovc r12, rdx
cmovc rbp, r14
mov rax, [ rsp - 0x50 ]
mov [ rax + 0x20 ], r13
mov [ rax + 0x10 ], r12
cmovc r9, r15
cmovc rdi, r10
mov [ rax + 0x18 ], rdi
cmovc rbx, r11
mov [ rax + 0x8 ], rbp
mov [ rax + 0x28 ], r9
mov [ rax + 0x0 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 424
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.4930
; seed 3039498294152266 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 7035577 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=49, initial num_batches=31): 190281 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.02704554295973166
; number reverted permutation / tried permutation: 75566 / 89756 =84.190%
; number reverted decision / tried decision: 67049 / 90243 =74.298%
; validated in 39.744s
