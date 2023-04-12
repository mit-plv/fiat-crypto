SECTION .text
	GLOBAL fiat_p384_mul
fiat_p384_mul:
sub rsp, 424
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, 0x100000001 
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, r10
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x20 ]
xor rdx, rdx
adox rcx, rbp
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mulx r14, rbp, [ rax + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
adox rbp, r8
adox r15, r14
mov rdx, [ rax + 0x20 ]
mulx r14, r8, [ rsi + 0x18 ]
adox r8, rdi
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x48 ], r8
mulx r8, rdi, [ rsi + 0x18 ]
adox rdi, r14
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x40 ], rdi
mulx rdi, r14, [ rsi + 0x20 ]
mov rdx, 0x0 
adox r8, rdx
mov rdx, 0xfffffffffffffffe 
mov [ rsp - 0x38 ], r8
mov [ rsp - 0x30 ], r15
mulx r15, r8, r9
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x28 ], rbp
mov [ rsp - 0x20 ], rcx
mulx rcx, rbp, [ rax + 0x0 ]
adcx r14, rcx
adcx r12, rdi
mov rdx, 0xffffffff00000000 
mulx rcx, rdi, r9
mov rdx, 0xffffffff 
mov [ rsp - 0x18 ], r12
mov [ rsp - 0x10 ], r14
mulx r14, r12, r9
mov rdx, -0x2 
inc rdx
adox r12, r10
setc r12b
clc
adcx rdi, r14
adcx r8, rcx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r10, [ rax + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x8 ], rbp
mulx rbp, r14, [ rsi + 0x0 ]
setc dl
clc
adcx r14, r11
adcx r10, rbp
adox rdi, r14
adox r8, r10
mov r11b, dl
mov rdx, [ rax + 0x18 ]
mulx r14, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x0 ], rbx
mulx rbx, r10, [ rax + 0x8 ]
adcx rbp, rcx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x8 ], rbp
mulx rbp, rcx, [ rax + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x10 ], r8
mov [ rsp + 0x18 ], rcx
mulx rcx, r8, [ rsi + 0x8 ]
setc dl
clc
adcx r10, rbp
mov bpl, dl
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x20 ], r10
mov [ rsp + 0x28 ], rdi
mulx rdi, r10, [ rax + 0x10 ]
adcx r10, rbx
adcx r8, rdi
mov rdx, [ rax + 0x8 ]
mulx rdi, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x30 ], r8
mov [ rsp + 0x38 ], r10
mulx r10, r8, [ rax + 0x0 ]
seto dl
mov [ rsp + 0x40 ], r8
mov r8, -0x2 
inc r8
adox rbx, r10
mov r10b, dl
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x48 ], rbx
mulx rbx, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov byte [ rsp + 0x50 ], r10b
mov [ rsp + 0x58 ], r14
mulx r14, r10, [ rax + 0x20 ]
adox r8, rdi
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x60 ], r8
mulx r8, rdi, [ rax + 0x28 ]
adcx r10, rcx
adcx rdi, r14
mov rdx, [ rsi + 0x20 ]
mulx r14, rcx, [ rax + 0x18 ]
setc dl
clc
mov [ rsp + 0x68 ], rdi
mov rdi, -0x1 
movzx r12, r12b
adcx r12, rdi
adcx r13, rcx
movzx r12, dl
lea r12, [ r12 + r8 ]
mov rdx, [ rax + 0x28 ]
mulx rcx, r8, [ rsi + 0x20 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x70 ], r13
mulx r13, rdi, [ rsi + 0x20 ]
adcx rdi, r14
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x78 ], rdi
mulx rdi, r14, [ rax + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x80 ], r12
mov [ rsp + 0x88 ], r10
mulx r10, r12, [ rsi + 0x10 ]
adcx r8, r13
adox r14, rbx
adox r12, rdi
mov rdx, [ rsi + 0x10 ]
mulx r13, rbx, [ rax + 0x28 ]
adox rbx, r10
mov rdx, [ rax + 0x0 ]
mulx r10, rdi, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x90 ], rdi
mov [ rsp + 0x98 ], r8
mulx r8, rdi, [ rax + 0x20 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0xa0 ], rbx
mov [ rsp + 0xa8 ], r12
mulx r12, rbx, r9
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0xb0 ], r14
mulx r14, r9, [ rsi + 0x28 ]
mov rdx, 0x0 
adox r13, rdx
adc rcx, 0x0
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xb8 ], rcx
mov [ rsp + 0xc0 ], r13
mulx r13, rcx, [ rax + 0x10 ]
add r11b, 0x7F
adox r15, rbx
adcx r9, r10
mov rdx, [ rax + 0x18 ]
mulx r10, r11, [ rsi + 0x28 ]
adcx rcx, r14
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xc8 ], rcx
mulx rcx, r14, [ rsi + 0x0 ]
setc dl
clc
mov [ rsp + 0xd0 ], r9
mov r9, -0x1 
movzx rbp, bpl
adcx rbp, r9
adcx rdi, [ rsp + 0x58 ]
adcx r14, r8
mov rbp, 0x0 
adcx rcx, rbp
mov r8, rbx
adox r8, r12
adox rbx, r12
adox r12, rbp
add dl, 0xFF
adcx r13, r11
mov r11, [ rsp + 0x28 ]
adox r11, [ rsp + 0x18 ]
mov rdx, 0x100000001 
mulx r9, rbp, r11
mov r9, [ rsp + 0x10 ]
adox r9, [ rsp + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xd8 ], r13
mov [ rsp + 0xe0 ], r9
mulx r9, r13, [ rax + 0x20 ]
adcx r13, r10
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xe8 ], r13
mulx r13, r10, [ rsi + 0x28 ]
adcx r10, r9
mov rdx, 0xffffffff00000000 
mov [ rsp + 0xf0 ], r10
mulx r10, r9, rbp
mov rdx, 0x0 
adcx r13, rdx
movzx rdx, byte [ rsp + 0x50 ]
clc
mov [ rsp + 0xf8 ], r13
mov r13, -0x1 
adcx rdx, r13
adcx r15, [ rsp + 0x8 ]
adox r15, [ rsp + 0x38 ]
adcx r8, rdi
adcx rbx, r14
adox r8, [ rsp + 0x30 ]
adox rbx, [ rsp + 0x88 ]
adcx r12, rcx
adox r12, [ rsp + 0x68 ]
mov rdx, 0xffffffff 
mulx r14, rdi, rbp
seto cl
inc r13
adox rdi, r11
movzx rcx, cl
movzx rdi, cl
adcx rdi, [ rsp + 0x80 ]
setc r11b
clc
adcx r9, r14
adox r9, [ rsp + 0xe0 ]
mov rcx, 0xfffffffffffffffe 
mov rdx, rcx
mulx r14, rcx, rbp
adcx rcx, r10
adox rcx, r15
mov r10, 0xffffffffffffffff 
mov rdx, r10
mulx r15, r10, rbp
mov rbp, r10
adcx rbp, r14
adox rbp, r8
mov r8, r10
adcx r8, r15
adcx r10, r15
adcx r15, r13
adox r8, rbx
clc
adcx r9, [ rsp + 0x40 ]
adcx rcx, [ rsp + 0x48 ]
adcx rbp, [ rsp + 0x60 ]
adox r10, r12
adox r15, rdi
adcx r8, [ rsp + 0xb0 ]
movzx rbx, r11b
adox rbx, r13
mov r12, 0x100000001 
mov rdx, r12
mulx r11, r12, r9
mov r11, 0xffffffff 
mov rdx, r12
mulx rdi, r12, r11
adcx r10, [ rsp + 0xa8 ]
adcx r15, [ rsp + 0xa0 ]
adcx rbx, [ rsp + 0xc0 ]
mov r14, 0xffffffff00000000 
mulx r11, r13, r14
mov r14, -0x2 
inc r14
adox r12, r9
setc r12b
clc
adcx r13, rdi
adox r13, rcx
mov r9, 0xfffffffffffffffe 
mulx rdi, rcx, r9
adcx rcx, r11
mov r11, 0xffffffffffffffff 
mulx r9, r14, r11
adox rcx, rbp
mov rbp, r14
adcx rbp, rdi
adox rbp, r8
mov r8, r14
adcx r8, r9
adcx r14, r9
adox r8, r10
adox r14, r15
mov rdx, 0x0 
adcx r9, rdx
clc
adcx r13, [ rsp + 0x0 ]
adox r9, rbx
mov r10, 0x100000001 
mov rdx, r10
mulx r15, r10, r13
mov r15, 0xffffffff 
mov rdx, r10
mulx rbx, r10, r15
adcx rcx, [ rsp - 0x20 ]
adcx rbp, [ rsp - 0x28 ]
mulx r15, rdi, r11
adcx r8, [ rsp - 0x30 ]
adcx r14, [ rsp - 0x48 ]
mov r11, 0xfffffffffffffffe 
mov [ rsp + 0x100 ], r14
mov [ rsp + 0x108 ], r8
mulx r8, r14, r11
mov r11, 0xffffffff00000000 
mov [ rsp + 0x110 ], rbp
mov [ rsp + 0x118 ], rcx
mulx rcx, rbp, r11
adcx r9, [ rsp - 0x40 ]
setc dl
clc
adcx rbp, rbx
adcx r14, rcx
mov rbx, rdi
adcx rbx, r8
mov r8, rdi
adcx r8, r15
adcx rdi, r15
movzx rcx, r12b
mov r11, 0x0 
adox rcx, r11
adc r15, 0x0
add dl, 0xFF
adcx rcx, [ rsp - 0x38 ]
adox r10, r13
adox rbp, [ rsp + 0x118 ]
adox r14, [ rsp + 0x110 ]
adox rbx, [ rsp + 0x108 ]
setc r10b
clc
adcx rbp, [ rsp - 0x8 ]
adox r8, [ rsp + 0x100 ]
adcx r14, [ rsp - 0x10 ]
adcx rbx, [ rsp - 0x18 ]
adox rdi, r9
adox r15, rcx
adcx r8, [ rsp + 0x70 ]
adcx rdi, [ rsp + 0x78 ]
movzx r12, r10b
adox r12, r11
mov r13, 0x100000001 
mov rdx, r13
mulx r9, r13, rbp
mov r9, 0xffffffff 
mov rdx, r13
mulx rcx, r13, r9
mov r10, 0xffffffff00000000 
mulx r9, r11, r10
mov r10, -0x2 
inc r10
adox r13, rbp
adcx r15, [ rsp + 0x98 ]
adcx r12, [ rsp + 0xb8 ]
mov r13, 0xfffffffffffffffe 
mulx r10, rbp, r13
setc r13b
clc
adcx r11, rcx
adcx rbp, r9
adox r11, r14
mov r14, 0xffffffffffffffff 
mulx r9, rcx, r14
adox rbp, rbx
mov rbx, rcx
adcx rbx, r10
adox rbx, r8
mov r8, rcx
adcx r8, r9
adox r8, rdi
adcx rcx, r9
adox rcx, r15
mov rdi, 0x0 
adcx r9, rdi
clc
adcx r11, [ rsp + 0x90 ]
adox r9, r12
mov rdx, 0x100000001 
mulx r12, r15, r11
movzx r12, r13b
adox r12, rdi
mov r13, 0xfffffffffffffffe 
mov rdx, r15
mulx r10, r15, r13
mov rdi, 0xffffffff 
mulx r14, r13, rdi
adcx rbp, [ rsp + 0xd0 ]
mov rdi, -0x2 
inc rdi
adox r13, r11
adcx rbx, [ rsp + 0xc8 ]
adcx r8, [ rsp + 0xd8 ]
adcx rcx, [ rsp + 0xe8 ]
adcx r9, [ rsp + 0xf0 ]
adcx r12, [ rsp + 0xf8 ]
mov r13, 0xffffffff00000000 
mulx rdi, r11, r13
setc r13b
clc
adcx r11, r14
adox r11, rbp
adcx r15, rdi
adox r15, rbx
mov r14, 0xffffffffffffffff 
mulx rbx, rbp, r14
mov rdx, rbp
adcx rdx, r10
adox rdx, r8
mov r10, rbp
adcx r10, rbx
adcx rbp, rbx
mov r8, 0x0 
adcx rbx, r8
adox r10, rcx
adox rbp, r9
adox rbx, r12
movzx rcx, r13b
adox rcx, r8
mov r9, r11
mov r13, 0xffffffff 
sub r9, r13
mov r12, r15
mov rdi, 0xffffffff00000000 
sbb r12, rdi
mov r8, rdx
mov r13, 0xfffffffffffffffe 
sbb r8, r13
mov r13, r10
sbb r13, r14
mov rdi, rbp
sbb rdi, r14
mov [ rsp + 0x120 ], r8
mov r8, rbx
sbb r8, r14
sbb rcx, 0x00000000
cmovc r12, r15
cmovc r9, r11
cmovc rdi, rbp
cmovc r13, r10
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x0 ], r9
mov r11, [ rsp + 0x120 ]
cmovc r11, rdx
mov [ rcx + 0x10 ], r11
mov [ rcx + 0x18 ], r13
cmovc r8, rbx
mov [ rcx + 0x20 ], rdi
mov [ rcx + 0x8 ], r12
mov [ rcx + 0x28 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 424
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.6440
; seed 1521459709928102 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 6240848 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=88, initial num_batches=31): 194962 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.031239664866056664
; number reverted permutation / tried permutation: 74796 / 89593 =83.484%
; number reverted decision / tried decision: 65183 / 90406 =72.100%
; validated in 58.544s
