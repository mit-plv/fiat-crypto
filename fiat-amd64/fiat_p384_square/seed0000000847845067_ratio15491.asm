SECTION .text
	GLOBAL fiat_p384_square
fiat_p384_square:
sub rsp, 432
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x0 ]
xor rdx, rdx
adox r12, r10
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mulx r14, r10, [ rsi + 0x8 ]
adcx rbx, r14
adox r11, r13
mov rdx, [ rsi + 0x8 ]
mulx r14, r13, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], rbx
mov [ rsp - 0x40 ], r10
mulx r10, rbx, [ rsi + 0x0 ]
adcx r13, rbp
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], rbx
mulx rbx, rbp, [ rsi + 0x18 ]
seto dl
mov [ rsp - 0x30 ], r13
mov r13, -0x2 
inc r13
adox rbp, r10
mov r10b, dl
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], rbp
mulx rbp, r13, [ rsi + 0x10 ]
adox r8, rbx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x20 ], r8
mulx r8, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], rbx
mov [ rsp - 0x10 ], r11
mulx r11, rbx, [ rsi + 0x10 ]
seto dl
mov [ rsp - 0x8 ], r12
mov r12, -0x2 
inc r12
adox r13, r8
adox r15, rbp
adox rbx, rdi
mov dil, dl
mov rdx, [ rsi + 0x18 ]
mulx r8, rbp, [ rsi + 0x8 ]
adcx rbp, r14
mov rdx, [ rsi + 0x10 ]
mulx r12, r14, [ rsi + 0x20 ]
adox r14, r11
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x0 ], r14
mulx r14, r11, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x8 ], rbx
mov [ rsp + 0x10 ], r15
mulx r15, rbx, [ rsi + 0x10 ]
adox rbx, r12
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x18 ], rbx
mulx rbx, r12, [ rsi + 0x8 ]
adcx r12, r8
adcx r11, rbx
mov rdx, 0x0 
adox r15, rdx
mov rdx, [ rsi + 0x18 ]
mulx rbx, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x20 ], r15
mov [ rsp + 0x28 ], r13
mulx r13, r15, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x30 ], r11
mov [ rsp + 0x38 ], r12
mulx r12, r11, [ rsi + 0x20 ]
adc r14, 0x0
add r10b, 0xFF
adcx rcx, r8
mov rdx, [ rsi + 0x28 ]
mulx r8, r10, [ rsi + 0x0 ]
mov rdx, 0x100000001 
mov [ rsp + 0x40 ], r14
mov [ rsp + 0x48 ], rbp
mulx rbp, r14, rax
adcx r15, rbx
adcx r10, r13
mov rdx, [ rsi + 0x18 ]
mulx rbx, rbp, rdx
adc r8, 0x0
add dil, 0xFF
adcx r9, rbp
mov rdx, [ rsi + 0x0 ]
mulx r13, rdi, [ rsi + 0x20 ]
adcx r11, rbx
mov rdx, [ rsi + 0x20 ]
mulx rbx, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x50 ], rdi
mov [ rsp + 0x58 ], r11
mulx r11, rdi, [ rsi + 0x8 ]
adox rdi, r13
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x60 ], rdi
mulx rdi, r13, [ rsi + 0x18 ]
adox rbp, r11
adcx r13, r12
mov rdx, 0x0 
adcx rdi, rdx
mov rdx, [ rsi + 0x18 ]
mulx r11, r12, [ rsi + 0x20 ]
adox r12, rbx
mov rdx, 0xffffffff 
mov [ rsp + 0x68 ], r12
mulx r12, rbx, r14
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x70 ], rbp
mov [ rsp + 0x78 ], rdi
mulx rdi, rbp, r14
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x80 ], r13
mov [ rsp + 0x88 ], r9
mulx r9, r13, r14
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x90 ], r8
mov [ rsp + 0x98 ], r10
mulx r10, r8, r14
clc
adcx rbx, rax
seto bl
mov rax, -0x2 
inc rax
adox rbp, r12
adox r8, rdi
mov rdx, [ rsi + 0x28 ]
mulx r12, r14, [ rsi + 0x10 ]
mov rdx, r13
adox rdx, r10
mov rdi, r13
adox rdi, r9
mov r10, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xa0 ], r12
mulx r12, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xa8 ], rax
mov [ rsp + 0xb0 ], r11
mulx r11, rax, [ rsi + 0x28 ]
adcx rbp, [ rsp - 0x8 ]
adcx r8, [ rsp - 0x10 ]
adcx r10, rcx
adcx rdi, r15
setc dl
clc
adcx rax, r12
mov cl, dl
mov rdx, [ rsi + 0x20 ]
mulx r12, r15, rdx
adcx r14, r11
setc dl
clc
adcx rbp, [ rsp - 0x40 ]
adcx r8, [ rsp - 0x48 ]
adcx r10, [ rsp - 0x30 ]
adcx rdi, [ rsp + 0x48 ]
setc r11b
clc
mov [ rsp + 0xb8 ], r14
mov r14, -0x1 
movzx rbx, bl
adcx rbx, r14
adcx r15, [ rsp + 0xb0 ]
mov bl, dl
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xc0 ], rax
mulx rax, r14, [ rsi + 0x20 ]
adcx r14, r12
mov rdx, 0x100000001 
mov [ rsp + 0xc8 ], r14
mulx r14, r12, rbp
mov r14, 0xffffffff00000000 
mov rdx, r14
mov [ rsp + 0xd0 ], r15
mulx r15, r14, r12
adox r13, r9
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0xd8 ], rdi
mov byte [ rsp + 0xe0 ], r11b
mulx r11, rdi, r12
mov rdx, 0x0 
adox r9, rdx
adc rax, 0x0
mov rdx, 0xffffffff 
mov [ rsp + 0xe8 ], rax
mov byte [ rsp + 0xf0 ], bl
mulx rbx, rax, r12
add cl, 0xFF
adcx r13, [ rsp + 0x98 ]
adcx r9, [ rsp + 0x90 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xf8 ], r9
mulx r9, rcx, rdx
adox r14, rbx
adox rdi, r15
mov rdx, 0xffffffffffffffff 
mulx rbx, r15, r12
mov r12, r15
adox r12, r11
mov r11, r15
adox r11, rbx
setc dl
clc
adcx rax, rbp
adcx r14, r8
adox r15, rbx
mov al, dl
mov rdx, [ rsi + 0x28 ]
mulx r8, rbp, [ rsi + 0x18 ]
mov rdx, 0x0 
adox rbx, rdx
adcx rdi, r10
movzx r10, byte [ rsp + 0xf0 ]
dec rdx
adox r10, rdx
adox rbp, [ rsp + 0xa0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x100 ], rbp
mulx rbp, r10, [ rsi + 0x28 ]
adox r10, r8
adox rcx, rbp
mov rdx, 0x0 
adox r9, rdx
movzx r8, byte [ rsp + 0xe0 ]
dec rdx
adox r8, rdx
adox r13, [ rsp + 0x38 ]
mov r8, [ rsp + 0xf8 ]
adox r8, [ rsp + 0x30 ]
movzx rax, al
movzx rbp, al
adox rbp, [ rsp + 0x40 ]
adcx r12, [ rsp + 0xd8 ]
seto al
inc rdx
adox r14, [ rsp - 0x18 ]
adcx r11, r13
adcx r15, r8
adcx rbx, rbp
movzx r13, al
adcx r13, rdx
adox rdi, [ rsp + 0x28 ]
adox r12, [ rsp + 0x10 ]
adox r11, [ rsp + 0x8 ]
adox r15, [ rsp + 0x0 ]
adox rbx, [ rsp + 0x18 ]
mov r8, 0x100000001 
mov rdx, r8
mulx rax, r8, r14
adox r13, [ rsp + 0x20 ]
mov rax, 0xffffffff00000000 
mov rdx, r8
mulx rbp, r8, rax
mov rax, 0xffffffff 
mov [ rsp + 0x108 ], r9
mov [ rsp + 0x110 ], rcx
mulx rcx, r9, rax
clc
adcx r8, rcx
mov rcx, 0xfffffffffffffffe 
mov [ rsp + 0x118 ], r10
mulx r10, rax, rcx
adcx rax, rbp
seto bpl
mov rcx, -0x2 
inc rcx
adox r9, r14
adox r8, rdi
adox rax, r12
mov r9, 0xffffffffffffffff 
mulx rdi, r14, r9
mov r12, r14
adcx r12, r10
adox r12, r11
mov r11, r14
adcx r11, rdi
adcx r14, rdi
mov rdx, 0x0 
adcx rdi, rdx
adox r11, r15
adox r14, rbx
adox rdi, r13
movzx r15, bpl
adox r15, rdx
add r8, [ rsp - 0x38 ]
adcx rax, [ rsp - 0x28 ]
adcx r12, [ rsp - 0x20 ]
mov rbx, 0x100000001 
mov rdx, rbx
mulx rbp, rbx, r8
mov rbp, 0xffffffff 
mov rdx, rbx
mulx r13, rbx, rbp
adcx r11, [ rsp + 0x88 ]
adcx r14, [ rsp + 0x58 ]
adcx rdi, [ rsp + 0x80 ]
mulx rcx, r10, r9
adcx r15, [ rsp + 0x78 ]
mov r9, 0xffffffff00000000 
mov [ rsp + 0x120 ], r15
mulx r15, rbp, r9
mov r9, -0x2 
inc r9
adox rbp, r13
mov r13, 0xfffffffffffffffe 
mov [ rsp + 0x128 ], rdi
mulx rdi, r9, r13
setc dl
clc
adcx rbx, r8
adox r9, r15
adcx rbp, rax
adcx r9, r12
mov rbx, r10
adox rbx, rdi
mov r8, r10
adox r8, rcx
adox r10, rcx
mov rax, 0x0 
adox rcx, rax
adcx rbx, r11
adcx r8, r14
adcx r10, [ rsp + 0x128 ]
adcx rcx, [ rsp + 0x120 ]
movzx r12, dl
adc r12, 0x0
add rbp, [ rsp + 0x50 ]
adcx r9, [ rsp + 0x60 ]
adcx rbx, [ rsp + 0x70 ]
adcx r8, [ rsp + 0x68 ]
mov r11, 0x100000001 
mov rdx, r11
mulx r14, r11, rbp
mov r14, 0xffffffff 
mov rdx, r14
mulx r15, r14, r11
mov rdx, r13
mulx rdi, r13, r11
adcx r10, [ rsp + 0xd0 ]
adcx rcx, [ rsp + 0xc8 ]
adcx r12, [ rsp + 0xe8 ]
mov rdx, -0x3 
inc rdx
adox r14, rbp
mov r14, 0xffffffff00000000 
mov rdx, r11
mulx rbp, r11, r14
setc r14b
clc
adcx r11, r15
adox r11, r9
adcx r13, rbp
mov r9, 0xffffffffffffffff 
mulx rbp, r15, r9
adox r13, rbx
mov rbx, r15
adcx rbx, rdi
adox rbx, r8
mov r8, r15
adcx r8, rbp
adcx r15, rbp
adox r8, r10
adox r15, rcx
adcx rbp, rax
clc
adcx r11, [ rsp + 0xa8 ]
adcx r13, [ rsp + 0xc0 ]
adox rbp, r12
adcx rbx, [ rsp + 0xb8 ]
adcx r8, [ rsp + 0x100 ]
adcx r15, [ rsp + 0x118 ]
mov rdx, 0x100000001 
mulx r10, rdi, r11
mov r10, 0xffffffff00000000 
mov rdx, r10
mulx rcx, r10, rdi
adcx rbp, [ rsp + 0x110 ]
movzx r12, r14b
adox r12, rax
mov r14, 0xffffffff 
mov rdx, rdi
mulx rax, rdi, r14
adcx r12, [ rsp + 0x108 ]
mov r9, -0x2 
inc r9
adox r10, rax
setc al
clc
adcx rdi, r11
adcx r10, r13
mov rdi, 0xfffffffffffffffe 
mulx r13, r11, rdi
adox r11, rcx
adcx r11, rbx
mov rbx, 0xffffffffffffffff 
mulx r9, rcx, rbx
mov rdx, rcx
adox rdx, r13
mov r13, rcx
adox r13, r9
adcx rdx, r8
adcx r13, r15
adox rcx, r9
adcx rcx, rbp
mov r8, 0x0 
adox r9, r8
adcx r9, r12
movzx r15, al
adc r15, 0x0
mov rbp, r10
sub rbp, r14
mov rax, r11
mov r12, 0xffffffff00000000 
sbb rax, r12
mov r8, rdx
sbb r8, rdi
mov rdi, r13
sbb rdi, rbx
mov r12, rcx
sbb r12, rbx
mov r14, r9
sbb r14, rbx
sbb r15, 0x00000000
cmovc rdi, r13
cmovc r14, r9
cmovc r12, rcx
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x18 ], rdi
cmovc r8, rdx
cmovc rbp, r10
mov [ r15 + 0x10 ], r8
mov [ r15 + 0x0 ], rbp
mov [ r15 + 0x28 ], r14
cmovc rax, r11
mov [ r15 + 0x8 ], rax
mov [ r15 + 0x20 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 432
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.5491
; seed 0012109612815705 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 6375636 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=95, initial num_batches=31): 193880 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.03040951522326557
; number reverted permutation / tried permutation: 76013 / 89974 =84.483%
; number reverted decision / tried decision: 66944 / 90025 =74.362%
; validated in 50.528s
