SECTION .text
	GLOBAL fiat_p384_square
fiat_p384_square:
sub rsp, 368
mov rdx, [ rsi + 0x20 ]
mulx r10, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x20 ]
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x10 ]
xor rdx, rdx
adox rax, r9
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mulx r14, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x8 ]
adcx r15, r14
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x48 ], rax
mulx rax, r14, [ rsi + 0x10 ]
adox r14, r10
adox rbx, rax
adcx r11, rdi
mov rdx, [ rsi + 0x18 ]
mulx rdi, r10, [ rsi + 0x10 ]
adcx r10, rcx
mov rdx, [ rsi + 0x10 ]
mulx rax, rcx, [ rsi + 0x20 ]
adcx rcx, rdi
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x40 ], rbx
mulx rbx, rdi, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x38 ], r14
mov [ rsp - 0x30 ], r8
mulx r8, r14, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], r14
mov [ rsp - 0x20 ], rcx
mulx rcx, r14, [ rsi + 0x28 ]
adcx r14, rax
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], r14
mulx r14, rax, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x10 ], r10
mov [ rsp - 0x8 ], r11
mulx r11, r10, [ rsi + 0x20 ]
mov rdx, 0x0 
adcx rcx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x0 ], rcx
mov [ rsp + 0x8 ], r15
mulx r15, rcx, rdx
adox rcx, rbp
adox r10, r15
mov rdx, 0x0 
adox r11, rdx
mov rdx, [ rsi + 0x20 ]
mulx r15, rbp, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x10 ], r11
mov [ rsp + 0x18 ], r10
mulx r10, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x20 ], rcx
mov [ rsp + 0x28 ], r9
mulx r9, rcx, rdx
add rcx, r10
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x30 ], rcx
mulx rcx, r10, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x38 ], r11
mov [ rsp + 0x40 ], rcx
mulx rcx, r11, rdx
mov rdx, -0x2 
inc rdx
adox rdi, r8
mov r8, 0x100000001 
mov rdx, r8
mov [ rsp + 0x48 ], rdi
mulx rdi, r8, r11
adcx r10, r9
mov rdx, [ rsi + 0x18 ]
mulx r9, rdi, [ rsi + 0x28 ]
adox rax, rbx
adox rdi, r14
adox rbp, r9
mov rdx, [ rsi + 0x28 ]
mulx r14, rbx, rdx
adox rbx, r15
mov rdx, [ rsi + 0x0 ]
mulx r9, r15, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x50 ], rbx
mov [ rsp + 0x58 ], rbp
mulx rbp, rbx, [ rsi + 0x8 ]
mov rdx, 0x0 
adox r14, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x60 ], r14
mov [ rsp + 0x68 ], rdi
mulx rdi, r14, [ rsi + 0x18 ]
mov rdx, -0x2 
inc rdx
adox rbx, rcx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x70 ], rax
mulx rax, rcx, [ rsi + 0x18 ]
adox r12, rbp
setc dl
clc
adcx r14, r9
adcx rcx, rdi
mov r9b, dl
mov rdx, [ rsi + 0x18 ]
mulx rdi, rbp, rdx
mov rdx, 0xffffffff 
mov [ rsp + 0x78 ], rcx
mov [ rsp + 0x80 ], r14
mulx r14, rcx, r8
adcx rbp, rax
setc al
clc
adcx rcx, r11
mov rdx, [ rsi + 0x0 ]
mulx r11, rcx, [ rsi + 0x18 ]
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x88 ], rbp
mov [ rsp + 0x90 ], r15
mulx r15, rbp, r8
setc dl
clc
adcx rbp, r14
mov r14, 0xfffffffffffffffe 
xchg rdx, r14
mov [ rsp + 0x98 ], rdi
mov byte [ rsp + 0xa0 ], al
mulx rax, rdi, r8
adcx rdi, r15
adox rcx, r13
mov rdx, [ rsi + 0x0 ]
mulx r15, r13, [ rsi + 0x20 ]
adox r13, r11
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0xa8 ], r10
mulx r10, r11, r8
mov rdx, [ rsi + 0x0 ]
mov byte [ rsp + 0xb0 ], r9b
mulx r9, r8, [ rsi + 0x28 ]
adox r8, r15
mov rdx, 0x0 
adox r9, rdx
mov r15, r11
adcx r15, rax
mov rax, r11
adcx rax, r10
adcx r11, r10
adc r10, 0x0
add r14b, 0x7F
adox rbx, rbp
adox rdi, r12
adox r15, rcx
adox rax, r13
mov rdx, [ rsi + 0x8 ]
mulx r14, r12, [ rsi + 0x18 ]
movzx rdx, byte [ rsp + 0xb0 ]
mov rbp, -0x1 
adcx rdx, rbp
adcx r12, [ rsp + 0x40 ]
adox r11, r8
mov rdx, [ rsi + 0x20 ]
mulx r13, rcx, [ rsi + 0x8 ]
adox r10, r9
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, [ rsi + 0x20 ]
adcx rcx, r14
mov rdx, [ rsi + 0x28 ]
mulx rbp, r14, [ rsi + 0x8 ]
adcx r14, r13
mov rdx, 0x0 
adcx rbp, rdx
clc
adcx rbx, [ rsp + 0x38 ]
adcx rdi, [ rsp + 0x30 ]
adcx r15, [ rsp + 0xa8 ]
adcx r12, rax
adcx rcx, r11
adcx r14, r10
seto al
movzx r11, byte [ rsp + 0xa0 ]
dec rdx
adox r11, rdx
adox r8, [ rsp + 0x98 ]
movzx r11, al
adcx r11, rbp
mov rdx, [ rsi + 0x18 ]
mulx rax, r13, [ rsi + 0x28 ]
mov rdx, 0x100000001 
mulx rbp, r10, rbx
mov rbp, 0xffffffff 
mov rdx, r10
mov [ rsp + 0xb8 ], r8
mulx r8, r10, rbp
adox r13, r9
mov r9, 0x0 
adox rax, r9
mov r9, 0xffffffff00000000 
mov [ rsp + 0xc0 ], rax
mulx rax, rbp, r9
mov r9, -0x2 
inc r9
adox rbp, r8
seto r8b
inc r9
adox r10, rbx
mov r10, 0xfffffffffffffffe 
mulx r9, rbx, r10
setc r10b
clc
mov [ rsp + 0xc8 ], r13
mov r13, -0x1 
movzx r8, r8b
adcx r8, r13
adcx rax, rbx
adox rbp, rdi
mov rdi, 0xffffffffffffffff 
mulx rbx, r8, rdi
adox rax, r15
mov r15, r8
adcx r15, r9
adox r15, r12
mov r12, r8
adcx r12, rbx
adcx r8, rbx
adox r12, rcx
adox r8, r14
setc cl
clc
adcx rbp, [ rsp + 0x28 ]
adcx rax, [ rsp + 0x8 ]
adcx r15, [ rsp - 0x8 ]
mov r14, 0x100000001 
mov rdx, r14
mulx r9, r14, rbp
mov rdx, r14
mulx r14, r9, rdi
adcx r12, [ rsp - 0x10 ]
adcx r8, [ rsp - 0x20 ]
movzx r13, cl
lea r13, [ r13 + rbx ]
mov rbx, 0xffffffff 
mulx rdi, rcx, rbx
mov rbx, 0xffffffff00000000 
mov [ rsp + 0xd0 ], r8
mov [ rsp + 0xd8 ], r12
mulx r12, r8, rbx
seto bl
mov [ rsp + 0xe0 ], r15
mov r15, -0x2 
inc r15
adox rcx, rbp
setc cl
clc
adcx r8, rdi
adox r8, rax
mov rbp, 0xfffffffffffffffe 
mulx rdi, rax, rbp
adcx rax, r12
seto dl
inc r15
mov r12, -0x1 
movzx rbx, bl
adox rbx, r12
adox r11, r13
movzx rbx, r10b
adox rbx, r15
mov r10, r9
adcx r10, rdi
mov r13, r9
adcx r13, r14
adcx r9, r14
adc r14, 0x0
add dl, 0x7F
adox rax, [ rsp + 0xe0 ]
movzx rcx, cl
adcx rcx, r12
adcx r11, [ rsp - 0x18 ]
adox r10, [ rsp + 0xd8 ]
adcx rbx, [ rsp + 0x0 ]
setc cl
clc
adcx r8, [ rsp + 0x90 ]
adox r13, [ rsp + 0xd0 ]
adcx rax, [ rsp + 0x80 ]
mov rdx, 0x100000001 
mulx r15, rdi, r8
adox r9, r11
adox r14, rbx
adcx r10, [ rsp + 0x78 ]
movzx r15, cl
mov r11, 0x0 
adox r15, r11
adcx r13, [ rsp + 0x88 ]
adcx r9, [ rsp + 0xb8 ]
adcx r14, [ rsp + 0xc8 ]
mov rdx, rdi
mulx rcx, rdi, rbp
mov rbx, 0xffffffff 
mulx r12, r11, rbx
adcx r15, [ rsp + 0xc0 ]
mov rbp, 0xffffffff00000000 
mov [ rsp + 0xe8 ], r15
mulx r15, rbx, rbp
mov rbp, -0x2 
inc rbp
adox rbx, r12
adox rdi, r15
mov r12, 0xffffffffffffffff 
mulx rbp, r15, r12
setc dl
clc
adcx r11, r8
adcx rbx, rax
mov r11, r15
adox r11, rcx
adcx rdi, r10
mov r8, r15
adox r8, rbp
adox r15, rbp
mov rax, 0x0 
adox rbp, rax
adcx r11, r13
adcx r8, r9
adcx r15, r14
adcx rbp, [ rsp + 0xe8 ]
movzx r10, dl
adc r10, 0x0
add rbx, [ rsp - 0x30 ]
mov r13, 0x100000001 
mov rdx, r13
mulx r9, r13, rbx
adcx rdi, [ rsp - 0x48 ]
adcx r11, [ rsp - 0x38 ]
mov r9, 0xfffffffffffffffe 
mov rdx, r9
mulx r14, r9, r13
adcx r8, [ rsp - 0x40 ]
adcx r15, [ rsp + 0x20 ]
adcx rbp, [ rsp + 0x18 ]
mov rcx, 0xffffffff 
mov rdx, r13
mulx rax, r13, rcx
mov r12, -0x2 
inc r12
adox r13, rbx
mov r13, 0xffffffff00000000 
mulx r12, rbx, r13
adcx r10, [ rsp + 0x10 ]
setc r13b
clc
adcx rbx, rax
adcx r9, r12
adox rbx, rdi
setc dil
clc
adcx rbx, [ rsp - 0x28 ]
adox r9, r11
adcx r9, [ rsp + 0x48 ]
mov r11, 0xffffffffffffffff 
mulx r12, rax, r11
mov rdx, 0x100000001 
mulx rcx, r11, rbx
setc cl
clc
mov rdx, -0x1 
movzx rdi, dil
adcx rdi, rdx
adcx r14, rax
mov rdi, rax
adcx rdi, r12
adcx rax, r12
adox r14, r8
adox rdi, r15
mov r8, 0x0 
adcx r12, r8
adox rax, rbp
adox r12, r10
movzx r15, r13b
adox r15, r8
add cl, 0xFF
adcx r14, [ rsp + 0x70 ]
adcx rdi, [ rsp + 0x68 ]
adcx rax, [ rsp + 0x58 ]
mov rbp, 0xffffffff 
mov rdx, r11
mulx r13, r11, rbp
adcx r12, [ rsp + 0x50 ]
mov r10, 0xffffffff00000000 
mulx r8, rcx, r10
adcx r15, [ rsp + 0x60 ]
adox r11, rbx
setc r11b
clc
adcx rcx, r13
adox rcx, r9
mov rbx, 0xfffffffffffffffe 
mulx r13, r9, rbx
adcx r9, r8
adox r9, r14
mov r14, 0xffffffffffffffff 
mulx rbx, r8, r14
mov rdx, r8
adcx rdx, r13
adox rdx, rdi
mov rdi, r8
adcx rdi, rbx
adcx r8, rbx
mov r13, 0x0 
adcx rbx, r13
adox rdi, rax
adox r8, r12
adox rbx, r15
movzx rax, r11b
adox rax, r13
mov r12, rcx
sub r12, rbp
mov r11, r9
sbb r11, r10
mov r15, rdx
mov r13, 0xfffffffffffffffe 
sbb r15, r13
mov r13, rdi
sbb r13, r14
mov r10, r8
sbb r10, r14
mov rbp, rbx
sbb rbp, r14
sbb rax, 0x00000000
cmovc r11, r9
cmovc r10, r8
cmovc rbp, rbx
mov rax, [ rsp - 0x50 ]
mov [ rax + 0x28 ], rbp
mov [ rax + 0x20 ], r10
cmovc r13, rdi
mov [ rax + 0x8 ], r11
cmovc r12, rcx
mov [ rax + 0x0 ], r12
cmovc r15, rdx
mov [ rax + 0x10 ], r15
mov [ rax + 0x18 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 368
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.5071
; seed 2993683218347285 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 6648443 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=43, initial num_batches=31): 195475 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.029401620800539315
; number reverted permutation / tried permutation: 76010 / 89760 =84.681%
; number reverted decision / tried decision: 65838 / 90239 =72.960%
; validated in 45.121s
