SECTION .text
	GLOBAL fiat_p384_square
fiat_p384_square:
sub rsp, 448
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, [ rsi + 0x10 ]
xor rdx, rdx
adox r8, r10
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r10, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rdx
adcx rbp, rcx
mov rdx, 0x100000001 
mov [ rsp - 0x58 ], r15
mulx r15, rcx, r11
adox r13, r9
mov rdx, [ rsi + 0x18 ]
mulx r9, r15, [ rsi + 0x0 ]
mov rdx, 0xfffffffffffffffe 
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r10
mulx r10, rdi, rcx
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x40 ], r13
mov [ rsp - 0x38 ], r8
mulx r8, r13, rcx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x30 ], rax
mov [ rsp - 0x28 ], rbx
mulx rbx, rax, [ rsi + 0x10 ]
mov rdx, 0xffffffff 
mov [ rsp - 0x20 ], rbp
mov [ rsp - 0x18 ], r9
mulx r9, rbp, rcx
adcx rax, r12
adcx r15, rbx
setc r12b
clc
adcx r13, r9
adcx rdi, r8
mov rdx, [ rsi + 0x0 ]
mulx rbx, r8, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], r8
mulx r8, r9, [ rsi + 0x10 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x8 ], r15
mov [ rsp + 0x0 ], rdi
mulx rdi, r15, rcx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x8 ], rdi
mulx rdi, rcx, [ rsi + 0x20 ]
mov rdx, r15
adcx rdx, r10
setc r10b
clc
adcx rcx, rbx
mov rbx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x10 ], rcx
mov byte [ rsp + 0x18 ], r10b
mulx r10, rcx, [ rsi + 0x20 ]
adcx rcx, rdi
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x20 ], rcx
mulx rcx, rdi, [ rsi + 0x10 ]
adox r9, r14
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x28 ], r9
mulx r9, r14, [ rsi + 0x20 ]
adox rdi, r8
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x30 ], rdi
mulx rdi, r8, [ rsi + 0x0 ]
seto dl
mov [ rsp + 0x38 ], rcx
mov rcx, 0x0 
dec rcx
movzx r12, r12b
adox r12, rcx
adox r14, [ rsp - 0x18 ]
mov r12b, dl
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x40 ], r14
mulx r14, rcx, [ rsi + 0x20 ]
adox r8, r9
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x48 ], r8
mulx r8, r9, [ rsi + 0x18 ]
adcx r9, r10
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x50 ], r9
mulx r9, r10, rdx
adcx r10, r8
adcx rcx, r9
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x58 ], rcx
mov [ rsp + 0x60 ], r10
mulx r10, rcx, [ rsi + 0x8 ]
mov rdx, 0x0 
adox rdi, rdx
mov [ rsp + 0x68 ], rdi
mov rdi, -0x3 
inc rdi
adox r8, r10
adcx r14, rdx
clc
adcx rbp, r11
adcx r13, [ rsp - 0x20 ]
adcx rax, [ rsp + 0x0 ]
adcx rbx, [ rsp - 0x8 ]
setc bpl
clc
adcx rcx, r13
mov rdx, [ rsi + 0x20 ]
mulx r10, r11, [ rsi + 0x8 ]
adcx r8, rax
mov rdx, [ rsi + 0x10 ]
mulx rax, r13, [ rsi + 0x8 ]
adox r13, r9
adcx r13, rbx
mov rdx, [ rsi + 0x18 ]
mulx rbx, r9, [ rsi + 0x8 ]
adox r9, rax
adox r11, rbx
mov rdx, 0x100000001 
mulx rbx, rax, rcx
mov rbx, 0xffffffff00000000 
mov rdx, rbx
mulx rdi, rbx, rax
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x70 ], r14
mov [ rsp + 0x78 ], r11
mulx r11, r14, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x80 ], r14
mov [ rsp + 0x88 ], r9
mulx r9, r14, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov byte [ rsp + 0x90 ], bpl
mov [ rsp + 0x98 ], r13
mulx r13, rbp, [ rsi + 0x8 ]
setc dl
clc
adcx r14, [ rsp - 0x28 ]
mov [ rsp + 0xa0 ], r14
mov r14b, dl
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xa8 ], r8
mov [ rsp + 0xb0 ], rdi
mulx rdi, r8, [ rsi + 0x10 ]
adcx r8, r9
adox rbp, r10
mov rdx, [ rsi + 0x18 ]
mulx r9, r10, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xb8 ], r8
mov [ rsp + 0xc0 ], rbp
mulx rbp, r8, [ rsi + 0x10 ]
adcx r10, rdi
mov rdx, 0x0 
adox r13, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xc8 ], r10
mulx r10, rdi, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xd0 ], r13
mov byte [ rsp + 0xd8 ], r14b
mulx r14, r13, [ rsi + 0x8 ]
adcx rdi, r9
mov rdx, -0x2 
inc rdx
adox r13, r11
mov rdx, [ rsi + 0x18 ]
mulx r9, r11, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xe0 ], r13
mov [ rsp + 0xe8 ], rdi
mulx rdi, r13, [ rsi + 0x10 ]
adox r13, r14
adox r11, rdi
mov rdx, [ rsi + 0x28 ]
mulx rdi, r14, [ rsi + 0x20 ]
adox r14, r9
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xf0 ], r14
mulx r14, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xf8 ], r11
mov [ rsp + 0x100 ], r13
mulx r13, r11, rdx
adox r11, rdi
adcx r9, r10
mov rdx, 0x0 
adox r13, rdx
adc r14, 0x0
mov r10, r15
add byte [ rsp + 0x18 ], 0xFF
adcx r10, [ rsp + 0x8 ]
adcx r15, [ rsp + 0x8 ]
mov rdi, [ rsp + 0x8 ]
adc rdi, 0x0
add r12b, 0xFF
adcx r8, [ rsp + 0x38 ]
adc rbp, 0x0
mov r12, 0xffffffff 
mov rdx, rax
mov [ rsp + 0x108 ], r13
mulx r13, rax, r12
test al, al
adox rbx, r13
mov r13, 0xfffffffffffffffe 
mov [ rsp + 0x110 ], r11
mulx r11, r12, r13
adox r12, [ rsp + 0xb0 ]
mov r13, 0xffffffffffffffff 
mov [ rsp + 0x118 ], r14
mov [ rsp + 0x120 ], r9
mulx r9, r14, r13
adcx rax, rcx
mov rax, r14
adox rax, r11
mov rcx, r14
adox rcx, r9
adcx rbx, [ rsp + 0xa8 ]
adox r14, r9
adcx r12, [ rsp + 0x98 ]
mov rdx, 0x0 
adox r9, rdx
movzx r11, byte [ rsp + 0x90 ]
dec rdx
adox r11, rdx
adox r10, [ rsp + 0x40 ]
adox r15, [ rsp + 0x48 ]
adox rdi, [ rsp + 0x68 ]
seto r11b
movzx rdx, byte [ rsp + 0xd8 ]
mov r13, 0x0 
dec r13
adox rdx, r13
adox r10, [ rsp + 0x88 ]
adox r15, [ rsp + 0x78 ]
adox rdi, [ rsp + 0xc0 ]
adcx rax, r10
adcx rcx, r15
movzx r11, r11b
movzx rdx, r11b
adox rdx, [ rsp + 0xd0 ]
adcx r14, rdi
adcx r9, rdx
setc r11b
clc
adcx rbx, [ rsp - 0x30 ]
mov r10, 0x100000001 
mov rdx, r10
mulx r15, r10, rbx
adcx r12, [ rsp - 0x38 ]
mov r15, 0xffffffffffffffff 
mov rdx, r10
mulx rdi, r10, r15
adcx rax, [ rsp - 0x40 ]
adcx rcx, [ rsp + 0x28 ]
adcx r14, [ rsp + 0x30 ]
adcx r8, r9
movzx r9, r11b
mov r13, 0x0 
adox r9, r13
mov r11, 0xffffffff 
mulx r15, r13, r11
mov r11, 0xffffffff00000000 
mov [ rsp + 0x128 ], r8
mov [ rsp + 0x130 ], r14
mulx r14, r8, r11
mov r11, -0x2 
inc r11
adox r8, r15
adcx rbp, r9
mov r9, 0xfffffffffffffffe 
mulx r11, r15, r9
adox r15, r14
mov rdx, r10
adox rdx, r11
mov r14, r10
adox r14, rdi
setc r11b
clc
adcx r13, rbx
adcx r8, r12
adcx r15, rax
adcx rdx, rcx
adox r10, rdi
adcx r14, [ rsp + 0x130 ]
adcx r10, [ rsp + 0x128 ]
mov r13, 0x0 
adox rdi, r13
adcx rdi, rbp
movzx rbx, r11b
adc rbx, 0x0
xor r12, r12
adox r8, [ rsp - 0x48 ]
adox r15, [ rsp + 0xa0 ]
mov r13, 0x100000001 
xchg rdx, r13
mulx rcx, rax, r8
mov rcx, 0xffffffff 
mov rdx, rax
mulx r11, rax, rcx
adcx rax, r8
adox r13, [ rsp + 0xb8 ]
mulx rbp, rax, r9
adox r14, [ rsp + 0xc8 ]
adox r10, [ rsp + 0xe8 ]
mov r8, 0xffffffff00000000 
mulx r9, r12, r8
adox rdi, [ rsp + 0x120 ]
adox rbx, [ rsp + 0x118 ]
seto cl
mov r8, -0x2 
inc r8
adox r12, r11
adcx r12, r15
adox rax, r9
adcx rax, r13
mov r15, 0xffffffffffffffff 
mulx r13, r11, r15
mov rdx, r11
adox rdx, rbp
adcx rdx, r14
mov rbp, r11
adox rbp, r13
adox r11, r13
adcx rbp, r10
mov r14, 0x0 
adox r13, r14
adcx r11, rdi
mov r10, -0x3 
inc r10
adox r12, [ rsp - 0x10 ]
adcx r13, rbx
adox rax, [ rsp + 0x10 ]
mov r9, 0x100000001 
xchg rdx, r9
mulx rbx, rdi, r12
mov rbx, 0xffffffff00000000 
mov rdx, rdi
mulx r14, rdi, rbx
mov r10, 0xffffffff 
mulx r15, r8, r10
adox r9, [ rsp + 0x20 ]
adox rbp, [ rsp + 0x50 ]
adox r11, [ rsp + 0x60 ]
adox r13, [ rsp + 0x58 ]
movzx r10, cl
mov rbx, 0x0 
adcx r10, rbx
adox r10, [ rsp + 0x70 ]
clc
adcx rdi, r15
seto cl
mov r15, -0x3 
inc r15
adox r8, r12
adox rdi, rax
mov r8, 0xfffffffffffffffe 
mulx rax, r12, r8
adcx r12, r14
mov r14, 0xffffffffffffffff 
mulx r15, rbx, r14
mov rdx, rbx
adcx rdx, rax
adox r12, r9
mov r9, rbx
adcx r9, r15
adcx rbx, r15
mov rax, 0x0 
adcx r15, rax
adox rdx, rbp
adox r9, r11
adox rbx, r13
adox r15, r10
movzx rbp, cl
adox rbp, rax
xor r11, r11
adox rdi, [ rsp + 0x80 ]
mov rax, 0x100000001 
xchg rdx, rax
mulx rcx, r13, rdi
adox r12, [ rsp + 0xe0 ]
mov rdx, r13
mulx r13, rcx, r8
adox rax, [ rsp + 0x100 ]
adox r9, [ rsp + 0xf8 ]
adox rbx, [ rsp + 0xf0 ]
mov r10, 0xffffffff00000000 
mulx r14, r11, r10
mov r8, 0xffffffff 
mov [ rsp + 0x138 ], rbx
mulx rbx, r10, r8
adox r15, [ rsp + 0x110 ]
adcx r10, rdi
adox rbp, [ rsp + 0x108 ]
seto r10b
mov rdi, -0x2 
inc rdi
adox r11, rbx
adcx r11, r12
adox rcx, r14
mov r12, 0xffffffffffffffff 
mulx rbx, r14, r12
mov rdx, r14
adox rdx, r13
adcx rcx, rax
mov r13, r14
adox r13, rbx
adox r14, rbx
adcx rdx, r9
adcx r13, [ rsp + 0x138 ]
adcx r14, r15
mov rax, 0x0 
adox rbx, rax
adcx rbx, rbp
movzx r9, r10b
adc r9, 0x0
mov r15, r11
sub r15, r8
mov r10, rcx
mov rbp, 0xffffffff00000000 
sbb r10, rbp
mov rax, rdx
mov rdi, 0xfffffffffffffffe 
sbb rax, rdi
mov rdi, r13
sbb rdi, r12
mov r8, r14
sbb r8, r12
mov rbp, rbx
sbb rbp, r12
sbb r9, 0x00000000
cmovc rbp, rbx
cmovc r10, rcx
cmovc r15, r11
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x0 ], r15
cmovc r8, r14
mov [ r9 + 0x20 ], r8
cmovc rdi, r13
mov [ r9 + 0x8 ], r10
mov [ r9 + 0x18 ], rdi
mov [ r9 + 0x28 ], rbp
cmovc rax, rdx
mov [ r9 + 0x10 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 448
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.4812
; seed 1849528033282531 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4456631 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=51, initial num_batches=31): 121046 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.02716087555824119
; number reverted permutation / tried permutation: 75564 / 89869 =84.082%
; number reverted decision / tried decision: 65760 / 90130 =72.961%
; validated in 38.064s
