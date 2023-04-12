SECTION .text
	GLOBAL fiat_p384_mul
fiat_p384_mul:
sub rsp, 384
mov rax, rdx
mov rdx, [ rdx + 0x10 ]
mulx r11, r10, [ rsi + 0x10 ]
mov rdx, [ rax + 0x20 ]
mulx r8, rcx, [ rsi + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x48 ], r13
mov [ rsp - 0x40 ], r9
mulx r9, r13, [ rsi + 0x18 ]
xor rdx, rdx
adox r15, r14
adox r13, rdi
mov rdx, [ rsi + 0x18 ]
mulx rdi, r14, [ rax + 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x38 ], r13
mov [ rsp - 0x30 ], r15
mulx r15, r13, [ rsi + 0x0 ]
adox r14, r9
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x28 ], r14
mulx r14, r9, [ rax + 0x10 ]
adox rbp, rdi
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x20 ], rbp
mulx rbp, rdi, [ rsi + 0x10 ]
adcx rdi, rbx
adcx r10, rbp
mov rdx, [ rax + 0x18 ]
mulx rbp, rbx, [ rsi + 0x10 ]
adcx rbx, r11
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], rbx
mulx rbx, r11, [ rax + 0x28 ]
adox r11, r12
mov rdx, 0x0 
adox rbx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x10 ], rbx
mulx rbx, r12, [ rax + 0x10 ]
adcx rcx, rbp
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x8 ], r11
mulx r11, rbp, [ rax + 0x28 ]
adcx rbp, r8
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x0 ], rbp
mulx rbp, r8, [ rsi + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x8 ], rcx
mov [ rsp + 0x10 ], r10
mulx r10, rcx, [ rsi + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x18 ], rdi
mov [ rsp + 0x20 ], r14
mulx r14, rdi, [ rsi + 0x8 ]
adc r11, 0x0
add r8, r10
adcx r12, rbp
adcx rdi, rbx
mov rdx, [ rax + 0x20 ]
mulx rbp, rbx, [ rsi + 0x8 ]
adcx rbx, r14
mov rdx, [ rax + 0x28 ]
mulx r14, r10, [ rsi + 0x8 ]
adcx r10, rbp
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x28 ], r11
mulx r11, rbp, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x30 ], rbp
mov [ rsp + 0x38 ], r10
mulx r10, rbp, [ rax + 0x8 ]
mov rdx, -0x2 
inc rdx
adox rbp, r11
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x40 ], rbp
mulx rbp, r11, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x48 ], rbx
mov [ rsp + 0x50 ], rdi
mulx rdi, rbx, [ rsi + 0x0 ]
mov rdx, 0x100000001 
mov [ rsp + 0x58 ], r12
mov [ rsp + 0x60 ], r8
mulx r8, r12, rbx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x68 ], rcx
mulx rcx, r8, [ rax + 0x10 ]
adox r9, r10
seto dl
mov r10, -0x2 
inc r10
adox r11, rdi
adox r8, rbp
adox r13, rcx
mov bpl, dl
mov rdx, [ rsi + 0x0 ]
mulx rcx, rdi, [ rax + 0x20 ]
adox rdi, r15
mov rdx, [ rsi + 0x20 ]
mulx r10, r15, [ rax + 0x0 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x70 ], r9
mov [ rsp + 0x78 ], r15
mulx r15, r9, [ rsi + 0x0 ]
adox r9, rcx
mov rdx, 0x0 
adcx r14, rdx
adox r15, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x80 ], r14
mulx r14, rcx, [ rax + 0x8 ]
add rcx, r10
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x88 ], rcx
mulx rcx, r10, [ rsi + 0x20 ]
adcx r10, r14
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x90 ], r10
mulx r10, r14, [ rsi + 0x20 ]
adcx r14, rcx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x98 ], r14
mulx r14, rcx, [ rax + 0x20 ]
mov rdx, 0xffffffff00000000 
mov [ rsp + 0xa0 ], r14
mov byte [ rsp + 0xa8 ], bpl
mulx rbp, r14, r12
adcx rcx, r10
mov r10, 0xffffffff 
mov rdx, r12
mov [ rsp + 0xb0 ], rcx
mulx rcx, r12, r10
mov r10, -0x2 
inc r10
adox r12, rbx
mov r12, 0xfffffffffffffffe 
mulx r10, rbx, r12
setc r12b
clc
adcx r14, rcx
adcx rbx, rbp
adox r14, r11
adox rbx, r8
mov r11, 0xffffffffffffffff 
mulx rbp, r8, r11
mov rdx, r8
adcx rdx, r10
mov rcx, r8
adcx rcx, rbp
adcx r8, rbp
mov r10, 0x0 
adcx rbp, r10
adox rdx, r13
adox rcx, rdi
adox r8, r9
clc
adcx r14, [ rsp + 0x68 ]
adcx rbx, [ rsp + 0x60 ]
adox rbp, r15
mov r13, rdx
mov rdx, [ rsi + 0x28 ]
mulx r9, rdi, [ rax + 0x18 ]
adcx r13, [ rsp + 0x58 ]
adcx rcx, [ rsp + 0x50 ]
seto dl
movzx r15, byte [ rsp + 0xa8 ]
dec r10
adox r15, r10
adox rdi, [ rsp + 0x20 ]
mov r15b, dl
mov rdx, [ rsi + 0x28 ]
mulx r11, r10, [ rax + 0x20 ]
adox r10, r9
adcx r8, [ rsp + 0x48 ]
adcx rbp, [ rsp + 0x38 ]
movzx r15, r15b
movzx rdx, r15b
adcx rdx, [ rsp + 0x80 ]
mov r15, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xb8 ], r10
mulx r10, r9, [ rax + 0x28 ]
mov rdx, 0x100000001 
mov [ rsp + 0xc0 ], rdi
mov byte [ rsp + 0xc8 ], r12b
mulx r12, rdi, r14
mov r12, 0xffffffff00000000 
mov rdx, rdi
mov [ rsp + 0xd0 ], r15
mulx r15, rdi, r12
adox r9, r11
mov r11, 0xffffffff 
mov [ rsp + 0xd8 ], r9
mulx r9, r12, r11
setc r11b
clc
adcx rdi, r9
mov r9, 0x0 
adox r10, r9
mov [ rsp + 0xe0 ], r10
mov r10, -0x3 
inc r10
adox r12, r14
adox rdi, rbx
mov r12, 0xfffffffffffffffe 
mulx rbx, r14, r12
adcx r14, r15
adox r14, r13
mov r13, 0xffffffffffffffff 
mulx r9, r15, r13
mov rdx, r15
adcx rdx, rbx
adox rdx, rcx
mov rcx, r15
adcx rcx, r9
adcx r15, r9
mov rbx, 0x0 
adcx r9, rbx
adox rcx, r8
adox r15, rbp
adox r9, [ rsp + 0xd0 ]
movzx r8, r11b
adox r8, rbx
add rdi, [ rsp - 0x40 ]
adcx r14, [ rsp + 0x18 ]
adcx rdx, [ rsp + 0x10 ]
adcx rcx, [ rsp - 0x18 ]
adcx r15, [ rsp + 0x8 ]
adcx r9, [ rsp + 0x0 ]
mov rbp, rdx
mov rdx, [ rax + 0x28 ]
mulx rbx, r11, [ rsi + 0x20 ]
mov rdx, 0x100000001 
mulx r13, r10, rdi
mov r13, 0xffffffff 
mov rdx, r10
mulx r12, r10, r13
adcx r8, [ rsp + 0x28 ]
mov r13, -0x2 
inc r13
adox r10, rdi
setc r10b
movzx rdi, byte [ rsp + 0xc8 ]
clc
adcx rdi, r13
adcx r11, [ rsp + 0xa0 ]
mov rdi, 0xffffffff00000000 
mov [ rsp + 0xe8 ], r11
mulx r11, r13, rdi
mov rdi, 0x0 
adcx rbx, rdi
clc
adcx r13, r12
adox r13, r14
mov r14, 0xfffffffffffffffe 
mulx rdi, r12, r14
adcx r12, r11
mov r11, 0xffffffffffffffff 
mov [ rsp + 0xf0 ], rbx
mulx rbx, r14, r11
adox r12, rbp
mov rbp, r14
adcx rbp, rdi
adox rbp, rcx
mov rcx, r14
adcx rcx, rbx
adcx r14, rbx
adox rcx, r15
adox r14, r9
mov r15, 0x0 
adcx rbx, r15
adox rbx, r8
movzx r9, r10b
adox r9, r15
xor rdx, rdx
adox r13, [ rsp - 0x48 ]
mov r15, 0x100000001 
mov rdx, r15
mulx r10, r15, r13
adox r12, [ rsp - 0x30 ]
adox rbp, [ rsp - 0x38 ]
adox rcx, [ rsp - 0x28 ]
adox r14, [ rsp - 0x20 ]
adox rbx, [ rsp - 0x8 ]
adox r9, [ rsp - 0x10 ]
mov r10, 0xffffffff 
mov rdx, r15
mulx r8, r15, r10
mov rdi, 0xffffffff00000000 
mulx r10, r11, rdi
adcx r15, r13
seto r15b
mov r13, -0x2 
inc r13
adox r11, r8
adcx r11, r12
mov r12, 0xfffffffffffffffe 
mulx r13, r8, r12
adox r8, r10
adcx r8, rbp
mov rbp, 0xffffffffffffffff 
mulx r12, r10, rbp
mov rdx, r10
adox rdx, r13
mov r13, r10
adox r13, r12
adox r10, r12
adcx rdx, rcx
adcx r13, r14
mov rcx, 0x0 
adox r12, rcx
adcx r10, rbx
adcx r12, r9
movzx r14, r15b
adc r14, 0x0
test al, al
adox r11, [ rsp + 0x78 ]
mov rbx, 0x100000001 
xchg rdx, rbx
mulx r9, r15, r11
adox r8, [ rsp + 0x88 ]
adox rbx, [ rsp + 0x90 ]
adox r13, [ rsp + 0x98 ]
adox r10, [ rsp + 0xb0 ]
adox r12, [ rsp + 0xe8 ]
mov r9, 0xffffffff 
mov rdx, r15
mulx rcx, r15, r9
mulx r9, rbp, rdi
adox r14, [ rsp + 0xf0 ]
adcx r15, r11
seto r15b
mov r11, -0x2 
inc r11
adox rbp, rcx
adcx rbp, r8
mov r8, 0xfffffffffffffffe 
mulx r11, rcx, r8
adox rcx, r9
adcx rcx, rbx
mov rbx, 0xffffffffffffffff 
mulx r8, r9, rbx
mov rdx, r9
adox rdx, r11
mov r11, r9
adox r11, r8
adcx rdx, r13
adcx r11, r10
adox r9, r8
adcx r9, r12
mov r13, 0x0 
adox r8, r13
adcx r8, r14
movzx r10, r15b
adc r10, 0x0
xor r12, r12
adox rbp, [ rsp + 0x30 ]
mov r13, 0x100000001 
xchg rdx, r13
mulx r14, r15, rbp
adox rcx, [ rsp + 0x40 ]
mov r14, 0xffffffff 
mov rdx, r15
mulx r12, r15, r14
adox r13, [ rsp + 0x70 ]
adox r11, [ rsp + 0xc0 ]
adox r9, [ rsp + 0xb8 ]
adcx r15, rbp
adox r8, [ rsp + 0xd8 ]
mulx rbp, r15, rdi
adox r10, [ rsp + 0xe0 ]
seto bl
mov r14, -0x2 
inc r14
adox r15, r12
adcx r15, rcx
mov rcx, 0xfffffffffffffffe 
mulx r14, r12, rcx
adox r12, rbp
adcx r12, r13
mov r13, 0xffffffffffffffff 
mulx rcx, rbp, r13
mov rdx, rbp
adox rdx, r14
mov r14, rbp
adox r14, rcx
adox rbp, rcx
adcx rdx, r11
mov r11, 0x0 
adox rcx, r11
adcx r14, r9
adcx rbp, r8
adcx rcx, r10
movzx r9, bl
adc r9, 0x0
mov r8, r15
mov rbx, 0xffffffff 
sub r8, rbx
mov r10, r12
sbb r10, rdi
mov r11, rdx
mov r13, 0xfffffffffffffffe 
sbb r11, r13
mov r13, r14
mov rbx, 0xffffffffffffffff 
sbb r13, rbx
mov rdi, rbp
sbb rdi, rbx
mov [ rsp + 0xf8 ], r8
mov r8, rcx
sbb r8, rbx
sbb r9, 0x00000000
cmovc r13, r14
cmovc r10, r12
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x8 ], r10
cmovc rdi, rbp
cmovc r11, rdx
mov [ r9 + 0x10 ], r11
cmovc r8, rcx
mov [ r9 + 0x28 ], r8
mov r12, [ rsp + 0xf8 ]
cmovc r12, r15
mov [ r9 + 0x0 ], r12
mov [ r9 + 0x20 ], rdi
mov [ r9 + 0x18 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 384
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.6419
; seed 2372027755415481 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4513283 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=46, initial num_batches=31): 122632 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.027171351763228675
; number reverted permutation / tried permutation: 74151 / 89860 =82.518%
; number reverted decision / tried decision: 64110 / 90139 =71.123%
; validated in 44.694s
