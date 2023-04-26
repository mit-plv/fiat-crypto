SECTION .text
	GLOBAL fiat_p384_square
fiat_p384_square:
sub rsp, 384
mov rdx, [ rsi + 0x10 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r14
mulx r14, rdi, [ rsi + 0x20 ]
add r11, r15
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x40 ], r11
mulx r11, r15, [ rsi + 0x10 ]
adcx r15, rcx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x38 ], r15
mulx r15, rcx, [ rsi + 0x18 ]
adcx rcx, r11
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], rcx
mulx rcx, r11, [ rsi + 0x20 ]
mov rdx, -0x2 
inc rdx
adox rdi, r9
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], rdi
mulx rdi, r9, [ rsi + 0x10 ]
adox r11, r14
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x20 ], r11
mulx r11, r14, rdx
adcx r12, r15
setc dl
clc
adcx r9, r10
adcx r14, rdi
mov r10b, dl
mov rdx, [ rsi + 0x0 ]
mulx rdi, r15, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x18 ], r12
mov [ rsp - 0x10 ], r8
mulx r8, r12, [ rsi + 0x8 ]
adcx rbx, r11
setc dl
clc
adcx r12, rdi
mov r11b, dl
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x8 ], rbx
mulx rbx, rdi, [ rsi + 0x10 ]
adcx rdi, r8
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x0 ], r14
mulx r14, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x8 ], r9
mov [ rsp + 0x10 ], rax
mulx rax, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x18 ], rbp
mov byte [ rsp + 0x20 ], r11b
mulx r11, rbp, [ rsi + 0x20 ]
adcx r9, rbx
adox r8, rcx
mov rdx, [ rsi + 0x0 ]
mulx rbx, rcx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x28 ], r8
mov [ rsp + 0x30 ], r9
mulx r9, r8, rdx
adox r8, r14
adox rbp, r9
adcx rcx, rax
mov rdx, [ rsi + 0x0 ]
mulx rax, r14, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x38 ], rbp
mulx rbp, r9, [ rsi + 0x0 ]
adcx r14, rbx
mov rdx, 0x0 
adox r11, rdx
adc rax, 0x0
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x40 ], r11
mulx r11, rbx, rdx
add rbx, rbp
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x48 ], r8
mulx r8, rbp, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x50 ], rax
mov [ rsp + 0x58 ], r14
mulx r14, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x60 ], rcx
mov [ rsp + 0x68 ], rbx
mulx rbx, rcx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x70 ], rcx
mov [ rsp + 0x78 ], r9
mulx r9, rcx, [ rsi + 0x8 ]
adcx rcx, r11
adcx rbp, r9
mov rdx, [ rsi + 0x8 ]
mulx r9, r11, [ rsi + 0x28 ]
adcx rax, r8
adcx r11, r14
mov rdx, [ rsi + 0x10 ]
mulx r14, r8, [ rsi + 0x18 ]
adc r9, 0x0
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x80 ], r9
mov [ rsp + 0x88 ], r11
mulx r11, r9, [ rsi + 0x18 ]
add r9, rbx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x90 ], r9
mulx r9, rbx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x98 ], rax
mov [ rsp + 0xa0 ], rbp
mulx rbp, rax, [ rsi + 0x20 ]
adcx r8, r11
adcx rbx, r14
mov rdx, [ rsi + 0x28 ]
mulx r11, r14, [ rsi + 0x18 ]
adcx rax, r9
adcx r14, rbp
mov rdx, 0x100000001 
mulx rbp, r9, r15
mov rbp, 0xffffffff 
mov rdx, rbp
mov [ rsp + 0xa8 ], r14
mulx r14, rbp, r9
adc r11, 0x0
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xb0 ], r11
mov [ rsp + 0xb8 ], rax
mulx rax, r11, rdx
mov rdx, 0xffffffff00000000 
mov [ rsp + 0xc0 ], rbx
mov [ rsp + 0xc8 ], r8
mulx r8, rbx, r9
add r10b, 0x7F
adox r13, r11
adcx rbx, r14
mov r10, 0xfffffffffffffffe 
mov rdx, r9
mulx r14, r9, r10
adcx r9, r8
mov r11, 0xffffffffffffffff 
mulx r10, r8, r11
mov rdx, r8
adcx rdx, r14
mov r14, r8
adcx r14, r10
adcx r8, r10
mov r11, 0x0 
adox rax, r11
adc r10, 0x0
test al, al
adox rbp, r15
adox rbx, r12
adox r9, rdi
adcx rbx, [ rsp + 0x78 ]
adox rdx, [ rsp + 0x30 ]
adcx r9, [ rsp + 0x68 ]
adcx rcx, rdx
adox r14, [ rsp + 0x60 ]
adox r8, [ rsp + 0x58 ]
mov rdx, [ rsi + 0x28 ]
mulx r15, rbp, [ rsi + 0x10 ]
adox r10, [ rsp + 0x50 ]
mov rdx, [ rsi + 0x20 ]
mulx rdi, r12, [ rsi + 0x10 ]
adcx r14, [ rsp + 0xa0 ]
mov rdx, 0x100000001 
mov [ rsp + 0xd0 ], rax
mulx rax, r11, rbx
adcx r8, [ rsp + 0x98 ]
mov rax, 0xffffffff 
mov rdx, r11
mov [ rsp + 0xd8 ], r13
mulx r13, r11, rax
adcx r10, [ rsp + 0x88 ]
setc al
movzx rax, al
adox rax, [ rsp + 0x80 ]
mov [ rsp + 0xe0 ], rax
movzx rax, byte [ rsp + 0x20 ]
clc
mov [ rsp + 0xe8 ], r10
mov r10, -0x1 
adcx rax, r10
adcx r12, [ rsp + 0x18 ]
adcx rbp, rdi
mov rax, 0xffffffff00000000 
mulx r10, rdi, rax
mov rax, 0x0 
adcx r15, rax
clc
adcx rdi, r13
mov r13, 0xfffffffffffffffe 
mov [ rsp + 0xf0 ], r15
mulx r15, rax, r13
adcx rax, r10
seto r10b
mov r13, -0x2 
inc r13
adox r11, rbx
adox rdi, r9
adox rax, rcx
mov r11, 0xffffffffffffffff 
mulx r9, rbx, r11
mov rcx, rbx
adcx rcx, r15
adox rcx, r14
mov r14, rbx
adcx r14, r9
adcx rbx, r9
adox r14, r8
adox rbx, [ rsp + 0xe8 ]
mov rdx, 0x0 
adcx r9, rdx
clc
adcx rdi, [ rsp + 0x10 ]
adcx rax, [ rsp + 0x8 ]
adcx rcx, [ rsp + 0x0 ]
adcx r14, [ rsp - 0x8 ]
adox r9, [ rsp + 0xe0 ]
movzx r8, r10b
adox r8, rdx
adcx r12, rbx
adcx rbp, r9
mov r10, 0x100000001 
mov rdx, r10
mulx r15, r10, rdi
mov r15, 0xffffffff00000000 
mov rdx, r10
mulx rbx, r10, r15
mov r9, 0xffffffff 
mulx r11, r13, r9
mov r15, -0x2 
inc r15
adox r10, r11
mov r11, 0xfffffffffffffffe 
mulx r9, r15, r11
adox r15, rbx
adcx r8, [ rsp + 0xf0 ]
setc bl
clc
adcx r13, rdi
adcx r10, rax
adcx r15, rcx
mov r13, 0xffffffffffffffff 
mulx rax, rdi, r13
mov rcx, rdi
adox rcx, r9
adcx rcx, r14
mov r14, rdi
adox r14, rax
adox rdi, rax
mov rdx, 0x0 
adox rax, rdx
mov r9, -0x3 
inc r9
adox r10, [ rsp + 0x70 ]
adox r15, [ rsp + 0x90 ]
adcx r14, r12
adcx rdi, rbp
adox rcx, [ rsp + 0xc8 ]
adcx rax, r8
adox r14, [ rsp + 0xc0 ]
adox rdi, [ rsp + 0xb8 ]
movzx r12, bl
adcx r12, rdx
adox rax, [ rsp + 0xa8 ]
mov rbp, 0x100000001 
mov rdx, rbp
mulx rbx, rbp, r10
mov rbx, 0xffffffff 
mov rdx, rbx
mulx r8, rbx, rbp
clc
adcx rbx, r10
mov rbx, 0xffffffff00000000 
mov rdx, rbp
mulx r10, rbp, rbx
adox r12, [ rsp + 0xb0 ]
mulx r13, r9, r11
seto r11b
mov rbx, -0x2 
inc rbx
adox rbp, r8
adox r9, r10
adcx rbp, r15
mov r15, 0xffffffffffffffff 
mulx r10, r8, r15
adcx r9, rcx
mov rcx, r8
adox rcx, r13
adcx rcx, r14
mov r14, r8
adox r14, r10
adcx r14, rdi
adox r8, r10
adcx r8, rax
mov rdi, 0x0 
adox r10, rdi
adcx r10, r12
mov rax, -0x3 
inc rax
adox rbp, [ rsp - 0x10 ]
adox r9, [ rsp - 0x28 ]
mov rdx, 0x100000001 
mulx r13, r12, rbp
adox rcx, [ rsp - 0x20 ]
adox r14, [ rsp + 0x28 ]
adox r8, [ rsp + 0x48 ]
adox r10, [ rsp + 0x38 ]
movzx r13, r11b
adcx r13, rdi
adox r13, [ rsp + 0x40 ]
mov r11, 0xffffffff 
mov rdx, r12
mulx rdi, r12, r11
clc
adcx r12, rbp
mov r12, 0xffffffff00000000 
mulx rax, rbp, r12
seto bl
mov r15, -0x2 
inc r15
adox rbp, rdi
adcx rbp, r9
mov r9, 0xfffffffffffffffe 
mulx r15, rdi, r9
adox rdi, rax
mov rax, 0xffffffffffffffff 
mulx r12, r9, rax
adcx rdi, rcx
mov rdx, r9
adox rdx, r15
mov rcx, r9
adox rcx, r12
adox r9, r12
adcx rdx, r14
adcx rcx, r8
adcx r9, r10
mov r14, 0x0 
adox r12, r14
adcx r12, r13
movzx r8, bl
adc r8, 0x0
xor r10, r10
adox rbp, [ rsp - 0x48 ]
adox rdi, [ rsp - 0x40 ]
mov r14, 0x100000001 
xchg rdx, r14
mulx r13, rbx, rbp
mov rdx, r11
mulx r13, r11, rbx
mov rdx, rbx
mulx r15, rbx, rax
adox r14, [ rsp - 0x38 ]
adox rcx, [ rsp - 0x30 ]
adox r9, [ rsp - 0x18 ]
adox r12, [ rsp + 0xd8 ]
adox r8, [ rsp + 0xd0 ]
mov r10, 0xffffffff00000000 
mov [ rsp + 0xf8 ], r8
mulx r8, rax, r10
adcx r11, rbp
seto r11b
mov rbp, -0x2 
inc rbp
adox rax, r13
adcx rax, rdi
mov rdi, 0xfffffffffffffffe 
mulx rbp, r13, rdi
adox r13, r8
mov rdx, rbx
adox rdx, rbp
adcx r13, r14
adcx rdx, rcx
mov r14, rbx
adox r14, r15
adox rbx, r15
adcx r14, r9
adcx rbx, r12
mov rcx, 0x0 
adox r15, rcx
adcx r15, [ rsp + 0xf8 ]
movzx r9, r11b
adc r9, 0x0
mov r12, rax
mov r11, 0xffffffff 
sub r12, r11
mov r8, r13
sbb r8, r10
mov rbp, rdx
sbb rbp, rdi
mov rcx, r14
mov rdi, 0xffffffffffffffff 
sbb rcx, rdi
mov r10, rbx
sbb r10, rdi
mov r11, r15
sbb r11, rdi
sbb r9, 0x00000000
cmovc r8, r13
cmovc r11, r15
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x8 ], r8
cmovc rbp, rdx
cmovc rcx, r14
mov [ r9 + 0x10 ], rbp
cmovc r10, rbx
mov [ r9 + 0x28 ], r11
cmovc r12, rax
mov [ r9 + 0x0 ], r12
mov [ r9 + 0x20 ], r10
mov [ r9 + 0x18 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 384
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.5914
; seed 3000466291231440 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5813247 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=95, initial num_batches=31): 187571 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.03226613285139957
; number reverted permutation / tried permutation: 77048 / 90126 =85.489%
; number reverted decision / tried decision: 64372 / 89873 =71.626%
; validated in 51.269s
