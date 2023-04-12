SECTION .text
	GLOBAL fiat_p384_square
fiat_p384_square:
sub rsp, 408
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x8 ]
xor rdx, rdx
adox rbx, r10
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mulx r14, r10, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x48 ], rbx
mov [ rsp - 0x40 ], rax
mulx rax, rbx, [ rsi + 0x18 ]
adcx r11, rax
adcx r15, rcx
mov rdx, [ rsi + 0x10 ]
mulx rax, rcx, rdx
adox rcx, rbp
seto dl
mov rbp, -0x2 
inc rbp
adox r12, r9
mov r9b, dl
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x38 ], r15
mulx r15, rbp, [ rsi + 0x10 ]
adox rbp, r13
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], r11
mulx r11, r13, [ rsi + 0x0 ]
adox r13, r15
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], rbx
mulx rbx, r15, rdx
adcx r15, rdi
mov rdx, 0x100000001 
mov [ rsp - 0x20 ], r15
mulx r15, rdi, r8
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x18 ], rcx
mulx rcx, r15, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], r15
mov [ rsp - 0x8 ], r14
mulx r14, r15, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x0 ], rax
mov byte [ rsp + 0x8 ], r9b
mulx r9, rax, [ rsi + 0x8 ]
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x10 ], r14
mov [ rsp + 0x18 ], r9
mulx r9, r14, rdi
mov rdx, 0xffffffff 
mov [ rsp + 0x20 ], r13
mov [ rsp + 0x28 ], rbp
mulx rbp, r13, rdi
adcx r15, rbx
setc bl
clc
adcx r14, rbp
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x30 ], r15
mulx r15, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov byte [ rsp + 0x38 ], bl
mov [ rsp + 0x40 ], rbp
mulx rbp, rbx, rdx
setc dl
clc
adcx rbx, r15
adcx rax, rbp
setc r15b
clc
adcx r13, r8
mov r13b, dl
mov rdx, [ rsi + 0x28 ]
mulx rbp, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x48 ], rax
mov [ rsp + 0x50 ], rbx
mulx rbx, rax, [ rsi + 0x20 ]
adcx r14, r12
setc dl
clc
adcx rax, rcx
adcx r10, rbx
mov r12b, dl
mov rdx, [ rsi + 0x28 ]
mulx rbx, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x58 ], r10
mov [ rsp + 0x60 ], rax
mulx rax, r10, [ rsi + 0x28 ]
setc dl
clc
adcx rcx, rax
adcx r8, rbx
mov bl, dl
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x68 ], r8
mulx r8, rax, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x70 ], rcx
mov [ rsp + 0x78 ], r10
mulx r10, rcx, [ rsi + 0x20 ]
adcx rax, rbp
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x80 ], rax
mulx rax, rbp, [ rsi + 0x20 ]
adox rbp, r11
mov rdx, [ rsi + 0x28 ]
mov byte [ rsp + 0x88 ], bl
mulx rbx, r11, [ rsi + 0x0 ]
adox r11, rax
mov rdx, 0xfffffffffffffffe 
mov byte [ rsp + 0x90 ], r15b
mulx r15, rax, rdi
adcx rcx, r8
mov r8, 0x0 
adox rbx, r8
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x98 ], rcx
mulx rcx, r8, rdx
adcx r8, r10
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0xa0 ], r8
mulx r8, r10, rdi
adc rcx, 0x0
add r13b, 0xFF
adcx r9, rax
mov rdi, r10
adcx rdi, r15
mov r13, r10
adcx r13, r8
adcx r10, r8
adc r8, 0x0
mov rdx, [ rsi + 0x8 ]
mulx r15, rax, [ rsi + 0x18 ]
add r12b, 0x7F
adox r9, [ rsp + 0x28 ]
adox rdi, [ rsp + 0x20 ]
adox r13, rbp
adox r10, r11
adox r8, rbx
adcx r14, [ rsp + 0x40 ]
mov rdx, [ rsi + 0x20 ]
mulx rbp, r12, [ rsi + 0x8 ]
seto dl
movzx r11, byte [ rsp + 0x90 ]
mov rbx, 0x0 
dec rbx
adox r11, rbx
adox rax, [ rsp + 0x18 ]
adcx r9, [ rsp + 0x50 ]
adox r12, r15
adcx rdi, [ rsp + 0x48 ]
mov r11b, dl
mov rdx, [ rsi + 0x18 ]
mulx rbx, r15, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xa8 ], rcx
mov [ rsp + 0xb0 ], rdi
mulx rdi, rcx, [ rsi + 0x8 ]
adox rcx, rbp
adcx rax, r13
adcx r12, r10
mov rdx, [ rsi + 0x18 ]
mulx r10, r13, [ rsi + 0x10 ]
adcx rcx, r8
mov rdx, [ rsi + 0x10 ]
mulx rbp, r8, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xb8 ], rcx
mov [ rsp + 0xc0 ], r12
mulx r12, rcx, rdx
setc dl
mov [ rsp + 0xc8 ], rax
movzx rax, byte [ rsp + 0x38 ]
clc
mov [ rsp + 0xd0 ], r9
mov r9, -0x1 
adcx rax, r9
adcx r15, [ rsp + 0x10 ]
mov al, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xd8 ], r15
mulx r15, r9, [ rsi + 0x20 ]
mov rdx, 0x0 
adcx rbx, rdx
adox rdi, rdx
add byte [ rsp + 0x8 ], 0xFF
adcx r13, [ rsp + 0x0 ]
adcx r9, r10
adcx r8, r15
adc rbp, 0x0
movzx r11, r11b
add al, 0x7F
adox rdi, r11
mov rdx, [ rsi + 0x20 ]
mulx r10, r11, [ rsi + 0x18 ]
movzx rdx, byte [ rsp + 0x88 ]
mov rax, -0x1 
adcx rdx, rax
adcx r11, [ rsp - 0x8 ]
adcx rcx, r10
mov rdx, 0x100000001 
mulx r10, r15, r14
mov rdx, [ rsi + 0x20 ]
mulx rax, r10, [ rsi + 0x28 ]
adcx r10, r12
mov rdx, 0xffffffff 
mov [ rsp + 0xe0 ], r10
mulx r10, r12, r15
mov rdx, 0x0 
adcx rax, rdx
mov rdx, 0xffffffff00000000 
mov [ rsp + 0xe8 ], rax
mov [ rsp + 0xf0 ], rcx
mulx rcx, rax, r15
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0xf8 ], r11
mov [ rsp + 0x100 ], rbx
mulx rbx, r11, r15
clc
adcx rax, r10
mov r10, 0xfffffffffffffffe 
mov rdx, r15
mov [ rsp + 0x108 ], rbp
mulx rbp, r15, r10
adcx r15, rcx
seto dl
mov rcx, -0x2 
inc rcx
adox r12, r14
adox rax, [ rsp + 0xd0 ]
adox r15, [ rsp + 0xb0 ]
mov r12, r11
adcx r12, rbp
mov r14, r11
adcx r14, rbx
adcx r11, rbx
adox r12, [ rsp + 0xc8 ]
adox r14, [ rsp + 0xc0 ]
adox r11, [ rsp + 0xb8 ]
mov rbp, 0x0 
adcx rbx, rbp
clc
adcx rax, [ rsp - 0x40 ]
adcx r15, [ rsp - 0x48 ]
adcx r12, [ rsp - 0x18 ]
adcx r13, r14
adox rbx, rdi
adcx r9, r11
movzx rdi, dl
adox rdi, rbp
mov rdx, 0x100000001 
mulx r11, r14, rax
mov r11, 0xffffffff 
mov rdx, r11
mulx rbp, r11, r14
inc rcx
adox r11, rax
adcx r8, rbx
adcx rdi, [ rsp + 0x108 ]
mov r11, 0xffffffff00000000 
mov rdx, r14
mulx rax, r14, r11
setc bl
clc
adcx r14, rbp
adox r14, r15
mulx rbp, r15, r10
adcx r15, rax
mov rax, 0xffffffffffffffff 
mulx r10, rcx, rax
adox r15, r12
mov r12, rcx
adcx r12, rbp
adox r12, r13
mov r13, rcx
adcx r13, r10
adox r13, r9
adcx rcx, r10
adox rcx, r8
mov r9, 0x0 
adcx r10, r9
clc
adcx r14, [ rsp - 0x28 ]
adcx r15, [ rsp - 0x30 ]
adcx r12, [ rsp - 0x38 ]
adox r10, rdi
adcx r13, [ rsp - 0x20 ]
adcx rcx, [ rsp + 0x30 ]
mov rdx, 0x100000001 
mulx rdi, r8, r14
mov rdx, r8
mulx r8, rdi, r11
movzx rbp, bl
adox rbp, r9
adcx r10, [ rsp + 0xd8 ]
adcx rbp, [ rsp + 0x100 ]
mov rbx, 0xffffffff 
mulx rax, r9, rbx
mov rbx, -0x2 
inc rbx
adox rdi, rax
mov rax, 0xfffffffffffffffe 
mulx r11, rbx, rax
adox rbx, r8
setc r8b
clc
adcx r9, r14
mov r9, 0xffffffffffffffff 
mulx rax, r14, r9
adcx rdi, r15
adcx rbx, r12
mov r15, r14
adox r15, r11
mov r12, r14
adox r12, rax
adox r14, rax
adcx r15, r13
adcx r12, rcx
adcx r14, r10
mov r13, 0x0 
adox rax, r13
adcx rax, rbp
movzx rcx, r8b
adc rcx, 0x0
add rdi, [ rsp - 0x10 ]
mov rdx, 0x100000001 
mulx r8, r10, rdi
adcx rbx, [ rsp + 0x60 ]
mov r8, 0xffffffff 
mov rdx, r10
mulx rbp, r10, r8
mulx r13, r11, r9
adcx r15, [ rsp + 0x58 ]
adcx r12, [ rsp + 0xf8 ]
adcx r14, [ rsp + 0xf0 ]
mov r8, -0x2 
inc r8
adox r10, rdi
adcx rax, [ rsp + 0xe0 ]
adcx rcx, [ rsp + 0xe8 ]
mov r10, 0xfffffffffffffffe 
mulx r8, rdi, r10
mov r9, 0xffffffff00000000 
mov [ rsp + 0x110 ], rcx
mulx rcx, r10, r9
setc dl
clc
adcx r10, rbp
adcx rdi, rcx
adox r10, rbx
mov rbx, r11
adcx rbx, r8
adox rdi, r15
mov rbp, r11
adcx rbp, r13
adcx r11, r13
mov r15, 0x0 
adcx r13, r15
adox rbx, r12
adox rbp, r14
adox r11, rax
adox r13, [ rsp + 0x110 ]
clc
adcx r10, [ rsp + 0x78 ]
movzx r12, dl
adox r12, r15
adcx rdi, [ rsp + 0x70 ]
adcx rbx, [ rsp + 0x68 ]
adcx rbp, [ rsp + 0x80 ]
adcx r11, [ rsp + 0x98 ]
adcx r13, [ rsp + 0xa0 ]
mov r14, 0x100000001 
mov rdx, r14
mulx rax, r14, r10
mov rax, 0xffffffff 
mov rdx, r14
mulx r8, r14, rax
mulx r15, rcx, r9
mov r9, -0x2 
inc r9
adox rcx, r8
adcx r12, [ rsp + 0xa8 ]
setc r8b
clc
adcx r14, r10
adcx rcx, rdi
mov r14, 0xfffffffffffffffe 
mulx rdi, r10, r14
adox r10, r15
adcx r10, rbx
mov rbx, 0xffffffffffffffff 
mulx r9, r15, rbx
mov rdx, r15
adox rdx, rdi
adcx rdx, rbp
mov rbp, r15
adox rbp, r9
adox r15, r9
adcx rbp, r11
mov r11, 0x0 
adox r9, r11
adcx r15, r13
adcx r9, r12
movzx r13, r8b
adc r13, 0x0
mov r8, rcx
sub r8, rax
mov r12, r10
mov rdi, 0xffffffff00000000 
sbb r12, rdi
mov r11, rdx
sbb r11, r14
mov rdi, rbp
sbb rdi, rbx
mov rax, r15
sbb rax, rbx
mov r14, r9
sbb r14, rbx
sbb r13, 0x00000000
cmovc rdi, rbp
cmovc r12, r10
cmovc r14, r9
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x8 ], r12
mov [ r13 + 0x28 ], r14
cmovc rax, r15
cmovc r8, rcx
mov [ r13 + 0x0 ], r8
cmovc r11, rdx
mov [ r13 + 0x10 ], r11
mov [ r13 + 0x20 ], rax
mov [ r13 + 0x18 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 408
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.5651
; seed 0531913486282329 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 6002465 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=95, initial num_batches=31): 189540 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.03157702710469782
; number reverted permutation / tried permutation: 76885 / 89873 =85.548%
; number reverted decision / tried decision: 66809 / 90126 =74.128%
; validated in 49.928s
