SECTION .text
	GLOBAL fiat_p384_square
fiat_p384_square:
sub rsp, 400
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mulx r9, r8, [ rsi + 0x10 ]
mov rdx, 0x100000001 
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rax
mov rbp, 0xffffffff00000000 
mov rdx, rbx
mov [ rsp - 0x70 ], r12
mulx r12, rbx, rbp
mov [ rsp - 0x68 ], r13
mov r13, 0xffffffffffffffff 
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, r13
mov r13, 0xffffffff 
mov [ rsp - 0x50 ], rdi
mulx rdi, rbp, r13
test al, al
adox rbp, rax
mov rbp, 0xfffffffffffffffe 
mulx r13, rax, rbp
adcx rbx, rdi
adcx rax, r12
mov rdx, [ rsi + 0x0 ]
mulx rdi, r12, [ rsi + 0x28 ]
mov rdx, r14
adcx rdx, r13
mov r13, r14
adcx r13, r15
adcx r14, r15
mov rbp, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x48 ], r12
mov [ rsp - 0x40 ], r9
mulx r9, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x38 ], r12
mov [ rsp - 0x30 ], r8
mulx r8, r12, [ rsi + 0x8 ]
mov rdx, 0x0 
adcx r15, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], r15
mov [ rsp - 0x20 ], rdi
mulx rdi, r15, [ rsi + 0x0 ]
clc
adcx r12, r10
adox rbx, r12
adcx r15, r8
setc dl
clc
adcx r11, r9
mov r10b, dl
mov rdx, [ rsi + 0x10 ]
mulx r8, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], r11
mulx r11, r12, rdx
adcx r9, rcx
adcx r12, r8
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], r12
mov [ rsp - 0x8 ], r9
mulx r9, r12, [ rsi + 0x20 ]
adcx r12, r11
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x0 ], r12
mulx r12, r11, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x8 ], r12
mov [ rsp + 0x10 ], r14
mulx r14, r12, [ rsi + 0x28 ]
adcx r12, r9
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x18 ], r12
mulx r12, r9, [ rsi + 0x10 ]
setc dl
clc
adcx r11, r8
setc r8b
clc
adcx rcx, rbx
movzx rbx, dl
lea rbx, [ rbx + r14 ]
adox rax, r15
mov rdx, [ rsi + 0x10 ]
mulx r14, r15, [ rsi + 0x8 ]
adcx r11, rax
setc dl
clc
adcx r15, r12
mov r12b, dl
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x20 ], rbx
mulx rbx, rax, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x28 ], rax
mov [ rsp + 0x30 ], r15
mulx r15, rax, rdx
adcx rax, r14
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x38 ], rax
mulx rax, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x40 ], r9
mov [ rsp + 0x48 ], r11
mulx r11, r9, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov byte [ rsp + 0x50 ], r12b
mov byte [ rsp + 0x58 ], r8b
mulx r8, r12, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x60 ], rcx
mov [ rsp + 0x68 ], r8
mulx r8, rcx, [ rsi + 0x18 ]
setc dl
clc
adcx r9, rbx
adcx r12, r11
setc bl
clc
mov r11, -0x1 
movzx r10, r10b
adcx r10, r11
adcx rdi, r14
adox rbp, rdi
mov r10b, dl
mov rdx, [ rsi + 0x0 ]
mulx rdi, r14, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x70 ], r12
mulx r12, r11, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x78 ], r9
mov [ rsp + 0x80 ], rbp
mulx rbp, r9, [ rsi + 0x20 ]
adcx r9, rax
adox r13, r9
adcx r14, rbp
mov rdx, 0x0 
adcx rdi, rdx
mov rdx, [ rsi + 0x8 ]
mulx rbp, rax, [ rsi + 0x28 ]
clc
adcx rax, [ rsp - 0x20 ]
adox r14, [ rsp + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x88 ], rax
mulx rax, r9, [ rsi + 0x28 ]
adox rdi, [ rsp - 0x28 ]
seto dl
mov [ rsp + 0x90 ], rdi
mov rdi, 0x0 
dec rdi
movzx r10, r10b
adox r10, rdi
adox r15, rcx
mov r10b, dl
mov rdx, [ rsi + 0x28 ]
mulx rdi, rcx, [ rsi + 0x18 ]
adcx r11, rbp
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x98 ], r11
mulx r11, rbp, rdx
adcx rcx, r12
adox r8, [ rsp - 0x30 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xa0 ], rcx
mulx rcx, r12, [ rsi + 0x28 ]
adox r9, [ rsp - 0x40 ]
adcx r12, rdi
adcx rbp, rcx
mov rdx, [ rsi + 0x20 ]
mulx rcx, rdi, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xa8 ], rbp
mov [ rsp + 0xb0 ], r12
mulx r12, rbp, rdx
mov rdx, 0x0 
adcx r11, rdx
adox rax, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xb8 ], r11
mov [ rsp + 0xc0 ], rax
mulx rax, r11, [ rsi + 0x18 ]
add bl, 0xFF
adcx r11, [ rsp + 0x68 ]
adcx rbp, rax
mov rdx, [ rsi + 0x8 ]
mulx rax, rbx, [ rsi + 0x20 ]
adcx rdi, r12
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xc8 ], rdi
mulx rdi, r12, [ rsi + 0x10 ]
mov rdx, 0x100000001 
mov [ rsp + 0xd0 ], rbp
mov [ rsp + 0xd8 ], r11
mulx r11, rbp, [ rsp + 0x60 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xe0 ], r9
mulx r9, r11, [ rsi + 0x8 ]
adc rcx, 0x0
add byte [ rsp + 0x58 ], 0x7F
adox r12, [ rsp + 0x8 ]
adox r11, rdi
mov rdx, 0xffffffff00000000 
mov [ rsp + 0xe8 ], rcx
mulx rcx, rdi, rbp
mov rdx, 0xffffffff 
mov [ rsp + 0xf0 ], r8
mov [ rsp + 0xf8 ], r15
mulx r15, r8, rbp
adox rbx, r9
adcx rdi, r15
mov rdx, [ rsi + 0x8 ]
mulx r15, r9, [ rsi + 0x28 ]
adox r9, rax
mov rdx, 0xfffffffffffffffe 
mov byte [ rsp + 0x100 ], r10b
mulx r10, rax, rbp
mov rdx, 0x0 
adox r15, rdx
adcx rax, rcx
mov rcx, 0xffffffffffffffff 
mov rdx, rcx
mov [ rsp + 0x108 ], rax
mulx rax, rcx, rbp
mov rbp, rcx
adcx rbp, r10
mov r10, rcx
adcx r10, rax
adcx rcx, rax
adc rax, 0x0
add byte [ rsp + 0x50 ], 0xFF
adcx r12, [ rsp + 0x80 ]
adox r8, [ rsp + 0x60 ]
adox rdi, [ rsp + 0x48 ]
adcx r11, r13
adcx rbx, r14
adcx r9, [ rsp + 0x90 ]
movzx r8, byte [ rsp + 0x100 ]
adcx r8, r15
setc r13b
clc
adcx rdi, [ rsp + 0x40 ]
adox r12, [ rsp + 0x108 ]
adcx r12, [ rsp + 0x30 ]
adox rbp, r11
adox r10, rbx
adcx rbp, [ rsp + 0x38 ]
adox rcx, r9
adox rax, r8
adcx r10, [ rsp + 0xf8 ]
movzx r14, r13b
mov r15, 0x0 
adox r14, r15
adcx rcx, [ rsp + 0xf0 ]
adcx rax, [ rsp + 0xe0 ]
mov r11, 0x100000001 
mov rdx, r11
mulx rbx, r11, rdi
mov rbx, 0xffffffff00000000 
mov rdx, r11
mulx r9, r11, rbx
mov r13, 0xffffffff 
mulx r15, r8, r13
adcx r14, [ rsp + 0xc0 ]
mov r13, -0x2 
inc r13
adox r8, rdi
setc r8b
clc
adcx r11, r15
adox r11, r12
mov rdi, 0xfffffffffffffffe 
mulx r15, r12, rdi
adcx r12, r9
mov r9, 0xffffffffffffffff 
mulx rdi, r13, r9
mov rdx, r13
adcx rdx, r15
mov r15, r13
adcx r15, rdi
adox r12, rbp
adox rdx, r10
adcx r13, rdi
mov rbp, 0x0 
adcx rdi, rbp
adox r15, rcx
adox r13, rax
clc
adcx r11, [ rsp - 0x38 ]
adcx r12, [ rsp - 0x18 ]
adox rdi, r14
movzx r10, r8b
adox r10, rbp
mov rcx, 0x100000001 
xchg rdx, rcx
mulx r8, rax, r11
adcx rcx, [ rsp - 0x8 ]
mov r8, 0xffffffff 
mov rdx, rax
mulx r14, rax, r8
adcx r15, [ rsp - 0x10 ]
adcx r13, [ rsp + 0x0 ]
adcx rdi, [ rsp + 0x18 ]
adcx r10, [ rsp + 0x20 ]
mulx r9, rbp, rbx
mov r8, -0x2 
inc r8
adox rax, r11
setc al
clc
adcx rbp, r14
adox rbp, r12
mov r11, 0xfffffffffffffffe 
mulx r14, r12, r11
adcx r12, r9
mov r9, 0xffffffffffffffff 
mulx r11, r8, r9
mov rdx, r8
adcx rdx, r14
adox r12, rcx
adox rdx, r15
mov rcx, r8
adcx rcx, r11
adcx r8, r11
mov r15, 0x0 
adcx r11, r15
adox rcx, r13
adox r8, rdi
adox r11, r10
clc
adcx rbp, [ rsp + 0x28 ]
adcx r12, [ rsp + 0x78 ]
movzx r13, al
adox r13, r15
mov rdi, 0x100000001 
xchg rdx, rdi
mulx r10, rax, rbp
adcx rdi, [ rsp + 0x70 ]
adcx rcx, [ rsp + 0xd8 ]
adcx r8, [ rsp + 0xd0 ]
adcx r11, [ rsp + 0xc8 ]
mov r10, 0xffffffff 
mov rdx, rax
mulx r14, rax, r10
mov r9, -0x3 
inc r9
adox rax, rbp
adcx r13, [ rsp + 0xe8 ]
mulx rbp, rax, rbx
mov r15, 0xfffffffffffffffe 
mulx r10, r9, r15
setc r15b
clc
adcx rax, r14
adcx r9, rbp
adox rax, r12
mov r12, 0xffffffffffffffff 
mulx rbp, r14, r12
mov rdx, r14
adcx rdx, r10
mov r10, r14
adcx r10, rbp
adox r9, rdi
adox rdx, rcx
adcx r14, rbp
adox r10, r8
mov rdi, 0x0 
adcx rbp, rdi
clc
adcx rax, [ rsp - 0x48 ]
mov rcx, 0x100000001 
xchg rdx, rcx
mulx rdi, r8, rax
adcx r9, [ rsp + 0x88 ]
mov rdx, r8
mulx r8, rdi, rbx
adcx rcx, [ rsp + 0x98 ]
adox r14, r11
adcx r10, [ rsp + 0xa0 ]
adox rbp, r13
movzx r11, r15b
mov r13, 0x0 
adox r11, r13
adcx r14, [ rsp + 0xb0 ]
adcx rbp, [ rsp + 0xa8 ]
mov r15, 0xffffffff 
mulx r12, r13, r15
mov r15, -0x2 
inc r15
adox rdi, r12
adcx r11, [ rsp + 0xb8 ]
setc r12b
clc
adcx r13, rax
mov r13, 0xfffffffffffffffe 
mulx r15, rax, r13
adcx rdi, r9
adox rax, r8
adcx rax, rcx
mov r9, 0xffffffffffffffff 
mulx rcx, r8, r9
mov rdx, r8
adox rdx, r15
mov r15, r8
adox r15, rcx
adox r8, rcx
adcx rdx, r10
adcx r15, r14
adcx r8, rbp
mov r10, 0x0 
adox rcx, r10
adcx rcx, r11
movzx r14, r12b
adc r14, 0x0
mov rbp, rdi
mov r12, 0xffffffff 
sub rbp, r12
mov r11, rax
sbb r11, rbx
mov r10, rdx
sbb r10, r13
mov r13, r15
sbb r13, r9
mov r12, r8
sbb r12, r9
mov rbx, rcx
sbb rbx, r9
sbb r14, 0x00000000
cmovc rbx, rcx
cmovc r11, rax
cmovc r13, r15
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x28 ], rbx
cmovc rbp, rdi
mov [ r14 + 0x0 ], rbp
cmovc r10, rdx
mov [ r14 + 0x10 ], r10
cmovc r12, r8
mov [ r14 + 0x20 ], r12
mov [ r14 + 0x8 ], r11
mov [ r14 + 0x18 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 400
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.5281
; seed 2854374970830574 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4437610 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=52, initial num_batches=31): 121285 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.027331153481265816
; number reverted permutation / tried permutation: 75285 / 90122 =83.537%
; number reverted decision / tried decision: 64594 / 89877 =71.869%
; validated in 39.433s
