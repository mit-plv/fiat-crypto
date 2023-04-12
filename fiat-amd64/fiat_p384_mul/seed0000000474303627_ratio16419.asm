SECTION .text
	GLOBAL fiat_p384_mul
fiat_p384_mul:
sub rsp, 408
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], r13
mov [ rsp - 0x40 ], r10
mulx r10, r13, [ rax + 0x10 ]
xor rdx, rdx
adox r9, r14
adox r15, rbx
mov rdx, [ rsi + 0x10 ]
mulx r14, rbx, [ rax + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x38 ], r15
mov [ rsp - 0x30 ], r9
mulx r9, r15, [ rax + 0x18 ]
adox r15, rdi
adox rbx, r9
adox rbp, r14
mov rdx, 0x0 
adox r12, rdx
mov rdx, [ rax + 0x8 ]
mulx r14, rdi, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x28 ], r12
mulx r12, r9, [ rax + 0x0 ]
adcx rdi, r12
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x20 ], rdi
mulx rdi, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x18 ], r9
mov [ rsp - 0x10 ], rbp
mulx rbp, r9, [ rax + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x8 ], rbx
mov [ rsp + 0x0 ], r15
mulx r15, rbx, [ rsi + 0x18 ]
adcx r9, r14
mov rdx, -0x2 
inc rdx
adox r12, r15
mov rdx, [ rax + 0x10 ]
mulx r15, r14, [ rsi + 0x18 ]
adox r14, rdi
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x8 ], r9
mulx r9, rdi, [ rsi + 0x20 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x10 ], rdi
mov [ rsp + 0x18 ], r14
mulx r14, rdi, [ rsi + 0x20 ]
seto dl
mov [ rsp + 0x20 ], r12
mov r12, -0x2 
inc r12
adox rdi, r9
mov r9b, dl
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x28 ], rdi
mulx rdi, r12, [ rax + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x30 ], rbx
mov [ rsp + 0x38 ], rdi
mulx rdi, rbx, [ rax + 0x10 ]
adox rbx, r14
adox r12, rdi
mov rdx, [ rsi + 0x8 ]
mulx rdi, r14, [ rax + 0x20 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x40 ], r12
mov [ rsp + 0x48 ], rbx
mulx rbx, r12, [ rsi + 0x8 ]
seto dl
mov [ rsp + 0x50 ], r12
mov r12, -0x2 
inc r12
adox rcx, rbx
mov bl, dl
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x58 ], rcx
mulx rcx, r12, [ rax + 0x18 ]
adox r13, r8
adox r12, r10
adox r14, rcx
mov rdx, [ rsi + 0x8 ]
mulx r10, r8, [ rax + 0x28 ]
adox r8, rdi
mov rdx, [ rax + 0x18 ]
mulx rcx, rdi, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x60 ], r8
mov [ rsp + 0x68 ], r14
mulx r14, r8, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x70 ], r12
mov [ rsp + 0x78 ], r13
mulx r13, r12, [ rsi + 0x0 ]
seto dl
mov byte [ rsp + 0x80 ], bl
mov rbx, -0x2 
inc rbx
adox r8, r11
adox r12, r14
movzx r11, dl
lea r11, [ r11 + r10 ]
mov rdx, [ rsi + 0x28 ]
mulx r14, r10, [ rax + 0x20 ]
adcx rdi, rbp
mov rdx, [ rsi + 0x0 ]
mulx rbx, rbp, [ rax + 0x18 ]
adcx r10, rcx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x88 ], r10
mulx r10, rcx, [ rsi + 0x0 ]
adox rbp, r13
adox rcx, rbx
mov rdx, [ rax + 0x28 ]
mulx rbx, r13, [ rsi + 0x28 ]
adcx r13, r14
mov rdx, 0x100000001 
mov [ rsp + 0x90 ], r13
mulx r13, r14, [ rsp - 0x40 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x98 ], rdi
mulx rdi, r13, [ rax + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xa0 ], r11
mov [ rsp + 0xa8 ], rcx
mulx rcx, r11, [ rax + 0x28 ]
adox r11, r10
mov rdx, 0xffffffff 
mov [ rsp + 0xb0 ], r11
mulx r11, r10, r14
mov rdx, 0x0 
adox rcx, rdx
adc rbx, 0x0
mov rdx, 0xffffffff00000000 
mov [ rsp + 0xb8 ], rbx
mov [ rsp + 0xc0 ], rcx
mulx rcx, rbx, r14
add r9b, 0xFF
adcx r15, r13
mov rdx, [ rsi + 0x18 ]
mulx r13, r9, [ rax + 0x28 ]
adox rbx, r11
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0xc8 ], r15
mulx r15, r11, r14
adox r11, rcx
seto cl
mov rdx, -0x2 
inc rdx
adox r10, [ rsp - 0x40 ]
adox rbx, r8
adox r11, r12
mov rdx, [ rax + 0x20 ]
mulx r8, r10, [ rsi + 0x18 ]
adcx r10, rdi
adcx r9, r8
mov rdx, 0x0 
adcx r13, rdx
clc
adcx rbx, [ rsp + 0x50 ]
mov rdx, [ rax + 0x20 ]
mulx rdi, r12, [ rsi + 0x20 ]
adcx r11, [ rsp + 0x58 ]
mov rdx, 0x100000001 
mov [ rsp + 0xd0 ], r13
mulx r13, r8, rbx
seto r13b
movzx rdx, byte [ rsp + 0x80 ]
mov [ rsp + 0xd8 ], r9
mov r9, 0x0 
dec r9
adox rdx, r9
adox r12, [ rsp + 0x38 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xe0 ], r12
mulx r12, r9, [ rax + 0x28 ]
adox r9, rdi
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0xe8 ], r9
mulx r9, rdi, r14
setc r14b
clc
mov rdx, -0x1 
movzx rcx, cl
adcx rcx, rdx
adcx r15, rdi
mov rcx, 0x0 
adox r12, rcx
mov rcx, rdi
adcx rcx, r9
adcx rdi, r9
adc r9, 0x0
add r13b, 0xFF
adcx rbp, r15
adcx rcx, [ rsp + 0xa8 ]
adcx rdi, [ rsp + 0xb0 ]
adcx r9, [ rsp + 0xc0 ]
movzx r14, r14b
adox r14, rdx
adox rbp, [ rsp + 0x78 ]
adox rcx, [ rsp + 0x70 ]
adox rdi, [ rsp + 0x68 ]
mov r13, 0xffffffff00000000 
mov rdx, r13
mulx r14, r13, r8
adox r9, [ rsp + 0x60 ]
seto r15b
movzx r15, r15b
adcx r15, [ rsp + 0xa0 ]
mov rdx, 0xffffffff 
mov [ rsp + 0xf0 ], r12
mov [ rsp + 0xf8 ], r10
mulx r10, r12, r8
mov rdx, -0x2 
inc rdx
adox r13, r10
setc r10b
clc
adcx r12, rbx
adcx r13, r11
mov r12, 0xfffffffffffffffe 
mov rdx, r12
mulx rbx, r12, r8
adox r12, r14
mov r11, 0xffffffffffffffff 
mov rdx, r11
mulx r14, r11, r8
mov r8, r11
adox r8, rbx
mov rbx, r11
adox rbx, r14
adox r11, r14
mov rdx, 0x0 
adox r14, rdx
adcx r12, rbp
adcx r8, rcx
adcx rbx, rdi
adcx r11, r9
adcx r14, r15
movzx rbp, r10b
adc rbp, 0x0
xor rcx, rcx
adox r13, [ rsp - 0x48 ]
adox r12, [ rsp - 0x30 ]
mov rdx, 0x100000001 
mulx r9, rdi, r13
mov r9, 0xffffffff 
mov rdx, rdi
mulx r15, rdi, r9
adox r8, [ rsp - 0x38 ]
adcx rdi, r13
adox rbx, [ rsp + 0x0 ]
adox r11, [ rsp - 0x8 ]
adox r14, [ rsp - 0x10 ]
mov rdi, 0xffffffff00000000 
mulx r13, r10, rdi
adox rbp, [ rsp - 0x28 ]
seto dil
mov r9, -0x3 
inc r9
adox r10, r15
mov r15, 0xfffffffffffffffe 
mulx r9, rcx, r15
adox rcx, r13
adcx r10, r12
adcx rcx, r8
mov r12, 0xffffffffffffffff 
mulx r13, r8, r12
mov rdx, r8
adox rdx, r9
mov r9, r8
adox r9, r13
adox r8, r13
adcx rdx, rbx
mov rbx, 0x0 
adox r13, rbx
adcx r9, r11
adcx r8, r14
adcx r13, rbp
movzx r11, dil
adc r11, 0x0
test al, al
adox r10, [ rsp + 0x30 ]
mov r14, 0x100000001 
xchg rdx, r14
mulx rbp, rdi, r10
mov rbp, 0xffffffff00000000 
mov rdx, rbp
mulx rbx, rbp, rdi
adox rcx, [ rsp + 0x20 ]
adox r14, [ rsp + 0x18 ]
mov rdx, r15
mulx r12, r15, rdi
adox r9, [ rsp + 0xc8 ]
adox r8, [ rsp + 0xf8 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x100 ], r8
mov [ rsp + 0x108 ], r9
mulx r9, r8, rdi
adcx rbp, r9
adcx r15, rbx
adox r13, [ rsp + 0xd8 ]
mov rbx, 0xffffffffffffffff 
mov rdx, rbx
mulx r9, rbx, rdi
adox r11, [ rsp + 0xd0 ]
seto dil
mov rdx, -0x2 
inc rdx
adox r8, r10
adox rbp, rcx
adox r15, r14
mov r8, rbx
adcx r8, r12
adox r8, [ rsp + 0x108 ]
mov r10, rbx
adcx r10, r9
adcx rbx, r9
mov rcx, 0x0 
adcx r9, rcx
clc
adcx rbp, [ rsp + 0x10 ]
adcx r15, [ rsp + 0x28 ]
adcx r8, [ rsp + 0x48 ]
adox r10, [ rsp + 0x100 ]
adox rbx, r13
adox r9, r11
adcx r10, [ rsp + 0x40 ]
adcx rbx, [ rsp + 0xe0 ]
movzx r14, dil
adox r14, rcx
mov r12, 0x100000001 
mov rdx, r12
mulx r13, r12, rbp
mov r13, 0xffffffff 
mov rdx, r12
mulx rdi, r12, r13
mov r11, 0xffffffff00000000 
mulx r13, rcx, r11
adcx r9, [ rsp + 0xe8 ]
mov r11, -0x2 
inc r11
adox r12, rbp
adcx r14, [ rsp + 0xf0 ]
setc r12b
clc
adcx rcx, rdi
mov rbp, 0xfffffffffffffffe 
mulx r11, rdi, rbp
adox rcx, r15
adcx rdi, r13
mov r15, 0xffffffffffffffff 
mulx rbp, r13, r15
adox rdi, r8
mov r8, r13
adcx r8, r11
adox r8, r10
mov r10, r13
adcx r10, rbp
adox r10, rbx
adcx r13, rbp
mov rbx, 0x0 
adcx rbp, rbx
adox r13, r9
clc
adcx rcx, [ rsp - 0x18 ]
adox rbp, r14
adcx rdi, [ rsp - 0x20 ]
mov rdx, 0x100000001 
mulx r14, r9, rcx
mov rdx, r15
mulx r15, r14, r9
adcx r8, [ rsp + 0x8 ]
adcx r10, [ rsp + 0x98 ]
adcx r13, [ rsp + 0x88 ]
movzx r11, r12b
adox r11, rbx
mov r12, 0xffffffff 
mov rdx, r9
mulx rbx, r9, r12
mov r12, -0x2 
inc r12
adox r9, rcx
adcx rbp, [ rsp + 0x90 ]
mov r9, 0xffffffff00000000 
mulx r12, rcx, r9
adcx r11, [ rsp + 0xb8 ]
setc r9b
clc
adcx rcx, rbx
adox rcx, rdi
mov rdi, 0xfffffffffffffffe 
mov [ rsp + 0x110 ], rcx
mulx rcx, rbx, rdi
adcx rbx, r12
adox rbx, r8
mov rdx, r14
adcx rdx, rcx
adox rdx, r10
mov r8, r14
adcx r8, r15
adcx r14, r15
adox r8, r13
adox r14, rbp
mov r10, 0x0 
adcx r15, r10
adox r15, r11
movzx r13, r9b
adox r13, r10
mov rbp, [ rsp + 0x110 ]
mov r12, 0xffffffff 
sub rbp, r12
mov r9, rbx
mov r11, 0xffffffff00000000 
sbb r9, r11
mov rcx, rdx
sbb rcx, rdi
mov r10, r8
mov rdi, 0xffffffffffffffff 
sbb r10, rdi
mov r11, r14
sbb r11, rdi
mov r12, r15
sbb r12, rdi
sbb r13, 0x00000000
cmovc r11, r14
cmovc r9, rbx
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x8 ], r9
cmovc rcx, rdx
cmovc r12, r15
cmovc rbp, [ rsp + 0x110 ]
mov [ r13 + 0x28 ], r12
mov [ r13 + 0x20 ], r11
mov [ r13 + 0x0 ], rbp
cmovc r10, r8
mov [ r13 + 0x10 ], rcx
mov [ r13 + 0x18 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 408
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.6419
; seed 4173925753631124 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 6374072 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=87, initial num_batches=31): 192574 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.030212084206140126
; number reverted permutation / tried permutation: 73937 / 89949 =82.199%
; number reverted decision / tried decision: 64916 / 90050 =72.089%
; validated in 57.587s
