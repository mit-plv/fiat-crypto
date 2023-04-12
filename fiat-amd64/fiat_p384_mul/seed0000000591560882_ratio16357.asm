SECTION .text
	GLOBAL fiat_p384_mul
fiat_p384_mul:
sub rsp, 384
mov rax, rdx
mov rdx, [ rdx + 0x10 ]
mulx r11, r10, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mulx r8, rcx, [ rax + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], r8
mov [ rsp - 0x40 ], rdi
mulx rdi, r8, [ rax + 0x0 ]
xor rdx, rdx
adox r13, rdi
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x38 ], r13
mulx r13, rdi, [ rsi + 0x8 ]
adox rdi, r14
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x30 ], rdi
mulx rdi, r14, [ rax + 0x18 ]
adox r14, r13
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x28 ], r14
mulx r14, r13, [ rsi + 0x8 ]
adox r13, rdi
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x20 ], r13
mulx r13, rdi, [ rax + 0x0 ]
adcx r9, r13
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x18 ], r9
mulx r9, r13, [ rsi + 0x8 ]
adox r13, r14
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x10 ], rdi
mulx rdi, r14, [ rax + 0x10 ]
adcx r14, rbx
adcx rcx, rdi
mov rdx, [ rax + 0x10 ]
mulx rdi, rbx, [ rsi + 0x28 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x8 ], rcx
mov [ rsp + 0x0 ], r14
mulx r14, rcx, [ rsi + 0x28 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x8 ], rcx
mov [ rsp + 0x10 ], r13
mulx r13, rcx, [ rsi + 0x28 ]
setc dl
clc
adcx rbp, r14
adcx rbx, r12
mov r12, 0x0 
adox r9, r12
mov r14b, dl
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x18 ], rbx
mulx rbx, r12, [ rsi + 0x28 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x20 ], rbp
mov [ rsp + 0x28 ], r9
mulx r9, rbp, [ rsi + 0x28 ]
adcx rcx, rdi
adcx rbp, r13
adcx r12, r9
mov rdx, [ rsi + 0x18 ]
mulx r13, rdi, [ rax + 0x0 ]
adc rbx, 0x0
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x30 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
test al, al
adox r9, r13
adox r10, rbx
mov rdx, [ rax + 0x0 ]
mulx rbx, r13, [ rsi + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x38 ], r12
mov [ rsp + 0x40 ], rbp
mulx rbp, r12, [ rsi + 0x18 ]
adox r12, r11
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x48 ], rcx
mulx rcx, r11, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x50 ], r12
mov [ rsp + 0x58 ], r10
mulx r10, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x60 ], r9
mov [ rsp + 0x68 ], rdi
mulx rdi, r9, [ rax + 0x20 ]
adcx r15, rbx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x70 ], r15
mulx r15, rbx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x78 ], r13
mov [ rsp + 0x80 ], r8
mulx r8, r13, [ rsi + 0x20 ]
adox r9, rbp
adcx r12, [ rsp - 0x40 ]
adcx r11, r10
mov rdx, [ rax + 0x28 ]
mulx r10, rbp, [ rsi + 0x18 ]
adox rbp, rdi
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x88 ], rbp
mulx rbp, rdi, [ rsi + 0x10 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x90 ], r9
mov [ rsp + 0x98 ], r11
mulx r11, r9, [ rsi + 0x10 ]
adcx r9, rcx
adcx rdi, r11
mov rdx, 0x100000001 
mulx r11, rcx, rbx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0xa0 ], rdi
mulx rdi, r11, [ rsi + 0x0 ]
mov rdx, 0x0 
adcx rbp, rdx
adox r10, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0xa8 ], r10
mov [ rsp + 0xb0 ], rbp
mulx rbp, r10, [ rsi + 0x0 ]
test al, al
adox r11, r15
adox r10, rdi
mov rdx, 0xffffffff 
mulx rdi, r15, rcx
mov rdx, 0xffffffff00000000 
mov [ rsp + 0xb8 ], r9
mov [ rsp + 0xc0 ], r12
mulx r12, r9, rcx
adcx r9, rdi
setc dil
clc
adcx r15, rbx
adcx r9, r11
mov rdx, [ rsi + 0x0 ]
mulx rbx, r15, [ rax + 0x28 ]
setc dl
clc
mov r11, -0x1 
movzx r14, r14b
adcx r14, r11
adcx r13, [ rsp - 0x48 ]
mov r14b, dl
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0xc8 ], r13
mulx r13, r11, [ rsi + 0x0 ]
adox r11, rbp
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xd0 ], r9
mulx r9, rbp, [ rax + 0x20 ]
adox rbp, r13
adox r15, r9
mov rdx, 0x0 
adox rbx, rdx
mov rdx, [ rsi + 0x20 ]
mulx r9, r13, [ rax + 0x28 ]
adcx r13, r8
adc r9, 0x0
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0xd8 ], r9
mulx r9, r8, rcx
add dil, 0xFF
adcx r12, r8
mov rdi, 0xffffffffffffffff 
mov rdx, rdi
mulx r8, rdi, rcx
mov rcx, rdi
adcx rcx, r9
mov r9, rdi
adcx r9, r8
adcx rdi, r8
adc r8, 0x0
add r14b, 0xFF
adcx r10, r12
adcx rcx, r11
mov r14, [ rsp + 0xd0 ]
adox r14, [ rsp + 0x80 ]
adox r10, [ rsp - 0x38 ]
adcx r9, rbp
adox rcx, [ rsp - 0x30 ]
adox r9, [ rsp - 0x28 ]
adcx rdi, r15
adox rdi, [ rsp - 0x20 ]
mov r11, 0x100000001 
mov rdx, r11
mulx rbp, r11, r14
mov rbp, 0xffffffff 
mov rdx, r11
mulx r15, r11, rbp
adcx r8, rbx
adox r8, [ rsp + 0x10 ]
seto bl
mov r12, -0x2 
inc r12
adox r11, r14
mov r11, 0xffffffff00000000 
mulx r12, r14, r11
movzx rbx, bl
movzx r11, bl
adcx r11, [ rsp + 0x28 ]
setc bl
clc
adcx r14, r15
adox r14, r10
mov r10, 0xfffffffffffffffe 
mulx rbp, r15, r10
adcx r15, r12
mov r12, 0xffffffffffffffff 
mov [ rsp + 0xe0 ], r13
mulx r13, r10, r12
adox r15, rcx
mov rcx, r10
adcx rcx, rbp
adox rcx, r9
mov r9, r10
adcx r9, r13
adox r9, rdi
adcx r10, r13
mov rdi, 0x0 
adcx r13, rdi
clc
adcx r14, [ rsp + 0x78 ]
adcx r15, [ rsp + 0x70 ]
adcx rcx, [ rsp + 0xc0 ]
adox r10, r8
adox r13, r11
adcx r9, [ rsp + 0x98 ]
adcx r10, [ rsp + 0xb8 ]
adcx r13, [ rsp + 0xa0 ]
mov rdx, 0x100000001 
mulx r11, r8, r14
movzx r11, bl
adox r11, rdi
mov rbx, 0xffffffff 
mov rdx, r8
mulx rbp, r8, rbx
adcx r11, [ rsp + 0xb0 ]
mov r12, -0x3 
inc r12
adox r8, r14
mov r8, 0xffffffff00000000 
mulx rdi, r14, r8
setc r12b
clc
adcx r14, rbp
adox r14, r15
mov r15, 0xfffffffffffffffe 
mulx r8, rbp, r15
adcx rbp, rdi
mov rdi, 0xffffffffffffffff 
mulx rbx, r15, rdi
adox rbp, rcx
mov rcx, r15
adcx rcx, r8
adox rcx, r9
mov r9, r15
adcx r9, rbx
adox r9, r10
adcx r15, rbx
mov r10, 0x0 
adcx rbx, r10
adox r15, r13
adox rbx, r11
clc
adcx r14, [ rsp + 0x68 ]
movzx r13, r12b
adox r13, r10
adcx rbp, [ rsp + 0x60 ]
adcx rcx, [ rsp + 0x58 ]
mov rdx, 0x100000001 
mulx r11, r12, r14
mov r11, 0xffffffff00000000 
mov rdx, r12
mulx r8, r12, r11
adcx r9, [ rsp + 0x50 ]
adcx r15, [ rsp + 0x90 ]
mov r10, 0xffffffff 
mulx r11, rdi, r10
mov r10, -0x2 
inc r10
adox rdi, r14
adcx rbx, [ rsp + 0x88 ]
mov rdi, 0xfffffffffffffffe 
mulx r10, r14, rdi
adcx r13, [ rsp + 0xa8 ]
setc dil
clc
adcx r12, r11
adcx r14, r8
adox r12, rbp
mov rbp, 0xffffffffffffffff 
mulx r11, r8, rbp
mov rdx, r8
adcx rdx, r10
mov r10, r8
adcx r10, r11
adcx r8, r11
adox r14, rcx
adox rdx, r9
adox r10, r15
mov rcx, 0x0 
adcx r11, rcx
adox r8, rbx
adox r11, r13
movzx r9, dil
adox r9, rcx
add r12, [ rsp - 0x10 ]
mov r15, 0x100000001 
xchg rdx, r12
mulx rdi, rbx, r15
mov rdi, 0xffffffff 
xchg rdx, rbx
mulx rcx, r13, rdi
adcx r14, [ rsp - 0x18 ]
mov rbp, 0xfffffffffffffffe 
mulx r15, rdi, rbp
adcx r12, [ rsp + 0x0 ]
adcx r10, [ rsp - 0x8 ]
mov rbp, -0x2 
inc rbp
adox r13, rbx
mov r13, 0xffffffffffffffff 
mulx rbp, rbx, r13
adcx r8, [ rsp + 0xc8 ]
mov r13, 0xffffffff00000000 
mov [ rsp + 0xe8 ], r8
mov [ rsp + 0xf0 ], r10
mulx r10, r8, r13
adcx r11, [ rsp + 0xe0 ]
adcx r9, [ rsp + 0xd8 ]
setc dl
clc
adcx r8, rcx
adox r8, r14
adcx rdi, r10
adox rdi, r12
mov rcx, rbx
adcx rcx, r15
mov r14, rbx
adcx r14, rbp
adcx rbx, rbp
adox rcx, [ rsp + 0xf0 ]
mov r15, 0x0 
adcx rbp, r15
adox r14, [ rsp + 0xe8 ]
adox rbx, r11
adox rbp, r9
movzx r12, dl
adox r12, r15
xor r10, r10
adox r8, [ rsp + 0x8 ]
mov r15, 0x100000001 
mov rdx, r15
mulx r11, r15, r8
adox rdi, [ rsp + 0x20 ]
mov rdx, r15
mulx r15, r11, r13
adox rcx, [ rsp + 0x18 ]
adox r14, [ rsp + 0x48 ]
adox rbx, [ rsp + 0x40 ]
adox rbp, [ rsp + 0x38 ]
mov r9, 0xffffffff 
mulx r13, r10, r9
adcx r11, r13
adox r12, [ rsp + 0x30 ]
seto r13b
mov r9, -0x2 
inc r9
adox r10, r8
mov r10, 0xfffffffffffffffe 
mulx r9, r8, r10
adcx r8, r15
adox r11, rdi
mov rdi, 0xffffffffffffffff 
mulx r10, r15, rdi
mov rdx, r15
adcx rdx, r9
mov r9, r15
adcx r9, r10
adcx r15, r10
adox r8, rcx
adox rdx, r14
adox r9, rbx
mov rcx, 0x0 
adcx r10, rcx
adox r15, rbp
adox r10, r12
movzx r14, r13b
adox r14, rcx
mov rbx, r11
mov rbp, 0xffffffff 
sub rbx, rbp
mov r13, r8
mov r12, 0xffffffff00000000 
sbb r13, r12
mov rcx, rdx
mov rdi, 0xfffffffffffffffe 
sbb rcx, rdi
mov rdi, r9
mov r12, 0xffffffffffffffff 
sbb rdi, r12
mov rbp, r15
sbb rbp, r12
mov [ rsp + 0xf8 ], rbp
mov rbp, r10
sbb rbp, r12
sbb r14, 0x00000000
cmovc rbx, r11
cmovc rdi, r9
cmovc rbp, r10
cmovc r13, r8
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x28 ], rbp
cmovc rcx, rdx
mov [ r14 + 0x0 ], rbx
mov r11, [ rsp + 0xf8 ]
cmovc r11, r15
mov [ r14 + 0x20 ], r11
mov [ r14 + 0x8 ], r13
mov [ r14 + 0x10 ], rcx
mov [ r14 + 0x18 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 384
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.6357
; seed 1031044862517270 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4275982 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=46, initial num_batches=31): 121159 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.02833477783582812
; number reverted permutation / tried permutation: 73732 / 89851 =82.060%
; number reverted decision / tried decision: 64487 / 90148 =71.535%
; validated in 42.919s
