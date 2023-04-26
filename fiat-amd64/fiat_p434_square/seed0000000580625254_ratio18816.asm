SECTION .text
	GLOBAL fiat_p434_square
fiat_p434_square:
sub rsp, 656
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x30 ]
mulx r9, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x30 ]
test al, al
adox rax, r13
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
adcx r13, rbp
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x48 ], rax
mulx rax, rbp, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x40 ], r12
mov [ rsp - 0x38 ], r13
mulx r13, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x30 ], rbx
mov [ rsp - 0x28 ], rax
mulx rax, rbx, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x20 ], rbp
mov [ rsp - 0x18 ], rcx
mulx rcx, rbp, rbx
adcx r11, r14
mov r14, rbp
setc dl
clc
adcx r14, rcx
mov [ rsp - 0x10 ], r11
mov r11, rbp
adcx r11, rcx
mov byte [ rsp - 0x8 ], dl
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x0 ], r11
mov [ rsp + 0x8 ], r14
mulx r14, r11, rbx
adox r12, r10
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x10 ], r12
mulx r12, r10, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x18 ], r14
mov [ rsp + 0x20 ], r10
mulx r10, r14, [ rsi + 0x20 ]
adcx r11, rcx
adox r8, r13
adox r14, r9
mov rdx, [ rsi + 0x28 ]
mulx r13, r9, [ rsi + 0x30 ]
adox r9, r10
mov rdx, [ rsi + 0x8 ]
mulx r10, rcx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x28 ], r9
mov [ rsp + 0x30 ], r14
mulx r14, r9, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x38 ], r8
mov [ rsp + 0x40 ], r13
mulx r13, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x48 ], r8
mov [ rsp + 0x50 ], r14
mulx r14, r8, [ rsi + 0x8 ]
setc dl
clc
adcx rcx, r12
seto r12b
mov byte [ rsp + 0x58 ], dl
mov rdx, -0x2 
inc rdx
adox r8, r13
adcx r15, r10
mov rdx, [ rsi + 0x18 ]
mulx r13, r10, rdx
adcx r9, rdi
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x60 ], r8
mulx r8, rdi, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x68 ], r13
mov [ rsp + 0x70 ], r9
mulx r9, r13, [ rsi + 0x10 ]
adox r13, r14
adox r10, r9
mov rdx, [ rsi + 0x0 ]
mulx r9, r14, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x78 ], r10
mov [ rsp + 0x80 ], r13
mulx r13, r10, [ rsi + 0x10 ]
seto dl
mov [ rsp + 0x88 ], r9
mov r9, -0x2 
inc r9
adox rdi, rax
adox r10, r8
adox r14, r13
seto al
inc r9
adox rbp, rbx
adox rdi, [ rsp + 0x8 ]
adox r10, [ rsp + 0x0 ]
adox r11, r14
mov bpl, dl
mov rdx, [ rsi + 0x28 ]
mulx r13, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mulx r9, r14, [ rsi + 0x18 ]
seto dl
mov byte [ rsp + 0x90 ], bpl
movzx rbp, byte [ rsp - 0x8 ]
mov byte [ rsp + 0x98 ], al
mov rax, 0x0 
dec rax
adox rbp, rax
adox r14, [ rsp - 0x18 ]
mov bpl, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xa0 ], r14
mulx r14, rax, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x10 ]
mov byte [ rsp + 0xa8 ], bpl
mov byte [ rsp + 0xb0 ], r12b
mulx r12, rbp, [ rsi + 0x20 ]
adox rbp, r9
adox r8, r12
adox rax, r13
mov rdx, [ rsi + 0x8 ]
mulx r9, r13, [ rsi + 0x20 ]
seto dl
mov r12, -0x2 
inc r12
adox rdi, [ rsp + 0x20 ]
adox rcx, r10
adcx r13, [ rsp + 0x50 ]
movzx r10, dl
lea r10, [ r10 + r14 ]
mov rdx, [ rsi + 0x30 ]
mulx r12, r14, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xb8 ], r10
mov [ rsp + 0xc0 ], rax
mulx rax, r10, [ rsi + 0x28 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0xc8 ], r8
mov [ rsp + 0xd0 ], rbp
mulx rbp, r8, rbx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xd8 ], rcx
mov [ rsp + 0xe0 ], rdi
mulx rdi, rcx, [ rsi + 0x8 ]
adcx r10, r9
adox r15, r11
adcx rcx, rax
seto dl
movzx r11, byte [ rsp + 0xb0 ]
mov r9, 0x0 
dec r9
adox r11, r9
adox r14, [ rsp + 0x40 ]
mov r11, 0x0 
adcx rdi, r11
mov al, dl
mov rdx, [ rsi + 0x0 ]
mulx r9, r11, [ rsi + 0x28 ]
mov rdx, 0x0 
adox r12, rdx
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0xe8 ], r12
mov [ rsp + 0xf0 ], r14
mulx r14, r12, rbx
add byte [ rsp + 0x58 ], 0xFF
adcx r12, [ rsp + 0x18 ]
adcx r8, r14
mov r14, 0x2341f27177344 
mov rdx, r14
mov [ rsp + 0xf8 ], r15
mulx r15, r14, rbx
adcx r14, rbp
adc r15, 0x0
mov rdx, [ rsi + 0x20 ]
mulx rbp, rbx, [ rsi + 0x0 ]
add byte [ rsp + 0x98 ], 0x7F
adox rbx, [ rsp + 0x88 ]
adox r11, rbp
movzx rdx, byte [ rsp + 0xa8 ]
mov rbp, -0x1 
adcx rdx, rbp
adcx rbx, r12
adcx r8, r11
mov rdx, [ rsi + 0x30 ]
mulx r11, r12, [ rsi + 0x0 ]
adox r12, r9
mov rdx, 0x0 
adox r11, rdx
adcx r14, r12
dec rdx
movzx rax, al
adox rax, rdx
adox rbx, [ rsp + 0x70 ]
adcx r15, r11
adox r13, r8
adox r10, r14
adox rcx, r15
mov rdx, [ rsi + 0x20 ]
mulx rax, rbp, [ rsi + 0x8 ]
setc dl
movzx rdx, dl
adox rdx, rdi
mov rdi, rdx
mov rdx, [ rsi + 0x28 ]
mulx r8, r9, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mulx r11, r12, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mulx r15, r14, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x100 ], r9
mov [ rsp + 0x108 ], r12
mulx r12, r9, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x110 ], rdi
mov [ rsp + 0x118 ], rcx
mulx rcx, rdi, [ rsi + 0x20 ]
clc
adcx r9, r8
seto dl
mov r8, -0x2 
inc r8
adox rbp, r11
adox rdi, rax
mov al, dl
mov rdx, [ rsi + 0x28 ]
mulx r8, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x120 ], r9
mov [ rsp + 0x128 ], rdi
mulx rdi, r9, [ rsi + 0x18 ]
adox r9, rcx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x130 ], r9
mulx r9, rcx, [ rsi + 0x28 ]
adcx r11, r12
adcx rcx, r8
mov rdx, [ rsi + 0x20 ]
mulx r8, r12, [ rsi + 0x30 ]
adcx r14, r9
adox rdi, [ rsp - 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x138 ], r14
mulx r14, r9, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x140 ], rcx
mov [ rsp + 0x148 ], r11
mulx r11, rcx, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x150 ], rdi
mov [ rsp + 0x158 ], rbp
mulx rbp, rdi, [ rsi + 0x20 ]
adcx r9, r15
adox rdi, [ rsp - 0x28 ]
adcx rcx, r14
mov rdx, 0xffffffffffffffff 
mulx r14, r15, [ rsp + 0xe0 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x160 ], rcx
mov [ rsp + 0x168 ], r9
mulx r9, rcx, [ rsi + 0x18 ]
adox r12, rbp
mov rdx, r15
seto bpl
mov [ rsp + 0x170 ], r12
mov r12, -0x2 
inc r12
adox rdx, r14
movzx r12, bpl
lea r12, [ r12 + r8 ]
mov r8, 0x0 
adcx r11, r8
mov rbp, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x178 ], r11
mulx r11, r8, [ rsi + 0x18 ]
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x180 ], r12
mov [ rsp + 0x188 ], rdi
mulx rdi, r12, [ rsp + 0xe0 ]
mov rdx, r15
clc
adcx rdx, [ rsp + 0xe0 ]
mov rdx, [ rsi + 0x20 ]
mov byte [ rsp + 0x190 ], al
mov [ rsp + 0x198 ], r10
mulx r10, rax, [ rsi + 0x18 ]
adcx rbp, [ rsp + 0xd8 ]
adox r15, r14
adcx r15, [ rsp + 0xf8 ]
adox r12, r14
adcx r12, rbx
setc dl
movzx rbx, byte [ rsp + 0x90 ]
clc
mov r14, -0x1 
adcx rbx, r14
adcx rax, [ rsp + 0x68 ]
adcx r8, r10
mov rbx, 0x7bc65c783158aea3 
mov r10b, dl
mov rdx, [ rsp + 0xe0 ]
mov [ rsp + 0x1a0 ], r8
mulx r8, r14, rbx
adox r14, rdi
adcx rcx, r11
mov r11, 0x6cfc5fd681c52056 
mulx rbx, rdi, r11
adox rdi, r8
mov r8, 0x2341f27177344 
mov [ rsp + 0x1a8 ], rcx
mulx rcx, r11, r8
adox r11, rbx
mov rdx, 0x0 
adox rcx, rdx
adc r9, 0x0
add r10b, 0xFF
adcx r13, r14
adcx rdi, [ rsp + 0x198 ]
adcx r11, [ rsp + 0x118 ]
adcx rcx, [ rsp + 0x110 ]
movzx r10, byte [ rsp + 0x190 ]
adc r10, 0x0
add rbp, [ rsp - 0x30 ]
adcx r15, [ rsp - 0x38 ]
adcx r12, [ rsp - 0x10 ]
adcx r13, [ rsp + 0xa0 ]
adcx rdi, [ rsp + 0xd0 ]
mov r14, 0xffffffffffffffff 
mov rdx, rbp
mulx rbx, rbp, r14
adcx r11, [ rsp + 0xc8 ]
mov r14, rbp
mov r8, -0x2 
inc r8
adox r14, rbx
adcx rcx, [ rsp + 0xc0 ]
mov r8, rbp
adox r8, rbx
adcx r10, [ rsp + 0xb8 ]
mov [ rsp + 0x1b0 ], r9
setc r9b
clc
adcx rbp, rdx
adcx r14, r15
adcx r8, r12
mov rbp, 0xfdc1767ae2ffffff 
mulx r12, r15, rbp
adox r15, rbx
adcx r15, r13
mov r13, 0x7bc65c783158aea3 
mulx rbp, rbx, r13
adox rbx, r12
mov r12, 0x6cfc5fd681c52056 
mov byte [ rsp + 0x1b8 ], r9b
mulx r9, r13, r12
adcx rbx, rdi
mov rdi, 0x2341f27177344 
mov [ rsp + 0x1c0 ], r10
mulx r10, r12, rdi
adox r13, rbp
adox r12, r9
adcx r13, r11
mov rdx, 0x0 
adox r10, rdx
mov r11, -0x3 
inc r11
adox r14, [ rsp + 0x48 ]
mov rbp, 0xffffffffffffffff 
mov rdx, rbp
mulx r9, rbp, r14
adox r8, [ rsp + 0x60 ]
adox r15, [ rsp + 0x80 ]
adox rbx, [ rsp + 0x78 ]
adox rax, r13
adcx r12, rcx
adcx r10, [ rsp + 0x1c0 ]
adox r12, [ rsp + 0x1a0 ]
adox r10, [ rsp + 0x1a8 ]
mov rcx, rbp
seto r13b
inc r11
adox rcx, r9
movzx r11, byte [ rsp + 0x1b8 ]
mov rdx, 0x0 
adcx r11, rdx
mov rdi, rbp
clc
adcx rdi, r14
adcx rcx, r8
mov rdi, 0xfdc1767ae2ffffff 
mov rdx, r14
mulx r8, r14, rdi
adox rbp, r9
adcx rbp, r15
adox r14, r9
mov r9, 0x7bc65c783158aea3 
mulx rdi, r15, r9
adox r15, r8
adcx r14, rbx
adcx r15, rax
mov rbx, 0x6cfc5fd681c52056 
mulx r8, rax, rbx
setc r9b
clc
adcx rcx, [ rsp + 0x108 ]
adcx rbp, [ rsp + 0x158 ]
adcx r14, [ rsp + 0x128 ]
adox rax, rdi
mov rdi, 0x2341f27177344 
mov [ rsp + 0x1c8 ], r11
mulx r11, rbx, rdi
adox rbx, r8
seto dl
mov r8, 0x0 
dec r8
movzx r9, r9b
adox r9, r8
adox r12, rax
adcx r15, [ rsp + 0x130 ]
adox rbx, r10
adcx r12, [ rsp + 0x150 ]
movzx r10, dl
lea r10, [ r10 + r11 ]
mov r9, 0xffffffffffffffff 
mov rdx, rcx
mulx rax, rcx, r9
adcx rbx, [ rsp + 0x188 ]
mov r11, rcx
seto r8b
mov r9, -0x2 
inc r9
adox r11, rax
mov r9, rcx
adox r9, rax
setc dil
clc
adcx rcx, rdx
adcx r11, rbp
adcx r9, r14
mov rcx, 0xfdc1767ae2ffffff 
mulx r14, rbp, rcx
adox rbp, rax
adcx rbp, r15
mov r15, 0x7bc65c783158aea3 
mulx rcx, rax, r15
adox rax, r14
adcx rax, r12
mov r12, 0x6cfc5fd681c52056 
mulx r15, r14, r12
adox r14, rcx
adcx r14, rbx
setc bl
clc
adcx r11, [ rsp + 0x100 ]
adcx r9, [ rsp + 0x120 ]
adcx rbp, [ rsp + 0x148 ]
mov rcx, 0x2341f27177344 
mov byte [ rsp + 0x1d0 ], bl
mulx rbx, r12, rcx
adcx rax, [ rsp + 0x140 ]
adcx r14, [ rsp + 0x138 ]
adox r12, r15
mov rdx, 0x0 
adox rbx, rdx
mov r15, [ rsp + 0x1c8 ]
dec rdx
movzx r13, r13b
adox r13, rdx
adox r15, [ rsp + 0x1b0 ]
setc r13b
clc
movzx r8, r8b
adcx r8, rdx
adcx r15, r10
mov r8, 0xffffffffffffffff 
mov rdx, r8
mulx r10, r8, r11
seto dl
adc dl, 0x0
movzx rdx, dl
add dil, 0xFF
adcx r15, [ rsp + 0x170 ]
mov rdi, r8
adox rdi, r10
mov rcx, r8
adox rcx, r10
mov byte [ rsp + 0x1d8 ], r13b
seto r13b
mov [ rsp + 0x1e0 ], r14
mov r14, -0x2 
inc r14
adox r8, r11
adox rdi, r9
adox rcx, rbp
movzx rdx, dl
movzx r8, dl
adcx r8, [ rsp + 0x180 ]
setc r9b
clc
adcx rdi, [ rsp - 0x40 ]
adcx rcx, [ rsp - 0x48 ]
setc bpl
movzx rdx, byte [ rsp + 0x1d0 ]
clc
adcx rdx, r14
adcx r15, r12
adcx rbx, r8
movzx rdx, r9b
mov r12, 0x0 
adcx rdx, r12
mov r9, 0xfdc1767ae2ffffff 
xchg rdx, r9
mulx r12, r8, r11
clc
movzx r13, r13b
adcx r13, r14
adcx r10, r8
adox r10, rax
mulx r13, rax, rdi
mov r8, 0x7bc65c783158aea3 
mov rdx, r11
mulx r14, r11, r8
adcx r11, r12
adox r11, [ rsp + 0x1e0 ]
mov r12, 0x2341f27177344 
mov [ rsp + 0x1e8 ], r11
mulx r11, r8, r12
mov r12, 0x6cfc5fd681c52056 
mov [ rsp + 0x1f0 ], r10
mov byte [ rsp + 0x1f8 ], bpl
mulx rbp, r10, r12
adcx r10, r14
adcx r8, rbp
setc dl
movzx r14, byte [ rsp + 0x1d8 ]
clc
mov rbp, -0x1 
adcx r14, rbp
adcx r15, [ rsp + 0x168 ]
adox r10, r15
adcx rbx, [ rsp + 0x160 ]
adcx r9, [ rsp + 0x178 ]
adox r8, rbx
movzx r14, dl
lea r14, [ r14 + r11 ]
mov r11, 0xffffffffffffffff 
mov rdx, r11
mulx r15, r11, rdi
adox r14, r9
mov rbx, r11
seto r9b
inc rbp
adox rbx, rdi
movzx rbx, r9b
adcx rbx, rbp
mov r9, r11
clc
adcx r9, r15
mov rdx, rdi
mulx rbp, rdi, r12
adcx r11, r15
adcx rax, r15
adox r9, rcx
mov rcx, 0x7bc65c783158aea3 
mulx r12, r15, rcx
adcx r15, r13
adcx rdi, r12
mov r13, 0x2341f27177344 
mulx rcx, r12, r13
adcx r12, rbp
mov rdx, 0x0 
adcx rcx, rdx
mov rbp, [ rsp + 0x1f0 ]
movzx rdx, byte [ rsp + 0x1f8 ]
clc
mov r13, -0x1 
adcx rdx, r13
adcx rbp, [ rsp + 0x10 ]
adox r11, rbp
mov rdx, [ rsp + 0x38 ]
adcx rdx, [ rsp + 0x1e8 ]
adcx r10, [ rsp + 0x30 ]
adcx r8, [ rsp + 0x28 ]
adcx r14, [ rsp + 0xf0 ]
adox rax, rdx
adox r15, r10
adcx rbx, [ rsp + 0xe8 ]
adox rdi, r8
adox r12, r14
adox rcx, rbx
seto bpl
adc bpl, 0x0
movzx rbp, bpl
mov rdx, r9
mov r10, 0xffffffffffffffff 
sub rdx, r10
mov r8, r11
sbb r8, r10
mov r14, rax
sbb r14, r10
mov rbx, r15
mov r13, 0xfdc1767ae2ffffff 
sbb rbx, r13
mov r13, rdi
mov r10, 0x7bc65c783158aea3 
sbb r13, r10
mov r10, r12
mov [ rsp + 0x200 ], rbx
mov rbx, 0x6cfc5fd681c52056 
sbb r10, rbx
mov rbx, rcx
mov [ rsp + 0x208 ], r8
mov r8, 0x2341f27177344 
sbb rbx, r8
movzx r8, bpl
sbb r8, 0x00000000
cmovc rdx, r9
cmovc r13, rdi
cmovc r14, rax
cmovc r10, r12
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x10 ], r14
mov [ r8 + 0x0 ], rdx
cmovc rbx, rcx
mov [ r8 + 0x28 ], r10
mov [ r8 + 0x30 ], rbx
mov r9, [ rsp + 0x208 ]
cmovc r9, r11
mov [ r8 + 0x8 ], r9
mov r11, [ rsp + 0x200 ]
cmovc r11, r15
mov [ r8 + 0x20 ], r13
mov [ r8 + 0x18 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 656
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.8816
; seed 3377363909098671 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 11010054 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=49, initial num_batches=31): 229767 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.020868834975741265
; number reverted permutation / tried permutation: 76820 / 90369 =85.007%
; number reverted decision / tried decision: 66208 / 89630 =73.868%
; validated in 519.254s
