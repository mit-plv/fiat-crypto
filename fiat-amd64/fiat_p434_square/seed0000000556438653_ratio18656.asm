SECTION .text
	GLOBAL fiat_p434_square
fiat_p434_square:
sub rsp, 712
mov rdx, [ rsi + 0x10 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, r11
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r15
mulx r15, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x40 ], r14
mov [ rsp - 0x38 ], r13
mulx r13, r14, [ rsi + 0x0 ]
test al, al
adox r14, rcx
adox r8, r13
mov rdx, [ rsi + 0x0 ]
mulx r13, rcx, [ rsi + 0x18 ]
adox rcx, r9
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x30 ], rcx
mulx rcx, r9, [ rsi + 0x0 ]
adox r9, r13
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x28 ], r9
mulx r9, r13, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x20 ], r13
mov [ rsp - 0x18 ], r15
mulx r15, r13, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x10 ], r13
mov [ rsp - 0x8 ], r10
mulx r10, r13, [ rsi + 0x8 ]
adcx r12, r15
setc dl
clc
adcx r13, r9
adcx rdi, r10
mov r9b, dl
mov rdx, [ rsi + 0x28 ]
mulx r10, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x0 ], rdi
mov [ rsp + 0x8 ], r13
mulx r13, rdi, [ rsi + 0x10 ]
mov rdx, rbx
mov [ rsp + 0x10 ], r12
setc r12b
clc
adcx rdx, rbp
adox r15, rcx
mov rcx, rbx
adcx rcx, rbp
mov [ rsp + 0x18 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x20 ], r15
mov [ rsp + 0x28 ], r10
mulx r10, r15, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov byte [ rsp + 0x30 ], r9b
mov byte [ rsp + 0x38 ], r12b
mulx r12, r9, [ rsi + 0x10 ]
setc dl
clc
adcx r15, r13
adcx rax, r10
seto r13b
mov r10, -0x2 
inc r10
adox rbx, r11
adox rdi, r14
adox rcx, r8
mov bl, dl
mov rdx, [ rsi + 0x10 ]
mulx r8, r14, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x40 ], rax
mulx rax, r10, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x48 ], r10
mov [ rsp + 0x50 ], r15
mulx r15, r10, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov byte [ rsp + 0x58 ], r13b
mov byte [ rsp + 0x60 ], bl
mulx rbx, r13, [ rsi + 0x18 ]
adcx r10, [ rsp - 0x8 ]
adcx r9, r15
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x68 ], r9
mulx r9, r15, [ rsi + 0x10 ]
adcx r15, r12
adcx r14, r9
mov rdx, [ rsi + 0x30 ]
mulx r9, r12, [ rsi + 0x18 ]
setc dl
mov [ rsp + 0x70 ], r14
movzx r14, byte [ rsp + 0x38 ]
clc
mov [ rsp + 0x78 ], r15
mov r15, -0x1 
adcx r14, r15
adcx r12, [ rsp - 0x18 ]
seto r14b
inc r15
adox r13, rax
movzx rax, dl
lea rax, [ rax + r8 ]
mov rdx, [ rsi + 0x20 ]
mulx r15, r8, [ rsi + 0x30 ]
adcx r8, r9
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x80 ], r8
mulx r8, r9, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x88 ], r12
mov [ rsp + 0x90 ], r13
mulx r13, r12, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x98 ], rax
mov [ rsp + 0xa0 ], r10
mulx r10, rax, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xa8 ], r8
mov byte [ rsp + 0xb0 ], r14b
mulx r14, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xb8 ], r10
mov [ rsp + 0xc0 ], r14
mulx r14, r10, [ rsi + 0x8 ]
adcx r9, r15
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xc8 ], r9
mulx r9, r15, [ rsi + 0x18 ]
adox r15, rbx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xd0 ], r15
mulx r15, rbx, rdx
setc dl
clc
adcx rbx, r13
adcx r10, r15
adcx r8, r14
adox rax, r9
seto r13b
mov r14, -0x2 
inc r14
adox r12, rdi
mov dil, dl
mov rdx, [ rsi + 0x20 ]
mulx r15, r9, [ rsi + 0x10 ]
adox rbx, rcx
mov rdx, 0x6cfc5fd681c52056 
mulx r14, rcx, r11
seto dl
mov [ rsp + 0xd8 ], rax
movzx rax, byte [ rsp + 0x30 ]
mov [ rsp + 0xe0 ], rbx
mov rbx, 0x0 
dec rbx
adox rax, rbx
adox r9, [ rsp - 0x38 ]
adox r15, [ rsp - 0x40 ]
mov al, dl
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xe8 ], r15
mulx r15, rbx, rdx
adox rbx, [ rsp - 0x48 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0xf0 ], rbx
mov [ rsp + 0xf8 ], r9
mulx r9, rbx, r11
mov rdx, 0x2341f27177344 
mov byte [ rsp + 0x100 ], dil
mov [ rsp + 0x108 ], r12
mulx r12, rdi, r11
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x110 ], r8
mov [ rsp + 0x118 ], r10
mulx r10, r8, r11
seto r11b
movzx rdx, byte [ rsp + 0x60 ]
mov byte [ rsp + 0x120 ], al
mov rax, 0x0 
dec rax
adox rdx, rax
adox rbp, r8
mov rdx, [ rsi + 0x8 ]
mulx rax, r8, [ rsi + 0x28 ]
adox rbx, r10
adox rcx, r9
adox rdi, r14
mov rdx, [ rsi + 0x8 ]
mulx r9, r14, [ rsi + 0x20 ]
adcx r14, [ rsp + 0xc0 ]
adcx r8, r9
mov rdx, [ rsi + 0x30 ]
mulx r9, r10, [ rsi + 0x8 ]
adcx r10, rax
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x128 ], r10
mulx r10, rax, [ rsi + 0x30 ]
mov rdx, 0x0 
adox r12, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x130 ], r12
mov [ rsp + 0x138 ], r8
mulx r8, r12, [ rsi + 0x18 ]
adc r9, 0x0
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x140 ], r9
mov [ rsp + 0x148 ], r14
mulx r14, r9, [ rsi + 0x28 ]
add r13b, 0x7F
adox r12, [ rsp + 0xb8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x150 ], r12
mulx r12, r13, [ rsi + 0x18 ]
adox r13, r8
adox rax, r12
mov rdx, [ rsi + 0x28 ]
mulx r12, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x158 ], rax
mov [ rsp + 0x160 ], r13
mulx r13, rax, [ rsi + 0x28 ]
adcx r9, r13
adcx r8, r14
mov rdx, [ rsi + 0x30 ]
mulx r13, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x168 ], r8
mov [ rsp + 0x170 ], r9
mulx r9, r8, [ rsi + 0x28 ]
adcx r8, r12
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x178 ], r8
mulx r8, r12, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x180 ], rax
mov [ rsp + 0x188 ], r9
mulx r9, rax, [ rsi + 0x30 ]
mov rdx, 0x0 
adox r10, rdx
dec rdx
movzx r11, r11b
adox r11, rdx
adox r15, r12
setc r11b
movzx r12, byte [ rsp + 0x58 ]
clc
adcx r12, rdx
adcx r14, [ rsp + 0x28 ]
adox rax, r8
mov r12, 0x0 
adcx r13, r12
adox r9, r12
add byte [ rsp + 0xb0 ], 0xFF
adcx rbp, [ rsp - 0x30 ]
movzx r8, byte [ rsp + 0x120 ]
adox r8, rdx
adox rbp, [ rsp + 0x118 ]
adcx rbx, [ rsp - 0x28 ]
adcx rcx, [ rsp + 0x20 ]
adcx rdi, r14
adox rbx, [ rsp + 0x110 ]
adox rcx, [ rsp + 0x148 ]
mov rdx, [ rsi + 0x28 ]
mulx r14, r8, [ rsi + 0x20 ]
adox rdi, [ rsp + 0x138 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x190 ], r9
mulx r9, r12, rdx
adcx r13, [ rsp + 0x130 ]
adox r13, [ rsp + 0x128 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x198 ], rax
mov [ rsp + 0x1a0 ], r15
mulx r15, rax, rdx
seto dl
mov [ rsp + 0x1a8 ], r10
mov r10, -0x1 
inc r10
mov r10, -0x1 
movzx r11, r11b
adox r11, r10
adox r8, [ rsp + 0x188 ]
adox r12, r14
mov r11b, dl
mov rdx, [ rsi + 0x28 ]
mulx r10, r14, [ rsi + 0x30 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x1b0 ], r10
mov [ rsp + 0x1b8 ], r12
mulx r12, r10, [ rsp + 0x108 ]
adox r14, r9
movzx r11, r11b
movzx r9, r11b
adcx r9, [ rsp + 0x140 ]
mov r11, 0xfdc1767ae2ffffff 
mov rdx, [ rsp + 0x108 ]
mov [ rsp + 0x1c0 ], r14
mov [ rsp + 0x1c8 ], r8
mulx r8, r14, r11
setc r11b
mov [ rsp + 0x1d0 ], r9
movzx r9, byte [ rsp + 0x100 ]
clc
mov [ rsp + 0x1d8 ], r13
mov r13, -0x1 
adcx r9, r13
adcx rax, [ rsp + 0xa8 ]
mov r9, r10
seto r13b
mov [ rsp + 0x1e0 ], rax
mov rax, -0x2 
inc rax
adox r9, r12
mov rax, r10
adox rax, r12
mov byte [ rsp + 0x1e8 ], r13b
setc r13b
clc
adcx r10, rdx
adcx r9, [ rsp + 0xe0 ]
adox r14, r12
adcx rax, rbp
movzx r10, r13b
lea r10, [ r10 + r15 ]
mov rbp, 0x6cfc5fd681c52056 
mulx r12, r15, rbp
mov r13, 0x7bc65c783158aea3 
mov [ rsp + 0x1f0 ], r10
mulx r10, rbp, r13
adox rbp, r8
adox r15, r10
mov r8, 0x2341f27177344 
mulx r13, r10, r8
adox r10, r12
mov rdx, 0x0 
adox r13, rdx
mov r12, -0x3 
inc r12
adox r9, [ rsp + 0x18 ]
adcx r14, rbx
mov rbx, 0xffffffffffffffff 
mov rdx, r9
mulx r12, r9, rbx
adox rax, [ rsp + 0x50 ]
adcx rbp, rcx
adox r14, [ rsp + 0x40 ]
adox rbp, [ rsp + 0xa0 ]
adcx r15, rdi
adox r15, [ rsp + 0x68 ]
adcx r10, [ rsp + 0x1d8 ]
adcx r13, [ rsp + 0x1d0 ]
adox r10, [ rsp + 0x78 ]
adox r13, [ rsp + 0x70 ]
movzx rcx, r11b
mov rdi, 0x0 
adcx rcx, rdi
mov r11, 0xfdc1767ae2ffffff 
mulx rbx, rdi, r11
adox rcx, [ rsp + 0x98 ]
mov r11, r9
clc
adcx r11, r12
mov r8, r9
mov [ rsp + 0x1f8 ], rcx
seto cl
mov [ rsp + 0x200 ], r13
mov r13, -0x2 
inc r13
adox r8, rdx
adcx r9, r12
adcx rdi, r12
adox r11, rax
adox r9, r14
mov r8, 0x7bc65c783158aea3 
mulx rax, r12, r8
mov r14, 0x6cfc5fd681c52056 
mulx r8, r13, r14
adcx r12, rbx
adcx r13, rax
adox rdi, rbp
adox r12, r15
mov rbp, 0x2341f27177344 
mulx rbx, r15, rbp
adox r13, r10
adcx r15, r8
adox r15, [ rsp + 0x200 ]
mov rdx, 0x0 
adcx rbx, rdx
adox rbx, [ rsp + 0x1f8 ]
clc
adcx r11, [ rsp + 0x48 ]
mov r10, 0xffffffffffffffff 
mov rdx, r11
mulx rax, r11, r10
adcx r9, [ rsp + 0x90 ]
adcx rdi, [ rsp + 0xd0 ]
adcx r12, [ rsp + 0xd8 ]
mov r8, r11
seto r10b
mov rbp, -0x2 
inc rbp
adox r8, rax
mov rbp, r11
adox rbp, rax
movzx r14, r10b
movzx rcx, cl
lea r14, [ r14 + rcx ]
mov rcx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x208 ], r14
mulx r14, r10, rcx
adox r10, rax
adcx r13, [ rsp + 0x150 ]
seto al
mov rcx, -0x2 
inc rcx
adox r11, rdx
adox r8, r9
adox rbp, rdi
adox r10, r12
adcx r15, [ rsp + 0x160 ]
adcx rbx, [ rsp + 0x158 ]
mov r11, [ rsp + 0x1a8 ]
adcx r11, [ rsp + 0x208 ]
mov r9, 0x7bc65c783158aea3 
mulx r12, rdi, r9
setc cl
clc
adcx r8, [ rsp - 0x10 ]
adcx rbp, [ rsp + 0x10 ]
adcx r10, [ rsp + 0xf8 ]
setc r9b
clc
mov [ rsp + 0x210 ], r10
mov r10, -0x1 
movzx rax, al
adcx rax, r10
adcx r14, rdi
adox r14, r13
mov rax, 0x6cfc5fd681c52056 
mulx rdi, r13, rax
mov r10, 0x2341f27177344 
mov [ rsp + 0x218 ], rbp
mulx rbp, rax, r10
adcx r13, r12
adox r13, r15
adcx rax, rdi
mov rdx, 0x0 
adcx rbp, rdx
adox rax, rbx
adox rbp, r11
movzx r15, cl
adox r15, rdx
add r9b, 0x7F
adox r14, [ rsp + 0xe8 ]
adox r13, [ rsp + 0xf0 ]
adox rax, [ rsp + 0x1a0 ]
mov rbx, 0xffffffffffffffff 
mov rdx, rbx
mulx rcx, rbx, r8
mov r11, rbx
adcx r11, r8
mov r11, rbx
setc r12b
clc
adcx r11, rcx
adox rbp, [ rsp + 0x198 ]
adox r15, [ rsp + 0x190 ]
adcx rbx, rcx
mov r9, 0xfdc1767ae2ffffff 
mov rdx, r8
mulx rdi, r8, r9
adcx r8, rcx
mov rcx, 0x7bc65c783158aea3 
mulx r10, r9, rcx
mov rcx, 0x6cfc5fd681c52056 
mov [ rsp + 0x220 ], r15
mov [ rsp + 0x228 ], rbp
mulx rbp, r15, rcx
adcx r9, rdi
adcx r15, r10
mov rdi, 0x2341f27177344 
mulx rcx, r10, rdi
adcx r10, rbp
setc dl
clc
mov rbp, -0x1 
movzx r12, r12b
adcx r12, rbp
adcx r11, [ rsp + 0x218 ]
seto r12b
inc rbp
adox r11, [ rsp + 0x180 ]
adcx rbx, [ rsp + 0x210 ]
adox rbx, [ rsp + 0x170 ]
movzx rbp, dl
lea rbp, [ rbp + rcx ]
adcx r8, r14
adox r8, [ rsp + 0x168 ]
adcx r9, r13
adox r9, [ rsp + 0x178 ]
adcx r15, rax
adcx r10, [ rsp + 0x228 ]
adcx rbp, [ rsp + 0x220 ]
movzx r14, r12b
mov r13, 0x0 
adcx r14, r13
adox r15, [ rsp + 0x1c8 ]
adox r10, [ rsp + 0x1b8 ]
adox rbp, [ rsp + 0x1c0 ]
mov rax, 0xffffffffffffffff 
mov rdx, r11
mulx r12, r11, rax
movzx rcx, byte [ rsp + 0x1e8 ]
mov r13, [ rsp + 0x1b0 ]
lea rcx, [ rcx + r13 ]
mov r13, 0xfdc1767ae2ffffff 
mulx rdi, rax, r13
mov r13, r11
clc
adcx r13, r12
mov [ rsp + 0x230 ], rbp
mov rbp, r11
adcx rbp, r12
adox rcx, r14
adcx rax, r12
seto r14b
mov r12, -0x2 
inc r12
adox r11, rdx
adox r13, rbx
adox rbp, r8
adox rax, r9
mov r11, 0x6cfc5fd681c52056 
mulx r8, rbx, r11
mov r9, 0x7bc65c783158aea3 
mulx r11, r12, r9
adcx r12, rdi
adox r12, r15
adcx rbx, r11
mov r15, 0x2341f27177344 
mulx r11, rdi, r15
adcx rdi, r8
mov rdx, 0x0 
adcx r11, rdx
adox rbx, r10
adox rdi, [ rsp + 0x230 ]
adox r11, rcx
clc
adcx r13, [ rsp - 0x20 ]
movzx r10, r14b
adox r10, rdx
mov rdx, r13
mulx r14, r13, r9
adcx rbp, [ rsp + 0x8 ]
adcx rax, [ rsp + 0x0 ]
adcx r12, [ rsp + 0x88 ]
adcx rbx, [ rsp + 0x80 ]
adcx rdi, [ rsp + 0xc8 ]
mov rcx, 0xffffffffffffffff 
mulx r15, r8, rcx
mov rcx, r8
mov r9, -0x2 
inc r9
adox rcx, rdx
adcx r11, [ rsp + 0x1e0 ]
adcx r10, [ rsp + 0x1f0 ]
mov rcx, r8
setc r9b
clc
adcx rcx, r15
adox rcx, rbp
adcx r8, r15
adox r8, rax
mov rbp, 0xfdc1767ae2ffffff 
mov [ rsp + 0x238 ], r8
mulx r8, rax, rbp
adcx rax, r15
adox rax, r12
mov r12, 0x6cfc5fd681c52056 
mulx rbp, r15, r12
adcx r13, r8
adcx r15, r14
adox r13, rbx
adox r15, rdi
mov r14, 0x2341f27177344 
mulx rdi, rbx, r14
adcx rbx, rbp
adox rbx, r11
mov rdx, 0x0 
adcx rdi, rdx
adox rdi, r10
movzx r11, r9b
adox r11, rdx
mov r9, rcx
mov r10, 0xffffffffffffffff 
sub r9, r10
mov r8, [ rsp + 0x238 ]
sbb r8, r10
mov rbp, rax
sbb rbp, r10
mov rdx, r13
mov r10, 0xfdc1767ae2ffffff 
sbb rdx, r10
mov r10, r15
mov r14, 0x7bc65c783158aea3 
sbb r10, r14
mov r14, rbx
sbb r14, r12
mov r12, rdi
mov [ rsp + 0x240 ], r14
mov r14, 0x2341f27177344 
sbb r12, r14
sbb r11, 0x00000000
cmovc rbp, rax
cmovc r8, [ rsp + 0x238 ]
cmovc r12, rdi
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x30 ], r12
mov [ r11 + 0x10 ], rbp
cmovc r9, rcx
mov [ r11 + 0x0 ], r9
cmovc rdx, r13
mov [ r11 + 0x18 ], rdx
mov [ r11 + 0x8 ], r8
cmovc r10, r15
mov rcx, [ rsp + 0x240 ]
cmovc rcx, rbx
mov [ r11 + 0x20 ], r10
mov [ r11 + 0x28 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 712
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.8656
; seed 1724158190536551 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 10706395 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=49, initial num_batches=31): 226027 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.021111401176586518
; number reverted permutation / tried permutation: 74671 / 89675 =83.268%
; number reverted decision / tried decision: 66191 / 90324 =73.282%
; validated in 503.199s
