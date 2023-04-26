SECTION .text
	GLOBAL fiat_p448_solinas_carry_mul
fiat_p448_solinas_carry_mul:
sub rsp, 744
mov rax, rdx
mov rdx, [ rdx + 0x18 ]
mulx r11, r10, [ rsi + 0x20 ]
mov rdx, [ rax + 0x30 ]
mulx r8, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x20 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x30 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], r8
mov [ rsp - 0x40 ], rcx
mulx rcx, r8, [ rax + 0x18 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x38 ], rcx
mov [ rsp - 0x30 ], r8
mulx r8, rcx, [ rax + 0x38 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], r11
mov [ rsp - 0x20 ], r10
mulx r10, r11, [ rax + 0x30 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x18 ], r10
mov [ rsp - 0x10 ], r11
mulx r11, r10, [ rsi + 0x38 ]
mov rdx, rcx
test al, al
adox rdx, rcx
mov [ rsp - 0x8 ], rbx
mov rbx, r8
adox rbx, r8
mov [ rsp + 0x0 ], r9
mov r9, rdx
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x8 ], rdi
mov [ rsp + 0x10 ], r15
mulx r15, rdi, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x18 ], r11
mov [ rsp + 0x20 ], r10
mulx r10, r11, [ rax + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x28 ], r10
mov [ rsp + 0x30 ], r11
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x38 ], r11
mov [ rsp + 0x40 ], r10
mulx r10, r11, [ rax + 0x38 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x48 ], r15
mov [ rsp + 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x58 ], rdi
mov [ rsp + 0x60 ], r15
mulx r15, rdi, [ rax + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x68 ], r15
mov [ rsp + 0x70 ], rdi
mulx rdi, r15, [ rax + 0x38 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x78 ], r10
mov [ rsp + 0x80 ], r11
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x88 ], r11
mov [ rsp + 0x90 ], r10
mulx r10, r11, [ rax + 0x30 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x98 ], r10
mov [ rsp + 0xa0 ], r11
mulx r11, r10, [ rax + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xa8 ], r11
mov [ rsp + 0xb0 ], r10
mulx r10, r11, [ rax + 0x38 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0xb8 ], rdi
mov [ rsp + 0xc0 ], r15
mulx r15, rdi, [ rsi + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0xc8 ], r15
mov [ rsp + 0xd0 ], rdi
mulx rdi, r15, [ rsi + 0x38 ]
adcx r9, r15
mov rdx, rdi
adcx rdx, rbx
mov rbx, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xd8 ], r12
mov [ rsp + 0xe0 ], rbp
mulx rbp, r12, [ rax + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xe8 ], r10
mov [ rsp + 0xf0 ], r11
mulx r11, r10, [ rax + 0x28 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xf8 ], r11
mov [ rsp + 0x100 ], r10
mulx r10, r11, [ rsi + 0x38 ]
test al, al
adox r9, r12
mov rdx, rbp
adox rdx, rbx
mov rbx, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x108 ], r10
mov [ rsp + 0x110 ], r11
mulx r11, r10, [ rsi + 0x28 ]
adcx r9, r10
mov rdx, r11
adcx rdx, rbx
xor rbx, rbx
adox rcx, r15
adox rdi, r8
mov r8, rdx
mov rdx, [ rsi + 0x18 ]
mulx rbx, r15, [ rax + 0x10 ]
adcx rcx, r12
adcx rbp, rdi
mov rdx, [ rax + 0x8 ]
mulx rdi, r12, [ rsi + 0x38 ]
add rcx, r10
adcx r11, rbp
mov rdx, [ rsi + 0x38 ]
mulx rbp, r10, [ rax + 0x28 ]
mov rdx, r10
mov [ rsp + 0x118 ], rbx
xor rbx, rbx
adox rdx, r13
mov [ rsp + 0x120 ], r15
mov r15, r14
adox r15, rbp
adcx rdx, [ rsp + 0xf0 ]
adcx r15, [ rsp + 0xe8 ]
mov rbx, rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x128 ], r11
mov [ rsp + 0x130 ], rcx
mulx rcx, r11, [ rsi + 0x20 ]
xor rdx, rdx
adox r9, r11
mov [ rsp + 0x138 ], rdi
mov rdi, rcx
adox rdi, r8
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x140 ], rdi
mulx rdi, r8, [ rax + 0x28 ]
mov rdx, rbx
adcx rdx, r10
adcx rbp, r15
mov r10, r8
mov [ rsp + 0x148 ], rbp
xor rbp, rbp
adox r10, [ rsp + 0x110 ]
adox rdi, [ rsp + 0x108 ]
adcx r10, [ rsp + 0xe0 ]
adcx rdi, [ rsp + 0xd8 ]
mov r8, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x150 ], r9
mulx r9, rbp, [ rax + 0x30 ]
xor rdx, rdx
adox r10, [ rsp + 0xc0 ]
adox rdi, [ rsp + 0xb8 ]
adcx rbx, r12
adcx r15, [ rsp + 0x138 ]
mov [ rsp + 0x158 ], rdi
mov rdi, [ rsp + 0x80 ]
mov [ rsp + 0x160 ], r10
mov r10, rdi
test al, al
adox r10, [ rsp + 0x150 ]
mov [ rsp + 0x168 ], r15
mov r15, [ rsp + 0x78 ]
mov [ rsp + 0x170 ], rbx
mov rbx, r15
adox rbx, [ rsp + 0x140 ]
mov [ rsp + 0x178 ], rbx
mov rbx, r11
adcx rbx, [ rsp + 0x130 ]
adcx rcx, [ rsp + 0x128 ]
mov r11, rbp
test al, al
adox r11, [ rsp + 0x50 ]
mov [ rsp + 0x180 ], r10
mov r10, r9
adox r10, [ rsp + 0x48 ]
adcx r8, r13
adcx r14, [ rsp + 0x148 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x188 ], r10
mulx r10, r13, [ rsi + 0x38 ]
xor rdx, rdx
adox r8, [ rsp + 0xf0 ]
adox r14, [ rsp + 0xe8 ]
adcx r8, r12
adcx r14, [ rsp + 0x138 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x190 ], r10
mulx r10, r12, [ rax + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x198 ], r13
mov [ rsp + 0x1a0 ], r11
mulx r11, r13, [ rsi + 0x28 ]
test al, al
adox r8, r12
mov rdx, r10
adox rdx, r14
adcx rbx, rdi
adcx r15, rcx
mov rdi, r12
xor rcx, rcx
adox rdi, [ rsp + 0x170 ]
adox r10, [ rsp + 0x168 ]
adcx rdi, r13
mov r14, r11
adcx r14, r10
mov r12, rdx
mov rdx, [ rax + 0x0 ]
mulx rcx, r10, [ rsi + 0x18 ]
mov rdx, rbp
mov [ rsp + 0x1a8 ], r15
xor r15, r15
adox rdx, [ rsp + 0x1a0 ]
adox r9, [ rsp + 0x188 ]
mov rbp, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x1b0 ], rbx
mulx rbx, r15, [ rax + 0x10 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x1b8 ], rbx
mov [ rsp + 0x1c0 ], r15
mulx r15, rbx, [ rsi + 0x20 ]
adcx rbp, [ rsp + 0x50 ]
adcx r9, [ rsp + 0x48 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x1c8 ], r14
mov [ rsp + 0x1d0 ], rdi
mulx rdi, r14, [ rax + 0x8 ]
xor rdx, rdx
adox rbp, [ rsp + 0x198 ]
adox r9, [ rsp + 0x190 ]
mov [ rsp + 0x1d8 ], r15
mov r15, r10
adcx r15, [ rsp + 0x160 ]
adcx rcx, [ rsp + 0x158 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x1e0 ], rbx
mulx rbx, r10, [ rax + 0x18 ]
xor rdx, rdx
adox r15, r14
adox rdi, rcx
adcx rbp, r10
mov r14, rbx
adcx r14, r9
mov rdx, [ rax + 0x8 ]
mulx rcx, r9, [ rsi + 0x30 ]
test al, al
adox r8, r13
adox r11, r12
mov rdx, [ rsi + 0x18 ]
mulx r12, r13, [ rax + 0x28 ]
mov rdx, [ rsp + 0x160 ]
adcx rdx, [ rsp + 0x20 ]
mov [ rsp + 0x1e8 ], rdi
mov rdi, [ rsp + 0x158 ]
adcx rdi, [ rsp + 0x18 ]
mov [ rsp + 0x1f0 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x1f8 ], r14
mov [ rsp + 0x200 ], rbp
mulx rbp, r14, [ rax + 0x10 ]
test al, al
adox r8, [ rsp + 0x1e0 ]
adox r11, [ rsp + 0x1d8 ]
adcx r8, r13
mov rdx, r12
adcx rdx, r11
add r8, [ rsp + 0xa0 ]
adcx rdx, [ rsp + 0x98 ]
xor r11, r11
adox r15, r9
adox rcx, rdi
adcx r15, r14
adcx rbp, rcx
mov r9, [ rsp + 0x1e0 ]
mov rdi, r9
xor r14, r14
adox rdi, [ rsp + 0x1d0 ]
mov r11, [ rsp + 0x1d8 ]
adox r11, [ rsp + 0x1c8 ]
adcx rdi, r13
adcx r12, r11
test al, al
adox rdi, [ rsp + 0xa0 ]
adox r12, [ rsp + 0x98 ]
mov r9, [ rsp + 0x198 ]
mov r13, r9
adcx r13, [ rsp + 0x1a0 ]
mov rcx, [ rsp + 0x190 ]
adcx rcx, [ rsp + 0x188 ]
mov r9, rdx
mov rdx, [ rax + 0x38 ]
mulx r14, r11, [ rsi + 0x8 ]
xor rdx, rdx
adox r13, r10
adox rbx, rcx
adcx r8, r11
mov r10, r14
adcx r10, r9
xor r9, r9
adox r8, [ rsp + 0x10 ]
adox r10, [ rsp + 0x8 ]
adcx r13, [ rsp + 0x0 ]
adcx rbx, [ rsp - 0x8 ]
test al, al
adox rdi, r11
adox r14, r12
adcx r15, [ rsp - 0x20 ]
adcx rbp, [ rsp - 0x28 ]
xor rdx, rdx
adox r13, [ rsp + 0xb0 ]
adox rbx, [ rsp + 0xa8 ]
mov rdx, [ rax + 0x28 ]
mulx r12, r9, [ rsi + 0x10 ]
adcx r13, [ rsp - 0x10 ]
adcx rbx, [ rsp - 0x18 ]
add r15, [ rsp + 0x60 ]
adcx rbp, [ rsp + 0x58 ]
xor rdx, rdx
adox r15, r9
adox r12, rbp
mov rcx, [ rsp + 0x0 ]
mov r11, rcx
adcx r11, [ rsp + 0x200 ]
mov r9, [ rsp - 0x8 ]
adcx r9, [ rsp + 0x1f8 ]
mov rdx, [ rax + 0x38 ]
mulx rbp, rcx, [ rsi + 0x0 ]
test al, al
adox r11, [ rsp + 0xb0 ]
adox r9, [ rsp + 0xa8 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x208 ], r14
mov [ rsp + 0x210 ], rdi
mulx rdi, r14, [ rsi + 0x10 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x218 ], rdi
mov [ rsp + 0x220 ], r14
mulx r14, rdi, [ rsi + 0x10 ]
adcx r13, rdi
mov rdx, r14
adcx rdx, rbx
test al, al
adox r15, [ rsp - 0x40 ]
adox r12, [ rsp - 0x48 ]
adcx r15, rcx
adcx rbp, r12
mov rbx, rdx
mov rdx, [ rsi + 0x10 ]
mulx r12, rcx, [ rax + 0x10 ]
mov rdx, 0xffffffffffffff 
mov [ rsp + 0x228 ], rbx
mov rbx, r15
and rbx, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x230 ], rbx
mov [ rsp + 0x238 ], r13
mulx r13, rbx, [ rsi + 0x18 ]
adox r11, [ rsp - 0x10 ]
adox r9, [ rsp - 0x18 ]
adcx r8, rbx
adcx r13, r10
mov rdx, [ rsi + 0x20 ]
mulx rbx, r10, [ rax + 0x8 ]
add r11, rdi
adcx r14, r9
mov rdx, [ rsi + 0x28 ]
mulx r9, rdi, [ rax + 0x0 ]
test al, al
adox r11, rdi
adox r9, r14
adcx r8, rcx
adcx r12, r13
mov rdx, [ rsi + 0x10 ]
mulx r13, rcx, [ rax + 0x18 ]
test al, al
adox r11, r10
adox rbx, r9
mov rdx, [ rax + 0x18 ]
mulx r14, r10, [ rsi + 0x8 ]
mov rdx, [ rsp + 0x180 ]
adcx rdx, [ rsp + 0x30 ]
mov rdi, [ rsp + 0x178 ]
adcx rdi, [ rsp + 0x28 ]
xor r9, r9
adox rdx, [ rsp + 0x70 ]
adox rdi, [ rsp + 0x68 ]
mov r9, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x240 ], rdi
mov [ rsp + 0x248 ], r12
mulx r12, rdi, [ rsi + 0x8 ]
adcx r11, [ rsp + 0x120 ]
adcx rbx, [ rsp + 0x118 ]
add r11, rcx
adcx r13, rbx
mov rdx, [ rsi + 0x20 ]
mulx rbx, rcx, [ rax + 0x10 ]
xor rdx, rdx
adox r11, rdi
adox r12, r13
mov rdx, [ rax + 0x18 ]
mulx r13, rdi, [ rsi + 0x0 ]
shrd r15, rbp, 56
mov rdx, [ rsp + 0x1f0 ]
test al, al
adox rdx, [ rsp + 0x1c0 ]
mov rbp, [ rsp + 0x1e8 ]
adox rbp, [ rsp + 0x1b8 ]
adcx rdx, rdi
adcx r13, rbp
test al, al
adox r8, r10
adox r14, [ rsp + 0x248 ]
mov r10, rdx
shrd r10, r13, 56
mov rdi, rdx
mov rdx, [ rax + 0x20 ]
mulx r13, rbp, [ rsi + 0x0 ]
test al, al
adox r8, rbp
adox r13, r14
adcx r9, rcx
adcx rbx, [ rsp + 0x240 ]
xor rdx, rdx
adox r9, [ rsp - 0x30 ]
adox rbx, [ rsp - 0x38 ]
adcx r8, r10
adc r13, 0x0
mov rcx, 0x38 
bzhi r14, rdi, rcx
mov rdx, [ rsi + 0x0 ]
mulx r10, rdi, [ rax + 0x28 ]
adox r9, [ rsp + 0x220 ]
adox rbx, [ rsp + 0x218 ]
mov rdx, r15
test al, al
adox rdx, r8
mov rbp, 0x0 
adox r13, rbp
mov r8, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, rbp, [ rax + 0x30 ]
mov rdx, r8
shrd rdx, r13, 56
mov r13, 0xffffffffffffff 
and r8, r13
adox r11, rdi
adox r10, r12
adcx r11, rdx
adc r10, 0x0
mov r12, r11
shrd r12, r10, 56
and r11, r13
mov rdx, [ rax + 0x0 ]
mulx r10, rdi, [ rsi + 0x10 ]
adox r9, [ rsp + 0x100 ]
adox rbx, [ rsp + 0xf8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x250 ], r11
mulx r11, r13, [ rax + 0x8 ]
mov rdx, [ rsp + 0x90 ]
mov [ rsp + 0x258 ], r8
mov r8, rdx
adcx r8, [ rsp + 0x210 ]
mov [ rsp + 0x260 ], r14
mov r14, [ rsp + 0x88 ]
adcx r14, [ rsp + 0x208 ]
test al, al
adox r9, rbp
adox rcx, rbx
mov rdx, [ rsp + 0x238 ]
adcx rdx, [ rsp + 0x40 ]
mov rbp, [ rsp + 0x228 ]
adcx rbp, [ rsp + 0x38 ]
xor rbx, rbx
adox r9, r12
adox rcx, rbx
adcx rdx, r13
adcx r11, rbp
mov r12, r9
shrd r12, rcx, 56
test al, al
adox r15, r8
adox r14, rbx
add r12, [ rsp + 0x230 ]
mov r13, 0xffffffffffffff 
mov r8, r15
and r8, r13
mov rbp, r12
shr rbp, 56
and r12, r13
lea r8, [ r8 + rbp ]
mov rcx, r8
and rcx, r13
shrd r15, r14, 56
mov r14, rdi
test al, al
adox r14, [ rsp + 0x1b0 ]
adox r10, [ rsp + 0x1a8 ]
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x0 ], rcx
adcx r14, [ rsp + 0xd0 ]
adcx r10, [ rsp + 0xc8 ]
xor rcx, rcx
adox rdx, r15
adox r11, rcx
mov rbx, rdx
shrd rbx, r11, 56
mov r15, rdx
mov rdx, [ rax + 0x10 ]
mulx rcx, r11, [ rsi + 0x0 ]
and r15, r13
adox r14, r11
adox rcx, r10
shr r8, 56
xor rdx, rdx
adox r14, rbx
adox rcx, rdx
mov r10, r14
shrd r10, rcx, 56
add r10, [ rsp + 0x260 ]
mov rbx, r10
shr rbx, 56
add rbp, [ rsp + 0x258 ]
lea r8, [ r8 + r15 ]
mov [ rdi + 0x8 ], r8
lea rbx, [ rbx + rbp ]
mov r11, rbx
and r11, r13
shr rbx, 56
add rbx, [ rsp + 0x250 ]
and r9, r13
mov [ rdi + 0x30 ], r9
mov [ rdi + 0x20 ], r11
and r10, r13
and r14, r13
mov [ rdi + 0x28 ], rbx
mov [ rdi + 0x10 ], r14
mov [ rdi + 0x18 ], r10
mov [ rdi + 0x38 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 744
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.0757
; seed 0436611226766746 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 11264251 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=47, initial num_batches=31): 218080 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.01936036404018341
; number reverted permutation / tried permutation: 49257 / 89851 =54.821%
; number reverted decision / tried decision: 29715 / 90148 =32.962%
; validated in 5.003s
