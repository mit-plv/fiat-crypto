SECTION .text
	GLOBAL fiat_p521_carry_mul
fiat_p521_carry_mul:
sub rsp, 824
mov rax, rdx
mov rdx, [ rdx + 0x20 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rax + 0x38 ]
lea rcx, [rdx + rdx]
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, [ rax + 0x8 ]
mov rdx, 0x1 
mov [ rsp - 0x80 ], rbx
shlx rbx, [ rax + 0x28 ], rdx
mov [ rsp - 0x78 ], rbp
shlx rbp, [ rax + 0x18 ], rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x20 ]
mov rdx, rbp
mov [ rsp - 0x60 ], r14
mulx r14, rbp, [ rsi + 0x30 ]
mov [ rsp - 0x58 ], r15
mov r15, rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r11
mulx r11, rdi, [ rsi + 0x0 ]
mov rdx, 0x1 
mov [ rsp - 0x40 ], r11
shlx r11, [ rax + 0x10 ], rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x38 ], rdi
mov [ rsp - 0x30 ], r10
mulx r10, rdi, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x28 ], r10
mov [ rsp - 0x20 ], rdi
mulx rdi, r10, [ rsi + 0x30 ]
mov rdx, [ rax + 0x40 ]
mov [ rsp - 0x18 ], rdi
lea rdi, [rdx + rdx]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x10 ], r10
mov [ rsp - 0x8 ], r9
mulx r9, r10, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x0 ], r9
mov [ rsp + 0x8 ], r10
mulx r10, r9, rcx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x10 ], r8
mov [ rsp + 0x18 ], r13
mulx r13, r8, [ rax + 0x10 ]
mov rdx, rdi
mov [ rsp + 0x20 ], r13
mulx r13, rdi, [ rsi + 0x40 ]
mov [ rsp + 0x28 ], r8
mov r8, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x30 ], r12
mov [ rsp + 0x38 ], r10
mulx r10, r12, rcx
mov rdx, rcx
mov [ rsp + 0x40 ], r10
mulx r10, rcx, [ rsi + 0x40 ]
mov [ rsp + 0x48 ], r10
mov r10, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x50 ], rcx
mov [ rsp + 0x58 ], r12
mulx r12, rcx, r8
mov rdx, r8
mov [ rsp + 0x60 ], r12
mulx r12, r8, [ rsi + 0x10 ]
mov [ rsp + 0x68 ], rcx
mov rcx, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x70 ], r9
mov [ rsp + 0x78 ], r12
mulx r12, r9, r10
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x80 ], r12
mov [ rsp + 0x88 ], r9
mulx r9, r12, r11
mov rdx, r11
mov [ rsp + 0x90 ], r8
mulx r8, r11, [ rsi + 0x38 ]
mov rdx, 0x1 
mov [ rsp + 0x98 ], r14
shlx r14, [ rax + 0x30 ], rdx
mov rdx, r14
mov [ rsp + 0xa0 ], rbp
mulx rbp, r14, [ rsi + 0x28 ]
mov [ rsp + 0xa8 ], r8
mov r8, 0x1 
mov [ rsp + 0xb0 ], r11
shlx r11, [ rax + 0x20 ], r8
mov r8, [ rax + 0x8 ]
mov [ rsp + 0xb8 ], rbp
mov rbp, r8
shl rbp, 0x1
mov r8, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0xc0 ], rbp
mov [ rsp + 0xc8 ], r14
mulx r14, rbp, r11
mov rdx, r8
mov [ rsp + 0xd0 ], r14
mulx r14, r8, [ rsi + 0x30 ]
mov [ rsp + 0xd8 ], r14
mov r14, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xe0 ], r8
mov [ rsp + 0xe8 ], rbp
mulx rbp, r8, r11
mov rdx, r14
mov [ rsp + 0xf0 ], rbp
mulx rbp, r14, [ rsi + 0x18 ]
mov [ rsp + 0xf8 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x100 ], r14
mov [ rsp + 0x108 ], r8
mulx r8, r14, [ rax + 0x0 ]
test al, al
adox rdi, r14
adox r8, r13
mov rdx, [ rsi + 0x38 ]
mulx r14, r13, r11
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x110 ], r8
mov [ rsp + 0x118 ], rdi
mulx rdi, r8, r15
adcx r8, r13
adcx r14, rdi
mov rdx, [ rsi + 0x18 ]
mulx rdi, r13, [ rax + 0x28 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x120 ], rdi
mov [ rsp + 0x128 ], r13
mulx r13, rdi, rbx
test al, al
adox r8, rdi
adox r13, r14
mov rdx, r15
mulx r14, r15, [ rsi + 0x38 ]
adcx r12, r15
adcx r14, r9
test al, al
adox r8, [ rsp + 0xc8 ]
adox r13, [ rsp + 0xb8 ]
mov rdx, [ rsi + 0x28 ]
mulx rdi, r9, rbx
mov rdx, r11
mulx r15, r11, [ rsi + 0x30 ]
adcx r12, r11
adcx r15, r14
xor rdx, rdx
adox r12, r9
adox rdi, r15
mov rdx, [ rsi + 0x20 ]
mulx r9, r14, rbp
mov rdx, r10
mulx r11, r10, [ rsi + 0x18 ]
mov r15, rdx
mov rdx, [ rsp + 0xc0 ]
mov [ rsp + 0x130 ], r13
mov [ rsp + 0x138 ], r8
mulx r8, r13, [ rsi + 0x40 ]
adcx r13, [ rsp + 0xb0 ]
adcx r8, [ rsp + 0xa8 ]
test al, al
adox r12, r14
adox r9, rdi
mov rdx, [ rsi + 0x38 ]
mulx r14, rdi, rbx
adcx r12, r10
adcx r11, r9
xor rdx, rdx
adox r13, [ rsp + 0xa0 ]
adox r8, [ rsp + 0x98 ]
mov r10, rdi
adcx r10, [ rsp + 0xe8 ]
adcx r14, [ rsp + 0xd0 ]
mov rdx, [ rsi + 0x20 ]
mulx rdi, r9, rbx
xor rdx, rdx
adox r12, [ rsp + 0x90 ]
adox r11, [ rsp + 0x78 ]
mov rdx, rcx
mov [ rsp + 0x140 ], r11
mulx r11, rcx, [ rsi + 0x8 ]
adcx r13, [ rsp + 0x108 ]
adcx r8, [ rsp + 0xf0 ]
add r13, r9
adcx rdi, r8
test al, al
adox r13, [ rsp + 0x100 ]
adox rdi, [ rsp + 0xf8 ]
adcx r13, [ rsp + 0x70 ]
adcx rdi, [ rsp + 0x38 ]
xor r9, r9
adox r13, rcx
adox r11, rdi
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mulx rdi, r8, [ rax + 0x0 ]
adcx r13, r8
adcx rdi, r11
xor rdx, rdx
adox r10, [ rsp + 0xe0 ]
adox r14, [ rsp + 0xd8 ]
mov rdx, r15
mulx r15, r9, [ rsi + 0x28 ]
adcx r10, r9
adcx r15, r14
mov r11, rdx
mov rdx, [ rsi + 0x18 ]
mulx r14, r8, [ rax + 0x0 ]
mov rdx, rbp
mulx r9, rbp, [ rsi + 0x38 ]
mov [ rsp + 0x148 ], rdi
mov rdi, [ rsp + 0x138 ]
add rdi, [ rsp + 0x58 ]
mov [ rsp + 0x150 ], r13
mov r13, [ rsp + 0x130 ]
adcx r13, [ rsp + 0x40 ]
test al, al
adox r10, [ rsp + 0x68 ]
adox r15, [ rsp + 0x60 ]
mov [ rsp + 0x158 ], r13
mov r13, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x160 ], rdi
mov [ rsp + 0x168 ], r9
mulx r9, rdi, [ rsi + 0x8 ]
adcx r10, r8
adcx r14, r15
mov rdx, [ rsi + 0x40 ]
mulx r15, r8, rbx
xor rdx, rdx
adox r12, rdi
adox r9, [ rsp + 0x140 ]
mov rdx, [ rax + 0x8 ]
mulx rdi, rbx, [ rsi + 0x0 ]
adcx r12, rbx
adcx rdi, r9
xor rdx, rdx
adox r8, rbp
adox r15, [ rsp + 0x168 ]
mov rdx, rcx
mulx rbp, rcx, [ rsi + 0x28 ]
adcx r8, [ rsp + 0x88 ]
adcx r15, [ rsp + 0x80 ]
mov r9, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x170 ], r14
mulx r14, rbx, [ rax + 0x10 ]
add r8, rcx
adcx rbp, r15
xor rdx, rdx
adox r8, [ rsp + 0x30 ]
adox rbp, [ rsp + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mulx r15, rcx, [ rax + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x178 ], r10
mov [ rsp + 0x180 ], r15
mulx r15, r10, r9
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x188 ], rcx
mov [ rsp + 0x190 ], r14
mulx r14, rcx, r11
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x198 ], r14
mulx r14, r11, [ rsi + 0x10 ]
mov rdx, r10
adcx rdx, [ rsp + 0x160 ]
adcx r15, [ rsp + 0x158 ]
add rdx, r11
adcx r14, r15
add rdx, [ rsp + 0x10 ]
adcx r14, [ rsp - 0x8 ]
mov r10, rdx
mov rdx, [ rax + 0x10 ]
mulx r15, r11, [ rsi + 0x10 ]
mov rdx, r9
mov [ rsp + 0x1a0 ], rcx
mulx rcx, r9, [ rsi + 0x30 ]
mov [ rsp + 0x1a8 ], rcx
mov [ rsp + 0x1b0 ], r9
mulx r9, rcx, [ rsi + 0x38 ]
mov rdx, [ rsp + 0x148 ]
mov [ rsp + 0x1b8 ], r9
mov r9, [ rsp + 0x150 ]
shrd r9, rdx, 58
shr rdx, 58
test al, al
adox r12, r9
adox rdx, rdi
mov rdi, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x1c0 ], rcx
mulx rcx, r9, [ rax + 0x18 ]
mov rdx, r12
shrd rdx, rdi, 58
shr rdi, 58
add r8, [ rsp + 0x8 ]
adcx rbp, [ rsp + 0x0 ]
mov [ rsp + 0x1c8 ], rdi
mov rdi, 0x3ffffffffffffff 
and r12, rdi
adox r10, rbx
adox r14, [ rsp + 0x190 ]
adcx r8, r11
adcx r15, rbp
xor rbx, rbx
adox r8, r9
adox rcx, r15
adcx r10, rdx
adcx r14, [ rsp + 0x1c8 ]
mov rdx, [ rsi + 0x40 ]
mulx r9, r11, r13
mov rdx, [ rsi + 0x0 ]
mulx rbp, r13, [ rax + 0x18 ]
mov rdx, [ rsp + 0x178 ]
xor r15, r15
adox rdx, [ rsp + 0x188 ]
mov rbx, [ rsp + 0x170 ]
adox rbx, [ rsp + 0x180 ]
mov r15, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x1d0 ], r12
mulx r12, rdi, [ rsi + 0x40 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x1d8 ], r14
mov [ rsp + 0x1e0 ], r10
mulx r10, r14, [ rsi + 0x28 ]
adcx r11, [ rsp + 0x1a0 ]
adcx r9, [ rsp + 0x198 ]
xor rdx, rdx
adox r11, [ rsp + 0x1b0 ]
adox r9, [ rsp + 0x1a8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x1e8 ], r12
mov [ rsp + 0x1f0 ], rdi
mulx rdi, r12, [ rsi + 0x18 ]
adcx r11, r14
adcx r10, r9
add r11, [ rsp - 0x20 ]
adcx r10, [ rsp - 0x28 ]
test al, al
adox r11, r12
adox rdi, r10
adcx r15, [ rsp + 0x28 ]
adcx rbx, [ rsp + 0x20 ]
mov rdx, [ rsp + 0x1c0 ]
mov r14, rdx
test al, al
adox r14, [ rsp + 0x50 ]
mov r9, [ rsp + 0x1b8 ]
adox r9, [ rsp + 0x48 ]
adcx r8, [ rsp - 0x30 ]
adcx rcx, [ rsp - 0x48 ]
mov rdx, [ rsi + 0x8 ]
mulx r10, r12, [ rax + 0x20 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x1f8 ], r10
mov [ rsp + 0x200 ], r12
mulx r12, r10, [ rax + 0x8 ]
test al, al
adox r15, r13
adox rbp, rbx
mov rdx, r10
adcx rdx, [ rsp + 0x1f0 ]
adcx r12, [ rsp + 0x1e8 ]
mov r13, rdx
mov rdx, [ rax + 0x10 ]
mulx r10, rbx, [ rsi + 0x28 ]
mov rdx, [ rsp + 0x1d8 ]
mov [ rsp + 0x208 ], r10
mov r10, [ rsp + 0x1e0 ]
shrd r10, rdx, 58
shr rdx, 58
mov [ rsp + 0x210 ], rbx
xor rbx, rbx
adox r15, r10
adox rdx, rbp
mov rbp, r15
shrd rbp, rdx, 58
shr rdx, 58
mov r10, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x218 ], r12
mulx r12, rbx, [ rax + 0x8 ]
mov rdx, 0x3ffffffffffffff 
and r15, rdx
adox r8, rbp
adox r10, rcx
mov rcx, r8
and rcx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x220 ], r15
mulx r15, rbp, [ rax + 0x20 ]
adox r14, [ rsp - 0x10 ]
adox r9, [ rsp - 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x228 ], r15
mov [ rsp + 0x230 ], rbp
mulx rbp, r15, [ rax + 0x18 ]
adcx r11, r15
adcx rbp, rdi
mov rdx, [ rsi + 0x30 ]
mulx r15, rdi, [ rax + 0x10 ]
xor rdx, rdx
adox r13, rdi
adox r15, [ rsp + 0x218 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x238 ], r12
mulx r12, rdi, [ rax + 0x8 ]
adcx r14, rdi
adcx r12, r9
mov rdx, [ rsi + 0x20 ]
mulx rdi, r9, [ rax + 0x18 ]
add r11, [ rsp + 0x200 ]
adcx rbp, [ rsp + 0x1f8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x240 ], rbp
mov [ rsp + 0x248 ], r11
mulx r11, rbp, [ rax + 0x18 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x250 ], r12
mov [ rsp + 0x258 ], r14
mulx r14, r12, [ rsi + 0x0 ]
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x20 ], rcx
xor rcx, rcx
adox r13, rbp
adox r11, r15
mov r15, rdx
mov rdx, [ rax + 0x10 ]
mulx rcx, rbp, [ rsi + 0x20 ]
mov rdx, rbx
adcx rdx, [ rsp + 0x118 ]
mov r15, [ rsp + 0x110 ]
adcx r15, [ rsp + 0x238 ]
xor rbx, rbx
adox rdx, [ rsp + 0x210 ]
adox r15, [ rsp + 0x208 ]
adcx r13, [ rsp + 0x230 ]
adcx r11, [ rsp + 0x228 ]
mov rbx, rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x260 ], r14
mov [ rsp + 0x268 ], r12
mulx r12, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x270 ], rcx
mov [ rsp + 0x278 ], rbp
mulx rbp, rcx, [ rax + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x280 ], rbp
mov [ rsp + 0x288 ], rcx
mulx rcx, rbp, [ rax + 0x20 ]
xor rdx, rdx
adox r13, [ rsp + 0x128 ]
adox r11, [ rsp + 0x120 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x290 ], rcx
mov [ rsp + 0x298 ], rbp
mulx rbp, rcx, [ rax + 0x28 ]
adcx r13, r14
adcx r12, r11
mov rdx, [ rax + 0x18 ]
mulx r11, r14, [ rsi + 0x18 ]
add rbx, r9
adcx rdi, r15
mov rdx, [ rax + 0x20 ]
mulx r15, r9, [ rsi + 0x18 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x2a0 ], r12
mov [ rsp + 0x2a8 ], r13
mulx r13, r12, [ rsi + 0x8 ]
test al, al
adox rbx, r9
adox r15, rdi
adcx rbx, rcx
adcx rbp, r15
test al, al
adox rbx, r12
adox r13, rbp
mov rdx, [ rax + 0x38 ]
mulx rdi, rcx, [ rsi + 0x0 ]
shrd r8, r10, 58
shr r10, 58
mov rdx, [ rsp + 0x258 ]
test al, al
adox rdx, [ rsp + 0x278 ]
mov r9, [ rsp + 0x250 ]
adox r9, [ rsp + 0x270 ]
mov r12, [ rsp + 0x248 ]
adcx r12, [ rsp + 0x268 ]
mov r15, [ rsp + 0x240 ]
adcx r15, [ rsp + 0x260 ]
add r12, r8
adcx r10, r15
mov rbp, r12
shrd rbp, r10, 58
shr r10, 58
mov r8, rdx
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x2b0 ], r13
mulx r13, r15, [ rsi + 0x8 ]
add r8, r14
adcx r11, r9
add r8, [ rsp + 0x298 ]
adcx r11, [ rsp + 0x290 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r14, [ rax + 0x40 ]
mov rdx, 0x3ffffffffffffff 
and r12, rdx
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x28 ], r12
adox r8, [ rsp + 0x288 ]
adox r11, [ rsp + 0x280 ]
adcx r8, [ rsp - 0x38 ]
adcx r11, [ rsp - 0x40 ]
test al, al
adox r8, rbp
adox r10, r11
mov rbp, r15
adcx rbp, [ rsp + 0x2a8 ]
adcx r13, [ rsp + 0x2a0 ]
mov r15, 0x3ffffffffffffff 
mov r12, r8
and r12, r15
adox rbx, rcx
adox rdi, [ rsp + 0x2b0 ]
mov [ rdx + 0x30 ], r12
shrd r8, r10, 58
shr r10, 58
test al, al
adox rbx, r8
adox r10, rdi
mov rcx, rbx
and rcx, r15
adox rbp, r14
adox r9, r13
shrd rbx, r10, 58
shr r10, 58
test al, al
adox rbp, rbx
adox r10, r9
mov r14, rbp
shrd r14, r10, 57
shr r10, 57
mov r11, 0x39 
bzhi r13, rbp, r11
mov r12, [ rsp + 0x150 ]
and r12, r15
adox r14, r12
mov rdi, 0x0 
adox r10, rdi
mov [ rdx + 0x40 ], r13
mov r8, r14
shrd r8, r10, 58
add r8, [ rsp + 0x1d0 ]
mov r9, r8
and r9, r15
mov [ rdx + 0x8 ], r9
shr r8, 58
mov rbx, [ rsp + 0x1e0 ]
and rbx, r15
and r14, r15
mov [ rdx + 0x38 ], rcx
lea r8, [ r8 + rbx ]
mov rcx, [ rsp + 0x220 ]
mov [ rdx + 0x18 ], rcx
mov [ rdx + 0x10 ], r8
mov [ rdx + 0x0 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 824
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.1868
; seed 2929555993048416 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 7153615 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=71, initial num_batches=31): 145771 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.020377249824040013
; number reverted permutation / tried permutation: 56092 / 90239 =62.159%
; number reverted decision / tried decision: 38680 / 89760 =43.093%
; validated in 4.337s
