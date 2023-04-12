SECTION .text
	GLOBAL fiat_p521_carry_mul
fiat_p521_carry_mul:
sub rsp, 904
mov rax, [ rdx + 0x30 ]
mov r10, rax
shl r10, 0x1
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, [ rax + 0x20 ]
mov rdx, [ rax + 0x0 ]
mulx r9, r8, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rax + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rax + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rcx
mulx rcx, rdi, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x40 ], r11
mov [ rsp - 0x38 ], r15
mulx r15, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp - 0x30 ], r14
mov [ rsp - 0x28 ], r9
mulx r9, r14, r10
mov rdx, 0x1 
mov [ rsp - 0x20 ], r8
shlx r8, [ rax + 0x40 ], rdx
mov [ rsp - 0x18 ], r15
shlx r15, [ rax + 0x20 ], rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], r11
mov [ rsp - 0x8 ], rcx
mulx rcx, r11, r8
mov rdx, r15
mov [ rsp + 0x0 ], rdi
mulx rdi, r15, [ rsi + 0x28 ]
xchg rdx, r10
mov [ rsp + 0x8 ], rbp
mov [ rsp + 0x10 ], rbx
mulx rbx, rbp, [ rsi + 0x38 ]
mov [ rsp + 0x18 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x20 ], r12
mov [ rsp + 0x28 ], rbx
mulx rbx, r12, [ rax + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x30 ], rbx
mov [ rsp + 0x38 ], r12
mulx r12, rbx, [ rsi + 0x8 ]
imul rdx, [ rax + 0x10 ], 0x2
mov [ rsp + 0x40 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x48 ], r12
mov [ rsp + 0x50 ], rbx
mulx rbx, r12, r8
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x58 ], rbx
mov [ rsp + 0x60 ], r12
mulx r12, rbx, [ rax + 0x20 ]
mov rdx, rbp
mov [ rsp + 0x68 ], r12
mulx r12, rbp, [ rsi + 0x38 ]
xchg rdx, r8
mov [ rsp + 0x70 ], rbx
mov [ rsp + 0x78 ], rcx
mulx rcx, rbx, [ rsi + 0x8 ]
xchg rdx, r8
mov [ rsp + 0x80 ], r11
mov [ rsp + 0x88 ], rcx
mulx rcx, r11, [ rsi + 0x40 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x90 ], rbx
mov [ rsp + 0x98 ], rdi
mulx rdi, rbx, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xa0 ], rdi
mov [ rsp + 0xa8 ], rbx
mulx rbx, rdi, [ rax + 0x30 ]
mov rdx, r8
mov [ rsp + 0xb0 ], rbx
mulx rbx, r8, [ rsi + 0x30 ]
mov [ rsp + 0xb8 ], rdi
mov rdi, [ rax + 0x28 ]
mov [ rsp + 0xc0 ], rbx
mov rbx, rdi
shl rbx, 0x1
mov rdi, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xc8 ], r8
mov [ rsp + 0xd0 ], r15
mulx r15, r8, rbx
mov rdx, rbx
mov [ rsp + 0xd8 ], r15
mulx r15, rbx, [ rsi + 0x40 ]
mov [ rsp + 0xe0 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xe8 ], rbx
mov [ rsp + 0xf0 ], r8
mulx r8, rbx, rdi
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xf8 ], r8
mov [ rsp + 0x100 ], rbx
mulx rbx, r8, rdi
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x108 ], rbx
mov [ rsp + 0x110 ], r8
mulx r8, rbx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x118 ], r8
mov r8, rdx
shl r8, 0x1
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x120 ], rbx
mov [ rsp + 0x128 ], r12
mulx r12, rbx, [ rax + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x130 ], r12
mov [ rsp + 0x138 ], rbx
mulx rbx, r12, [ rax + 0x38 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x140 ], rbx
mov [ rsp + 0x148 ], r12
mulx r12, rbx, r8
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x150 ], rbp
mov [ rsp + 0x158 ], rcx
mulx rcx, rbp, r8
add r14, rbx
adcx r12, r9
mov rdx, [ rax + 0x8 ]
mulx rbx, r9, [ rsi + 0x30 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x160 ], rbx
lea rbx, [rdx + rdx]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x168 ], r9
mov [ rsp + 0x170 ], r12
mulx r12, r9, rbx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x178 ], r14
mov [ rsp + 0x180 ], r12
mulx r12, r14, rbx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x188 ], r9
mov [ rsp + 0x190 ], rcx
mulx rcx, r9, rbx
test al, al
adox r11, r9
adox rcx, [ rsp + 0x158 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, rbx, r13
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x198 ], rcx
mov rcx, rdx
shl rcx, 0x1
mov rdx, rcx
mov [ rsp + 0x1a0 ], r11
mulx r11, rcx, [ rsi + 0x40 ]
xor rdx, rdx
adox rcx, [ rsp + 0x150 ]
adox r11, [ rsp + 0x128 ]
mov rdx, r10
mov [ rsp + 0x1a8 ], r9
mulx r9, r10, [ rsi + 0x38 ]
xchg rdx, r13
mov [ rsp + 0x1b0 ], rbx
mov [ rsp + 0x1b8 ], r9
mulx r9, rbx, [ rsi + 0x30 ]
adcx rcx, r14
adcx r12, r11
mov r14, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x1c0 ], r9
mulx r9, r11, r15
xor rdx, rdx
adox rbp, [ rsp + 0x110 ]
mov [ rsp + 0x1c8 ], rbx
mov rbx, [ rsp + 0x190 ]
adox rbx, [ rsp + 0x108 ]
mov [ rsp + 0x1d0 ], rbx
mov rbx, r10
adcx rbx, [ rsp + 0x188 ]
mov [ rsp + 0x1d8 ], rbp
mov rbp, [ rsp + 0x180 ]
adcx rbp, [ rsp + 0x1b8 ]
test al, al
adox rbx, r11
adox r9, rbp
mov rdx, [ rsi + 0x20 ]
mulx r11, r10, r15
adcx rcx, [ rsp + 0xd0 ]
adcx r12, [ rsp + 0x98 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x1e0 ], r9
mulx r9, rbp, r8
xor rdx, rdx
adox rcx, r10
adox r11, r12
adcx rcx, [ rsp + 0x1b0 ]
adcx r11, [ rsp + 0x1a8 ]
mov rdx, [ rsi + 0x40 ]
mulx r12, r10, rdi
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x1e8 ], r12
mov [ rsp + 0x1f0 ], r10
mulx r10, r12, r13
add rcx, rbp
adcx r9, r11
mov rdx, r12
xor rbp, rbp
adox rdx, [ rsp + 0x1a0 ]
adox r10, [ rsp + 0x198 ]
xchg rdx, r14
mulx r12, r11, [ rsi + 0x20 ]
adcx r14, [ rsp + 0xf0 ]
adcx r10, [ rsp + 0xd8 ]
mov rbp, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1f8 ], rbx
mov [ rsp + 0x200 ], r9
mulx r9, rbx, r8
xor rdx, rdx
adox r14, r11
adox r12, r10
mov rdx, rdi
mulx r11, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x208 ], r11
mulx r11, r10, r13
mov rdx, rbp
mulx r13, rbp, [ rsi + 0x28 ]
adcx r14, rbx
adcx r9, r12
mov rdx, r15
mulx rbx, r15, [ rsi + 0x38 ]
test al, al
adox r10, r15
adox rbx, r11
adcx r10, [ rsp + 0x1c8 ]
adcx rbx, [ rsp + 0x1c0 ]
xor rdx, rdx
adox rcx, [ rsp + 0x90 ]
mov r12, [ rsp + 0x200 ]
adox r12, [ rsp + 0x88 ]
mov rdx, [ rax + 0x0 ]
mulx r15, r11, [ rsi + 0x0 ]
adcx rcx, r11
adcx r15, r12
mov rdx, [ rsi + 0x0 ]
mulx r11, r12, [ rax + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x210 ], r15
mov [ rsp + 0x218 ], rcx
mulx rcx, r15, r8
test al, al
adox r14, rdi
adox r9, [ rsp + 0x208 ]
mov rdx, rbp
adcx rdx, [ rsp + 0x1f8 ]
adcx r13, [ rsp + 0x1e0 ]
test al, al
adox rdx, r15
adox rcx, r13
adcx rdx, [ rsp + 0x80 ]
adcx rcx, [ rsp + 0x78 ]
xor rdi, rdi
adox r14, [ rsp + 0x50 ]
adox r9, [ rsp + 0x48 ]
mov rbp, rdx
mov rdx, [ rsi + 0x10 ]
mulx r13, r15, [ rax + 0x0 ]
adcx rbp, r15
adcx r13, rcx
mov rdx, [ rsi + 0x28 ]
mulx r15, rcx, r8
xor rdx, rdx
adox r10, rcx
adox r15, rbx
adcx r14, r12
adcx r11, r9
mov rdi, [ rsp + 0x210 ]
mov rbx, [ rsp + 0x218 ]
shrd rbx, rdi, 58
shr rdi, 58
mov r12, [ rsp + 0x40 ]
mov r9, r12
add r9, [ rsp + 0xe8 ]
mov rcx, [ rsp + 0x28 ]
adcx rcx, [ rsp + 0xe0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x220 ], r15
mulx r15, r12, [ rax + 0x8 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x228 ], r10
mov [ rsp + 0x230 ], rcx
mulx rcx, r10, r8
test al, al
adox r14, rbx
adox rdi, r11
mov rdx, [ rsi + 0x0 ]
mulx r11, r8, [ rax + 0x10 ]
mov rdx, [ rsp + 0x178 ]
adcx rdx, [ rsp + 0xc8 ]
mov rbx, [ rsp + 0x170 ]
adcx rbx, [ rsp + 0xc0 ]
mov [ rsp + 0x238 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x240 ], r14
mov [ rsp + 0x248 ], r11
mulx r11, r14, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x250 ], r8
mov [ rsp + 0x258 ], r9
mulx r9, r8, [ rsi + 0x8 ]
test al, al
adox rdi, r14
adox r11, rbx
adcx rbp, r8
adcx r9, r13
test al, al
adox rdi, r12
adox r15, r11
mov rdx, r10
adcx rdx, [ rsp + 0x258 ]
adcx rcx, [ rsp + 0x230 ]
mov r13, [ rsp + 0x228 ]
test al, al
adox r13, [ rsp + 0x60 ]
mov r12, [ rsp + 0x220 ]
adox r12, [ rsp + 0x58 ]
mov r10, rdx
mov rdx, [ rax + 0x8 ]
mulx r14, rbx, [ rsi + 0x18 ]
adcx rbp, [ rsp + 0x250 ]
adcx r9, [ rsp + 0x248 ]
test al, al
adox r10, [ rsp + 0x100 ]
adox rcx, [ rsp + 0xf8 ]
mov rdx, [ rsi + 0x10 ]
mulx r11, r8, [ rax + 0x10 ]
adcx r10, [ rsp + 0x20 ]
adcx rcx, [ rsp + 0x18 ]
xor rdx, rdx
adox r10, rbx
adox r14, rcx
adcx r10, r8
adcx r11, r14
mov rbx, [ rsp + 0x238 ]
mov r8, [ rsp + 0x240 ]
shrd r8, rbx, 58
shr rbx, 58
test al, al
adox rbp, r8
adox rbx, r9
mov rdx, [ rax + 0x10 ]
mulx rcx, r9, [ rsi + 0x18 ]
mov rdx, [ rax + 0x0 ]
mulx r8, r14, [ rsi + 0x40 ]
adcx rdi, r9
adcx rcx, r15
mov rdx, [ rax + 0x8 ]
mulx r9, r15, [ rsi + 0x10 ]
xor rdx, rdx
adox r13, [ rsp + 0x10 ]
adox r12, [ rsp + 0x8 ]
mov rdx, rbp
shrd rdx, rbx, 58
shr rbx, 58
mov [ rsp + 0x260 ], rbx
mov rbx, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x268 ], rcx
mov [ rsp + 0x270 ], rdi
mulx rdi, rcx, [ rax + 0x8 ]
test al, al
adox r14, rcx
adox rdi, r8
adcx r13, r15
adcx r9, r12
mov rdx, [ rax + 0x18 ]
mulx r15, r8, [ rsi + 0x8 ]
test al, al
adox r10, r8
adox r15, r11
mov rdx, [ rsp + 0x0 ]
mov r11, rdx
adcx r11, [ rsp + 0x270 ]
mov r12, [ rsp - 0x8 ]
adcx r12, [ rsp + 0x268 ]
mov rdx, [ rax + 0x18 ]
mulx r8, rcx, [ rsi + 0x0 ]
test al, al
adox r10, [ rsp + 0x120 ]
adox r15, [ rsp + 0x118 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x278 ], r12
mov [ rsp + 0x280 ], r11
mulx r11, r12, [ rax + 0x0 ]
mov rdx, r12
adcx rdx, [ rsp + 0x1d8 ]
adcx r11, [ rsp + 0x1d0 ]
test al, al
adox r13, [ rsp - 0x10 ]
adox r9, [ rsp - 0x18 ]
adcx r13, rcx
adcx r8, r9
mov rcx, rdx
mov rdx, [ rsi + 0x20 ]
mulx r9, r12, [ rax + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x288 ], rdi
mov [ rsp + 0x290 ], r14
mulx r14, rdi, [ rax + 0x20 ]
test al, al
adox r13, rbx
adox r8, [ rsp + 0x260 ]
adcx rcx, [ rsp + 0x138 ]
adcx r11, [ rsp + 0x130 ]
mov rdx, [ rsp + 0x1f0 ]
xor rbx, rbx
adox rdx, [ rsp - 0x20 ]
mov [ rsp + 0x298 ], r14
mov r14, [ rsp + 0x1e8 ]
adox r14, [ rsp - 0x28 ]
adcx rcx, r12
adcx r9, r11
mov r12, rdx
mov rdx, [ rsi + 0x8 ]
mulx rbx, r11, [ rax + 0x28 ]
mov rdx, r13
shrd rdx, r8, 58
shr r8, 58
mov [ rsp + 0x2a0 ], rbx
xor rbx, rbx
adox r10, rdx
adox r8, r15
mov r15, [ rsp + 0x290 ]
adcx r15, [ rsp + 0xa8 ]
mov rdx, [ rsp + 0x288 ]
adcx rdx, [ rsp + 0xa0 ]
add r12, [ rsp + 0x168 ]
adcx r14, [ rsp + 0x160 ]
mov rbx, 0x3ffffffffffffff 
mov [ rsp + 0x2a8 ], r14
mov r14, r10
and r14, rbx
shrd r10, r8, 58
shr r8, 58
mov rbx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x2b0 ], r8
mov [ rsp + 0x2b8 ], r10
mulx r10, r8, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x2c0 ], r12
mov [ rsp + 0x2c8 ], r11
mulx r11, r12, [ rax + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x2d0 ], r11
mov [ rsp + 0x2d8 ], r12
mulx r12, r11, [ rax + 0x28 ]
xor rdx, rdx
adox rcx, r8
adox r10, r9
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x20 ], r14
adcx r15, [ rsp - 0x30 ]
adcx rbx, [ rsp - 0x38 ]
mov rdx, [ rsi + 0x8 ]
mulx r8, r14, [ rax + 0x38 ]
add r15, rdi
adcx rbx, [ rsp + 0x298 ]
mov rdx, [ rax + 0x28 ]
mulx r9, rdi, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x2e0 ], r12
mov [ rsp + 0x2e8 ], r11
mulx r11, r12, [ rax + 0x28 ]
xor rdx, rdx
adox rcx, [ rsp + 0x70 ]
adox r10, [ rsp + 0x68 ]
adcx r15, r12
adcx r11, rbx
test al, al
adox rcx, [ rsp + 0x2c8 ]
adox r10, [ rsp + 0x2a0 ]
mov rdx, [ rsi + 0x28 ]
mulx r12, rbx, [ rax + 0x10 ]
adcx rcx, [ rsp + 0xb8 ]
adcx r10, [ rsp + 0xb0 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x2f0 ], r10
mov [ rsp + 0x2f8 ], rcx
mulx rcx, r10, [ rsi + 0x10 ]
xor rdx, rdx
adox r15, r10
adox rcx, r11
adcx r15, r14
adcx r8, rcx
mov r14, rbx
xor r11, r11
adox r14, [ rsp + 0x2c0 ]
adox r12, [ rsp + 0x2a8 ]
adcx r14, [ rsp + 0x38 ]
adcx r12, [ rsp + 0x30 ]
mov rdx, [ rsi + 0x8 ]
mulx r10, rbx, [ rax + 0x30 ]
mov rdx, [ rsp + 0x2d8 ]
mov rcx, rdx
test al, al
adox rcx, [ rsp + 0x280 ]
mov [ rsp + 0x300 ], r8
mov r8, [ rsp + 0x2d0 ]
adox r8, [ rsp + 0x278 ]
adcx r14, [ rsp - 0x40 ]
adcx r12, [ rsp - 0x48 ]
xor rdx, rdx
adox rcx, rdi
adox r9, r8
adcx r14, [ rsp + 0x2e8 ]
adcx r12, [ rsp + 0x2e0 ]
add r14, rbx
adcx r10, r12
xor r11, r11
adox r14, [ rsp + 0x148 ]
adox r10, [ rsp + 0x140 ]
adcx rcx, [ rsp + 0x2b8 ]
adcx r9, [ rsp + 0x2b0 ]
mov rdx, rcx
shrd rdx, r9, 58
shr r9, 58
mov rdi, rdx
xor rbx, rbx
adox rdi, [ rsp + 0x2f8 ]
adox r9, [ rsp + 0x2f0 ]
mov r11, 0x3ffffffffffffff 
mov r8, rdi
and r8, r11
and rcx, r11
shrd rdi, r9, 58
shr r9, 58
xor r12, r12
adox r14, rdi
adox r9, r10
mov rbx, r14
shrd rbx, r9, 58
shr r9, 58
and r13, r11
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x30 ], r8
and r14, r11
mov rdx, [ rsi + 0x0 ]
mulx rdi, r8, [ rax + 0x40 ]
mov rdx, [ rsp + 0x218 ]
and rdx, r11
adox r15, r8
adox rdi, [ rsp + 0x300 ]
adcx r15, rbx
adcx r9, rdi
mov rbx, r15
shrd rbx, r9, 57
shr r9, 57
xor r8, r8
adox rbx, rdx
adox r9, r8
mov r12, rbx
shrd r12, r9, 58
mov rdx, [ rsp + 0x240 ]
and rdx, r11
mov rdi, 0x39 
bzhi r9, r15, rdi
mov [ r10 + 0x40 ], r9
mov [ r10 + 0x18 ], r13
and rbp, r11
lea r12, [ r12 + rdx ]
mov r13, r12
and r13, r11
shr r12, 58
mov [ r10 + 0x8 ], r13
and rbx, r11
lea r12, [ r12 + rbp ]
mov [ r10 + 0x38 ], r14
mov [ r10 + 0x28 ], rcx
mov [ r10 + 0x0 ], rbx
mov [ r10 + 0x10 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 904
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.1294
; seed 2218345779575265 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 6143847 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=65, initial num_batches=31): 114653 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.018661434765546735
; number reverted permutation / tried permutation: 55549 / 90151 =61.618%
; number reverted decision / tried decision: 43823 / 89848 =48.775%
; validated in 3.338s
