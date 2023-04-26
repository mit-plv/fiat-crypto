SECTION .text
	GLOBAL fiat_p521_carry_mul
fiat_p521_carry_mul:
sub rsp, 888
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x18 ]
mov rdx, [ rax + 0x8 ]
lea rcx, [rdx + rdx]
mov rdx, [ rax + 0x28 ]
mov r8, rdx
shl r8, 0x1
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x28 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x48 ], rbx
mov [ rsp - 0x40 ], r9
mulx r9, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], r12
mov [ rsp - 0x30 ], rbp
mulx rbp, r12, [ rax + 0x10 ]
mov rdx, 0x1 
mov [ rsp - 0x28 ], rbp
shlx rbp, [ rax + 0x38 ], rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x20 ], r12
lea r12, [rdx + rdx]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x18 ], r14
mov [ rsp - 0x10 ], r13
mulx r13, r14, r12
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x8 ], r11
mov [ rsp + 0x0 ], r10
mulx r10, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x8 ], r10
mov [ rsp + 0x10 ], r11
mulx r11, r10, r12
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x18 ], r9
mov [ rsp + 0x20 ], rbx
mulx rbx, r9, [ rax + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x28 ], rbx
mov [ rsp + 0x30 ], r9
mulx r9, rbx, rbp
mov rdx, 0x1 
mov [ rsp + 0x38 ], r9
shlx r9, [ rax + 0x30 ], rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x40 ], rbx
mov [ rsp + 0x48 ], rdi
mulx rdi, rbx, [ rax + 0x8 ]
mov rdx, r9
mov [ rsp + 0x50 ], rdi
mulx rdi, r9, [ rsi + 0x18 ]
mov [ rsp + 0x58 ], rbx
mov rbx, rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x60 ], r15
mov [ rsp + 0x68 ], rdi
mulx rdi, r15, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x70 ], rdi
mov [ rsp + 0x78 ], r15
mulx r15, rdi, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x80 ], r15
mov [ rsp + 0x88 ], rdi
mulx rdi, r15, [ rax + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x90 ], rdi
mov [ rsp + 0x98 ], r15
mulx r15, rdi, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0xa0 ], r15
mov [ rsp + 0xa8 ], rdi
mulx rdi, r15, rbx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0xb0 ], rdi
mov [ rsp + 0xb8 ], r15
mulx r15, rdi, [ rsi + 0x0 ]
mov rdx, r12
mov [ rsp + 0xc0 ], r15
mulx r15, r12, [ rsi + 0x38 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0xc8 ], rdi
lea rdi, [rdx + rdx]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0xd0 ], r9
mov [ rsp + 0xd8 ], r13
mulx r13, r9, rdi
xor rdx, rdx
adox r9, r12
adox r15, r13
mov rdx, [ rsi + 0x8 ]
mulx r13, r12, [ rax + 0x30 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xe0 ], r13
mov [ rsp + 0xe8 ], r12
mulx r12, r13, r8
imul rdx, [ rax + 0x20 ], 0x2
mov [ rsp + 0xf0 ], r14
mov [ rsp + 0xf8 ], r12
mulx r12, r14, [ rsi + 0x38 ]
mov [ rsp + 0x100 ], r13
mov [ rsp + 0x108 ], rcx
mulx rcx, r13, [ rsi + 0x30 ]
test al, al
adox r10, r14
adox r12, r11
mulx r14, r11, [ rsi + 0x40 ]
mov [ rsp + 0x110 ], r14
mov r14, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x118 ], r11
mov [ rsp + 0x120 ], r12
mulx r12, r11, [ rax + 0x38 ]
mov rdx, [ rax + 0x40 ]
mov [ rsp + 0x128 ], r12
mov r12, rdx
shl r12, 0x1
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x130 ], r11
mov [ rsp + 0x138 ], r10
mulx r10, r11, r12
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x140 ], r10
mov [ rsp + 0x148 ], r11
mulx r11, r10, r12
test al, al
adox r9, r13
adox rcx, r15
mov rdx, [ rsi + 0x40 ]
mulx r13, r15, [ rsp + 0x108 ]
adcx r9, [ rsp + 0x100 ]
adcx rcx, [ rsp + 0xf8 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x150 ], r11
mov [ rsp + 0x158 ], r10
mulx r10, r11, rdi
test al, al
adox r15, r11
adox r10, r13
adcx r15, [ rsp + 0xf0 ]
adcx r10, [ rsp + 0xd8 ]
mov rdx, [ rsi + 0x28 ]
mulx r13, rdi, r14
mov rdx, [ rsi + 0x30 ]
mulx r11, r14, r8
test al, al
adox r15, rdi
adox r13, r10
mov rdx, r8
mulx r10, r8, [ rsi + 0x20 ]
mov rdi, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x160 ], rcx
mov [ rsp + 0x168 ], r9
mulx r9, rcx, rbx
mov rdx, r14
adcx rdx, [ rsp + 0x138 ]
adcx r11, [ rsp + 0x120 ]
xor r14, r14
adox r15, r8
adox r10, r13
mov r13, rdx
mov rdx, [ rsi + 0x20 ]
mulx r14, r8, rbp
adcx r15, [ rsp + 0xd0 ]
adcx r10, [ rsp + 0x68 ]
add r13, rcx
adcx r9, r11
test al, al
adox r13, r8
adox r14, r9
mov rdx, [ rsi + 0x18 ]
mulx r11, rcx, r12
adcx r13, rcx
adcx r11, r14
xor rdx, rdx
adox r13, [ rsp + 0x60 ]
adox r11, [ rsp + 0x48 ]
mov rdx, rbp
mulx r8, rbp, [ rsi + 0x10 ]
mulx r14, r9, [ rsi + 0x28 ]
xchg rdx, rbx
mov [ rsp + 0x170 ], r11
mulx r11, rcx, [ rsi + 0x20 ]
mov [ rsp + 0x178 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x180 ], r14
mov [ rsp + 0x188 ], r9
mulx r9, r14, rdi
mov rdx, rcx
adcx rdx, [ rsp + 0x168 ]
adcx r11, [ rsp + 0x160 ]
test al, al
adox rdx, [ rsp + 0x40 ]
adox r11, [ rsp + 0x38 ]
mov rcx, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x190 ], r11
mov [ rsp + 0x198 ], r9
mulx r9, r11, rdi
mov rdx, r12
mulx rdi, r12, [ rsi + 0x8 ]
mov [ rsp + 0x1a0 ], r9
mov [ rsp + 0x1a8 ], r11
mulx r11, r9, [ rsi + 0x10 ]
adcx r15, rbp
adcx r8, r10
mov r10, r14
add r10, [ rsp + 0x118 ]
mov rbp, [ rsp + 0x110 ]
adcx rbp, [ rsp + 0x198 ]
xor r14, r14
adox r15, r12
adox rdi, r8
adcx rcx, r9
adcx r11, [ rsp + 0x190 ]
mov r12, rdx
mov rdx, [ rax + 0x0 ]
mulx r8, r9, [ rsi + 0x8 ]
mov rdx, r13
mulx r14, r13, [ rsi + 0x30 ]
mov [ rsp + 0x1b0 ], r11
xor r11, r11
adox r10, r13
adox r14, rbp
adcx r15, [ rsp + 0x20 ]
adcx rdi, [ rsp + 0x18 ]
mov rbp, rdx
mov rdx, [ rsi + 0x38 ]
mulx r11, r13, [ rax + 0x0 ]
add r10, [ rsp + 0x188 ]
adcx r14, [ rsp + 0x180 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x1b8 ], rdi
mov [ rsp + 0x1c0 ], r15
mulx r15, rdi, [ rax + 0x0 ]
mov rdx, rbp
mov [ rsp + 0x1c8 ], r15
mulx r15, rbp, [ rsi + 0x38 ]
add r10, [ rsp + 0x148 ]
adcx r14, [ rsp + 0x140 ]
mov rdx, rbp
mov [ rsp + 0x1d0 ], rdi
xor rdi, rdi
adox rdx, [ rsp + 0x1a8 ]
adox r15, [ rsp + 0x1a0 ]
mov rbp, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x1d8 ], r15
mulx r15, rdi, r12
mov rdx, r12
mov [ rsp + 0x1e0 ], rbp
mulx rbp, r12, [ rsi + 0x38 ]
adcx rdi, r13
adcx r11, r15
mov r13, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x1e8 ], r11
mulx r11, r15, rbx
test al, al
adox r15, r12
adox rbp, r11
adcx rcx, r9
adcx r8, [ rsp + 0x1b0 ]
mov rdx, rbx
mulx r9, rbx, [ rsi + 0x30 ]
mov r12, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1f0 ], rdi
mulx rdi, r11, [ rax + 0x0 ]
add r10, r11
adcx rdi, r14
xor rdx, rdx
adox r15, [ rsp + 0x1d0 ]
adox rbp, [ rsp + 0x1c8 ]
adcx rcx, [ rsp + 0xc8 ]
adcx r8, [ rsp + 0xc0 ]
xor r14, r14
adox r10, [ rsp + 0x58 ]
adox rdi, [ rsp + 0x50 ]
mov rdx, [ rsi + 0x8 ]
mulx r14, r11, [ rax + 0x10 ]
adcx r10, r11
adcx r14, rdi
mov rdx, rbx
xor rdi, rdi
adox rdx, [ rsp + 0x1e0 ]
adox r9, [ rsp + 0x1d8 ]
adcx r10, [ rsp + 0x0 ]
adcx r14, [ rsp - 0x8 ]
mov rbx, rdx
mov rdx, [ rax + 0x8 ]
mulx rdi, r11, [ rsi + 0x8 ]
mov rdx, [ rsp + 0x1b8 ]
mov [ rsp + 0x1f8 ], r14
mov r14, [ rsp + 0x1c0 ]
shrd r14, rdx, 58
shr rdx, 58
test al, al
adox rbx, [ rsp + 0x158 ]
adox r9, [ rsp + 0x150 ]
mov [ rsp + 0x200 ], r10
mov r10, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x208 ], rbp
mov [ rsp + 0x210 ], r15
mulx r15, rbp, [ rax + 0x8 ]
adcx rbx, [ rsp + 0x30 ]
adcx r9, [ rsp + 0x28 ]
xor rdx, rdx
adox rcx, r14
adox r10, r8
mov r8, rcx
shrd r8, r10, 58
shr r10, 58
mov r14, r11
test al, al
adox r14, [ rsp + 0x178 ]
adox rdi, [ rsp + 0x170 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x218 ], r10
mulx r10, r11, [ rax + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x220 ], r10
mov [ rsp + 0x228 ], r11
mulx r11, r10, [ rax + 0x10 ]
adcx r14, r10
adcx r11, rdi
xor rdx, rdx
adox rbx, rbp
adox r15, r9
mov rbp, [ rsp + 0x210 ]
adcx rbp, [ rsp + 0x98 ]
mov r9, [ rsp + 0x208 ]
adcx r9, [ rsp + 0x90 ]
xor rdi, rdi
adox rbp, [ rsp - 0x10 ]
adox r9, [ rsp - 0x18 ]
mov rdx, [ rsi + 0x0 ]
mulx rdi, r10, [ rax + 0x20 ]
mov rdx, [ rsp - 0x30 ]
mov [ rsp + 0x230 ], rdi
mov rdi, rdx
adcx rdi, [ rsp + 0x1f0 ]
mov [ rsp + 0x238 ], r10
mov r10, [ rsp - 0x38 ]
adcx r10, [ rsp + 0x1e8 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x240 ], r9
mov [ rsp + 0x248 ], rbp
mulx rbp, r9, [ rsi + 0x18 ]
mov rdx, r12
mov [ rsp + 0x250 ], r15
mulx r15, r12, [ rsi + 0x38 ]
test al, al
adox r14, r8
adox r11, [ rsp + 0x218 ]
adcx rdi, [ rsp + 0x228 ]
adcx r10, [ rsp + 0x220 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x258 ], r11
mulx r11, r8, r13
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x260 ], r14
mulx r14, r13, [ rsi + 0x20 ]
mov rdx, r12
mov [ rsp + 0x268 ], r11
xor r11, r11
adox rdx, [ rsp + 0xb8 ]
adox r15, [ rsp + 0xb0 ]
adcx rdi, r13
adcx r14, r10
mov r12, rdx
mov rdx, [ rax + 0x18 ]
mulx r13, r10, [ rsi + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x270 ], r15
mulx r15, r11, [ rsi + 0x10 ]
xor rdx, rdx
adox rdi, r9
adox rbp, r14
mov rdx, [ rax + 0x28 ]
mulx r14, r9, [ rsi + 0x10 ]
adcx rdi, r9
adcx r14, rbp
mov rdx, [ rax + 0x18 ]
mulx r9, rbp, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x278 ], r14
mov [ rsp + 0x280 ], rdi
mulx rdi, r14, [ rax + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x288 ], rdi
mov [ rsp + 0x290 ], r14
mulx r14, rdi, [ rsi + 0x10 ]
xor rdx, rdx
adox rbx, r11
adox r15, [ rsp + 0x250 ]
mov r11, rbp
adcx r11, [ rsp + 0x248 ]
adcx r9, [ rsp + 0x240 ]
add rbx, r10
adcx r13, r15
mov rdx, [ rsi + 0x28 ]
mulx rbp, r10, [ rax + 0x0 ]
test al, al
adox r11, [ rsp + 0x10 ]
adox r9, [ rsp + 0x8 ]
adcx rbx, [ rsp + 0x238 ]
adcx r13, [ rsp + 0x230 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x298 ], r9
mulx r9, r15, [ rax + 0x8 ]
test al, al
adox r12, r8
mov rdx, [ rsp + 0x268 ]
adox rdx, [ rsp + 0x270 ]
mov r8, [ rsp + 0xe8 ]
mov [ rsp + 0x2a0 ], r11
mov r11, r8
adcx r11, [ rsp + 0x280 ]
mov [ rsp + 0x2a8 ], r13
mov r13, [ rsp + 0xe0 ]
adcx r13, [ rsp + 0x278 ]
mov r8, [ rsp + 0x258 ]
mov [ rsp + 0x2b0 ], r13
mov r13, [ rsp + 0x260 ]
shrd r13, r8, 58
shr r8, 58
test al, al
adox r12, r10
adox rbp, rdx
adcx r12, r15
adcx r9, rbp
test al, al
adox r12, [ rsp - 0x20 ]
adox r9, [ rsp - 0x28 ]
mov r10, r13
adcx r10, [ rsp + 0x200 ]
adcx r8, [ rsp + 0x1f8 ]
mov r15, r10
shrd r15, r8, 58
shr r8, 58
xor rdx, rdx
adox r12, rdi
adox r14, r9
mov rdx, [ rax + 0x20 ]
mulx r13, rdi, [ rsi + 0x20 ]
mov rdx, [ rax + 0x8 ]
mulx r9, rbp, [ rsi + 0x38 ]
mov rdx, rbp
adcx rdx, [ rsp + 0x290 ]
adcx r9, [ rsp + 0x288 ]
xor rbp, rbp
adox rbx, r15
adox r8, [ rsp + 0x2a8 ]
mov r15, rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x2b8 ], r13
mulx r13, rbp, [ rsi + 0x10 ]
adcx r15, [ rsp + 0x88 ]
adcx r9, [ rsp + 0x80 ]
xor rdx, rdx
adox r15, [ rsp + 0xa8 ]
adox r9, [ rsp + 0xa0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x2c0 ], r13
mov [ rsp + 0x2c8 ], rbp
mulx rbp, r13, [ rax + 0x28 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x2d0 ], r9
mov [ rsp + 0x2d8 ], r15
mulx r15, r9, [ rsi + 0x8 ]
adcx r12, r9
adcx r15, r14
mov rdx, 0x3ffffffffffffff 
and r10, rdx
mov rdx, [ rsi + 0x0 ]
mulx r9, r14, [ rax + 0x38 ]
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x18 ], r10
mov r10, r13
adox r10, [ rsp + 0x2a0 ]
adox rbp, [ rsp + 0x298 ]
adcx r10, [ rsp + 0x78 ]
adcx rbp, [ rsp + 0x70 ]
test al, al
adox r12, [ rsp - 0x40 ]
adox r15, [ rsp - 0x48 ]
mov r13, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x2e0 ], rbp
mov [ rsp + 0x2e8 ], r10
mulx r10, rbp, [ rax + 0x28 ]
mov rdx, rbx
shrd rdx, r8, 58
shr r8, 58
add r12, rdx
adcx r8, r15
xor r15, r15
adox r11, r14
adox r9, [ rsp + 0x2b0 ]
mov r14, rdi
adcx r14, [ rsp + 0x2d8 ]
mov rdx, [ rsp + 0x2b8 ]
adcx rdx, [ rsp + 0x2d0 ]
xor rdi, rdi
adox r14, rbp
adox r10, rdx
mov rdx, [ rsi + 0x0 ]
mulx rbp, r15, [ rax + 0x40 ]
mov rdx, r12
shrd rdx, r8, 58
shr r8, 58
test al, al
adox r14, [ rsp + 0x2c8 ]
adox r10, [ rsp + 0x2c0 ]
mov r13, rdx
adcx r13, [ rsp + 0x2e8 ]
adcx r8, [ rsp + 0x2e0 ]
mov rdx, r13
shrd rdx, r8, 58
shr r8, 58
mov rdi, 0x3a 
mov [ rsp + 0x2f0 ], rbp
bzhi rbp, r13, rdi
adox r11, rdx
adox r8, r9
xor r9, r9
adox r14, [ rsp + 0x130 ]
adox r10, [ rsp + 0x128 ]
bzhi r13, [ rsp + 0x1c0 ], rdi
adox r14, r15
adox r10, [ rsp + 0x2f0 ]
bzhi r15, [ rsp + 0x260 ], rdi
bzhi rdx, rcx, rdi
mov rcx, r11
shrd rcx, r8, 58
shr r8, 58
test al, al
adox r14, rcx
adox r8, r10
mov r10, 0x1ffffffffffffff 
mov rcx, r14
and rcx, r10
shrd r14, r8, 57
shr r8, 57
xor rdi, rdi
adox r14, r13
adox r8, rdi
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x40 ], rcx
mov r13, 0x3a 
bzhi rcx, r14, r13
shrd r14, r8, 58
lea r14, [ r14 + rdx ]
mov rdx, r14
shr rdx, 58
lea rdx, [ rdx + r15 ]
mov [ r9 + 0x10 ], rdx
bzhi r15, r11, r13
bzhi r11, rbx, r13
mov [ r9 + 0x20 ], r11
mov [ r9 + 0x30 ], rbp
mov [ r9 + 0x38 ], r15
bzhi rbx, r12, r13
mov [ r9 + 0x28 ], rbx
bzhi r12, r14, r13
mov [ r9 + 0x0 ], rcx
mov [ r9 + 0x8 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 888
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.1162
; seed 3188607769750219 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 13380705 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=41, initial num_batches=31): 226321 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.016913981737135673
; number reverted permutation / tried permutation: 47723 / 90109 =52.961%
; number reverted decision / tried decision: 32750 / 89890 =36.433%
; validated in 5.372s
