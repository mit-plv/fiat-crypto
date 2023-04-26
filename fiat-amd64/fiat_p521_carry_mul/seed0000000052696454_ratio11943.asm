SECTION .text
	GLOBAL fiat_p521_carry_mul
fiat_p521_carry_mul:
sub rsp, 688
mov rax, [ rdx + 0x20 ]
lea r10, [rax + rax]
mov rax, rdx
mov rdx, [ rdx + 0x18 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, [ rax + 0x0 ]
mov rdx, 0x1 
mov [ rsp - 0x80 ], rbx
shlx rbx, [ rax + 0x10 ], rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, [ rax + 0x40 ]
mov [ rsp - 0x68 ], r13
mov r13, rdx
shl r13, 0x1
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, r13
mov rdx, [ rsi + 0x40 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r12
mulx r12, rdi, rbx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x40 ], rbp
mov [ rsp - 0x38 ], rcx
mulx rcx, rbp, [ rax + 0x18 ]
mov rdx, r13
mov [ rsp - 0x30 ], r11
mulx r11, r13, [ rsi + 0x28 ]
xchg rdx, r10
mov [ rsp - 0x28 ], rcx
mov [ rsp - 0x20 ], rbp
mulx rbp, rcx, [ rsi + 0x28 ]
mov [ rsp - 0x18 ], r9
mov r9, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x10 ], r8
mov [ rsp - 0x8 ], r15
mulx r15, r8, r10
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x0 ], r14
mov [ rsp + 0x8 ], r15
mulx r15, r14, [ rax + 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x10 ], r15
mov [ rsp + 0x18 ], r14
mulx r14, r15, [ rsi + 0x20 ]
mov rdx, 0x1 
mov [ rsp + 0x20 ], r14
shlx r14, [ rax + 0x18 ], rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x28 ], r15
mov [ rsp + 0x30 ], r8
mulx r8, r15, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x38 ], r8
mov [ rsp + 0x40 ], r15
mulx r15, r8, r14
mov rdx, rbx
mov [ rsp + 0x48 ], rbp
mulx rbp, rbx, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x50 ], rcx
mov [ rsp + 0x58 ], rbp
mulx rbp, rcx, r14
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x60 ], rbp
mov [ rsp + 0x68 ], rcx
mulx rcx, rbp, r10
mov rdx, 0x1 
mov [ rsp + 0x70 ], rcx
shlx rcx, [ rax + 0x38 ], rdx
imul rdx, [ rax + 0x28 ], 0x2
mov [ rsp + 0x78 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x80 ], rbx
mov [ rsp + 0x88 ], r12
mulx r12, rbx, [ rax + 0x0 ]
mov rdx, 0x1 
mov [ rsp + 0x90 ], r12
shlx r12, [ rax + 0x30 ], rdx
mov rdx, rcx
mov [ rsp + 0x98 ], rbx
mulx rbx, rcx, [ rsi + 0x30 ]
xchg rdx, r12
mov [ rsp + 0xa0 ], rdi
mov [ rsp + 0xa8 ], r15
mulx r15, rdi, [ rsi + 0x30 ]
mov [ rsp + 0xb0 ], r8
mov r8, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xb8 ], r11
mov [ rsp + 0xc0 ], r13
mulx r13, r11, rbp
mov rdx, r9
mov [ rsp + 0xc8 ], rbx
mulx rbx, r9, [ rsi + 0x38 ]
xchg rdx, r14
mov [ rsp + 0xd0 ], rcx
mov [ rsp + 0xd8 ], r15
mulx r15, rcx, [ rsi + 0x40 ]
xor rdx, rdx
adox rcx, r9
adox rbx, r15
mov rdx, [ rsi + 0x40 ]
mulx r15, r9, r12
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0xe0 ], r15
mov [ rsp + 0xe8 ], r9
mulx r9, r15, r14
mov rdx, r8
mov [ rsp + 0xf0 ], rbx
mulx rbx, r8, [ rsi + 0x38 ]
adcx r15, r11
adcx r13, r9
mov r11, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0xf8 ], rcx
mulx rcx, r9, rbp
xor rdx, rdx
adox r15, rdi
adox r13, [ rsp + 0xd8 ]
mov rdx, r12
mulx rdi, r12, [ rsi + 0x28 ]
adcx r9, r8
adcx rbx, rcx
test al, al
adox r9, [ rsp + 0xd0 ]
adox rbx, [ rsp + 0xc8 ]
xchg rdx, r14
mulx rcx, r8, [ rsi + 0x30 ]
adcx r9, [ rsp + 0xc0 ]
adcx rbx, [ rsp + 0xb8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x100 ], r13
mov [ rsp + 0x108 ], r15
mulx r15, r13, [ rax + 0x38 ]
mov rdx, 0x1 
mov [ rsp + 0x110 ], r15
shlx r15, [ rax + 0x8 ], rdx
mov rdx, [ rsp + 0xb0 ]
mov [ rsp + 0x118 ], r13
mov r13, rdx
mov [ rsp + 0x120 ], rdi
xor rdi, rdi
adox r13, [ rsp + 0xa0 ]
mov [ rsp + 0x128 ], r12
mov r12, [ rsp + 0xa8 ]
adox r12, [ rsp + 0x88 ]
mov rdx, r15
mulx rdi, r15, [ rsi + 0x40 ]
adcx r15, [ rsp + 0x80 ]
adcx rdi, [ rsp + 0x58 ]
xor rdx, rdx
adox r13, r8
adox rcx, r12
mov rdx, [ rsi + 0x28 ]
mulx r12, r8, rbp
adcx r13, r8
adcx r12, rcx
mov rdx, r11
mulx rcx, r11, [ rsi + 0x20 ]
xor r8, r8
adox r13, r11
adox rcx, r12
adcx r9, [ rsp + 0x98 ]
adcx rbx, [ rsp + 0x90 ]
xor r12, r12
adox r15, [ rsp + 0x68 ]
adox rdi, [ rsp + 0x60 ]
adcx r15, [ rsp + 0x50 ]
adcx rdi, [ rsp + 0x48 ]
mulx r11, r8, [ rsi + 0x18 ]
xchg rdx, rbp
mov [ rsp + 0x130 ], rbx
mulx rbx, r12, [ rsi + 0x20 ]
test al, al
adox r15, r12
adox rbx, rdi
adcx r15, r8
adcx r11, rbx
mov rdi, rdx
mov rdx, [ rsi + 0x8 ]
mulx r12, r8, r10
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x138 ], r9
mulx r9, rbx, r14
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x140 ], r12
mov [ rsp + 0x148 ], r8
mulx r8, r12, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x150 ], r8
mov [ rsp + 0x158 ], r12
mulx r12, r8, [ rsi + 0x8 ]
xor rdx, rdx
adox r15, rbx
adox r9, r11
mov rdx, [ rsi + 0x18 ]
mulx rbx, r11, r14
adcx r13, r11
adcx rbx, rcx
add r13, [ rsp + 0x30 ]
adcx rbx, [ rsp + 0x8 ]
xor rdx, rdx
adox r13, r8
adox r12, rbx
mov rdx, rdi
mulx rcx, rdi, [ rsi + 0x30 ]
mov rdx, rdi
adcx rdx, [ rsp + 0xf8 ]
adcx rcx, [ rsp + 0xf0 ]
xchg rdx, rbp
mulx r11, r8, [ rsi + 0x28 ]
xor rbx, rbx
adox rbp, r8
adox r11, rcx
adcx r13, [ rsp + 0x158 ]
adcx r12, [ rsp + 0x150 ]
mov rdi, rdx
mov rdx, [ rsi + 0x20 ]
mulx r8, rcx, r14
xor rdx, rdx
adox rbp, rcx
adox r8, r11
adcx r15, [ rsp + 0x148 ]
adcx r9, [ rsp + 0x140 ]
mov rdx, [ rsi + 0x0 ]
mulx r11, rbx, [ rax + 0x0 ]
test al, al
adox r15, rbx
adox r11, r9
mov rdx, r15
shrd rdx, r11, 58
shr r11, 58
add r13, rdx
adcx r11, r12
mov rdx, [ rsi + 0x8 ]
mulx rcx, r12, [ rax + 0x8 ]
mov rdx, r13
shrd rdx, r11, 58
shr r11, 58
mov r9, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x160 ], r11
mulx r11, rbx, [ rsi + 0x10 ]
mov rdx, 0x3a 
mov [ rsp + 0x168 ], r9
bzhi r9, r15, rdx
bzhi r15, r13, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x170 ], r15
mulx r15, r13, r14
adox rbp, [ rsp + 0x0 ]
adox r8, [ rsp - 0x8 ]
mov rdx, [ rsp + 0x128 ]
mov r14, rdx
test al, al
adox r14, [ rsp + 0x108 ]
mov [ rsp + 0x178 ], r9
mov r9, [ rsp + 0x120 ]
adox r9, [ rsp + 0x100 ]
adcx rbp, rbx
adcx r11, r8
test al, al
adox r14, [ rsp + 0x78 ]
adox r9, [ rsp + 0x70 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rbx, [ rax + 0x10 ]
adcx rbp, r12
adcx rcx, r11
test al, al
adox rbp, rbx
adox r8, rcx
mov rdx, [ rsi + 0x40 ]
mulx r11, r12, rdi
mov rdx, [ rax + 0x10 ]
mulx rbx, rdi, [ rsi + 0x28 ]
adcx r12, r13
adcx r15, r11
mov rdx, [ rsi + 0x40 ]
mulx rcx, r13, r10
add rbp, [ rsp + 0x168 ]
adcx r8, [ rsp + 0x160 ]
xor rdx, rdx
adox r14, [ rsp - 0x10 ]
adox r9, [ rsp - 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x180 ], r8
mulx r8, r11, [ rax + 0x10 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x188 ], rbp
mov [ rsp + 0x190 ], r15
mulx r15, rbp, [ rax + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x198 ], r12
mov [ rsp + 0x1a0 ], rbx
mulx rbx, r12, [ rax + 0x8 ]
adcx r14, r12
adcx rbx, r9
xor rdx, rdx
adox r14, r11
adox r8, rbx
mov rdx, [ rax + 0x10 ]
mulx r11, r9, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x30 ]
mulx rbx, r12, r10
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x1a8 ], r11
mov [ rsp + 0x1b0 ], r9
mulx r9, r11, [ rsi + 0x38 ]
adcx r13, r11
adcx r9, rcx
xor rdx, rdx
adox r13, rbp
adox r15, r9
mov rdx, [ rax + 0x18 ]
mulx rbp, rcx, [ rsi + 0x0 ]
adcx r13, rdi
adcx r15, [ rsp + 0x1a0 ]
mov rdx, r12
test al, al
adox rdx, [ rsp + 0x198 ]
adox rbx, [ rsp + 0x190 ]
adcx r13, [ rsp + 0x28 ]
adcx r15, [ rsp + 0x20 ]
xchg rdx, r10
mulx r12, rdi, [ rsi + 0x38 ]
mov rdx, rdi
add rdx, [ rsp + 0xe8 ]
adcx r12, [ rsp + 0xe0 ]
mov r11, [ rsp + 0x180 ]
mov r9, [ rsp + 0x188 ]
shrd r9, r11, 58
shr r11, 58
xor rdi, rdi
adox r14, rcx
adox rbp, r8
mov r8, rdx
mov rdx, [ rsi + 0x28 ]
mulx rdi, rcx, [ rax + 0x0 ]
adcx r14, r9
adcx r11, rbp
mov rdx, [ rsi + 0x18 ]
mulx rbp, r9, [ rax + 0x8 ]
mov rdx, r9
test al, al
adox rdx, [ rsp + 0x138 ]
adox rbp, [ rsp + 0x130 ]
mov r9, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x1b8 ], r15
mov [ rsp + 0x1c0 ], r13
mulx r13, r15, [ rsi + 0x10 ]
adcx r10, rcx
adcx rdi, rbx
mov rdx, [ rax + 0x8 ]
mulx rcx, rbx, [ rsi + 0x20 ]
add r10, rbx
adcx rcx, rdi
xor rdx, rdx
adox r10, [ rsp + 0x40 ]
adox rcx, [ rsp + 0x38 ]
mov rdx, [ rax + 0x28 ]
mulx rbx, rdi, [ rsi + 0x0 ]
adcx r10, [ rsp - 0x20 ]
adcx rcx, [ rsp - 0x28 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x1c8 ], rbx
mov [ rsp + 0x1d0 ], rdi
mulx rdi, rbx, [ rax + 0x0 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x1d8 ], r12
mov [ rsp + 0x1e0 ], r8
mulx r8, r12, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x1e8 ], rcx
mov [ rsp + 0x1f0 ], r10
mulx r10, rcx, [ rax + 0x8 ]
test al, al
adox r9, r15
adox r13, rbp
adcx r9, [ rsp - 0x30 ]
adcx r13, [ rsp - 0x38 ]
xor rdx, rdx
adox r9, r12
adox r8, r13
mov rdx, [ rsi + 0x20 ]
mulx r15, rbp, [ rax + 0x10 ]
mov rdx, [ rax + 0x20 ]
mulx r13, r12, [ rsi + 0x18 ]
adcx rbx, rcx
adcx r10, rdi
mov rdx, [ rsi + 0x30 ]
mulx rcx, rdi, [ rax + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x1f8 ], r13
mov [ rsp + 0x200 ], r12
mulx r12, r13, [ rax + 0x20 ]
test al, al
adox rbx, [ rsp + 0x1b0 ]
adox r10, [ rsp + 0x1a8 ]
mov rdx, r14
shrd rdx, r11, 58
shr r11, 58
mov [ rsp + 0x208 ], r10
mov r10, r13
test al, al
adox r10, [ rsp + 0x1f0 ]
adox r12, [ rsp + 0x1e8 ]
mov r13, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x210 ], rbx
mov [ rsp + 0x218 ], r12
mulx r12, rbx, [ rax + 0x8 ]
adcx r9, r13
adcx r11, r8
mov rdx, rdi
xor r8, r8
adox rdx, [ rsp + 0x1e0 ]
adox rcx, [ rsp + 0x1d8 ]
mov rdi, 0x3ffffffffffffff 
mov r13, r9
and r13, rdi
adox rdx, rbx
adox r12, rcx
adcx rdx, rbp
adcx r15, r12
mov rbp, rdx
mov rdx, [ rsi + 0x8 ]
mulx rcx, rbx, [ rax + 0x28 ]
xor rdx, rdx
adox rbp, [ rsp + 0x18 ]
adox r15, [ rsp + 0x10 ]
mov rdx, [ rax + 0x18 ]
mulx r12, r8, [ rsi + 0x28 ]
and r14, rdi
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x220 ], r12
mulx r12, rdi, [ rax + 0x20 ]
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x20 ], r13
mov [ rdx + 0x18 ], r14
adox rbp, rdi
adox r12, r15
adcx r10, [ rsp + 0x1d0 ]
mov r13, [ rsp + 0x218 ]
adcx r13, [ rsp + 0x1c8 ]
shrd r9, r11, 58
shr r11, 58
xor r15, r15
adox r10, r9
adox r11, r13
mov r14, r10
shrd r14, r11, 58
shr r11, 58
mov rdi, rdx
mov rdx, [ rsi + 0x10 ]
mulx r9, r13, [ rax + 0x28 ]
xor rdx, rdx
adox rbp, rbx
adox rcx, r12
adcx rbp, [ rsp - 0x40 ]
adcx rcx, [ rsp - 0x48 ]
test al, al
adox rbp, r14
adox r11, rcx
mov r15, [ rsp + 0x200 ]
mov rbx, r15
adcx rbx, [ rsp + 0x1c0 ]
mov r12, [ rsp + 0x1f8 ]
adcx r12, [ rsp + 0x1b8 ]
xor r15, r15
adox rbx, r13
adox r9, r12
mov rdx, [ rsi + 0x8 ]
mulx r13, r14, [ rax + 0x30 ]
adcx rbx, r14
adcx r13, r9
mov rdx, rbp
shrd rdx, r11, 58
shr r11, 58
mov rcx, 0x3a 
bzhi r12, rbp, rcx
mov [ rdi + 0x30 ], r12
mov rbp, rdx
mov rdx, [ rsi + 0x18 ]
mulx r14, r9, [ rax + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mulx r15, r12, [ rax + 0x30 ]
mov rdx, [ rax + 0x38 ]
mulx rdi, rcx, [ rsi + 0x0 ]
adox rbx, rcx
adox rdi, r13
xor rdx, rdx
adox rbx, rbp
adox r11, rdi
mov r13, rbx
shrd r13, r11, 58
shr r11, 58
mov rdx, [ rsi + 0x20 ]
mulx rcx, rbp, [ rax + 0x20 ]
mov rdx, r8
xor rdi, rdi
adox rdx, [ rsp + 0x210 ]
mov [ rsp + 0x228 ], r11
mov r11, [ rsp + 0x208 ]
adox r11, [ rsp + 0x220 ]
adcx rdx, rbp
adcx rcx, r11
test al, al
adox rdx, r9
adox r14, rcx
adcx rdx, r12
adcx r15, r14
mov r8, 0x3ffffffffffffff 
and rbx, r8
adox rdx, [ rsp + 0x118 ]
adox r15, [ rsp + 0x110 ]
mov r9, rdx
mov rdx, [ rax + 0x40 ]
mulx rbp, r12, [ rsi + 0x0 ]
adcx r9, r12
adcx rbp, r15
xor rdx, rdx
adox r9, r13
adox rbp, [ rsp + 0x228 ]
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x38 ], rbx
mov r13, r9
shrd r13, rbp, 57
shr rbp, 57
test al, al
adox r13, [ rsp + 0x178 ]
adox rbp, rdx
mov r11, r13
shrd r11, rbp, 58
and r10, r8
mov rcx, 0x39 
bzhi r14, r9, rcx
add r11, [ rsp + 0x170 ]
mov rbx, r11
shr rbx, 58
and r11, r8
mov [ rdi + 0x8 ], r11
mov [ rdi + 0x40 ], r14
and r13, r8
mov r15, [ rsp + 0x188 ]
and r15, r8
lea rbx, [ rbx + r15 ]
mov [ rdi + 0x28 ], r10
mov [ rdi + 0x10 ], rbx
mov [ rdi + 0x0 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 688
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.1943
; seed 2099712435525434 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 7225098 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=75, initial num_batches=31): 146725 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.02030768302381504
; number reverted permutation / tried permutation: 55332 / 90098 =61.413%
; number reverted decision / tried decision: 38763 / 89901 =43.117%
; validated in 3.82s
