SECTION .text
	GLOBAL fiat_p521_carry_mul
fiat_p521_carry_mul:
sub rsp, 848
mov rax, rdx
mov rdx, [ rdx + 0x10 ]
mulx r11, r10, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, [ rax + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x0 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], r12
mov [ rsp - 0x40 ], rbp
mulx rbp, r12, [ rax + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x38 ], rbp
mov [ rsp - 0x30 ], r12
mulx r12, rbp, [ rax + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x28 ], rdi
mov [ rsp - 0x20 ], r15
mulx r15, rdi, [ rsi + 0x0 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x18 ], r8
mov r8, rdx
shl r8, 0x1
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x10 ], rcx
mov [ rsp - 0x8 ], r12
mulx r12, rcx, r8
mov rdx, 0x1 
mov [ rsp + 0x0 ], rbp
shlx rbp, [ rax + 0x40 ], rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x8 ], rbx
mov [ rsp + 0x10 ], r9
mulx r9, rbx, rbp
imul rdx, [ rax + 0x18 ], 0x2
mov [ rsp + 0x18 ], r11
mov r11, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x20 ], r10
mov [ rsp + 0x28 ], r15
mulx r15, r10, [ rax + 0x10 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x30 ], r15
mov [ rsp + 0x38 ], r10
mulx r10, r15, [ rax + 0x0 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x40 ], r10
mov [ rsp + 0x48 ], r15
mulx r15, r10, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x50 ], r15
mov [ rsp + 0x58 ], r10
mulx r10, r15, [ rsi + 0x28 ]
mov rdx, rbp
mov [ rsp + 0x60 ], r10
mulx r10, rbp, [ rsi + 0x8 ]
mov [ rsp + 0x68 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x70 ], rdi
mov [ rsp + 0x78 ], r10
mulx r10, rdi, r11
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x80 ], rbp
mov [ rsp + 0x88 ], r14
mulx r14, rbp, [ rsi + 0x30 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x90 ], r14
mov r14, rdx
shl r14, 0x1
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x98 ], rbp
mov [ rsp + 0xa0 ], r13
mulx r13, rbp, r14
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xa8 ], r12
lea r12, [rdx + rdx]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0xb0 ], rcx
mov [ rsp + 0xb8 ], r13
mulx r13, rcx, r11
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0xc0 ], r13
mov r13, rdx
shl r13, 0x1
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xc8 ], rcx
mov [ rsp + 0xd0 ], rbp
mulx rbp, rcx, r12
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xd8 ], rbp
mov [ rsp + 0xe0 ], rcx
mulx rcx, rbp, r13
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0xe8 ], rcx
mov rcx, rdx
shl rcx, 0x1
mov rdx, rcx
mov [ rsp + 0xf0 ], rbp
mulx rbp, rcx, [ rsi + 0x40 ]
mov [ rsp + 0xf8 ], r10
mov r10, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x100 ], rdi
mov [ rsp + 0x108 ], rbp
mulx rbp, rdi, r12
test al, al
adox rcx, rbx
adox r9, [ rsp + 0x108 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x110 ], r9
mulx r9, rbx, r8
mov rdx, r12
mov [ rsp + 0x118 ], rcx
mulx rcx, r12, [ rsi + 0x38 ]
mov [ rsp + 0x120 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x128 ], rdi
mov [ rsp + 0x130 ], r9
mulx r9, rdi, r10
mov rdx, r8
mov [ rsp + 0x138 ], r9
mulx r9, r8, [ rsi + 0x40 ]
xchg rdx, r10
mov [ rsp + 0x140 ], rdi
mov [ rsp + 0x148 ], rbx
mulx rbx, rdi, [ rsi + 0x28 ]
xchg rdx, r10
mov [ rsp + 0x150 ], rbx
mov [ rsp + 0x158 ], rdi
mulx rdi, rbx, [ rsi + 0x38 ]
mov rdx, rbp
mov [ rsp + 0x160 ], rdi
mulx rdi, rbp, [ rsi + 0x28 ]
mov [ rsp + 0x168 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x170 ], rbp
mov [ rsp + 0x178 ], rbx
mulx rbx, rbp, r14
adcx r8, r12
adcx rcx, r9
mov rdx, r10
mulx r14, r10, [ rsi + 0x20 ]
add rbp, [ rsp + 0x100 ]
adcx rbx, [ rsp + 0xf8 ]
xor r12, r12
adox rbp, [ rsp + 0x148 ]
adox rbx, [ rsp + 0x130 ]
mov r9, [ rax + 0x8 ]
mov r12, r9
shl r12, 0x1
xchg rdx, r13
mov [ rsp + 0x180 ], rcx
mulx rcx, r9, [ rsi + 0x40 ]
mov [ rsp + 0x188 ], r8
mov r8, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x190 ], rbx
mov [ rsp + 0x198 ], rbp
mulx rbp, rbx, r13
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x1a0 ], r14
mov [ rsp + 0x1a8 ], r10
mulx r10, r14, r11
xor rdx, rdx
adox r9, rbx
adox rbp, rcx
mov rdx, [ rsi + 0x40 ]
mulx rcx, r11, r12
adcx r11, [ rsp + 0xd0 ]
adcx rcx, [ rsp + 0xb8 ]
test al, al
adox r11, r14
adox r10, rcx
adcx r11, [ rsp + 0xb0 ]
adcx r10, [ rsp + 0xa8 ]
mov rdx, [ rsi + 0x28 ]
mulx rbx, r12, r8
mov rdx, [ rsp + 0x178 ]
mov r14, rdx
xor rcx, rcx
adox r14, [ rsp + 0xc8 ]
mov [ rsp + 0x1b0 ], rbp
mov rbp, [ rsp + 0x160 ]
adox rbp, [ rsp + 0xc0 ]
adcx r11, [ rsp + 0x128 ]
adcx r10, [ rsp + 0x120 ]
test al, al
adox r11, [ rsp + 0xf0 ]
adox r10, [ rsp + 0xe8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1b8 ], r9
mulx r9, rcx, r15
adcx r14, [ rsp + 0xe0 ]
adcx rbp, [ rsp + 0xd8 ]
xor rdx, rdx
adox r14, r12
adox rbx, rbp
adcx r14, [ rsp + 0x1a8 ]
adcx rbx, [ rsp + 0x1a0 ]
mov rdx, [ rax + 0x0 ]
mulx rbp, r12, [ rsi + 0x8 ]
mov rdx, [ rsp + 0x198 ]
test al, al
adox rdx, [ rsp + 0x170 ]
mov [ rsp + 0x1c0 ], r10
mov r10, [ rsp + 0x190 ]
adox r10, [ rsp + 0x168 ]
mov [ rsp + 0x1c8 ], r11
mov r11, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1d0 ], rbp
mov [ rsp + 0x1d8 ], r12
mulx r12, rbp, r13
adcx r14, rcx
adcx r9, rbx
mov rdx, [ rsi + 0x20 ]
mulx rbx, rcx, r8
xor rdx, rdx
adox r11, rcx
adox rbx, r10
adcx r11, rbp
adcx r12, rbx
mov rdx, [ rsi + 0x10 ]
mulx rbp, r10, r13
mov rdx, [ rsi + 0x10 ]
mulx rcx, r13, r15
xor rdx, rdx
adox r11, r13
adox rcx, r12
adcx r11, [ rsp + 0x1d8 ]
adcx rcx, [ rsp + 0x1d0 ]
mov rdx, [ rsi + 0x0 ]
mulx r12, rbx, [ rax + 0x8 ]
mov rdx, r10
add rdx, [ rsp + 0x1c8 ]
adcx rbp, [ rsp + 0x1c0 ]
mov r10, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x1e0 ], rbp
mulx rbp, r13, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x1e8 ], r10
mov [ rsp + 0x1f0 ], rbp
mulx rbp, r10, [ rax + 0x10 ]
test al, al
adox r11, rbx
adox r12, rcx
adcx r14, [ rsp + 0xa0 ]
adcx r9, [ rsp + 0x88 ]
test al, al
adox r14, r13
adox r9, [ rsp + 0x1f0 ]
adcx r14, r10
adcx rbp, r9
mov rdx, [ rsi + 0x38 ]
mulx rbx, rcx, r8
mov rdx, [ rsp + 0x1e8 ]
test al, al
adox rdx, [ rsp + 0x80 ]
mov r13, [ rsp + 0x1e0 ]
adox r13, [ rsp + 0x78 ]
adcx rdx, [ rsp + 0x70 ]
adcx r13, [ rsp + 0x28 ]
mov r10, 0x3ffffffffffffff 
mov r9, rdx
and r9, r10
xchg rdx, rdi
mov [ rsp + 0x1f8 ], r9
mulx r9, r10, [ rsi + 0x40 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x200 ], r9
mov [ rsp + 0x208 ], r10
mulx r10, r9, r8
shrd rdi, r13, 58
shr r13, 58
test al, al
adox r11, rdi
adox r13, r12
mov rdx, [ rsi + 0x10 ]
mulx r12, r8, [ rax + 0x8 ]
mov rdx, r15
mulx rdi, r15, [ rsi + 0x40 ]
mov [ rsp + 0x210 ], rbx
mov rbx, r11
shrd rbx, r13, 58
shr r13, 58
mov [ rsp + 0x218 ], rcx
mov rcx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x220 ], rdi
mov [ rsp + 0x228 ], r15
mulx r15, rdi, [ rax + 0x0 ]
test al, al
adox r14, rbx
adox r13, rbp
mov rdx, r9
adcx rdx, [ rsp + 0x188 ]
adcx r10, [ rsp + 0x180 ]
mov rbp, rdx
mov rdx, [ rsi + 0x20 ]
mulx rbx, r9, rcx
xor rdx, rdx
adox rbp, [ rsp + 0x158 ]
adox r10, [ rsp + 0x150 ]
adcx rbp, r9
adcx rbx, r10
mov r9, 0x3a 
bzhi r10, r11, r9
mov rdx, [ rsi + 0x38 ]
mulx r9, r11, [ rax + 0x0 ]
adox rbp, rdi
adox r15, rbx
xor rdx, rdx
adox rbp, r8
adox r12, r15
adcx rbp, [ rsp + 0x20 ]
adcx r12, [ rsp + 0x18 ]
mov r8, 0x3ffffffffffffff 
mov rdi, r14
and rdi, r8
mov rdx, rcx
mulx rbx, rcx, [ rsi + 0x28 ]
mov r15, r11
adox r15, [ rsp + 0x228 ]
adox r9, [ rsp + 0x220 ]
mov r11, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x230 ], rdi
mulx rdi, r8, [ rsi + 0x0 ]
adcx rbp, r8
adcx rdi, r12
shrd r14, r13, 58
shr r13, 58
mov rdx, [ rsi + 0x20 ]
mulx r8, r12, [ rax + 0x0 ]
xor rdx, rdx
adox rbp, r14
adox r13, rdi
mov rdi, [ rsp + 0x218 ]
mov r14, rdi
adcx r14, [ rsp + 0x208 ]
mov [ rsp + 0x238 ], r10
mov r10, [ rsp + 0x210 ]
adcx r10, [ rsp + 0x200 ]
xor rdi, rdi
adox r14, [ rsp + 0x140 ]
adox r10, [ rsp + 0x138 ]
mov rdx, r11
mulx rdi, r11, [ rsi + 0x30 ]
adcx r14, rcx
adcx rbx, r10
xor rdx, rdx
adox r14, r12
adox r8, rbx
mov rdx, [ rsi + 0x10 ]
mulx r12, rcx, [ rax + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mulx rbx, r10, [ rax + 0x28 ]
adcx r14, [ rsp + 0x10 ]
adcx r8, [ rsp + 0x8 ]
mov rdx, r11
add rdx, [ rsp + 0x1b8 ]
adcx rdi, [ rsp + 0x1b0 ]
mov r11, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x240 ], rbx
mov [ rsp + 0x248 ], r10
mulx r10, rbx, [ rax + 0x8 ]
xor rdx, rdx
adox r11, [ rsp + 0x68 ]
adox rdi, [ rsp + 0x60 ]
adcx r11, rbx
adcx r10, rdi
mov rdx, [ rax + 0x0 ]
mulx rdi, rbx, [ rsi + 0x30 ]
mov rdx, 0x3ffffffffffffff 
mov [ rsp + 0x250 ], r9
mov r9, rbp
and r9, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x258 ], r15
mov [ rsp + 0x260 ], rdi
mulx rdi, r15, [ rax + 0x10 ]
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x18 ], r9
adox r14, [ rsp + 0x0 ]
adox r8, [ rsp - 0x8 ]
adcx r14, [ rsp - 0x10 ]
adcx r8, [ rsp - 0x18 ]
mov r9, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x268 ], rdi
mov [ rsp + 0x270 ], r15
mulx r15, rdi, [ rsi + 0x0 ]
xor rdx, rdx
adox r14, rdi
adox r15, r8
adcx r11, [ rsp + 0x38 ]
adcx r10, [ rsp + 0x30 ]
shrd rbp, r13, 58
shr r13, 58
test al, al
adox r14, rbp
adox r13, r15
mov r8, [ rsp + 0x48 ]
adcx r8, [ rsp - 0x20 ]
mov rdi, [ rsp + 0x40 ]
adcx rdi, [ rsp - 0x28 ]
xor r15, r15
adox r11, rcx
adox r12, r10
mov rdx, [ rax + 0x28 ]
mulx r10, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mulx r15, rbp, [ rax + 0x8 ]
adcx r11, [ rsp - 0x40 ]
adcx r12, [ rsp - 0x48 ]
mov rdx, rbx
test al, al
adox rdx, [ rsp + 0x118 ]
mov r9, [ rsp + 0x110 ]
adox r9, [ rsp + 0x260 ]
adcx r11, rcx
adcx r10, r12
test al, al
adox rdx, rbp
adox r15, r9
adcx rdx, [ rsp + 0x270 ]
adcx r15, [ rsp + 0x268 ]
mov rbx, rdx
mov rdx, [ rax + 0x20 ]
mulx rbp, rcx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, r12, [ rax + 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x278 ], rbp
mov [ rsp + 0x280 ], rcx
mulx rcx, rbp, [ rsi + 0x20 ]
mov rdx, r14
shrd rdx, r13, 58
shr r13, 58
test al, al
adox rbx, r12
adox r9, r15
mov r15, 0x3ffffffffffffff 
and r14, r15
adox r11, rdx
adox r13, r10
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x20 ], r14
mov r12, r11
and r12, r15
mov rdx, [ rax + 0x30 ]
mulx r15, r14, [ rsi + 0x0 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x288 ], r12
mulx r12, r10, [ rsi + 0x18 ]
mov rdx, [ rsp + 0x98 ]
mov [ rsp + 0x290 ], r12
mov r12, rdx
adox r12, [ rsp + 0x258 ]
mov [ rsp + 0x298 ], r10
mov r10, [ rsp + 0x90 ]
adox r10, [ rsp + 0x250 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x2a0 ], rdi
mov [ rsp + 0x2a8 ], r8
mulx r8, rdi, [ rax + 0x10 ]
adcx r12, rdi
adcx r8, r10
mov rdx, [ rax + 0x18 ]
mulx rdi, r10, [ rsi + 0x28 ]
test al, al
adox r12, rbp
adox rcx, r8
adcx rbx, [ rsp - 0x30 ]
adcx r9, [ rsp - 0x38 ]
mov rdx, [ rax + 0x28 ]
mulx r8, rbp, [ rsi + 0x8 ]
test al, al
adox rbx, rbp
adox r8, r9
shrd r11, r13, 58
shr r13, 58
mov rdx, [ rax + 0x30 ]
mulx rbp, r9, [ rsi + 0x8 ]
xor rdx, rdx
adox rbx, r14
adox r15, r8
mov rdx, [ rax + 0x30 ]
mulx r8, r14, [ rsi + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x2b0 ], rbp
mov [ rsp + 0x2b8 ], r9
mulx r9, rbp, [ rsi + 0x30 ]
mov rdx, rbp
adcx rdx, [ rsp + 0x2a8 ]
adcx r9, [ rsp + 0x2a0 ]
test al, al
adox rdx, r10
adox rdi, r9
mov r10, rdx
mov rdx, [ rax + 0x40 ]
mulx r9, rbp, [ rsi + 0x0 ]
adcx r10, [ rsp + 0x280 ]
adcx rdi, [ rsp + 0x278 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x2c0 ], r15
mov [ rsp + 0x2c8 ], rbx
mulx rbx, r15, [ rsi + 0x18 ]
add r10, r15
adcx rbx, rdi
test al, al
adox r12, [ rsp + 0x298 ]
adox rcx, [ rsp + 0x290 ]
adcx r10, r14
adcx r8, rbx
mov rdx, [ rsi + 0x8 ]
mulx rdi, r14, [ rax + 0x38 ]
test al, al
adox r12, [ rsp + 0x248 ]
adox rcx, [ rsp + 0x240 ]
adcx r10, r14
adcx rdi, r8
add r10, rbp
adcx r9, rdi
mov rdx, r11
xor rbp, rbp
adox rdx, [ rsp + 0x2c8 ]
adox r13, [ rsp + 0x2c0 ]
mov r11, 0x3a 
bzhi r15, rdx, r11
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x30 ], r15
shrd rdx, r13, 58
shr r13, 58
xor r8, r8
adox r12, [ rsp + 0x2b8 ]
adox rcx, [ rsp + 0x2b0 ]
adcx r12, [ rsp + 0x58 ]
adcx rcx, [ rsp + 0x50 ]
add r12, rdx
adcx r13, rcx
mov rbp, r12
shrd rbp, r13, 58
shr r13, 58
test al, al
adox r10, rbp
adox r13, r9
mov r14, r10
shrd r14, r13, 57
shr r13, 57
xor rdi, rdi
adox r14, [ rsp + 0x1f8 ]
adox r13, rdi
mov r8, r14
shrd r8, r13, 58
add r8, [ rsp + 0x238 ]
bzhi r9, r12, r11
mov [ rbx + 0x38 ], r9
bzhi r15, r8, r11
shr r8, 58
add r8, [ rsp + 0x230 ]
mov [ rbx + 0x10 ], r8
mov rdx, [ rsp + 0x288 ]
mov [ rbx + 0x28 ], rdx
mov rdx, 0x1ffffffffffffff 
and r10, rdx
bzhi rcx, r14, r11
mov [ rbx + 0x40 ], r10
mov [ rbx + 0x8 ], r15
mov [ rbx + 0x0 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 848
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.1314
; seed 3777850834727325 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 7161829 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=65, initial num_batches=31): 138530 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.019342824298094804
; number reverted permutation / tried permutation: 54913 / 89767 =61.173%
; number reverted decision / tried decision: 39131 / 90232 =43.367%
; validated in 4.456s
