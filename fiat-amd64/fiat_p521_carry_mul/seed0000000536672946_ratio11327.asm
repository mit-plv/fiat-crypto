SECTION .text
	GLOBAL fiat_p521_carry_mul
fiat_p521_carry_mul:
sub rsp, 872
mov rax, [ rdx + 0x28 ]
mov r10, rax
shl r10, 0x1
mov rax, [ rdx + 0x20 ]
mov r11, rax
shl r11, 0x1
mov rax, rdx
mov rdx, [ rsi + 0x40 ]
mulx r8, rcx, r11
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x38 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x78 ], rbp
mov rbp, rdx
shl rbp, 0x1
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rbp
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r15
mulx r15, rdi, rbp
imul rdx, [ rax + 0x8 ], 0x2
mov [ rsp - 0x40 ], r14
mov r14, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x38 ], r15
mov [ rsp - 0x30 ], rdi
mulx rdi, r15, rbp
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x28 ], r13
mov [ rsp - 0x20 ], r12
mulx r12, r13, [ rax + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x18 ], r12
mov [ rsp - 0x10 ], r13
mulx r13, r12, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x8 ], r13
mov r13, rdx
shl r13, 0x1
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x0 ], r12
mov [ rsp + 0x8 ], rdi
mulx rdi, r12, [ rax + 0x0 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x10 ], rdi
mov [ rsp + 0x18 ], r12
mulx r12, rdi, r13
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x20 ], r15
mov [ rsp + 0x28 ], r11
mulx r11, r15, [ rsi + 0x10 ]
mov rdx, 0x1 
mov [ rsp + 0x30 ], r11
shlx r11, [ rax + 0x40 ], rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x38 ], r15
mov [ rsp + 0x40 ], r14
mulx r14, r15, [ rsi + 0x8 ]
mov rdx, r11
mov [ rsp + 0x48 ], r14
mulx r14, r11, [ rsi + 0x40 ]
mov [ rsp + 0x50 ], r15
mov [ rsp + 0x58 ], r12
mulx r12, r15, [ rsi + 0x30 ]
mov [ rsp + 0x60 ], r12
mov [ rsp + 0x68 ], r15
mulx r15, r12, [ rsi + 0x38 ]
mov [ rsp + 0x70 ], r15
mov r15, rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x78 ], r12
mov [ rsp + 0x80 ], rdi
mulx rdi, r12, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x88 ], rdi
mov [ rsp + 0x90 ], r12
mulx r12, rdi, r15
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x98 ], r12
mov [ rsp + 0xa0 ], rdi
mulx rdi, r12, [ rax + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0xa8 ], rdi
mov [ rsp + 0xb0 ], r12
mulx r12, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xb8 ], r12
mov [ rsp + 0xc0 ], rdi
mulx rdi, r12, [ rax + 0x8 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xc8 ], rdi
mov [ rsp + 0xd0 ], r12
mulx r12, rdi, r10
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xd8 ], r14
mov [ rsp + 0xe0 ], r11
mulx r11, r14, [ rax + 0x38 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0xe8 ], r11
mov r11, rdx
shl r11, 0x1
mov rdx, r11
mov [ rsp + 0xf0 ], r14
mulx r14, r11, [ rsi + 0x38 ]
add rcx, rdi
adcx r12, r8
mov r8, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xf8 ], r12
mulx r12, rdi, r10
mov rdx, r8
mov [ rsp + 0x100 ], r12
mulx r12, r8, [ rsi + 0x30 ]
mov [ rsp + 0x108 ], rdi
mov rdi, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x110 ], rcx
mov [ rsp + 0x118 ], r12
mulx r12, rcx, [ rsi + 0x20 ]
mov rdx, rdi
mov [ rsp + 0x120 ], r12
mulx r12, rdi, [ rsi + 0x28 ]
mov [ rsp + 0x128 ], rcx
mov rcx, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x130 ], r12
mov [ rsp + 0x138 ], rdi
mulx rdi, r12, [ rsi + 0x10 ]
mov rdx, rcx
mov [ rsp + 0x140 ], rdi
mulx rdi, rcx, [ rsi + 0x40 ]
mov [ rsp + 0x148 ], r12
mov r12, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x150 ], rdi
mov [ rsp + 0x158 ], rcx
mulx rcx, rdi, r10
mov rdx, r10
mov [ rsp + 0x160 ], r8
mulx r8, r10, [ rsi + 0x28 ]
mov [ rsp + 0x168 ], r8
mov r8, r9
add r8, [ rsp + 0xe0 ]
adcx rbx, [ rsp + 0xd8 ]
xchg rdx, r15
mov [ rsp + 0x170 ], rbx
mulx rbx, r9, [ rsi + 0x28 ]
mov [ rsp + 0x178 ], rbx
xor rbx, rbx
adox rdi, r11
adox r14, rcx
mov r11, rdx
mov rdx, [ rsi + 0x30 ]
mulx rbx, rcx, r15
mov rdx, 0x1 
shlx r15, [ rax + 0x18 ], rdx
mov rdx, [ rsp + 0x110 ]
adcx rdx, [ rsp + 0x160 ]
mov [ rsp + 0x180 ], r9
mov r9, [ rsp + 0xf8 ]
adcx r9, [ rsp + 0x118 ]
mov [ rsp + 0x188 ], r8
mov r8, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x190 ], r14
mov [ rsp + 0x198 ], rdi
mulx rdi, r14, r15
mov rdx, r14
mov [ rsp + 0x1a0 ], rbx
xor rbx, rbx
adox rdx, [ rsp + 0x80 ]
adox rdi, [ rsp + 0x58 ]
mov r14, rdx
mov rdx, [ rsp + 0x40 ]
mov [ rsp + 0x1a8 ], rcx
mulx rcx, rbx, [ rsi + 0x40 ]
mov rdx, r15
mov [ rsp + 0x1b0 ], r10
mulx r10, r15, [ rsi + 0x40 ]
mov [ rsp + 0x1b8 ], r10
mov r10, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x1c0 ], r15
mov [ rsp + 0x1c8 ], rdi
mulx rdi, r15, r13
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x1d0 ], r14
mulx r14, r13, r10
adcx rbx, r15
adcx rdi, rcx
mov rdx, [ rsi + 0x40 ]
mulx rcx, r10, rbp
add r10, [ rsp + 0x78 ]
adcx rcx, [ rsp + 0x70 ]
xor rdx, rdx
adox rbx, r13
adox r14, rdi
mov rdx, [ rax + 0x0 ]
mulx r13, r15, [ rsi + 0x30 ]
adcx r10, r15
adcx r13, rcx
mov rdx, [ rsi + 0x28 ]
mulx rcx, rdi, [ rsp + 0x28 ]
xor rdx, rdx
adox r8, [ rsp + 0x20 ]
adox r9, [ rsp + 0x8 ]
mov rdx, r11
mulx r15, r11, [ rsi + 0x20 ]
adcx r8, r11
adcx r15, r9
mov r9, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1d8 ], r13
mulx r13, r11, r12
add rbx, rdi
adcx rcx, r14
mov rdx, [ rsi + 0x30 ]
mulx rdi, r14, [ rsp + 0x28 ]
test al, al
adox rbx, [ rsp + 0x108 ]
adox rcx, [ rsp + 0x100 ]
adcx rbx, r11
adcx r13, rcx
xor rdx, rdx
adox rbx, [ rsp - 0x20 ]
adox r13, [ rsp - 0x28 ]
mov rdx, r9
mulx r11, r9, [ rsi + 0x8 ]
mov [ rsp + 0x1e0 ], r10
mulx r10, rcx, [ rsi + 0x10 ]
adcx rbx, r9
adcx r11, r13
mov rdx, [ rsi + 0x20 ]
mulx r9, r13, r12
mov rdx, r14
test al, al
adox rdx, [ rsp + 0x1d0 ]
adox rdi, [ rsp + 0x1c8 ]
mov r12, rdx
mov rdx, [ rsp + 0x28 ]
mov [ rsp + 0x1e8 ], r15
mulx r15, r14, [ rsi + 0x38 ]
adcx r12, [ rsp + 0x1b0 ]
adcx rdi, [ rsp + 0x168 ]
test al, al
adox r12, r13
adox r9, rdi
mov rdx, [ rsi + 0x18 ]
mulx rdi, r13, rbp
adcx r12, r13
adcx rdi, r9
xor rdx, rdx
adox rbx, [ rsp + 0x18 ]
adox r11, [ rsp + 0x10 ]
adcx r12, rcx
adcx r10, rdi
mov rcx, r14
add rcx, [ rsp + 0x1c0 ]
adcx r15, [ rsp + 0x1b8 ]
xor r14, r14
adox rcx, [ rsp + 0x1a8 ]
adox r15, [ rsp + 0x1a0 ]
mov rdx, [ rax + 0x8 ]
mulx r13, r9, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx r14, rdi, [ rax + 0x0 ]
adcx r12, rdi
adcx r14, r10
test al, al
adox r12, r9
adox r13, r14
mov rdx, [ rsi + 0x8 ]
mulx r9, r10, [ rax + 0x8 ]
adcx rcx, [ rsp + 0x138 ]
adcx r15, [ rsp + 0x130 ]
mov rdx, [ rax + 0x0 ]
mulx r14, rdi, [ rsi + 0x18 ]
mov rdx, 0x3ffffffffffffff 
mov [ rsp + 0x1f0 ], r9
mov r9, rbx
and r9, rdx
adox rcx, [ rsp - 0x30 ]
adox r15, [ rsp - 0x38 ]
mov rdx, rbp
mov [ rsp + 0x1f8 ], r9
mulx r9, rbp, [ rsi + 0x38 ]
mov [ rsp + 0x200 ], r9
mov r9, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x208 ], rbp
mov [ rsp + 0x210 ], r10
mulx r10, rbp, [ rax + 0x10 ]
adcx r8, rdi
adcx r14, [ rsp + 0x1e8 ]
shrd rbx, r11, 58
shr r11, 58
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x218 ], r10
mulx r10, rdi, [ rsi + 0x0 ]
xor rdx, rdx
adox r12, rbx
adox r11, r13
adcx rcx, [ rsp + 0xa0 ]
adcx r15, [ rsp + 0x98 ]
xor r13, r13
adox rcx, [ rsp + 0xc0 ]
adox r15, [ rsp + 0xb8 ]
adcx rcx, [ rsp + 0x210 ]
adcx r15, [ rsp + 0x1f0 ]
mov rdx, 0x3a 
bzhi rbx, r12, rdx
mov rdx, r9
mulx r13, r9, [ rsi + 0x30 ]
mov rdx, r9
adox rdx, [ rsp + 0x198 ]
adox r13, [ rsp + 0x190 ]
shrd r12, r11, 58
shr r11, 58
test al, al
adox rcx, [ rsp + 0x0 ]
adox r15, [ rsp - 0x8 ]
mov r9, [ rsp + 0x208 ]
mov [ rsp + 0x220 ], rbx
mov rbx, r9
adcx rbx, [ rsp + 0x158 ]
mov [ rsp + 0x228 ], rbp
mov rbp, [ rsp + 0x200 ]
adcx rbp, [ rsp + 0x150 ]
test al, al
adox rcx, r12
adox r11, r15
adcx r8, [ rsp + 0x38 ]
adcx r14, [ rsp + 0x30 ]
mov r9, 0x3a 
bzhi r12, rcx, r9
shrd rcx, r11, 58
shr r11, 58
mov r15, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x230 ], r12
mulx r12, r9, [ rax + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x238 ], rbp
mov [ rsp + 0x240 ], rbx
mulx rbx, rbp, [ rsi + 0x28 ]
add r8, r9
adcx r12, r14
mov rdx, [ rax + 0x8 ]
mulx r9, r14, [ rsi + 0x30 ]
mov rdx, r14
add rdx, [ rsp + 0x188 ]
adcx r9, [ rsp + 0x170 ]
mov r14, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x248 ], rbx
mov [ rsp + 0x250 ], rbp
mulx rbp, rbx, [ rax + 0x28 ]
test al, al
adox r15, [ rsp + 0x180 ]
adox r13, [ rsp + 0x178 ]
adcx r8, rdi
adcx r10, r12
test al, al
adox r8, rcx
adox r11, r10
mov rdx, r8
shrd rdx, r11, 58
shr r11, 58
mov rdi, rdx
mov rdx, [ rsi + 0x28 ]
mulx r12, rcx, [ rax + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x258 ], rbp
mulx rbp, r10, [ rsi + 0x40 ]
mov rdx, 0x3a 
mov [ rsp + 0x260 ], rbp
bzhi rbp, r8, rdx
adox r14, rcx
adox r12, r9
mov r9, [ rsp + 0x68 ]
mov r8, r9
add r8, [ rsp + 0x240 ]
mov rcx, [ rsp + 0x60 ]
adcx rcx, [ rsp + 0x238 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x268 ], rbp
mulx rbp, r9, [ rax + 0x28 ]
mov rdx, [ rsp + 0x1e0 ]
mov [ rsp + 0x270 ], r10
xor r10, r10
adox rdx, [ rsp - 0x40 ]
mov [ rsp + 0x278 ], r12
mov r12, [ rsp + 0x1d8 ]
adox r12, [ rsp - 0x48 ]
mov r10, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x280 ], r14
mov [ rsp + 0x288 ], rbx
mulx rbx, r14, [ rax + 0x10 ]
adcx r8, [ rsp + 0x250 ]
adcx rcx, [ rsp + 0x248 ]
test al, al
adox r15, [ rsp + 0xb0 ]
adox r13, [ rsp + 0xa8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x290 ], rbp
mov [ rsp + 0x298 ], r9
mulx r9, rbp, [ rsi + 0x18 ]
adcx r10, [ rsp - 0x10 ]
adcx r12, [ rsp - 0x18 ]
test al, al
adox r15, rbp
adox r9, r13
adcx r8, [ rsp + 0x128 ]
adcx rcx, [ rsp + 0x120 ]
test al, al
adox r15, r14
adox rbx, r9
mov rdx, [ rsi + 0x10 ]
mulx r13, r14, [ rax + 0x18 ]
adcx r15, [ rsp + 0x50 ]
adcx rbx, [ rsp + 0x48 ]
mov rdx, [ rax + 0x20 ]
mulx r9, rbp, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x2a0 ], r9
mov [ rsp + 0x2a8 ], rbp
mulx rbp, r9, [ rax + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x2b0 ], r13
mov [ rsp + 0x2b8 ], r14
mulx r14, r13, [ rsi + 0x0 ]
add r10, r9
adcx rbp, r12
add r15, r13
adcx r14, rbx
test al, al
adox r15, rdi
adox r11, r14
adcx r8, [ rsp + 0x228 ]
adcx rcx, [ rsp + 0x218 ]
test al, al
adox r8, [ rsp + 0x2b8 ]
adox rcx, [ rsp + 0x2b0 ]
adcx r8, [ rsp + 0x2a8 ]
adcx rcx, [ rsp + 0x2a0 ]
test al, al
adox r10, [ rsp + 0x148 ]
adox rbp, [ rsp + 0x140 ]
adcx r10, [ rsp + 0x298 ]
adcx rbp, [ rsp + 0x290 ]
mov rdx, 0x3ffffffffffffff 
mov rdi, r15
and rdi, rdx
mov rdx, [ rsi + 0x28 ]
mulx rbx, r12, [ rax + 0x18 ]
adox r8, [ rsp + 0x288 ]
adox rcx, [ rsp + 0x258 ]
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x20 ], rdi
shrd r15, r11, 58
shr r11, 58
mov r9, rdx
mov rdx, [ rax + 0x38 ]
mulx r14, r13, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, rdi, [ rax + 0x20 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x2c0 ], r14
mov [ rsp + 0x2c8 ], r13
mulx r13, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x2d0 ], rbx
mov [ rsp + 0x2d8 ], r12
mulx r12, rbx, [ rax + 0x10 ]
test al, al
adox r10, r14
adox r13, rbp
mov rdx, [ rax + 0x18 ]
mulx r14, rbp, [ rsi + 0x20 ]
mov rdx, rbp
adcx rdx, [ rsp + 0x280 ]
adcx r14, [ rsp + 0x278 ]
xor rbp, rbp
adox r8, r15
adox r11, rcx
mov rcx, r8
shrd rcx, r11, 58
shr r11, 58
mov r15, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x2e0 ], r13
mulx r13, rbp, [ rax + 0x28 ]
xor rdx, rdx
adox r15, rdi
adox r9, r14
adcx r15, rbp
adcx r13, r9
test al, al
adox r15, [ rsp + 0x90 ]
adox r13, [ rsp + 0x88 ]
mov rdi, [ rsp + 0x270 ]
adcx rdi, [ rsp + 0xd0 ]
mov r14, [ rsp + 0x260 ]
adcx r14, [ rsp + 0xc8 ]
xor rbp, rbp
adox rdi, rbx
adox r12, r14
adcx rdi, [ rsp + 0x2d8 ]
adcx r12, [ rsp + 0x2d0 ]
mov rdx, [ rax + 0x30 ]
mulx r9, rbx, [ rsi + 0x10 ]
xor rdx, rdx
adox r10, rcx
adox r11, [ rsp + 0x2e0 ]
mov rbp, r10
shrd rbp, r11, 58
shr r11, 58
xor rcx, rcx
adox r15, [ rsp + 0x2c8 ]
adox r13, [ rsp + 0x2c0 ]
adcx r15, rbp
adcx r11, r13
mov rdx, [ rax + 0x20 ]
mulx rbp, r14, [ rsi + 0x20 ]
test al, al
adox rdi, r14
adox rbp, r12
mov rdx, [ rsi + 0x18 ]
mulx r13, r12, [ rax + 0x28 ]
mov rdx, 0x3ffffffffffffff 
mov r14, r15
and r14, rdx
adox rdi, r12
adox r13, rbp
adcx rdi, rbx
adcx r9, r13
test al, al
adox rdi, [ rsp + 0xf0 ]
adox r9, [ rsp + 0xe8 ]
mov rdx, [ rax + 0x40 ]
mulx rbp, rbx, [ rsi + 0x0 ]
adcx rdi, rbx
adcx rbp, r9
shrd r15, r11, 58
shr r11, 58
xor rdx, rdx
adox rdi, r15
adox r11, rbp
mov rcx, rdi
shrd rcx, r11, 57
shr r11, 57
mov r12, 0x39 
bzhi r13, rdi, r12
adox rcx, [ rsp + 0x1f8 ]
adox r11, rdx
mov r9, 0x3ffffffffffffff 
mov rbx, rcx
and rbx, r9
shrd rcx, r11, 58
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x0 ], rbx
add rcx, [ rsp + 0x220 ]
and r10, r9
mov r15, [ rsp + 0x268 ]
mov [ rbp + 0x18 ], r15
mov [ rbp + 0x30 ], r10
mov r15, rcx
shr r15, 58
add r15, [ rsp + 0x230 ]
and r8, r9
mov [ rbp + 0x10 ], r15
and rcx, r9
mov [ rbp + 0x8 ], rcx
mov [ rbp + 0x38 ], r14
mov [ rbp + 0x28 ], r8
mov [ rbp + 0x40 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 872
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.1327
; seed 2623009681325715 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 6039927 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=65, initial num_batches=31): 113500 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.018791617845712375
; number reverted permutation / tried permutation: 54802 / 89539 =61.205%
; number reverted decision / tried decision: 43990 / 90460 =48.629%
; validated in 3.336s
