SECTION .text
	GLOBAL fiat_p521_carry_mul
fiat_p521_carry_mul:
sub rsp, 864
mov rax, rdx
mov rdx, [ rdx + 0x8 ]
mulx r11, r10, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mulx r8, rcx, [ rax + 0x0 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x8 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x78 ], rbp
lea rbp, [rdx + rdx]
mov rdx, 0x1 
mov [ rsp - 0x70 ], r12
shlx r12, [ rax + 0x30 ], rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x28 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x48 ], rbx
mov [ rsp - 0x40 ], r9
mulx r9, rbx, [ rsi + 0x10 ]
mov rdx, [ rax + 0x40 ]
mov [ rsp - 0x38 ], r9
mov r9, rdx
shl r9, 0x1
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x30 ], rbx
mov [ rsp - 0x28 ], rdi
mulx rdi, rbx, [ rax + 0x0 ]
mov rdx, 0x1 
mov [ rsp - 0x20 ], r15
shlx r15, [ rax + 0x38 ], rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x18 ], r14
mov [ rsp - 0x10 ], r13
mulx r13, r14, [ rax + 0x20 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x8 ], r13
lea r13, [rdx + rdx]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x0 ], r14
mov [ rsp + 0x8 ], r8
mulx r8, r14, r9
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x10 ], rcx
mov [ rsp + 0x18 ], r11
mulx r11, rcx, r15
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x20 ], r10
mov [ rsp + 0x28 ], r8
mulx r8, r10, r15
mov rdx, rbp
mov [ rsp + 0x30 ], r14
mulx r14, rbp, [ rsi + 0x28 ]
mov [ rsp + 0x38 ], rdi
mov rdi, [ rax + 0x18 ]
mov [ rsp + 0x40 ], rbx
lea rbx, [rdi + rdi]
mov rdi, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x48 ], r11
mov [ rsp + 0x50 ], rcx
mulx rcx, r11, r13
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x58 ], r14
mov [ rsp + 0x60 ], rbp
mulx rbp, r14, rbx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x68 ], r8
mov [ rsp + 0x70 ], r10
mulx r10, r8, rbx
mov rdx, rbx
mov [ rsp + 0x78 ], rcx
mulx rcx, rbx, [ rsi + 0x40 ]
mov rdx, 0x1 
mov [ rsp + 0x80 ], r11
shlx r11, [ rax + 0x8 ], rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x88 ], rbp
mov [ rsp + 0x90 ], r14
mulx r14, rbp, r12
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x98 ], r14
mov [ rsp + 0xa0 ], rbp
mulx rbp, r14, [ rax + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0xa8 ], rbp
mov [ rsp + 0xb0 ], r14
mulx r14, rbp, [ rsi + 0x28 ]
mov rdx, r13
mov [ rsp + 0xb8 ], r14
mulx r14, r13, [ rsi + 0x40 ]
xchg rdx, rdi
mov [ rsp + 0xc0 ], rbp
mov [ rsp + 0xc8 ], r14
mulx r14, rbp, [ rsi + 0x38 ]
mov [ rsp + 0xd0 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xd8 ], r14
mov [ rsp + 0xe0 ], rbp
mulx rbp, r14, [ rax + 0x18 ]
mov rdx, 0x1 
mov [ rsp + 0xe8 ], rbp
shlx rbp, [ rax + 0x10 ], rdx
mov rdx, r9
mov [ rsp + 0xf0 ], r14
mulx r14, r9, [ rsi + 0x18 ]
xchg rdx, r11
mov [ rsp + 0xf8 ], r14
mov [ rsp + 0x100 ], r9
mulx r9, r14, [ rsi + 0x40 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x108 ], rcx
mov [ rsp + 0x110 ], rbx
mulx rbx, rcx, rbp
xor rdx, rdx
adox r14, rcx
adox rbx, r9
adcx r14, r8
adcx r10, rbx
mov rdx, rbp
mulx r8, rbp, [ rsi + 0x40 ]
mov rdx, [ rsi + 0x40 ]
mulx rcx, r9, [ rax + 0x0 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x118 ], r8
mulx r8, rbx, [ rax + 0x8 ]
xor rdx, rdx
adox r9, rbx
adox r8, rcx
mov rdx, rdi
mulx rcx, rdi, [ rsi + 0x38 ]
mov [ rsp + 0x120 ], r8
mulx r8, rbx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x128 ], r9
mov [ rsp + 0x130 ], rbp
mulx rbp, r9, r12
mov rdx, rdi
adcx rdx, [ rsp + 0x110 ]
adcx rcx, [ rsp + 0x108 ]
mov rdi, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x138 ], rcx
mov [ rsp + 0x140 ], rbp
mulx rbp, rcx, r12
xor rdx, rdx
adox r14, rbx
adox r8, r10
mov rdx, [ rsi + 0x20 ]
mulx rbx, r10, r13
adcx r14, r10
adcx rbx, r8
xor rdx, rdx
adox r14, r9
adox rbx, [ rsp + 0x140 ]
mov rdx, r15
mulx r9, r15, [ rsi + 0x38 ]
mulx r10, r8, [ rsi + 0x10 ]
adcx r14, r8
adcx r10, rbx
mov rbx, [ rsp + 0x130 ]
test al, al
adox rbx, [ rsp + 0x90 ]
mov r8, [ rsp + 0x118 ]
adox r8, [ rsp + 0x88 ]
mov [ rsp + 0x148 ], r9
mov r9, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x150 ], r15
mov [ rsp + 0x158 ], r8
mulx r8, r15, [ rax + 0x0 ]
mov rdx, r11
mov [ rsp + 0x160 ], rbx
mulx rbx, r11, [ rsi + 0x8 ]
adcx r14, r11
adcx rbx, r10
test al, al
adox r14, r15
adox r8, rbx
xchg rdx, r13
mulx r15, r10, [ rsi + 0x30 ]
adcx rdi, r10
adcx r15, [ rsp + 0x138 ]
mov r11, rdx
mov rdx, [ rsi + 0x0 ]
mulx r10, rbx, [ rax + 0x8 ]
xor rdx, rdx
adox rdi, rcx
adox rbp, r15
mov rcx, [ rsp + 0x160 ]
adcx rcx, [ rsp + 0x80 ]
mov r15, [ rsp + 0x158 ]
adcx r15, [ rsp + 0x78 ]
mov [ rsp + 0x168 ], rbp
mov rbp, [ rsp + 0x150 ]
mov [ rsp + 0x170 ], rdi
mov rdi, rbp
add rdi, [ rsp + 0xa0 ]
mov [ rsp + 0x178 ], r10
mov r10, [ rsp + 0x148 ]
adcx r10, [ rsp + 0x98 ]
mov rdx, r13
mulx rbp, r13, [ rsi + 0x30 ]
xchg rdx, r12
mov [ rsp + 0x180 ], rbx
mov [ rsp + 0x188 ], r8
mulx r8, rbx, [ rsi + 0x20 ]
test al, al
adox rdi, r13
adox rbp, r10
mov r10, [ rsp + 0xd0 ]
adcx r10, [ rsp + 0xe0 ]
mov r13, [ rsp + 0xc8 ]
adcx r13, [ rsp + 0xd8 ]
mov [ rsp + 0x190 ], rbp
mov [ rsp + 0x198 ], rdi
mulx rdi, rbp, [ rsi + 0x30 ]
add r10, rbp
adcx rdi, r13
test al, al
adox r10, [ rsp + 0x70 ]
adox rdi, [ rsp + 0x68 ]
xchg rdx, r12
mulx rbp, r13, [ rsi + 0x10 ]
mov [ rsp + 0x1a0 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x1a8 ], r10
mov [ rsp + 0x1b0 ], r14
mulx r14, r10, r11
adcx rcx, [ rsp + 0x60 ]
adcx r15, [ rsp + 0x58 ]
xor rdx, rdx
adox rcx, rbx
adox r8, r15
adcx rcx, [ rsp + 0x50 ]
adcx r8, [ rsp + 0x48 ]
xor r11, r11
adox rcx, r13
adox rbp, r8
mov rdx, r12
mulx rbx, r12, [ rsi + 0x38 ]
adcx r10, r12
adcx rbx, r14
mov rdx, 0x3ffffffffffffff 
mov r13, [ rsp + 0x1b0 ]
and r13, rdx
mov rdx, r9
mulx r14, r9, [ rsi + 0x30 ]
adox rcx, [ rsp + 0x40 ]
adox rbp, [ rsp + 0x38 ]
adcx rcx, [ rsp + 0x180 ]
adcx rbp, [ rsp + 0x178 ]
mov r15, [ rsp + 0x188 ]
mov r8, [ rsp + 0x1b0 ]
shrd r8, r15, 58
shr r15, 58
add rcx, r8
adcx r15, rbp
mov r12, [ rsp + 0x30 ]
mov rbp, r12
test al, al
adox rbp, [ rsp + 0x1a8 ]
mov r8, [ rsp + 0x28 ]
adox r8, [ rsp + 0x1a0 ]
mov r12, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x1b8 ], r13
mulx r13, r11, [ rsi + 0x18 ]
adcx rbp, r11
adcx r13, r8
mov rdx, rcx
shrd rdx, r15, 58
shr r15, 58
mov r8, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x1c0 ], r15
mulx r15, r11, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x1c8 ], r8
mov [ rsp + 0x1d0 ], r15
mulx r15, r8, [ rax + 0x0 ]
test al, al
adox r10, r9
adox r14, rbx
mov rdx, r12
mulx rbx, r12, [ rsi + 0x20 ]
mov r9, r12
adcx r9, [ rsp + 0x170 ]
adcx rbx, [ rsp + 0x168 ]
add rbp, [ rsp + 0x20 ]
adcx r13, [ rsp + 0x18 ]
mov r12, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x1d8 ], rbx
mov [ rsp + 0x1e0 ], r9
mulx r9, rbx, [ rsi + 0x8 ]
mov rdx, rdi
mov [ rsp + 0x1e8 ], r15
mulx r15, rdi, [ rsi + 0x28 ]
mov [ rsp + 0x1f0 ], r8
xor r8, r8
adox r10, rdi
adox r15, r14
adcx r10, r11
adcx r15, [ rsp + 0x1d0 ]
mov r11, rdx
mov rdx, [ rsi + 0x10 ]
mulx rdi, r14, [ rax + 0x10 ]
xor rdx, rdx
adox rbp, rbx
adox r9, r13
mov rdx, [ rsi + 0x18 ]
mulx r13, r8, [ rax + 0x8 ]
adcx r10, r8
adcx r13, r15
mov rdx, [ rsi + 0x40 ]
mulx r15, rbx, r11
add r10, r14
adcx rdi, r13
mov rdx, [ rax + 0x8 ]
mulx r8, r14, [ rsi + 0x8 ]
mov rdx, [ rsp + 0x198 ]
xor r13, r13
adox rdx, [ rsp + 0x10 ]
mov [ rsp + 0x1f8 ], r9
mov r9, [ rsp + 0x190 ]
adox r9, [ rsp + 0x8 ]
adcx rbx, [ rsp + 0x1f0 ]
adcx r15, [ rsp + 0x1e8 ]
mov r13, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x200 ], rbp
mov [ rsp + 0x208 ], r15
mulx r15, rbp, [ rax + 0x0 ]
mov rdx, [ rsp + 0x1e0 ]
mov [ rsp + 0x210 ], rbx
xor rbx, rbx
adox rdx, [ rsp + 0x100 ]
mov [ rsp + 0x218 ], rdi
mov rdi, [ rsp + 0x1d8 ]
adox rdi, [ rsp + 0xf8 ]
mov rbx, 0x3a 
mov [ rsp + 0x220 ], r10
bzhi r10, rcx, rbx
adox rdx, rbp
adox r15, rdi
test al, al
adox rdx, r14
adox r8, r15
mov rcx, rdx
mov rdx, [ rax + 0x8 ]
mulx rbp, r14, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x30 ]
mulx r15, rdi, [ rax + 0x0 ]
adcx r13, r14
adcx rbp, r9
mov rdx, [ rsi + 0x18 ]
mulx r14, r9, [ rax + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x228 ], r10
mulx r10, rbx, [ rsi + 0x10 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x230 ], r8
mov [ rsp + 0x238 ], rcx
mulx rcx, r8, [ rsi + 0x8 ]
add r13, r9
adcx r14, rbp
mov rdx, r11
mulx rbp, r11, [ rsi + 0x38 ]
xor rdx, rdx
adox r13, rbx
adox r10, r14
mov rdx, [ rsi + 0x28 ]
mulx rbx, r9, [ rax + 0x8 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x240 ], rbx
mulx rbx, r14, r12
adcx r14, r11
adcx rbp, rbx
mov rdx, [ rax + 0x8 ]
mulx r11, r12, [ rsi + 0x30 ]
test al, al
adox r13, r8
adox rcx, r10
mov rdx, [ rsi + 0x0 ]
mulx r10, r8, [ rax + 0x18 ]
adcx r14, rdi
adcx r15, rbp
mov rdx, [ rax + 0x10 ]
mulx rbx, rdi, [ rsi + 0x20 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x248 ], rbx
mulx rbx, rbp, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x250 ], rdi
mov [ rsp + 0x258 ], r15
mulx r15, rdi, [ rsi + 0x28 ]
test al, al
adox r13, rbp
adox rbx, rcx
mov rdx, [ rsp + 0x220 ]
adcx rdx, [ rsp - 0x10 ]
mov rcx, [ rsp + 0x218 ]
adcx rcx, [ rsp - 0x18 ]
mov rbp, [ rsp + 0x238 ]
test al, al
adox rbp, [ rsp + 0xb0 ]
mov [ rsp + 0x260 ], r15
mov r15, [ rsp + 0x230 ]
adox r15, [ rsp + 0xa8 ]
adcx rdx, [ rsp + 0x0 ]
adcx rcx, [ rsp - 0x8 ]
mov [ rsp + 0x268 ], rdi
mov rdi, r12
test al, al
adox rdi, [ rsp + 0x210 ]
adox r11, [ rsp + 0x208 ]
adcx rbp, [ rsp + 0x1c8 ]
adcx r15, [ rsp + 0x1c0 ]
mov r12, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x270 ], r11
mov [ rsp + 0x278 ], rdi
mulx rdi, r11, [ rax + 0x28 ]
mov rdx, rbp
shrd rdx, r15, 58
shr r15, 58
mov [ rsp + 0x280 ], rdi
mov rdi, r8
mov [ rsp + 0x288 ], r11
xor r11, r11
adox rdi, [ rsp + 0x200 ]
adox r10, [ rsp + 0x1f8 ]
mov r8, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x290 ], rbx
mulx rbx, r11, [ rsi + 0x10 ]
adcx rdi, r8
adcx r15, r10
mov rdx, rdi
shrd rdx, r15, 58
shr r15, 58
add r12, rdx
adcx r15, rcx
mov rdx, [ rsi + 0x30 ]
mulx r8, rcx, [ rax + 0x10 ]
mov rdx, rcx
xor r10, r10
adox rdx, [ rsp + 0x128 ]
adox r8, [ rsp + 0x120 ]
mov rcx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x298 ], rbx
mulx rbx, r10, [ rax + 0x30 ]
adcx r14, r9
mov rdx, [ rsp + 0x240 ]
adcx rdx, [ rsp + 0x258 ]
mov r9, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x2a0 ], rbx
mov [ rsp + 0x2a8 ], r10
mulx r10, rbx, [ rsi + 0x18 ]
mov rdx, 0x3ffffffffffffff 
mov [ rsp + 0x2b0 ], r11
mov r11, r12
and r11, rdx
shrd r12, r15, 58
shr r15, 58
test al, al
adox r14, [ rsp + 0x250 ]
adox r9, [ rsp + 0x248 ]
and rbp, rdx
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x20 ], r11
adox r14, rbx
adox r10, r9
adcx rcx, [ rsp + 0xc0 ]
adcx r8, [ rsp + 0xb8 ]
xor rbx, rbx
adox r13, r12
adox r15, [ rsp + 0x290 ]
mov r11, [ rsp + 0x268 ]
mov r12, r11
adcx r12, [ rsp + 0x278 ]
mov r9, [ rsp + 0x260 ]
adcx r9, [ rsp + 0x270 ]
test al, al
adox r12, [ rsp + 0xf0 ]
adox r9, [ rsp + 0xe8 ]
mov r11, r13
shrd r11, r15, 58
shr r15, 58
mov rbx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x2b8 ], rbp
mov [ rsp + 0x2c0 ], r15
mulx r15, rbp, [ rax + 0x20 ]
test al, al
adox rcx, rbp
adox r15, r8
mov rdx, [ rax + 0x20 ]
mulx rbp, r8, [ rsi + 0x18 ]
adcx r12, r8
adcx rbp, r9
test al, al
adox r14, [ rsp + 0x2b0 ]
adox r10, [ rsp + 0x298 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, r9, [ rax + 0x38 ]
adcx r14, [ rsp + 0x288 ]
adcx r10, [ rsp + 0x280 ]
add rcx, [ rsp - 0x20 ]
adcx r15, [ rsp - 0x28 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x2c8 ], r8
mulx r8, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x2d0 ], r9
mov [ rsp + 0x2d8 ], rbp
mulx rbp, r9, [ rax + 0x30 ]
test al, al
adox rcx, [ rsp + 0x2a8 ]
adox r15, [ rsp + 0x2a0 ]
adcx rcx, [ rsp - 0x40 ]
adcx r15, [ rsp - 0x48 ]
test al, al
adox r14, rbx
adox r8, r10
adcx r14, r11
adcx r8, [ rsp + 0x2c0 ]
mov rdx, 0x3ffffffffffffff 
mov r11, r14
and r11, rdx
adox r12, [ rsp - 0x30 ]
mov r10, [ rsp - 0x38 ]
adox r10, [ rsp + 0x2d8 ]
adcx r12, r9
adcx rbp, r10
xor rbx, rbx
adox r12, [ rsp + 0x2d0 ]
adox rbp, [ rsp + 0x2c8 ]
shrd r14, r8, 58
shr r8, 58
xor r9, r9
adox r12, r14
adox r8, rbp
mov rdx, [ rax + 0x40 ]
mulx r10, rbx, [ rsi + 0x0 ]
mov rdx, 0x3a 
bzhi rbp, r12, rdx
shrd r12, r8, 58
shr r8, 58
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x38 ], rbp
test al, al
adox rcx, rbx
adox r10, r15
mov [ r14 + 0x30 ], r11
adcx rcx, r12
adcx r8, r10
mov r15, rcx
shrd r15, r8, 57
shr r8, 57
mov r11, 0x1ffffffffffffff 
and rcx, r11
adox r15, [ rsp + 0x1b8 ]
adox r8, r9
mov [ r14 + 0x40 ], rcx
bzhi rbx, r15, rdx
shrd r15, r8, 58
add r15, [ rsp + 0x228 ]
bzhi rbp, r13, rdx
bzhi r13, r15, rdx
shr r15, 58
mov [ r14 + 0x28 ], rbp
add r15, [ rsp + 0x2b8 ]
mov [ r14 + 0x10 ], r15
bzhi r12, rdi, rdx
mov [ r14 + 0x18 ], r12
mov [ r14 + 0x0 ], rbx
mov [ r14 + 0x8 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 864
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.1498
; seed 4074111051614018 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 7259368 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=67, initial num_batches=31): 138907 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.019134861326771144
; number reverted permutation / tried permutation: 54247 / 89683 =60.487%
; number reverted decision / tried decision: 38910 / 90316 =43.082%
; validated in 4.172s
