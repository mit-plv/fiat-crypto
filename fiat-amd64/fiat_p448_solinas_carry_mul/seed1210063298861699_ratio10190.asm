SECTION .text
	GLOBAL fiat_p448_solinas_carry_mul
fiat_p448_solinas_carry_mul:
sub rsp, 848
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx r11, r10, [ rax + 0x38 ]
mov rdx, [ rsi + 0x28 ]
mulx r8, rcx, [ rax + 0x38 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x38 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x28 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x38 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x48 ], r14
mov [ rsp - 0x40 ], r13
mulx r13, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x38 ], r13
mov [ rsp - 0x30 ], r14
mulx r14, r13, [ rax + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x28 ], r14
mov [ rsp - 0x20 ], r13
mulx r13, r14, [ rax + 0x30 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x18 ], r13
mov [ rsp - 0x10 ], r14
mulx r14, r13, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x8 ], r11
mov [ rsp + 0x0 ], r10
mulx r10, r11, [ rax + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x8 ], r10
mov [ rsp + 0x10 ], r11
mulx r11, r10, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x18 ], r11
mov [ rsp + 0x20 ], r10
mulx r10, r11, [ rax + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x28 ], r10
mov [ rsp + 0x30 ], r11
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x38 ], r11
mov [ rsp + 0x40 ], r10
mulx r10, r11, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x48 ], rdi
mov [ rsp + 0x50 ], r15
mulx r15, rdi, [ rax + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x58 ], r15
mov [ rsp + 0x60 ], rdi
mulx rdi, r15, [ rax + 0x28 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x68 ], rdi
mov [ rsp + 0x70 ], r15
mulx r15, rdi, [ rsi + 0x30 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x78 ], r15
mov [ rsp + 0x80 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x88 ], r8
mov [ rsp + 0x90 ], rcx
mulx rcx, r8, [ rax + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x98 ], r12
mov [ rsp + 0xa0 ], rbp
mulx rbp, r12, [ rax + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xa8 ], rdi
mov [ rsp + 0xb0 ], r15
mulx r15, rdi, [ rax + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xb8 ], r15
mov [ rsp + 0xc0 ], rdi
mulx rdi, r15, [ rax + 0x30 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0xc8 ], rdi
mov [ rsp + 0xd0 ], r15
mulx r15, rdi, [ rsi + 0x10 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xd8 ], r15
mov [ rsp + 0xe0 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xe8 ], rdi
mov [ rsp + 0xf0 ], r15
mulx r15, rdi, [ rax + 0x18 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xf8 ], r15
mov [ rsp + 0x100 ], rdi
mulx rdi, r15, [ rax + 0x20 ]
mov rdx, r11
mov [ rsp + 0x108 ], rcx
xor rcx, rcx
adox rdx, r9
mov [ rsp + 0x110 ], r8
mov r8, rbx
adox r8, r10
mov rcx, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x118 ], rbp
mov [ rsp + 0x120 ], r12
mulx r12, rbp, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x128 ], r12
mov [ rsp + 0x130 ], rbp
mulx rbp, r12, [ rax + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x138 ], r14
mov [ rsp + 0x140 ], r13
mulx r13, r14, [ rax + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x148 ], r13
mov [ rsp + 0x150 ], r14
mulx r14, r13, [ rax + 0x30 ]
mov rdx, rcx
adcx rdx, r11
adcx r10, r8
mov r11, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x158 ], r14
mov [ rsp + 0x160 ], r13
mulx r13, r14, [ rax + 0x10 ]
test al, al
adox r11, r9
adox rbx, r10
mov rdx, [ rsi + 0x28 ]
mulx r10, r9, [ rax + 0x8 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x168 ], r10
mov [ rsp + 0x170 ], r9
mulx r9, r10, [ rsi + 0x38 ]
adcx r11, r14
mov rdx, r13
adcx rdx, rbx
add r15, r12
adcx rbp, rdi
mov rdi, rdx
mov rdx, [ rsi + 0x30 ]
mulx rbx, r12, [ rax + 0x18 ]
test al, al
adox rcx, r14
adox r13, r8
adcx rcx, r12
mov rdx, rbx
adcx rdx, r13
mov r8, r10
xor r14, r14
adox r8, [ rsp + 0x140 ]
mov r13, r9
adox r13, [ rsp + 0x138 ]
adcx rcx, [ rsp + 0x120 ]
adcx rdx, [ rsp + 0x118 ]
mov r14, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x178 ], rbp
mov [ rsp + 0x180 ], r15
mulx r15, rbp, [ rsi + 0x8 ]
add rcx, [ rsp + 0x110 ]
adcx r14, [ rsp + 0x108 ]
test al, al
adox rcx, [ rsp + 0xb0 ]
adox r14, [ rsp + 0xa8 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x188 ], r13
mov [ rsp + 0x190 ], r8
mulx r8, r13, [ rax + 0x30 ]
adcx r11, r12
adcx rbx, rdi
mov rdx, r10
xor rdi, rdi
adox rdx, r10
adox r9, r9
mov r10, r13
adcx r10, [ rsp + 0xa0 ]
mov r12, r8
adcx r12, [ rsp + 0x98 ]
mov [ rsp + 0x198 ], r9
xor r9, r9
adox r10, [ rsp + 0x90 ]
adox r12, [ rsp + 0x88 ]
mov rdi, rdx
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x1a0 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
adcx rcx, r9
mov rdx, rbx
adcx rdx, r14
test al, al
adox rcx, rbp
adox r15, rdx
mov rdx, [ rax + 0x8 ]
mulx r14, rbp, [ rsi + 0x0 ]
adcx rcx, rbp
adcx r14, r15
mov rdx, r10
add rdx, [ rsp + 0x50 ]
mov r15, r12
adcx r15, [ rsp + 0x48 ]
mov rbp, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x1a8 ], r14
mov [ rsp + 0x1b0 ], rcx
mulx rcx, r14, [ rsi + 0x30 ]
add r11, [ rsp + 0x120 ]
mov rdx, [ rsp + 0x1a0 ]
adcx rdx, [ rsp + 0x118 ]
mov [ rsp + 0x1b8 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x1c0 ], rbp
mov [ rsp + 0x1c8 ], rdi
mulx rdi, rbp, [ rax + 0x28 ]
test al, al
adox r11, [ rsp + 0x110 ]
adox r15, [ rsp + 0x108 ]
adcx r11, [ rsp + 0xb0 ]
adcx r15, [ rsp + 0xa8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x1d0 ], rdi
mov [ rsp + 0x1d8 ], rbp
mulx rbp, rdi, [ rsi + 0x20 ]
test al, al
adox r11, r9
adox rbx, r15
adcx r10, [ rsp + 0xa0 ]
adcx r12, [ rsp + 0x98 ]
test al, al
adox r10, r13
adox r8, r12
adcx r11, [ rsp + 0x40 ]
adcx rbx, [ rsp + 0x38 ]
mov rdx, [ rsi + 0x10 ]
mulx r9, r13, [ rax + 0x0 ]
xor rdx, rdx
adox r10, [ rsp + 0x90 ]
adox r8, [ rsp + 0x88 ]
mov r15, r14
adcx r15, [ rsp + 0x190 ]
mov r12, rcx
adcx r12, [ rsp + 0x188 ]
test al, al
adox r11, rdi
adox rbp, rbx
adcx r15, [ rsp + 0x1d8 ]
adcx r12, [ rsp + 0x1d0 ]
mov rdi, [ rsp + 0x1c8 ]
xor rbx, rbx
adox rdi, [ rsp + 0x140 ]
mov rdx, [ rsp + 0x198 ]
adox rdx, [ rsp + 0x138 ]
mov rbx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x1e0 ], r8
mov [ rsp + 0x1e8 ], r10
mulx r10, r8, [ rax + 0x38 ]
adcx r15, [ rsp + 0xd0 ]
adcx r12, [ rsp + 0xc8 ]
xor rdx, rdx
adox rdi, r14
adox rcx, rbx
adcx r15, [ rsp + 0x0 ]
adcx r12, [ rsp - 0x8 ]
test al, al
adox rdi, [ rsp + 0x1d8 ]
adox rcx, [ rsp + 0x1d0 ]
adcx r15, r13
adcx r9, r12
mov r14, [ rsp + 0x180 ]
test al, al
adox r14, [ rsp - 0x10 ]
mov r13, [ rsp + 0x178 ]
adox r13, [ rsp - 0x18 ]
mov rdx, [ rax + 0x20 ]
mulx r12, rbx, [ rsi + 0x8 ]
adcx r11, [ rsp + 0x20 ]
adcx rbp, [ rsp + 0x18 ]
test al, al
adox r14, r8
adox r10, r13
adcx r15, [ rsp + 0xc0 ]
adcx r9, [ rsp + 0xb8 ]
add r11, [ rsp + 0xe0 ]
adcx rbp, [ rsp + 0xd8 ]
xor rdx, rdx
adox rdi, [ rsp + 0xd0 ]
adox rcx, [ rsp + 0xc8 ]
mov rdx, [ rsi + 0x30 ]
mulx r13, r8, [ rax + 0x10 ]
mov rdx, r8
adcx rdx, [ rsp + 0x1c0 ]
mov [ rsp + 0x1f0 ], r9
mov r9, r13
adcx r9, [ rsp + 0x1b8 ]
mov [ rsp + 0x1f8 ], r15
mov r15, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x200 ], rcx
mov [ rsp + 0x208 ], rdi
mulx rdi, rcx, [ rsi + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x210 ], rbp
mov [ rsp + 0x218 ], r11
mulx r11, rbp, [ rsi + 0x10 ]
add r15, [ rsp - 0x20 ]
adcx r9, [ rsp - 0x28 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x220 ], r12
mov [ rsp + 0x228 ], rbx
mulx rbx, r12, [ rsi + 0x8 ]
mov rdx, r14
mov [ rsp + 0x230 ], rbx
xor rbx, rbx
adox rdx, rcx
adox rdi, r10
adcx rdx, rbp
adcx r11, rdi
mov rcx, rdx
mov rdx, [ rax + 0x10 ]
mulx rdi, rbp, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x238 ], r12
mulx r12, rbx, [ rax + 0x0 ]
test al, al
adox r14, rbx
adox r12, r10
mov rdx, [ rsi + 0x20 ]
mulx rbx, r10, [ rax + 0x20 ]
adcx r15, r10
mov rdx, rbx
adcx rdx, r9
xor r9, r9
adox rcx, [ rsp + 0x10 ]
adox r11, [ rsp + 0x8 ]
adcx r14, [ rsp + 0x80 ]
adcx r12, [ rsp + 0x78 ]
test al, al
adox r14, rbp
adox rdi, r12
adcx rcx, [ rsp + 0x150 ]
adcx r11, [ rsp + 0x148 ]
mov rbp, 0x38 
bzhi r12, rcx, rbp
adox r14, [ rsp + 0x100 ]
adox rdi, [ rsp + 0xf8 ]
mov rbp, [ rsp + 0x50 ]
mov [ rsp + 0x240 ], r12
mov r12, rbp
test al, al
adox r12, [ rsp + 0x1e8 ]
mov [ rsp + 0x248 ], rdx
mov rdx, [ rsp + 0x48 ]
adox rdx, [ rsp + 0x1e0 ]
mov rbp, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x250 ], r15
mulx r15, r9, [ rsi + 0x8 ]
adcx r14, [ rsp + 0x30 ]
adcx rdi, [ rsp + 0x28 ]
xor rdx, rdx
adox r14, [ rsp + 0xf0 ]
adox rdi, [ rsp + 0xe8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x258 ], r15
mov [ rsp + 0x260 ], r9
mulx r9, r15, [ rsi + 0x0 ]
shrd rcx, r11, 56
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x268 ], rcx
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsp + 0x218 ]
mov [ rsp + 0x270 ], r9
xor r9, r9
adox rdx, [ rsp + 0x228 ]
mov [ rsp + 0x278 ], r15
mov r15, [ rsp + 0x210 ]
adox r15, [ rsp + 0x220 ]
adcx r12, r8
adcx r13, rbp
xor r8, r8
adox rdx, r11
adox rcx, r15
mov r9, [ rsp + 0x60 ]
mov rbp, r9
adcx rbp, [ rsp + 0x250 ]
mov r11, [ rsp + 0x58 ]
mov r15, r11
adcx r15, [ rsp + 0x248 ]
test al, al
adox rbp, [ rsp - 0x30 ]
adox r15, [ rsp - 0x38 ]
mov r8, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x280 ], rcx
mov [ rsp + 0x288 ], r15
mulx r15, rcx, [ rax + 0x38 ]
adcx r14, [ rsp - 0x40 ]
adcx rdi, [ rsp - 0x48 ]
add r14, rcx
adcx r15, rdi
xor rdx, rdx
adox r12, [ rsp - 0x20 ]
adox r13, [ rsp - 0x28 ]
adcx r12, r10
adcx rbx, r13
test al, al
adox r12, r9
adox r11, rbx
mov rdx, [ rax + 0x10 ]
mulx r10, r9, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mulx rdi, rcx, [ rax + 0x10 ]
adcx r12, [ rsp - 0x30 ]
adcx r11, [ rsp - 0x38 ]
test al, al
adox rbp, [ rsp + 0x238 ]
mov rdx, [ rsp + 0x230 ]
mov r13, rdx
adox r13, [ rsp + 0x288 ]
adcx r12, [ rsp + 0x238 ]
adcx rdx, r11
mov rbx, 0xffffffffffffff 
mov r11, r14
and r11, rbx
adox rbp, [ rsp + 0x278 ]
adox r13, [ rsp + 0x270 ]
mov rbx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x290 ], r11
mov [ rsp + 0x298 ], r8
mulx r8, r11, [ rax + 0x0 ]
shrd r14, r15, 56
mov rdx, [ rsp + 0x0 ]
mov r15, rdx
mov [ rsp + 0x2a0 ], rbx
xor rbx, rbx
adox r15, [ rsp + 0x208 ]
mov [ rsp + 0x2a8 ], r12
mov r12, [ rsp - 0x8 ]
adox r12, [ rsp + 0x200 ]
mov rdx, r14
adcx rdx, rbp
adc r13, 0x0
mov rbp, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x2b0 ], r8
mulx r8, rbx, [ rsi + 0x18 ]
mov rdx, rbp
shrd rdx, r13, 56
mov r13, rdx
add r13, [ rsp + 0x1b0 ]
mov [ rsp + 0x2b8 ], r8
mov r8, [ rsp + 0x1a8 ]
adc r8, 0x0
mov rdx, 0xffffffffffffff 
and rbp, rdx
adox r15, [ rsp + 0x130 ]
adox r12, [ rsp + 0x128 ]
adcx r15, [ rsp + 0x170 ]
adcx r12, [ rsp + 0x168 ]
mov rdx, r13
shrd rdx, r8, 56
mov r8, r9
test al, al
adox r8, [ rsp + 0x1f8 ]
adox r10, [ rsp + 0x1f0 ]
adcx r8, rdx
adc r10, 0x0
test al, al
adox r15, rcx
adox rdi, r12
mov r9, r11
adcx r9, [ rsp + 0x2a8 ]
mov rcx, [ rsp + 0x2b0 ]
adcx rcx, [ rsp + 0x2a0 ]
add r9, rbx
adcx rcx, [ rsp + 0x2b8 ]
mov rdx, [ rax + 0x10 ]
mulx rbx, r11, [ rsi + 0x10 ]
xor rdx, rdx
adox r9, r11
adox rbx, rcx
adcx r9, [ rsp + 0x260 ]
adcx rbx, [ rsp + 0x258 ]
mov rdx, [ rsi + 0x10 ]
mulx rcx, r12, [ rax + 0x20 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x2c0 ], rbp
mulx rbp, r11, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffff 
mov [ rsp + 0x2c8 ], rcx
mov rcx, r8
and rcx, rdx
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x10 ], rcx
adox r9, r11
adox rbp, rbx
mov rbx, rdx
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, [ rax + 0x18 ]
adcx r9, [ rsp + 0x268 ]
adc rbp, 0x0
add r14, r9
adc rbp, 0x0
xor rdx, rdx
adox r15, r11
adox rcx, rdi
mov rdi, r14
shrd rdi, rbp, 56
shrd r8, r10, 56
add r8, [ rsp + 0x240 ]
mov r10, 0x38 
bzhi r11, r8, r10
shr r8, 56
xor r9, r9
adox r15, r12
adox rcx, [ rsp + 0x2c8 ]
adcx r15, [ rsp + 0x70 ]
adcx rcx, [ rsp + 0x68 ]
mov [ rbx + 0x18 ], r11
test al, al
adox r15, [ rsp + 0x160 ]
adox rcx, [ rsp + 0x158 ]
mov rdx, rdi
adcx rdx, [ rsp + 0x298 ]
mov r12, [ rsp + 0x280 ]
adc r12, 0x0
mov rbp, rdx
shrd rbp, r12, 56
bzhi rdi, rdx, r10
adox r15, rbp
adox rcx, r9
mov r11, r15
shrd r11, rcx, 56
add r11, [ rsp + 0x290 ]
mov rdx, r11
shr rdx, 56
bzhi r12, r15, r10
mov [ rbx + 0x30 ], r12
mov rbp, rdx
add rbp, [ rsp + 0x2c0 ]
bzhi r15, r14, r10
lea r15, [ r15 + rdx ]
mov r14, rbp
shr r14, 56
lea r8, [ r8 + r15 ]
mov rcx, r8
shr rcx, 56
lea rcx, [ rcx + rdi ]
mov [ rbx + 0x28 ], rcx
bzhi rdi, rbp, r10
bzhi rdx, r13, r10
mov [ rbx + 0x0 ], rdi
lea r14, [ r14 + rdx ]
bzhi r13, r11, r10
mov [ rbx + 0x8 ], r14
bzhi r11, r8, r10
mov [ rbx + 0x20 ], r11
mov [ rbx + 0x38 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 848
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.0190
; seed 1210063298861699 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 71779 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=49, initial num_batches=31): 1177 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.01639755360202845
; number reverted permutation / tried permutation: 222 / 508 =43.701%
; number reverted decision / tried decision: 137 / 491 =27.902%
; validated in 5.773s
