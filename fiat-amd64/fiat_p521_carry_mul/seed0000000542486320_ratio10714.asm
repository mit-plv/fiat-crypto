SECTION .text
	GLOBAL fiat_p521_carry_mul
fiat_p521_carry_mul:
sub rsp, 944
mov rax, [ rdx + 0x18 ]
lea r10, [rax + rax]
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rax + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, [ rax + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rax + 0x10 ]
imul rdx, [ rax + 0x28 ], 0x2
mov [ rsp - 0x70 ], r12
mov r12, [ rax + 0x20 ]
mov [ rsp - 0x68 ], r13
mov r13, r12
shl r13, 0x1
mov r12, [ rax + 0x40 ]
mov [ rsp - 0x60 ], r14
lea r14, [r12 + r12]
mov r12, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp - 0x48 ], rbp
mov [ rsp - 0x40 ], rbx
mulx rbx, rbp, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x38 ], r9
mov [ rsp - 0x30 ], r8
mulx r8, r9, [ rax + 0x8 ]
mov rdx, r12
mov [ rsp - 0x28 ], rdi
mulx rdi, r12, [ rsi + 0x40 ]
mov [ rsp - 0x20 ], r15
mov r15, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x18 ], rcx
mov [ rsp - 0x10 ], r11
mulx r11, rcx, [ rsi + 0x20 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x8 ], r11
mov [ rsp + 0x0 ], rcx
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, 0x1 
mov [ rsp + 0x8 ], r8
shlx r8, [ rax + 0x8 ], rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x10 ], r9
mov [ rsp + 0x18 ], rcx
mulx rcx, r9, r15
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x20 ], r11
mov [ rsp + 0x28 ], rcx
mulx rcx, r11, [ rax + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x30 ], rcx
mov [ rsp + 0x38 ], r11
mulx r11, rcx, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x40 ], r9
mov [ rsp + 0x48 ], rdi
mulx rdi, r9, r14
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x50 ], rdi
mov [ rsp + 0x58 ], r9
mulx r9, rdi, [ rax + 0x0 ]
mov rdx, r14
mov [ rsp + 0x60 ], r9
mulx r9, r14, [ rsi + 0x30 ]
mov [ rsp + 0x68 ], r9
mov r9, 0x1 
mov [ rsp + 0x70 ], r14
shlx r14, [ rax + 0x10 ], r9
mov r9, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x78 ], rdi
mov [ rsp + 0x80 ], r12
mulx r12, rdi, r15
mov rdx, r14
mov [ rsp + 0x88 ], r12
mulx r12, r14, [ rsi + 0x38 ]
xchg rdx, r15
mov [ rsp + 0x90 ], rdi
mov [ rsp + 0x98 ], r12
mulx r12, rdi, [ rsi + 0x38 ]
mov [ rsp + 0xa0 ], r14
mov r14, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xa8 ], r8
mov [ rsp + 0xb0 ], r12
mulx r12, r8, r10
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0xb8 ], r12
mov [ rsp + 0xc0 ], r8
mulx r8, r12, [ rsi + 0x28 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0xc8 ], r8
mov [ rsp + 0xd0 ], r12
mulx r12, r8, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0xd8 ], r12
mov [ rsp + 0xe0 ], r8
mulx r8, r12, r15
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0xe8 ], r8
mulx r8, r15, r10
test al, al
adox rbp, rcx
adox r11, rbx
mov rdx, [ rax + 0x10 ]
mulx rcx, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xf0 ], r11
mov [ rsp + 0xf8 ], rbp
mulx rbp, r11, r10
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x100 ], rcx
mulx rcx, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x108 ], rbx
mov [ rsp + 0x110 ], rcx
mulx rcx, rbx, r13
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x118 ], r10
mov [ rsp + 0x120 ], r8
mulx r8, r10, r13
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x128 ], r15
mov [ rsp + 0x130 ], rcx
mulx rcx, r15, r13
adcx r15, rdi
adcx rcx, [ rsp + 0xb0 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x138 ], rbx
mulx rbx, rdi, r13
mov rdx, [ rax + 0x38 ]
mov r13, rdx
shl r13, 0x1
mov rdx, r14
mov [ rsp + 0x140 ], rcx
mulx rcx, r14, [ rsi + 0x30 ]
mov rdx, r13
mov [ rsp + 0x148 ], rcx
mulx rcx, r13, [ rsi + 0x28 ]
mov [ rsp + 0x150 ], rcx
mov [ rsp + 0x158 ], r13
mulx r13, rcx, [ rsi + 0x40 ]
mov [ rsp + 0x160 ], r13
mov r13, [ rax + 0x30 ]
mov [ rsp + 0x168 ], rcx
mov rcx, r13
shl rcx, 0x1
mov r13, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x170 ], r14
mov [ rsp + 0x178 ], r15
mulx r15, r14, [ rsp + 0xa8 ]
test al, al
adox r14, [ rsp + 0xa0 ]
adox r15, [ rsp + 0x98 ]
mov rdx, r13
mov [ rsp + 0x180 ], rbx
mulx rbx, r13, [ rsi + 0x30 ]
adcx r14, r11
adcx rbp, r15
add r14, r10
adcx r8, rbp
xchg rdx, rcx
mulx r10, r11, [ rsi + 0x38 ]
mov r15, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x188 ], rbx
mulx rbx, rbp, rcx
mov rdx, r15
mov [ rsp + 0x190 ], r13
mulx r13, r15, [ rsi + 0x18 ]
mov [ rsp + 0x198 ], rbx
mov [ rsp + 0x1a0 ], rbp
mulx rbp, rbx, [ rsi + 0x28 ]
mov [ rsp + 0x1a8 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x1b0 ], rbx
mov [ rsp + 0x1b8 ], rdi
mulx rdi, rbx, r9
test al, al
adox r14, [ rsp + 0x90 ]
adox r8, [ rsp + 0x88 ]
adcx r14, r15
adcx r13, r8
mov rdx, r11
add rdx, [ rsp + 0x80 ]
adcx r10, [ rsp + 0x48 ]
xor r11, r11
adox r12, [ rsp + 0xc0 ]
mov r15, [ rsp + 0xb8 ]
adox r15, [ rsp + 0xe8 ]
adcx r12, [ rsp + 0x1b8 ]
adcx r15, [ rsp + 0x180 ]
test al, al
adox r12, [ rsp + 0x40 ]
adox r15, [ rsp + 0x28 ]
xchg rdx, rcx
mulx r11, r8, [ rsi + 0x38 ]
mov [ rsp + 0x1c0 ], r11
mov r11, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x1c8 ], r8
mov [ rsp + 0x1d0 ], rdi
mulx rdi, r8, rbp
adcx r12, r8
adcx rdi, r15
mov rdx, r11
mulx r15, r11, [ rsi + 0x18 ]
mov [ rsp + 0x1d8 ], rbx
mulx rbx, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x1e0 ], r10
mov [ rsp + 0x1e8 ], rcx
mulx rcx, r10, r9
xor rdx, rdx
adox r12, r11
adox r15, rdi
adcx r14, r8
adcx rbx, r13
test al, al
adox r12, r10
adox rcx, r15
mov rdx, r9
mulx r13, r9, [ rsi + 0x8 ]
adcx r14, r9
adcx r13, rbx
xor rdi, rdi
adox r12, [ rsp + 0x20 ]
adox rcx, [ rsp + 0x18 ]
mov r11, rdx
mov rdx, [ rax + 0x0 ]
mulx r10, r8, [ rsi + 0x18 ]
adcx r14, [ rsp + 0x78 ]
adcx r13, [ rsp + 0x60 ]
mov rdx, rbp
mulx r15, rbp, [ rsi + 0x30 ]
mov rbx, rbp
test al, al
adox rbx, [ rsp + 0x178 ]
adox r15, [ rsp + 0x140 ]
mov r9, [ rsp + 0x138 ]
mov rbp, r9
adcx rbp, [ rsp + 0x128 ]
mov [ rsp + 0x1f0 ], r13
mov r13, [ rsp + 0x130 ]
adcx r13, [ rsp + 0x120 ]
xor r9, r9
adox rbp, [ rsp + 0x170 ]
adox r13, [ rsp + 0x148 ]
adcx rbp, [ rsp + 0x1b0 ]
adcx r13, [ rsp + 0x1a8 ]
mov rdi, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x1f8 ], r14
mulx r14, r9, r11
test al, al
adox rbp, [ rsp + 0x1a0 ]
adox r13, [ rsp + 0x198 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x200 ], r10
mov [ rsp + 0x208 ], r8
mulx r8, r10, [ rax + 0x0 ]
adcx rbx, [ rsp + 0x158 ]
adcx r15, [ rsp + 0x150 ]
test al, al
adox rbx, r9
adox r14, r15
mov rdx, [ rax + 0x8 ]
mulx r15, r9, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x210 ], r15
mov [ rsp + 0x218 ], r9
mulx r9, r15, r11
adcx rbp, r15
adcx r9, r13
test al, al
adox rbp, r10
adox r8, r9
mov rdx, [ rsp + 0x1e8 ]
adcx rdx, [ rsp + 0x190 ]
mov r13, [ rsp + 0x1e0 ]
adcx r13, [ rsp + 0x188 ]
test al, al
adox rdx, [ rsp + 0x1d8 ]
adox r13, [ rsp + 0x1d0 ]
mov r10, rdx
mov rdx, [ rsi + 0x30 ]
mulx r9, r15, [ rax + 0x0 ]
adcx r12, [ rsp + 0x10 ]
adcx rcx, [ rsp + 0x8 ]
test al, al
adox rbx, [ rsp + 0x208 ]
adox r14, [ rsp + 0x200 ]
adcx r10, [ rsp + 0x0 ]
adcx r13, [ rsp - 0x8 ]
add rbp, [ rsp + 0x218 ]
adcx r8, [ rsp + 0x210 ]
mov rdx, [ rsp + 0x1f0 ]
mov [ rsp + 0x220 ], r9
mov r9, [ rsp + 0x1f8 ]
shrd r9, rdx, 58
shr rdx, 58
test al, al
adox r12, r9
adox rdx, rcx
mov rcx, 0x3a 
bzhi r9, r12, rcx
mov rcx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x228 ], r9
mov [ rsp + 0x230 ], r15
mulx r15, r9, [ rax + 0x8 ]
adox rbp, [ rsp + 0x118 ]
adox r8, [ rsp + 0x110 ]
shrd r12, rcx, 58
shr rcx, 58
test al, al
adox rbp, r12
adox rcx, r8
adcx rbx, r9
adcx r15, r14
xor rdx, rdx
adox rbx, [ rsp + 0x108 ]
adox r15, [ rsp + 0x100 ]
adcx rbx, [ rsp - 0x10 ]
adcx r15, [ rsp - 0x18 ]
mov rdx, [ rsi + 0x10 ]
mulx r9, r14, [ rax + 0x10 ]
mov rdx, [ rax + 0x18 ]
mulx r12, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x238 ], r12
mov [ rsp + 0x240 ], r8
mulx r8, r12, r11
mov rdx, rbp
shrd rdx, rcx, 58
shr rcx, 58
test al, al
adox rbx, rdx
adox rcx, r15
mov rdx, [ rax + 0x10 ]
mulx r15, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x248 ], rcx
mov [ rsp + 0x250 ], rbx
mulx rbx, rcx, rdi
adcx rcx, [ rsp + 0x1c8 ]
adcx rbx, [ rsp + 0x1c0 ]
test al, al
adox rcx, [ rsp + 0x70 ]
adox rbx, [ rsp + 0x68 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x258 ], r15
mulx r15, rdi, [ rax + 0x0 ]
mov rdx, r12
adcx rdx, [ rsp + 0x168 ]
adcx r8, [ rsp + 0x160 ]
mov r12, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x260 ], r8
mov [ rsp + 0x268 ], r11
mulx r11, r8, [ rsi + 0x20 ]
add rcx, rdi
adcx r15, rbx
test al, al
adox rcx, r8
adox r11, r15
mov rdx, [ rax + 0x20 ]
mulx rdi, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mulx r15, r8, [ rax + 0x20 ]
adcx r10, [ rsp + 0x38 ]
adcx r13, [ rsp + 0x30 ]
test al, al
adox r10, r14
adox r9, r13
adcx rcx, [ rsp + 0x268 ]
adcx r11, [ rsp + 0x258 ]
mov rdx, 0x3ffffffffffffff 
mov r14, [ rsp + 0x250 ]
and r14, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x270 ], r14
mulx r14, r13, [ rax + 0x20 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x278 ], r15
mov [ rsp + 0x280 ], r8
mulx r8, r15, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x288 ], r14
mov [ rsp + 0x290 ], r13
mulx r13, r14, [ rax + 0x18 ]
adox r10, r14
adox r13, r9
adcx r10, rbx
adcx rdi, r13
mov rdx, [ rsi + 0x30 ]
mulx r9, rbx, [ rax + 0x8 ]
test al, al
adox r12, [ rsp + 0x230 ]
mov rdx, [ rsp + 0x260 ]
adox rdx, [ rsp + 0x220 ]
adcx r12, [ rsp + 0xd0 ]
adcx rdx, [ rsp + 0xc8 ]
mov r14, rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x298 ], r9
mulx r9, r13, [ rsi + 0x10 ]
mov rdx, [ rsp + 0x58 ]
test al, al
adox rdx, [ rsp - 0x20 ]
mov [ rsp + 0x2a0 ], rbx
mov rbx, [ rsp + 0x50 ]
adox rbx, [ rsp - 0x28 ]
mov [ rsp + 0x2a8 ], rbx
mov rbx, r15
adcx rbx, [ rsp + 0xf8 ]
adcx r8, [ rsp + 0xf0 ]
xor r15, r15
adox rbx, [ rsp + 0xe0 ]
adox r8, [ rsp + 0xd8 ]
adcx rcx, [ rsp + 0x240 ]
adcx r11, [ rsp + 0x238 ]
mov r15, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x2b0 ], r9
mov [ rsp + 0x2b8 ], r13
mulx r13, r9, [ rax + 0x10 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x2c0 ], r15
mov [ rsp + 0x2c8 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
xor rdx, rdx
adox r12, r9
adox r13, r14
adcx rcx, [ rsp + 0x290 ]
adcx r11, [ rsp + 0x288 ]
xor r14, r14
adox rbx, [ rsp + 0x280 ]
adox r8, [ rsp + 0x278 ]
mov rdx, [ rax + 0x20 ]
mulx r14, r9, [ rsi + 0x10 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x2d0 ], r11
mov [ rsp + 0x2d8 ], rcx
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsp + 0x248 ]
mov [ rsp + 0x2e0 ], rcx
mov rcx, [ rsp + 0x250 ]
shrd rcx, rdx, 58
shr rdx, 58
mov [ rsp + 0x2e8 ], r11
mov r11, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x2f0 ], r14
mov [ rsp + 0x2f8 ], r9
mulx r9, r14, [ rax + 0x20 ]
test al, al
adox r12, [ rsp - 0x30 ]
adox r13, [ rsp - 0x38 ]
adcx rbx, r15
adcx rdi, r8
mov rdx, [ rsi + 0x0 ]
mulx r8, r15, [ rax + 0x30 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x300 ], r9
mov [ rsp + 0x308 ], r14
mulx r14, r9, [ rsi + 0x0 ]
xor rdx, rdx
adox r10, rcx
adox r11, [ rsp + 0x2c8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x310 ], r8
mulx r8, rcx, [ rsi + 0x20 ]
adcx rbx, [ rsp + 0x2b8 ]
adcx rdi, [ rsp + 0x2b0 ]
mov rdx, r10
shrd rdx, r11, 58
shr r11, 58
mov [ rsp + 0x318 ], rdi
mov rdi, 0x3ffffffffffffff 
and r10, rdi
mov rdi, [ rsp + 0x2a0 ]
mov [ rsp + 0x320 ], rbx
mov rbx, rdi
adox rbx, [ rsp + 0x2c0 ]
mov [ rsp + 0x328 ], r15
mov r15, [ rsp + 0x298 ]
adox r15, [ rsp + 0x2a8 ]
adcx rbx, [ rsp - 0x40 ]
adcx r15, [ rsp - 0x48 ]
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x20 ], r10
xor r10, r10
adox rbx, rcx
adox r8, r15
adcx r12, [ rsp + 0x2f8 ]
adcx r13, [ rsp + 0x2f0 ]
mov rcx, rdx
mov rdx, [ rax + 0x28 ]
mulx r10, r15, [ rsi + 0x8 ]
mov rdx, r9
xor rdi, rdi
adox rdx, [ rsp + 0x2d8 ]
adox r14, [ rsp + 0x2d0 ]
adcx r12, r15
adcx r10, r13
add rdx, rcx
adcx r11, r14
mov r9, rdx
shrd r9, r11, 58
shr r11, 58
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mulx r15, r13, [ rax + 0x40 ]
mov rdx, 0x3a 
bzhi r14, rcx, rdx
adox r12, [ rsp + 0x328 ]
adox r10, [ rsp + 0x310 ]
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x28 ], r14
xor r14, r14
adox rbx, [ rsp + 0x308 ]
adox r8, [ rsp + 0x300 ]
adcx r12, r9
adcx r11, r10
mov rdx, [ rsi + 0x10 ]
mulx r9, rdi, [ rax + 0x28 ]
mov rdx, 0x3a 
bzhi r10, r12, rdx
bzhi r14, [ rsp + 0x1f8 ], rdx
adox rbx, rdi
adox r9, r8
mov [ rcx + 0x30 ], r10
shrd r12, r11, 58
shr r11, 58
mov rdx, [ rsi + 0x8 ]
mulx rdi, r8, [ rax + 0x30 ]
test al, al
adox rbx, r8
adox rdi, r9
mov rdx, [ rax + 0x38 ]
mulx r9, r10, [ rsi + 0x8 ]
adcx rbx, [ rsp + 0x2e8 ]
adcx rdi, [ rsp + 0x2e0 ]
mov rdx, r10
add rdx, [ rsp + 0x320 ]
adcx r9, [ rsp + 0x318 ]
test al, al
adox rbx, r12
adox r11, rdi
mov r12, rbx
shrd r12, r11, 58
shr r11, 58
mov r8, 0x3a 
bzhi r10, rbx, r8
adox rdx, r13
adox r15, r9
test al, al
adox rdx, r12
adox r11, r15
mov r13, rdx
shrd r13, r11, 57
shr r11, 57
add r13, r14
adc r11, 0x0
bzhi r14, r13, r8
mov [ rcx + 0x0 ], r14
shrd r13, r11, 58
bzhi rdi, rbp, r8
add r13, [ rsp + 0x228 ]
mov rbp, 0x39 
bzhi r9, rdx, rbp
mov [ rcx + 0x40 ], r9
mov rbx, r13
shr rbx, 58
lea rbx, [ rbx + rdi ]
bzhi r12, r13, r8
mov [ rcx + 0x8 ], r12
mov r15, [ rsp + 0x270 ]
mov [ rcx + 0x18 ], r15
mov [ rcx + 0x38 ], r10
mov [ rcx + 0x10 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 944
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.0714
; seed 0950774200744678 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5964116 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=65, initial num_batches=31): 113598 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.019046913239112048
; number reverted permutation / tried permutation: 55094 / 89873 =61.302%
; number reverted decision / tried decision: 43915 / 90126 =48.726%
; validated in 3.526s
