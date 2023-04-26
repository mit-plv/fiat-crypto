SECTION .text
	GLOBAL fiat_p521_carry_mul
fiat_p521_carry_mul:
sub rsp, 952
mov rax, rdx
mov rdx, [ rdx + 0x28 ]
mulx r11, r10, [ rsi + 0x18 ]
mov rdx, [ rax + 0x20 ]
lea rcx, [rdx + rdx]
mov rdx, [ rax + 0x10 ]
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rax + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r11
mulx r11, rdi, [ rsi + 0x28 ]
mov rdx, rcx
mov [ rsp - 0x40 ], r10
mulx r10, rcx, [ rsi + 0x28 ]
mov [ rsp - 0x38 ], rbp
mov rbp, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x30 ], rbx
mov [ rsp - 0x28 ], r11
mulx r11, rbx, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x20 ], r11
mov [ rsp - 0x18 ], rbx
mulx rbx, r11, rbp
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], rdi
mov [ rsp - 0x8 ], r15
mulx r15, rdi, [ rax + 0x10 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x0 ], r15
mov [ rsp + 0x8 ], rdi
mulx rdi, r15, [ rsi + 0x0 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x10 ], rdi
lea rdi, [rdx + rdx]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x18 ], r15
mov [ rsp + 0x20 ], r14
mulx r14, r15, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x28 ], r14
mov [ rsp + 0x30 ], r15
mulx r15, r14, [ rax + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x38 ], r15
mov [ rsp + 0x40 ], r14
mulx r14, r15, rdi
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x48 ], r14
mov [ rsp + 0x50 ], r15
mulx r15, r14, rbp
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x58 ], r15
mov [ rsp + 0x60 ], r14
mulx r14, r15, [ rax + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x68 ], r14
mov [ rsp + 0x70 ], r15
mulx r15, r14, [ rax + 0x8 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x78 ], r15
mov [ rsp + 0x80 ], r14
mulx r14, r15, rdi
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x88 ], r14
mov [ rsp + 0x90 ], r15
mulx r15, r14, [ rsi + 0x18 ]
mov rdx, rdi
mov [ rsp + 0x98 ], r15
mulx r15, rdi, [ rsi + 0x10 ]
mov [ rsp + 0xa0 ], r14
mov r14, rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0xa8 ], r9
mov [ rsp + 0xb0 ], r8
mulx r8, r9, [ rsi + 0x8 ]
mov rdx, 0x1 
mov [ rsp + 0xb8 ], r8
shlx r8, [ rax + 0x18 ], rdx
mov rdx, r8
mov [ rsp + 0xc0 ], r9
mulx r9, r8, [ rsi + 0x38 ]
mov [ rsp + 0xc8 ], r13
mov r13, [ rax + 0x28 ]
mov [ rsp + 0xd0 ], r12
lea r12, [r13 + r13]
mov r13, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xd8 ], r15
mov [ rsp + 0xe0 ], rdi
mulx rdi, r15, [ rax + 0x38 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xe8 ], rdi
mov [ rsp + 0xf0 ], r15
mulx r15, rdi, [ rsi + 0x10 ]
imul rdx, [ rax + 0x40 ], 0x2
xchg rdx, r13
mov [ rsp + 0xf8 ], r15
mov [ rsp + 0x100 ], rdi
mulx rdi, r15, [ rsi + 0x40 ]
xchg rdx, r12
mov [ rsp + 0x108 ], rdi
mov [ rsp + 0x110 ], r15
mulx r15, rdi, [ rsi + 0x30 ]
mov [ rsp + 0x118 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x120 ], rdi
mov [ rsp + 0x128 ], r10
mulx r10, rdi, r13
mov rdx, r13
mov [ rsp + 0x130 ], r10
mulx r10, r13, [ rsi + 0x28 ]
mov [ rsp + 0x138 ], r10
mov [ rsp + 0x140 ], r13
mulx r13, r10, [ rsi + 0x18 ]
mov [ rsp + 0x148 ], r13
mov [ rsp + 0x150 ], r10
mulx r10, r13, [ rsi + 0x30 ]
mov [ rsp + 0x158 ], r10
mov r10, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x160 ], r13
mov [ rsp + 0x168 ], rdi
mulx rdi, r13, [ rsi + 0x20 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x170 ], rdi
lea rdi, [rdx + rdx]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x178 ], r13
mov [ rsp + 0x180 ], rcx
mulx rcx, r13, rdi
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x188 ], rcx
mov [ rsp + 0x190 ], r13
mulx r13, rcx, r10
mov rdx, r14
mov [ rsp + 0x198 ], r13
mulx r13, r14, [ rsi + 0x38 ]
mov [ rsp + 0x1a0 ], rcx
imul rcx, [ rax + 0x10 ], 0x2
mov [ rsp + 0x1a8 ], rbx
mov rbx, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x1b0 ], r11
mov [ rsp + 0x1b8 ], r13
mulx r13, r11, rcx
mov rdx, rdi
mov [ rsp + 0x1c0 ], r13
mulx r13, rdi, [ rsi + 0x30 ]
mov [ rsp + 0x1c8 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x1d0 ], rdi
mov [ rsp + 0x1d8 ], r11
mulx r11, rdi, r10
mov rdx, r13
mov [ rsp + 0x1e0 ], r11
mulx r11, r13, [ rsi + 0x28 ]
mov [ rsp + 0x1e8 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x1f0 ], r11
mov [ rsp + 0x1f8 ], r13
mulx r13, r11, rcx
mov rdx, r12
mulx rcx, r12, [ rsi + 0x30 ]
test al, al
adox r11, r8
adox r9, r13
mov rdx, [ rsi + 0x40 ]
mulx r13, r8, rdi
imul rdx, [ rax + 0x8 ], 0x2
mov [ rsp + 0x200 ], rcx
mov [ rsp + 0x208 ], r12
mulx r12, rcx, [ rsi + 0x40 ]
add r8, r14
adcx r13, [ rsp + 0x1b8 ]
test al, al
adox r11, [ rsp + 0x1b0 ]
adox r9, [ rsp + 0x1a8 ]
adcx rcx, [ rsp + 0x1d8 ]
adcx r12, [ rsp + 0x1c0 ]
xor r14, r14
adox rcx, [ rsp + 0x208 ]
adox r12, [ rsp + 0x200 ]
mov rdx, r15
mulx r14, r15, [ rsi + 0x20 ]
adcx rcx, [ rsp + 0x180 ]
adcx r12, [ rsp + 0x128 ]
add rcx, r15
adcx r14, r12
mov r15, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x210 ], r13
mulx r13, r12, rdi
xor rdx, rdx
adox rcx, r12
adox r13, r14
mov rdx, [ rsi + 0x28 ]
mulx r12, r14, r15
mov rdx, rdi
mov [ rsp + 0x218 ], r8
mulx r8, rdi, [ rsi + 0x38 ]
mov rdx, rbx
mov [ rsp + 0x220 ], r8
mulx r8, rbx, [ rsi + 0x18 ]
adcx rcx, [ rsp + 0xe0 ]
adcx r13, [ rsp + 0xd8 ]
mov [ rsp + 0x228 ], rdi
xor rdi, rdi
adox rcx, [ rsp + 0x1a0 ]
adox r13, [ rsp + 0x198 ]
adcx r11, r14
adcx r12, r9
mov r9, rdx
mov rdx, [ rax + 0x0 ]
mulx rdi, r14, [ rsi + 0x0 ]
xor rdx, rdx
adox r11, [ rsp + 0x190 ]
adox r12, [ rsp + 0x188 ]
adcx r11, rbx
adcx r8, r12
xor rbx, rbx
adox r11, [ rsp + 0x168 ]
adox r8, [ rsp + 0x130 ]
mov rdx, [ rsi + 0x8 ]
mulx rbx, r12, [ rax + 0x0 ]
adcx rcx, r14
adcx rdi, r13
xor rdx, rdx
adox r11, r12
adox rbx, r8
mov r13, rcx
shrd r13, rdi, 58
shr rdi, 58
mov rdx, [ rsi + 0x38 ]
mulx r8, r14, rbp
mov rdx, r14
xor rbp, rbp
adox rdx, [ rsp + 0x110 ]
adox r8, [ rsp + 0x108 ]
adcx rdx, [ rsp + 0x120 ]
adcx r8, [ rsp + 0x118 ]
mov r12, rdx
mov rdx, [ rax + 0x8 ]
mulx rbp, r14, [ rsi + 0x0 ]
xor rdx, rdx
adox r11, r14
adox rbp, rbx
mov rbx, 0x3ffffffffffffff 
and rcx, rbx
mov rdx, r9
mulx r14, r9, [ rsi + 0x20 ]
adox r12, [ rsp + 0x1f8 ]
adox r8, [ rsp + 0x1f0 ]
mov rbx, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x230 ], rcx
mov [ rsp + 0x238 ], r8
mulx r8, rcx, [ rsi + 0x8 ]
adcx r11, r13
adcx rdi, rbp
test al, al
adox r12, r9
adox r14, [ rsp + 0x238 ]
mov rdx, [ rsi + 0x40 ]
mulx rbp, r13, r15
adcx r12, [ rsp + 0x150 ]
adcx r14, [ rsp + 0x148 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x240 ], rdi
mulx rdi, r9, [ rsi + 0x18 ]
add r12, [ rsp + 0xd0 ]
adcx r14, [ rsp + 0xc8 ]
mov rdx, r15
mov [ rsp + 0x248 ], rdi
mulx rdi, r15, [ rsi + 0x38 ]
xor rdx, rdx
adox r12, rcx
adox r8, r14
adcx r13, [ rsp + 0x228 ]
adcx rbp, [ rsp + 0x220 ]
xor rcx, rcx
adox r12, [ rsp + 0xb0 ]
adox r8, [ rsp + 0xa8 ]
mov rdx, r15
adcx rdx, [ rsp + 0x60 ]
adcx rdi, [ rsp + 0x58 ]
xor r14, r14
adox r13, [ rsp + 0x90 ]
adox rbp, [ rsp + 0x88 ]
adcx r13, [ rsp + 0x140 ]
adcx rbp, [ rsp + 0x138 ]
xor rcx, rcx
adox rdx, [ rsp + 0x1d0 ]
adox rdi, [ rsp + 0x1c8 ]
adcx rdx, [ rsp + 0x50 ]
adcx rdi, [ rsp + 0x48 ]
mov r14, [ rsp + 0x240 ]
mov r15, r11
shrd r15, r14, 58
shr r14, 58
mov rcx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x250 ], rbp
mov [ rsp + 0x258 ], r13
mulx r13, rbp, r10
add rcx, rbp
adcx r13, rdi
test al, al
adox rcx, r9
adox r13, [ rsp + 0x248 ]
mov rdx, [ rsi + 0x38 ]
mulx rdi, r9, [ rax + 0x8 ]
adcx r12, r15
adcx r14, r8
mov rdx, [ rsi + 0x40 ]
mulx r15, r8, [ rax + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x260 ], r14
mulx r14, rbp, [ rax + 0x0 ]
mov rdx, rbp
test al, al
adox rdx, [ rsp + 0x258 ]
adox r14, [ rsp + 0x250 ]
adcx r8, r9
adcx rdi, r15
mov r9, rdx
mov rdx, [ rsi + 0x40 ]
mulx rbp, r15, r10
test al, al
adox r9, [ rsp + 0xa0 ]
adox r14, [ rsp + 0x98 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x268 ], r12
mulx r12, r10, rbx
adcx r10, [ rsp + 0x1e8 ]
adcx r12, [ rsp + 0x1e0 ]
add rcx, [ rsp + 0x20 ]
adcx r13, [ rsp - 0x8 ]
mov rdx, [ rsp + 0x160 ]
mov rbx, rdx
mov [ rsp + 0x270 ], r13
xor r13, r13
adox rbx, [ rsp + 0x218 ]
mov [ rsp + 0x278 ], rcx
mov rcx, [ rsp + 0x158 ]
adox rcx, [ rsp + 0x210 ]
adcx rbx, [ rsp - 0x10 ]
adcx rcx, [ rsp - 0x28 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x280 ], rdi
mulx rdi, r13, [ rax + 0x10 ]
xor rdx, rdx
adox r15, [ rsp + 0x30 ]
adox rbp, [ rsp + 0x28 ]
adcx rbx, [ rsp + 0x80 ]
adcx rcx, [ rsp + 0x78 ]
test al, al
adox rbx, [ rsp + 0x8 ]
adox rcx, [ rsp + 0x0 ]
adcx r10, [ rsp + 0x40 ]
adcx r12, [ rsp + 0x38 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x288 ], rbp
mov [ rsp + 0x290 ], r15
mulx r15, rbp, [ rsi + 0x28 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x298 ], r15
mov [ rsp + 0x2a0 ], rbp
mulx rbp, r15, [ rsi + 0x8 ]
test al, al
adox rbx, [ rsp - 0x30 ]
adox rcx, [ rsp - 0x38 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x2a8 ], rcx
mov [ rsp + 0x2b0 ], rbx
mulx rbx, rcx, [ rsi + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x2b8 ], rbx
mov [ rsp + 0x2c0 ], rcx
mulx rcx, rbx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x2c8 ], rbp
mov [ rsp + 0x2d0 ], r15
mulx r15, rbp, [ rax + 0x10 ]
adcx r9, rbp
adcx r15, r14
add r10, rbx
adcx rcx, r12
xor rdx, rdx
adox r8, r13
adox rdi, [ rsp + 0x280 ]
mov rdx, [ rax + 0x20 ]
mulx r13, r14, [ rsi + 0x20 ]
adcx r8, [ rsp + 0x2a0 ]
adcx rdi, [ rsp + 0x298 ]
test al, al
adox r8, r14
adox r13, rdi
mov rdx, [ rsi + 0x0 ]
mulx rbx, r12, [ rax + 0x18 ]
mov rdx, [ rax + 0x18 ]
mulx r14, rbp, [ rsi + 0x20 ]
adcx r8, [ rsp - 0x40 ]
adcx r13, [ rsp - 0x48 ]
mov rdx, [ rsp + 0x278 ]
xor rdi, rdi
adox rdx, [ rsp + 0x2d0 ]
mov [ rsp + 0x2d8 ], r14
mov r14, [ rsp + 0x270 ]
adox r14, [ rsp + 0x2c8 ]
mov rdi, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x2e0 ], rbp
mov [ rsp + 0x2e8 ], rcx
mulx rcx, rbp, [ rax + 0x38 ]
adcx rdi, r12
adcx rbx, r14
mov rdx, [ rsp + 0x260 ]
mov r12, [ rsp + 0x268 ]
shrd r12, rdx, 58
shr rdx, 58
xor r14, r14
adox r9, [ rsp + 0x2c0 ]
adox r15, [ rsp + 0x2b8 ]
adcx rdi, r12
adcx rdx, rbx
mov rbx, rdx
mov rdx, [ rax + 0x10 ]
mulx r14, r12, [ rsi + 0x28 ]
mov rdx, rdi
shrd rdx, rbx, 58
shr rbx, 58
add r9, [ rsp + 0x18 ]
adcx r15, [ rsp + 0x10 ]
mov [ rsp + 0x2f0 ], rcx
xor rcx, rcx
adox r9, rdx
adox rbx, r15
mov rdx, [ rax + 0x18 ]
mulx rcx, r15, [ rsi + 0x18 ]
mov rdx, 0x3a 
mov [ rsp + 0x2f8 ], rbp
bzhi rbp, r9, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x300 ], r14
mov [ rsp + 0x308 ], r12
mulx r12, r14, [ rax + 0x30 ]
mov rdx, [ rsp + 0x70 ]
mov [ rsp + 0x310 ], rcx
mov rcx, rdx
adox rcx, [ rsp + 0x2b0 ]
mov [ rsp + 0x318 ], r15
mov r15, [ rsp + 0x68 ]
adox r15, [ rsp + 0x2a8 ]
add r8, r14
adcx r12, r13
mov rdx, 0x3a 
bzhi r13, rdi, rdx
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x18 ], r13
mov rdx, [ rax + 0x20 ]
mulx r13, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x320 ], r15
mulx r15, rdi, [ rax + 0x28 ]
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x20 ], rbp
adox r10, [ rsp + 0x178 ]
mov rbp, [ rsp + 0x2e8 ]
adox rbp, [ rsp + 0x170 ]
test al, al
adox r10, [ rsp + 0x318 ]
adox rbp, [ rsp + 0x310 ]
adcx r8, [ rsp + 0xf0 ]
adcx r12, [ rsp + 0xe8 ]
mov rdx, [ rsp + 0x290 ]
mov [ rsp + 0x328 ], r12
xor r12, r12
adox rdx, [ rsp - 0x18 ]
mov [ rsp + 0x330 ], r8
mov r8, [ rsp + 0x288 ]
adox r8, [ rsp - 0x20 ]
adcx r10, r14
adcx r13, rbp
mov r14, rdx
mov rdx, [ rax + 0x28 ]
mulx r12, rbp, [ rsi + 0x8 ]
test al, al
adox r10, rbp
adox r12, r13
adcx r14, [ rsp + 0x308 ]
adcx r8, [ rsp + 0x300 ]
shrd r9, rbx, 58
shr rbx, 58
test al, al
adox rcx, rdi
adox r15, [ rsp + 0x320 ]
adcx r14, [ rsp + 0x2e0 ]
adcx r8, [ rsp + 0x2d8 ]
test al, al
adox rcx, r9
adox rbx, r15
mov rdx, [ rax + 0x20 ]
mulx r13, rdi, [ rsi + 0x18 ]
adcx r14, rdi
adcx r13, r8
mov rdx, [ rsi + 0x0 ]
mulx r9, rbp, [ rax + 0x40 ]
test al, al
adox r14, [ rsp + 0x100 ]
adox r13, [ rsp + 0xf8 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, r15, [ rax + 0x30 ]
mov rdx, 0x3a 
bzhi rdi, rcx, rdx
adox r14, [ rsp + 0xc0 ]
adox r13, [ rsp + 0xb8 ]
shrd rcx, rbx, 58
shr rbx, 58
xor rdx, rdx
adox r10, r15
adox r8, r12
adcx r10, rcx
adcx rbx, r8
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x28 ], rdi
mov r15, 0x3ffffffffffffff 
and r11, r15
mov rdi, r10
and rdi, r15
shrd r10, rbx, 58
shr rbx, 58
test al, al
adox r14, [ rsp + 0x2f8 ]
adox r13, [ rsp + 0x2f0 ]
mov [ r12 + 0x30 ], rdi
adcx r14, r10
adcx rbx, r13
mov rcx, r14
and rcx, r15
shrd r14, rbx, 58
shr rbx, 58
mov r8, rbp
xor rdi, rdi
adox r8, [ rsp + 0x330 ]
adox r9, [ rsp + 0x328 ]
mov rdx, [ rsp + 0x268 ]
and rdx, r15
adox r8, r14
adox rbx, r9
mov rbp, r8
shrd rbp, rbx, 57
shr rbx, 57
test al, al
adox rbp, [ rsp + 0x230 ]
adox rbx, rdi
mov r10, 0x1ffffffffffffff 
and r8, r10
mov r13, rbp
and r13, r15
shrd rbp, rbx, 58
lea rbp, [ rbp + r11 ]
mov r11, rbp
and r11, r15
shr rbp, 58
lea rbp, [ rbp + rdx ]
mov [ r12 + 0x10 ], rbp
mov [ r12 + 0x38 ], rcx
mov [ r12 + 0x40 ], r8
mov [ r12 + 0x8 ], r11
mov [ r12 + 0x0 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 952
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.3800
; seed 3410720925555516 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 6828808 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=73, initial num_batches=31): 130315 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.019083125488372203
; number reverted permutation / tried permutation: 54071 / 90406 =59.809%
; number reverted decision / tried decision: 49372 / 89593 =55.107%
; validated in 3.432s
