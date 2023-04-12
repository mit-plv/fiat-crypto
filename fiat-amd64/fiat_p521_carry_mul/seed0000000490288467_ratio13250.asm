SECTION .text
	GLOBAL fiat_p521_carry_mul
fiat_p521_carry_mul:
sub rsp, 1008
mov rax, rdx
mov rdx, [ rsi + 0x28 ]
mulx r11, r10, [ rax + 0x0 ]
imul rdx, [ rax + 0x40 ], 0x2
mulx r8, rcx, [ rsi + 0x38 ]
mov r9, 0x1 
mov [ rsp - 0x80 ], rbx
shlx rbx, [ rax + 0x30 ], r9
mov r9, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x20 ]
mov rdx, r9
mov [ rsp - 0x48 ], r11
mulx r11, r9, [ rsi + 0x20 ]
mov [ rsp - 0x40 ], r11
mov r11, [ rax + 0x20 ]
mov [ rsp - 0x38 ], r9
lea r9, [r11 + r11]
xchg rdx, r9
mov [ rsp - 0x30 ], r10
mulx r10, r11, [ rsi + 0x40 ]
mov [ rsp - 0x28 ], rdi
mov rdi, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x20 ], r15
mov [ rsp - 0x18 ], r14
mulx r14, r15, [ rsi + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x10 ], r14
mov [ rsp - 0x8 ], r15
mulx r15, r14, [ rsi + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x0 ], r15
mov [ rsp + 0x8 ], r14
mulx r14, r15, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x10 ], r14
mov [ rsp + 0x18 ], r15
mulx r15, r14, rdi
mov rdx, rdi
mov [ rsp + 0x20 ], r15
mulx r15, rdi, [ rsi + 0x30 ]
mov [ rsp + 0x28 ], r14
mov r14, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x30 ], r15
mov [ rsp + 0x38 ], rdi
mulx rdi, r15, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x40 ], rdi
mov [ rsp + 0x48 ], r15
mulx r15, rdi, [ rax + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x50 ], r15
mov [ rsp + 0x58 ], rdi
mulx rdi, r15, [ rax + 0x10 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x60 ], rdi
mov [ rsp + 0x68 ], r15
mulx r15, rdi, [ rsi + 0x8 ]
mov rdx, r14
mov [ rsp + 0x70 ], r15
mulx r15, r14, [ rsi + 0x28 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x78 ], rdi
mov [ rsp + 0x80 ], r15
mulx r15, rdi, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x88 ], r15
mov [ rsp + 0x90 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
imul rdx, [ rax + 0x38 ], 0x2
mov [ rsp + 0x98 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0xa0 ], r15
mov [ rsp + 0xa8 ], r14
mulx r14, r15, r9
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xb0 ], r13
mov [ rsp + 0xb8 ], r8
mulx r8, r13, [ rsi + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0xc0 ], r8
mov [ rsp + 0xc8 ], r13
mulx r13, r8, [ rsi + 0x18 ]
mov rdx, rdi
mov [ rsp + 0xd0 ], r13
mulx r13, rdi, [ rsi + 0x28 ]
mov [ rsp + 0xd8 ], r8
mov r8, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xe0 ], r13
mov [ rsp + 0xe8 ], rdi
mulx rdi, r13, rbx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xf0 ], rdi
mov [ rsp + 0xf8 ], r13
mulx r13, rdi, rbx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x100 ], r13
mov [ rsp + 0x108 ], rdi
mulx rdi, r13, [ rax + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x110 ], rdi
mov [ rsp + 0x118 ], r13
mulx r13, rdi, [ rax + 0x30 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x120 ], r13
mov [ rsp + 0x128 ], rdi
mulx rdi, r13, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x130 ], rdi
mov [ rsp + 0x138 ], r13
mulx r13, rdi, rbx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x140 ], r13
mov [ rsp + 0x148 ], rdi
mulx rdi, r13, [ rax + 0x18 ]
mov rdx, 0x1 
mov [ rsp + 0x150 ], rdi
shlx rdi, [ rax + 0x10 ], rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x158 ], r13
mov [ rsp + 0x160 ], rcx
mulx rcx, r13, [ rsi + 0x20 ]
mov rdx, rdi
mov [ rsp + 0x168 ], rcx
mulx rcx, rdi, [ rsi + 0x38 ]
mov [ rsp + 0x170 ], r13
imul r13, [ rax + 0x28 ], 0x2
mov [ rsp + 0x178 ], rcx
mov [ rsp + 0x180 ], rdi
mulx rdi, rcx, [ rsi + 0x40 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x188 ], rdi
mov [ rsp + 0x190 ], rcx
mulx rcx, rdi, [ rax + 0x10 ]
mov rdx, r13
mov [ rsp + 0x198 ], rcx
mulx rcx, r13, [ rsi + 0x30 ]
mov [ rsp + 0x1a0 ], rdi
mov rdi, [ rax + 0x18 ]
mov [ rsp + 0x1a8 ], rcx
lea rcx, [rdi + rdi]
test al, al
adox r15, rbp
adox r12, r14
mulx rbp, rdi, [ rsi + 0x28 ]
mov [ rsp + 0x1b0 ], r12
mulx r12, r14, [ rsi + 0x38 ]
mov [ rsp + 0x1b8 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x1c0 ], r13
mov [ rsp + 0x1c8 ], rbp
mulx rbp, r13, [ rax + 0x40 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x1d0 ], rbp
mov [ rsp + 0x1d8 ], r13
mulx r13, rbp, r15
mov rdx, r8
mov [ rsp + 0x1e0 ], r13
mulx r13, r8, [ rsi + 0x40 ]
adcx r11, r14
adcx r12, r10
test al, al
adox r8, [ rsp + 0x160 ]
adox r13, [ rsp + 0xb8 ]
adcx r8, [ rsp + 0xb0 ]
adcx r13, [ rsp - 0x18 ]
mov r10, [ rax + 0x8 ]
mov r14, r10
shl r14, 0x1
xchg rdx, r14
mov [ rsp + 0x1e8 ], rbp
mulx rbp, r10, [ rsi + 0x40 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x1f0 ], r12
mov [ rsp + 0x1f8 ], r11
mulx r11, r12, rcx
mov rdx, r12
mov [ rsp + 0x200 ], rbp
xor rbp, rbp
adox rdx, [ rsp + 0x190 ]
adox r11, [ rsp + 0x188 ]
xchg rdx, r15
mulx rbp, r12, [ rsi + 0x20 ]
mov rdx, rbx
mov [ rsp + 0x208 ], rbp
mulx rbp, rbx, [ rsi + 0x20 ]
adcx r15, [ rsp + 0x38 ]
adcx r11, [ rsp + 0x30 ]
mov [ rsp + 0x210 ], r12
xor r12, r12
adox r15, rdi
adox r11, [ rsp + 0x1c8 ]
mov rdi, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x218 ], r10
mulx r10, r12, [ rsi + 0x28 ]
adcx r8, r12
adcx r10, r13
test al, al
adox r15, rbx
adox rbp, r11
mov rdx, [ rsp + 0x218 ]
adcx rdx, [ rsp + 0x180 ]
mov r13, [ rsp + 0x200 ]
adcx r13, [ rsp + 0x178 ]
mov rbx, rdx
mov rdx, [ rsi + 0x30 ]
mulx r12, r11, rcx
mov rdx, r14
mov [ rsp + 0x220 ], rbp
mulx rbp, r14, [ rsi + 0x10 ]
test al, al
adox rbx, r11
adox r12, r13
adcx rbx, [ rsp + 0xa8 ]
adcx r12, [ rsp + 0x80 ]
add rbx, [ rsp + 0x210 ]
adcx r12, [ rsp + 0x208 ]
xor r13, r13
adox rbx, [ rsp + 0x108 ]
adox r12, [ rsp + 0x100 ]
adcx rbx, r14
adcx rbp, r12
test al, al
adox r8, [ rsp - 0x20 ]
adox r10, [ rsp - 0x28 ]
mov r11, rdx
mov rdx, [ rsi + 0x40 ]
mulx r12, r14, rcx
adcx r14, [ rsp + 0x28 ]
adcx r12, [ rsp + 0x20 ]
mov rdx, r11
mulx rcx, r11, [ rsi + 0x18 ]
xchg rdx, r9
mov [ rsp + 0x228 ], r10
mulx r10, r13, [ rsi + 0x8 ]
mov [ rsp + 0x230 ], r8
mov r8, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x238 ], r15
mov [ rsp + 0x240 ], rcx
mulx rcx, r15, r9
add rbx, r13
adcx r10, rbp
add r14, [ rsp + 0x1c0 ]
adcx r12, [ rsp + 0x1a8 ]
mov rdx, [ rsi + 0x30 ]
mulx r13, rbp, r8
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x248 ], r13
mov [ rsp + 0x250 ], rbp
mulx rbp, r13, [ rax + 0x0 ]
add rbx, r13
adcx rbp, r10
mov rdx, [ rsi + 0x38 ]
mulx r13, r10, r9
add r14, [ rsp + 0xf8 ]
adcx r12, [ rsp + 0xf0 ]
mov rdx, rbx
shrd rdx, rbp, 58
shr rbp, 58
test al, al
adox r14, r15
adox rcx, r12
mov r15, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x258 ], rbp
mulx rbp, r12, rdi
mov rdx, r11
adcx rdx, [ rsp + 0x238 ]
mov [ rsp + 0x260 ], r15
mov r15, [ rsp + 0x220 ]
adcx r15, [ rsp + 0x240 ]
xchg rdx, r8
mov [ rsp + 0x268 ], rcx
mulx rcx, r11, [ rsi + 0x10 ]
mov [ rsp + 0x270 ], r14
xor r14, r14
adox r12, r10
adox r13, rbp
adcx r8, r11
adcx rcx, r15
mov r10, rdx
mov rdx, [ rax + 0x0 ]
mulx r15, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mulx r14, r11, r10
test al, al
adox r12, [ rsp + 0x250 ]
adox r13, [ rsp + 0x248 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x278 ], r15
mov [ rsp + 0x280 ], rbp
mulx rbp, r15, rdi
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x288 ], r14
mulx r14, rdi, [ rsi + 0x8 ]
mov rdx, r15
adcx rdx, [ rsp + 0x1f8 ]
adcx rbp, [ rsp + 0x1f0 ]
mov r15, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x290 ], rbp
mov [ rsp + 0x298 ], r11
mulx r11, rbp, [ rsi + 0x0 ]
test al, al
adox r8, rdi
adox r14, rcx
adcx r12, [ rsp - 0x30 ]
adcx r13, [ rsp - 0x48 ]
test al, al
adox r8, rbp
adox r11, r14
mov rdx, [ rax + 0x8 ]
mulx rdi, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mulx r14, rbp, [ rax + 0x10 ]
mov rdx, [ rsp + 0x270 ]
adcx rdx, [ rsp + 0x298 ]
mov [ rsp + 0x2a0 ], r13
mov r13, [ rsp + 0x268 ]
adcx r13, [ rsp + 0x288 ]
mov [ rsp + 0x2a8 ], r12
mov r12, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x2b0 ], r14
mov [ rsp + 0x2b8 ], rbp
mulx rbp, r14, [ rax + 0x10 ]
test al, al
adox r12, [ rsp + 0x280 ]
adox r13, [ rsp + 0x278 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x2c0 ], rbp
mov [ rsp + 0x2c8 ], r14
mulx r14, rbp, [ rsi + 0x10 ]
adcx r12, rcx
adcx rdi, r13
mov rdx, [ rax + 0x0 ]
mulx r13, rcx, [ rsi + 0x18 ]
add r8, [ rsp + 0x260 ]
adcx r11, [ rsp + 0x258 ]
mov rdx, r10
mov [ rsp + 0x2d0 ], r14
mulx r14, r10, [ rsi + 0x28 ]
test al, al
adox r15, [ rsp + 0xe8 ]
mov rdx, [ rsp + 0x290 ]
adox rdx, [ rsp + 0xe0 ]
xchg rdx, r9
mov [ rsp + 0x2d8 ], rbp
mov [ rsp + 0x2e0 ], r14
mulx r14, rbp, [ rsi + 0x30 ]
adcx r15, [ rsp - 0x38 ]
adcx r9, [ rsp - 0x40 ]
mov rdx, r8
shrd rdx, r11, 58
shr r11, 58
mov [ rsp + 0x2e8 ], r10
xor r10, r10
adox r12, [ rsp + 0x2c8 ]
adox rdi, [ rsp + 0x2c0 ]
adcx r12, rdx
adcx r11, rdi
test al, al
adox r15, rcx
adox r13, r9
mov rcx, 0x3ffffffffffffff 
and r8, rcx
adox r15, [ rsp + 0xa0 ]
adox r13, [ rsp + 0x98 ]
mov rdx, [ rsi + 0x30 ]
mulx rdi, r9, [ rax + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r10, [ rax + 0x18 ]
mov rdx, [ rsp + 0x1e8 ]
adcx rdx, [ rsp + 0x148 ]
mov [ rsp + 0x2f0 ], r8
mov r8, [ rsp + 0x1e0 ]
adcx r8, [ rsp + 0x140 ]
mov [ rsp + 0x2f8 ], rcx
mov rcx, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x300 ], r10
mov [ rsp + 0x308 ], r11
mulx r11, r10, [ rax + 0x8 ]
xor rdx, rdx
adox rcx, rbp
adox r14, r8
mov rbp, r9
adcx rbp, [ rsp + 0x1b8 ]
adcx rdi, [ rsp + 0x1b0 ]
add r15, [ rsp + 0x68 ]
adcx r13, [ rsp + 0x60 ]
xor r9, r9
adox rcx, [ rsp + 0x2e8 ]
adox r14, [ rsp + 0x2e0 ]
mov rdx, [ rsi + 0x20 ]
mulx r9, r8, [ rax + 0x0 ]
adcx rcx, r8
adcx r9, r14
mov rdx, [ rsi + 0x18 ]
mulx r8, r14, [ rax + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x310 ], r11
mov [ rsp + 0x318 ], r10
mulx r10, r11, [ rsi + 0x0 ]
xor rdx, rdx
adox r15, r11
adox r10, r13
adcx rcx, [ rsp + 0xd8 ]
adcx r9, [ rsp + 0xd0 ]
test al, al
adox rcx, [ rsp + 0x2d8 ]
adox r9, [ rsp + 0x2d0 ]
mov r13, [ rsp + 0x308 ]
mov r11, r12
shrd r11, r13, 58
shr r13, 58
mov [ rsp + 0x320 ], r10
xor r10, r10
adox rcx, [ rsp + 0x300 ]
adox r9, [ rsp + 0x2f8 ]
adcx rbp, [ rsp + 0x2b8 ]
adcx rdi, [ rsp + 0x2b0 ]
xor rdx, rdx
adox rbp, [ rsp + 0x170 ]
adox rdi, [ rsp + 0x168 ]
mov r10, [ rsp + 0x138 ]
mov [ rsp + 0x328 ], rdi
mov rdi, r10
adcx rdi, [ rsp + 0x2a8 ]
mov [ rsp + 0x330 ], rbp
mov rbp, [ rsp + 0x130 ]
adcx rbp, [ rsp + 0x2a0 ]
add rdi, r14
adcx r8, rbp
mov rdx, [ rsi + 0x40 ]
mulx r14, r10, [ rax + 0x0 ]
xor rdx, rdx
adox r15, r11
adox r13, [ rsp + 0x320 ]
mov r11, r15
shrd r11, r13, 58
shr r13, 58
mov rbp, 0x3ffffffffffffff 
and r15, rbp
mov rbp, [ rsp + 0x18 ]
mov [ rsp + 0x338 ], r13
mov r13, rbp
adox r13, [ rsp + 0x230 ]
mov [ rsp + 0x340 ], r11
mov r11, [ rsp + 0x10 ]
adox r11, [ rsp + 0x228 ]
adcx r13, [ rsp + 0x8 ]
adcx r11, [ rsp + 0x0 ]
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x18 ], r15
mov rdx, [ rax + 0x30 ]
mulx rbp, r15, [ rsi + 0x8 ]
test al, al
adox r13, [ rsp + 0x78 ]
adox r11, [ rsp + 0x70 ]
adcx r10, [ rsp + 0x318 ]
adcx r14, [ rsp + 0x310 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x348 ], rbp
mov [ rsp + 0x350 ], r15
mulx r15, rbp, [ rax + 0x20 ]
xor rdx, rdx
adox r10, [ rsp + 0x1a0 ]
adox r14, [ rsp + 0x198 ]
adcx r10, [ rsp + 0x158 ]
adcx r14, [ rsp + 0x150 ]
add rcx, rbp
adcx r15, r9
mov rdx, [ rax + 0x20 ]
mulx rbp, r9, [ rsi + 0x20 ]
add r10, r9
adcx rbp, r14
mov rdx, [ rsi + 0x0 ]
mulx r9, r14, [ rax + 0x38 ]
test al, al
adox rdi, [ rsp + 0x48 ]
adox r8, [ rsp + 0x40 ]
mov rdx, [ rsp + 0x330 ]
adcx rdx, [ rsp + 0x118 ]
mov [ rsp + 0x358 ], r9
mov r9, [ rsp + 0x328 ]
adcx r9, [ rsp + 0x110 ]
mov [ rsp + 0x360 ], r14
xor r14, r14
adox rcx, [ rsp + 0x340 ]
adox r15, [ rsp + 0x338 ]
adcx rdx, [ rsp + 0xc8 ]
adcx r9, [ rsp + 0xc0 ]
test al, al
adox rdi, [ rsp + 0x58 ]
adox r8, [ rsp + 0x50 ]
mov r14, rcx
shrd r14, r15, 58
shr r15, 58
test al, al
adox rdi, [ rsp + 0x90 ]
adox r8, [ rsp + 0x88 ]
adcx rdi, r14
adcx r15, r8
mov r14, 0x3a 
bzhi r8, rbx, r14
mov rbx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x368 ], r8
mulx r8, r14, [ rax + 0x30 ]
adox r10, [ rsp - 0x8 ]
adox rbp, [ rsp - 0x10 ]
test al, al
adox r13, r14
adox r8, r11
mov rdx, rdi
shrd rdx, r15, 58
shr r15, 58
test al, al
adox r13, rdx
adox r15, r8
mov r11, r13
shrd r11, r15, 58
shr r15, 58
xor r14, r14
adox r10, [ rsp + 0x128 ]
adox rbp, [ rsp + 0x120 ]
adcx rbx, [ rsp + 0x350 ]
adcx r9, [ rsp + 0x348 ]
mov r8, 0x3ffffffffffffff 
and r13, r8
adox rbx, [ rsp + 0x360 ]
adox r9, [ rsp + 0x358 ]
mov rdx, [ rsi + 0x8 ]
mulx r8, r14, [ rax + 0x38 ]
adcx rbx, r11
adcx r15, r9
mov rdx, rbx
shrd rdx, r15, 58
shr r15, 58
xor r11, r11
adox r10, r14
adox r8, rbp
adcx r10, [ rsp + 0x1d8 ]
adcx r8, [ rsp + 0x1d0 ]
xor rbp, rbp
adox r10, rdx
adox r15, r8
mov r11, 0x3ffffffffffffff 
and rbx, r11
mov r9, r10
shrd r9, r15, 57
shr r15, 57
xor r14, r14
adox r9, [ rsp + 0x368 ]
adox r15, r14
mov rbp, r9
shrd rbp, r15, 58
mov rdx, 0x1ffffffffffffff 
and r10, rdx
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x38 ], rbx
mov [ r8 + 0x40 ], r10
and r9, r11
and r12, r11
add rbp, [ rsp + 0x2f0 ]
mov [ r8 + 0x0 ], r9
mov rbx, rbp
and rbx, r11
shr rbp, 58
and rcx, r11
and rdi, r11
mov [ r8 + 0x28 ], rdi
mov [ r8 + 0x30 ], r13
lea rbp, [ rbp + r12 ]
mov [ r8 + 0x8 ], rbx
mov [ r8 + 0x10 ], rbp
mov [ r8 + 0x20 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1008
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.3250
; seed 2413770704979672 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 6964647 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=85, initial num_batches=31): 132681 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.01905064248051624
; number reverted permutation / tried permutation: 54146 / 89596 =60.434%
; number reverted decision / tried decision: 49924 / 90403 =55.224%
; validated in 3.9s
