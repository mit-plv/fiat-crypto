SECTION .text
	GLOBAL fiat_p521_carry_mul
fiat_p521_carry_mul:
sub rsp, 1176
mov rax, rdx
mov rdx, [ rsi + 0x20 ]
mulx r11, r10, [ rax + 0x18 ]
mov rdx, [ rax + 0x38 ]
lea rcx, [rdx + rdx]
imul rdx, [ rax + 0x28 ], 0x2
mov r8, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x28 ]
imul rdx, [ rax + 0x40 ], 0x2
mov [ rsp - 0x78 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rax + 0x10 ]
mov rdx, 0x1 
mov [ rsp - 0x60 ], r14
shlx r14, [ rax + 0x8 ], rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x48 ], rbx
mov [ rsp - 0x40 ], r9
mulx r9, rbx, [ rax + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x38 ], r13
mov [ rsp - 0x30 ], r12
mulx r12, r13, [ rax + 0x20 ]
mov rdx, rbp
mov [ rsp - 0x28 ], r12
mulx r12, rbp, [ rsi + 0x40 ]
mov [ rsp - 0x20 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp - 0x18 ], rdi
mov [ rsp - 0x10 ], r15
mulx r15, rdi, [ rax + 0x0 ]
mov rdx, r13
mov [ rsp - 0x8 ], r11
mulx r11, r13, [ rsi + 0x28 ]
xchg rdx, r8
mov [ rsp + 0x0 ], r10
mov [ rsp + 0x8 ], r15
mulx r15, r10, [ rsi + 0x30 ]
mov [ rsp + 0x10 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x18 ], r9
mov [ rsp + 0x20 ], rbx
mulx rbx, r9, rcx
mov rdx, rcx
mov [ rsp + 0x28 ], r11
mulx r11, rcx, [ rsi + 0x40 ]
mov [ rsp + 0x30 ], r13
mov [ rsp + 0x38 ], r11
mulx r11, r13, [ rsi + 0x38 ]
mov [ rsp + 0x40 ], rcx
mov rcx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x48 ], rbx
mov [ rsp + 0x50 ], r9
mulx r9, rbx, r8
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x58 ], r9
mov [ rsp + 0x60 ], rbx
mulx rbx, r9, [ rax + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x68 ], rbx
mov [ rsp + 0x70 ], r9
mulx r9, rbx, rcx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x78 ], r9
mov [ rsp + 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x88 ], rbx
mov [ rsp + 0x90 ], r9
mulx r9, rbx, [ rax + 0x8 ]
mov rdx, rcx
mov [ rsp + 0x98 ], r9
mulx r9, rcx, [ rsi + 0x10 ]
mov [ rsp + 0xa0 ], rbx
mov rbx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xa8 ], r9
mov [ rsp + 0xb0 ], rcx
mulx rcx, r9, [ rax + 0x38 ]
imul rdx, [ rax + 0x18 ], 0x2
mov [ rsp + 0xb8 ], rcx
mov [ rsp + 0xc0 ], r9
mulx r9, rcx, [ rsi + 0x30 ]
mov [ rsp + 0xc8 ], r9
mov r9, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xd0 ], rcx
mov [ rsp + 0xd8 ], r15
mulx r15, rcx, rbx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0xe0 ], r15
mov [ rsp + 0xe8 ], rcx
mulx rcx, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xf0 ], rcx
mov [ rsp + 0xf8 ], r15
mulx r15, rcx, r8
imul rdx, [ rax + 0x10 ], 0x2
mov [ rsp + 0x100 ], r15
mov [ rsp + 0x108 ], rcx
mulx rcx, r15, [ rsi + 0x38 ]
xchg rdx, r9
mov [ rsp + 0x110 ], r10
mov [ rsp + 0x118 ], r11
mulx r11, r10, [ rsi + 0x40 ]
mov [ rsp + 0x120 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x128 ], rcx
mov [ rsp + 0x130 ], r15
mulx r15, rcx, r8
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x138 ], r15
mov [ rsp + 0x140 ], rcx
mulx rcx, r15, [ rax + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x148 ], rcx
mov [ rsp + 0x150 ], r15
mulx r15, rcx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x158 ], r15
mov [ rsp + 0x160 ], rcx
mulx rcx, r15, [ rax + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x168 ], rcx
mov [ rsp + 0x170 ], r15
mulx r15, rcx, [ rax + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x178 ], r15
mov [ rsp + 0x180 ], rcx
mulx rcx, r15, [ rax + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x188 ], rcx
mov [ rsp + 0x190 ], r15
mulx r15, rcx, [ rax + 0x30 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x198 ], r15
mov [ rsp + 0x1a0 ], rcx
mulx rcx, r15, [ rsi + 0x38 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x1a8 ], rcx
mov rcx, rdx
shl rcx, 0x1
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x1b0 ], r15
mov [ rsp + 0x1b8 ], r14
mulx r14, r15, rcx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x1c0 ], r12
mov [ rsp + 0x1c8 ], rbp
mulx rbp, r12, [ rax + 0x40 ]
test al, al
adox r10, r15
adox r14, r11
mov rdx, [ rax + 0x0 ]
mulx r15, r11, [ rsi + 0x38 ]
mov rdx, r11
adcx rdx, [ rsp + 0x1c8 ]
adcx r15, [ rsp + 0x1c0 ]
xchg rdx, rcx
mov [ rsp + 0x1d0 ], rbp
mulx rbp, r11, [ rsi + 0x28 ]
mov [ rsp + 0x1d8 ], r12
mov r12, 0x1 
mov [ rsp + 0x1e0 ], rbp
shlx rbp, [ rax + 0x30 ], r12
mov r12, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x1e8 ], r11
mov [ rsp + 0x1f0 ], r15
mulx r15, r11, rbp
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x1f8 ], r15
mov [ rsp + 0x200 ], r11
mulx r11, r15, rbp
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x208 ], rcx
mov [ rsp + 0x210 ], r11
mulx r11, rcx, [ rsp + 0x1b8 ]
mov rdx, rbp
mov [ rsp + 0x218 ], r15
mulx r15, rbp, [ rsi + 0x20 ]
mov [ rsp + 0x220 ], r15
xor r15, r15
adox rcx, [ rsp + 0x130 ]
adox r11, [ rsp + 0x128 ]
mov r15, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x228 ], r11
mov [ rsp + 0x230 ], rcx
mulx rcx, r11, [ rax + 0x8 ]
mov rdx, r8
mov [ rsp + 0x238 ], rcx
mulx rcx, r8, [ rsi + 0x30 ]
mov [ rsp + 0x240 ], r11
mov r11, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x248 ], rbp
mov [ rsp + 0x250 ], r14
mulx r14, rbp, r15
adcx rbp, [ rsp + 0x120 ]
adcx r14, [ rsp + 0x118 ]
xor rdx, rdx
adox rbp, r8
adox rcx, r14
mov rdx, [ rsi + 0x30 ]
mulx r14, r8, [ rax + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x258 ], rcx
mov [ rsp + 0x260 ], rbp
mulx rbp, rcx, [ rax + 0x0 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x268 ], rbp
mov [ rsp + 0x270 ], rcx
mulx rcx, rbp, r9
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x278 ], r14
mulx r14, r9, r13
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x280 ], r8
mulx r8, r13, rdi
adcx rbp, r9
adcx r14, rcx
mov rdx, [ rsi + 0x28 ]
mulx r9, rcx, rdi
add r10, [ rsp + 0x110 ]
mov rdx, [ rsp + 0x250 ]
adcx rdx, [ rsp + 0xd8 ]
add r10, [ rsp + 0x218 ]
adcx rdx, [ rsp + 0x210 ]
xchg rdx, r12
mov [ rsp + 0x288 ], r8
mov [ rsp + 0x290 ], r13
mulx r13, r8, [ rsi + 0x30 ]
test al, al
adox r10, [ rsp + 0x50 ]
adox r12, [ rsp + 0x48 ]
mov [ rsp + 0x298 ], r12
mov r12, [ rsp + 0x280 ]
mov [ rsp + 0x2a0 ], r10
mov r10, r12
adcx r10, [ rsp + 0x208 ]
mov [ rsp + 0x2a8 ], r9
mov r9, [ rsp + 0x278 ]
adcx r9, [ rsp + 0x1f0 ]
mov r12, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x2b0 ], r9
mov [ rsp + 0x2b8 ], r10
mulx r10, r9, rdi
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x2c0 ], r10
mov [ rsp + 0x2c8 ], r9
mulx r9, r10, [ rax + 0x8 ]
add rbp, r8
adcx r13, r14
mov rdx, [ rsp + 0x260 ]
test al, al
adox rdx, [ rsp + 0x270 ]
mov r14, [ rsp + 0x258 ]
adox r14, [ rsp + 0x268 ]
adcx rbp, rcx
adcx r13, [ rsp + 0x2a8 ]
xor rcx, rcx
adox rdx, r10
adox r9, r14
adcx rbp, [ rsp + 0x248 ]
adcx r13, [ rsp + 0x220 ]
test al, al
adox rbp, [ rsp + 0x80 ]
adox r13, [ rsp + 0x78 ]
mov r8, rdx
mov rdx, [ rsi + 0x18 ]
mulx r14, r10, [ rax + 0x10 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x2d0 ], r13
mulx r13, rcx, r15
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x2d8 ], rbp
mov [ rsp + 0x2e0 ], r9
mulx r9, rbp, rdi
mov rdx, rcx
adcx rdx, [ rsp + 0x2c8 ]
adcx r13, [ rsp + 0x2c0 ]
mov rdi, [ rsp + 0x230 ]
add rdi, [ rsp + 0xd0 ]
mov rcx, [ rsp + 0x228 ]
adcx rcx, [ rsp + 0xc8 ]
mov [ rsp + 0x2e8 ], r8
xor r8, r8
adox rdi, [ rsp + 0x1e8 ]
adox rcx, [ rsp + 0x1e0 ]
mov r8, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x2f0 ], r14
mov [ rsp + 0x2f8 ], r10
mulx r10, r14, r15
mov rdx, r11
mulx r15, r11, [ rsi + 0x38 ]
adcx rdi, rbp
adcx r9, rcx
test al, al
adox rdi, r14
adox r10, r9
adcx r8, [ rsp + 0xe8 ]
adcx r13, [ rsp + 0xe0 ]
mov rbp, r11
xor rcx, rcx
adox rbp, [ rsp + 0x40 ]
adox r15, [ rsp + 0x38 ]
mov r14, rdx
mov rdx, [ rsi + 0x30 ]
mulx r9, r11, [ rax + 0x0 ]
adcx rbp, r11
adcx r9, r15
xor rdx, rdx
adox rdi, [ rsp + 0xb0 ]
adox r10, [ rsp + 0xa8 ]
adcx rdi, [ rsp + 0x108 ]
adcx r10, [ rsp + 0x100 ]
mov rcx, [ rsp + 0x2f8 ]
mov r15, rcx
xor r11, r11
adox r15, [ rsp + 0x2e8 ]
mov rdx, [ rsp + 0x2f0 ]
adox rdx, [ rsp + 0x2e0 ]
mov rcx, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x300 ], r15
mulx r15, r11, [ rsi + 0x8 ]
mov rdx, [ rsp + 0x2d8 ]
adcx rdx, [ rsp + 0x60 ]
mov [ rsp + 0x308 ], rcx
mov rcx, [ rsp + 0x2d0 ]
adcx rcx, [ rsp + 0x58 ]
mov [ rsp + 0x310 ], r9
xor r9, r9
adox rdi, [ rsp + 0x70 ]
adox r10, [ rsp + 0x68 ]
mov r9, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x318 ], rbp
mov [ rsp + 0x320 ], r13
mulx r13, rbp, r12
adcx r9, r11
adcx r15, rcx
test al, al
adox r9, [ rsp + 0x240 ]
adox r15, [ rsp + 0x238 ]
adcx rbp, [ rsp + 0x290 ]
adcx r13, [ rsp + 0x288 ]
mov rdx, [ rax + 0x8 ]
mulx r11, r12, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x328 ], r8
mulx r8, rcx, r14
test al, al
adox rbp, [ rsp + 0x200 ]
adox r13, [ rsp + 0x1f8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x330 ], r15
mulx r15, r14, rbx
mov rdx, rcx
adcx rdx, [ rsp + 0x2a0 ]
adcx r8, [ rsp + 0x298 ]
xor rbx, rbx
adox rdx, [ rsp + 0x150 ]
adox r8, [ rsp + 0x148 ]
adcx rdx, r12
adcx r11, r8
mov r12, rdx
mov rdx, [ rax + 0x8 ]
mulx r8, rcx, [ rsi + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x338 ], r8
mulx r8, rbx, [ rsi + 0x28 ]
xor rdx, rdx
adox r12, [ rsp + 0xf8 ]
adox r11, [ rsp + 0xf0 ]
mov [ rsp + 0x340 ], r11
mov r11, rbx
adcx r11, [ rsp + 0x2b8 ]
adcx r8, [ rsp + 0x2b0 ]
mov rbx, rdi
shrd rbx, r10, 58
shr r10, 58
test al, al
adox rbp, r14
adox r15, r13
adcx r9, rbx
adcx r10, [ rsp + 0x330 ]
mov rdx, [ rsi + 0x8 ]
mulx r14, r13, [ rax + 0x10 ]
mov rdx, [ rsp + 0x30 ]
mov rbx, rdx
add rbx, [ rsp + 0x328 ]
mov [ rsp + 0x348 ], r8
mov r8, [ rsp + 0x28 ]
adcx r8, [ rsp + 0x320 ]
add rbx, [ rsp + 0x20 ]
adcx r8, [ rsp + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x350 ], r11
mov [ rsp + 0x358 ], r12
mulx r12, r11, [ rax + 0x28 ]
test al, al
adox rbp, [ rsp + 0x140 ]
adox r15, [ rsp + 0x138 ]
adcx rbp, [ rsp + 0x170 ]
adcx r15, [ rsp + 0x168 ]
xor rdx, rdx
adox rbp, rcx
adox r15, [ rsp + 0x338 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x360 ], r12
mulx r12, rcx, [ rax + 0x18 ]
adcx rbx, [ rsp + 0xa0 ]
adcx r8, [ rsp + 0x98 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x368 ], r11
mov [ rsp + 0x370 ], r12
mulx r12, r11, [ rsi + 0x10 ]
add rbp, r13
adcx r14, r15
xor rdx, rdx
adox rbp, [ rsp + 0x90 ]
adox r14, [ rsp + 0x88 ]
mov r13, r9
shrd r13, r10, 58
shr r10, 58
mov r15, r13
test al, al
adox r15, [ rsp + 0x358 ]
adox r10, [ rsp + 0x340 ]
mov r13, [ rsp + 0x10 ]
adcx r13, [ rsp + 0x1b0 ]
mov [ rsp + 0x378 ], rcx
mov rcx, [ rsp + 0x8 ]
adcx rcx, [ rsp + 0x1a8 ]
add rbx, r11
adcx r12, r8
mov rdx, [ rax + 0x20 ]
mulx r11, r8, [ rsi + 0x8 ]
mov rdx, [ rsp + 0x0 ]
mov [ rsp + 0x380 ], rcx
mov rcx, rdx
mov [ rsp + 0x388 ], r13
xor r13, r13
adox rcx, [ rsp + 0x350 ]
mov [ rsp + 0x390 ], r12
mov r12, [ rsp - 0x8 ]
adox r12, [ rsp + 0x348 ]
mov rdx, r15
shrd rdx, r10, 58
shr r10, 58
mov r13, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x398 ], r12
mov [ rsp + 0x3a0 ], rcx
mulx rcx, r12, [ rax + 0x10 ]
test al, al
adox rbp, r13
adox r10, r14
mov rdx, [ rsi + 0x28 ]
mulx r13, r14, [ rax + 0x18 ]
mov rdx, [ rsp + 0x318 ]
adcx rdx, [ rsp + 0x180 ]
mov [ rsp + 0x3a8 ], r13
mov r13, [ rsp + 0x310 ]
adcx r13, [ rsp + 0x178 ]
mov [ rsp + 0x3b0 ], r14
mov r14, 0x3a 
mov [ rsp + 0x3b8 ], rbx
bzhi rbx, r15, r14
bzhi r15, rbp, r14
adox rdx, r12
adox rcx, r13
mov r12, rdx
mov rdx, [ rax + 0x20 ]
mulx r14, r13, [ rsi + 0x10 ]
mov rdx, [ rsp + 0x300 ]
mov [ rsp + 0x3c0 ], rbx
xor rbx, rbx
adox rdx, [ rsp + 0x190 ]
mov [ rsp + 0x3c8 ], r15
mov r15, [ rsp + 0x308 ]
adox r15, [ rsp + 0x188 ]
mov rbx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x3d0 ], r14
mov [ rsp + 0x3d8 ], r13
mulx r13, r14, [ rax + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x3e0 ], r13
mov [ rsp + 0x3e8 ], r14
mulx r14, r13, [ rax + 0x20 ]
adcx rbx, r8
adcx r11, r15
mov rdx, [ rsp + 0x3b8 ]
test al, al
adox rdx, [ rsp + 0x378 ]
mov r8, [ rsp + 0x390 ]
adox r8, [ rsp + 0x370 ]
adcx rbx, [ rsp - 0x10 ]
adcx r11, [ rsp - 0x18 ]
mov r15, [ rsp + 0x388 ]
add r15, [ rsp - 0x30 ]
mov [ rsp + 0x3f0 ], r11
mov r11, [ rsp + 0x380 ]
adcx r11, [ rsp - 0x38 ]
mov [ rsp + 0x3f8 ], rbx
xor rbx, rbx
adox r12, [ rsp + 0x160 ]
adox rcx, [ rsp + 0x158 ]
adcx r15, [ rsp + 0x3b0 ]
adcx r11, [ rsp + 0x3a8 ]
add r12, [ rsp + 0x3d8 ]
adcx rcx, [ rsp + 0x3d0 ]
test al, al
adox r12, [ rsp + 0x3e8 ]
adox rcx, [ rsp + 0x3e0 ]
shrd rbp, r10, 58
shr r10, 58
add r12, [ rsp + 0x1a0 ]
adcx rcx, [ rsp + 0x198 ]
mov rbx, rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x400 ], rcx
mov [ rsp + 0x408 ], r12
mulx r12, rcx, [ rsi + 0x10 ]
test al, al
adox r15, [ rsp - 0x20 ]
adox r11, [ rsp - 0x28 ]
adcx r15, [ rsp - 0x40 ]
adcx r11, [ rsp - 0x48 ]
test al, al
adox rbx, r13
adox r14, r8
mov rdx, [ rsi + 0x18 ]
mulx r8, r13, [ rax + 0x20 ]
adcx rbx, rbp
adcx r10, r14
add r15, rcx
adcx r12, r11
mov rdx, 0x3ffffffffffffff 
mov rbp, rbx
and rbp, rdx
adox r15, [ rsp + 0xc0 ]
adox r12, [ rsp + 0xb8 ]
mov rdx, [ rax + 0x30 ]
mulx r11, rcx, [ rsi + 0x8 ]
shrd rbx, r10, 58
shr r10, 58
mov rdx, rbx
test al, al
adox rdx, [ rsp + 0x3f8 ]
adox r10, [ rsp + 0x3f0 ]
mov r14, rdx
shrd r14, r10, 58
shr r10, 58
mov rbx, r14
test al, al
adox rbx, [ rsp + 0x408 ]
adox r10, [ rsp + 0x400 ]
mov r14, rbx
shrd r14, r10, 58
shr r10, 58
mov [ rsp + 0x410 ], rbp
mov rbp, 0x3ffffffffffffff 
and rdx, rbp
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x28 ], rdx
mov rdx, r13
adox rdx, [ rsp + 0x3a0 ]
adox r8, [ rsp + 0x398 ]
adcx rdx, [ rsp + 0x368 ]
adcx r8, [ rsp + 0x360 ]
xor r13, r13
adox rdx, rcx
adox r11, r8
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mulx r13, r8, [ rax + 0x38 ]
adcx rcx, r8
adcx r13, r11
test al, al
adox rcx, r14
adox r10, r13
mov rdx, 0x3ffffffffffffff 
and rbx, rdx
mov [ rbp + 0x30 ], rbx
and rdi, rdx
mov r14, rcx
shrd r14, r10, 58
shr r10, 58
test al, al
adox r15, [ rsp + 0x1d8 ]
adox r12, [ rsp + 0x1d0 ]
adcx r15, r14
adcx r10, r12
mov r11, 0x1ffffffffffffff 
mov r8, r15
and r8, r11
and rcx, rdx
shrd r15, r10, 57
shr r10, 57
mov [ rbp + 0x38 ], rcx
and r9, rdx
mov r13, [ rsp + 0x3c8 ]
mov [ rbp + 0x18 ], r13
adox r15, rdi
mov r13, 0x0 
adox r10, r13
mov rbx, r15
shrd rbx, r10, 58
lea rbx, [ rbx + r9 ]
mov rdi, rbx
and rdi, rdx
shr rbx, 58
mov [ rbp + 0x8 ], rdi
add rbx, [ rsp + 0x3c0 ]
and r15, rdx
mov r14, [ rsp + 0x410 ]
mov [ rbp + 0x20 ], r14
mov [ rbp + 0x10 ], rbx
mov [ rbp + 0x40 ], r8
mov [ rbp + 0x0 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1176
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.1254
; seed 2089293026205924 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 6844744 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=84, initial num_batches=31): 129277 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.01888704676171965
; number reverted permutation / tried permutation: 54352 / 90253 =60.222%
; number reverted decision / tried decision: 49485 / 89746 =55.139%
; validated in 4.784s
