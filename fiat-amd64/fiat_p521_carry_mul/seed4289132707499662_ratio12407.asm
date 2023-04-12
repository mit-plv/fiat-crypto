SECTION .text
	GLOBAL fiat_p521_carry_mul
fiat_p521_carry_mul:
sub rsp, 1128
mov rax, rdx
mov rdx, [ rsi + 0x38 ]
mulx r11, r10, [ rax + 0x8 ]
mov rdx, [ rax + 0x38 ]
lea rcx, [rdx + rdx]
mov rdx, [ rax + 0x38 ]
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rax + 0x20 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x28 ]
mov rdx, 0x1 
mov [ rsp - 0x60 ], r14
shlx r14, [ rax + 0x30 ], rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x48 ], rbp
mov [ rsp - 0x40 ], rbx
mulx rbx, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], rdi
mov [ rsp - 0x30 ], r15
mulx r15, rdi, [ rax + 0x0 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x28 ], rbx
mov [ rsp - 0x20 ], rbp
mulx rbp, rbx, [ rsi + 0x20 ]
mov rdx, rcx
mov [ rsp - 0x18 ], r15
mulx r15, rcx, [ rsi + 0x28 ]
mov [ rsp - 0x10 ], r15
mov r15, [ rax + 0x10 ]
mov [ rsp - 0x8 ], rcx
lea rcx, [r15 + r15]
mov r15, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x0 ], rdi
mov [ rsp + 0x8 ], r13
mulx r13, rdi, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x10 ], r13
mov [ rsp + 0x18 ], rdi
mulx rdi, r13, rcx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x20 ], r12
mov [ rsp + 0x28 ], r9
mulx r9, r12, r14
mov rdx, r15
mov [ rsp + 0x30 ], r8
mulx r8, r15, [ rsi + 0x18 ]
mov [ rsp + 0x38 ], r8
mov r8, rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x40 ], r15
mov [ rsp + 0x48 ], rbp
mulx rbp, r15, [ rsi + 0x10 ]
mov rdx, 0x1 
mov [ rsp + 0x50 ], rbp
shlx rbp, [ rax + 0x20 ], rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x58 ], r15
mov [ rsp + 0x60 ], rbx
mulx rbx, r15, rbp
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x68 ], r9
mov [ rsp + 0x70 ], r12
mulx r12, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x78 ], r12
mov [ rsp + 0x80 ], r9
mulx r9, r12, [ rax + 0x30 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x88 ], r9
mov [ rsp + 0x90 ], r12
mulx r12, r9, [ rax + 0x0 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x98 ], r12
mov [ rsp + 0xa0 ], r9
mulx r9, r12, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0xa8 ], r9
mov [ rsp + 0xb0 ], r12
mulx r12, r9, r8
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xb8 ], r12
mov [ rsp + 0xc0 ], r9
mulx r9, r12, [ rax + 0x0 ]
mov rdx, r8
mov [ rsp + 0xc8 ], r9
mulx r9, r8, [ rsi + 0x10 ]
mov [ rsp + 0xd0 ], r12
mov r12, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0xd8 ], r9
mov [ rsp + 0xe0 ], r8
mulx r8, r9, [ rsi + 0x8 ]
mov rdx, rbp
mov [ rsp + 0xe8 ], r8
mulx r8, rbp, [ rsi + 0x30 ]
mov [ rsp + 0xf0 ], r9
mov r9, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xf8 ], r8
mov [ rsp + 0x100 ], rbp
mulx rbp, r8, [ rsi + 0x18 ]
mov rdx, 0x1 
mov [ rsp + 0x108 ], rbp
shlx rbp, [ rax + 0x18 ], rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x110 ], r8
mov [ rsp + 0x118 ], rbx
mulx rbx, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x120 ], rbx
mov [ rsp + 0x128 ], r8
mulx r8, rbx, [ rax + 0x18 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x130 ], r8
mov [ rsp + 0x138 ], rbx
mulx rbx, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x140 ], rbx
mov [ rsp + 0x148 ], r8
mulx r8, rbx, rbp
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x150 ], r15
mov r15, rdx
shl r15, 0x1
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x158 ], r11
mov [ rsp + 0x160 ], r10
mulx r10, r11, r15
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x168 ], r8
mulx r8, r15, [ rax + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x170 ], r8
mov [ rsp + 0x178 ], r15
mulx r15, r8, [ rax + 0x18 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x180 ], r15
mov [ rsp + 0x188 ], r8
mulx r8, r15, rbp
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x190 ], r8
mov [ rsp + 0x198 ], r15
mulx r15, r8, r12
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x1a0 ], r15
mov [ rsp + 0x1a8 ], r8
mulx r8, r15, rbp
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x1b0 ], r8
mulx r8, rbp, [ rax + 0x0 ]
mov rdx, r14
mov [ rsp + 0x1b8 ], r8
mulx r8, r14, [ rsi + 0x28 ]
mov [ rsp + 0x1c0 ], rbp
mov [ rsp + 0x1c8 ], r15
mulx r15, rbp, [ rsi + 0x40 ]
test al, al
adox r11, r13
adox rdi, r10
mov r13, 0x1 
shlx r10, [ rax + 0x28 ], r13
mov [ rsp + 0x1d0 ], r15
mulx r15, r13, [ rsi + 0x38 ]
mov [ rsp + 0x1d8 ], rbp
mov rbp, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x1e0 ], rdi
mov [ rsp + 0x1e8 ], r11
mulx r11, rdi, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x1f0 ], r8
mov [ rsp + 0x1f8 ], r14
mulx r14, r8, r10
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x200 ], r11
mov [ rsp + 0x208 ], rdi
mulx rdi, r11, [ rsi + 0x30 ]
adcx r8, r13
adcx r15, r14
mov rdx, [ rsi + 0x40 ]
mulx r14, r13, [ rax + 0x0 ]
mov rdx, rcx
mov [ rsp + 0x210 ], r15
mulx r15, rcx, [ rsi + 0x40 ]
mov rdx, r10
mov [ rsp + 0x218 ], r8
mulx r8, r10, [ rsi + 0x38 ]
test al, al
adox rcx, rbx
adox r15, [ rsp + 0x168 ]
adcx r13, [ rsp + 0x160 ]
adcx r14, [ rsp + 0x158 ]
mov rbx, [ rsp + 0x150 ]
mov [ rsp + 0x220 ], r8
mov r8, rbx
mov [ rsp + 0x228 ], r10
xor r10, r10
adox r8, [ rsp + 0x198 ]
mov [ rsp + 0x230 ], rdi
mov rdi, [ rsp + 0x118 ]
adox rdi, [ rsp + 0x190 ]
adcx r13, [ rsp + 0x208 ]
adcx r14, [ rsp + 0x200 ]
mulx r10, rbx, [ rsi + 0x28 ]
mov [ rsp + 0x238 ], r11
mov [ rsp + 0x240 ], r10
mulx r10, r11, [ rsi + 0x30 ]
test al, al
adox r8, r11
adox r10, rdi
adcx rcx, [ rsp + 0x100 ]
adcx r15, [ rsp + 0xf8 ]
test al, al
adox r13, [ rsp + 0x188 ]
adox r14, [ rsp + 0x180 ]
xchg rdx, rbp
mulx r11, rdi, [ rsi + 0x30 ]
adcx r8, [ rsp + 0x1f8 ]
adcx r10, [ rsp + 0x1f0 ]
mov [ rsp + 0x248 ], r11
mov r11, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x250 ], rdi
mov [ rsp + 0x258 ], r10
mulx r10, rdi, r9
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x260 ], r8
mov [ rsp + 0x268 ], r10
mulx r10, r8, r12
add rcx, rbx
adcx r15, [ rsp + 0x240 ]
mov rdx, r9
mulx rbx, r9, [ rsi + 0x40 ]
mov rdx, rbp
mov [ rsp + 0x270 ], rbx
mulx rbx, rbp, [ rsi + 0x20 ]
test al, al
adox rcx, [ rsp + 0x70 ]
adox r15, [ rsp + 0x68 ]
mov rdx, [ rsp + 0x1c8 ]
mov [ rsp + 0x278 ], r9
mov r9, rdx
adcx r9, [ rsp + 0x1e8 ]
mov [ rsp + 0x280 ], r15
mov r15, [ rsp + 0x1b0 ]
adcx r15, [ rsp + 0x1e0 ]
xor rdx, rdx
adox r13, [ rsp + 0x60 ]
adox r14, [ rsp + 0x48 ]
adcx r9, rdi
adcx r15, [ rsp + 0x268 ]
test al, al
adox r13, [ rsp + 0x110 ]
adox r14, [ rsp + 0x108 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x288 ], rcx
mulx rcx, rdi, r11
adcx r9, rbp
adcx rbx, r15
add r9, rdi
adcx rcx, rbx
add r9, [ rsp + 0xe0 ]
adcx rcx, [ rsp + 0xd8 ]
xor rdx, rdx
adox r13, [ rsp + 0x58 ]
adox r14, [ rsp + 0x50 ]
mov r11, [ rax + 0x40 ]
mov rbp, r11
shl rbp, 0x1
mov r11, r8
test al, al
adox r11, [ rsp + 0x260 ]
adox r10, [ rsp + 0x258 ]
mov rdx, [ rax + 0x40 ]
mulx r15, r8, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mulx rbx, rdi, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x290 ], rbx
mov [ rsp + 0x298 ], rdi
mulx rdi, rbx, rbp
mov rdx, rbp
mov [ rsp + 0x2a0 ], rcx
mulx rcx, rbp, [ rsi + 0x28 ]
adcx r11, rbx
adcx rdi, r10
mulx rbx, r10, [ rsi + 0x30 ]
test al, al
adox r11, [ rsp + 0x80 ]
adox rdi, [ rsp + 0x78 ]
adcx r13, [ rsp + 0x30 ]
adcx r14, [ rsp + 0x28 ]
mov [ rsp + 0x2a8 ], rdi
mov rdi, [ rsp + 0x1a8 ]
mov [ rsp + 0x2b0 ], r11
mov r11, rdi
add r11, [ rsp + 0x1d8 ]
mov [ rsp + 0x2b8 ], rcx
mov rcx, [ rsp + 0x1a0 ]
adcx rcx, [ rsp + 0x1d0 ]
mov [ rsp + 0x2c0 ], rbp
mulx rbp, rdi, [ rsi + 0x10 ]
add r13, r8
adcx r15, r14
mulx r14, r8, [ rsi + 0x8 ]
add r9, r8
adcx r14, [ rsp + 0x2a0 ]
add r9, [ rsp + 0x298 ]
adcx r14, [ rsp + 0x290 ]
xor r8, r8
adox r11, r10
adox rbx, rcx
mov r10, rdx
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x2c8 ], r15
mov [ rsp + 0x2d0 ], r13
mulx r13, r15, r10
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x2d8 ], r8
mov [ rsp + 0x2e0 ], rcx
mulx rcx, r8, [ rax + 0x8 ]
mov rdx, r9
shrd rdx, r14, 58
shr r14, 58
mov [ rsp + 0x2e8 ], rcx
mov rcx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x2f0 ], r8
mov [ rsp + 0x2f8 ], r14
mulx r14, r8, [ rax + 0x10 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x300 ], rcx
mov [ rsp + 0x308 ], rbp
mulx rbp, rcx, r10
xor rdx, rdx
adox r11, [ rsp + 0x20 ]
adox rbx, [ rsp + 0x8 ]
mov rdx, 0x3a 
mov [ rsp + 0x310 ], rbp
bzhi rbp, r9, rdx
adox r11, [ rsp + 0x178 ]
adox rbx, [ rsp + 0x170 ]
add r11, r8
adcx r14, rbx
xor r9, r9
adox r15, [ rsp + 0xa0 ]
adox r13, [ rsp + 0x98 ]
mov r8, [ rsp + 0x40 ]
mov rbx, r8
adcx rbx, [ rsp + 0x288 ]
mov rdx, [ rsp + 0x38 ]
adcx rdx, [ rsp + 0x280 ]
mov r8, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x318 ], rbp
mulx rbp, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x320 ], rbp
mov [ rsp + 0x328 ], r9
mulx r9, rbp, [ rax + 0x8 ]
test al, al
adox rbx, rdi
adox r8, [ rsp + 0x308 ]
mov rdx, r12
mulx rdi, r12, [ rsi + 0x30 ]
adcx r11, [ rsp + 0x138 ]
adcx r14, [ rsp + 0x130 ]
test al, al
adox r15, [ rsp + 0x238 ]
adox r13, [ rsp + 0x230 ]
mov rdx, [ rsp + 0x278 ]
adcx rdx, [ rsp + 0x228 ]
mov [ rsp + 0x330 ], r14
mov r14, [ rsp + 0x270 ]
adcx r14, [ rsp + 0x220 ]
test al, al
adox r15, [ rsp + 0x18 ]
adox r13, [ rsp + 0x10 ]
mov [ rsp + 0x338 ], r11
mov r11, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x340 ], r13
mov [ rsp + 0x348 ], r15
mulx r15, r13, [ rsi + 0x18 ]
adcx rbx, [ rsp + 0x0 ]
adcx r8, [ rsp - 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x350 ], r15
mov [ rsp + 0x358 ], r13
mulx r13, r15, [ rsi + 0x20 ]
xor rdx, rdx
adox rbx, [ rsp + 0x2e0 ]
adox r8, [ rsp + 0x2d8 ]
adcx rbx, [ rsp + 0x300 ]
adcx r8, [ rsp + 0x2f8 ]
test al, al
adox r11, [ rsp + 0x250 ]
adox r14, [ rsp + 0x248 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x360 ], r13
mov [ rsp + 0x368 ], r15
mulx r15, r13, r10
adcx r11, [ rsp - 0x8 ]
adcx r14, [ rsp - 0x10 ]
add r11, r13
adcx r15, r14
add r11, [ rsp - 0x30 ]
adcx r15, [ rsp - 0x38 ]
mov rdx, rcx
test al, al
adox rdx, [ rsp + 0xc0 ]
mov r10, [ rsp + 0xb8 ]
adox r10, [ rsp + 0x310 ]
mov rcx, rdx
mov rdx, [ rax + 0x10 ]
mulx r14, r13, [ rsi + 0x20 ]
adcx rcx, [ rsp + 0xd0 ]
adcx r10, [ rsp + 0xc8 ]
mov rdx, r12
add rdx, [ rsp + 0x218 ]
adcx rdi, [ rsp + 0x210 ]
mov r12, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x370 ], r15
mov [ rsp + 0x378 ], r11
mulx r11, r15, [ rsi + 0x10 ]
mov rdx, 0x3ffffffffffffff 
mov [ rsp + 0x380 ], r11
mov r11, rbx
and r11, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x388 ], r11
mov [ rsp + 0x390 ], r15
mulx r15, r11, [ rax + 0x18 ]
shrd rbx, r8, 58
shr r8, 58
test al, al
adox r12, [ rsp + 0x2c0 ]
adox rdi, [ rsp + 0x2b8 ]
adcx rcx, [ rsp + 0x2f0 ]
adcx r10, [ rsp + 0x2e8 ]
xor rdx, rdx
adox r12, [ rsp + 0x1c0 ]
adox rdi, [ rsp + 0x1b8 ]
adcx rcx, r13
adcx r14, r10
add r12, rbp
adcx r9, rdi
mov rdx, [ rsi + 0x10 ]
mulx r13, rbp, [ rax + 0x8 ]
mov rdx, [ rsp + 0x2b0 ]
xor r10, r10
adox rdx, [ rsp + 0xf0 ]
mov rdi, [ rsp + 0x2a8 ]
adox rdi, [ rsp + 0xe8 ]
mov [ rsp + 0x398 ], r14
mov r14, [ rsp + 0x348 ]
adcx r14, [ rsp + 0x368 ]
mov [ rsp + 0x3a0 ], rcx
mov rcx, [ rsp + 0x340 ]
adcx rcx, [ rsp + 0x360 ]
test al, al
adox rdx, [ rsp - 0x20 ]
adox rdi, [ rsp - 0x28 ]
adcx rdx, rbx
adcx r8, rdi
mov rbx, rdx
mov rdx, [ rsi + 0x0 ]
mulx r10, rdi, [ rax + 0x38 ]
xor rdx, rdx
adox r14, [ rsp + 0x358 ]
adox rcx, [ rsp + 0x350 ]
adcx r12, [ rsp + 0x328 ]
adcx r9, [ rsp + 0x320 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x3a8 ], r10
mov [ rsp + 0x3b0 ], rdi
mulx rdi, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x3b8 ], rdi
mov [ rsp + 0x3c0 ], r10
mulx r10, rdi, [ rax + 0x18 ]
xor rdx, rdx
adox r12, r11
adox r15, r9
mov rdx, [ rax + 0x20 ]
mulx r9, r11, [ rsi + 0x0 ]
adcx r12, r11
adcx r9, r15
mov rdx, [ rsi + 0x8 ]
mulx r11, r15, [ rax + 0x10 ]
mov rdx, rbx
shrd rdx, r8, 58
shr r8, 58
mov [ rsp + 0x3c8 ], r9
mov r9, 0x3ffffffffffffff 
and rbx, r9
adox r14, [ rsp + 0x390 ]
adox rcx, [ rsp + 0x380 ]
mov r9, rbp
adcx r9, [ rsp + 0x378 ]
adcx r13, [ rsp + 0x370 ]
add r14, [ rsp + 0x148 ]
adcx rcx, [ rsp + 0x140 ]
mov rbp, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x3d0 ], rbx
mov [ rsp + 0x3d8 ], r12
mulx r12, rbx, [ rax + 0x28 ]
add r9, r15
adcx r11, r13
mov rdx, rdi
add rdx, [ rsp + 0x3a0 ]
adcx r10, [ rsp + 0x398 ]
xor rdi, rdi
adox r9, [ rsp + 0x3c0 ]
adox r11, [ rsp + 0x3b8 ]
adcx r9, rbp
adcx r8, r11
test al, al
adox rdx, [ rsp + 0x128 ]
adox r10, [ rsp + 0x120 ]
adcx r14, [ rsp + 0x3b0 ]
adcx rcx, [ rsp + 0x3a8 ]
mov r15, r9
shrd r15, r8, 58
shr r8, 58
mov rbp, r15
test al, al
adox rbp, [ rsp + 0x3d8 ]
adox r8, [ rsp + 0x3c8 ]
mov r13, rbp
shrd r13, r8, 58
shr r8, 58
mov r11, [ rsp + 0x338 ]
xor r15, r15
adox r11, [ rsp - 0x40 ]
mov rdi, [ rsp + 0x330 ]
adox rdi, [ rsp - 0x48 ]
adcx r11, [ rsp + 0xb0 ]
adcx rdi, [ rsp + 0xa8 ]
mov [ rsp + 0x3e0 ], rcx
xor rcx, rcx
adox rdx, rbx
adox r12, r10
adcx rdx, [ rsp + 0x90 ]
adcx r12, [ rsp + 0x88 ]
mov r15, 0x3a 
bzhi rbx, rbp, r15
adox r11, r13
adox r8, rdi
bzhi r10, r11, r15
shrd r11, r8, 58
shr r8, 58
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x28 ], r10
test al, al
adox rdx, r11
adox r8, r12
bzhi r13, rdx, r15
shrd rdx, r8, 58
shr r8, 58
add r14, rdx
adcx r8, [ rsp + 0x3e0 ]
mov [ rbp + 0x30 ], r13
bzhi rdi, r14, r15
shrd r14, r8, 58
shr r8, 58
mov r12, r14
xor r10, r10
adox r12, [ rsp + 0x2d0 ]
adox r8, [ rsp + 0x2c8 ]
mov [ rbp + 0x38 ], rdi
mov rcx, r12
shrd rcx, r8, 57
shr r8, 57
test al, al
adox rcx, [ rsp + 0x318 ]
adox r8, r10
mov r11, 0x1ffffffffffffff 
and r12, r11
bzhi r13, rcx, r15
shrd rcx, r8, 58
mov [ rbp + 0x40 ], r12
add rcx, [ rsp + 0x388 ]
bzhi rdx, rcx, r15
shr rcx, 58
bzhi rdi, r9, r15
add rcx, [ rsp + 0x3d0 ]
mov [ rbp + 0x8 ], rdx
mov [ rbp + 0x18 ], rdi
mov [ rbp + 0x10 ], rcx
mov [ rbp + 0x20 ], rbx
mov [ rbp + 0x0 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1128
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.2407
; seed 4289132707499662 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 40019 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=86, initial num_batches=31): 734 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.01834128788825308
; number reverted permutation / tried permutation: 298 / 499 =59.719%
; number reverted decision / tried decision: 269 / 500 =53.800%
; validated in 3.616s
