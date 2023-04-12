SECTION .text
	GLOBAL fiat_p521_carry_mul
fiat_p521_carry_mul:
sub rsp, 1016
mov rax, [ rdx + 0x38 ]
mov r10, rax
shl r10, 0x1
mov rax, rdx
mov rdx, [ rdx + 0x20 ]
mulx rcx, r11, [ rsi + 0x20 ]
mov rdx, r10
mulx r8, r10, [ rsi + 0x38 ]
mov r9, rdx
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x60 ], r14
lea r14, [rdx + rdx]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], rbp
mov [ rsp - 0x40 ], rbx
mulx rbx, rbp, [ rax + 0x20 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x38 ], rcx
mov [ rsp - 0x30 ], r11
mulx r11, rcx, [ rsi + 0x10 ]
mov rdx, 0x1 
mov [ rsp - 0x28 ], r11
shlx r11, [ rax + 0x40 ], rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x20 ], rcx
mov [ rsp - 0x18 ], rbx
mulx rbx, rcx, r9
mov rdx, r11
mov [ rsp - 0x10 ], rbp
mulx rbp, r11, [ rsi + 0x20 ]
mov [ rsp - 0x8 ], rdi
mov [ rsp + 0x0 ], r15
mulx r15, rdi, [ rsi + 0x10 ]
mov [ rsp + 0x8 ], r8
mov r8, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x10 ], r10
mov [ rsp + 0x18 ], r15
mulx r15, r10, [ rsi + 0x28 ]
mov rdx, r8
mov [ rsp + 0x20 ], r15
mulx r15, r8, [ rsi + 0x8 ]
mov [ rsp + 0x28 ], r10
mov r10, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x30 ], rdi
mov [ rsp + 0x38 ], r13
mulx r13, rdi, r14
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x40 ], r12
mov [ rsp + 0x48 ], rbp
mulx rbp, r12, [ rax + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x50 ], rbp
mov [ rsp + 0x58 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x60 ], r11
mov [ rsp + 0x68 ], r12
mulx r12, r11, [ rsi + 0x18 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x70 ], r12
mov r12, rdx
shl r12, 0x1
imul rdx, [ rax + 0x20 ], 0x2
mov [ rsp + 0x78 ], r11
mov r11, rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x80 ], rbp
mov [ rsp + 0x88 ], r15
mulx r15, rbp, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x90 ], r15
mov [ rsp + 0x98 ], rbp
mulx rbp, r15, [ rax + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xa0 ], rbp
mov [ rsp + 0xa8 ], r15
mulx r15, rbp, r12
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xb0 ], r8
mov [ rsp + 0xb8 ], rbx
mulx rbx, r8, r9
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xc0 ], rbx
mov [ rsp + 0xc8 ], r8
mulx r8, rbx, [ rax + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0xd0 ], r8
mov [ rsp + 0xd8 ], rbx
mulx rbx, r8, [ rsi + 0x28 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0xe0 ], rbx
mov [ rsp + 0xe8 ], r8
mulx r8, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xf0 ], r8
mov [ rsp + 0xf8 ], rbx
mulx rbx, r8, [ rax + 0x8 ]
mov rdx, 0x1 
mov [ rsp + 0x100 ], rbx
shlx rbx, [ rax + 0x10 ], rdx
mov rdx, [ rax + 0x40 ]
mov [ rsp + 0x108 ], r8
mov [ rsp + 0x110 ], rcx
mulx rcx, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x118 ], rcx
mov [ rsp + 0x120 ], r8
mulx r8, rcx, rbx
mov rdx, rbx
mov [ rsp + 0x128 ], r15
mulx r15, rbx, [ rsi + 0x40 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x130 ], r15
mov [ rsp + 0x138 ], rbx
mulx rbx, r15, r12
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x140 ], rbx
mov [ rsp + 0x148 ], r15
mulx r15, rbx, [ rax + 0x20 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x150 ], r15
mov r15, rdx
shl r15, 0x1
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x158 ], rbx
mov [ rsp + 0x160 ], rbp
mulx rbp, rbx, r15
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x168 ], r8
mov [ rsp + 0x170 ], rcx
mulx rcx, r8, r11
mov rdx, r11
mov [ rsp + 0x178 ], rcx
mulx rcx, r11, [ rsi + 0x38 ]
mov [ rsp + 0x180 ], r8
mov r8, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x188 ], rbp
mov [ rsp + 0x190 ], rbx
mulx rbx, rbp, r10
mov rdx, r10
mov [ rsp + 0x198 ], rbx
mulx rbx, r10, [ rsi + 0x38 ]
mov [ rsp + 0x1a0 ], rbx
imul rbx, [ rax + 0x8 ], 0x2
mov [ rsp + 0x1a8 ], r10
mov r10, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x1b0 ], rbp
mov [ rsp + 0x1b8 ], r13
mulx r13, rbp, rbx
test al, al
adox rdi, r11
adox rcx, [ rsp + 0x1b8 ]
mov rdx, r15
mulx r11, r15, [ rsi + 0x38 ]
adcx rdi, [ rsp + 0x190 ]
adcx rcx, [ rsp + 0x188 ]
add rbp, [ rsp + 0x170 ]
adcx r13, [ rsp + 0x168 ]
xor rbx, rbx
adox rdi, [ rsp + 0x160 ]
adox rcx, [ rsp + 0x128 ]
mov [ rsp + 0x1c0 ], rcx
mov rcx, r15
adcx rcx, [ rsp + 0x180 ]
adcx r11, [ rsp + 0x178 ]
xor r15, r15
adox rcx, [ rsp + 0x148 ]
adox r11, [ rsp + 0x140 ]
mov rbx, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x1c8 ], rdi
mulx rdi, r15, r8
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x1d0 ], r13
mov [ rsp + 0x1d8 ], rbp
mulx rbp, r13, r14
adcx rcx, [ rsp + 0x110 ]
adcx r11, [ rsp + 0xb8 ]
mov rdx, r14
mov [ rsp + 0x1e0 ], r11
mulx r11, r14, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1e8 ], rcx
mov [ rsp + 0x1f0 ], rbp
mulx rbp, rcx, r12
mov rdx, r14
test al, al
adox rdx, [ rsp + 0x138 ]
adox r11, [ rsp + 0x130 ]
mov r14, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x1f8 ], rbp
mov [ rsp + 0x200 ], rcx
mulx rcx, rbp, r9
adcx r14, r15
adcx rdi, r11
mov rdx, r13
add rdx, [ rsp + 0x1d8 ]
mov r15, [ rsp + 0x1d0 ]
adcx r15, [ rsp + 0x1f0 ]
mov r13, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x208 ], rdi
mulx rdi, r11, r8
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x210 ], r14
mulx r14, r8, rbx
add r13, r11
adcx rdi, r15
xor rdx, rdx
adox r13, r8
adox r14, rdi
adcx r13, [ rsp + 0x200 ]
adcx r14, [ rsp + 0x1f8 ]
mov r15, rbp
test al, al
adox r15, [ rsp + 0x1c8 ]
adox rcx, [ rsp + 0x1c0 ]
mov rdx, [ rsi + 0x40 ]
mulx r11, rbp, rbx
mov rdx, r12
mulx r8, r12, [ rsi + 0x38 ]
mov rdi, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x218 ], rcx
mov [ rsp + 0x220 ], r15
mulx r15, rcx, rbx
mov rdx, rcx
adcx rdx, [ rsp + 0x210 ]
adcx r15, [ rsp + 0x208 ]
test al, al
adox rbp, r12
adox r8, r11
mov rbx, rdx
mov rdx, [ rsi + 0x10 ]
mulx r12, r11, r9
adcx rbp, [ rsp + 0xc8 ]
adcx r8, [ rsp + 0xc0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x228 ], r8
mulx r8, rcx, [ rax + 0x0 ]
xor rdx, rdx
adox r13, r11
adox r12, r14
mov r14, [ rsp + 0x1b0 ]
mov r11, r14
adcx r11, [ rsp + 0x220 ]
mov [ rsp + 0x230 ], rbp
mov rbp, [ rsp + 0x198 ]
adcx rbp, [ rsp + 0x218 ]
xor r14, r14
adox r13, [ rsp + 0xb0 ]
adox r12, [ rsp + 0x88 ]
adcx r11, rcx
adcx r8, rbp
mov rdx, rdi
mulx rcx, rdi, [ rsi + 0x20 ]
mov rbp, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x238 ], r15
mulx r15, r14, [ rax + 0x0 ]
xor rdx, rdx
adox r11, [ rsp + 0x80 ]
adox r8, [ rsp + 0x68 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x240 ], r8
mov [ rsp + 0x248 ], r11
mulx r11, r8, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x250 ], r11
mov [ rsp + 0x258 ], r8
mulx r8, r11, r9
mov rdx, [ rsp + 0x1e8 ]
adcx rdx, [ rsp + 0x60 ]
mov [ rsp + 0x260 ], r15
mov r15, [ rsp + 0x1e0 ]
adcx r15, [ rsp + 0x48 ]
test al, al
adox r13, [ rsp + 0x40 ]
adox r12, [ rsp + 0x38 ]
mov [ rsp + 0x268 ], r15
mov r15, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x270 ], r14
mov [ rsp + 0x278 ], r8
mulx r8, r14, [ rsi + 0x8 ]
mov rdx, 0x3ffffffffffffff 
mov [ rsp + 0x280 ], r15
mov r15, r13
and r15, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x288 ], r15
mov [ rsp + 0x290 ], r8
mulx r8, r15, [ rsi + 0x28 ]
adox rbx, rdi
adox rcx, [ rsp + 0x238 ]
shrd r13, r12, 58
shr r12, 58
xor rdx, rdx
adox rbx, r11
adox rcx, [ rsp + 0x278 ]
mov rdx, [ rsi + 0x40 ]
mulx r11, rdi, r9
adcx rdi, [ rsp + 0x1a8 ]
adcx r11, [ rsp + 0x1a0 ]
add rbx, [ rsp + 0x30 ]
adcx rcx, [ rsp + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x298 ], r8
mulx r8, r9, [ rax + 0x8 ]
add rbx, r14
adcx rcx, [ rsp + 0x290 ]
test al, al
adox rbx, [ rsp + 0x108 ]
adox rcx, [ rsp + 0x100 ]
mov rdx, [ rsp + 0x270 ]
mov r14, rdx
adcx r14, [ rsp + 0x280 ]
mov [ rsp + 0x2a0 ], r15
mov r15, [ rsp + 0x260 ]
adcx r15, [ rsp + 0x268 ]
xor rdx, rdx
adox r14, r9
adox r8, r15
adcx rbx, r13
adcx r12, rcx
mov rdx, [ rsi + 0x40 ]
mulx r9, r13, rbp
mov rdx, rbx
shrd rdx, r12, 58
shr r12, 58
mov rbp, rdx
mov rdx, [ rsi + 0x38 ]
mulx r15, rcx, [ rax + 0x8 ]
xor rdx, rdx
adox r13, [ rsp + 0x10 ]
adox r9, [ rsp + 0x8 ]
adcx rdi, [ rsp + 0xd8 ]
adcx r11, [ rsp + 0xd0 ]
add rdi, [ rsp + 0x258 ]
adcx r11, [ rsp + 0x250 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x2a8 ], r11
mov [ rsp + 0x2b0 ], rdi
mulx rdi, r11, r10
test al, al
adox r13, r11
adox rdi, r9
mov rdx, [ rsi + 0x0 ]
mulx r11, r9, [ rax + 0x10 ]
mov rdx, r9
adcx rdx, [ rsp + 0x248 ]
adcx r11, [ rsp + 0x240 ]
xor r9, r9
adox rdx, rbp
adox r12, r11
mov rbp, rdx
mov rdx, [ rax + 0x0 ]
mulx r9, r11, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x2b8 ], r15
mov [ rsp + 0x2c0 ], rcx
mulx rcx, r15, r10
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x2c8 ], r9
mov [ rsp + 0x2d0 ], r11
mulx r11, r9, [ rax + 0x0 ]
adcx r13, [ rsp + 0x2a0 ]
adcx rdi, [ rsp + 0x298 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x2d8 ], r12
mov [ rsp + 0x2e0 ], rbp
mulx rbp, r12, [ rsi + 0x8 ]
xor rdx, rdx
adox r15, r9
adox r11, rcx
adcx r14, [ rsp + 0xf8 ]
adcx r8, [ rsp + 0xf0 ]
mov rdx, r10
mulx rcx, r10, [ rsi + 0x28 ]
test al, al
adox r13, [ rsp + 0x58 ]
adox rdi, [ rsp + 0x50 ]
adcx r14, [ rsp + 0xa8 ]
adcx r8, [ rsp + 0xa0 ]
mov rdx, 0x3ffffffffffffff 
mov r9, [ rsp + 0x2e0 ]
and r9, rdx
mov rdx, r10
adox rdx, [ rsp + 0x230 ]
adox rcx, [ rsp + 0x228 ]
adcx rdx, [ rsp + 0x2d0 ]
adcx rcx, [ rsp + 0x2c8 ]
mov r10, [ rsp + 0x2d8 ]
mov [ rsp + 0x2e8 ], r9
mov r9, [ rsp + 0x2e0 ]
shrd r9, r10, 58
shr r10, 58
mov [ rsp + 0x2f0 ], r11
xor r11, r11
adox r14, r9
adox r10, r8
mov r8, rdx
mov rdx, [ rax + 0x10 ]
mulx r11, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x2f8 ], r15
mov [ rsp + 0x300 ], r10
mulx r10, r15, [ rax + 0x20 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x308 ], r14
mov [ rsp + 0x310 ], r11
mulx r11, r14, [ rsi + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x318 ], r9
mov [ rsp + 0x320 ], rbp
mulx rbp, r9, [ rsi + 0x40 ]
adcx r13, r14
adcx r11, rdi
mov rdx, [ rsi + 0x18 ]
mulx r14, rdi, [ rax + 0x18 ]
test al, al
adox r9, [ rsp + 0x2c0 ]
adox rbp, [ rsp + 0x2b8 ]
mov rdx, [ rsp + 0x0 ]
mov [ rsp + 0x328 ], rbp
mov rbp, rdx
adcx rbp, [ rsp + 0x2b0 ]
mov [ rsp + 0x330 ], r9
mov r9, [ rsp - 0x8 ]
adcx r9, [ rsp + 0x2a8 ]
test al, al
adox rbp, rdi
adox r14, r9
mov rdx, [ rax + 0x18 ]
mulx r9, rdi, [ rsi + 0x8 ]
adcx rbp, r15
adcx r10, r14
xor rdx, rdx
adox r8, [ rsp + 0x78 ]
adox rcx, [ rsp + 0x70 ]
mov rdx, [ rax + 0x20 ]
mulx r14, r15, [ rsi + 0x0 ]
adcx rbp, r12
adcx r10, [ rsp + 0x320 ]
test al, al
adox r8, [ rsp + 0x318 ]
adox rcx, [ rsp + 0x310 ]
adcx r8, rdi
adcx r9, rcx
mov rdx, [ rax + 0x28 ]
mulx rdi, r12, [ rsi + 0x10 ]
add r8, r15
adcx r14, r9
mov rdx, [ rsi + 0x0 ]
mulx rcx, r15, [ rax + 0x38 ]
mov rdx, [ rsp + 0x300 ]
mov r9, [ rsp + 0x308 ]
shrd r9, rdx, 58
shr rdx, 58
mov [ rsp + 0x338 ], r10
mov r10, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x340 ], rbp
mov [ rsp + 0x348 ], rcx
mulx rcx, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x350 ], r15
mov [ rsp + 0x358 ], rdi
mulx rdi, r15, [ rax + 0x18 ]
test al, al
adox r8, r9
adox r10, r14
mov rdx, [ rsi + 0x30 ]
mulx r9, r14, [ rax + 0x8 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x360 ], r12
mov [ rsp + 0x368 ], rcx
mulx rcx, r12, [ rsi + 0x0 ]
adcx r13, r15
adcx rdi, r11
test al, al
adox r13, [ rsp - 0x10 ]
adox rdi, [ rsp - 0x18 ]
mov rdx, r14
adcx rdx, [ rsp + 0x2f8 ]
adcx r9, [ rsp + 0x2f0 ]
mov r11, r8
shrd r11, r10, 58
shr r10, 58
xor r15, r15
adox r13, rbp
adox rdi, [ rsp + 0x368 ]
mov rbp, rdx
mov rdx, [ rax + 0x18 ]
mulx r15, r14, [ rsi + 0x20 ]
adcx r13, r11
adcx r10, rdi
mov rdx, r13
shrd rdx, r10, 58
shr r10, 58
mov r11, 0x3ffffffffffffff 
and r13, r11
mov rdi, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x370 ], r13
mulx r13, r11, [ rsi + 0x30 ]
adox rbp, [ rsp + 0x28 ]
adox r9, [ rsp + 0x20 ]
adcx rbp, r14
adcx r15, r9
xor rdx, rdx
adox rbp, [ rsp + 0x158 ]
adox r15, [ rsp + 0x150 ]
adcx rbp, [ rsp + 0x360 ]
adcx r15, [ rsp + 0x358 ]
add rbp, [ rsp + 0x98 ]
adcx r15, [ rsp + 0x90 ]
test al, al
adox rbp, [ rsp + 0x350 ]
adox r15, [ rsp + 0x348 ]
mov r14, r12
adcx r14, [ rsp + 0x340 ]
adcx rcx, [ rsp + 0x338 ]
test al, al
adox r14, rdi
adox r10, rcx
mov r12, r14
shrd r12, r10, 58
shr r10, 58
mov rdi, 0x3ffffffffffffff 
and r14, rdi
mov rdx, [ rsi + 0x18 ]
mulx rcx, r9, [ rax + 0x28 ]
adox rbp, r12
adox r10, r15
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x30 ], r14
mov r15, r11
adcx r15, [ rsp + 0x330 ]
adcx r13, [ rsp + 0x328 ]
xor r11, r11
adox r15, [ rsp + 0xe8 ]
adox r13, [ rsp + 0xe0 ]
adcx r15, [ rsp - 0x30 ]
adcx r13, [ rsp - 0x38 ]
test al, al
adox r15, r9
adox rcx, r13
adcx r15, [ rsp - 0x20 ]
adcx rcx, [ rsp - 0x28 ]
test al, al
adox r15, [ rsp - 0x40 ]
adox rcx, [ rsp - 0x48 ]
adcx r15, [ rsp + 0x120 ]
adcx rcx, [ rsp + 0x118 ]
mov r12, rbp
shrd r12, r10, 58
shr r10, 58
xor r14, r14
adox r15, r12
adox r10, rcx
mov r11, [ rsp + 0x308 ]
and r11, rdi
mov r9, 0x1ffffffffffffff 
mov r13, r15
and r13, r9
shrd r15, r10, 57
shr r10, 57
xor rcx, rcx
adox r15, [ rsp + 0x288 ]
adox r10, rcx
and rbx, rdi
mov r14, r15
shrd r14, r10, 58
and r15, rdi
lea r14, [ r14 + rbx ]
mov r12, r14
and r12, rdi
mov [ rdx + 0x8 ], r12
and r8, rdi
shr r14, 58
add r14, [ rsp + 0x2e8 ]
and rbp, rdi
mov [ rdx + 0x10 ], r14
mov [ rdx + 0x38 ], rbp
mov [ rdx + 0x20 ], r8
mov [ rdx + 0x40 ], r13
mov [ rdx + 0x18 ], r11
mov r11, [ rsp + 0x370 ]
mov [ rdx + 0x28 ], r11
mov [ rdx + 0x0 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1016
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.2628
; seed 3122722338976570 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 6406287 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=98, initial num_batches=31): 126729 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.019781973551918606
; number reverted permutation / tried permutation: 52539 / 89704 =58.569%
; number reverted decision / tried decision: 49385 / 90295 =54.693%
; validated in 3.631s
