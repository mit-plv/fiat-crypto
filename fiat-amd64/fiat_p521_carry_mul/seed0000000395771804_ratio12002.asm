SECTION .text
	GLOBAL fiat_p521_carry_mul
fiat_p521_carry_mul:
sub rsp, 1088
mov rax, rdx
mov rdx, [ rdx + 0x18 ]
mulx r11, r10, [ rsi + 0x8 ]
mov rdx, [ rax + 0x10 ]
mulx r8, rcx, [ rsi + 0x8 ]
imul rdx, [ rax + 0x28 ], 0x2
mov r9, rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
imul rdx, [ rax + 0x40 ], 0x2
mov [ rsp - 0x70 ], r12
mov r12, 0x1 
mov [ rsp - 0x68 ], r13
shlx r13, [ rax + 0x30 ], r12
mov r12, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, r13
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbp
mulx rbp, rdi, r9
mov rdx, r9
mov [ rsp - 0x40 ], rbx
mulx rbx, r9, [ rsi + 0x28 ]
mov [ rsp - 0x38 ], r11
mov r11, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x30 ], r10
mov [ rsp - 0x28 ], r8
mulx r8, r10, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x20 ], rcx
mov [ rsp - 0x18 ], r8
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x10 ], r8
mov [ rsp - 0x8 ], rcx
mulx rcx, r8, [ rax + 0x20 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x0 ], rcx
mov [ rsp + 0x8 ], r8
mulx r8, rcx, r13
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x10 ], r10
mov [ rsp + 0x18 ], rbp
mulx rbp, r10, [ rsi + 0x8 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x20 ], rbp
mov [ rsp + 0x28 ], r10
mulx r10, rbp, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x30 ], r10
mov [ rsp + 0x38 ], rbp
mulx rbp, r10, [ rax + 0x0 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x40 ], rdi
mov [ rsp + 0x48 ], r8
mulx r8, rdi, r12
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x50 ], r8
mov [ rsp + 0x58 ], rdi
mulx rdi, r8, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x60 ], rdi
mov [ rsp + 0x68 ], r8
mulx r8, rdi, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x70 ], r8
mov [ rsp + 0x78 ], rdi
mulx rdi, r8, [ rax + 0x0 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x80 ], rdi
mov [ rsp + 0x88 ], r8
mulx r8, rdi, [ rsi + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x90 ], r8
mov [ rsp + 0x98 ], rdi
mulx rdi, r8, [ rsi + 0x10 ]
mov rdx, r13
mov [ rsp + 0xa0 ], rdi
mulx rdi, r13, [ rsi + 0x20 ]
mov [ rsp + 0xa8 ], r8
mov r8, 0x1 
mov [ rsp + 0xb0 ], rcx
shlx rcx, [ rax + 0x8 ], r8
mov r8, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xb8 ], rdi
mov [ rsp + 0xc0 ], r13
mulx r13, rdi, r11
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0xc8 ], rbx
mov [ rsp + 0xd0 ], r9
mulx r9, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xd8 ], r9
mov [ rsp + 0xe0 ], rbx
mulx rbx, r9, [ rax + 0x20 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0xe8 ], rbx
mov [ rsp + 0xf0 ], r9
mulx r9, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0xf8 ], r9
mov [ rsp + 0x100 ], rbx
mulx rbx, r9, rcx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x108 ], r13
mulx r13, rcx, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x110 ], rdi
mov [ rsp + 0x118 ], rbx
mulx rbx, rdi, [ rax + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x120 ], rbx
mov [ rsp + 0x128 ], rdi
mulx rdi, rbx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x130 ], rdi
mov rdi, rdx
shl rdi, 0x1
imul rdx, [ rax + 0x20 ], 0x2
mov [ rsp + 0x138 ], rbx
xor rbx, rbx
adox r10, rcx
adox r13, rbp
mov rbp, rdx
mov rdx, [ rax + 0x0 ]
mulx rbx, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x140 ], r13
mov [ rsp + 0x148 ], r10
mulx r10, r13, rbp
mov rdx, rbp
mov [ rsp + 0x150 ], rbx
mulx rbx, rbp, [ rsi + 0x40 ]
xchg rdx, rdi
mov [ rsp + 0x158 ], rbx
mov [ rsp + 0x160 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
mov [ rsp + 0x168 ], rcx
mov rcx, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x170 ], r10
mov [ rsp + 0x178 ], r13
mulx r13, r10, [ rsi + 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x180 ], r13
mov [ rsp + 0x188 ], r10
mulx r10, r13, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x190 ], r10
mov [ rsp + 0x198 ], r13
mulx r13, r10, rcx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x1a0 ], r13
mov [ rsp + 0x1a8 ], r10
mulx r10, r13, r12
mov rdx, r12
mov [ rsp + 0x1b0 ], r10
mulx r10, r12, [ rsi + 0x18 ]
xchg rdx, rcx
mov [ rsp + 0x1b8 ], r10
mov [ rsp + 0x1c0 ], r12
mulx r12, r10, [ rsi + 0x40 ]
mov [ rsp + 0x1c8 ], r12
mov r12, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x1d0 ], r10
mov [ rsp + 0x1d8 ], r13
mulx r13, r10, r11
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x1e0 ], rbp
mov [ rsp + 0x1e8 ], rbx
mulx rbx, rbp, r12
mov rdx, r8
mov [ rsp + 0x1f0 ], r9
mulx r9, r8, [ rsi + 0x18 ]
mov [ rsp + 0x1f8 ], r9
mov r9, 0x1 
mov [ rsp + 0x200 ], r8
shlx r8, [ rax + 0x18 ], r9
mov r9, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x208 ], rbx
mov [ rsp + 0x210 ], rbp
mulx rbp, rbx, r8
adcx r10, r14
adcx r15, r13
mov rdx, 0x1 
shlx r14, [ rax + 0x10 ], rdx
xor r13, r13
adox r10, [ rsp + 0x210 ]
adox r15, [ rsp + 0x208 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x218 ], r15
mulx r15, r13, r14
mov rdx, r8
mov [ rsp + 0x220 ], r10
mulx r10, r8, [ rsi + 0x30 ]
xchg rdx, r9
mov [ rsp + 0x228 ], rbp
mov [ rsp + 0x230 ], rbx
mulx rbx, rbp, [ rsi + 0x30 ]
mov [ rsp + 0x238 ], rbx
mov rbx, r13
adcx rbx, [ rsp + 0x1f0 ]
adcx r15, [ rsp + 0x118 ]
mov r13, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x240 ], rbp
mov [ rsp + 0x248 ], r15
mulx r15, rbp, rcx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x250 ], r15
mov [ rsp + 0x258 ], rbp
mulx rbp, r15, rdi
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x260 ], rbp
mov [ rsp + 0x268 ], r15
mulx r15, rbp, r9
mov rdx, rdi
mulx r9, rdi, [ rsi + 0x38 ]
add rbx, r8
adcx r10, [ rsp + 0x248 ]
add rbx, [ rsp + 0x268 ]
adcx r10, [ rsp + 0x260 ]
test al, al
adox rbx, [ rsp + 0x110 ]
adox r10, [ rsp + 0x108 ]
adcx rbp, rdi
adcx r9, r15
test al, al
adox rbx, [ rsp + 0x200 ]
adox r10, [ rsp + 0x1f8 ]
adcx rbx, [ rsp + 0x1e8 ]
adcx r10, [ rsp + 0x1e0 ]
mov rdx, [ rax + 0x0 ]
mulx r15, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x270 ], r9
mulx r9, rdi, r14
test al, al
adox rbx, [ rsp + 0x1d8 ]
adox r10, [ rsp + 0x1b0 ]
adcx rdi, [ rsp + 0x230 ]
adcx r9, [ rsp + 0x228 ]
add rdi, [ rsp + 0x178 ]
adcx r9, [ rsp + 0x170 ]
test al, al
adox rdi, [ rsp + 0xd0 ]
adox r9, [ rsp + 0xc8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x278 ], rbp
mulx rbp, r14, r13
adcx rbx, r8
adcx r15, r10
mov rdx, rcx
mulx r13, rcx, [ rsi + 0x30 ]
mulx r10, r8, [ rsi + 0x10 ]
mov [ rsp + 0x280 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x288 ], rcx
mov [ rsp + 0x290 ], r15
mulx r15, rcx, r12
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x298 ], rbx
mov [ rsp + 0x2a0 ], rbp
mulx rbp, rbx, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x2a8 ], rbp
mov [ rsp + 0x2b0 ], rbx
mulx rbx, rbp, r12
test al, al
adox rdi, [ rsp + 0xc0 ]
adox r9, [ rsp + 0xb8 ]
adcx rdi, rcx
adcx r15, r9
xor rdx, rdx
adox rdi, r8
adox r10, r15
adcx rdi, [ rsp + 0x168 ]
adcx r10, [ rsp + 0x150 ]
mov r8, rbp
test al, al
adox r8, [ rsp + 0xb0 ]
adox rbx, [ rsp + 0x48 ]
mov rdx, [ rsi + 0x38 ]
mulx rbp, rcx, r11
mov rdx, [ rsi + 0x20 ]
mulx r9, r11, [ rax + 0x0 ]
mov rdx, [ rsp + 0x40 ]
mov r15, rdx
adcx r15, [ rsp + 0x278 ]
mov [ rsp + 0x2b8 ], rbx
mov rbx, [ rsp + 0x18 ]
adcx rbx, [ rsp + 0x270 ]
add r15, r14
adcx rbx, [ rsp + 0x2a0 ]
mov rdx, 0x3ffffffffffffff 
mov r14, [ rsp + 0x298 ]
and r14, rdx
mov rdx, [ rsp + 0x258 ]
mov [ rsp + 0x2c0 ], r14
mov r14, rdx
adox r14, [ rsp + 0x220 ]
mov [ rsp + 0x2c8 ], r8
mov r8, [ rsp + 0x250 ]
adox r8, [ rsp + 0x218 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x2d0 ], rbx
mov [ rsp + 0x2d8 ], r15
mulx r15, rbx, [ rax + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x2e0 ], r8
mov [ rsp + 0x2e8 ], r14
mulx r14, r8, r12
mov rdx, [ rsp + 0x2b0 ]
mov r12, rdx
adcx r12, [ rsp + 0x148 ]
mov [ rsp + 0x2f0 ], r9
mov r9, [ rsp + 0x2a8 ]
adcx r9, [ rsp + 0x140 ]
mov rdx, rcx
test al, al
adox rdx, [ rsp + 0x160 ]
adox rbp, [ rsp + 0x158 ]
mov rcx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x2f8 ], r11
mov [ rsp + 0x300 ], r9
mulx r9, r11, r13
adcx rcx, [ rsp + 0x240 ]
adcx rbp, [ rsp + 0x238 ]
test al, al
adox rcx, r8
adox r14, rbp
adcx rdi, rbx
adcx r15, r10
mov rdx, [ rsi + 0x20 ]
mulx rbx, r10, [ rax + 0x10 ]
test al, al
adox rcx, r11
adox r9, r14
mov rdx, [ rsp + 0x290 ]
mov r8, [ rsp + 0x298 ]
shrd r8, rdx, 58
shr rdx, 58
add rcx, [ rsp + 0x10 ]
adcx r9, [ rsp - 0x18 ]
mov r11, rdx
mov rdx, [ rsi + 0x18 ]
mulx r14, rbp, [ rax + 0x8 ]
add rdi, r8
adcx r11, r15
mov rdx, [ rax + 0x18 ]
mulx r8, r15, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x308 ], rbx
mov [ rsp + 0x310 ], r10
mulx r10, rbx, [ rax + 0x10 ]
mov rdx, rdi
shrd rdx, r11, 58
shr r11, 58
mov [ rsp + 0x318 ], r11
mov r11, [ rsp + 0x1d0 ]
test al, al
adox r11, [ rsp + 0x58 ]
mov [ rsp + 0x320 ], rdx
mov rdx, [ rsp + 0x1c8 ]
adox rdx, [ rsp + 0x50 ]
adcx r12, r15
adcx r8, [ rsp + 0x300 ]
test al, al
adox rcx, [ rsp - 0x8 ]
adox r9, [ rsp - 0x10 ]
adcx r11, [ rsp + 0x88 ]
adcx rdx, [ rsp + 0x80 ]
mov r15, [ rsp + 0x2e8 ]
mov [ rsp + 0x328 ], rdx
xor rdx, rdx
adox r15, [ rsp + 0x2f8 ]
mov [ rsp + 0x330 ], r11
mov r11, [ rsp + 0x2e0 ]
adox r11, [ rsp + 0x2f0 ]
adcx rcx, [ rsp - 0x20 ]
adcx r9, [ rsp - 0x28 ]
test al, al
adox r15, rbp
adox r14, r11
adcx r15, rbx
adcx r10, r14
mov rdx, [ rsi + 0x0 ]
mulx rbx, rbp, [ rax + 0x20 ]
xor rdx, rdx
adox r12, [ rsp + 0x8 ]
adox r8, [ rsp + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mulx r14, r11, [ rax + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x338 ], rbx
mov [ rsp + 0x340 ], rbp
mulx rbp, rbx, [ rax + 0x0 ]
mov rdx, r11
adcx rdx, [ rsp + 0x330 ]
adcx r14, [ rsp + 0x328 ]
mov r11, [ rsp + 0x1a8 ]
mov [ rsp + 0x348 ], r10
mov r10, r11
add r10, [ rsp + 0x2d8 ]
mov [ rsp + 0x350 ], r15
mov r15, [ rsp + 0x1a0 ]
adcx r15, [ rsp + 0x2d0 ]
mov r11, 0x3ffffffffffffff 
and rdi, r11
adox r12, [ rsp + 0x38 ]
adox r8, [ rsp + 0x30 ]
mov r11, [ rsp + 0x2c8 ]
adcx r11, [ rsp + 0x288 ]
mov [ rsp + 0x358 ], rdi
mov rdi, [ rsp + 0x2b8 ]
adcx rdi, [ rsp + 0x280 ]
mov [ rsp + 0x360 ], r8
xor r8, r8
adox r10, [ rsp + 0x1c0 ]
adox r15, [ rsp + 0x1b8 ]
mov r8, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x368 ], r12
mov [ rsp + 0x370 ], rdi
mulx rdi, r12, [ rax + 0x8 ]
adcx r8, [ rsp + 0x310 ]
adcx r14, [ rsp + 0x308 ]
test al, al
adox r10, rbx
adox rbp, r15
adcx r10, r12
adcx rdi, rbp
mov rdx, [ rax + 0x30 ]
mulx r15, rbx, [ rsi + 0x8 ]
xor rdx, rdx
adox r10, [ rsp + 0xe0 ]
adox rdi, [ rsp + 0xd8 ]
adcx rcx, [ rsp + 0x138 ]
adcx r9, [ rsp + 0x130 ]
xor r12, r12
adox r10, [ rsp + 0x320 ]
adox rdi, [ rsp + 0x318 ]
mov rdx, [ rax + 0x0 ]
mulx r12, rbp, [ rsi + 0x28 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x378 ], r15
mov [ rsp + 0x380 ], rbx
mulx rbx, r15, [ rsi + 0x38 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x388 ], rbx
mov [ rsp + 0x390 ], r15
mulx r15, rbx, [ rsi + 0x10 ]
mov rdx, r10
shrd rdx, rdi, 58
shr rdi, 58
test al, al
adox r11, rbp
adox r12, [ rsp + 0x370 ]
mov rbp, 0x3ffffffffffffff 
and r10, rbp
adox r11, [ rsp + 0x128 ]
adox r12, [ rsp + 0x120 ]
mov rbp, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x398 ], r10
mov [ rsp + 0x3a0 ], r15
mulx r15, r10, [ rax + 0x28 ]
adcx rcx, rbp
adcx rdi, r9
mov rdx, 0x3ffffffffffffff 
mov r9, rcx
and r9, rdx
adox r11, [ rsp + 0x188 ]
adox r12, [ rsp + 0x180 ]
adcx r8, [ rsp + 0x68 ]
adcx r14, [ rsp + 0x60 ]
mov rbp, [ rsp + 0x350 ]
add rbp, [ rsp - 0x30 ]
mov rdx, [ rsp + 0x348 ]
adcx rdx, [ rsp - 0x38 ]
test al, al
adox r11, [ rsp + 0xa8 ]
adox r12, [ rsp + 0xa0 ]
adcx r11, [ rsp + 0xf0 ]
adcx r12, [ rsp + 0xe8 ]
add r8, rbx
adcx r14, [ rsp + 0x3a0 ]
xor rbx, rbx
adox r11, r10
adox r15, r12
xchg rdx, r13
mulx r12, r10, [ rsi + 0x40 ]
adcx r10, [ rsp + 0x390 ]
adcx r12, [ rsp + 0x388 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x3a8 ], r14
mulx r14, rbx, [ rax + 0x20 ]
add rbp, [ rsp + 0x340 ]
adcx r13, [ rsp + 0x338 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x3b0 ], r14
mov [ rsp + 0x3b8 ], rbx
mulx rbx, r14, [ rax + 0x8 ]
shrd rcx, rdi, 58
shr rdi, 58
xor rdx, rdx
adox r10, r14
adox rbx, r12
adcx rbp, rcx
adcx rdi, r13
mov r12, rbp
shrd r12, rdi, 58
shr rdi, 58
xor r13, r13
adox r11, r12
adox rdi, r15
mov rdx, 0x3ffffffffffffff 
and rbp, rdx
mov rdx, [ rax + 0x40 ]
mulx r14, r15, [ rsi + 0x0 ]
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x20 ], rbp
mov [ rdx + 0x18 ], r9
adox r10, [ rsp + 0x78 ]
adox rbx, [ rsp + 0x70 ]
adcx r8, [ rsp + 0x28 ]
mov r9, [ rsp + 0x3a8 ]
adcx r9, [ rsp + 0x20 ]
add r8, [ rsp - 0x40 ]
adcx r9, [ rsp - 0x48 ]
mov rcx, r11
shrd rcx, rdi, 58
shr rdi, 58
test al, al
adox r8, rcx
adox rdi, r9
mov r12, 0x3ffffffffffffff 
mov rbp, r8
and rbp, r12
mov [ rdx + 0x30 ], rbp
mov r9, rdx
mov rdx, [ rax + 0x28 ]
mulx rbp, rcx, [ rsi + 0x10 ]
and r11, r12
adox r10, [ rsp + 0x198 ]
adox rbx, [ rsp + 0x190 ]
adcx r10, [ rsp + 0x3b8 ]
adcx rbx, [ rsp + 0x3b0 ]
xor rdx, rdx
adox r10, rcx
adox rbp, rbx
mov rdx, [ rax + 0x30 ]
mulx rcx, r13, [ rsi + 0x10 ]
mov rdx, r13
adcx rdx, [ rsp + 0x368 ]
adcx rcx, [ rsp + 0x360 ]
xor rbx, rbx
adox r10, [ rsp + 0x380 ]
adox rbp, [ rsp + 0x378 ]
adcx rdx, [ rsp + 0x98 ]
adcx rcx, [ rsp + 0x90 ]
test al, al
adox r10, [ rsp + 0x100 ]
adox rbp, [ rsp + 0xf8 ]
shrd r8, rdi, 58
shr rdi, 58
xor r13, r13
adox r10, r8
adox rdi, rbp
adcx rdx, r15
adcx r14, rcx
mov rbx, r10
shrd rbx, rdi, 58
shr rdi, 58
add rdx, rbx
adcx rdi, r14
mov r15, rdx
shrd r15, rdi, 57
shr rdi, 57
test al, al
adox r15, [ rsp + 0x2c0 ]
adox rdi, r13
mov rcx, r15
and rcx, r12
shrd r15, rdi, 58
add r15, [ rsp + 0x358 ]
mov [ r9 + 0x0 ], rcx
mov rbp, r15
and rbp, r12
shr r15, 58
mov [ r9 + 0x28 ], r11
add r15, [ rsp + 0x398 ]
mov r11, 0x1ffffffffffffff 
and rdx, r11
mov [ r9 + 0x8 ], rbp
and r10, r12
mov [ r9 + 0x40 ], rdx
mov [ r9 + 0x10 ], r15
mov [ r9 + 0x38 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1088
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.2002
; seed 1329053551542359 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 6421444 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=97, initial num_batches=31): 128107 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.019949874202749414
; number reverted permutation / tried permutation: 52550 / 89819 =58.507%
; number reverted decision / tried decision: 48940 / 90180 =54.269%
; validated in 3.586s
