SECTION .text
	GLOBAL fiat_p521_carry_mul
fiat_p521_carry_mul:
sub rsp, 960
mov rax, [ rdx + 0x38 ]
lea r10, [rax + rax]
mov rax, [ rdx + 0x8 ]
lea r11, [rax + rax]
mov rax, [ rdx + 0x28 ]
lea rcx, [rax + rax]
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r9, r8, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rax + 0x10 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x10 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r13
mulx r13, rdi, [ rax + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x40 ], r12
mov [ rsp - 0x38 ], rbp
mulx rbp, r12, [ rax + 0x40 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x30 ], rbx
mov [ rsp - 0x28 ], rbp
mulx rbp, rbx, [ rsi + 0x40 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x20 ], r12
mov [ rsp - 0x18 ], r15
mulx r15, r12, [ rax + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x10 ], r14
mov [ rsp - 0x8 ], rbp
mulx rbp, r14, [ rax + 0x20 ]
imul rdx, [ rax + 0x10 ], 0x2
mov [ rsp + 0x0 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x8 ], r14
mov [ rsp + 0x10 ], rbx
mulx rbx, r14, [ rax + 0x8 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x18 ], rbx
mov [ rsp + 0x20 ], r14
mulx r14, rbx, rbp
mov rdx, r10
mov [ rsp + 0x28 ], r15
mulx r15, r10, [ rsi + 0x10 ]
mov [ rsp + 0x30 ], r12
mov [ rsp + 0x38 ], r13
mulx r13, r12, [ rsi + 0x20 ]
mov [ rsp + 0x40 ], rdi
mov rdi, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x48 ], r9
mov [ rsp + 0x50 ], r8
mulx r8, r9, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x58 ], r8
mov [ rsp + 0x60 ], r9
mulx r9, r8, [ rax + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x68 ], r9
mov [ rsp + 0x70 ], r8
mulx r8, r9, [ rsi + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x78 ], r8
lea r8, [rdx + rdx]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x80 ], r9
mov [ rsp + 0x88 ], r13
mulx r13, r9, rdi
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x90 ], r13
mov [ rsp + 0x98 ], r9
mulx r9, r13, [ rsi + 0x8 ]
mov rdx, r8
mov [ rsp + 0xa0 ], r9
mulx r9, r8, [ rsi + 0x38 ]
mov [ rsp + 0xa8 ], r13
mov [ rsp + 0xb0 ], r12
mulx r12, r13, [ rsi + 0x30 ]
mov [ rsp + 0xb8 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xc0 ], r10
mov [ rsp + 0xc8 ], r14
mulx r14, r10, [ rax + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xd0 ], r14
mov [ rsp + 0xd8 ], r10
mulx r10, r14, [ rax + 0x8 ]
mov rdx, r11
mov [ rsp + 0xe0 ], r10
mulx r10, r11, [ rsi + 0x40 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0xe8 ], r14
mov [ rsp + 0xf0 ], rbx
mulx rbx, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xf8 ], rbx
mov [ rsp + 0x100 ], r14
mulx r14, rbx, rcx
mov rdx, rcx
mov [ rsp + 0x108 ], r9
mulx r9, rcx, [ rsi + 0x40 ]
mov [ rsp + 0x110 ], r8
mov [ rsp + 0x118 ], r14
mulx r14, r8, [ rsi + 0x28 ]
mov [ rsp + 0x120 ], r14
mov r14, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x128 ], r8
mov [ rsp + 0x130 ], rbx
mulx rbx, r8, rbp
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x138 ], r9
mulx r9, rbp, r14
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x140 ], r9
lea r9, [rdx + rdx]
test al, al
adox r11, r8
adox rbx, r10
mov rdx, r9
mulx r10, r9, [ rsi + 0x38 ]
mov r8, 0x1 
mov [ rsp + 0x148 ], rbp
shlx rbp, [ rax + 0x40 ], r8
adcx r11, r13
adcx r12, rbx
xchg rdx, rbp
mulx rbx, r13, [ rsi + 0x8 ]
mov [ rsp + 0x150 ], rbx
mulx rbx, r8, [ rsi + 0x40 ]
mov [ rsp + 0x158 ], rbx
mov [ rsp + 0x160 ], r8
mulx r8, rbx, [ rsi + 0x18 ]
mov [ rsp + 0x168 ], r8
mov r8, [ rax + 0x30 ]
mov [ rsp + 0x170 ], rbx
mov rbx, r8
shl rbx, 0x1
xchg rdx, rbp
mov [ rsp + 0x178 ], r13
mulx r13, r8, [ rsi + 0x40 ]
xchg rdx, rbx
mov [ rsp + 0x180 ], r12
mov [ rsp + 0x188 ], r11
mulx r11, r12, [ rsi + 0x30 ]
mov [ rsp + 0x190 ], r11
mov [ rsp + 0x198 ], r12
mulx r12, r11, [ rsi + 0x38 ]
mov [ rsp + 0x1a0 ], r13
mov [ rsp + 0x1a8 ], r8
mulx r8, r13, [ rsi + 0x40 ]
mov [ rsp + 0x1b0 ], r8
mov r8, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x1b8 ], r13
mov [ rsp + 0x1c0 ], rcx
mulx rcx, r13, r15
add r13, r9
adcx r10, rcx
mov rdx, r11
test al, al
adox rdx, [ rsp + 0x1c0 ]
adox r12, [ rsp + 0x138 ]
xchg rdx, r14
mulx r9, r15, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x30 ]
mulx rcx, r11, rbx
mov rdx, r15
adcx rdx, [ rsp + 0x1a8 ]
adcx r9, [ rsp + 0x1a0 ]
test al, al
adox rdx, [ rsp + 0x198 ]
adox r9, [ rsp + 0x190 ]
adcx r13, [ rsp + 0x130 ]
adcx r10, [ rsp + 0x118 ]
xchg rdx, r8
mov [ rsp + 0x1c8 ], r9
mulx r9, r15, [ rsi + 0x28 ]
test al, al
adox r13, r15
adox r9, r10
xchg rdx, rbx
mulx r15, r10, [ rsi + 0x28 ]
mov rdx, r10
adcx rdx, [ rsp + 0x188 ]
adcx r15, [ rsp + 0x180 ]
xchg rdx, rbx
mov [ rsp + 0x1d0 ], r8
mulx r8, r10, [ rsi + 0x18 ]
mov [ rsp + 0x1d8 ], r9
mov r9, [ rsp + 0x110 ]
mov [ rsp + 0x1e0 ], r13
mov r13, r9
add r13, [ rsp + 0xf0 ]
mov [ rsp + 0x1e8 ], r12
mov r12, [ rsp + 0x108 ]
adcx r12, [ rsp + 0xc8 ]
xor r9, r9
adox rbx, [ rsp + 0x148 ]
adox r15, [ rsp + 0x140 ]
adcx rbx, r10
adcx r8, r15
mov r10, rdx
mov rdx, [ rsi + 0x40 ]
mulx r9, r15, rdi
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x1f0 ], r14
mov [ rsp + 0x1f8 ], r8
mulx r8, r14, [ rsi + 0x30 ]
mov rdx, r10
mov [ rsp + 0x200 ], rbx
mulx rbx, r10, [ rsi + 0x20 ]
xor rdx, rdx
adox r13, r11
adox rcx, r12
adcx r13, [ rsp + 0x128 ]
adcx rcx, [ rsp + 0x120 ]
mov rdx, rbp
mulx r11, rbp, [ rsi + 0x38 ]
test al, al
adox r13, r10
adox rbx, rcx
mov r12, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r10, [ rax + 0x0 ]
adcx r15, rbp
adcx r11, r9
xor rdx, rdx
adox r15, r14
adox r8, r11
mov rdx, [ rsi + 0x30 ]
mulx r14, r9, rdi
mov rdx, [ rsp + 0x200 ]
adcx rdx, [ rsp + 0xc0 ]
mov rbp, [ rsp + 0x1f8 ]
adcx rbp, [ rsp + 0xb8 ]
xor r11, r11
adox r15, [ rsp + 0xe8 ]
adox r8, [ rsp + 0xe0 ]
adcx rdx, [ rsp + 0x178 ]
adcx rbp, [ rsp + 0x150 ]
mov [ rsp + 0x208 ], r8
xor r8, r8
adox rdx, r10
adox rcx, rbp
mov r11, r9
adcx r11, [ rsp + 0x1f0 ]
adcx r14, [ rsp + 0x1e8 ]
mov r10, rdx
mov rdx, [ rax + 0x0 ]
mulx rbp, r9, [ rsi + 0x10 ]
mov rdx, [ rsp + 0xb0 ]
mov [ rsp + 0x210 ], r15
mov r15, rdx
mov [ rsp + 0x218 ], rbx
xor rbx, rbx
adox r15, [ rsp + 0x1e0 ]
mov r8, [ rsp + 0x88 ]
adox r8, [ rsp + 0x1d8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x220 ], r13
mulx r13, rbx, [ rsi + 0x8 ]
adcx r15, [ rsp + 0x170 ]
adcx r8, [ rsp + 0x168 ]
mov rdx, r12
mov [ rsp + 0x228 ], r13
mulx r13, r12, [ rsi + 0x28 ]
add r15, r9
adcx rbp, r8
test al, al
adox r11, r12
adox r13, r14
adcx r11, [ rsp + 0x50 ]
adcx r13, [ rsp + 0x48 ]
test al, al
adox r15, [ rsp + 0x60 ]
adox rbp, [ rsp + 0x58 ]
mov r14, 0x3ffffffffffffff 
mov r9, r10
and r9, r14
mulx r12, r8, [ rsi + 0x10 ]
mov r14, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x230 ], r9
mov [ rsp + 0x238 ], rbp
mulx rbp, r9, rdi
mov rdx, r9
adox rdx, [ rsp + 0x1d0 ]
adox rbp, [ rsp + 0x1c8 ]
adcx r11, [ rsp + 0x70 ]
adcx r13, [ rsp + 0x68 ]
mov r9, [ rsp + 0x220 ]
add r9, [ rsp + 0x98 ]
mov [ rsp + 0x240 ], r13
mov r13, [ rsp + 0x218 ]
adcx r13, [ rsp + 0x90 ]
mov [ rsp + 0x248 ], r11
mov r11, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x250 ], r15
mov [ rsp + 0x258 ], rbx
mulx rbx, r15, [ rsi + 0x8 ]
xor rdx, rdx
adox r9, r8
adox r12, r13
mov rdx, [ rsi + 0x20 ]
mulx r13, r8, r14
adcx r11, r8
adcx r13, rbp
mov rdx, [ rax + 0x20 ]
mulx r8, rbp, [ rsi + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x260 ], r8
mov [ rsp + 0x268 ], rbp
mulx rbp, r8, [ rsi + 0x18 ]
xor rdx, rdx
adox r11, r8
adox rbp, r13
mov rdx, rdi
mulx r13, rdi, [ rsi + 0x38 ]
mov rdx, rdi
adcx rdx, [ rsp + 0x1b8 ]
adcx r13, [ rsp + 0x1b0 ]
mov r8, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x270 ], r13
mulx r13, rdi, [ rax + 0x10 ]
xor rdx, rdx
adox r11, [ rsp + 0x80 ]
adox rbp, [ rsp + 0x78 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x278 ], r8
mov [ rsp + 0x280 ], r13
mulx r13, r8, [ rsi + 0x18 ]
shrd r10, rcx, 58
shr rcx, 58
test al, al
adox r11, [ rsp + 0x258 ]
adox rbp, [ rsp + 0x228 ]
adcx r9, r15
adcx rbx, r12
xor rdx, rdx
adox r9, [ rsp + 0x40 ]
adox rbx, [ rsp + 0x38 ]
adcx r9, r10
adcx rcx, rbx
mov r15, rdi
test al, al
adox r15, [ rsp + 0x210 ]
mov r12, [ rsp + 0x208 ]
adox r12, [ rsp + 0x280 ]
adcx r15, r8
adcx r13, r12
mov rdx, [ rsi + 0x30 ]
mulx r8, rdi, r14
mov rdx, rdi
add rdx, [ rsp + 0x278 ]
adcx r8, [ rsp + 0x270 ]
mov r14, 0x3ffffffffffffff 
mov r10, r9
and r10, r14
mov rbx, [ rsp + 0x250 ]
adox rbx, [ rsp + 0xd8 ]
mov r12, [ rsp + 0x238 ]
adox r12, [ rsp + 0xd0 ]
shrd r9, rcx, 58
shr rcx, 58
xor rdi, rdi
adox rbx, r9
adox rcx, r12
mov r12, rdx
mov rdx, [ rax + 0x18 ]
mulx rdi, r9, [ rsi + 0x0 ]
mov rdx, rbx
shrd rdx, rcx, 58
shr rcx, 58
test al, al
adox r15, [ rsp + 0x268 ]
adox r13, [ rsp + 0x260 ]
mov r14, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x288 ], r10
mov [ rsp + 0x290 ], r13
mulx r13, r10, [ rax + 0x20 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x298 ], r15
mov [ rsp + 0x2a0 ], r13
mulx r13, r15, [ rsi + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x2a8 ], r13
mov [ rsp + 0x2b0 ], r15
mulx r15, r13, [ rsi + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x2b8 ], r10
mov [ rsp + 0x2c0 ], r15
mulx r15, r10, [ rsi + 0x18 ]
adcx r11, r9
adcx rdi, rbp
test al, al
adox r11, r14
adox rcx, rdi
mov rdx, [ rsi + 0x28 ]
mulx r9, rbp, [ rax + 0x18 ]
mov rdx, [ rax + 0x28 ]
mulx rdi, r14, [ rsi + 0x0 ]
adcx r12, [ rsp + 0x30 ]
adcx r8, [ rsp + 0x28 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x2c8 ], rdi
mov [ rsp + 0x2d0 ], r14
mulx r14, rdi, [ rax + 0x0 ]
xor rdx, rdx
adox r12, [ rsp + 0x20 ]
adox r8, [ rsp + 0x18 ]
mov rdx, 0x3ffffffffffffff 
mov [ rsp + 0x2d8 ], r9
mov r9, r11
and r9, rdx
adox r12, r10
adox r15, r8
mov r10, rdi
adcx r10, [ rsp + 0x160 ]
adcx r14, [ rsp + 0x158 ]
xor rdi, rdi
adox r12, r13
adox r15, [ rsp + 0x2c0 ]
mov rdx, [ rax + 0x10 ]
mulx r8, r13, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x2e0 ], r14
mulx r14, rdi, [ rax + 0x18 ]
mov rdx, r13
adcx rdx, [ rsp + 0x248 ]
adcx r8, [ rsp + 0x240 ]
test al, al
adox rdx, rdi
adox r14, r8
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x18 ], r9
adcx r12, [ rsp + 0x2b8 ]
adcx r15, [ rsp + 0x2a0 ]
mov r9, rdx
mov rdx, [ rax + 0x8 ]
mulx r8, rdi, [ rsi + 0x38 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x2e8 ], r15
mulx r15, r13, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x2f0 ], r12
mov [ rsp + 0x2f8 ], r10
mulx r10, r12, [ rax + 0x30 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x300 ], r10
mov [ rsp + 0x308 ], r12
mulx r12, r10, [ rax + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x310 ], r12
mov [ rsp + 0x318 ], r10
mulx r10, r12, [ rax + 0x28 ]
mov rdx, rdi
test al, al
adox rdx, [ rsp + 0x10 ]
adox r8, [ rsp - 0x8 ]
mov rdi, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x320 ], r10
mov [ rsp + 0x328 ], r12
mulx r12, r10, [ rsi + 0x30 ]
adcx rdi, r13
adcx r15, r8
xor rdx, rdx
adox rdi, rbp
adox r15, [ rsp + 0x2d8 ]
mov rdx, [ rsi + 0x20 ]
mulx r13, rbp, [ rax + 0x18 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x330 ], r13
mulx r13, r8, [ rsi + 0x18 ]
shrd r11, rcx, 58
shr rcx, 58
test al, al
adox r9, [ rsp - 0x10 ]
adox r14, [ rsp - 0x18 ]
adcx rdi, [ rsp + 0x8 ]
adcx r15, [ rsp + 0x0 ]
test al, al
adox r9, r11
adox rcx, r14
adcx rdi, r8
adcx r13, r15
mov rdx, 0x3ffffffffffffff 
mov r8, r9
and r8, rdx
mov r11, [ rsp + 0x328 ]
mov r14, r11
adox r14, [ rsp + 0x298 ]
mov r15, [ rsp + 0x320 ]
adox r15, [ rsp + 0x290 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x338 ], rbp
mulx rbp, r11, [ rsi + 0x8 ]
shrd r9, rcx, 58
shr rcx, 58
add r14, [ rsp + 0x2b0 ]
adcx r15, [ rsp + 0x2a8 ]
test al, al
adox rdi, [ rsp + 0x308 ]
adox r13, [ rsp + 0x300 ]
adcx rdi, r11
adcx rbp, r13
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x20 ], r8
mov r8, r10
test al, al
adox r8, [ rsp + 0x2f8 ]
adox r12, [ rsp + 0x2e0 ]
mov r10, [ rsp + 0x2d0 ]
mov r11, r10
adcx r11, [ rsp + 0x2f0 ]
mov r13, [ rsp + 0x2c8 ]
adcx r13, [ rsp + 0x2e8 ]
xor r10, r10
adox r11, r9
adox rcx, r13
adcx rdi, [ rsp - 0x20 ]
adcx rbp, [ rsp - 0x28 ]
test al, al
adox r8, [ rsp - 0x30 ]
adox r12, [ rsp - 0x38 ]
adcx r8, [ rsp + 0x338 ]
adcx r12, [ rsp + 0x330 ]
xor r9, r9
adox r8, [ rsp + 0x318 ]
adox r12, [ rsp + 0x310 ]
mov r10, r11
shrd r10, rcx, 58
shr rcx, 58
add r14, r10
adcx rcx, r15
test al, al
adox r8, [ rsp - 0x40 ]
adox r12, [ rsp - 0x48 ]
adcx r8, [ rsp + 0xa8 ]
adcx r12, [ rsp + 0xa0 ]
xor r15, r15
adox r8, [ rsp + 0x100 ]
adox r12, [ rsp + 0xf8 ]
mov r9, r14
shrd r9, rcx, 58
shr rcx, 58
mov r13, 0x3a 
bzhi r10, r14, r13
mov [ rdx + 0x30 ], r10
adox r8, r9
adox rcx, r12
mov r14, r8
shrd r14, rcx, 58
shr rcx, 58
test al, al
adox rdi, r14
adox rcx, rbp
bzhi rbp, r8, r13
mov r12, 0x39 
bzhi r9, rdi, r12
shrd rdi, rcx, 57
shr rcx, 57
test al, al
adox rdi, [ rsp + 0x230 ]
adox rcx, r15
mov r10, rdi
shrd r10, rcx, 58
add r10, [ rsp + 0x288 ]
bzhi r8, rbx, r13
mov rbx, r10
shr rbx, 58
bzhi r14, rdi, r13
bzhi rdi, r10, r13
mov [ rdx + 0x8 ], rdi
bzhi rcx, r11, r13
lea rbx, [ rbx + r8 ]
mov [ rdx + 0x28 ], rcx
mov [ rdx + 0x10 ], rbx
mov [ rdx + 0x40 ], r9
mov [ rdx + 0x0 ], r14
mov [ rdx + 0x38 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 960
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.0887
; seed 2940043275796150 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 13517408 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=41, initial num_batches=31): 229920 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.017009178090947614
; number reverted permutation / tried permutation: 47830 / 89969 =53.163%
; number reverted decision / tried decision: 32235 / 90030 =35.805%
; validated in 6.621s
