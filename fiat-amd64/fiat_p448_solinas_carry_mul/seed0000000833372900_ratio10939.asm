SECTION .text
	GLOBAL fiat_p448_solinas_carry_mul
fiat_p448_solinas_carry_mul:
sub rsp, 912
mov rax, rdx
mov rdx, [ rdx + 0x20 ]
mulx r11, r10, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mulx r8, rcx, [ rax + 0x20 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x30 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x38 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x28 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x38 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x48 ], r8
mov [ rsp - 0x40 ], rcx
mulx rcx, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x38 ], rcx
mov [ rsp - 0x30 ], r8
mulx r8, rcx, [ rax + 0x28 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x28 ], r11
mov [ rsp - 0x20 ], r10
mulx r10, r11, [ rsi + 0x28 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x18 ], rdi
mov [ rsp - 0x10 ], r15
mulx r15, rdi, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x8 ], rbx
mov [ rsp + 0x0 ], r9
mulx r9, rbx, [ rax + 0x28 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x8 ], r9
mov [ rsp + 0x10 ], rbx
mulx rbx, r9, [ rsi + 0x38 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x18 ], rbx
mov [ rsp + 0x20 ], r9
mulx r9, rbx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x28 ], r9
mov [ rsp + 0x30 ], rbx
mulx rbx, r9, [ rsi + 0x38 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x38 ], r15
mov [ rsp + 0x40 ], rdi
mulx rdi, r15, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x48 ], r14
mov [ rsp + 0x50 ], r13
mulx r13, r14, [ rax + 0x38 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x58 ], r13
mov [ rsp + 0x60 ], r14
mulx r14, r13, [ rax + 0x28 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x68 ], rbx
mov [ rsp + 0x70 ], r9
mulx r9, rbx, [ rsi + 0x18 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x78 ], r9
mov [ rsp + 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x88 ], rbx
mov [ rsp + 0x90 ], r9
mulx r9, rbx, [ rax + 0x10 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x98 ], r9
mov [ rsp + 0xa0 ], rbx
mulx rbx, r9, [ rax + 0x20 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xa8 ], r10
mov [ rsp + 0xb0 ], r11
mulx r11, r10, [ rsi + 0x0 ]
add r9, rcx
adcx r8, rbx
mov rdx, [ rsi + 0x30 ]
mulx rbx, rcx, [ rax + 0x20 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xb8 ], r11
mov [ rsp + 0xc0 ], r10
mulx r10, r11, [ rax + 0x10 ]
mov rdx, rbp
mov [ rsp + 0xc8 ], rbx
xor rbx, rbx
adox rdx, r15
mov [ rsp + 0xd0 ], rcx
mov rcx, rdi
adox rcx, r12
mov [ rsp + 0xd8 ], r8
mov r8, rdx
adcx r8, rbp
adcx r12, rcx
add r8, r15
adcx rdi, r12
mov rbp, rdx
mov rdx, [ rax + 0x30 ]
mulx r12, r15, [ rsi + 0x30 ]
mov rdx, r13
add rdx, r15
mov [ rsp + 0xe0 ], r9
mov r9, r12
adcx r9, r14
test al, al
adox rdx, [ rsp + 0xb0 ]
adox r9, [ rsp + 0xa8 ]
mov [ rsp + 0xe8 ], rdi
mov rdi, rdx
adcx rdi, r13
adcx r14, r9
xor r13, r13
adox r8, r11
mov rbx, r10
adox rbx, [ rsp + 0xe8 ]
adcx rdx, [ rsp + 0x70 ]
adcx r9, [ rsp + 0x68 ]
mov [ rsp + 0xf0 ], rbx
mov rbx, [ rsp + 0x50 ]
mov [ rsp + 0xf8 ], r8
mov r8, rbx
mov [ rsp + 0x100 ], r14
xor r14, r14
adox r8, [ rsp + 0xe0 ]
mov r13, [ rsp + 0x48 ]
adox r13, [ rsp + 0xd8 ]
adcx r8, [ rsp + 0x40 ]
adcx r13, [ rsp + 0x38 ]
test al, al
adox rdx, [ rsp + 0x0 ]
adox r9, [ rsp - 0x8 ]
mov rbx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x108 ], r9
mulx r9, r14, [ rax + 0x0 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x110 ], rbx
mov [ rsp + 0x118 ], rdi
mulx rdi, rbx, [ rax + 0x8 ]
mov rdx, r8
adcx rdx, r14
adcx r9, r13
test al, al
adox r8, [ rsp - 0x10 ]
adox r13, [ rsp - 0x18 ]
adcx r8, rbx
adcx rdi, r13
mov r14, rdx
mov rdx, [ rax + 0x10 ]
mulx r13, rbx, [ rsi + 0x28 ]
test al, al
adox r8, rbx
adox r13, rdi
mov rdx, [ rsi + 0x20 ]
mulx rbx, rdi, [ rax + 0x18 ]
mov rdx, r15
adcx rdx, [ rsp + 0x118 ]
adcx r12, [ rsp + 0x100 ]
test al, al
adox r8, rdi
adox rbx, r13
adcx rdx, [ rsp + 0xb0 ]
adcx r12, [ rsp + 0xa8 ]
mov r15, rdx
mov rdx, [ rax + 0x8 ]
mulx rdi, r13, [ rsi + 0x10 ]
add r15, [ rsp + 0x70 ]
adcx r12, [ rsp + 0x68 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x120 ], rbx
mov [ rsp + 0x128 ], r8
mulx r8, rbx, [ rax + 0x18 ]
mov rdx, rbx
test al, al
adox rdx, [ rsp + 0x110 ]
mov [ rsp + 0x130 ], r9
mov r9, r8
adox r9, [ rsp + 0x108 ]
adcx r15, [ rsp + 0x0 ]
adcx r12, [ rsp - 0x8 ]
mov [ rsp + 0x138 ], r9
xor r9, r9
adox r15, rbx
adox r8, r12
adcx r14, r13
adcx rdi, [ rsp + 0x130 ]
mov r13, [ rsp + 0x128 ]
xor rbx, rbx
adox r13, [ rsp - 0x20 ]
mov r9, [ rsp + 0x120 ]
adox r9, [ rsp - 0x28 ]
adcx rbp, r11
adcx r10, rcx
mov r11, rdx
mov rdx, [ rax + 0x18 ]
mulx r12, rcx, [ rsi + 0x30 ]
xor rdx, rdx
adox r15, [ rsp - 0x40 ]
adox r8, [ rsp - 0x48 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x140 ], rdi
mulx rdi, rbx, [ rsi + 0x18 ]
adcx r15, rbx
mov rdx, rdi
adcx rdx, r8
mov r8, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x148 ], r14
mov [ rsp + 0x150 ], r9
mulx r9, r14, [ rax + 0x38 ]
mov rdx, rcx
mov [ rsp + 0x158 ], r13
xor r13, r13
adox rdx, [ rsp + 0xf8 ]
mov [ rsp + 0x160 ], r10
mov r10, r12
adox r10, [ rsp + 0xf0 ]
mov r13, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x168 ], rbp
mov [ rsp + 0x170 ], r11
mulx r11, rbp, [ rax + 0x20 ]
mov rdx, r14
adcx rdx, r14
mov [ rsp + 0x178 ], r8
mov r8, r9
adcx r8, r9
mov [ rsp + 0x180 ], r8
mov r8, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x188 ], r15
mov [ rsp + 0x190 ], r10
mulx r10, r15, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x198 ], r8
mov [ rsp + 0x1a0 ], r10
mulx r10, r8, [ rax + 0x38 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x1a8 ], r10
mov [ rsp + 0x1b0 ], r8
mulx r8, r10, [ rax + 0x30 ]
test al, al
adox r13, rbp
mov rdx, r11
adox rdx, [ rsp + 0x190 ]
mov [ rsp + 0x1b8 ], r15
mov r15, r10
adcx r15, [ rsp + 0x188 ]
mov [ rsp + 0x1c0 ], rdx
mov rdx, r8
adcx rdx, [ rsp + 0x178 ]
test al, al
adox r13, [ rsp + 0x10 ]
mov [ rsp + 0x1c8 ], rdx
mov rdx, [ rsp + 0x1c0 ]
adox rdx, [ rsp + 0x8 ]
adcx r15, [ rsp + 0x60 ]
mov [ rsp + 0x1d0 ], rdx
mov rdx, [ rsp + 0x58 ]
mov [ rsp + 0x1d8 ], r13
mov r13, rdx
adcx r13, [ rsp + 0x1c8 ]
mov [ rsp + 0x1e0 ], r13
mov r13, [ rsp + 0x170 ]
mov [ rsp + 0x1e8 ], r15
xor r15, r15
adox r13, [ rsp - 0x40 ]
mov rdx, [ rsp + 0x138 ]
adox rdx, [ rsp - 0x48 ]
mov r15, rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x1f0 ], r13
mov [ rsp + 0x1f8 ], r8
mulx r8, r13, [ rsi + 0x20 ]
adcx r14, [ rsp + 0x20 ]
adcx r9, [ rsp + 0x18 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x200 ], r8
mov [ rsp + 0x208 ], r13
mulx r13, r8, [ rsi + 0x18 ]
mov rdx, rbx
mov [ rsp + 0x210 ], r9
xor r9, r9
adox rdx, [ rsp + 0x1f0 ]
adox rdi, r15
mov rbx, r8
adcx rbx, [ rsp + 0x1d8 ]
mov r15, r13
adcx r15, [ rsp + 0x1d0 ]
test al, al
adox r14, [ rsp + 0xd0 ]
mov [ rsp + 0x218 ], r15
mov r15, [ rsp + 0x210 ]
adox r15, [ rsp + 0xc8 ]
adcx r14, [ rsp + 0x1b8 ]
adcx r15, [ rsp + 0x1a0 ]
add r14, [ rsp + 0x208 ]
adcx r15, [ rsp + 0x200 ]
add r14, [ rsp + 0x1b0 ]
adcx r15, [ rsp + 0x1a8 ]
mov [ rsp + 0x220 ], rbx
mov rbx, rcx
add rbx, [ rsp + 0x168 ]
adcx r12, [ rsp + 0x160 ]
mov rcx, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x228 ], r15
mulx r15, r9, [ rsi + 0x10 ]
mov rdx, r9
add rdx, [ rsp + 0x158 ]
adcx r15, [ rsp + 0x150 ]
mov r9, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x230 ], r14
mov [ rsp + 0x238 ], rdi
mulx rdi, r14, [ rax + 0x38 ]
test al, al
adox r9, [ rsp + 0x90 ]
adox r15, [ rsp + 0x88 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x240 ], r15
mov [ rsp + 0x248 ], r9
mulx r9, r15, [ rax + 0x0 ]
adcx rbx, rbp
adcx r11, r12
test al, al
adox rbx, [ rsp + 0x10 ]
adox r11, [ rsp + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx r12, rbp, [ rax + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x250 ], r12
mov [ rsp + 0x258 ], rbp
mulx rbp, r12, [ rsi + 0x8 ]
adcx rbx, r8
adcx r13, r11
mov rdx, [ rsi + 0x10 ]
mulx r11, r8, [ rax + 0x0 ]
add rbx, r14
mov rdx, rdi
adcx rdx, r13
xor r13, r13
adox rcx, r10
mov [ rsp + 0x260 ], r9
mov r9, [ rsp + 0x238 ]
adox r9, [ rsp + 0x1f8 ]
adcx rbx, r12
adcx rbp, rdx
mov r10, r8
test al, al
adox r10, [ rsp + 0x230 ]
adox r11, [ rsp + 0x228 ]
mov r12, r15
adcx r12, [ rsp + 0x1e8 ]
mov r8, [ rsp + 0x260 ]
adcx r8, [ rsp + 0x1e0 ]
xor r15, r15
adox r12, [ rsp + 0x80 ]
adox r8, [ rsp + 0x78 ]
mov rdx, [ rsi + 0x28 ]
mulx r15, r13, [ rax + 0x0 ]
mov rdx, r14
adcx rdx, [ rsp + 0x220 ]
adcx rdi, [ rsp + 0x218 ]
add rdx, r13
adcx r15, rdi
mov r14, rdx
mov rdx, [ rax + 0x38 ]
mulx rdi, r13, [ rsi + 0x0 ]
mov rdx, r13
test al, al
adox rdx, [ rsp + 0x248 ]
adox rdi, [ rsp + 0x240 ]
mov r13, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x268 ], r8
mov [ rsp + 0x270 ], r12
mulx r12, r8, [ rax + 0x8 ]
adcx rcx, [ rsp + 0x60 ]
adcx r9, [ rsp + 0x58 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x278 ], r15
mov [ rsp + 0x280 ], r14
mulx r14, r15, [ rax + 0x8 ]
test al, al
adox rcx, [ rsp - 0x30 ]
adox r9, [ rsp - 0x38 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x288 ], r14
mov [ rsp + 0x290 ], r15
mulx r15, r14, [ rsi + 0x0 ]
adcx rbx, [ rsp + 0x30 ]
adcx rbp, [ rsp + 0x28 ]
mov rdx, r13
shrd rdx, rdi, 56
mov rdi, rdx
mov [ rsp + 0x298 ], r15
xor r15, r15
adox rdi, rcx
adox r9, r15
mov rcx, rdi
shrd rcx, r9, 56
xor r9, r9
adox r10, r8
adox r12, r11
mov r15, 0xffffffffffffff 
and r13, r15
mov r11, [ rsp + 0x290 ]
mov r8, r11
adox r8, [ rsp + 0x280 ]
mov r15, [ rsp + 0x288 ]
adox r15, [ rsp + 0x278 ]
mov r11, 0x38 
bzhi r9, rdi, r11
mov rdi, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x2a0 ], r9
mulx r9, r11, [ rax + 0x10 ]
adox r8, r11
adox r9, r15
mov rdx, [ rax + 0x10 ]
mulx r11, r15, [ rsi + 0x8 ]
add rbx, rcx
adc rbp, 0x0
mov rdx, [ rsp + 0x198 ]
test al, al
adox rdx, [ rsp + 0x20 ]
mov rcx, [ rsp + 0x180 ]
adox rcx, [ rsp + 0x18 ]
mov [ rsp + 0x2a8 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x2b0 ], r9
mov [ rsp + 0x2b8 ], r8
mulx r8, r9, [ rax + 0x20 ]
adcx r10, [ rsp + 0xa0 ]
adcx r12, [ rsp + 0x98 ]
mov rdx, r15
test al, al
adox rdx, [ rsp + 0x148 ]
adox r11, [ rsp + 0x140 ]
mov r15, rbx
shrd r15, rbp, 56
xor rbp, rbp
adox rdx, r14
adox r11, [ rsp + 0x298 ]
adcx r10, r15
adc r12, 0x0
mov r14, 0xffffffffffffff 
and rbx, r14
mov r15, rdx
and r15, r14
adox r13, [ rsp + 0xd0 ]
adox rcx, [ rsp + 0xc8 ]
shrd rdx, r11, 56
test al, al
adox r13, [ rsp + 0x1b8 ]
adox rcx, [ rsp + 0x1a0 ]
mov r11, [ rsp + 0x2b8 ]
adcx r11, [ rsp + 0x258 ]
mov r14, [ rsp + 0x2b0 ]
adcx r14, [ rsp + 0x250 ]
mov rbp, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x2c0 ], rbx
mov [ rsp + 0x2c8 ], r15
mulx r15, rbx, [ rsi + 0x20 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x2d0 ], r15
mov [ rsp + 0x2d8 ], rbx
mulx rbx, r15, [ rsi + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x2e0 ], rcx
mov [ rsp + 0x2e8 ], r13
mulx r13, rcx, [ rsi + 0x10 ]
mov rdx, rcx
test al, al
adox rdx, [ rsp + 0x270 ]
adox r13, [ rsp + 0x268 ]
adcx rdx, r15
adcx rbx, r13
test al, al
adox r11, r9
adox r8, r14
mov r9, rdx
mov rdx, [ rsi + 0x0 ]
mulx r15, r14, [ rax + 0x28 ]
adcx r11, r14
adcx r15, r8
test al, al
adox r9, [ rsp + 0xc0 ]
adox rbx, [ rsp + 0xb8 ]
adcx r9, rbp
adc rbx, 0x0
mov rdx, [ rsi + 0x30 ]
mulx rcx, rbp, [ rax + 0x0 ]
test al, al
adox rdi, r9
mov rdx, 0x0 
adox rbx, rdx
mov rdx, [ rax + 0x20 ]
mulx r8, r13, [ rsi + 0x10 ]
mov rdx, [ rax + 0x8 ]
mulx r9, r14, [ rsi + 0x28 ]
mov rdx, 0x38 
mov [ rsp + 0x2f0 ], r8
bzhi r8, r10, rdx
shrd r10, r12, 56
bzhi r12, rdi, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x2f8 ], r12
mov [ rsp + 0x300 ], r13
mulx r13, r12, [ rsi + 0x8 ]
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x10 ], r8
mov r8, [ rsp + 0x2e8 ]
adox r8, [ rsp + 0x208 ]
mov rdx, [ rsp + 0x2e0 ]
adox rdx, [ rsp + 0x200 ]
add r10, [ rsp + 0x2c8 ]
mov [ rsp + 0x308 ], r13
mov r13, r10
shr r13, 56
test al, al
adox r8, [ rsp + 0x1b0 ]
adox rdx, [ rsp + 0x1a8 ]
shrd rdi, rbx, 56
test al, al
adox r11, rdi
mov rbx, 0x0 
adox r15, rbx
mov rdi, r11
shrd rdi, r15, 56
xor r15, r15
adox r8, rbp
adox rcx, rdx
adcx r8, r14
adcx r9, rcx
mov rdx, [ rax + 0x18 ]
mulx rbp, rbx, [ rsi + 0x18 ]
xor rdx, rdx
adox r8, [ rsp + 0x2d8 ]
adox r9, [ rsp + 0x2d0 ]
adcx r8, rbx
adcx rbp, r9
add r8, [ rsp + 0x300 ]
adcx rbp, [ rsp + 0x2f0 ]
mov rdx, [ rsi + 0x0 ]
mulx r14, r15, [ rax + 0x30 ]
xor rdx, rdx
adox r8, r12
adox rbp, [ rsp + 0x308 ]
adcx r8, r15
adcx r14, rbp
xor r12, r12
adox r8, rdi
adox r14, r12
mov rdx, 0x38 
bzhi rdi, r8, rdx
shrd r8, r14, 56
add r8, [ rsp + 0x2a8 ]
mov rcx, r8
shr rcx, 56
bzhi rbx, r8, rdx
mov r9, rcx
add r9, [ rsp + 0x2a0 ]
add rcx, [ rsp + 0x2f8 ]
bzhi r15, r9, rdx
shr r9, 56
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x0 ], r15
mov [ rbp + 0x38 ], rbx
bzhi r14, r10, rdx
bzhi r10, r11, rdx
lea r13, [ r13 + rcx ]
bzhi r11, r13, rdx
mov [ rbp + 0x20 ], r11
add r9, [ rsp + 0x2c0 ]
shr r13, 56
lea r13, [ r13 + r10 ]
mov [ rbp + 0x8 ], r9
mov [ rbp + 0x30 ], rdi
mov [ rbp + 0x18 ], r14
mov [ rbp + 0x28 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 912
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.0939
; seed 3765083775094217 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5513676 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=106, initial num_batches=31): 128948 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.023386938224153903
; number reverted permutation / tried permutation: 56111 / 90173 =62.226%
; number reverted decision / tried decision: 48448 / 89826 =53.935%
; validated in 3.434s
