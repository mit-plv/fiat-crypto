SECTION .text
	GLOBAL fiat_p448_solinas_carry_mul
fiat_p448_solinas_carry_mul:
sub rsp, 856
mov rax, rdx
mov rdx, [ rdx + 0x18 ]
mulx r11, r10, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x10 ]
mulx r8, rcx, [ rax + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x20 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x30 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x48 ], r12
mov [ rsp - 0x40 ], rbp
mulx rbp, r12, [ rsi + 0x28 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x38 ], r8
mov [ rsp - 0x30 ], rcx
mulx rcx, r8, [ rsi + 0x18 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x28 ], rbx
mov [ rsp - 0x20 ], r9
mulx r9, rbx, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x18 ], rcx
mov [ rsp - 0x10 ], r8
mulx r8, rcx, [ rax + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x8 ], r8
mov [ rsp + 0x0 ], rcx
mulx rcx, r8, [ rax + 0x20 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x8 ], rbp
mov [ rsp + 0x10 ], r12
mulx r12, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x18 ], r12
mov [ rsp + 0x20 ], rbp
mulx rbp, r12, [ rax + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x28 ], rbp
mov [ rsp + 0x30 ], r12
mulx r12, rbp, [ rsi + 0x28 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x38 ], r11
mov [ rsp + 0x40 ], r10
mulx r10, r11, [ rsi + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x48 ], r14
mov [ rsp + 0x50 ], r13
mulx r13, r14, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x58 ], r10
mov [ rsp + 0x60 ], r11
mulx r11, r10, [ rax + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x68 ], r11
mov [ rsp + 0x70 ], r10
mulx r10, r11, [ rax + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x78 ], r10
mov [ rsp + 0x80 ], r11
mulx r11, r10, [ rax + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x88 ], r11
mov [ rsp + 0x90 ], r10
mulx r10, r11, [ rax + 0x30 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x98 ], r10
mov [ rsp + 0xa0 ], r11
mulx r11, r10, [ rax + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xa8 ], r11
mov [ rsp + 0xb0 ], r10
mulx r10, r11, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0xb8 ], r10
mov [ rsp + 0xc0 ], r11
mulx r11, r10, [ rsi + 0x20 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0xc8 ], r11
mov [ rsp + 0xd0 ], r10
mulx r10, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xd8 ], r10
mov [ rsp + 0xe0 ], r11
mulx r11, r10, [ rax + 0x18 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0xe8 ], rcx
mov [ rsp + 0xf0 ], r8
mulx r8, rcx, [ rsi + 0x38 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0xf8 ], r12
mov [ rsp + 0x100 ], rbp
mulx rbp, r12, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x108 ], r13
mov [ rsp + 0x110 ], r14
mulx r14, r13, [ rax + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x118 ], r14
mov [ rsp + 0x120 ], r13
mulx r13, r14, [ rax + 0x10 ]
mov rdx, rcx
test al, al
adox rdx, rcx
mov [ rsp + 0x128 ], r13
mov r13, r8
adox r13, r8
adcx rcx, r10
mov [ rsp + 0x130 ], r14
mov r14, r11
adcx r14, r8
mov r8, rdx
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x138 ], r14
mov [ rsp + 0x140 ], rcx
mulx rcx, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x148 ], rcx
mov [ rsp + 0x150 ], r14
mulx r14, rcx, [ rax + 0x30 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x158 ], r13
mov [ rsp + 0x160 ], r8
mulx r8, r13, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x168 ], r9
mov [ rsp + 0x170 ], rbx
mulx rbx, r9, [ rax + 0x28 ]
add r13, r9
adcx rbx, r8
test al, al
adox r13, rcx
adox r14, rbx
adcx r13, r12
adcx rbp, r14
mov rdx, [ rax + 0x18 ]
mulx rcx, r12, [ rsi + 0x20 ]
mov rdx, [ rax + 0x38 ]
mulx r9, r8, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x30 ]
mulx r14, rbx, [ rax + 0x8 ]
mov rdx, r15
mov [ rsp + 0x178 ], rcx
xor rcx, rcx
adox rdx, [ rsp + 0x170 ]
mov [ rsp + 0x180 ], r12
mov r12, rdi
adox r12, [ rsp + 0x168 ]
mov rcx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x188 ], r14
mov [ rsp + 0x190 ], rbx
mulx rbx, r14, [ rax + 0x0 ]
adcx rcx, r8
mov rdx, r9
adcx rdx, r12
mov r12, r13
test al, al
adox r12, r14
adox rbx, rbp
mov r14, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x198 ], rbx
mov [ rsp + 0x1a0 ], r12
mulx r12, rbx, [ rsi + 0x38 ]
adcx r13, rbx
adcx r12, rbp
mov rdx, rcx
add rdx, [ rsp + 0x110 ]
mov rbp, r14
adcx rbp, [ rsp + 0x108 ]
mov rbx, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x1a8 ], r12
mov [ rsp + 0x1b0 ], r13
mulx r13, r12, [ rsi + 0x30 ]
test al, al
adox rbx, r12
mov rdx, r13
adox rdx, rbp
adcx rcx, [ rsp + 0x170 ]
adcx r14, [ rsp + 0x168 ]
test al, al
adox rbx, [ rsp + 0x100 ]
adox rdx, [ rsp + 0xf8 ]
adcx rcx, r15
adcx rdi, r14
xor r15, r15
adox rcx, r8
adox r9, rdi
mov r8, rdx
mov rdx, [ rsi + 0x28 ]
mulx r14, rbp, [ rax + 0x10 ]
adcx rcx, [ rsp + 0x110 ]
adcx r9, [ rsp + 0x108 ]
test al, al
adox rcx, r12
adox r13, r9
mov rdx, [ rsi + 0x38 ]
mulx rdi, r12, [ rax + 0x30 ]
mov rdx, [ rsp + 0x190 ]
mov r9, rdx
adcx r9, [ rsp + 0x1b0 ]
mov [ rsp + 0x1b8 ], r13
mov r13, [ rsp + 0x188 ]
adcx r13, [ rsp + 0x1a8 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x1c0 ], rcx
mulx rcx, r15, [ rsi + 0x30 ]
test al, al
adox r9, rbp
adox r14, r13
adcx rbx, [ rsp + 0xf0 ]
adcx r8, [ rsp + 0xe8 ]
xor rdx, rdx
adox r9, [ rsp + 0x180 ]
adox r14, [ rsp + 0x178 ]
adcx rbx, [ rsp + 0x60 ]
adcx r8, [ rsp + 0x58 ]
mov rbp, r10
add rbp, [ rsp + 0x160 ]
adcx r11, [ rsp + 0x158 ]
mov r10, r12
add r10, r15
mov r13, rcx
adcx r13, rdi
add rbx, [ rsp + 0xa0 ]
adcx r8, [ rsp + 0x98 ]
test al, al
adox rbp, [ rsp + 0x50 ]
adox r11, [ rsp + 0x48 ]
mov [ rsp + 0x1c8 ], r14
mov r14, r10
adcx r14, r12
adcx rdi, r13
xor r12, r12
adox r14, r15
adox rcx, rdi
adcx rbx, [ rsp + 0xe0 ]
adcx r8, [ rsp + 0xd8 ]
mov rdx, [ rax + 0x28 ]
mulx rdi, r15, [ rsi + 0x20 ]
mov rdx, [ rsp + 0x100 ]
mov [ rsp + 0x1d0 ], r8
mov r8, rdx
mov [ rsp + 0x1d8 ], rbx
xor rbx, rbx
adox r8, [ rsp + 0x1c0 ]
mov r12, [ rsp + 0xf8 ]
adox r12, [ rsp + 0x1b8 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x1e0 ], r9
mulx r9, rbx, [ rax + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x1e8 ], rdi
mov [ rsp + 0x1f0 ], r15
mulx r15, rdi, [ rax + 0x28 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x1f8 ], r11
mov [ rsp + 0x200 ], rbp
mulx rbp, r11, [ rsi + 0x8 ]
adcx r8, [ rsp + 0xf0 ]
adcx r12, [ rsp + 0xe8 ]
test al, al
adox r10, rbx
mov rdx, r9
adox rdx, r13
adcx r10, [ rsp + 0x40 ]
adcx rdx, [ rsp + 0x38 ]
test al, al
adox r8, [ rsp + 0x60 ]
adox r12, [ rsp + 0x58 ]
adcx r14, rbx
adcx r9, rcx
add r14, [ rsp + 0x40 ]
adcx r9, [ rsp + 0x38 ]
mov r13, [ rsp + 0x120 ]
mov rcx, r13
test al, al
adox rcx, [ rsp + 0x1a0 ]
mov rbx, [ rsp + 0x118 ]
adox rbx, [ rsp + 0x198 ]
mov r13, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x208 ], r9
mov [ rsp + 0x210 ], r14
mulx r14, r9, [ rsi + 0x0 ]
mov rdx, rdi
adcx rdx, [ rsp + 0x200 ]
mov [ rsp + 0x218 ], r12
mov r12, r15
adcx r12, [ rsp + 0x1f8 ]
mov [ rsp + 0x220 ], r12
xor r12, r12
adox r10, [ rsp + 0x10 ]
adox r13, [ rsp + 0x8 ]
adcx r10, [ rsp + 0x1f0 ]
adcx r13, [ rsp + 0x1e8 ]
mov [ rsp + 0x228 ], rdx
xor rdx, rdx
adox r10, [ rsp - 0x10 ]
adox r13, [ rsp - 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x230 ], r8
mulx r8, r12, [ rsi + 0x28 ]
adcx r10, [ rsp + 0x150 ]
adcx r13, [ rsp + 0x148 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x238 ], r8
mov [ rsp + 0x240 ], r12
mulx r12, r8, [ rsi + 0x18 ]
add rcx, r11
adcx rbp, rbx
xor rdx, rdx
adox rcx, r9
adox r14, rbp
mov r11, 0x38 
bzhi rbx, rcx, r11
shrd rcx, r14, 56
mov rdx, [ rsi + 0x0 ]
mulx rbp, r9, [ rax + 0x38 ]
mov rdx, [ rsp + 0x1e0 ]
xor r14, r14
adox rdx, [ rsp - 0x20 ]
mov r11, [ rsp + 0x1c8 ]
adox r11, [ rsp - 0x28 ]
mov [ rsp + 0x248 ], rbx
mov rbx, [ rsp + 0x50 ]
mov [ rsp + 0x250 ], rcx
mov rcx, rbx
adcx rcx, [ rsp + 0x140 ]
mov [ rsp + 0x258 ], rbp
mov rbp, [ rsp + 0x48 ]
adcx rbp, [ rsp + 0x138 ]
mov rbx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x260 ], r9
mulx r9, r14, [ rax + 0x30 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x268 ], r11
mov [ rsp + 0x270 ], rbx
mulx rbx, r11, [ rsi + 0x8 ]
add rcx, rdi
adcx r15, rbp
test al, al
adox r10, r11
adox rbx, r13
adcx rcx, r14
mov rdx, r9
adcx rdx, r15
mov rdi, [ rsp + 0x230 ]
test al, al
adox rdi, [ rsp + 0xa0 ]
mov r13, [ rsp + 0x218 ]
adox r13, [ rsp + 0x98 ]
mov rbp, rdx
mov rdx, [ rax + 0x30 ]
mulx r15, r11, [ rsi + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x278 ], rbx
mov [ rsp + 0x280 ], r10
mulx r10, rbx, [ rsi + 0x0 ]
adcx rcx, r8
mov rdx, r12
adcx rdx, rbp
mov rbp, [ rsp + 0x90 ]
mov [ rsp + 0x288 ], rdx
mov rdx, rbp
test al, al
adox rdx, [ rsp + 0x270 ]
mov [ rsp + 0x290 ], rcx
mov rcx, [ rsp + 0x88 ]
adox rcx, [ rsp + 0x268 ]
adcx rdx, r11
adcx r15, rcx
mov rbp, rdx
mov rdx, [ rax + 0x0 ]
mulx rcx, r11, [ rsi + 0x30 ]
mov rdx, r14
mov [ rsp + 0x298 ], r13
xor r13, r13
adox rdx, [ rsp + 0x228 ]
adox r9, [ rsp + 0x220 ]
adcx rdx, r8
adcx r12, r9
xor r8, r8
adox rdx, r11
adox rcx, r12
adcx rbp, [ rsp + 0x260 ]
adcx r15, [ rsp + 0x258 ]
mov r13, rbp
shrd r13, r15, 56
mov r14, rbx
add r14, [ rsp + 0x1d8 ]
adcx r10, [ rsp + 0x1d0 ]
mov rbx, [ rsp + 0x210 ]
xor r11, r11
adox rbx, [ rsp + 0x10 ]
mov r8, [ rsp + 0x208 ]
adox r8, [ rsp + 0x8 ]
mov r9, 0xffffffffffffff 
and rbp, r9
mov r12, r13
adox r12, r14
adox r10, r11
adcx rbx, [ rsp + 0x1f0 ]
adcx r8, [ rsp + 0x1e8 ]
mov r15, rdx
mov rdx, [ rax + 0x8 ]
mulx r11, r14, [ rsi + 0x18 ]
test al, al
adox rbx, [ rsp - 0x10 ]
adox r8, [ rsp - 0x18 ]
adcx rdi, [ rsp + 0xe0 ]
mov rdx, [ rsp + 0xd8 ]
adcx rdx, [ rsp + 0x298 ]
mov r9, r12
shrd r9, r10, 56
add r15, [ rsp + 0x240 ]
adcx rcx, [ rsp + 0x238 ]
add rdi, [ rsp + 0x30 ]
adcx rdx, [ rsp + 0x28 ]
add rdi, r14
adcx r11, rdx
xor r10, r10
adox rbx, [ rsp + 0x150 ]
adox r8, [ rsp + 0x148 ]
adcx rbx, [ rsp + 0x0 ]
adcx r8, [ rsp - 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx r10, r14, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x2a0 ], rbp
mov [ rsp + 0x2a8 ], r8
mulx r8, rbp, [ rax + 0x28 ]
mov rdx, [ rsp + 0x280 ]
add rdx, [ rsp + 0x70 ]
mov [ rsp + 0x2b0 ], rbx
mov rbx, [ rsp + 0x278 ]
adcx rbx, [ rsp + 0x68 ]
mov [ rsp + 0x2b8 ], r8
xor r8, r8
adox rdx, r9
adox rbx, r8
adcx rdi, [ rsp + 0x20 ]
adcx r11, [ rsp + 0x18 ]
test al, al
adox rdi, r14
adox r10, r11
mov r9, rdx
shrd r9, rbx, 56
add rdi, [ rsp + 0xc0 ]
adcx r10, [ rsp + 0xb8 ]
test al, al
adox rdi, [ rsp + 0x250 ]
adox r10, r8
mov r14, 0xffffffffffffff 
and rdx, r14
adox r13, rdi
adox r10, r8
mov rbx, rdx
mov rdx, [ rsi + 0x10 ]
mulx rdi, r11, [ rax + 0x0 ]
adcx r15, [ rsp + 0xd0 ]
adcx rcx, [ rsp + 0xc8 ]
xor rdx, rdx
adox r15, [ rsp + 0xb0 ]
adox rcx, [ rsp + 0xa8 ]
mov r8, r13
shrd r8, r10, 56
mov rdx, [ rsi + 0x10 ]
mulx r14, r10, [ rax + 0x20 ]
mov rdx, r11
add rdx, [ rsp + 0x290 ]
adcx rdi, [ rsp + 0x288 ]
mov r11, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x2c0 ], rbx
mov [ rsp + 0x2c8 ], r8
mulx r8, rbx, [ rsi + 0x0 ]
add r11, [ rsp + 0x80 ]
adcx rdi, [ rsp + 0x78 ]
xor rdx, rdx
adox r15, r10
adox r14, rcx
adcx r15, rbp
adcx r14, [ rsp + 0x2b8 ]
mov rdx, [ rax + 0x8 ]
mulx rcx, rbp, [ rsi + 0x20 ]
mov rdx, rbp
xor r10, r10
adox rdx, [ rsp + 0x2b0 ]
adox rcx, [ rsp + 0x2a8 ]
adcx rdx, [ rsp + 0x130 ]
adcx rcx, [ rsp + 0x128 ]
mov rbp, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x2d0 ], r14
mulx r14, r10, [ rax + 0x28 ]
xor rdx, rdx
adox r11, rbx
adox r8, rdi
mov rdx, [ rsi + 0x0 ]
mulx rdi, rbx, [ rax + 0x30 ]
adcx rbp, [ rsp - 0x30 ]
adcx rcx, [ rsp - 0x38 ]
test al, al
adox r11, r9
mov rdx, 0x0 
adox r8, rdx
mov r9, 0x38 
bzhi rdx, r11, r9
adox rbp, [ rsp - 0x40 ]
adox rcx, [ rsp - 0x48 ]
xor r9, r9
adox rbp, r10
adox r14, rcx
adcx r15, rbx
adcx rdi, [ rsp + 0x2d0 ]
xor r10, r10
adox rbp, [ rsp + 0x2c8 ]
adox r14, r10
mov r9, 0xffffffffffffff 
mov rbx, rbp
and rbx, r9
shrd r11, r8, 56
add r11, [ rsp + 0x248 ]
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x10 ], rdx
shrd rbp, r14, 56
and r12, r9
adox r15, rbp
adox rdi, r10
mov rdx, r11
and rdx, r9
mov rcx, r15
and rcx, r9
mov [ r8 + 0x18 ], rdx
shrd r15, rdi, 56
add r15, [ rsp + 0x2a0 ]
mov r14, r15
and r14, r9
mov [ r8 + 0x30 ], rcx
and r13, r9
shr r15, 56
lea r12, [ r12 + r15 ]
mov rbp, r12
shr rbp, 56
lea r13, [ r13 + r15 ]
and r12, r9
mov [ r8 + 0x38 ], r14
add rbp, [ rsp + 0x2c0 ]
shr r11, 56
mov [ r8 + 0x8 ], rbp
lea r11, [ r11 + r13 ]
mov rdi, r11
shr rdi, 56
lea rdi, [ rdi + rbx ]
and r11, r9
mov [ r8 + 0x28 ], rdi
mov [ r8 + 0x20 ], r11
mov [ r8 + 0x0 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 856
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.0153
; seed 2945501258608733 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 77180 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=48, initial num_batches=31): 1186 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.015366675304483027
; number reverted permutation / tried permutation: 257 / 506 =50.791%
; number reverted decision / tried decision: 140 / 493 =28.398%
; validated in 5.753s
