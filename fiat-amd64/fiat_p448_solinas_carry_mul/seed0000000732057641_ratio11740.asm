SECTION .text
	GLOBAL fiat_p448_solinas_carry_mul
fiat_p448_solinas_carry_mul:
sub rsp, 896
mov rax, rdx
mov rdx, [ rsi + 0x38 ]
mulx r11, r10, [ rax + 0x8 ]
mov rdx, [ rax + 0x28 ]
mulx r8, rcx, [ rsi + 0x38 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x38 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x38 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x28 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x48 ], r14
mov [ rsp - 0x40 ], r13
mulx r13, r14, [ rax + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x38 ], rbx
mov [ rsp - 0x30 ], r9
mulx r9, rbx, [ rax + 0x30 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], r9
mov [ rsp - 0x20 ], rbx
mulx rbx, r9, [ rax + 0x10 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x18 ], rbx
mov [ rsp - 0x10 ], r9
mulx r9, rbx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x8 ], r9
mov [ rsp + 0x0 ], rbx
mulx rbx, r9, [ rax + 0x20 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x8 ], rbx
mov [ rsp + 0x10 ], r9
mulx r9, rbx, [ rax + 0x18 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x18 ], r11
mov [ rsp + 0x20 ], r10
mulx r10, r11, [ rax + 0x30 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x28 ], rdi
mov [ rsp + 0x30 ], r15
mulx r15, rdi, [ rsi + 0x10 ]
mov rdx, rbp
test al, al
adox rdx, rbx
mov [ rsp + 0x38 ], r15
mov r15, r9
adox r15, r12
mov [ rsp + 0x40 ], rdi
mov rdi, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x48 ], r15
mov [ rsp + 0x50 ], r13
mulx r13, r15, [ rsi + 0x30 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x58 ], rdi
mov [ rsp + 0x60 ], r13
mulx r13, rdi, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x68 ], r13
mov [ rsp + 0x70 ], rdi
mulx rdi, r13, [ rax + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x78 ], rdi
mov [ rsp + 0x80 ], r13
mulx r13, rdi, [ rax + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x88 ], r13
mov [ rsp + 0x90 ], rdi
mulx rdi, r13, [ rax + 0x20 ]
mov rdx, rcx
adcx rdx, r11
mov [ rsp + 0x98 ], rdi
mov rdi, r10
adcx rdi, r8
mov [ rsp + 0xa0 ], r13
mov r13, rbp
test al, al
adox r13, rbp
adox r12, r12
mov rbp, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xa8 ], r12
mov [ rsp + 0xb0 ], r13
mulx r13, r12, [ rax + 0x30 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xb8 ], r15
mov [ rsp + 0xc0 ], r14
mulx r14, r15, [ rax + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xc8 ], r14
mov [ rsp + 0xd0 ], r15
mulx r15, r14, [ rax + 0x38 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xd8 ], r15
mov [ rsp + 0xe0 ], r14
mulx r14, r15, [ rax + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xe8 ], r14
mov [ rsp + 0xf0 ], r15
mulx r15, r14, [ rax + 0x28 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0xf8 ], r15
mov [ rsp + 0x100 ], r14
mulx r14, r15, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x108 ], r13
mov [ rsp + 0x110 ], r12
mulx r12, r13, [ rax + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x118 ], r12
mov [ rsp + 0x120 ], r13
mulx r13, r12, [ rsi + 0x20 ]
adcx rbp, r15
mov rdx, r14
adcx rdx, rdi
mov rdi, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x128 ], r13
mov [ rsp + 0x130 ], r12
mulx r12, r13, [ rax + 0x18 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x138 ], r12
mov [ rsp + 0x140 ], r13
mulx r13, r12, [ rsi + 0x30 ]
mov rdx, r12
mov [ rsp + 0x148 ], rdi
xor rdi, rdi
adox rdx, [ rsp + 0x110 ]
mov [ rsp + 0x150 ], rbp
mov rbp, r13
adox rbp, [ rsp + 0x108 ]
mov [ rsp + 0x158 ], r13
mov r13, rdx
adcx r13, [ rsp + 0x110 ]
mov [ rsp + 0x160 ], r12
mov r12, rbp
adcx r12, [ rsp + 0x108 ]
add r13, [ rsp + 0x160 ]
adcx r12, [ rsp + 0x158 ]
add r13, [ rsp + 0xc0 ]
adcx r12, [ rsp + 0x50 ]
test al, al
adox r13, [ rsp + 0xb8 ]
adox r12, [ rsp + 0x60 ]
mov [ rsp + 0x168 ], r12
mov r12, rbx
adcx r12, [ rsp + 0xb0 ]
adcx r9, [ rsp + 0xa8 ]
mov rbx, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x170 ], r9
mulx r9, rdi, [ rax + 0x20 ]
mov rdx, rcx
mov [ rsp + 0x178 ], r12
xor r12, r12
adox rdx, [ rsp + 0x150 ]
adox r8, [ rsp + 0x148 ]
adcx rbx, [ rsp + 0xc0 ]
adcx rbp, [ rsp + 0x50 ]
mov rcx, [ rsp + 0x58 ]
test al, al
adox rcx, [ rsp + 0x30 ]
mov [ rsp + 0x180 ], r13
mov r13, [ rsp + 0x48 ]
adox r13, [ rsp + 0x28 ]
adcx rcx, [ rsp + 0xf0 ]
adcx r13, [ rsp + 0xe8 ]
add rdx, r11
adcx r10, r8
add rbx, [ rsp + 0xb8 ]
adcx rbp, [ rsp + 0x60 ]
xor r11, r11
adox rbx, rdi
mov r12, r9
adox r12, rbp
mov r8, rdx
mov rdx, [ rsi + 0x20 ]
mulx r11, rbp, [ rax + 0x28 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x188 ], r13
mov [ rsp + 0x190 ], rcx
mulx rcx, r13, [ rax + 0x10 ]
adcx rbx, rbp
mov rdx, r11
adcx rdx, r12
test al, al
adox r8, r15
adox r14, r10
mov r15, rdi
adcx r15, [ rsp + 0x180 ]
adcx r9, [ rsp + 0x168 ]
xor rdi, rdi
adox r8, [ rsp + 0x20 ]
adox r14, [ rsp + 0x18 ]
mov r10, rdx
mov rdx, [ rax + 0x18 ]
mulx rdi, r12, [ rsi + 0x28 ]
adcx r15, rbp
adcx r11, r9
xor rdx, rdx
adox r15, [ rsp + 0x70 ]
adox r11, [ rsp + 0x68 ]
mov rbp, [ rsp + 0x20 ]
mov r9, rbp
adcx r9, [ rsp + 0x150 ]
mov [ rsp + 0x198 ], r10
mov r10, [ rsp + 0x18 ]
adcx r10, [ rsp + 0x148 ]
xor rbp, rbp
adox r9, r13
mov rdx, rcx
adox rdx, r10
adcx r9, r12
mov r10, rdi
adcx r10, rdx
xor rdx, rdx
adox r8, r13
adox rcx, r14
adcx r15, [ rsp + 0xe0 ]
adcx r11, [ rsp + 0xd8 ]
mov rdx, [ rax + 0x28 ]
mulx r13, rbp, [ rsi + 0x30 ]
xor rdx, rdx
adox r8, r12
adox rdi, rcx
mov rdx, [ rax + 0x20 ]
mulx r12, r14, [ rsi + 0x20 ]
adcx r9, r14
mov rdx, r12
adcx rdx, r10
add rbx, [ rsp + 0x70 ]
mov r10, [ rsp + 0x198 ]
adcx r10, [ rsp + 0x68 ]
xor rcx, rcx
adox rbx, [ rsp + 0xe0 ]
adox r10, [ rsp + 0xd8 ]
mov [ rsp + 0x1a0 ], r11
mov r11, rbp
adcx r11, [ rsp - 0x30 ]
adcx r13, [ rsp - 0x38 ]
mov rbp, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1a8 ], r15
mulx r15, rcx, [ rax + 0x0 ]
add r11, [ rsp - 0x40 ]
adcx r13, [ rsp - 0x48 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x1b0 ], r10
mov [ rsp + 0x1b8 ], rbx
mulx rbx, r10, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x1c0 ], rbx
mov [ rsp + 0x1c8 ], r10
mulx r10, rbx, [ rax + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1d0 ], r10
mov [ rsp + 0x1d8 ], rbx
mulx rbx, r10, [ rax + 0x28 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x1e0 ], r15
mov [ rsp + 0x1e8 ], rcx
mulx rcx, r15, [ rax + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x1f0 ], rcx
mov [ rsp + 0x1f8 ], r15
mulx r15, rcx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x200 ], r15
mov [ rsp + 0x208 ], rcx
mulx rcx, r15, [ rax + 0x38 ]
xor rdx, rdx
adox r9, r10
mov [ rsp + 0x210 ], rcx
mov rcx, rbx
adox rcx, rbp
adcx r11, [ rsp + 0x0 ]
adcx r13, [ rsp - 0x8 ]
xor rbp, rbp
adox r8, r14
adox r12, rdi
adcx r8, r10
adcx rbx, r12
mov rdx, [ rsi + 0x18 ]
mulx r14, rdi, [ rax + 0x8 ]
mov rdx, [ rax + 0x30 ]
mulx r12, r10, [ rsi + 0x20 ]
test al, al
adox r8, [ rsp - 0x20 ]
adox rbx, [ rsp - 0x28 ]
adcx r8, r15
adcx rbx, [ rsp + 0x210 ]
xor rdx, rdx
adox r8, [ rsp + 0x208 ]
adox rbx, [ rsp + 0x200 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x218 ], rcx
mulx rcx, rbp, [ rax + 0x8 ]
mov rdx, r11
adcx rdx, [ rsp + 0x1e8 ]
mov [ rsp + 0x220 ], r9
mov r9, r13
adcx r9, [ rsp + 0x1e0 ]
add r8, rdi
adcx r14, rbx
xor rdi, rdi
adox rdx, [ rsp + 0x1d8 ]
adox r9, [ rsp + 0x1d0 ]
mov rbx, [ rsp + 0x178 ]
adcx rbx, [ rsp + 0x30 ]
mov [ rsp + 0x228 ], r9
mov r9, [ rsp + 0x170 ]
adcx r9, [ rsp + 0x28 ]
mov rdi, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x230 ], rcx
mov [ rsp + 0x238 ], rbp
mulx rbp, rcx, [ rax + 0x0 ]
test al, al
adox rbx, [ rsp + 0xf0 ]
adox r9, [ rsp + 0xe8 ]
adcx r8, [ rsp - 0x10 ]
adcx r14, [ rsp - 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x240 ], r14
mov [ rsp + 0x248 ], r8
mulx r8, r14, [ rax + 0x10 ]
test al, al
adox r11, [ rsp + 0x1f8 ]
adox r13, [ rsp + 0x1f0 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x250 ], rdi
mov [ rsp + 0x258 ], rbp
mulx rbp, rdi, [ rax + 0x8 ]
adcx r11, rdi
adcx rbp, r13
xor rdx, rdx
adox r11, r14
adox r8, rbp
adcx rbx, r10
mov r14, r12
adcx r14, r9
test al, al
adox r11, [ rsp + 0x130 ]
adox r8, [ rsp + 0x128 ]
adcx r11, [ rsp + 0xa0 ]
adcx r8, [ rsp + 0x98 ]
mov r9, rcx
test al, al
adox r9, [ rsp + 0x1b8 ]
mov r13, [ rsp + 0x1b0 ]
adox r13, [ rsp + 0x258 ]
adcx r11, [ rsp + 0xd0 ]
adcx r8, [ rsp + 0xc8 ]
xor rcx, rcx
adox r9, [ rsp + 0x238 ]
adox r13, [ rsp + 0x230 ]
mov rdx, [ rsi + 0x28 ]
mulx rbp, rdi, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x260 ], r13
mulx r13, rcx, [ rax + 0x38 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x268 ], r9
mov [ rsp + 0x270 ], r13
mulx r13, r9, [ rax + 0x30 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x278 ], rcx
mov [ rsp + 0x280 ], rbp
mulx rbp, rcx, [ rsi + 0x20 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x288 ], rbp
mov [ rsp + 0x290 ], rcx
mulx rcx, rbp, [ rsi + 0x30 ]
adcx r11, r9
adcx r13, r8
xor rdx, rdx
adox rbx, [ rsp + 0x1c8 ]
adox r14, [ rsp + 0x1c0 ]
adcx rbx, rbp
adcx rcx, r14
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rax + 0x20 ]
mov rdx, rdi
xor rbp, rbp
adox rdx, [ rsp + 0x1a8 ]
mov r14, [ rsp + 0x1a0 ]
adox r14, [ rsp + 0x280 ]
adcx rbx, [ rsp + 0x80 ]
adcx rcx, [ rsp + 0x78 ]
mov rdi, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x298 ], rcx
mulx rcx, rbp, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x2a0 ], rbx
mov [ rsp + 0x2a8 ], rcx
mulx rcx, rbx, [ rax + 0x0 ]
test al, al
adox r11, [ rsp + 0x278 ]
adox r13, [ rsp + 0x270 ]
mov rdx, r10
adcx rdx, [ rsp + 0x190 ]
adcx r12, [ rsp + 0x188 ]
add rdi, [ rsp + 0x290 ]
adcx r14, [ rsp + 0x288 ]
mov r10, 0x38 
mov [ rsp + 0x2b0 ], r14
bzhi r14, r11, r10
mov r10, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x2b8 ], r14
mov [ rsp + 0x2c0 ], rdi
mulx rdi, r14, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x2c8 ], rbp
mov [ rsp + 0x2d0 ], r12
mulx r12, rbp, [ rax + 0x10 ]
mov rdx, rbp
adox rdx, [ rsp + 0x250 ]
adox r12, [ rsp + 0x228 ]
mov rbp, [ rsp + 0x220 ]
mov [ rsp + 0x2d8 ], r10
xor r10, r10
adox rbp, [ rsp - 0x20 ]
mov [ rsp + 0x2e0 ], r9
mov r9, [ rsp + 0x218 ]
adox r9, [ rsp - 0x28 ]
adcx rbp, r15
adcx r9, [ rsp + 0x210 ]
shrd r11, r13, 56
xor r15, r15
adox rbp, rbx
adox rcx, r9
mov r10, r11
adcx r10, rbp
adc rcx, 0x0
xor rbx, rbx
adox rdx, r14
adox rdi, r12
mov r15, [ rsp + 0x140 ]
mov r13, r15
adcx r13, [ rsp + 0x248 ]
mov r14, [ rsp + 0x138 ]
adcx r14, [ rsp + 0x240 ]
mov r15, r10
shrd r15, rcx, 56
add r13, r8
adcx r14, [ rsp + 0x2e0 ]
mov r8, [ rsp + 0x2d8 ]
test al, al
adox r8, [ rsp + 0x1c8 ]
mov r12, [ rsp + 0x2d0 ]
adox r12, [ rsp + 0x1c0 ]
mov r9, rdx
shrd r9, rdi, 56
mov rbp, [ rsp + 0x2c8 ]
mov rcx, rbp
xor rdi, rdi
adox rcx, [ rsp + 0x2c0 ]
mov rbx, [ rsp + 0x2a8 ]
adox rbx, [ rsp + 0x2b0 ]
mov rbp, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x2e8 ], r15
mulx r15, rdi, [ rax + 0x18 ]
adcx r13, r9
adc r14, 0x0
test al, al
adox rcx, rdi
adox r15, rbx
adcx r11, r13
adc r14, 0x0
mov rdx, [ rax + 0x0 ]
mulx rbx, r9, [ rsi + 0x10 ]
add r8, r9
adcx rbx, r12
xor rdx, rdx
adox rcx, [ rsp + 0x10 ]
adox r15, [ rsp + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx rdi, r12, [ rax + 0x30 ]
mov rdx, [ rax + 0x28 ]
mulx r9, r13, [ rsi + 0x0 ]
adcx rcx, r13
adcx r9, r15
mov rdx, [ rsi + 0x8 ]
mulx r13, r15, [ rax + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x2f0 ], rdi
mov [ rsp + 0x2f8 ], r12
mulx r12, rdi, [ rax + 0x10 ]
test al, al
adox r8, r15
adox r13, rbx
mov rdx, rdi
adcx rdx, [ rsp + 0x2a0 ]
adcx r12, [ rsp + 0x298 ]
xor rbx, rbx
adox r8, [ rsp + 0x120 ]
adox r13, [ rsp + 0x118 ]
mov r15, r11
shrd r15, r14, 56
test al, al
adox rcx, r15
adox r9, rbx
mov r14, [ rsp + 0x2e8 ]
mov rdi, r14
adcx rdi, [ rsp + 0x268 ]
mov r15, [ rsp + 0x260 ]
adc r15, 0x0
xor r14, r14
adox rdx, [ rsp + 0x90 ]
adox r12, [ rsp + 0x88 ]
mov rbx, rcx
shrd rbx, r9, 56
mov r9, 0x38 
bzhi r14, rbp, r9
adox rdx, [ rsp + 0x40 ]
adox r12, [ rsp + 0x38 ]
add rdx, [ rsp + 0x100 ]
adcx r12, [ rsp + 0xf8 ]
test al, al
adox rdx, [ rsp + 0x2f8 ]
adox r12, [ rsp + 0x2f0 ]
adcx rdx, rbx
adc r12, 0x0
mov rbp, rdi
shrd rbp, r15, 56
xor r15, r15
adox r8, rbp
adox r13, r15
mov rbx, r8
shrd rbx, r13, 56
lea rbx, [ rbx + r14 ]
mov r14, rdx
shrd r14, r12, 56
add r14, [ rsp + 0x2b8 ]
mov r12, r14
shr r12, 56
bzhi rbp, rbx, r9
shr rbx, 56
bzhi r13, r11, r9
lea r13, [ r13 + r12 ]
lea rbx, [ rbx + r13 ]
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x18 ], rbp
bzhi rbp, r10, r9
lea rbp, [ rbp + r12 ]
bzhi r10, rbp, r9
shr rbp, 56
mov r12, rbx
shr r12, 56
bzhi r13, rdi, r9
bzhi rdi, rcx, r9
lea rbp, [ rbp + r13 ]
lea r12, [ r12 + rdi ]
mov [ r11 + 0x8 ], rbp
bzhi rcx, r14, r9
mov [ r11 + 0x0 ], r10
bzhi r14, r8, r9
bzhi r8, rdx, r9
bzhi rdx, rbx, r9
mov [ r11 + 0x30 ], r8
mov [ r11 + 0x20 ], rdx
mov [ r11 + 0x28 ], r12
mov [ r11 + 0x38 ], rcx
mov [ r11 + 0x10 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 896
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.1740
; seed 0447477664383917 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5363390 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=104, initial num_batches=31): 123547 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.023035244500213485
; number reverted permutation / tried permutation: 52195 / 89932 =58.038%
; number reverted decision / tried decision: 47484 / 90067 =52.721%
; validated in 2.86s
