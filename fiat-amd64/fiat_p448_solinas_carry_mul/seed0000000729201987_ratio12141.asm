SECTION .text
	GLOBAL fiat_p448_solinas_carry_mul
fiat_p448_solinas_carry_mul:
sub rsp, 840
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx r11, r10, [ rax + 0x20 ]
mov rdx, [ rsi + 0x30 ]
mulx r8, rcx, [ rax + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x38 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x38 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x48 ], r11
mov [ rsp - 0x40 ], r10
mulx r10, r11, [ rsi + 0x38 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x38 ], r10
mov [ rsp - 0x30 ], r11
mulx r11, r10, [ rsi + 0x38 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x28 ], rbx
mov [ rsp - 0x20 ], r9
mulx r9, rbx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x18 ], r9
mov [ rsp - 0x10 ], rbx
mulx rbx, r9, [ rsi + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x8 ], rbx
mov [ rsp + 0x0 ], r9
mulx r9, rbx, [ rsi + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x8 ], r9
mov [ rsp + 0x10 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
xor rdx, rdx
adox rbp, rcx
adox r8, r12
mov rdx, [ rax + 0x0 ]
mulx r12, rcx, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x18 ], r12
mov [ rsp + 0x20 ], rcx
mulx rcx, r12, [ rax + 0x0 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x28 ], rbx
mov [ rsp + 0x30 ], r9
mulx r9, rbx, [ rsi + 0x20 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x38 ], rcx
mov [ rsp + 0x40 ], r12
mulx r12, rcx, [ rsi + 0x38 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x48 ], r9
mov [ rsp + 0x50 ], rbx
mulx rbx, r9, [ rsi + 0x28 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x58 ], rbx
mov [ rsp + 0x60 ], r9
mulx r9, rbx, [ rsi + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x68 ], r9
mov [ rsp + 0x70 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x78 ], rbx
mov [ rsp + 0x80 ], r9
mulx r9, rbx, [ rsi + 0x8 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x88 ], r9
mov [ rsp + 0x90 ], rbx
mulx rbx, r9, [ rsi + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x98 ], rbx
mov [ rsp + 0xa0 ], r9
mulx r9, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xa8 ], r9
mov [ rsp + 0xb0 ], rbx
mulx rbx, r9, [ rax + 0x18 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0xb8 ], rbx
mov [ rsp + 0xc0 ], r9
mulx r9, rbx, [ rsi + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0xc8 ], r9
mov [ rsp + 0xd0 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xd8 ], rbx
mov [ rsp + 0xe0 ], r9
mulx r9, rbx, [ rax + 0x38 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0xe8 ], r8
mov [ rsp + 0xf0 ], rbp
mulx rbp, r8, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xf8 ], rdi
mov [ rsp + 0x100 ], r15
mulx r15, rdi, [ rax + 0x30 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x108 ], r14
mov [ rsp + 0x110 ], r13
mulx r13, r14, [ rsi + 0x28 ]
mov rdx, rdi
adcx rdx, rbx
mov [ rsp + 0x118 ], r13
mov r13, r9
adcx r13, r15
mov [ rsp + 0x120 ], r14
mov r14, rdx
add r14, r10
mov [ rsp + 0x128 ], r12
mov r12, r11
adcx r12, r13
test al, al
adox rdx, rdi
adox r15, r13
mov rdi, rcx
adcx rdi, r8
mov r13, rbp
adcx r13, [ rsp + 0x128 ]
add rdi, [ rsp + 0x110 ]
adcx r13, [ rsp + 0x108 ]
mov [ rsp + 0x130 ], r13
xor r13, r13
adox r14, [ rsp + 0x100 ]
adox r12, [ rsp + 0xf8 ]
mov r13, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x138 ], r12
mov [ rsp + 0x140 ], r14
mulx r14, r12, [ rax + 0x0 ]
adcx r13, rbx
adcx r9, r15
mov rdx, rdi
add rdx, rcx
mov rbx, [ rsp + 0x128 ]
adcx rbx, [ rsp + 0x130 ]
xor rcx, rcx
adox r13, r10
adox r11, r9
adcx rdx, r8
adcx rbp, rbx
mov r10, rdx
mov rdx, [ rax + 0x30 ]
mulx r15, r8, [ rsi + 0x28 ]
mov rdx, r8
xor r9, r9
adox rdx, [ rsp + 0xf0 ]
adox r15, [ rsp + 0xe8 ]
adcx rdx, [ rsp - 0x20 ]
adcx r15, [ rsp - 0x28 ]
mov rcx, rdx
mov rdx, [ rsi + 0x18 ]
mulx r8, rbx, [ rax + 0x0 ]
mov rdx, rcx
mov [ rsp + 0x148 ], rbp
xor rbp, rbp
adox rdx, r12
adox r14, r15
adcx rcx, rbx
adcx r8, r15
add r13, [ rsp + 0x100 ]
adcx r11, [ rsp + 0xf8 ]
xor r9, r9
adox rcx, [ rsp + 0xb0 ]
adox r8, [ rsp + 0xa8 ]
mov rbp, rdx
mov rdx, [ rax + 0x20 ]
mulx r15, r12, [ rsi + 0x30 ]
adcx rcx, [ rsp + 0x90 ]
adcx r8, [ rsp + 0x88 ]
mov rdx, [ rsi + 0x38 ]
mulx r9, rbx, [ rax + 0x38 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x150 ], r8
mov [ rsp + 0x158 ], rcx
mulx rcx, r8, [ rsi + 0x38 ]
mov rdx, rbx
mov [ rsp + 0x160 ], r11
xor r11, r11
adox rdx, [ rsp - 0x30 ]
mov [ rsp + 0x168 ], r13
mov r13, r9
adox r13, [ rsp - 0x38 ]
mov r11, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x170 ], r13
mov [ rsp + 0x178 ], r15
mulx r15, r13, [ rsi + 0x30 ]
adcx rbp, r13
adcx r15, r14
mov rdx, [ rax + 0x10 ]
mulx r13, r14, [ rsi + 0x28 ]
mov rdx, rbx
add rdx, rbx
adcx r9, r9
add rdi, r8
mov rbx, rcx
adcx rbx, [ rsp + 0x130 ]
mov [ rsp + 0x180 ], r11
xor r11, r11
adox rbp, r14
adox r13, r15
adcx r10, [ rsp + 0x110 ]
mov r15, [ rsp + 0x148 ]
adcx r15, [ rsp + 0x108 ]
xor r14, r14
adox rdx, [ rsp - 0x30 ]
adox r9, [ rsp - 0x38 ]
adcx r10, r8
adcx rcx, r15
xor r11, r11
adox rdx, r12
adox r9, [ rsp + 0x178 ]
adcx rdx, [ rsp + 0x60 ]
adcx r9, [ rsp + 0x58 ]
mov r14, rdx
mov rdx, [ rsi + 0x30 ]
mulx r15, r8, [ rax + 0x10 ]
test al, al
adox rdi, r8
mov rdx, r15
adox rdx, rbx
mov rbx, [ rsp + 0x168 ]
adcx rbx, [ rsp + 0x120 ]
mov [ rsp + 0x188 ], r9
mov r9, [ rsp + 0x160 ]
adcx r9, [ rsp + 0x118 ]
mov r11, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x190 ], r14
mov [ rsp + 0x198 ], r9
mulx r9, r14, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x1a0 ], rbx
mov [ rsp + 0x1a8 ], rcx
mulx rcx, rbx, [ rax + 0x18 ]
xor rdx, rdx
adox rdi, rbx
mov [ rsp + 0x1b0 ], r10
mov r10, rcx
adox r10, r11
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x1b8 ], r13
mulx r13, r11, [ rax + 0x28 ]
adcx rdi, [ rsp + 0x50 ]
adcx r10, [ rsp + 0x48 ]
test al, al
adox rdi, [ rsp + 0xa0 ]
adox r10, [ rsp + 0x98 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x1c0 ], r13
mov [ rsp + 0x1c8 ], r11
mulx r11, r13, [ rax + 0x30 ]
adcx rbp, r14
adcx r9, [ rsp + 0x1b8 ]
test al, al
adox rbp, [ rsp - 0x40 ]
adox r9, [ rsp - 0x48 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x1d0 ], r9
mulx r9, r14, [ rsi + 0x8 ]
adcx rdi, r13
mov rdx, r11
adcx rdx, r10
test al, al
adox rbp, [ rsp + 0x1c8 ]
mov r10, [ rsp + 0x1d0 ]
adox r10, [ rsp + 0x1c0 ]
adcx rbp, r14
adcx r9, r10
add rbp, [ rsp - 0x10 ]
adcx r9, [ rsp - 0x18 ]
mov r14, rbp
shrd r14, r9, 56
mov r10, r8
test al, al
adox r10, [ rsp + 0x1b0 ]
adox r15, [ rsp + 0x1a8 ]
mov r8, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x1d8 ], r14
mulx r14, r9, [ rax + 0x28 ]
adcx r10, rbx
adcx rcx, r15
test al, al
adox r10, [ rsp + 0x50 ]
adox rcx, [ rsp + 0x48 ]
mov rdx, [ rsi + 0x18 ]
mulx r15, rbx, [ rax + 0x30 ]
adcx r10, [ rsp + 0xa0 ]
adcx rcx, [ rsp + 0x98 ]
mov rdx, [ rsp + 0x140 ]
test al, al
adox rdx, [ rsp + 0x120 ]
mov [ rsp + 0x1e0 ], rcx
mov rcx, [ rsp + 0x138 ]
adox rcx, [ rsp + 0x118 ]
adcx rdi, [ rsp + 0x0 ]
adcx r8, [ rsp - 0x8 ]
mov [ rsp + 0x1e8 ], r10
mov r10, 0x38 
mov [ rsp + 0x1f0 ], r15
bzhi r15, rbp, r10
adox rdi, [ rsp + 0x40 ]
adox r8, [ rsp + 0x38 ]
xor rbp, rbp
adox rdx, r9
mov r10, r14
adox r10, rcx
adcx rdx, rbx
adcx r10, [ rsp + 0x1f0 ]
mov rcx, rdx
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x1f8 ], r15
mulx r15, rbp, [ rsi + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x200 ], r15
mov [ rsp + 0x208 ], rbp
mulx rbp, r15, [ rsi + 0x8 ]
mov rdx, r9
test al, al
adox rdx, [ rsp + 0x1a0 ]
adox r14, [ rsp + 0x198 ]
mov r9, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x210 ], r8
mov [ rsp + 0x218 ], rdi
mulx rdi, r8, [ rax + 0x8 ]
adcx rcx, [ rsp + 0xd0 ]
adcx r10, [ rsp + 0xc8 ]
add r9, rbx
adcx r14, [ rsp + 0x1f0 ]
test al, al
adox r9, [ rsp + 0xd0 ]
adox r14, [ rsp + 0xc8 ]
adcx rcx, r15
adcx rbp, r10
mov rdx, [ rax + 0x0 ]
mulx r15, rbx, [ rsi + 0x28 ]
mov rdx, r12
test al, al
adox rdx, [ rsp + 0x180 ]
mov r10, [ rsp + 0x170 ]
adox r10, [ rsp + 0x178 ]
adcx r9, rbx
adcx r15, r14
test al, al
adox r9, r8
adox rdi, r15
mov r12, rdx
mov rdx, [ rsi + 0x20 ]
mulx r14, r8, [ rax + 0x30 ]
mov rdx, [ rsi + 0x0 ]
mulx r15, rbx, [ rax + 0x8 ]
mov rdx, r13
adcx rdx, [ rsp + 0x1e8 ]
adcx r11, [ rsp + 0x1e0 ]
mov r13, [ rsp + 0x218 ]
mov [ rsp + 0x220 ], rdi
mov rdi, r13
add rdi, [ rsp + 0x1d8 ]
mov [ rsp + 0x228 ], r9
mov r9, [ rsp + 0x210 ]
adc r9, 0x0
mov r13, rdi
shrd r13, r9, 56
test al, al
adox rdx, [ rsp + 0x0 ]
adox r11, [ rsp - 0x8 ]
adcx rcx, rbx
adcx r15, rbp
add rcx, r13
adc r15, 0x0
mov rbp, rdx
mov rdx, [ rax + 0x8 ]
mulx r9, rbx, [ rsi + 0x8 ]
xor rdx, rdx
adox r12, [ rsp + 0x60 ]
adox r10, [ rsp + 0x58 ]
adcx r12, r8
mov r13, r14
adcx r13, r10
mov r10, r8
test al, al
adox r10, [ rsp + 0x190 ]
adox r14, [ rsp + 0x188 ]
mov r8, rcx
shrd r8, r15, 56
test al, al
adox r10, [ rsp + 0x208 ]
adox r14, [ rsp + 0x200 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x230 ], r14
mulx r14, r15, [ rsi + 0x20 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x238 ], r10
mov [ rsp + 0x240 ], r8
mulx r8, r10, [ rsi + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x248 ], r8
mov [ rsp + 0x250 ], r10
mulx r10, r8, [ rsi + 0x0 ]
adcx r12, [ rsp + 0x208 ]
adcx r13, [ rsp + 0x200 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x258 ], r10
mov [ rsp + 0x260 ], r8
mulx r8, r10, [ rsi + 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x268 ], r8
mov [ rsp + 0x270 ], r10
mulx r10, r8, [ rsi + 0x10 ]
test al, al
adox r12, [ rsp + 0xe0 ]
adox r13, [ rsp + 0xd8 ]
adcx r12, rbx
adcx r9, r13
mov rdx, [ rsi + 0x20 ]
mulx r13, rbx, [ rax + 0x10 ]
test al, al
adox rbp, r15
adox r14, r11
mov rdx, [ rsp + 0x260 ]
mov r11, rdx
adcx r11, [ rsp + 0x158 ]
mov r15, [ rsp + 0x258 ]
adcx r15, [ rsp + 0x150 ]
add rbp, [ rsp + 0x10 ]
adcx r14, [ rsp + 0x8 ]
add rbp, [ rsp + 0x250 ]
adcx r14, [ rsp + 0x248 ]
mov rdx, r11
shrd rdx, r15, 56
mov r15, 0xffffffffffffff 
and r11, r15
mov r15, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x278 ], r11
mov [ rsp + 0x280 ], r13
mulx r13, r11, [ rax + 0x28 ]
adox r12, [ rsp + 0x80 ]
adox r9, [ rsp + 0x78 ]
adcx r12, [ rsp + 0x240 ]
adc r9, 0x0
test al, al
adox rbp, [ rsp + 0xc0 ]
adox r14, [ rsp + 0xb8 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x288 ], rbx
mov [ rsp + 0x290 ], r15
mulx r15, rbx, [ rsi + 0x8 ]
mov rdx, r12
shrd rdx, r9, 56
xor r9, r9
adox rbp, [ rsp + 0x30 ]
adox r14, [ rsp + 0x28 ]
mov [ rsp + 0x298 ], rdx
mov rdx, [ rsp + 0x270 ]
mov [ rsp + 0x2a0 ], r14
mov r14, rdx
adcx r14, [ rsp + 0x228 ]
mov [ rsp + 0x2a8 ], rbp
mov rbp, [ rsp + 0x268 ]
adcx rbp, [ rsp + 0x220 ]
test al, al
adox r14, r8
adox r10, rbp
adcx r14, rbx
adcx r15, r10
test al, al
adox r14, r11
adox r13, r15
mov rdx, [ rsp + 0x290 ]
mov r8, rdx
adcx r8, [ rsp + 0x2a8 ]
mov r11, [ rsp + 0x2a0 ]
adc r11, 0x0
mov rdx, [ rsi + 0x28 ]
mulx rbp, rbx, [ rax + 0x8 ]
mov rdx, r8
xor r10, r10
adox rdx, [ rsp + 0x1d8 ]
adox r11, r10
mov r9, rdx
shrd r9, r11, 56
mov r15, 0x38 
bzhi r8, rdx, r15
mov rdx, [ rax + 0x30 ]
mulx r10, r11, [ rsi + 0x0 ]
adox r14, r9
mov rdx, 0x0 
adox r13, rdx
mov rdx, [ rax + 0x18 ]
mulx r15, r9, [ rsi + 0x18 ]
mov rdx, r14
shrd rdx, r13, 56
mov r13, [ rsp + 0x20 ]
mov [ rsp + 0x2b0 ], r8
mov r8, r13
mov [ rsp + 0x2b8 ], rdx
xor rdx, rdx
adox r8, [ rsp + 0x238 ]
mov [ rsp + 0x2c0 ], r10
mov r10, [ rsp + 0x18 ]
adox r10, [ rsp + 0x230 ]
mov r13, 0x38 
bzhi rdx, r14, r13
adox r8, rbx
adox rbp, r10
xor rbx, rbx
adox r8, [ rsp + 0x288 ]
adox rbp, [ rsp + 0x280 ]
adcx r8, r9
adcx r15, rbp
mov r14, rdx
mov rdx, [ rsi + 0x8 ]
mulx r10, r9, [ rax + 0x28 ]
test al, al
adox r8, [ rsp + 0x70 ]
adox r15, [ rsp + 0x68 ]
adcx r8, r9
adcx r10, r15
xor rdx, rdx
adox r8, r11
adox r10, [ rsp + 0x2c0 ]
adcx r8, [ rsp + 0x2b8 ]
adc r10, 0x0
bzhi rbx, rdi, r13
mov rdi, [ rsp + 0x298 ]
add rdi, [ rsp + 0x278 ]
mov r11, r8
shrd r11, r10, 56
add r11, [ rsp + 0x1f8 ]
mov rbp, r11
shr rbp, 56
bzhi r9, r8, r13
bzhi r15, rdi, r13
mov r8, rbp
add r8, [ rsp + 0x2b0 ]
lea rbx, [ rbx + rbp ]
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x18 ], r15
bzhi rbp, rbx, r13
mov [ r10 + 0x0 ], rbp
shr rdi, 56
bzhi r15, r12, r13
lea rdi, [ rdi + r8 ]
bzhi r12, rdi, r13
shr rdi, 56
shr rbx, 56
bzhi r8, rcx, r13
mov [ r10 + 0x20 ], r12
lea rbx, [ rbx + r8 ]
mov [ r10 + 0x8 ], rbx
bzhi rcx, r11, r13
lea rdi, [ rdi + r14 ]
mov [ r10 + 0x28 ], rdi
mov [ r10 + 0x10 ], r15
mov [ r10 + 0x38 ], rcx
mov [ r10 + 0x30 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 840
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.2141
; seed 4049550137080074 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5415836 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=117, initial num_batches=31): 125133 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.02310502016678496
; number reverted permutation / tried permutation: 52777 / 90288 =58.454%
; number reverted decision / tried decision: 47285 / 89711 =52.708%
; validated in 2.904s
