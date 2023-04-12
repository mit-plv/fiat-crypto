SECTION .text
	GLOBAL fiat_p448_solinas_carry_mul
fiat_p448_solinas_carry_mul:
sub rsp, 800
mov rax, rdx
mov rdx, [ rdx + 0x30 ]
mulx r11, r10, [ rsi + 0x30 ]
mov rdx, [ rax + 0x8 ]
mulx r8, rcx, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x30 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x28 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x30 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], rbx
mov [ rsp - 0x40 ], r9
mulx r9, rbx, [ rax + 0x28 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x38 ], r9
mov [ rsp - 0x30 ], rbx
mulx rbx, r9, [ rsi + 0x38 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x28 ], rdi
mov [ rsp - 0x20 ], r15
mulx r15, rdi, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x18 ], r12
mov [ rsp - 0x10 ], rbp
mulx rbp, r12, [ rax + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x8 ], rbp
mov [ rsp + 0x0 ], r12
mulx r12, rbp, [ rax + 0x10 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x8 ], r12
mov [ rsp + 0x10 ], rbp
mulx rbp, r12, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x18 ], rbp
mov [ rsp + 0x20 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x28 ], r12
mov [ rsp + 0x30 ], rbp
mulx rbp, r12, [ rax + 0x18 ]
mov rdx, r13
mov [ rsp + 0x38 ], r15
xor r15, r15
adox rdx, r13
mov [ rsp + 0x40 ], rdi
mov rdi, r14
adox rdi, r14
mov r15, rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x48 ], r8
mov [ rsp + 0x50 ], rcx
mulx rcx, r8, [ rsi + 0x0 ]
adcx r15, r12
mov rdx, rbp
adcx rdx, rdi
mov rdi, r9
test al, al
adox rdi, r10
mov [ rsp + 0x58 ], rcx
mov rcx, r11
adox rcx, rbx
mov [ rsp + 0x60 ], r8
mov r8, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x68 ], r15
mov [ rsp + 0x70 ], rcx
mulx rcx, r15, [ rax + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x78 ], rcx
mov [ rsp + 0x80 ], r15
mulx r15, rcx, [ rax + 0x38 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x88 ], r8
mov [ rsp + 0x90 ], rdi
mulx rdi, r8, [ rsi + 0x18 ]
mov rdx, rcx
adcx rdx, [ rsp + 0x90 ]
mov [ rsp + 0x98 ], rdi
mov rdi, r15
adcx rdi, [ rsp + 0x70 ]
mov [ rsp + 0xa0 ], r8
mov r8, rdx
mov [ rsp + 0xa8 ], r15
xor r15, r15
adox r8, r9
adox rbx, rdi
adcx rdx, [ rsp + 0x50 ]
adcx rdi, [ rsp + 0x48 ]
add rdx, [ rsp + 0x40 ]
adcx rdi, [ rsp + 0x38 ]
mov r9, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0xb0 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
xor rdx, rdx
adox r8, r10
adox r11, rbx
mov rdx, [ rsi + 0x30 ]
mulx rbx, r10, [ rax + 0x38 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xb8 ], rdi
mov [ rsp + 0xc0 ], r15
mulx r15, rdi, [ rax + 0x30 ]
mov rdx, rdi
adcx rdx, r10
mov [ rsp + 0xc8 ], r11
mov r11, rbx
adcx r11, r15
mov [ rsp + 0xd0 ], r8
mov r8, rdx
test al, al
adox r8, rdi
adox r15, r11
adcx r8, r10
adcx rbx, r15
test al, al
adox r13, r12
adox rbp, r14
mov r14, rdx
mov rdx, [ rsi + 0x30 ]
mulx r10, r12, [ rax + 0x20 ]
adcx r13, r12
mov rdx, r10
adcx rdx, rbp
mov rdi, rdx
mov rdx, [ rsi + 0x28 ]
mulx rbp, r15, [ rax + 0x18 ]
mov rdx, r12
mov [ rsp + 0xd8 ], rbx
xor rbx, rbx
adox rdx, [ rsp + 0x68 ]
adox r10, [ rsp + 0x88 ]
adcx rdx, [ rsp - 0x10 ]
adcx r10, [ rsp - 0x18 ]
xor r12, r12
adox r9, r15
mov rbx, rbp
adox rbx, [ rsp + 0xb0 ]
mov [ rsp + 0xe0 ], r8
mov r8, rcx
adcx r8, [ rsp + 0xd0 ]
mov [ rsp + 0xe8 ], r10
mov r10, [ rsp + 0xa8 ]
adcx r10, [ rsp + 0xc8 ]
add r13, [ rsp - 0x10 ]
adcx rdi, [ rsp - 0x18 ]
test al, al
adox r8, [ rsp + 0x50 ]
adox r10, [ rsp + 0x48 ]
adcx r8, [ rsp + 0x40 ]
adcx r10, [ rsp + 0x38 ]
mov rcx, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xf0 ], rbx
mulx rbx, r12, [ rsi + 0x20 ]
xor rdx, rdx
adox r13, [ rsp - 0x20 ]
adox rdi, [ rsp - 0x28 ]
adcx r8, r15
adcx rbp, r10
test al, al
adox r8, r12
mov r15, rbx
adox r15, rbp
mov rdx, [ rsi + 0x10 ]
mulx rbp, r10, [ rax + 0x30 ]
adcx r9, r12
adcx rbx, [ rsp + 0xf0 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xf8 ], rdi
mulx rdi, r12, [ rax + 0x20 ]
test al, al
adox r9, [ rsp - 0x30 ]
adox rbx, [ rsp - 0x38 ]
adcx r12, [ rsp + 0x0 ]
adcx rdi, [ rsp - 0x8 ]
test al, al
adox r12, [ rsp + 0x20 ]
adox rdi, [ rsp + 0x18 ]
adcx r8, [ rsp - 0x30 ]
adcx r15, [ rsp - 0x38 ]
xor rdx, rdx
adox r8, r10
mov [ rsp + 0x100 ], r13
mov r13, rbp
adox r13, r15
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x108 ], rcx
mulx rcx, r15, [ rax + 0x38 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x110 ], rbx
mov [ rsp + 0x118 ], r9
mulx r9, rbx, [ rsi + 0x20 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x120 ], r9
mov [ rsp + 0x128 ], rbx
mulx rbx, r9, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x130 ], rbx
mov [ rsp + 0x138 ], r9
mulx r9, rbx, [ rax + 0x0 ]
adcx r8, r15
mov rdx, rcx
adcx rdx, r13
mov r13, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x140 ], r8
mov [ rsp + 0x148 ], r9
mulx r9, r8, [ rax + 0x38 ]
test al, al
adox r12, r8
adox r9, rdi
mov rdx, r12
adcx rdx, [ rsp + 0x138 ]
mov rdi, r9
adcx rdi, [ rsp + 0x130 ]
mov r8, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x150 ], r13
mov [ rsp + 0x158 ], rbx
mulx rbx, r13, [ rsi + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x160 ], rbx
mov [ rsp + 0x168 ], r13
mulx r13, rbx, [ rsi + 0x30 ]
xor rdx, rdx
adox r8, rbx
adox r13, rdi
mov rdx, [ rax + 0x30 ]
mulx rbx, rdi, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x170 ], rbx
mov [ rsp + 0x178 ], rdi
mulx rdi, rbx, [ rax + 0x10 ]
adcx r8, rbx
adcx rdi, r13
add r8, [ rsp + 0x128 ]
adcx rdi, [ rsp + 0x120 ]
mov rdx, [ rax + 0x10 ]
mulx rbx, r13, [ rsi + 0x38 ]
mov rdx, r10
mov [ rsp + 0x180 ], rbx
xor rbx, rbx
adox rdx, [ rsp + 0x118 ]
adox rbp, [ rsp + 0x110 ]
adcx r8, [ rsp + 0x168 ]
adcx rdi, [ rsp + 0x160 ]
mov r10, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x188 ], r13
mulx r13, rbx, [ rsi + 0x10 ]
mov rdx, [ rsp + 0x108 ]
add rdx, [ rsp - 0x20 ]
mov [ rsp + 0x190 ], rbp
mov rbp, [ rsp + 0xe8 ]
adcx rbp, [ rsp - 0x28 ]
add r8, rbx
adcx r13, rdi
mov rdi, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x198 ], rbp
mulx rbp, rbx, [ rax + 0x38 ]
xor rdx, rdx
adox r10, r15
adox rcx, [ rsp + 0x190 ]
adcx r8, [ rsp + 0x178 ]
adcx r13, [ rsp + 0x170 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x1a0 ], rcx
mulx rcx, r15, [ rax + 0x10 ]
xor rdx, rdx
adox r8, rbx
adox rbp, r13
mov rdx, [ rsi + 0x8 ]
mulx r13, rbx, [ rax + 0x18 ]
mov rdx, [ rsp + 0x158 ]
mov [ rsp + 0x1a8 ], r10
mov r10, rdx
adcx r10, [ rsp + 0x140 ]
mov [ rsp + 0x1b0 ], rdi
mov rdi, [ rsp + 0x148 ]
adcx rdi, [ rsp + 0x150 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x1b8 ], r13
mov [ rsp + 0x1c0 ], rbx
mulx rbx, r13, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1c8 ], rcx
mov [ rsp + 0x1d0 ], r15
mulx r15, rcx, [ rax + 0x38 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1d8 ], r15
mov [ rsp + 0x1e0 ], rcx
mulx rcx, r15, [ rax + 0x8 ]
test al, al
adox r10, r15
adox rcx, rdi
mov rdx, [ rax + 0x8 ]
mulx r15, rdi, [ rsi + 0x10 ]
adcx r12, r13
adcx rbx, r9
mov rdx, [ rsi + 0x20 ]
mulx r13, r9, [ rax + 0x28 ]
test al, al
adox r12, rdi
adox r15, rbx
mov rdx, [ rsi + 0x0 ]
mulx rbx, rdi, [ rax + 0x18 ]
adcx r12, [ rsp + 0x10 ]
adcx r15, [ rsp + 0x8 ]
xor rdx, rdx
adox r14, [ rsp + 0x188 ]
adox r11, [ rsp + 0x180 ]
adcx r12, rdi
adcx rbx, r15
mov rdi, r12
shrd rdi, rbx, 56
mov r15, 0xffffffffffffff 
mov rbx, r8
and rbx, r15
and r12, r15
adox r10, [ rsp + 0x1d0 ]
adox rcx, [ rsp + 0x1c8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x1e8 ], r12
mulx r12, r15, [ rsi + 0x30 ]
adcx r10, [ rsp + 0x1c0 ]
adcx rcx, [ rsp + 0x1b8 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x1f0 ], rbx
mov [ rsp + 0x1f8 ], rdi
mulx rdi, rbx, [ rsi + 0x28 ]
xor rdx, rdx
adox r14, r15
mov [ rsp + 0x200 ], rcx
mov rcx, r12
adox rcx, r11
adcx r14, rbx
mov r11, rdi
adcx r11, rcx
mov rcx, [ rsp + 0xe0 ]
test al, al
adox rcx, [ rsp + 0x188 ]
mov [ rsp + 0x208 ], r10
mov r10, [ rsp + 0xd8 ]
adox r10, [ rsp + 0x180 ]
adcx r14, r9
mov [ rsp + 0x210 ], r10
mov r10, r13
adcx r10, r11
test al, al
adox r14, [ rsp - 0x40 ]
adox r10, [ rsp - 0x48 ]
adcx rcx, r15
adcx r12, [ rsp + 0x210 ]
test al, al
adox rcx, rbx
adox rdi, r12
mov rdx, [ rsi + 0x0 ]
mulx rbx, r15, [ rax + 0x20 ]
adcx rcx, r9
adcx r13, rdi
mov rdx, r15
xor r9, r9
adox rdx, [ rsp + 0x208 ]
adox rbx, [ rsp + 0x200 ]
mov r11, rdx
mov rdx, [ rsi + 0x10 ]
mulx rdi, r12, [ rax + 0x38 ]
mov rdx, [ rsi + 0x30 ]
mulx r9, r15, [ rax + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x218 ], r9
mov [ rsp + 0x220 ], r15
mulx r15, r9, [ rax + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x228 ], r15
mov [ rsp + 0x230 ], r9
mulx r9, r15, [ rax + 0x0 ]
shrd r8, rbp, 56
test al, al
adox r14, r12
mov rdx, rdi
adox rdx, r10
adcx rcx, [ rsp - 0x40 ]
adcx r13, [ rsp - 0x48 ]
mov rbp, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x238 ], r14
mulx r14, r10, [ rax + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x240 ], rbp
mov [ rsp + 0x248 ], r14
mulx r14, rbp, [ rax + 0x20 ]
test al, al
adox rcx, r12
adox rdi, r13
mov rdx, [ rax + 0x10 ]
mulx r13, r12, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x250 ], r14
mov [ rsp + 0x258 ], rbp
mulx rbp, r14, [ rax + 0x8 ]
adcx rcx, r15
adcx r9, rdi
xor rdx, rdx
adox r11, [ rsp + 0x1f8 ]
adox rbx, rdx
adcx rcx, r14
adcx rbp, r9
mov r15, r8
add r15, r11
adc rbx, 0x0
mov rdx, [ rsi + 0x8 ]
mulx r14, rdi, [ rax + 0x20 ]
mov rdx, [ rsp + 0x1b0 ]
test al, al
adox rdx, [ rsp + 0x1e0 ]
mov r9, [ rsp + 0x198 ]
adox r9, [ rsp + 0x1d8 ]
mov r11, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x260 ], rbx
mov [ rsp + 0x268 ], r15
mulx r15, rbx, [ rsi + 0x0 ]
adcx r11, [ rsp + 0x220 ]
adcx r9, [ rsp + 0x218 ]
mov rdx, rbx
add rdx, [ rsp + 0x1a8 ]
adcx r15, [ rsp + 0x1a0 ]
test al, al
adox r11, [ rsp + 0x230 ]
adox r9, [ rsp + 0x228 ]
adcx r11, r12
adcx r13, r9
mov r12, [ rsp + 0x100 ]
add r12, [ rsp + 0x1e0 ]
mov rbx, [ rsp + 0xf8 ]
adcx rbx, [ rsp + 0x1d8 ]
xor r9, r9
adox rcx, [ rsp + 0xa0 ]
adox rbp, [ rsp + 0x98 ]
adcx rcx, r10
adcx rbp, [ rsp + 0x248 ]
mov r10, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x270 ], r15
mulx r15, r9, [ rax + 0x28 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x278 ], r10
mov [ rsp + 0x280 ], rbx
mulx rbx, r10, [ rsi + 0x8 ]
test al, al
adox rcx, rdi
adox r14, rbp
mov rdx, [ rsi + 0x8 ]
mulx rbp, rdi, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x288 ], rbp
mov [ rsp + 0x290 ], rdi
mulx rdi, rbp, [ rsi + 0x10 ]
adcx rcx, r9
adcx r15, r14
mov rdx, r10
xor r9, r9
adox rdx, [ rsp + 0x238 ]
adox rbx, [ rsp + 0x240 ]
adcx r11, [ rsp + 0xc0 ]
adcx r13, [ rsp + 0xb8 ]
mov r10, [ rsp + 0x268 ]
mov r14, [ rsp + 0x260 ]
mov r9, r10
shrd r9, r14, 56
add r12, rbp
adcx rdi, [ rsp + 0x280 ]
xor r14, r14
adox rcx, r9
adox r15, r14
adcx r11, [ rsp + 0x258 ]
adcx r13, [ rsp + 0x250 ]
mov rbp, rcx
shrd rbp, r15, 56
xor r9, r9
adox r11, [ rsp + 0x80 ]
adox r13, [ rsp + 0x78 ]
adcx r11, [ rsp + 0x60 ]
adcx r13, [ rsp + 0x58 ]
xor r14, r14
adox r11, rbp
adox r13, r14
adcx r12, [ rsp + 0x290 ]
adcx rdi, [ rsp + 0x288 ]
mov r9, rdx
mov rdx, [ rsi + 0x0 ]
mulx rbp, r15, [ rax + 0x10 ]
mov rdx, r11
shrd rdx, r13, 56
mov r14, 0x38 
mov [ rsp + 0x298 ], rbx
bzhi rbx, r11, r14
add rdx, [ rsp + 0x1f0 ]
xor r11, r11
adox r8, [ rsp + 0x278 ]
mov r13, [ rsp + 0x270 ]
adox r13, r11
adcx r12, r15
adcx rbp, rdi
mov rdi, rdx
shr rdi, 56
bzhi r15, r10, r14
adox r9, [ rsp + 0x30 ]
mov r10, [ rsp + 0x298 ]
adox r10, [ rsp + 0x28 ]
bzhi r11, rdx, r14
mov rdx, r8
shrd rdx, r13, 56
xor r13, r13
adox r9, rdx
adox r10, r13
mov rdx, r9
shrd rdx, r10, 56
add r12, rdx
adc rbp, 0x0
bzhi rdx, r9, r14
bzhi r9, r8, r14
lea r9, [ r9 + rdi ]
mov r8, r12
shrd r8, rbp, 56
add r8, [ rsp + 0x1e8 ]
lea r15, [ r15 + rdi ]
bzhi rdi, r12, r14
mov r10, r8
shr r10, 56
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x10 ], rdi
lea r10, [ r10 + r15 ]
bzhi rbp, r10, r14
shr r10, 56
bzhi r15, r9, r14
bzhi rdi, r8, r14
shr r9, 56
bzhi r8, rcx, r14
mov [ r12 + 0x30 ], rbx
lea r9, [ r9 + rdx ]
lea r10, [ r10 + r8 ]
mov [ r12 + 0x8 ], r9
mov [ r12 + 0x28 ], r10
mov [ r12 + 0x0 ], r15
mov [ r12 + 0x20 ], rbp
mov [ r12 + 0x18 ], rdi
mov [ r12 + 0x38 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 800
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.1936
; seed 2427683618540499 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5433686 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=107, initial num_batches=31): 127699 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.02350135801001383
; number reverted permutation / tried permutation: 55971 / 89990 =62.197%
; number reverted decision / tried decision: 48884 / 90009 =54.310%
; validated in 3.325s
