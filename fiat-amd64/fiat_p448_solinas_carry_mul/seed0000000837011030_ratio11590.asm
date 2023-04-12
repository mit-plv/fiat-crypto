SECTION .text
	GLOBAL fiat_p448_solinas_carry_mul
fiat_p448_solinas_carry_mul:
sub rsp, 824
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x38 ]
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x38 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x18 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], r11
mov [ rsp - 0x40 ], r10
mulx r10, r11, [ rax + 0x10 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x38 ], r10
mov [ rsp - 0x30 ], r11
mulx r11, r10, [ rsi + 0x28 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x28 ], rbx
mov [ rsp - 0x20 ], r9
mulx r9, rbx, [ rsi + 0x28 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x18 ], rdi
mov [ rsp - 0x10 ], r15
mulx r15, rdi, [ rsi + 0x30 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x8 ], r8
mov [ rsp + 0x0 ], rcx
mulx rcx, r8, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x8 ], rcx
mov [ rsp + 0x10 ], r8
mulx r8, rcx, [ rax + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x18 ], r9
mov [ rsp + 0x20 ], rbx
mulx rbx, r9, [ rax + 0x20 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x28 ], rbx
mov [ rsp + 0x30 ], r9
mulx r9, rbx, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x38 ], r9
mov [ rsp + 0x40 ], rbx
mulx rbx, r9, [ rax + 0x30 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x48 ], r12
mov [ rsp + 0x50 ], rbp
mulx rbp, r12, [ rsi + 0x28 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x58 ], rbp
mov [ rsp + 0x60 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x68 ], r12
mov [ rsp + 0x70 ], rbp
mulx rbp, r12, [ rax + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x78 ], rbp
mov [ rsp + 0x80 ], r12
mulx r12, rbp, [ rax + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x88 ], r12
mov [ rsp + 0x90 ], rbp
mulx rbp, r12, [ rax + 0x38 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x98 ], rbp
mov [ rsp + 0xa0 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0xa8 ], r12
mov [ rsp + 0xb0 ], rbp
mulx rbp, r12, [ rsi + 0x20 ]
mov rdx, r9
add rdx, rdi
mov [ rsp + 0xb8 ], rbp
mov rbp, r15
adcx rbp, rbx
mov [ rsp + 0xc0 ], r12
mov r12, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xc8 ], r11
mov [ rsp + 0xd0 ], r10
mulx r10, r11, [ rax + 0x20 ]
mov rdx, r12
add rdx, rcx
mov [ rsp + 0xd8 ], r10
mov r10, r8
adcx r10, rbp
mov [ rsp + 0xe0 ], r11
mov r11, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xe8 ], r10
mov [ rsp + 0xf0 ], r14
mulx r14, r10, [ rax + 0x10 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xf8 ], r14
mov [ rsp + 0x100 ], r10
mulx r10, r14, [ rax + 0x38 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x108 ], r10
mov [ rsp + 0x110 ], r14
mulx r14, r10, [ rax + 0x28 ]
xor rdx, rdx
adox r11, r13
mov [ rsp + 0x118 ], r14
mov r14, [ rsp + 0xe8 ]
adox r14, [ rsp + 0xf0 ]
adcx r11, [ rsp + 0xd0 ]
adcx r14, [ rsp + 0xc8 ]
mov [ rsp + 0x120 ], r13
xor r13, r13
adox r11, r10
adox r14, [ rsp + 0x118 ]
mov rdx, [ rsp + 0x110 ]
mov [ rsp + 0x128 ], r14
mov r14, rdx
adcx r14, rdx
mov [ rsp + 0x130 ], r11
mov r11, [ rsp + 0x108 ]
mov [ rsp + 0x138 ], r10
mov r10, r11
adcx r10, r11
test al, al
adox r12, r9
adox rbx, rbp
adcx r12, rdi
adcx r15, rbx
mov rdi, rdx
mov rdx, [ rsi + 0x38 ]
mulx rbp, r9, [ rax + 0x28 ]
mov rdx, r9
add rdx, [ rsp + 0x50 ]
mov rbx, rbp
adcx rbx, [ rsp + 0x48 ]
mov [ rsp + 0x140 ], r10
xor r10, r10
adox r12, rcx
adox r8, r15
adcx rdx, [ rsp + 0x20 ]
adcx rbx, [ rsp + 0x18 ]
mov r13, rdx
add r13, r9
adcx rbp, rbx
add r13, [ rsp + 0x50 ]
adcx rbp, [ rsp + 0x48 ]
add r13, [ rsp + 0x20 ]
adcx rbp, [ rsp + 0x18 ]
test al, al
adox r13, [ rsp + 0x0 ]
adox rbp, [ rsp - 0x8 ]
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mulx r9, r15, [ rax + 0x30 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x148 ], r9
mulx r9, r10, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x150 ], r15
mov [ rsp + 0x158 ], r8
mulx r8, r15, [ rax + 0x20 ]
adcx rcx, [ rsp + 0x0 ]
adcx rbx, [ rsp - 0x8 ]
xor rdx, rdx
adox rcx, [ rsp + 0x40 ]
adox rbx, [ rsp + 0x38 ]
adcx r13, [ rsp + 0x40 ]
adcx rbp, [ rsp + 0x38 ]
mov [ rsp + 0x160 ], r12
xor r12, r12
adox rdi, [ rsp + 0x10 ]
adox r11, [ rsp + 0x8 ]
adcx r13, r10
mov rdx, r9
adcx rdx, rbp
add r13, r15
mov rbp, r8
adcx rbp, rdx
xor rdx, rdx
adox rcx, r10
adox r9, rbx
adcx rcx, r15
adcx r8, r9
mov rdx, [ rsi + 0x38 ]
mulx r10, r12, [ rax + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mulx rbx, r15, [ rax + 0x30 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x168 ], rbx
mulx rbx, r9, [ rax + 0x30 ]
xor rdx, rdx
adox r14, [ rsp + 0x10 ]
mov [ rsp + 0x170 ], r15
mov r15, [ rsp + 0x140 ]
adox r15, [ rsp + 0x8 ]
adcx r12, [ rsp - 0x10 ]
adcx r10, [ rsp - 0x18 ]
add r14, [ rsp + 0x80 ]
adcx r15, [ rsp + 0x78 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x178 ], r15
mov [ rsp + 0x180 ], r14
mulx r14, r15, [ rsi + 0x18 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x188 ], r10
mov [ rsp + 0x190 ], r12
mulx r12, r10, [ rsi + 0x28 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x198 ], rbx
mov [ rsp + 0x1a0 ], r9
mulx r9, rbx, [ rsi + 0x30 ]
add rcx, r15
mov rdx, r14
adcx rdx, r8
mov r8, rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x1a8 ], rcx
mov [ rsp + 0x1b0 ], r9
mulx r9, rcx, [ rsi + 0x28 ]
test al, al
adox rdi, [ rsp + 0x80 ]
adox r11, [ rsp + 0x78 ]
adcx rdi, r10
mov rdx, r12
adcx rdx, r11
mov r11, [ rsp + 0x160 ]
test al, al
adox r11, [ rsp + 0x120 ]
mov [ rsp + 0x1b8 ], rdx
mov rdx, [ rsp + 0x158 ]
adox rdx, [ rsp + 0xf0 ]
adcx r13, r15
adcx r14, rbp
mov rbp, [ rsp + 0x1a0 ]
mov r15, rbp
test al, al
adox r15, [ rsp + 0x130 ]
mov [ rsp + 0x1c0 ], rdi
mov rdi, [ rsp + 0x198 ]
mov [ rsp + 0x1c8 ], r14
mov r14, rdi
adox r14, [ rsp + 0x128 ]
mov [ rsp + 0x1d0 ], r14
mov r14, rcx
adcx r14, [ rsp + 0x190 ]
adcx r9, [ rsp + 0x188 ]
mov rcx, rdx
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x1d8 ], r15
mov [ rsp + 0x1e0 ], r13
mulx r13, r15, [ rsi + 0x20 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x1e8 ], r8
mov [ rsp + 0x1f0 ], rcx
mulx rcx, r8, [ rsi + 0x38 ]
test al, al
adox r14, r15
adox r13, r9
mov rdx, r14
adcx rdx, r8
adcx rcx, r13
xor r9, r9
adox rdx, rbx
adox rcx, [ rsp + 0x1b0 ]
adcx r11, [ rsp + 0xd0 ]
mov rbx, [ rsp + 0x1f0 ]
adcx rbx, [ rsp + 0xc8 ]
mov r15, rdx
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rax + 0x18 ]
mov rdx, r10
test al, al
adox rdx, [ rsp + 0x180 ]
adox r12, [ rsp + 0x178 ]
adcx rdx, [ rsp + 0xc0 ]
adcx r12, [ rsp + 0xb8 ]
xor r10, r10
adox rdx, [ rsp + 0xa0 ]
adox r12, [ rsp + 0x98 ]
mov r10, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1f8 ], r9
mov [ rsp + 0x200 ], r8
mulx r8, r9, [ rax + 0x20 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x208 ], r8
mov [ rsp + 0x210 ], r9
mulx r9, r8, [ rsi + 0x28 ]
adcx r15, r8
adcx r9, rcx
mov rdx, [ rsi + 0x28 ]
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x218 ], rbx
mov [ rsp + 0x220 ], r11
mulx r11, rbx, [ rax + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x228 ], r11
mov [ rsp + 0x230 ], rbx
mulx rbx, r11, [ rax + 0x18 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x238 ], r8
mov [ rsp + 0x240 ], rcx
mulx rcx, r8, [ rax + 0x0 ]
xor rdx, rdx
adox r10, r8
adox rcx, r12
adcx r15, r11
adcx rbx, r9
add r10, [ rsp + 0x240 ]
adcx rcx, [ rsp + 0x238 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, r12, [ rax + 0x0 ]
xor rdx, rdx
adox r14, r12
adox r9, r13
adcx r14, [ rsp + 0x230 ]
adcx r9, [ rsp + 0x228 ]
mov r13, [ rsp + 0x138 ]
mov r11, r13
add r11, [ rsp + 0x220 ]
mov r8, [ rsp + 0x118 ]
adcx r8, [ rsp + 0x218 ]
mov rdx, [ rsi + 0x10 ]
mulx r12, r13, [ rax + 0x28 ]
add r11, rbp
adcx rdi, r8
mov rdx, [ rsp + 0x170 ]
mov rbp, rdx
test al, al
adox rbp, [ rsp + 0x1a8 ]
mov r8, [ rsp + 0x168 ]
mov [ rsp + 0x248 ], r12
mov r12, r8
adox r12, [ rsp + 0x1e8 ]
adcx r11, [ rsp - 0x20 ]
adcx rdi, [ rsp - 0x28 ]
test al, al
adox r11, [ rsp + 0x60 ]
adox rdi, [ rsp + 0x58 ]
adcx r10, [ rsp + 0x100 ]
adcx rcx, [ rsp + 0xf8 ]
mov [ rsp + 0x250 ], rcx
xor rcx, rcx
adox r14, [ rsp - 0x30 ]
adox r9, [ rsp - 0x38 ]
mov rcx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x258 ], r10
mov [ rsp + 0x260 ], r12
mulx r12, r10, [ rax + 0x10 ]
adcx r14, [ rsp + 0x200 ]
adcx r9, [ rsp + 0x1f8 ]
test al, al
adox r15, [ rsp + 0x210 ]
adox rbx, [ rsp + 0x208 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x268 ], r9
mov [ rsp + 0x270 ], r14
mulx r14, r9, [ rsi + 0x20 ]
adcx r11, r9
adcx r14, rdi
mov rdx, [ rsi + 0x0 ]
mulx r9, rdi, [ rax + 0x38 ]
test al, al
adox r15, r13
adox rbx, [ rsp + 0x248 ]
mov rdx, rcx
adcx rdx, [ rsp + 0x1e0 ]
adcx r8, [ rsp + 0x1c8 ]
mov rcx, rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x278 ], rbp
mulx rbp, r13, [ rsi + 0x8 ]
xor rdx, rdx
adox r15, r13
adox rbp, rbx
mov rbx, [ rsp + 0xc0 ]
mov r13, rbx
adcx r13, [ rsp + 0x1c0 ]
mov [ rsp + 0x280 ], r8
mov r8, [ rsp + 0xb8 ]
adcx r8, [ rsp + 0x1b8 ]
xor rbx, rbx
adox r15, rdi
adox r9, rbp
mov rdx, [ rsi + 0x10 ]
mulx rbp, rdi, [ rax + 0x0 ]
adcx r13, [ rsp + 0xa0 ]
adcx r8, [ rsp + 0x98 ]
test al, al
adox r11, r10
adox r12, r14
adcx r13, rdi
adcx rbp, r8
mov rdx, [ rsi + 0x8 ]
mulx r14, r10, [ rax + 0x38 ]
xor rdx, rdx
adox rcx, r10
mov rbx, r14
adox rbx, [ rsp + 0x280 ]
adcx rcx, [ rsp - 0x40 ]
adcx rbx, [ rsp - 0x48 ]
test al, al
adox rcx, [ rsp + 0x70 ]
adox rbx, [ rsp + 0x68 ]
mov rdx, [ rax + 0x8 ]
mulx r8, rdi, [ rsi + 0x8 ]
mov rdx, r10
adcx rdx, [ rsp + 0x278 ]
adcx r14, [ rsp + 0x260 ]
mov r10, [ rsp - 0x20 ]
mov [ rsp + 0x288 ], rbx
mov rbx, r10
mov [ rsp + 0x290 ], rcx
xor rcx, rcx
adox rbx, [ rsp + 0x1d8 ]
mov [ rsp + 0x298 ], r14
mov r14, [ rsp - 0x28 ]
adox r14, [ rsp + 0x1d0 ]
adcx r13, rdi
adcx r8, rbp
mov r10, rdx
mov rdx, [ rax + 0x18 ]
mulx rdi, rbp, [ rsi + 0x10 ]
mov rdx, r15
shrd rdx, r9, 56
mov r9, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x2a0 ], r8
mulx r8, rcx, [ rsi + 0x0 ]
test al, al
adox r11, rbp
adox rdi, r12
adcx r10, rcx
adcx r8, [ rsp + 0x298 ]
mov rdx, r9
add rdx, r10
adc r8, 0x0
mov r12, rdx
mov rdx, [ rsi + 0x8 ]
mulx rcx, rbp, [ rax + 0x0 ]
add rbx, rbp
adcx rcx, r14
mov rdx, r12
shrd rdx, r8, 56
mov r14, 0x38 
bzhi r10, r15, r14
mov r15, rdx
mov rdx, [ rsi + 0x10 ]
mulx rbp, r8, [ rax + 0x10 ]
adox rbx, [ rsp + 0xb0 ]
adox rcx, [ rsp + 0xa8 ]
xor rdx, rdx
adox rbx, r15
adox rcx, rdx
mov rdx, [ rax + 0x10 ]
mulx r14, r15, [ rsi + 0x0 ]
mov rdx, rbx
shrd rdx, rcx, 56
xor rcx, rcx
adox r13, r15
adox r14, [ rsp + 0x2a0 ]
adcx r13, rdx
adc r14, 0x0
mov r15, r13
shrd r15, r14, 56
mov rdx, r8
xor r14, r14
adox rdx, [ rsp + 0x290 ]
adox rbp, [ rsp + 0x288 ]
adcx rdx, [ rsp + 0x90 ]
adcx rbp, [ rsp + 0x88 ]
mov rcx, 0xffffffffffffff 
and r13, rcx
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x10 ], r13
mov r13, [ rsp + 0x270 ]
and r13, rcx
lea r15, [ r15 + r13 ]
mov r13, r15
and r13, rcx
mov [ r8 + 0x18 ], r13
and rbx, rcx
adox rdx, [ rsp + 0xe0 ]
adox rbp, [ rsp + 0xd8 ]
mov r13, [ rsp + 0x270 ]
mov r14, [ rsp + 0x268 ]
shrd r13, r14, 56
test al, al
adox rdx, r13
mov r14, 0x0 
adox rbp, r14
adcx r9, rdx
adc rbp, 0x0
mov r13, r9
and r13, rcx
shrd r9, rbp, 56
mov rdx, [ rsi + 0x8 ]
mulx r14, rbp, [ rax + 0x20 ]
shr r15, 56
mov rdx, [ rax + 0x28 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x2a8 ], rbx
mov [ rsp + 0x2b0 ], r15
mulx r15, rbx, [ rsi + 0x8 ]
add r11, rbp
adcx r14, rdi
xor rdx, rdx
adox r11, rcx
adox r8, r14
adcx r11, r9
adc r8, 0x0
mov rdi, r11
shrd rdi, r8, 56
mov rdx, [ rsi + 0x18 ]
mulx rbp, r9, [ rax + 0x18 ]
mov rdx, 0x38 
bzhi rcx, r11, rdx
mov r14, r9
adox r14, [ rsp + 0x258 ]
adox rbp, [ rsp + 0x250 ]
xor r11, r11
adox r14, [ rsp + 0x30 ]
adox rbp, [ rsp + 0x28 ]
adcx r14, rbx
adcx r15, rbp
bzhi rbx, r12, rdx
adox r14, [ rsp + 0x150 ]
adox r15, [ rsp + 0x148 ]
xor r12, r12
adox r14, rdi
adox r15, r12
mov r11, r14
shrd r11, r15, 56
lea r11, [ r11 + r10 ]
mov r10, r11
shr r10, 56
lea rbx, [ rbx + r10 ]
lea r13, [ r13 + r10 ]
bzhi r8, rbx, rdx
add r13, [ rsp + 0x2b0 ]
shr rbx, 56
mov rdi, r13
shr rdi, 56
bzhi r9, r11, rdx
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x38 ], r9
bzhi r11, r14, rdx
mov [ rbp + 0x0 ], r8
bzhi r14, r13, rdx
mov [ rbp + 0x20 ], r14
add rbx, [ rsp + 0x2a8 ]
lea rdi, [ rdi + rcx ]
mov [ rbp + 0x30 ], r11
mov [ rbp + 0x8 ], rbx
mov [ rbp + 0x28 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 824
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.1590
; seed 2082129117669951 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5510636 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=109, initial num_batches=31): 127784 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.02318861198598492
; number reverted permutation / tried permutation: 55758 / 90322 =61.732%
; number reverted decision / tried decision: 48697 / 89677 =54.303%
; validated in 3.217s
