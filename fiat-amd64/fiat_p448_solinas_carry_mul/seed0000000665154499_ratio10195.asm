SECTION .text
	GLOBAL fiat_p448_solinas_carry_mul
fiat_p448_solinas_carry_mul:
sub rsp, 608
mov rax, rdx
mov rdx, [ rsi + 0x30 ]
mulx r11, r10, [ rax + 0x38 ]
mov rdx, [ rax + 0x38 ]
mulx r8, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x30 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x38 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x30 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x48 ], r8
mov [ rsp - 0x40 ], rcx
mulx rcx, r8, [ rsi + 0x28 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x38 ], rcx
mov [ rsp - 0x30 ], r8
mulx r8, rcx, [ rsi + 0x8 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x28 ], r8
mov [ rsp - 0x20 ], rcx
mulx rcx, r8, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x18 ], rdi
mov [ rsp - 0x10 ], r15
mulx r15, rdi, [ rax + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x8 ], rcx
mov [ rsp + 0x0 ], r8
mulx r8, rcx, [ rax + 0x0 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x8 ], r8
mov [ rsp + 0x10 ], rcx
mulx rcx, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x18 ], rcx
mov [ rsp + 0x20 ], r8
mulx r8, rcx, [ rax + 0x28 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x28 ], r8
mov [ rsp + 0x30 ], rcx
mulx rcx, r8, [ rsi + 0x10 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x38 ], rcx
mov [ rsp + 0x40 ], r8
mulx r8, rcx, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x48 ], r14
mov [ rsp + 0x50 ], r13
mulx r13, r14, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x58 ], rbx
mov [ rsp + 0x60 ], r9
mulx r9, rbx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x68 ], r9
mov [ rsp + 0x70 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
mov rdx, rcx
mov [ rsp + 0x78 ], rbx
xor rbx, rbx
adox rdx, rcx
mov [ rsp + 0x80 ], r9
mov r9, r8
adox r9, r8
adcx rdx, r14
mov [ rsp + 0x88 ], r15
mov r15, r13
adcx r15, r9
mov r9, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x90 ], r15
mulx r15, rbx, [ rax + 0x10 ]
mov rdx, rbp
mov [ rsp + 0x98 ], r9
xor r9, r9
adox rdx, r10
mov [ rsp + 0xa0 ], rdi
mov rdi, r11
adox rdi, r12
adcx rcx, r14
adcx r13, r8
mov r8, rdx
test al, al
adox r8, rbx
mov r14, r15
adox r14, rdi
adcx rdx, rbp
adcx r12, rdi
test al, al
adox rdx, r10
adox r11, r12
mov r10, rdx
mov rdx, [ rsi + 0x30 ]
mulx rdi, rbp, [ rax + 0x18 ]
adcx rcx, [ rsp + 0xa0 ]
adcx r13, [ rsp + 0x88 ]
mov rdx, [ rsi + 0x30 ]
mulx r9, r12, [ rax + 0x30 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xa8 ], r13
mov [ rsp + 0xb0 ], rcx
mulx rcx, r13, [ rax + 0x38 ]
xor rdx, rdx
adox r10, rbx
adox r15, r11
mov rdx, [ rsi + 0x38 ]
mulx r11, rbx, [ rax + 0x28 ]
adcx r10, rbp
mov rdx, rdi
adcx rdx, r15
mov r15, rbx
test al, al
adox r15, r12
mov [ rsp + 0xb8 ], rdx
mov rdx, r9
adox rdx, r11
adcx r15, r13
mov [ rsp + 0xc0 ], r10
mov r10, rcx
adcx r10, rdx
mov rdx, r15
test al, al
adox rdx, rbx
adox r11, r10
adcx r8, rbp
adcx rdi, r14
mov r14, rdx
mov rdx, [ rax + 0x10 ]
mulx rbx, rbp, [ rsi + 0x30 ]
xor rdx, rdx
adox r14, r12
adox r9, r11
mov rdx, [ rax + 0x8 ]
mulx r11, r12, [ rsi + 0x38 ]
adcx r15, r12
mov rdx, r11
adcx rdx, r10
mov r10, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xc8 ], rdi
mov [ rsp + 0xd0 ], r8
mulx r8, rdi, [ rax + 0x20 ]
test al, al
adox r14, r13
adox rcx, r9
adcx r14, r12
adcx r11, rcx
xor rdx, rdx
adox r15, rbp
mov r13, rbx
adox r13, r10
mov rdx, [ rsi + 0x30 ]
mulx r12, r9, [ rax + 0x28 ]
adcx r14, rbp
adcx rbx, r11
add rdi, r9
adcx r12, r8
xor rdx, rdx
adox rdi, [ rsp + 0x60 ]
adox r12, [ rsp + 0x58 ]
adcx rdi, [ rsp + 0x50 ]
adcx r12, [ rsp + 0x48 ]
mov rbp, rdi
test al, al
adox rbp, [ rsp + 0x10 ]
mov r10, r12
adox r10, [ rsp + 0x8 ]
mov rdx, [ rax + 0x0 ]
mulx rcx, r8, [ rsi + 0x38 ]
adcx rdi, r8
adcx rcx, r12
mov rdx, [ rax + 0x8 ]
mulx r9, r11, [ rsi + 0x30 ]
xor rdx, rdx
adox rdi, r11
adox r9, rcx
mov r12, [ rsp + 0xb0 ]
adcx r12, [ rsp + 0x0 ]
mov r8, [ rsp + 0xa8 ]
adcx r8, [ rsp - 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx r11, rcx, [ rax + 0x8 ]
add rbp, rcx
adcx r11, r10
mov rdx, [ rax + 0x18 ]
mulx rcx, r10, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xd8 ], r9
mov [ rsp + 0xe0 ], rdi
mulx rdi, r9, [ rax + 0x10 ]
test al, al
adox r12, [ rsp - 0x10 ]
adox r8, [ rsp - 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xe8 ], r8
mov [ rsp + 0xf0 ], r12
mulx r12, r8, [ rsi + 0x28 ]
adcx r15, r10
mov rdx, rcx
adcx rdx, r13
mov r13, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xf8 ], r12
mov [ rsp + 0x100 ], r8
mulx r8, r12, [ rsi + 0x20 ]
add r15, r12
mov rdx, r8
adcx rdx, r13
xor r13, r13
adox rbp, r9
adox rdi, r11
mov r11, rdx
mov rdx, [ rax + 0x28 ]
mulx r13, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x108 ], r11
mov [ rsp + 0x110 ], r15
mulx r15, r11, [ rax + 0x18 ]
adcx r14, r10
adcx rcx, rbx
add rbp, r11
adcx r15, rdi
mov rdx, [ rsp + 0xc0 ]
add rdx, [ rsp + 0x100 ]
mov rbx, [ rsp + 0xb8 ]
adcx rbx, [ rsp + 0xf8 ]
test al, al
adox rdx, [ rsp + 0x30 ]
adox rbx, [ rsp + 0x28 ]
adcx r14, r12
adcx r8, rcx
test al, al
adox r14, r9
mov r10, r13
adox r10, r8
mov r12, rbp
shrd r12, r15, 56
mov rdi, r9
xor r11, r11
adox rdi, [ rsp + 0x110 ]
adox r13, [ rsp + 0x108 ]
mov r9, rdx
mov rdx, [ rax + 0x30 ]
mulx r15, rcx, [ rsi + 0x10 ]
adcx r9, [ rsp + 0x20 ]
adcx rbx, [ rsp + 0x18 ]
xor rdx, rdx
adox rdi, rcx
mov r11, r15
adox r11, r13
adcx r14, rcx
adcx r15, r10
test al, al
adox rdi, [ rsp - 0x40 ]
adox r11, [ rsp - 0x48 ]
mov rdx, [ rax + 0x0 ]
mulx r10, r8, [ rsi + 0x0 ]
mov rdx, [ rax + 0x30 ]
mulx rcx, r13, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x118 ], r12
mov [ rsp + 0x120 ], rbx
mulx rbx, r12, [ rax + 0x18 ]
adcx rdi, r8
adcx r10, r11
mov rdx, 0x38 
bzhi r11, rbp, rdx
mov rdx, [ rax + 0x10 ]
mulx r8, rbp, [ rsi + 0x28 ]
mov rdx, rbp
adox rdx, [ rsp + 0xe0 ]
adox r8, [ rsp + 0xd8 ]
mov rbp, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x128 ], r11
mov [ rsp + 0x130 ], r9
mulx r9, r11, [ rsi + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x138 ], r15
mov [ rsp + 0x140 ], r14
mulx r14, r15, [ rsi + 0x20 ]
xor rdx, rdx
adox rbp, r12
adox rbx, r8
mov rdx, [ rsi + 0x10 ]
mulx r8, r12, [ rax + 0x28 ]
adcx rbp, r11
adcx r9, rbx
test al, al
adox rbp, r12
adox r8, r9
mov rdx, [ rax + 0x38 ]
mulx rbx, r11, [ rsi + 0x0 ]
adcx rbp, r13
adcx rcx, r8
add rbp, r11
adcx rbx, rcx
mov rdx, [ rsp + 0x100 ]
mov r13, rdx
test al, al
adox r13, [ rsp + 0xd0 ]
mov r12, [ rsp + 0xf8 ]
adox r12, [ rsp + 0xc8 ]
mov rdx, rbp
shrd rdx, rbx, 56
mov r9, rdx
test al, al
adox r9, rdi
mov r8, 0x0 
adox r10, r8
mov rdi, rdx
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, [ rax + 0x38 ]
mov rdx, [ rax + 0x8 ]
mulx r8, rbx, [ rsi + 0x18 ]
adcx r13, [ rsp + 0x30 ]
adcx r12, [ rsp + 0x28 ]
mov rdx, 0xffffffffffffff 
and rbp, rdx
mov rdx, [ rsp - 0x40 ]
mov [ rsp + 0x148 ], rbp
mov rbp, rdx
adox rbp, [ rsp + 0x140 ]
mov [ rsp + 0x150 ], r8
mov r8, [ rsp - 0x48 ]
adox r8, [ rsp + 0x138 ]
adcx r13, [ rsp + 0x20 ]
adcx r12, [ rsp + 0x18 ]
mov rdx, r9
shrd rdx, r10, 56
mov r10, r11
mov [ rsp + 0x158 ], rdx
xor rdx, rdx
adox r10, [ rsp + 0x130 ]
mov [ rsp + 0x160 ], r12
mov r12, rcx
adox r12, [ rsp + 0x120 ]
adcx rbp, r15
adcx r14, r8
mov rdx, [ rax + 0x18 ]
mulx r8, r15, [ rsi + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x168 ], r12
mov [ rsp + 0x170 ], r10
mulx r10, r12, [ rsi + 0x10 ]
xor rdx, rdx
adox rbp, rbx
adox r14, [ rsp + 0x150 ]
adcx rbp, r12
adcx r10, r14
mov rdx, [ rsi + 0x0 ]
mulx r12, rbx, [ rax + 0x8 ]
mov rdx, 0x38 
bzhi r14, r9, rdx
adox rbp, r15
adox r8, r10
mov r9, [ rsp + 0x98 ]
add r9, [ rsp + 0xa0 ]
mov r15, [ rsp + 0x90 ]
adcx r15, [ rsp + 0x88 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x178 ], r14
mulx r14, r10, [ rsi + 0x0 ]
xor rdx, rdx
adox rbp, r10
adox r14, r8
adcx rbp, [ rsp + 0x118 ]
adc r14, 0x0
add rdi, rbp
adc r14, 0x0
mov rdx, [ rax + 0x10 ]
mulx r10, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x180 ], r10
mulx r10, rbp, [ rax + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x188 ], r8
mov [ rsp + 0x190 ], r10
mulx r10, r8, [ rsi + 0x28 ]
mov rdx, 0xffffffffffffff 
mov [ rsp + 0x198 ], rbp
mov rbp, rdi
and rbp, rdx
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x1a0 ], rbp
mov [ rsp + 0x1a8 ], r10
mulx r10, rbp, [ rsi + 0x18 ]
adox r9, [ rsp + 0x0 ]
adox r15, [ rsp - 0x8 ]
adcx r13, r11
adcx rcx, [ rsp + 0x160 ]
test al, al
adox r13, [ rsp - 0x20 ]
adox rcx, [ rsp - 0x28 ]
adcx r13, rbx
adcx r12, rcx
test al, al
adox r9, [ rsp - 0x10 ]
adox r15, [ rsp - 0x18 ]
mov rdx, r8
adcx rdx, [ rsp + 0x170 ]
mov r11, [ rsp + 0x1a8 ]
adcx r11, [ rsp + 0x168 ]
mov rbx, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r8, [ rax + 0x28 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x1b0 ], rcx
mov [ rsp + 0x1b8 ], r8
mulx r8, rcx, [ rsi + 0x20 ]
mov rdx, rbp
test al, al
adox rdx, [ rsp + 0xf0 ]
mov [ rsp + 0x1c0 ], r15
mov r15, r10
adox r15, [ rsp + 0xe8 ]
adcx rbx, rcx
adcx r8, r11
xor r11, r11
adox rdx, [ rsp + 0x198 ]
adox r15, [ rsp + 0x190 ]
adcx r13, [ rsp + 0x158 ]
adc r12, 0x0
mov rcx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x1c8 ], r9
mulx r9, r11, [ rax + 0x8 ]
mov rdx, r13
shrd rdx, r12, 56
test al, al
adox rcx, r11
adox r9, r15
adcx rcx, [ rsp + 0x70 ]
adcx r9, [ rsp + 0x68 ]
xor r15, r15
adox rbx, [ rsp + 0x188 ]
adox r8, [ rsp + 0x180 ]
mov r12, rdx
mov rdx, [ rsi + 0x30 ]
mulx r15, r11, [ rax + 0x0 ]
adcx rbx, [ rsp + 0x80 ]
adcx r8, [ rsp + 0x78 ]
mov rdx, rbp
mov [ rsp + 0x1d0 ], r9
xor r9, r9
adox rdx, [ rsp + 0x1c8 ]
adox r10, [ rsp + 0x1c0 ]
adcx rdx, r11
adcx r15, r10
test al, al
adox rdx, [ rsp - 0x30 ]
adox r15, [ rsp - 0x38 ]
mov rbp, rdx
mov rdx, [ rax + 0x10 ]
mulx r10, r11, [ rsi + 0x20 ]
adcx rbp, r11
adcx r10, r15
mov rdx, [ rsi + 0x8 ]
mulx r11, r15, [ rax + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1d8 ], rcx
mulx rcx, r9, [ rax + 0x18 ]
xor rdx, rdx
adox rbp, r9
adox rcx, r10
mov rdx, [ rax + 0x20 ]
mulx r9, r10, [ rsi + 0x8 ]
adcx rbx, r10
adcx r9, r8
mov rdx, [ rsi + 0x0 ]
mulx r10, r8, [ rax + 0x30 ]
xor rdx, rdx
adox rbp, [ rsp + 0x40 ]
adox rcx, [ rsp + 0x38 ]
adcx rbp, r15
adcx r11, rcx
xor r15, r15
adox rbp, r8
adox r10, r11
adcx rbx, [ rsp + 0x1b8 ]
adcx r9, [ rsp + 0x1b0 ]
shrd rdi, r14, 56
xor rdx, rdx
adox rbx, rdi
adox r9, rdx
mov r15, 0x38 
bzhi r14, rbx, r15
shrd rbx, r9, 56
test al, al
adox rbp, rbx
adox r10, rdx
mov r8, rbp
shrd r8, r10, 56
bzhi rcx, rbp, r15
add r8, [ rsp + 0x148 ]
bzhi r11, r8, r15
mov rdi, r12
adox rdi, [ rsp + 0x1d8 ]
mov r9, [ rsp + 0x1d0 ]
adox r9, rdx
mov r12, rdi
shrd r12, r9, 56
add r12, [ rsp + 0x128 ]
bzhi rbx, r12, r15
shr r8, 56
mov rbp, r8
add rbp, [ rsp + 0x178 ]
mov r10, rbp
shr r10, 56
bzhi r9, rbp, r15
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x0 ], r9
shr r12, 56
bzhi r9, r13, r15
lea r10, [ r10 + r9 ]
add r8, [ rsp + 0x1a0 ]
mov [ rbp + 0x18 ], rbx
lea r12, [ r12 + r8 ]
mov r13, r12
shr r13, 56
lea r13, [ r13 + r14 ]
mov [ rbp + 0x38 ], r11
bzhi r14, rdi, r15
bzhi r11, r12, r15
mov [ rbp + 0x30 ], rcx
mov [ rbp + 0x20 ], r11
mov [ rbp + 0x10 ], r14
mov [ rbp + 0x8 ], r10
mov [ rbp + 0x28 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 608
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.0195
; seed 2936879082361248 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5423508 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=81, initial num_batches=31): 134956 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.02488352557053479
; number reverted permutation / tried permutation: 56218 / 89789 =62.611%
; number reverted decision / tried decision: 34959 / 90210 =38.753%
; validated in 3.15s
