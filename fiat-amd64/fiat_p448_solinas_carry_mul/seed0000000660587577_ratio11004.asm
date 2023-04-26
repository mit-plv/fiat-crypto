SECTION .text
	GLOBAL fiat_p448_solinas_carry_mul
fiat_p448_solinas_carry_mul:
sub rsp, 456
mov rax, rdx
mov rdx, [ rdx + 0x38 ]
mulx r11, r10, [ rsi + 0x38 ]
mov rdx, r10
xor rcx, rcx
adox rdx, r10
mov r8, r11
adox r8, r11
mov r9, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, rcx, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x38 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x28 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x48 ], r12
mov [ rsp - 0x40 ], rbp
mulx rbp, r12, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x38 ], rbp
mov [ rsp - 0x30 ], r12
mulx r12, rbp, [ rax + 0x18 ]
adcx r10, rbp
mov rdx, r12
adcx rdx, r11
xor r11, r11
adox r9, rbp
adox r12, r8
adcx r10, rcx
mov r8, rbx
adcx r8, rdx
mov rdx, [ rax + 0x20 ]
mulx r11, rbp, [ rsi + 0x8 ]
xor rdx, rdx
adox r9, rcx
adox rbx, r12
mov rdx, [ rsi + 0x38 ]
mulx r12, rcx, [ rax + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], r11
mov [ rsp - 0x20 ], rbp
mulx rbp, r11, [ rax + 0x10 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x18 ], rbp
mov [ rsp - 0x10 ], r11
mulx r11, rbp, [ rax + 0x30 ]
adcx r10, r15
mov rdx, rdi
adcx rdx, r8
mov r8, rcx
test al, al
adox r8, rbp
mov [ rsp - 0x8 ], rdx
mov rdx, r11
adox rdx, r12
adcx r8, r13
mov [ rsp + 0x0 ], r10
mov r10, r14
adcx r10, rdx
mov rdx, r8
test al, al
adox rdx, rcx
adox r12, r10
adcx rdx, rbp
adcx r11, r12
mov rcx, rdx
mov rdx, [ rax + 0x10 ]
mulx r12, rbp, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x8 ], r12
mov [ rsp + 0x10 ], rbp
mulx rbp, r12, [ rax + 0x30 ]
add rcx, r13
adcx r14, r11
mov rdx, [ rsi + 0x38 ]
mulx r11, r13, [ rax + 0x8 ]
test al, al
adox rcx, r13
mov rdx, r11
adox rdx, r14
mov r14, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x18 ], rbp
mov [ rsp + 0x20 ], r12
mulx r12, rbp, [ rsi + 0x30 ]
adcx rcx, rbp
mov rdx, r12
adcx rdx, r14
add r8, r13
adcx r11, r10
mov r10, rdx
mov rdx, [ rsi + 0x28 ]
mulx r14, r13, [ rax + 0x18 ]
xor rdx, rdx
adox r8, rbp
adox r12, r11
adcx r8, r13
mov rbp, r14
adcx rbp, r12
mov rdx, [ rsi + 0x30 ]
mulx r12, r11, [ rax + 0x28 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x28 ], rbp
mov [ rsp + 0x30 ], r8
mulx r8, rbp, [ rax + 0x20 ]
test al, al
adox rcx, r13
adox r14, r10
adcx rbp, r11
adcx r12, r8
mov rdx, [ rax + 0x30 ]
mulx r13, r10, [ rsi + 0x28 ]
test al, al
adox rbp, r10
adox r13, r12
mov rdx, [ rsi + 0x20 ]
mulx r8, r11, [ rax + 0x20 ]
mov rdx, [ rax + 0x30 ]
mulx r10, r12, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x38 ], r14
mov [ rsp + 0x40 ], rcx
mulx rcx, r14, [ rax + 0x0 ]
adcx r9, r15
adcx rdi, rbx
mov rdx, [ rax + 0x38 ]
mulx rbx, r15, [ rsi + 0x18 ]
mov rdx, r12
add rdx, [ rsp + 0x0 ]
mov [ rsp + 0x48 ], rcx
mov rcx, r10
adcx rcx, [ rsp - 0x8 ]
mov [ rsp + 0x50 ], r14
xor r14, r14
adox r9, r12
adox r10, rdi
adcx rdx, r15
mov r12, rbx
adcx r12, rcx
xor rdi, rdi
adox r9, r15
adox rbx, r10
mov r14, rdx
mov rdx, [ rax + 0x8 ]
mulx rcx, r15, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x20 ]
mulx rdi, r10, [ rax + 0x38 ]
adcx rbp, r10
adcx rdi, r13
mov rdx, r11
test al, al
adox rdx, [ rsp + 0x30 ]
mov r13, r8
adox r13, [ rsp + 0x28 ]
mov r10, rbp
adcx r10, [ rsp + 0x50 ]
mov [ rsp + 0x58 ], rbx
mov rbx, rdi
adcx rbx, [ rsp + 0x48 ]
mov [ rsp + 0x60 ], r9
mov r9, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x68 ], r12
mov [ rsp + 0x70 ], r14
mulx r14, r12, [ rsi + 0x18 ]
mov rdx, r11
test al, al
adox rdx, [ rsp + 0x40 ]
adox r8, [ rsp + 0x38 ]
mov r11, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x78 ], r14
mov [ rsp + 0x80 ], r12
mulx r12, r14, [ rsi + 0x18 ]
adcx r9, r14
mov rdx, r12
adcx rdx, r13
add r11, r14
adcx r12, r8
test al, al
adox r10, r15
adox rcx, rbx
mov r15, rdx
mov rdx, [ rsi + 0x10 ]
mulx rbx, r13, [ rax + 0x30 ]
adcx r11, r13
mov rdx, rbx
adcx rdx, r12
mov r8, rdx
mov rdx, [ rsi + 0x18 ]
mulx r12, r14, [ rax + 0x20 ]
add rbp, [ rsp + 0x80 ]
adcx rdi, [ rsp + 0x78 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x88 ], rdi
mov [ rsp + 0x90 ], rbp
mulx rbp, rdi, [ rax + 0x10 ]
xor rdx, rdx
adox r9, r13
adox rbx, r15
adcx r10, rdi
adcx rbp, rcx
mov rdx, [ rsi + 0x20 ]
mulx rcx, r15, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mulx rdi, r13, [ rax + 0x30 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x98 ], rbx
mov [ rsp + 0xa0 ], r9
mulx r9, rbx, [ rsi + 0x8 ]
add r10, r15
adcx rcx, rbp
xor rdx, rdx
adox r10, r14
adox r12, rcx
mov rdx, [ rax + 0x28 ]
mulx rbp, r14, [ rsi + 0x10 ]
adcx r10, r14
adcx rbp, r12
test al, al
adox r10, r13
adox rdi, rbp
mov rdx, [ rsi + 0x20 ]
mulx r13, r15, [ rax + 0x0 ]
adcx r11, rbx
mov rdx, r9
adcx rdx, r8
add r11, r15
adcx r13, rdx
mov rdx, [ rsi + 0x10 ]
mulx rcx, r8, [ rax + 0x8 ]
mov rdx, [ rsi + 0x38 ]
mulx r14, r12, [ rax + 0x30 ]
mov rdx, [ rax + 0x0 ]
mulx r15, rbp, [ rsi + 0x0 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0xa8 ], r14
mov [ rsp + 0xb0 ], r12
mulx r12, r14, [ rsi + 0x0 ]
mov rdx, r8
mov [ rsp + 0xb8 ], r15
xor r15, r15
adox rdx, [ rsp + 0x90 ]
adox rcx, [ rsp + 0x88 ]
adcx r10, r14
adcx r12, rdi
mov rdi, r10
shrd rdi, r12, 56
mov r8, rdx
mov rdx, [ rax + 0x8 ]
mulx r12, r14, [ rsi + 0x18 ]
mov rdx, rbx
add rdx, [ rsp + 0xa0 ]
adcx r9, [ rsp + 0x98 ]
add r11, r14
adcx r12, r13
test al, al
adox rdx, rbp
adox r9, [ rsp + 0xb8 ]
mov rbx, rdx
mov rdx, [ rax + 0x10 ]
mulx rbp, r13, [ rsi + 0x8 ]
adcx r8, r13
adcx rbp, rcx
mov rdx, 0xffffffffffffff 
and r10, rdx
mov rcx, rdi
adox rcx, rbx
adox r9, r15
mov rdx, [ rax + 0x18 ]
mulx rbx, r14, [ rsi + 0x0 ]
mov rdx, [ rax + 0x20 ]
mulx r15, r13, [ rsi + 0x0 ]
adcx r8, r14
adcx rbx, rbp
mov rdx, [ rsi + 0x30 ]
mulx r14, rbp, [ rax + 0x38 ]
mov rdx, r8
shrd rdx, rbx, 56
mov rbx, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0xc0 ], r10
mov [ rsp + 0xc8 ], r14
mulx r14, r10, [ rsi + 0x8 ]
mov rdx, rcx
shrd rdx, r9, 56
mov r9, 0xffffffffffffff 
and r8, r9
adox r11, [ rsp - 0x10 ]
adox r12, [ rsp - 0x18 ]
adcx r11, r10
adcx r14, r12
add r11, r13
adcx r15, r14
test al, al
adox r11, rbx
mov r13, 0x0 
adox r15, r13
mov rbx, rdx
mov rdx, [ rax + 0x20 ]
mulx r12, r10, [ rsi + 0x28 ]
mov rdx, rbp
adcx rdx, [ rsp + 0xb0 ]
mov r14, [ rsp + 0xa8 ]
mov r9, r14
adcx r9, [ rsp + 0xc8 ]
add rdi, r11
adc r15, 0x0
mov r11, rdx
add r11, [ rsp + 0x10 ]
mov [ rsp + 0xd0 ], r8
mov r8, r9
adcx r8, [ rsp + 0x8 ]
mov [ rsp + 0xd8 ], r15
xor r15, r15
adox rdx, [ rsp + 0xb0 ]
adox r14, r9
adcx rdx, rbp
adcx r14, [ rsp + 0xc8 ]
mov r13, rdx
mov rdx, [ rax + 0x0 ]
mulx r9, rbp, [ rsi + 0x10 ]
test al, al
adox r13, [ rsp + 0x10 ]
adox r14, [ rsp + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0xe0 ], rdi
mulx rdi, r15, [ rsi + 0x30 ]
adcx r11, r15
mov rdx, rdi
adcx rdx, r8
mov r8, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xe8 ], rbx
mov [ rsp + 0xf0 ], r9
mulx r9, rbx, [ rax + 0x28 ]
test al, al
adox r11, r10
mov rdx, r12
adox rdx, r8
mov r8, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xf8 ], r11
mov [ rsp + 0x100 ], r9
mulx r9, r11, [ rax + 0x38 ]
adcx r13, r15
adcx rdi, r14
mov rdx, [ rsi + 0x0 ]
mulx r15, r14, [ rax + 0x8 ]
xor rdx, rdx
adox r13, r10
adox r12, rdi
mov r10, rbp
adcx r10, [ rsp + 0x70 ]
mov rdi, [ rsp + 0xf0 ]
adcx rdi, [ rsp + 0x68 ]
test al, al
adox r13, rbx
adox r12, [ rsp + 0x100 ]
adcx r13, [ rsp + 0x20 ]
adcx r12, [ rsp + 0x18 ]
mov rbp, rbx
mov [ rsp + 0x108 ], r15
xor r15, r15
adox rbp, [ rsp + 0xf8 ]
adox r8, [ rsp + 0x100 ]
adcx rbp, [ rsp + 0x20 ]
adcx r8, [ rsp + 0x18 ]
mov rdx, [ rax + 0x0 ]
mulx r15, rbx, [ rsi + 0x30 ]
test al, al
adox r13, r11
mov rdx, r9
adox rdx, r12
mov r12, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x110 ], r13
mov [ rsp + 0x118 ], r15
mulx r15, r13, [ rsi + 0x8 ]
adcx r10, r13
adcx r15, rdi
mov rdx, [ rax + 0x0 ]
mulx r13, rdi, [ rsi + 0x8 ]
add rbp, r11
adcx r9, r8
mov rdx, [ rsi + 0x18 ]
mulx r8, r11, [ rax + 0x10 ]
xor rdx, rdx
adox rbp, rdi
adox r13, r9
adcx rbp, r14
adcx r13, [ rsp + 0x108 ]
mov rdx, [ rax + 0x10 ]
mulx rdi, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x120 ], r8
mulx r8, r9, [ rax + 0x10 ]
test al, al
adox rbp, [ rsp + 0xe8 ]
mov rdx, 0x0 
adox r13, rdx
mov rdx, rbp
shrd rdx, r13, 56
add r10, r14
adcx rdi, r15
mov r15, rbx
xor r14, r14
adox r15, [ rsp + 0x60 ]
mov r13, [ rsp + 0x118 ]
adox r13, [ rsp + 0x58 ]
adcx r15, [ rsp - 0x40 ]
adcx r13, [ rsp - 0x48 ]
mov rbx, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x128 ], rdi
mulx rdi, r14, [ rax + 0x0 ]
mov rdx, r14
test al, al
adox rdx, [ rsp + 0x110 ]
adox rdi, r12
adcx r15, r9
adcx r8, r13
mov r12, rdx
mov rdx, [ rax + 0x20 ]
mulx r13, r9, [ rsi + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x130 ], r13
mulx r13, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x138 ], r9
mov [ rsp + 0x140 ], r8
mulx r8, r9, [ rax + 0x8 ]
test al, al
adox r12, r9
adox r8, rdi
adcx r12, r11
adcx r8, [ rsp + 0x120 ]
mov rdx, [ rax + 0x18 ]
mulx rdi, r11, [ rsi + 0x18 ]
test al, al
adox r12, r14
adox r13, r8
mov rdx, 0x38 
bzhi r14, rbp, rdx
adox r10, rbx
mov rbp, [ rsp + 0x128 ]
mov r9, 0x0 
adox rbp, r9
bzhi rbx, r10, rdx
mov r8, [ rsp + 0xe0 ]
mov r9, [ rsp + 0xd8 ]
mov rdx, r8
shrd rdx, r9, 56
shrd r10, rbp, 56
xor r9, r9
adox r12, [ rsp - 0x20 ]
adox r13, [ rsp - 0x28 ]
adcx r12, [ rsp - 0x30 ]
adcx r13, [ rsp - 0x38 ]
add r10, [ rsp + 0xd0 ]
test al, al
adox r15, r11
adox rdi, [ rsp + 0x140 ]
adcx r12, rdx
adc r13, 0x0
mov r11, r12
shrd r11, r13, 56
mov rbp, 0x38 
bzhi rdx, r10, rbp
adox r15, [ rsp + 0x138 ]
adox rdi, [ rsp + 0x130 ]
mov r13, rdx
mov rdx, [ rax + 0x28 ]
mulx rbp, r9, [ rsi + 0x8 ]
mov rdx, 0xffffffffffffff 
and r8, rdx
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x10 ], rbx
adox r15, r9
adox rbp, rdi
mov rbx, rdx
mov rdx, [ rsi + 0x0 ]
mulx r9, rdi, [ rax + 0x30 ]
adcx r15, rdi
adcx r9, rbp
add r15, r11
adc r9, 0x0
mov rdx, 0xffffffffffffff 
mov r11, r15
and r11, rdx
shrd r15, r9, 56
and rcx, rdx
add r15, [ rsp + 0xc0 ]
mov [ rbx + 0x30 ], r11
mov rbp, r15
shr rbp, 56
lea r8, [ r8 + rbp ]
lea rcx, [ rcx + rbp ]
and r15, rdx
mov [ rbx + 0x38 ], r15
mov rdi, rcx
shr rdi, 56
and r12, rdx
lea rdi, [ rdi + r14 ]
shr r10, 56
lea r10, [ r10 + r8 ]
mov r14, r10
and r14, rdx
mov [ rbx + 0x20 ], r14
shr r10, 56
lea r10, [ r10 + r12 ]
and rcx, rdx
mov [ rbx + 0x28 ], r10
mov [ rbx + 0x18 ], r13
mov [ rbx + 0x0 ], rcx
mov [ rbx + 0x8 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 456
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.1004
; seed 0263126776082018 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5072797 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=80, initial num_batches=31): 132766 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.026172149210780562
; number reverted permutation / tried permutation: 59046 / 89826 =65.734%
; number reverted decision / tried decision: 35350 / 90173 =39.202%
; validated in 3.367s
