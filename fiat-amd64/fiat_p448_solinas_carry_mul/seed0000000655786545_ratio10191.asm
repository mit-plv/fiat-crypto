SECTION .text
	GLOBAL fiat_p448_solinas_carry_mul
fiat_p448_solinas_carry_mul:
sub rsp, 656
mov rax, rdx
mov rdx, [ rsi + 0x38 ]
mulx r11, r10, [ rax + 0x30 ]
mov rdx, [ rsi + 0x20 ]
mulx r8, rcx, [ rax + 0x38 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x30 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x20 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x28 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x48 ], r8
mov [ rsp - 0x40 ], rcx
mulx rcx, r8, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x38 ], rcx
mov [ rsp - 0x30 ], r8
mulx r8, rcx, [ rax + 0x10 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x28 ], r8
mov [ rsp - 0x20 ], rcx
mulx rcx, r8, [ rax + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], rcx
mov [ rsp - 0x10 ], r8
mulx r8, rcx, [ rax + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x8 ], r8
mov [ rsp + 0x0 ], rcx
mulx rcx, r8, [ rax + 0x38 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x8 ], rcx
mov [ rsp + 0x10 ], r8
mulx r8, rcx, [ rax + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x18 ], r8
mov [ rsp + 0x20 ], rcx
mulx rcx, r8, [ rax + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x28 ], rcx
mov [ rsp + 0x30 ], r8
mulx r8, rcx, [ rsi + 0x8 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x38 ], r8
mov [ rsp + 0x40 ], rcx
mulx rcx, r8, [ rsi + 0x18 ]
test al, al
adox r13, r9
adox rbx, r14
mov rdx, r10
adcx rdx, rbp
mov r9, r12
adcx r9, r11
xor r14, r14
adox r13, r15
adox rdi, rbx
mov r15, rdx
mov rdx, [ rax + 0x10 ]
mulx r14, rbx, [ rsi + 0x10 ]
mov rdx, r15
adcx rdx, r10
adcx r11, r9
add rdx, rbp
adcx r12, r11
mov r10, rdx
mov rdx, [ rax + 0x8 ]
mulx r11, rbp, [ rsi + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x48 ], r14
mov [ rsp + 0x50 ], rbx
mulx rbx, r14, [ rsi + 0x0 ]
add r13, [ rsp - 0x40 ]
adcx rdi, [ rsp - 0x48 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x58 ], rbx
mov [ rsp + 0x60 ], r14
mulx r14, rbx, [ rax + 0x38 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x68 ], rcx
mov [ rsp + 0x70 ], r8
mulx r8, rcx, [ rsi + 0x38 ]
mov rdx, rbx
mov [ rsp + 0x78 ], r11
xor r11, r11
adox rdx, rbx
mov [ rsp + 0x80 ], rbp
mov rbp, r14
adox rbp, r14
mov r11, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x88 ], rdi
mov [ rsp + 0x90 ], r13
mulx r13, rdi, [ rax + 0x18 ]
adcx r15, rcx
mov rdx, r8
adcx rdx, r9
xor r9, r9
adox r11, rdi
mov [ rsp + 0x98 ], rdx
mov rdx, r13
adox rdx, rbp
mov rbp, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xa0 ], r15
mulx r15, r9, [ rax + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xa8 ], rbp
mov [ rsp + 0xb0 ], r11
mulx r11, rbp, [ rax + 0x20 ]
adcx r10, rcx
adcx r8, r12
mov rdx, [ rsi + 0x30 ]
mulx rcx, r12, [ rax + 0x20 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0xb8 ], r11
mov [ rsp + 0xc0 ], rbp
mulx rbp, r11, [ rsi + 0x28 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0xc8 ], r8
mov [ rsp + 0xd0 ], r10
mulx r10, r8, [ rsi + 0x30 ]
test al, al
adox rbx, rdi
adox r13, r14
mov rdx, [ rsi + 0x28 ]
mulx rdi, r14, [ rax + 0x28 ]
adcx rbx, r12
mov rdx, rcx
adcx rdx, r13
mov r13, r9
mov [ rsp + 0xd8 ], rdx
xor rdx, rdx
adox r13, r8
mov [ rsp + 0xe0 ], rbx
mov rbx, r10
adox rbx, r15
adcx r13, r11
mov [ rsp + 0xe8 ], rdi
mov rdi, rbp
adcx rdi, rbx
mov rbx, r13
mov [ rsp + 0xf0 ], r14
xor r14, r14
adox rbx, r9
adox r15, rdi
mov rdx, r12
adcx rdx, [ rsp + 0xb0 ]
adcx rcx, [ rsp + 0xa8 ]
xor r9, r9
adox rbx, r8
adox r10, r15
adcx rbx, r11
adcx rbp, r10
xor r14, r14
adox rbx, [ rsp - 0x10 ]
adox rbp, [ rsp - 0x18 ]
mov r9, rdx
mov rdx, [ rsi + 0x28 ]
mulx r11, r12, [ rax + 0x18 ]
adcx rbx, [ rsp - 0x20 ]
adcx rbp, [ rsp - 0x28 ]
test al, al
adox r13, [ rsp - 0x10 ]
adox rdi, [ rsp - 0x18 ]
adcx r13, [ rsp - 0x20 ]
adcx rdi, [ rsp - 0x28 ]
test al, al
adox rbx, r12
mov rdx, r11
adox rdx, rbp
adcx rbx, [ rsp - 0x30 ]
adcx rdx, [ rsp - 0x38 ]
mov r8, rdx
mov rdx, [ rsi + 0x10 ]
mulx r10, r15, [ rax + 0x30 ]
test al, al
adox rbx, [ rsp + 0x0 ]
adox r8, [ rsp - 0x8 ]
adcx r13, r12
adcx r11, rdi
test al, al
adox r13, [ rsp - 0x30 ]
adox r11, [ rsp - 0x38 ]
adcx r13, [ rsp + 0x0 ]
adcx r11, [ rsp - 0x8 ]
mov rdx, [ rsp + 0xe0 ]
test al, al
adox rdx, [ rsp + 0xf0 ]
mov r12, [ rsp + 0xd8 ]
adox r12, [ rsp + 0xe8 ]
mov rbp, rdx
mov rdx, [ rsi + 0x38 ]
mulx r14, rdi, [ rax + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0xf8 ], r12
mov [ rsp + 0x100 ], rbp
mulx rbp, r12, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x108 ], rcx
mov [ rsp + 0x110 ], r9
mulx r9, rcx, [ rax + 0x38 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x118 ], rbp
mov [ rsp + 0x120 ], r12
mulx r12, rbp, [ rsi + 0x28 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x128 ], r12
mov [ rsp + 0x130 ], rbp
mulx rbp, r12, [ rsi + 0x20 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x138 ], rbp
mov [ rsp + 0x140 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
adcx r13, r15
mov rdx, r10
adcx rdx, r11
add rbx, r15
adcx r10, r8
xor r15, r15
adox r13, rcx
mov r8, r9
adox r8, rdx
mov rdx, [ rsi + 0x20 ]
mulx r15, r11, [ rax + 0x18 ]
adcx r13, rbp
adcx r12, r8
mov rdx, rdi
test al, al
adox rdx, [ rsp + 0x90 ]
adox r14, [ rsp + 0x88 ]
mov rdi, rdx
mov rdx, [ rsi + 0x30 ]
mulx r8, rbp, [ rax + 0x8 ]
adcx rbx, rcx
adcx r9, r10
add rdi, rbp
adcx r8, r14
test al, al
adox rdi, [ rsp + 0x30 ]
adox r8, [ rsp + 0x28 ]
adcx rbx, [ rsp + 0x140 ]
adcx r9, [ rsp + 0x138 ]
test al, al
adox rbx, [ rsp + 0x80 ]
adox r9, [ rsp + 0x78 ]
mov rdx, [ rax + 0x20 ]
mulx r10, rcx, [ rsi + 0x18 ]
mov rdx, [ rax + 0x28 ]
mulx rbp, r14, [ rsi + 0x10 ]
adcx rdi, r11
adcx r15, r8
test al, al
adox rdi, rcx
adox r10, r15
mov rdx, [ rsp + 0x120 ]
mov r11, rdx
adcx r11, [ rsp + 0xd0 ]
mov r8, [ rsp + 0x118 ]
mov rcx, r8
adcx rcx, [ rsp + 0xc8 ]
mov r15, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x148 ], r9
mov [ rsp + 0x150 ], rbx
mulx rbx, r9, [ rax + 0x30 ]
xor rdx, rdx
adox r11, [ rsp + 0x130 ]
adox rcx, [ rsp + 0x128 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x158 ], r12
mov [ rsp + 0x160 ], r13
mulx r13, r12, [ rsi + 0x10 ]
adcx rdi, r14
adcx rbp, r10
mov rdx, [ rax + 0x0 ]
mulx r10, r14, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x168 ], r13
mov [ rsp + 0x170 ], r12
mulx r12, r13, [ rax + 0x38 ]
xor rdx, rdx
adox rdi, r9
adox rbx, rbp
mov r9, r15
adcx r9, [ rsp + 0xa0 ]
adcx r8, [ rsp + 0x98 ]
xor r15, r15
adox rdi, r13
adox r12, rbx
mov rdx, rdi
shrd rdx, r12, 56
mov rbp, rdx
mov rdx, [ rsi + 0x18 ]
mulx rbx, r13, [ rax + 0x30 ]
mov rdx, [ rax + 0x0 ]
mulx r15, r12, [ rsi + 0x8 ]
xor rdx, rdx
adox r9, [ rsp + 0x130 ]
adox r8, [ rsp + 0x128 ]
adcx r9, [ rsp + 0x20 ]
adcx r8, [ rsp + 0x18 ]
test al, al
adox r11, [ rsp + 0x20 ]
adox rcx, [ rsp + 0x18 ]
adcx r9, r13
mov [ rsp + 0x178 ], rcx
mov rcx, rbx
adcx rcx, r8
mov r8, r14
test al, al
adox r8, [ rsp + 0x90 ]
adox r10, [ rsp + 0x88 ]
adcx r8, [ rsp + 0x170 ]
adcx r10, [ rsp + 0x168 ]
add r8, [ rsp + 0x40 ]
adcx r10, [ rsp + 0x38 ]
mov r14, 0xffffffffffffff 
and rdi, r14
mov r14, [ rsp + 0x110 ]
adox r14, [ rsp + 0xf0 ]
mov [ rsp + 0x180 ], rdi
mov rdi, [ rsp + 0x108 ]
adox rdi, [ rsp + 0xe8 ]
adcx r9, [ rsp + 0x10 ]
adcx rcx, [ rsp + 0x8 ]
add r9, r12
adcx r15, rcx
mov rdx, [ rax + 0x8 ]
mulx rcx, r12, [ rsi + 0x0 ]
mov rdx, rbp
test al, al
adox rdx, [ rsp + 0x160 ]
mov [ rsp + 0x188 ], r10
mov r10, [ rsp + 0x158 ]
mov [ rsp + 0x190 ], r8
mov r8, 0x0 
adox r10, r8
mov r8, rdx
shrd r8, r10, 56
add r9, r12
adcx rcx, r15
xor r15, r15
adox r9, r8
adox rcx, r15
mov r12, r9
shrd r12, rcx, 56
mov r10, rdx
mov rdx, [ rsi + 0x20 ]
mulx rcx, r8, [ rax + 0x30 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x198 ], r12
mulx r12, r15, [ rax + 0x0 ]
test al, al
adox r14, r8
mov rdx, rcx
adox rdx, rdi
adcx r14, [ rsp + 0x70 ]
adcx rdx, [ rsp + 0x68 ]
add r11, r13
adcx rbx, [ rsp + 0x178 ]
mov r13, r8
add r13, [ rsp + 0x100 ]
adcx rcx, [ rsp + 0xf8 ]
mov rdi, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x1a0 ], r14
mulx r14, r8, [ rax + 0x18 ]
mov rdx, r8
test al, al
adox rdx, [ rsp + 0x190 ]
adox r14, [ rsp + 0x188 ]
mov r8, 0xffffffffffffff 
and r10, r8
adox r11, [ rsp + 0x10 ]
adox rbx, [ rsp + 0x8 ]
mov r8, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x1a8 ], r10
mov [ rsp + 0x1b0 ], rdi
mulx rdi, r10, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x1b8 ], r12
mov [ rsp + 0x1c0 ], r15
mulx r15, r12, [ rax + 0x10 ]
adcx r11, r10
adcx rdi, rbx
mov rdx, 0xffffffffffffff 
and r9, rdx
mov rdx, [ rax + 0x8 ]
mulx r10, rbx, [ rsi + 0x8 ]
mov rdx, r8
shrd rdx, r14, 56
xor r14, r14
adox r13, [ rsp + 0x70 ]
adox rcx, [ rsp + 0x68 ]
mov r14, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x1c8 ], r9
mov [ rsp + 0x1d0 ], rdi
mulx rdi, r9, [ rax + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x1d8 ], r14
mov [ rsp + 0x1e0 ], rdi
mulx rdi, r14, [ rsi + 0x30 ]
adcx r13, [ rsp + 0x1c0 ]
adcx rcx, [ rsp + 0x1b8 ]
xor rdx, rdx
adox r13, rbx
adox r10, rcx
mov rdx, [ rax + 0x8 ]
mulx rcx, rbx, [ rsi + 0x20 ]
adcx r13, r12
adcx r15, r10
xor rdx, rdx
adox r13, [ rsp + 0x198 ]
adox r15, rdx
adcx r11, rbx
adcx rcx, [ rsp + 0x1d0 ]
mov r12, r13
shrd r12, r15, 56
mov r10, 0x38 
bzhi rbx, r8, r10
mov rdx, [ rsi + 0x18 ]
mulx r15, r8, [ rax + 0x18 ]
lea r12, [ r12 + rbx ]
mov rdx, [ rsi + 0x8 ]
mulx r10, rbx, [ rax + 0x28 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x1e8 ], rcx
mov [ rsp + 0x1f0 ], r11
mulx r11, rcx, [ rsi + 0x28 ]
mov rdx, r14
adox rdx, [ rsp + 0x1a0 ]
adox rdi, [ rsp + 0x1b0 ]
mov r14, [ rsp + 0x150 ]
test al, al
adox r14, [ rsp + 0x50 ]
mov [ rsp + 0x1f8 ], r12
mov r12, [ rsp + 0x148 ]
adox r12, [ rsp + 0x48 ]
adcx rdx, rcx
adcx r11, rdi
mov rcx, 0xffffffffffffff 
and r13, rcx
adox rdx, r9
adox r11, [ rsp + 0x1e0 ]
adcx rdx, r8
adcx r15, r11
mov r9, rdx
mov rdx, [ rax + 0x20 ]
mulx rdi, r8, [ rsi + 0x10 ]
add r9, r8
adcx rdi, r15
mov rdx, [ rax + 0x30 ]
mulx r15, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r8, [ rax + 0x18 ]
test al, al
adox r14, r8
adox rcx, r12
adcx r14, [ rsp + 0x60 ]
adcx rcx, [ rsp + 0x58 ]
add r14, [ rsp + 0x1d8 ]
adc rcx, 0x0
add r9, rbx
adcx r10, rdi
mov rdx, 0x38 
bzhi rbx, [ rsp + 0x1f8 ], rdx
adox rbp, r14
mov r12, 0x0 
adox rcx, r12
mov rdx, [ rax + 0x18 ]
mulx r8, rdi, [ rsi + 0x10 ]
mov rdx, [ rax + 0x28 ]
mulx r12, r14, [ rsi + 0x0 ]
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x18 ], rbx
mov rbx, 0x38 
bzhi rdx, rbp, rbx
mov rbx, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x200 ], r13
mov [ rsp + 0x208 ], r12
mulx r12, r13, [ rsi + 0x18 ]
mov rdx, r13
adox rdx, [ rsp + 0x1f0 ]
adox r12, [ rsp + 0x1e8 ]
add rdx, rdi
adcx r8, r12
add rdx, [ rsp + 0xc0 ]
adcx r8, [ rsp + 0xb8 ]
add r9, r11
adcx r15, r10
shrd rbp, rcx, 56
xor r11, r11
adox rdx, r14
adox r8, [ rsp + 0x208 ]
adcx rdx, rbp
adc r8, 0x0
mov r10, rdx
shrd r10, r8, 56
add r9, r10
adc r15, 0x0
mov rcx, r9
shrd rcx, r15, 56
add rcx, [ rsp + 0x180 ]
mov rdi, 0x38 
bzhi r14, rcx, rdi
shr rcx, 56
bzhi r13, r9, rdi
bzhi r12, rdx, rdi
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x30 ], r13
lea rbx, [ rbx + rcx ]
mov [ rbp + 0x38 ], r14
add rcx, [ rsp + 0x1a8 ]
mov rdx, [ rsp + 0x1f8 ]
shr rdx, 56
lea rdx, [ rdx + rbx ]
mov r8, rdx
shr r8, 56
bzhi r10, rdx, rdi
mov r9, rcx
shr r9, 56
add r9, [ rsp + 0x1c8 ]
bzhi r15, rcx, rdi
mov [ rbp + 0x8 ], r9
lea r8, [ r8 + r12 ]
mov [ rbp + 0x28 ], r8
mov r14, [ rsp + 0x200 ]
mov [ rbp + 0x10 ], r14
mov [ rbp + 0x0 ], r15
mov [ rbp + 0x20 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 656
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.0191
; seed 3551544531047080 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5450616 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=79, initial num_batches=31): 135892 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.024931493981597677
; number reverted permutation / tried permutation: 56756 / 90016 =63.051%
; number reverted decision / tried decision: 34834 / 89983 =38.712%
; validated in 3.917s
