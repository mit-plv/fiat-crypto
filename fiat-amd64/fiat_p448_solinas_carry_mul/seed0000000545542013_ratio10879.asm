SECTION .text
	GLOBAL fiat_p448_solinas_carry_mul
fiat_p448_solinas_carry_mul:
sub rsp, 568
mov rax, rdx
mov rdx, [ rsi + 0x38 ]
mulx r11, r10, [ rax + 0x30 ]
mov rdx, [ rsi + 0x30 ]
mulx r8, rcx, [ rax + 0x38 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x28 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x48 ], r14
mov [ rsp - 0x40 ], r13
mulx r13, r14, [ rax + 0x20 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x38 ], r13
mov [ rsp - 0x30 ], r14
mulx r14, r13, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], rdi
mov [ rsp - 0x20 ], r15
mulx r15, rdi, [ rax + 0x8 ]
mov rdx, r10
mov [ rsp - 0x18 ], r15
xor r15, r15
adox rdx, rcx
mov [ rsp - 0x10 ], rdi
mov rdi, r8
adox rdi, r11
mov r15, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x8 ], rbx
mov [ rsp + 0x0 ], r9
mulx r9, rbx, [ rsi + 0x38 ]
mov rdx, r15
adcx rdx, r10
adcx r11, rdi
xor r10, r10
adox rbx, rbp
adox r12, r9
mov rbp, rdx
mov rdx, [ rax + 0x30 ]
mulx r10, r9, [ rsi + 0x30 ]
adcx rbp, rcx
adcx r8, r11
mov rdx, [ rsi + 0x38 ]
mulx r11, rcx, [ rax + 0x10 ]
xor rdx, rdx
adox r15, rcx
mov [ rsp + 0x8 ], r8
mov r8, r11
adox r8, rdi
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x10 ], r8
mulx r8, rdi, [ rsi + 0x0 ]
mov rdx, r13
adcx rdx, r9
mov [ rsp + 0x18 ], r8
mov r8, r10
adcx r8, r14
mov [ rsp + 0x20 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x28 ], r15
mov [ rsp + 0x30 ], rbp
mulx rbp, r15, [ rax + 0x8 ]
add rdi, [ rsp + 0x0 ]
adcx r8, [ rsp - 0x8 ]
mov rdx, rdi
test al, al
adox rdx, r13
adox r14, r8
mov r13, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x38 ], rbp
mov [ rsp + 0x40 ], r15
mulx r15, rbp, [ rax + 0x30 ]
adcx rbx, rbp
adcx r15, r12
test al, al
adox r13, r9
adox r10, r14
mov rdx, [ rax + 0x38 ]
mulx r9, r12, [ rsi + 0x20 ]
mov rdx, rcx
adcx rdx, [ rsp + 0x30 ]
adcx r11, [ rsp + 0x8 ]
test al, al
adox rbx, r12
adox r9, r15
mov rcx, rdx
mov rdx, [ rsi + 0x30 ]
mulx rbp, r14, [ rax + 0x10 ]
mov rdx, [ rax + 0x8 ]
mulx r12, r15, [ rsi + 0x38 ]
adcx r13, [ rsp + 0x0 ]
adcx r10, [ rsp - 0x8 ]
test al, al
adox r13, r15
mov rdx, r12
adox rdx, r10
mov r10, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x48 ], r11
mov [ rsp + 0x50 ], rcx
mulx rcx, r11, [ rax + 0x0 ]
adcx r13, r14
mov rdx, rbp
adcx rdx, r10
test al, al
adox rdi, r15
adox r12, r8
mov r8, rdx
mov rdx, [ rsi + 0x30 ]
mulx r10, r15, [ rax + 0x8 ]
mov rdx, rbx
adcx rdx, r11
adcx rcx, r9
add rdi, r14
adcx rbp, r12
mov r14, rdx
mov rdx, [ rsi + 0x20 ]
mulx r12, r11, [ rax + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x58 ], r12
mov [ rsp + 0x60 ], r11
mulx r11, r12, [ rax + 0x10 ]
test al, al
adox rdi, [ rsp - 0x20 ]
adox rbp, [ rsp - 0x28 ]
adcx r14, r15
adcx r10, rcx
xor rdx, rdx
adox r13, [ rsp - 0x20 ]
adox r8, [ rsp - 0x28 ]
mov rdx, [ rsi + 0x18 ]
mulx rcx, r15, [ rax + 0x0 ]
adcx r14, r12
adcx r11, r10
mov rdx, [ rax + 0x28 ]
mulx r10, r12, [ rsi + 0x18 ]
test al, al
adox r14, [ rsp + 0x60 ]
adox r11, [ rsp + 0x58 ]
adcx rbx, r15
adcx rcx, r9
mov rdx, [ rax + 0x28 ]
mulx r15, r9, [ rsi + 0x10 ]
test al, al
adox rbx, [ rsp - 0x10 ]
adox rcx, [ rsp - 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x68 ], rcx
mov [ rsp + 0x70 ], rbx
mulx rbx, rcx, [ rax + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x78 ], r10
mov [ rsp + 0x80 ], r12
mulx r12, r10, [ rax + 0x20 ]
adcx r13, rcx
mov rdx, rbx
adcx rdx, r8
mov r8, rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x88 ], r13
mov [ rsp + 0x90 ], r15
mulx r15, r13, [ rsi + 0x8 ]
add r14, r10
adcx r12, r11
xor rdx, rdx
adox rdi, rcx
adox rbx, rbp
mov rdx, [ rax + 0x18 ]
mulx r11, rbp, [ rsi + 0x30 ]
mov rdx, rbp
adcx rdx, [ rsp + 0x50 ]
mov rcx, r11
adcx rcx, [ rsp + 0x48 ]
add rdx, [ rsp - 0x30 ]
adcx rcx, [ rsp - 0x38 ]
mov r10, rdx
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x98 ], rcx
mov [ rsp + 0xa0 ], r8
mulx r8, rcx, [ rsi + 0x38 ]
test al, al
adox r14, r9
adox r12, [ rsp + 0x90 ]
adcx r14, r13
adcx r15, r12
xor rdx, rdx
adox rdi, [ rsp + 0x80 ]
adox rbx, [ rsp + 0x78 ]
mov rdx, [ rax + 0x18 ]
mulx r13, r9, [ rsi + 0x38 ]
mov rdx, rbp
adcx rdx, [ rsp + 0x28 ]
adcx r11, [ rsp + 0x10 ]
mov rbp, rcx
test al, al
adox rbp, rcx
mov r12, r8
adox r12, r8
adcx rcx, r9
mov [ rsp + 0xa8 ], r10
mov r10, r13
adcx r10, r8
mov r8, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xb0 ], rbx
mov [ rsp + 0xb8 ], rdi
mulx rdi, rbx, [ rax + 0x38 ]
xor rdx, rdx
adox rbp, r9
adox r13, r12
mov rdx, [ rsi + 0x10 ]
mulx r12, r9, [ rax + 0x30 ]
adcx r14, rbx
adcx rdi, r15
mov rdx, [ rsi + 0x30 ]
mulx rbx, r15, [ rax + 0x20 ]
mov rdx, r14
shrd rdx, rdi, 56
add rbp, r15
mov rdi, rbx
adcx rdi, r13
add rcx, r15
adcx rbx, r10
mov r10, rdx
mov rdx, [ rax + 0x28 ]
mulx r15, r13, [ rsi + 0x20 ]
xor rdx, rdx
adox r8, [ rsp - 0x30 ]
adox r11, [ rsp - 0x38 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xc0 ], r10
mov [ rsp + 0xc8 ], rbx
mulx rbx, r10, [ rax + 0x38 ]
mov rdx, r9
adcx rdx, [ rsp + 0xb8 ]
mov [ rsp + 0xd0 ], rbx
mov rbx, r12
adcx rbx, [ rsp + 0xb0 ]
add r8, r13
mov [ rsp + 0xd8 ], rbx
mov rbx, r15
adcx rbx, r11
mov r11, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xe0 ], rbx
mov [ rsp + 0xe8 ], r8
mulx r8, rbx, [ rsi + 0x28 ]
mov rdx, [ rsp + 0x88 ]
add rdx, [ rsp + 0x80 ]
mov [ rsp + 0xf0 ], r11
mov r11, [ rsp + 0xa0 ]
adcx r11, [ rsp + 0x78 ]
add rbp, rbx
mov [ rsp + 0xf8 ], r10
mov r10, r8
adcx r10, rdi
xor rdi, rdi
adox rcx, rbx
adox r8, [ rsp + 0xc8 ]
adcx rdx, r9
adcx r12, r11
mov r9, rdx
mov rdx, [ rsi + 0x20 ]
mulx r11, rbx, [ rax + 0x30 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x100 ], r8
mulx r8, rdi, [ rsi + 0x8 ]
xor rdx, rdx
adox r9, rdi
mov [ rsp + 0x108 ], rcx
mov rcx, r8
adox rcx, r12
mov r12, 0x38 
bzhi rdx, r14, r12
mov r14, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x110 ], rcx
mulx rcx, r12, [ rax + 0x0 ]
mov rdx, r13
adox rdx, [ rsp + 0xa8 ]
adox r15, [ rsp + 0x98 ]
mov r13, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x118 ], r14
mov [ rsp + 0x120 ], r9
mulx r9, r14, [ rax + 0x30 ]
add rbp, rbx
mov rdx, r11
adcx rdx, r10
mov r10, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x128 ], rcx
mov [ rsp + 0x130 ], r12
mulx r12, rcx, [ rsi + 0x8 ]
test al, al
adox rbp, [ rsp + 0xf8 ]
adox r10, [ rsp + 0xd0 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x138 ], r15
mov [ rsp + 0x140 ], r13
mulx r13, r15, [ rax + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x148 ], r9
mov [ rsp + 0x150 ], r14
mulx r14, r9, [ rax + 0x8 ]
adcx rbp, r15
adcx r13, r10
mov rdx, [ rax + 0x18 ]
mulx r15, r10, [ rsi + 0x0 ]
xor rdx, rdx
adox rbp, r9
adox r14, r13
mov r9, rcx
adcx r9, [ rsp + 0x70 ]
adcx r12, [ rsp + 0x68 ]
test al, al
adox r9, r10
adox r15, r12
mov rdx, [ rsi + 0x0 ]
mulx r13, rcx, [ rax + 0x0 ]
mov rdx, r9
shrd rdx, r15, 56
mov r10, rdi
test al, al
adox r10, [ rsp + 0xf0 ]
adox r8, [ rsp + 0xd8 ]
mov rdi, [ rsp + 0x140 ]
adcx rdi, [ rsp + 0x150 ]
mov r12, [ rsp + 0x138 ]
adcx r12, [ rsp + 0x148 ]
xor r15, r15
adox r10, rcx
adox r13, r8
mov rcx, rdx
mov rdx, [ rax + 0x38 ]
mulx r15, r8, [ rsi + 0x10 ]
mov rdx, r10
adcx rdx, [ rsp + 0xc0 ]
adc r13, 0x0
mov r10, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x158 ], rcx
mov [ rsp + 0x160 ], r14
mulx r14, rcx, [ rsi + 0x20 ]
test al, al
adox rdi, r8
mov rdx, r15
adox rdx, r12
mov r12, r10
shrd r12, r13, 56
mov r13, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x168 ], rdi
mov [ rsp + 0x170 ], r12
mulx r12, rdi, [ rsi + 0x18 ]
mov rdx, 0x38 
mov [ rsp + 0x178 ], r13
bzhi r13, r9, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x180 ], r13
mulx r13, r9, [ rsi + 0x10 ]
mov rdx, 0x38 
mov [ rsp + 0x188 ], r13
bzhi r13, r10, rdx
adox rbp, rcx
adox r14, [ rsp + 0x160 ]
mov r10, [ rsp + 0xe8 ]
test al, al
adox r10, [ rsp + 0x150 ]
mov rcx, [ rsp + 0xe0 ]
adox rcx, [ rsp + 0x148 ]
mov rdx, [ rsp + 0x120 ]
adcx rdx, [ rsp + 0x130 ]
mov [ rsp + 0x190 ], r13
mov r13, [ rsp + 0x110 ]
adcx r13, [ rsp + 0x128 ]
mov [ rsp + 0x198 ], r9
xor r9, r9
adox r10, r8
adox r15, rcx
mov r8, rdx
mov rdx, [ rax + 0x18 ]
mulx r9, rcx, [ rsi + 0x8 ]
adcx rbp, rdi
adcx r12, r14
test al, al
adox r8, [ rsp + 0x40 ]
adox r13, [ rsp + 0x38 ]
adcx r8, [ rsp + 0x198 ]
adcx r13, [ rsp + 0x188 ]
test al, al
adox r8, rcx
adox r9, r13
mov rdx, [ rax + 0x20 ]
mulx r14, rdi, [ rsi + 0x0 ]
adcx r8, rdi
adcx r14, r9
mov rdx, [ rsi + 0x8 ]
mulx r13, rcx, [ rax + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mulx rdi, r9, [ rax + 0x0 ]
xor rdx, rdx
adox r10, rcx
adox r13, r15
adcx r10, [ rsp + 0x20 ]
adcx r13, [ rsp + 0x18 ]
test al, al
adox r10, [ rsp + 0x170 ]
adox r13, rdx
mov r15, r10
shrd r15, r13, 56
mov rcx, rbx
xor r13, r13
adox rcx, [ rsp + 0x108 ]
adox r11, [ rsp + 0x100 ]
mov rdx, [ rax + 0x0 ]
mulx r13, rbx, [ rsi + 0x10 ]
adcx rcx, [ rsp + 0xf8 ]
adcx r11, [ rsp + 0xd0 ]
test al, al
adox rcx, rbx
adox r13, r11
mov rdx, [ rax + 0x8 ]
mulx r11, rbx, [ rsi + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x1a0 ], r14
mov [ rsp + 0x1a8 ], r8
mulx r8, r14, [ rsi + 0x0 ]
adcx rcx, rbx
adcx r11, r13
mov rdx, [ rsi + 0x10 ]
mulx rbx, r13, [ rax + 0x20 ]
xor rdx, rdx
adox rbp, r13
adox rbx, r12
adcx rcx, r14
adcx r8, r11
add rcx, r15
adc r8, 0x0
mov r12, 0xffffffffffffff 
mov r15, rcx
and r15, r12
mov rdx, [ rax + 0x18 ]
mulx r11, r14, [ rsi + 0x10 ]
mov rdx, r9
adox rdx, [ rsp + 0x168 ]
adox rdi, [ rsp + 0x178 ]
shrd rcx, r8, 56
mov r9, rdx
mov rdx, [ rsi + 0x8 ]
mulx r8, r13, [ rax + 0x28 ]
xor rdx, rdx
adox rbp, r13
adox r8, rbx
mov rdx, [ rax + 0x8 ]
mulx r13, rbx, [ rsi + 0x20 ]
add rcx, [ rsp + 0x180 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x1b0 ], r8
mulx r8, r12, [ rsi + 0x18 ]
add r9, rbx
adcx r13, rdi
test al, al
adox r9, r12
adox r8, r13
mov rdx, [ rsp + 0x1a8 ]
adcx rdx, [ rsp + 0x158 ]
mov rdi, [ rsp + 0x1a0 ]
adc rdi, 0x0
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x10 ], r15
mov r15, rdx
mov rdx, [ rax + 0x30 ]
mulx r13, r12, [ rsi + 0x0 ]
mov rdx, 0x38 
bzhi rbx, rcx, rdx
adox r9, r14
adox r11, r8
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x18 ], rbx
test al, al
adox rbp, r12
adox r13, [ rsp + 0x1b0 ]
mov rdx, [ rsi + 0x8 ]
mulx r12, r8, [ rax + 0x20 ]
adcx r9, r8
adcx r12, r11
mov rdx, r15
test al, al
adox rdx, [ rsp + 0xc0 ]
mov rbx, 0x0 
adox rdi, rbx
adcx r9, [ rsp - 0x40 ]
adcx r12, [ rsp - 0x48 ]
mov r15, rdx
shrd r15, rdi, 56
xor r11, r11
adox r9, r15
adox r12, r11
mov rbx, r9
shrd rbx, r12, 56
xor r8, r8
adox rbp, rbx
adox r13, r8
mov r11, rbp
shrd r11, r13, 56
add r11, [ rsp + 0x118 ]
mov rdi, 0xffffffffffffff 
and rbp, rdi
and rdx, rdi
mov r15, r11
shr r15, 56
lea rdx, [ rdx + r15 ]
add r15, [ rsp + 0x190 ]
mov r12, r15
shr r12, 56
shr rcx, 56
and r10, rdi
lea r12, [ r12 + r10 ]
lea rcx, [ rcx + rdx ]
mov rbx, rcx
and rbx, rdi
and r15, rdi
and r9, rdi
mov [ r14 + 0x8 ], r12
and r11, rdi
shr rcx, 56
lea rcx, [ rcx + r9 ]
mov [ r14 + 0x28 ], rcx
mov [ r14 + 0x20 ], rbx
mov [ r14 + 0x30 ], rbp
mov [ r14 + 0x38 ], r11
mov [ r14 + 0x0 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 568
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.0879
; seed 1036085267010077 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5462245 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=90, initial num_batches=31): 142568 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.026100623461598665
; number reverted permutation / tried permutation: 58627 / 90133 =65.045%
; number reverted decision / tried decision: 33917 / 89866 =37.742%
; validated in 3.362s
