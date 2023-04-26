SECTION .text
	GLOBAL fiat_p448_solinas_carry_square
fiat_p448_solinas_carry_square:
sub rsp, 544
mov rax, [ rsi + 0x30 ]
lea r10, [rax + rax]
mov rax, [ rsi + 0x20 ]
mov r11, rax
shl r11, 0x1
mov rax, 0x1 
shlx rdx, [ rsi + 0x10 ], rax
mov rcx, rdx
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, rax, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rdx
imul rdx, [ rsi + 0x38 ], 0x2
mov [ rsp - 0x58 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r9
mulx r9, rdi, rcx
mov rdx, r15
mov [ rsp - 0x40 ], r9
mulx r9, r15, [ rsi + 0x8 ]
xchg rdx, r11
mov [ rsp - 0x38 ], rdi
mov [ rsp - 0x30 ], r8
mulx r8, rdi, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], r8
mov r8, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x20 ], rdi
mov [ rsp - 0x18 ], r9
mulx r9, rdi, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x10 ], r15
mov [ rsp - 0x8 ], rbx
mulx rbx, r15, r8
mov rdx, r8
mov [ rsp + 0x0 ], rbx
mulx rbx, r8, [ rsi + 0x18 ]
mov [ rsp + 0x8 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x10 ], rax
mov [ rsp + 0x18 ], r14
mulx r14, rax, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x20 ], r14
mov [ rsp + 0x28 ], rax
mulx rax, r14, r10
mov rdx, r11
mov [ rsp + 0x30 ], rax
mulx rax, r11, [ rsi + 0x28 ]
xchg rdx, r10
mov [ rsp + 0x38 ], r14
mov [ rsp + 0x40 ], r13
mulx r13, r14, [ rsi + 0x0 ]
mov [ rsp + 0x48 ], r13
mov r13, rdi
test al, al
adox r13, r11
mov [ rsp + 0x50 ], r14
mov r14, rax
adox r14, r9
mov [ rsp + 0x58 ], rbx
imul rbx, [ rsi + 0x18 ], 0x2
xchg rdx, rbx
mov [ rsp + 0x60 ], r8
mov [ rsp + 0x68 ], r12
mulx r12, r8, [ rsi + 0x0 ]
mov [ rsp + 0x70 ], r12
mov r12, r13
mov [ rsp + 0x78 ], r8
xor r8, r8
adox r12, rdi
adox r9, r14
mulx r8, rdi, [ rsi + 0x10 ]
adcx r12, r11
adcx rax, r9
mov r11, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x80 ], r8
mulx r8, r9, r15
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x88 ], rdi
mulx rdi, r15, rdx
mov rdx, r10
mov [ rsp + 0x90 ], r8
mulx r8, r10, [ rsi + 0x18 ]
mov [ rsp + 0x98 ], r9
mov r9, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xa0 ], rdi
mov [ rsp + 0xa8 ], r15
mulx r15, rdi, r11
add r13, rbp
adcx r14, [ rsp + 0x68 ]
imul rdx, [ rsi + 0x28 ], 0x2
mov r11, [ rsi + 0x8 ]
mov [ rsp + 0xb0 ], r15
lea r15, [r11 + r11]
mov [ rsp + 0xb8 ], r15
mulx r15, r11, [ rsi + 0x0 ]
xchg rdx, r9
mov [ rsp + 0xc0 ], r15
mov [ rsp + 0xc8 ], r11
mulx r11, r15, [ rsi + 0x30 ]
xchg rdx, rbx
mov [ rsp + 0xd0 ], rdi
mov [ rsp + 0xd8 ], r8
mulx r8, rdi, [ rsi + 0x20 ]
xchg rdx, r9
mov [ rsp + 0xe0 ], r10
mov [ rsp + 0xe8 ], r8
mulx r8, r10, [ rsi + 0x8 ]
mov [ rsp + 0xf0 ], r8
mov r8, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xf8 ], r10
mov [ rsp + 0x100 ], rdi
mulx rdi, r10, rcx
mov rdx, r15
xor rcx, rcx
adox rdx, r15
mov [ rsp + 0x108 ], r14
mov r14, r11
adox r14, r11
mov rcx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x110 ], r14
mov [ rsp + 0x118 ], r13
mulx r13, r14, rbx
mov rdx, r9
mov [ rsp + 0x120 ], rcx
mulx rcx, r9, [ rsi + 0x28 ]
adcx r9, r14
adcx r13, rcx
mov r14, r9
add r14, [ rsp + 0x60 ]
mov rcx, r13
adcx rcx, [ rsp + 0x58 ]
mov [ rsp + 0x128 ], rcx
xor rcx, rcx
adox r9, r10
adox rdi, r13
adcx r12, rbp
adcx rax, [ rsp + 0x68 ]
mov rbp, rdx
mov rdx, [ rsi + 0x18 ]
mulx r13, r10, r8
add r12, r10
mov rdx, r13
adcx rdx, rax
mov rax, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x130 ], r12
mulx r12, rcx, r8
add r14, rcx
adcx r12, [ rsp + 0x128 ]
xor rdx, rdx
adox r9, [ rsp + 0x78 ]
adox rdi, [ rsp + 0x70 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x138 ], rax
mulx rax, rcx, rbp
mov rdx, r10
adcx rdx, [ rsp + 0x118 ]
adcx r13, [ rsp + 0x108 ]
mov r10, r9
shrd r10, rdi, 56
mov rdi, [ rsp + 0x40 ]
mov [ rsp + 0x140 ], r13
mov r13, rdi
test al, al
adox r13, rdi
mov [ rsp + 0x148 ], rdx
mov rdx, [ rsp + 0x18 ]
mov [ rsp + 0x150 ], r10
mov r10, rdx
adox r10, rdx
adcx r13, [ rsp + 0x10 ]
adcx r10, [ rsp - 0x8 ]
add r13, [ rsp + 0x100 ]
adcx r10, [ rsp + 0xe8 ]
mov [ rsp + 0x158 ], r10
xor r10, r10
adox r14, rcx
adox rax, r12
adcx rdi, [ rsp + 0x10 ]
adcx rdx, [ rsp - 0x8 ]
test al, al
adox rdi, [ rsp + 0x100 ]
adox rdx, [ rsp + 0xe8 ]
adcx r13, [ rsp + 0xe0 ]
mov r12, [ rsp + 0x158 ]
adcx r12, [ rsp + 0xd8 ]
mov rcx, 0xffffffffffffff 
and r9, rcx
adox rdi, [ rsp + 0xe0 ]
adox rdx, [ rsp + 0xd8 ]
adcx r13, [ rsp + 0x28 ]
adcx r12, [ rsp + 0x20 ]
mov r10, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x160 ], r9
mulx r9, rcx, rbx
mov rdx, r8
mov [ rsp + 0x168 ], r10
mulx r10, r8, [ rsi + 0x20 ]
xor rdx, rdx
adox r14, rcx
adox r9, rax
mov rdx, rbp
mulx rax, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x170 ], rdi
mulx rdi, rcx, rbx
adcx r13, [ rsp + 0x8 ]
adcx r12, [ rsp + 0x0 ]
mov rdx, r14
shrd rdx, r9, 56
add r15, r8
mov rbx, r10
adcx rbx, r11
mov r11, rbp
xor r9, r9
adox r11, [ rsp + 0x130 ]
mov [ rsp + 0x178 ], rdx
mov rdx, rax
adox rdx, [ rsp + 0x138 ]
adcx r15, [ rsp + 0x38 ]
adcx rbx, [ rsp + 0x30 ]
test al, al
adox r13, [ rsp + 0xf8 ]
adox r12, [ rsp + 0xf0 ]
adcx r11, [ rsp + 0xa8 ]
adcx rdx, [ rsp + 0xa0 ]
mov [ rsp + 0x180 ], r12
xor r12, r12
adox r11, [ rsp - 0x10 ]
adox rdx, [ rsp - 0x18 ]
adcx r15, rcx
mov r9, rdi
adcx r9, rbx
mov rbx, r8
test al, al
adox rbx, [ rsp + 0x120 ]
adox r10, [ rsp + 0x110 ]
adcx rbx, [ rsp + 0x38 ]
adcx r10, [ rsp + 0x30 ]
test al, al
adox r11, [ rsp + 0xd0 ]
adox rdx, [ rsp + 0xb0 ]
adcx r11, [ rsp + 0x98 ]
adcx rdx, [ rsp + 0x90 ]
mov r8, 0x38 
bzhi r12, r14, r8
adox rbx, rcx
adox rdi, r10
mov r14, [ rsp + 0x170 ]
xor rcx, rcx
adox r14, [ rsp - 0x30 ]
mov r10, [ rsp + 0x168 ]
adox r10, [ rsp - 0x48 ]
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x188 ], r10
mulx r10, r8, rdx
adcx r11, [ rsp + 0x150 ]
adc rcx, 0x0
mov rdx, rbp
mov [ rsp + 0x190 ], r14
xor r14, r14
adox rdx, [ rsp + 0x148 ]
adox rax, [ rsp + 0x140 ]
adcx rdx, [ rsp - 0x10 ]
adcx rax, [ rsp - 0x18 ]
mov rbp, r11
mov [ rsp + 0x198 ], r12
xor r12, r12
adox rbp, [ rsp + 0x178 ]
adox rcx, r12
adcx rdx, r8
adcx r10, rax
mov r14, rdx
add r14, [ rsp + 0x178 ]
adc r10, 0x0
mov r8, r14
shrd r8, r10, 56
mov rdx, [ rsi + 0x0 ]
mulx rax, r11, [ rsp + 0xb8 ]
mov rdx, 0x38 
bzhi r10, rbp, rdx
adox r15, r11
adox rax, r9
add rbx, [ rsp + 0x88 ]
adcx rdi, [ rsp + 0x80 ]
shrd rbp, rcx, 56
add rbx, [ rsp - 0x20 ]
adcx rdi, [ rsp - 0x28 ]
xor r9, r9
adox rbx, [ rsp + 0xc8 ]
adox rdi, [ rsp + 0xc0 ]
adcx r15, r8
adc rax, 0x0
mov r12, r15
shrd r12, rax, 56
bzhi rcx, r15, rdx
adox r13, [ rsp + 0x50 ]
mov r8, [ rsp + 0x48 ]
adox r8, [ rsp + 0x180 ]
xor r11, r11
adox rbx, rbp
adox rdi, r11
mov r9, rbx
shrd r9, rdi, 56
xor rbp, rbp
adox r13, r9
adox r8, rbp
mov r11, r13
shrd r11, r8, 56
add r11, [ rsp + 0x198 ]
mov r15, [ rsp + 0x190 ]
test al, al
adox r15, [ rsp - 0x38 ]
mov rax, [ rsp + 0x188 ]
adox rax, [ rsp - 0x40 ]
adcx r15, r12
adc rax, 0x0
bzhi r12, r11, rdx
mov rdi, r15
shrd rdi, rax, 56
add rdi, [ rsp + 0x160 ]
shr r11, 56
bzhi r9, r14, rdx
bzhi r14, rdi, rdx
lea r10, [ r10 + r11 ]
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x18 ], r14
shr rdi, 56
bzhi rax, rbx, rdx
lea rdi, [ rdi + r10 ]
mov rbx, rdi
shr rbx, 56
lea r9, [ r9 + r11 ]
mov r11, r9
shr r11, 56
bzhi r14, rdi, rdx
mov [ r8 + 0x20 ], r14
lea r11, [ r11 + rcx ]
mov [ r8 + 0x8 ], r11
bzhi rcx, r13, rdx
bzhi r13, r15, rdx
mov [ r8 + 0x10 ], r13
lea rbx, [ rbx + rax ]
mov [ r8 + 0x28 ], rbx
bzhi r15, r9, rdx
mov [ r8 + 0x38 ], r12
mov [ r8 + 0x30 ], rcx
mov [ r8 + 0x0 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 544
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.0390
; seed 0708043470786565 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 20757 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=137, initial num_batches=31): 679 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.032711856241268
; number reverted permutation / tried permutation: 325 / 500 =65.000%
; number reverted decision / tried decision: 266 / 499 =53.307%
; validated in 1.964s
