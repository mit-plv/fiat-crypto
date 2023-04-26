SECTION .text
	GLOBAL fiat_p521_carry_square
fiat_p521_carry_square:
sub rsp, 488
imul rax, [ rsi + 0x40 ], 0x4
mov rdx, [ rsi + 0x8 ]
mulx r11, r10, rdx
mov rdx, [ rsi + 0x20 ]
mov rcx, rdx
shl rcx, 0x1
mov rdx, [ rsi + 0x40 ]
lea r8, [rdx + rdx]
mov rdx, [ rsi + 0x38 ]
mov r9, rdx
shl r9, 0x2
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x80 ], rbx
mov rbx, rdx
shl rbx, 0x2
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rdx
mov rdx, rbx
mov [ rsp - 0x68 ], r13
mulx r13, rbx, [ rsi + 0x28 ]
mov [ rsp - 0x60 ], r14
mov r14, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, rdx
mov rdx, rax
mov [ rsp - 0x48 ], rdi
mulx rdi, rax, [ rsi + 0x30 ]
mov [ rsp - 0x40 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x38 ], r11
mov [ rsp - 0x30 ], r10
mulx r10, r11, r9
imul rdx, [ rsi + 0x30 ], 0x2
mov [ rsp - 0x28 ], r10
mov r10, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x20 ], r11
mov [ rsp - 0x18 ], r12
mulx r12, r11, r15
mov rdx, rcx
mov [ rsp - 0x10 ], r12
mulx r12, rcx, [ rsi + 0x10 ]
mov [ rsp - 0x8 ], r12
mov r12, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x0 ], rcx
mov [ rsp + 0x8 ], r11
mulx r11, rcx, r15
mov rdx, 0x1 
mov [ rsp + 0x10 ], r11
shlx r11, [ rsi + 0x28 ], rdx
mov rdx, r11
mov [ rsp + 0x18 ], rcx
mulx rcx, r11, [ rsi + 0x18 ]
xchg rdx, r9
mov [ rsp + 0x20 ], rbp
mov [ rsp + 0x28 ], rdi
mulx rdi, rbp, [ rsi + 0x20 ]
xchg rdx, r9
mov [ rsp + 0x30 ], rax
mov [ rsp + 0x38 ], r10
mulx r10, rax, [ rsi + 0x28 ]
mov [ rsp + 0x40 ], r10
xor r10, r10
adox rbx, rbp
adox rdi, r13
mov r13, [ rsi + 0x38 ]
mov rbp, r13
shl rbp, 0x1
mov r13, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x48 ], rdi
mulx rdi, r10, r14
mov rdx, r13
mov [ rsp + 0x50 ], rbx
mulx rbx, r13, [ rsi + 0x0 ]
mov [ rsp + 0x58 ], rbx
mov rbx, [ rsi + 0x10 ]
mov [ rsp + 0x60 ], r13
mov r13, rbx
shl r13, 0x1
mov rbx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x68 ], r13
mov [ rsp + 0x70 ], rax
mulx rax, r13, rdx
mov rdx, rbp
mov [ rsp + 0x78 ], rdi
mulx rdi, rbp, [ rsi + 0x8 ]
xchg rdx, r8
mov [ rsp + 0x80 ], rdi
mov [ rsp + 0x88 ], rbp
mulx rbp, rdi, [ rsi + 0x40 ]
mov [ rsp + 0x90 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x98 ], rdi
mov [ rsp + 0xa0 ], r10
mulx r10, rdi, r8
xor rdx, rdx
adox r13, r11
adox rcx, rax
mov r11, 0x1 
shlx rax, [ rsi + 0x18 ], r11
imul rdx, [ rsi + 0x8 ], 0x2
mov r11, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xa8 ], rcx
mov [ rsp + 0xb0 ], r13
mulx r13, rcx, r14
mov rdx, r11
mulx r14, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xb8 ], r10
mov r10, rdx
shl r10, 0x2
mov rdx, r10
mov [ rsp + 0xc0 ], rdi
mulx rdi, r10, [ rsi + 0x20 ]
mov rdx, r9
mov [ rsp + 0xc8 ], rax
mulx rax, r9, [ rsi + 0x30 ]
mov [ rsp + 0xd0 ], rax
mov rax, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xd8 ], r9
mov [ rsp + 0xe0 ], r14
mulx r14, r9, [ rsp + 0x38 ]
mov rdx, r8
mov [ rsp + 0xe8 ], r14
mulx r14, r8, [ rsi + 0x38 ]
test al, al
adox r10, [ rsp + 0xa0 ]
adox rdi, [ rsp + 0x78 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xf0 ], r9
mov [ rsp + 0xf8 ], r11
mulx r11, r9, rax
adcx r8, [ rsp + 0x30 ]
adcx r14, [ rsp + 0x28 ]
xor rdx, rdx
adox r10, r9
adox r11, rdi
mov rdx, r15
mulx rdi, r15, [ rsi + 0x8 ]
adcx r10, r15
adcx rdi, r11
xor r9, r9
adox r10, [ rsp + 0x20 ]
adox rdi, [ rsp - 0x18 ]
mov r11, rcx
adcx r11, [ rsp + 0x70 ]
adcx r13, [ rsp + 0x40 ]
mov rcx, rdx
mov rdx, [ rsi + 0x18 ]
mulx r9, r15, rax
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x100 ], r14
mulx r14, rax, rcx
xor rdx, rdx
adox r11, r15
adox r9, r13
adcx r11, [ rsp + 0x8 ]
adcx r9, [ rsp - 0x10 ]
mov r13, rax
xor r15, r15
adox r13, [ rsp + 0x50 ]
adox r14, [ rsp + 0x48 ]
mov rdx, r10
shrd rdx, rdi, 58
shr rdi, 58
test al, al
adox r11, [ rsp + 0xf8 ]
adox r9, [ rsp + 0xe0 ]
adcx r11, rdx
adcx rdi, r9
xor rax, rax
adox r13, [ rsp - 0x30 ]
adox r14, [ rsp - 0x38 ]
mov rdx, [ rsp + 0x68 ]
mulx r9, r15, [ rsi + 0x0 ]
mov rax, r11
shrd rax, rdi, 58
shr rdi, 58
mov [ rsp + 0x108 ], r8
xor r8, r8
adox r13, r15
adox r9, r14
adcx r13, rax
adcx rdi, r9
mulx r15, r14, [ rsi + 0x8 ]
mov rdx, r13
shrd rdx, rdi, 58
shr rdi, 58
mov rax, [ rsp - 0x20 ]
mov r9, rax
test al, al
adox r9, [ rsp + 0xf0 ]
mov [ rsp + 0x110 ], rdi
mov rdi, [ rsp - 0x28 ]
adox rdi, [ rsp + 0xe8 ]
mov rax, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x118 ], r15
mulx r15, r8, rcx
mov rdx, 0x3ffffffffffffff 
and r13, rdx
adox r9, r8
adox r15, rdi
mov rdx, [ rsp + 0xc8 ]
mulx r8, rdi, [ rsi + 0x0 ]
mov [ rsp + 0x120 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x128 ], rax
mov [ rsp + 0x130 ], r8
mulx r8, rax, rcx
mov rdx, rax
adcx rdx, [ rsp + 0xd8 ]
adcx r8, [ rsp + 0xd0 ]
add r9, r14
adcx r15, [ rsp + 0x118 ]
xchg rdx, r13
mulx r14, rcx, [ rsi + 0x8 ]
add r9, rdi
adcx r15, [ rsp + 0x130 ]
test al, al
adox r9, [ rsp + 0x128 ]
adox r15, [ rsp + 0x110 ]
mov rdi, 0x3ffffffffffffff 
mov rax, r9
and rax, rdi
and r10, rdi
mov rdi, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x138 ], rax
mov [ rsp + 0x140 ], r10
mulx r10, rax, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x148 ], r10
mov [ rsp + 0x150 ], rax
mulx rax, r10, rdi
adox r13, [ rsp - 0x40 ]
adox r8, [ rsp - 0x48 ]
adcx r13, rcx
adcx r14, r8
mov rdx, [ rsp + 0x150 ]
mov rdi, rdx
test al, al
adox rdi, [ rsp + 0x18 ]
mov rcx, [ rsp + 0x148 ]
adox rcx, [ rsp + 0x10 ]
mov rdx, r12
mulx r8, r12, [ rsi + 0x0 ]
adcx r13, r12
adcx r8, r14
xor r14, r14
adox rdi, [ rsp + 0x0 ]
adox rcx, [ rsp - 0x8 ]
mulx r14, r12, [ rsi + 0x8 ]
shrd r9, r15, 58
shr r15, 58
mov [ rsp + 0x158 ], rcx
xor rcx, rcx
adox r13, r9
adox r15, r8
mov r8, 0x3ffffffffffffff 
mov r9, r13
and r9, r8
mov r8, r10
adox r8, [ rsp + 0x108 ]
adox rax, [ rsp + 0x100 ]
adcx r8, r12
adcx r14, rax
add r8, [ rsp + 0x60 ]
adcx r14, [ rsp + 0x58 ]
shrd r13, r15, 58
shr r15, 58
xor r10, r10
adox r8, r13
adox r15, r14
mov rcx, rdx
mov rdx, [ rsi + 0x8 ]
mulx rax, r12, rbx
adcx rdi, r12
adcx rax, [ rsp + 0x158 ]
mov rdx, [ rsi + 0x0 ]
mulx r13, r14, rbp
mov rdx, rbx
mulx rbp, rbx, [ rsi + 0x10 ]
mov rdx, [ rsp + 0x38 ]
mulx r10, r12, [ rsi + 0x0 ]
mov [ rsp + 0x160 ], r9
mov r9, r8
shrd r9, r15, 58
shr r15, 58
test al, al
adox rdi, r12
adox r10, rax
xchg rdx, rcx
mulx r12, rax, [ rsi + 0x18 ]
adcx rdi, r9
adcx r15, r10
mov rdx, rax
xor r9, r9
adox rdx, [ rsp + 0x98 ]
adox r12, [ rsp + 0x90 ]
mov r10, rdi
shrd r10, r15, 58
shr r15, 58
xor rax, rax
adox rdx, rbx
adox rbp, r12
mov r9, rdx
mov rdx, [ rsi + 0x8 ]
mulx r12, rbx, rcx
adcx r9, rbx
adcx r12, rbp
xor rdx, rdx
adox r9, [ rsp + 0xc0 ]
adox r12, [ rsp + 0xb8 ]
mov rax, 0x3a 
bzhi rbp, r8, rax
adox r9, r10
adox r15, r12
bzhi r8, r9, rax
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x38 ], r8
mov rdx, rcx
mulx rbx, rcx, [ rsi + 0x10 ]
mov rdx, rcx
adox rdx, [ rsp + 0xb0 ]
adox rbx, [ rsp + 0xa8 ]
shrd r9, r15, 58
shr r15, 58
xor r12, r12
adox rdx, [ rsp + 0x88 ]
adox rbx, [ rsp + 0x80 ]
adcx rdx, r14
adcx r13, rbx
xor r14, r14
adox rdx, r9
adox r15, r13
mov r12, 0x39 
bzhi r8, rdx, r12
shrd rdx, r15, 57
shr r15, 57
test al, al
adox rdx, [ rsp + 0x140 ]
adox r15, r14
bzhi rcx, r11, rax
mov [ r10 + 0x40 ], r8
mov r11, rdx
shrd r11, r15, 58
mov r9, [ rsp + 0x138 ]
mov [ r10 + 0x18 ], r9
lea r11, [ r11 + rcx ]
bzhi r9, rdi, rax
mov rdi, r11
shr rdi, 58
bzhi rbx, r11, rax
mov [ r10 + 0x8 ], rbx
mov [ r10 + 0x30 ], r9
mov r13, [ rsp + 0x160 ]
mov [ r10 + 0x20 ], r13
bzhi r13, rdx, rax
mov [ r10 + 0x28 ], rbp
add rdi, [ rsp + 0x120 ]
mov [ r10 + 0x0 ], r13
mov [ r10 + 0x10 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 488
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.1875
; seed 0579142649247609 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3340897 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=98, initial num_batches=31): 108917 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.03260112478774413
; number reverted permutation / tried permutation: 61991 / 89897 =68.958%
; number reverted decision / tried decision: 51316 / 90102 =56.953%
; validated in 1.994s
