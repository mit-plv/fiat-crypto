SECTION .text
	GLOBAL fiat_p521_carry_square
fiat_p521_carry_square:
sub rsp, 552
mov rax, 0x1 
shlx r10, [ rsi + 0x10 ], rax
mov r11, [ rsi + 0x8 ]
mov rdx, r11
shl rdx, 0x1
mov r11, [ rsi + 0x28 ]
lea rcx, [ 4 * r11]
mov r11, rdx
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, rdx
mov rdx, 0x2 
shlx rax, [ rsi + 0x38 ], rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, r10
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x70 ], r12
lea r12, [rdx + rdx]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rax
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, rax
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x48 ], rbp
lea rbp, [ 4 * rdx]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], rbx
mov [ rsp - 0x38 ], r14
mulx r14, rbx, rbp
mov rdx, [ rsi + 0x40 ]
mov [ rsp - 0x30 ], r13
lea r13, [ 4 * rdx]
mov rdx, r13
mov [ rsp - 0x28 ], r12
mulx r12, r13, [ rsi + 0x28 ]
mov [ rsp - 0x20 ], r12
mov [ rsp - 0x18 ], r13
mulx r13, r12, [ rsi + 0x8 ]
mov [ rsp - 0x10 ], r9
mov r9, 0x1 
mov [ rsp - 0x8 ], r8
shlx r8, [ rsi + 0x18 ], r9
xchg rdx, rcx
mov [ rsp + 0x0 ], r8
mulx r8, r9, [ rsi + 0x20 ]
xor rdx, rdx
adox r9, rbx
adox r14, r8
mov rdx, r10
mulx rbx, r10, [ rsi + 0x0 ]
mov rdx, rcx
mulx r8, rcx, [ rsi + 0x10 ]
mov [ rsp + 0x8 ], rbx
mov [ rsp + 0x10 ], r10
mulx r10, rbx, [ rsi + 0x20 ]
mov [ rsp + 0x18 ], r10
mov r10, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x20 ], rbx
mov [ rsp + 0x28 ], r8
mulx r8, rbx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x30 ], r8
lea r8, [rdx + rdx]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x38 ], rbx
mov [ rsp + 0x40 ], rcx
mulx rcx, rbx, r8
adcx r9, r15
adcx rdi, r14
mov rdx, [ rsi + 0x40 ]
mov r15, rdx
shl r15, 0x1
mov rdx, [ rsi + 0x28 ]
mov r14, rdx
shl r14, 0x1
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x48 ], rcx
mov [ rsp + 0x50 ], rbx
mulx rbx, rcx, r14
mov rdx, r15
mov [ rsp + 0x58 ], rbx
mulx rbx, r15, [ rsi + 0x0 ]
test al, al
adox r9, r12
adox r13, rdi
xchg rdx, r10
mulx rdi, r12, [ rsi + 0x38 ]
xchg rdx, r11
mov [ rsp + 0x60 ], rbx
mov [ rsp + 0x68 ], r15
mulx r15, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x70 ], r15
mov [ rsp + 0x78 ], rbx
mulx rbx, r15, rax
adcx r12, [ rsp - 0x8 ]
adcx rdi, [ rsp - 0x10 ]
mov rdx, rbp
mov [ rsp + 0x80 ], r13
mulx r13, rbp, [ rsi + 0x20 ]
mov [ rsp + 0x88 ], r9
mov [ rsp + 0x90 ], rbx
mulx rbx, r9, [ rsi + 0x28 ]
xor rdx, rdx
adox rcx, rbp
adox r13, [ rsp + 0x58 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x98 ], r15
mulx r15, rbp, rax
adcx rcx, rbp
adcx r15, r13
mov rdx, r8
mulx r13, r8, [ rsi + 0x8 ]
xor rbp, rbp
adox r12, [ rsp + 0x50 ]
adox rdi, [ rsp + 0x48 ]
xchg rdx, rax
mov [ rsp + 0xa0 ], r13
mulx r13, rbp, [ rsi + 0x20 ]
adcx r9, rbp
adcx r13, rbx
mov rdx, [ rsi + 0x20 ]
mulx rbp, rbx, rdx
mov rdx, r14
mov [ rsp + 0xa8 ], r8
mulx r8, r14, [ rsi + 0x18 ]
mov [ rsp + 0xb0 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xb8 ], r9
mov [ rsp + 0xc0 ], rdi
mulx rdi, r9, [ rsp + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xc8 ], rdi
mov [ rsp + 0xd0 ], r9
mulx r9, rdi, [ rsp - 0x28 ]
mov rdx, [ rsp - 0x18 ]
mov [ rsp + 0xd8 ], r12
mov r12, rdx
add r12, [ rsp + 0x98 ]
mov [ rsp + 0xe0 ], r15
mov r15, [ rsp - 0x20 ]
adcx r15, [ rsp + 0x90 ]
add rbx, r14
adcx r8, rbp
test al, al
adox rbx, rdi
adox r9, r8
imul rdx, [ rsi + 0x38 ], 0x2
mulx r14, rbp, [ rsi + 0x38 ]
mulx r8, rdi, [ rsi + 0x8 ]
mov [ rsp + 0xe8 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xf0 ], r12
mov [ rsp + 0xf8 ], r14
mulx r14, r12, rdx
mov rdx, r12
add rdx, [ rsp + 0x88 ]
adcx r14, [ rsp + 0x80 ]
xor r12, r12
adox rbx, rdi
adox r8, r9
mov r9, rdx
mov rdx, [ rsi + 0x30 ]
mulx r12, rdi, [ rsp - 0x28 ]
mov rdx, r15
mov [ rsp + 0x100 ], r8
mulx r8, r15, [ rsi + 0x0 ]
adcx rdi, [ rsp - 0x30 ]
adcx r12, [ rsp - 0x38 ]
mov rdx, 0x3ffffffffffffff 
mov [ rsp + 0x108 ], rbx
mov rbx, r9
and rbx, rdx
shrd r9, r14, 58
shr r14, 58
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x110 ], rbx
mov [ rsp + 0x118 ], r8
mulx r8, rbx, r13
xor rdx, rdx
adox rcx, [ rsp + 0x40 ]
mov [ rsp + 0x120 ], r15
mov r15, [ rsp + 0xe0 ]
adox r15, [ rsp + 0x28 ]
mov rdx, r11
mov [ rsp + 0x128 ], r12
mulx r12, r11, [ rsi + 0x30 ]
mov [ rsp + 0x130 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x138 ], r8
mov [ rsp + 0x140 ], rbx
mulx rbx, r8, r10
adcx rbp, r11
adcx r12, [ rsp + 0xf8 ]
xor rdx, rdx
adox rcx, [ rsp + 0x78 ]
adox r15, [ rsp + 0x70 ]
mov rdx, [ rsi + 0x8 ]
mulx r11, r10, r13
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x148 ], r12
mov [ rsp + 0x150 ], rbp
mulx rbp, r12, rax
adcx r8, r12
adcx rbp, rbx
mov rdx, r10
test al, al
adox rdx, [ rsp + 0xd8 ]
adox r11, [ rsp + 0xc0 ]
adcx rcx, r9
adcx r14, r15
mov r9, 0x3a 
bzhi rbx, rcx, r9
adox r8, [ rsp + 0x140 ]
adox rbp, [ rsp + 0x138 ]
mov r15, [ rsp + 0x20 ]
mov r10, r15
add r10, [ rsp + 0x130 ]
mov r12, [ rsp + 0x18 ]
adcx r12, [ rsp + 0x128 ]
xchg rdx, rdi
mulx r9, r15, [ rsi + 0x18 ]
xor rdx, rdx
adox r10, [ rsp - 0x40 ]
adox r12, [ rsp - 0x48 ]
mov [ rsp + 0x158 ], rbx
mov rbx, [ rsp + 0x38 ]
mov [ rsp + 0x160 ], r11
mov r11, rbx
adcx r11, [ rsp + 0xf0 ]
mov [ rsp + 0x168 ], rdi
mov rdi, [ rsp + 0x30 ]
adcx rdi, [ rsp + 0xe8 ]
mov rdx, [ rsp + 0x0 ]
mov [ rsp + 0x170 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
add r11, [ rsp + 0xd0 ]
adcx rdi, [ rsp + 0xc8 ]
mov [ rsp + 0x178 ], r8
mov [ rsp + 0x180 ], rdi
mulx rdi, r8, [ rsi + 0x10 ]
xor rdx, rdx
adox r10, rbx
adox rbp, r12
mov r12, r8
adcx r12, [ rsp + 0x150 ]
adcx rdi, [ rsp + 0x148 ]
mov rdx, rax
mulx rbx, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x188 ], rdi
mulx rdi, r8, [ rsp - 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x190 ], r12
mov [ rsp + 0x198 ], rbp
mulx rbp, r12, rdx
mov rdx, r15
add rdx, [ rsp + 0xb8 ]
adcx r9, [ rsp + 0xb0 ]
xor r15, r15
adox r11, rax
adox rbx, [ rsp + 0x180 ]
adcx rdx, r12
adcx rbp, r9
xor rax, rax
adox rdx, [ rsp + 0x10 ]
adox rbp, [ rsp + 0x8 ]
mov r15, r8
adcx r15, [ rsp + 0x178 ]
adcx rdi, [ rsp + 0x170 ]
shrd rcx, r14, 58
shr r14, 58
test al, al
adox r15, [ rsp + 0x120 ]
adox rdi, [ rsp + 0x118 ]
adcx rdx, rcx
adcx r14, rbp
mov r8, rdx
shrd r8, r14, 58
shr r14, 58
mov r12, 0x3a 
bzhi r9, rdx, r12
mov rdx, [ rsi + 0x0 ]
mulx rcx, rbp, r13
adox r10, r8
adox r14, [ rsp + 0x198 ]
mov rdx, [ rsp - 0x28 ]
mulx r8, r13, [ rsi + 0x0 ]
mov rdx, r10
shrd rdx, r14, 58
shr r14, 58
mov r12, [ rsp + 0x190 ]
mov [ rsp + 0x1a0 ], r9
xor r9, r9
adox r12, [ rsp + 0xa8 ]
mov rax, [ rsp + 0x188 ]
adox rax, [ rsp + 0xa0 ]
adcx r11, rdx
adcx r14, rbx
mov rbx, r11
shrd rbx, r14, 58
shr r14, 58
test al, al
adox r12, rbp
adox rcx, rax
mov rbp, 0x3a 
bzhi rdx, r10, rbp
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x18 ], rdx
adox r12, rbx
adox r14, rcx
mov rax, r12
shrd rax, r14, 58
shr r14, 58
bzhi rbx, r12, rbp
mov rcx, r13
adox rcx, [ rsp + 0x168 ]
adox r8, [ rsp + 0x160 ]
mov r13, [ rsp + 0x68 ]
mov rdx, r13
xor r12, r12
adox rdx, [ rsp + 0x108 ]
mov r9, [ rsp + 0x60 ]
adox r9, [ rsp + 0x100 ]
mov [ r10 + 0x28 ], rbx
adcx rcx, rax
adcx r14, r8
mov r13, rcx
shrd r13, r14, 58
shr r14, 58
add r15, r13
adcx r14, rdi
mov rdi, r15
shrd rdi, r14, 58
shr r14, 58
xor rax, rax
adox rdx, rdi
adox r14, r9
mov r12, 0x39 
bzhi rbx, rdx, r12
shrd rdx, r14, 57
shr r14, 57
add rdx, [ rsp + 0x110 ]
adc r14, 0x0
mov r8, rdx
shrd r8, r14, 58
add r8, [ rsp + 0x158 ]
bzhi r9, rdx, rbp
bzhi r13, r15, rbp
mov [ r10 + 0x40 ], rbx
mov [ r10 + 0x38 ], r13
bzhi r15, r8, rbp
shr r8, 58
add r8, [ rsp + 0x1a0 ]
bzhi rdi, rcx, rbp
mov [ r10 + 0x10 ], r8
bzhi rcx, r11, rbp
mov [ r10 + 0x30 ], rdi
mov [ r10 + 0x0 ], r9
mov [ r10 + 0x20 ], rcx
mov [ r10 + 0x8 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 552
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.0535
; seed 0209461109838868 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 34075 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=67, initial num_batches=31): 974 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.028584005869405724
; number reverted permutation / tried permutation: 309 / 517 =59.768%
; number reverted decision / tried decision: 251 / 482 =52.075%
; validated in 2.643s
