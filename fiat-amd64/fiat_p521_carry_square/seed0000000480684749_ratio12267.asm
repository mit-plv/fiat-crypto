SECTION .text
	GLOBAL fiat_p521_carry_square
fiat_p521_carry_square:
sub rsp, 480
mov rax, 0x2 
shlx r10, [ rsi + 0x38 ], rax
mov r11, [ rsi + 0x10 ]
lea rdx, [r11 + r11]
mov r11, [ rsi + 0x30 ]
lea rcx, [r11 + r11]
mov r11, 0x1 
shlx r8, [ rsi + 0x20 ], r11
xchg rdx, r8
mulx r11, r9, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
shlx rbx, [ rsi + 0x30 ], rax
mov [ rsp - 0x78 ], rbp
imul rbp, [ rsi + 0x18 ], 0x2
mov [ rsp - 0x70 ], r12
mov r12, [ rsi + 0x40 ]
mov [ rsp - 0x68 ], r13
lea r13, [ 4 * r12]
mov r12, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, r13
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, rax, rcx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], r11
mov [ rsp - 0x40 ], r9
mulx r9, r11, r13
imul rdx, [ rsi + 0x28 ], 0x4
mov [ rsp - 0x38 ], rbp
imul rbp, [ rsi + 0x28 ], 0x2
mov [ rsp - 0x30 ], r15
mov r15, 0x1 
mov [ rsp - 0x28 ], r14
shlx r14, [ rsi + 0x8 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x20 ], rdi
mov [ rsp - 0x18 ], rax
mulx rax, rdi, rbp
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], rax
mov [ rsp - 0x8 ], rdi
mulx rdi, rax, rdx
mov rdx, r8
mov [ rsp + 0x0 ], rdi
mulx rdi, r8, [ rsi + 0x0 ]
xchg rdx, rcx
mov [ rsp + 0x8 ], rax
mov [ rsp + 0x10 ], rdi
mulx rdi, rax, [ rsi + 0x0 ]
xchg rdx, rbp
mov [ rsp + 0x18 ], rdi
mov [ rsp + 0x20 ], rax
mulx rax, rdi, [ rsi + 0x28 ]
mov [ rsp + 0x28 ], r8
mov r8, [ rsi + 0x38 ]
mov [ rsp + 0x30 ], r14
lea r14, [r8 + r8]
mov [ rsp + 0x38 ], r9
mulx r9, r8, [ rsi + 0x0 ]
mov [ rsp + 0x40 ], r9
mov r9, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x48 ], r8
mov [ rsp + 0x50 ], r11
mulx r11, r8, r14
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x58 ], r11
mov [ rsp + 0x60 ], r8
mulx r8, r11, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x68 ], r8
mov [ rsp + 0x70 ], r11
mulx r11, r8, rbx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x78 ], r11
mov [ rsp + 0x80 ], r8
mulx r8, r11, r12
mov rdx, r12
mov [ rsp + 0x88 ], r8
mulx r8, r12, [ rsi + 0x0 ]
xchg rdx, r10
mov [ rsp + 0x90 ], r8
mov [ rsp + 0x98 ], r12
mulx r12, r8, [ rsi + 0x28 ]
mov [ rsp + 0xa0 ], r11
mov [ rsp + 0xa8 ], r12
mulx r12, r11, [ rsi + 0x30 ]
xchg rdx, r9
mov [ rsp + 0xb0 ], r12
mov [ rsp + 0xb8 ], r11
mulx r11, r12, [ rsi + 0x18 ]
mov [ rsp + 0xc0 ], r8
mov r8, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xc8 ], rax
mov [ rsp + 0xd0 ], rdi
mulx rdi, rax, rdx
mov rdx, r8
mov [ rsp + 0xd8 ], r15
mulx r15, r8, [ rsi + 0x10 ]
test al, al
adox rax, r12
adox r11, rdi
mov rdx, r14
mulx r12, r14, [ rsi + 0x38 ]
xchg rdx, r13
mov [ rsp + 0xe0 ], r11
mulx r11, rdi, [ rsi + 0x30 ]
adcx r14, rdi
adcx r11, r12
xchg rdx, rbx
mulx rdi, r12, [ rsi + 0x20 ]
mov [ rsp + 0xe8 ], rax
mov [ rsp + 0xf0 ], r15
mulx r15, rax, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xf8 ], r8
mov [ rsp + 0x100 ], r11
mulx r11, r8, r10
mov rdx, [ rsp + 0xd8 ]
mov [ rsp + 0x108 ], r11
mulx r11, r10, [ rsi + 0x20 ]
xor rdx, rdx
adox r10, rax
adox r15, r11
mov rdx, [ rsi + 0x10 ]
mulx r11, rax, r9
mov rdx, r12
adcx rdx, [ rsp + 0xd0 ]
adcx rdi, [ rsp + 0xc8 ]
mov r12, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x110 ], r8
mov [ rsp + 0x118 ], r14
mulx r14, r8, r9
test al, al
adox r10, rax
adox r11, r15
adcx r12, r8
adcx r14, rdi
mov rdx, r9
mulx r15, r9, [ rsi + 0x20 ]
xor rdx, rdx
adox r12, [ rsp + 0x50 ]
adox r14, [ rsp + 0x38 ]
mov rax, r9
adcx rax, [ rsp + 0x80 ]
adcx r15, [ rsp + 0x78 ]
mov rdx, [ rsi + 0x18 ]
mulx r8, rdi, rbx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x120 ], r14
mulx r14, r9, rbx
xor rdx, rdx
adox r10, r9
adox r14, r11
adcx r10, [ rsp + 0x70 ]
adcx r14, [ rsp + 0x68 ]
mov r11, 0x3a 
bzhi r9, r10, r11
shrd r10, r14, 58
shr r14, 58
mov rdx, [ rsp + 0x30 ]
mov [ rsp + 0x128 ], r9
mulx r9, r11, [ rsi + 0x0 ]
test al, al
adox rax, rdi
adox r8, r15
adcx r12, r11
adcx r9, [ rsp + 0x120 ]
xor rdx, rdx
adox r12, r10
adox r14, r9
mov r15, [ rsp + 0xc0 ]
mov rdi, r15
adcx rdi, [ rsp - 0x18 ]
mov r10, [ rsp + 0xa8 ]
adcx r10, [ rsp - 0x20 ]
mov rdx, [ rsi + 0x8 ]
mulx r11, r15, rdx
mov rdx, r12
shrd rdx, r14, 58
shr r14, 58
xor r9, r9
adox rax, r15
adox r11, r8
adcx rax, [ rsp + 0x28 ]
adcx r11, [ rsp + 0x10 ]
test al, al
adox rax, rdx
adox r14, r11
mov rdx, rbx
mulx r8, rbx, [ rsi + 0x38 ]
adcx rbx, [ rsp + 0x8 ]
adcx r8, [ rsp + 0x0 ]
mov r15, rdx
mov rdx, [ rsi + 0x8 ]
mulx r9, r11, rcx
add rdi, [ rsp - 0x28 ]
adcx r10, [ rsp - 0x30 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x130 ], r14
mulx r14, rcx, [ rsp - 0x38 ]
add rdi, r11
adcx r9, r10
mov rdx, [ rsi + 0x40 ]
lea r11, [rdx + rdx]
xor rdx, rdx
adox rbx, [ rsp + 0xa0 ]
adox r8, [ rsp + 0x88 ]
adcx rdi, rcx
adcx r14, r9
mov r10, [ rsp + 0x130 ]
mov rcx, rax
shrd rcx, r10, 58
shr r10, 58
xor r9, r9
adox rdi, rcx
adox r10, r14
mov rdx, [ rsi + 0x28 ]
mulx rcx, r14, r15
mov rdx, rdi
shrd rdx, r10, 58
shr r10, 58
mov r15, 0x3ffffffffffffff 
and rdi, r15
mov r9, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x138 ], rdi
mulx rdi, r15, [ rsp - 0x38 ]
mov rdx, 0x3a 
mov [ rsp + 0x140 ], r8
bzhi r8, rax, rdx
mov rax, r14
adox rax, [ rsp + 0xb8 ]
adox rcx, [ rsp + 0xb0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x148 ], r8
mulx r8, r14, r11
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x150 ], r8
mov [ rsp + 0x158 ], r14
mulx r14, r8, rdx
test al, al
adox rax, r8
adox r14, rcx
mov rdx, r15
adcx rdx, [ rsp + 0x118 ]
adcx rdi, [ rsp + 0x100 ]
mov r15, rdx
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, [ rsp - 0x38 ]
xor rdx, rdx
adox rax, rcx
adox r8, r14
adcx rax, [ rsp + 0x98 ]
adcx r8, [ rsp + 0x90 ]
xor r14, r14
adox rax, r9
adox r10, r8
mov rdx, [ rsi + 0x40 ]
mulx rcx, r9, r11
adcx r9, [ rsp + 0x110 ]
adcx rcx, [ rsp + 0x108 ]
mov rdx, 0x3ffffffffffffff 
mov r11, rax
and r11, rdx
adox r15, [ rsp - 0x40 ]
adox rdi, [ rsp - 0x48 ]
mov rdx, [ rsi + 0x8 ]
mulx r14, r8, r13
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x20 ], r11
adcx r9, [ rsp + 0xf8 ]
adcx rcx, [ rsp + 0xf0 ]
shrd rax, r10, 58
shr r10, 58
test al, al
adox r15, [ rsp + 0x48 ]
adox rdi, [ rsp + 0x40 ]
adcx r15, rax
adcx r10, rdi
xchg rdx, rbp
mulx r11, r13, [ rsi + 0x8 ]
mulx rdi, rax, [ rsi + 0x10 ]
test al, al
adox rbx, [ rsp - 0x8 ]
mov rdx, [ rsp - 0x10 ]
adox rdx, [ rsp + 0x140 ]
adcx rbx, [ rsp + 0x20 ]
adcx rdx, [ rsp + 0x18 ]
mov rbp, r15
shrd rbp, r10, 58
shr r10, 58
add rbx, rbp
adcx r10, rdx
mov rdx, 0x3ffffffffffffff 
mov rbp, rbx
and rbp, rdx
shrd rbx, r10, 58
shr r10, 58
mov rdx, rax
add rdx, [ rsp + 0xe8 ]
adcx rdi, [ rsp + 0xe0 ]
xor rax, rax
adox rdx, r8
adox r14, rdi
adcx r9, r13
adcx r11, rcx
test al, al
adox r9, [ rsp + 0x60 ]
adox r11, [ rsp + 0x58 ]
adcx r9, rbx
adcx r10, r11
mov r8, 0x3ffffffffffffff 
mov rcx, r9
and rcx, r8
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x30 ], rbp
and r15, r8
adox rdx, [ rsp + 0x158 ]
adox r14, [ rsp + 0x150 ]
mov [ r13 + 0x38 ], rcx
shrd r9, r10, 58
shr r10, 58
test al, al
adox rdx, r9
adox r10, r14
mov rbp, 0x1ffffffffffffff 
mov rbx, rdx
and rbx, rbp
mov [ r13 + 0x40 ], rbx
shrd rdx, r10, 57
shr r10, 57
test al, al
adox rdx, [ rsp + 0x128 ]
adox r10, rax
mov rdi, rdx
and rdi, r8
mov [ r13 + 0x0 ], rdi
shrd rdx, r10, 58
and r12, r8
lea rdx, [ rdx + r12 ]
mov r11, rdx
and r11, r8
mov [ r13 + 0x8 ], r11
shr rdx, 58
mov rcx, [ rsp + 0x138 ]
mov [ r13 + 0x18 ], rcx
add rdx, [ rsp + 0x148 ]
mov [ r13 + 0x28 ], r15
mov [ r13 + 0x10 ], rdx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 480
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.2267
; seed 0914328038201571 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3282378 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=108, initial num_batches=31): 113346 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.03453167185497831
; number reverted permutation / tried permutation: 63108 / 89869 =70.222%
; number reverted decision / tried decision: 52338 / 90130 =58.069%
; validated in 1.912s
