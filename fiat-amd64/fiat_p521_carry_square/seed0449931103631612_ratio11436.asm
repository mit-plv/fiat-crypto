SECTION .text
	GLOBAL fiat_p521_carry_square
fiat_p521_carry_square:
sub rsp, 552
mov rax, [ rsi + 0x18 ]
lea r10, [rax + rax]
mov rax, [ rsi + 0x8 ]
mov r11, rax
shl r11, 0x1
mov rax, [ rsi + 0x30 ]
mov rdx, rax
shl rdx, 0x2
xchg rdx, r10
mulx rcx, rax, [ rsi + 0x0 ]
mov r8, [ rsi + 0x40 ]
mov r9, r8
shl r9, 0x2
mov r8, 0x1 
mov [ rsp - 0x80 ], rbx
shlx rbx, [ rsi + 0x10 ], r8
mov r8, [ rsi + 0x28 ]
mov [ rsp - 0x78 ], rbp
mov rbp, r8
shl rbp, 0x2
mov r8, 0x1 
mov [ rsp - 0x70 ], r12
shlx r12, [ rsi + 0x38 ], r8
mov [ rsp - 0x68 ], r13
mulx r13, r8, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mov r14, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r9
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x48 ], rcx
lea rcx, [rdx + rdx]
imul rdx, [ rsi + 0x28 ], 0x2
mov [ rsp - 0x40 ], rax
mov rax, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], r11
mov [ rsp - 0x30 ], r12
mulx r12, r11, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], r13
mov [ rsp - 0x20 ], r8
mulx r8, r13, r14
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], r8
mulx r8, r14, rcx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], r13
mov [ rsp - 0x8 ], rbp
mulx rbp, r13, rax
imul rdx, [ rsi + 0x40 ], 0x2
xchg rdx, r9
mov [ rsp + 0x0 ], r8
mov [ rsp + 0x8 ], r14
mulx r14, r8, [ rsi + 0x20 ]
mov [ rsp + 0x10 ], r14
mov r14, [ rsi + 0x38 ]
mov [ rsp + 0x18 ], r8
lea r8, [ 4 * r14]
xchg rdx, r8
mov [ rsp + 0x20 ], r12
mulx r12, r14, [ rsi + 0x20 ]
mov [ rsp + 0x28 ], r11
mov r11, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x30 ], rdi
mov [ rsp + 0x38 ], r15
mulx r15, rdi, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x40 ], rbx
mov [ rsp + 0x48 ], r12
mulx r12, rbx, r9
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x50 ], r12
mov [ rsp + 0x58 ], rbx
mulx rbx, r12, r11
test al, al
adox rdi, r13
adox rbp, r15
mov rdx, [ rsi + 0x18 ]
mulx r15, r13, r11
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x60 ], r15
mov [ rsp + 0x68 ], r13
mulx r13, r15, rcx
mov rdx, r11
mov [ rsp + 0x70 ], r13
mulx r13, r11, [ rsi + 0x10 ]
mov [ rsp + 0x78 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x80 ], r13
mov [ rsp + 0x88 ], r11
mulx r11, r13, rdx
mov rdx, rcx
mov [ rsp + 0x90 ], rbx
mulx rbx, rcx, [ rsi + 0x0 ]
mov [ rsp + 0x98 ], rbx
mov rbx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xa0 ], rcx
mov [ rsp + 0xa8 ], r12
mulx r12, rcx, r8
imul rdx, [ rsi + 0x30 ], 0x2
mov [ rsp + 0xb0 ], r12
mov r12, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xb8 ], rcx
mov [ rsp + 0xc0 ], rbp
mulx rbp, rcx, r8
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xc8 ], rbp
mov [ rsp + 0xd0 ], rcx
mulx rcx, rbp, r10
mov rdx, r8
mov [ rsp + 0xd8 ], rdi
mulx rdi, r8, [ rsi + 0x18 ]
mov [ rsp + 0xe0 ], r11
xor r11, r11
adox rbp, r14
adox rcx, [ rsp + 0x48 ]
adcx rbp, r8
adcx rdi, rcx
mov r14, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r8, r12
mov rdx, r9
mulx r11, r9, [ rsi + 0x40 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xe8 ], rcx
mov [ rsp + 0xf0 ], r8
mulx r8, rcx, rbx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xf8 ], r13
mulx r13, rbx, r12
xor rdx, rdx
adox r9, rcx
adox r8, r11
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsp + 0x40 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x100 ], rcx
mov [ rsp + 0x108 ], r11
mulx r11, rcx, rax
mov rdx, r15
mov [ rsp + 0x110 ], r13
mulx r13, r15, [ rsi + 0x30 ]
adcx r9, rcx
adcx r11, r8
mov rdx, [ rsi + 0x8 ]
mulx rcx, r8, rax
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x118 ], r11
mov [ rsp + 0x120 ], r9
mulx r9, r11, [ rsp + 0x40 ]
xor rdx, rdx
adox r15, [ rsp + 0x38 ]
adox r13, [ rsp + 0x30 ]
adcx rbp, [ rsp + 0x28 ]
adcx rdi, [ rsp + 0x20 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x128 ], rdi
mov [ rsp + 0x130 ], rbp
mulx rbp, rdi, r14
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x138 ], r9
mov [ rsp + 0x140 ], r11
mulx r11, r9, r12
xor rdx, rdx
adox rdi, [ rsp + 0xf8 ]
adox rbp, [ rsp + 0xe0 ]
mov rdx, r12
mov [ rsp + 0x148 ], rbx
mulx rbx, r12, [ rsi + 0x30 ]
adcx rdi, [ rsp + 0x8 ]
adcx rbp, [ rsp + 0x0 ]
xor rdx, rdx
adox rdi, r8
adox rcx, rbp
mov rdx, [ rsi + 0x10 ]
mulx rbp, r8, rdx
mov rdx, r9
adcx rdx, [ rsp + 0xd8 ]
adcx r11, [ rsp + 0xc0 ]
mov r9, rdx
mov rdx, [ rsp - 0x8 ]
mov [ rsp + 0x150 ], r11
mov [ rsp + 0x158 ], rcx
mulx rcx, r11, [ rsi + 0x20 ]
test al, al
adox r15, r8
adox rbp, r13
adcx r15, [ rsp - 0x20 ]
adcx rbp, [ rsp - 0x28 ]
mov rdx, [ rsi + 0x18 ]
mulx r8, r13, r10
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x160 ], rbp
mov [ rsp + 0x168 ], r15
mulx r15, rbp, rax
test al, al
adox r11, r13
adox r8, rcx
adcx r12, [ rsp + 0xa8 ]
adcx rbx, [ rsp + 0x90 ]
add r12, [ rsp + 0x18 ]
adcx rbx, [ rsp + 0x10 ]
mov rdx, r14
mulx rcx, r14, [ rsi + 0x30 ]
test al, al
adox r11, [ rsp + 0x88 ]
adox r8, [ rsp + 0x80 ]
adcx rdi, [ rsp + 0xf0 ]
mov rdx, [ rsp + 0x158 ]
adcx rdx, [ rsp + 0xe8 ]
mov r13, [ rsp + 0x148 ]
mov [ rsp + 0x170 ], rdx
mov rdx, r13
mov [ rsp + 0x178 ], rdi
xor rdi, rdi
adox rdx, [ rsp + 0x120 ]
mov [ rsp + 0x180 ], r9
mov r9, [ rsp + 0x110 ]
adox r9, [ rsp + 0x118 ]
mov r13, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x188 ], r9
mulx r9, rdi, [ rsp - 0x30 ]
adcx rdi, r14
adcx rcx, r9
test al, al
adox r12, [ rsp + 0x140 ]
adox rbx, [ rsp + 0x138 ]
mov rdx, [ rsi + 0x20 ]
mulx r9, r14, r10
adcx rbp, r14
adcx r9, r15
add rdi, [ rsp - 0x10 ]
adcx rcx, [ rsp - 0x18 ]
add rbp, [ rsp + 0x68 ]
adcx r9, [ rsp + 0x60 ]
mov rdx, [ rsi + 0x8 ]
mulx r15, r10, [ rsp - 0x30 ]
test al, al
adox r11, [ rsp + 0xd0 ]
adox r8, [ rsp + 0xc8 ]
mov rdx, r10
adcx rdx, [ rsp + 0x180 ]
adcx r15, [ rsp + 0x150 ]
mov r14, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x190 ], r13
mulx r13, r10, rdx
xor rdx, rdx
adox r11, r10
adox r13, r8
adcx rbp, [ rsp + 0xb8 ]
adcx r9, [ rsp + 0xb0 ]
mov rdx, [ rsp - 0x38 ]
mulx r10, r8, [ rsi + 0x0 ]
add r14, [ rsp + 0x58 ]
adcx r15, [ rsp + 0x50 ]
add rbp, r8
adcx r10, r9
mov rdx, r11
shrd rdx, r13, 58
shr r13, 58
test al, al
adox rbp, rdx
adox r13, r10
mov r9, rbp
shrd r9, r13, 58
shr r13, 58
mov r8, [ rsp + 0x108 ]
mov r10, r8
xor rdx, rdx
adox r10, [ rsp + 0x130 ]
mov [ rsp + 0x198 ], r15
mov r15, [ rsp + 0x100 ]
adox r15, [ rsp + 0x128 ]
adcx r10, r9
adcx r13, r15
mov r8, r10
shrd r8, r13, 58
shr r13, 58
mov r9, 0x3a 
bzhi r15, rbp, r9
adox r12, [ rsp - 0x40 ]
adox rbx, [ rsp - 0x48 ]
mov rbp, [ rsp + 0xa0 ]
mov r9, rbp
test al, al
adox r9, [ rsp + 0x168 ]
mov [ rsp + 0x1a0 ], r15
mov r15, [ rsp + 0x98 ]
adox r15, [ rsp + 0x160 ]
adcx r12, r8
adcx r13, rbx
mov rbp, r12
shrd rbp, r13, 58
shr r13, 58
test al, al
adox r9, rbp
adox r13, r15
mov r8, r9
shrd r8, r13, 58
shr r13, 58
mov rbx, 0x3ffffffffffffff 
and r9, rbx
adox rdi, [ rsp + 0x78 ]
adox rcx, [ rsp + 0x70 ]
mov rdx, rax
mulx r15, rax, [ rsi + 0x0 ]
and r12, rbx
adox rdi, rax
adox r15, rcx
adcx rdi, r8
adcx r13, r15
mov rdx, rdi
and rdx, rbx
shrd rdi, r13, 58
shr r13, 58
mov rbp, rdi
add rbp, [ rsp + 0x178 ]
adcx r13, [ rsp + 0x170 ]
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x28 ], rdx
mov rcx, rbp
shrd rcx, r13, 58
shr r13, 58
mov rdx, [ rsp - 0x30 ]
mulx r15, rax, [ rsi + 0x0 ]
and rbp, rbx
mov rdx, rax
adox rdx, [ rsp + 0x190 ]
adox r15, [ rsp + 0x188 ]
mov [ r8 + 0x30 ], rbp
adcx rdx, rcx
adcx r13, r15
mov rdi, rdx
shrd rdi, r13, 58
shr r13, 58
and rdx, rbx
adox r14, rdi
adox r13, [ rsp + 0x198 ]
mov rcx, r14
shrd rcx, r13, 57
shr r13, 57
mov [ r8 + 0x38 ], rdx
and r11, rbx
adox rcx, r11
mov rax, 0x0 
adox r13, rax
mov rbp, rcx
and rbp, rbx
shrd rcx, r13, 58
add rcx, [ rsp + 0x1a0 ]
mov r15, rcx
and r15, rbx
and r10, rbx
shr rcx, 58
mov [ r8 + 0x8 ], r15
lea rcx, [ rcx + r10 ]
mov [ r8 + 0x10 ], rcx
mov rdi, 0x39 
bzhi rdx, r14, rdi
mov [ r8 + 0x18 ], r12
mov [ r8 + 0x40 ], rdx
mov [ r8 + 0x20 ], r9
mov [ r8 + 0x0 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 552
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.1436
; seed 0449931103631612 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 16909 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=98, initial num_batches=31): 519 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.030693713407061327
; number reverted permutation / tried permutation: 320 / 493 =64.909%
; number reverted decision / tried decision: 297 / 506 =58.696%
; validated in 1.582s
