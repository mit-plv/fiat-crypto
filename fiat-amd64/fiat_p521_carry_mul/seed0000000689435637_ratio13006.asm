SECTION .text
	GLOBAL fiat_p521_carry_mul
fiat_p521_carry_mul:
sub rsp, 560
mov rax, [ rdx + 0x10 ]
mov r10, rax
shl r10, 0x1
mov rax, 0x1 
shlx r11, [ rdx + 0x38 ], rax
mov rcx, rdx
mov rdx, [ rdx + 0x8 ]
mulx r9, r8, [ rsi + 0x10 ]
mov rdx, [ rcx + 0x20 ]
mov rax, rdx
shl rax, 0x1
imul rdx, [ rcx + 0x8 ], 0x2
mov [ rsp - 0x80 ], rbx
mov rbx, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rcx + 0x8 ]
mov rdx, [ rcx + 0x20 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x0 ]
mov rdx, [ rcx + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x48 ], r14
mov [ rsp - 0x40 ], r13
mulx r13, r14, r10
imul rdx, [ rcx + 0x40 ], 0x2
mov [ rsp - 0x38 ], r12
mov r12, [ rcx + 0x18 ]
mov [ rsp - 0x30 ], rbp
lea rbp, [r12 + r12]
mov [ rsp - 0x28 ], r9
mulx r9, r12, [ rsi + 0x28 ]
xchg rdx, r10
mov [ rsp - 0x20 ], r8
mov [ rsp - 0x18 ], rdi
mulx rdi, r8, [ rsi + 0x40 ]
mov rdx, [ rcx + 0x28 ]
mov [ rsp - 0x10 ], r15
lea r15, [rdx + rdx]
mov rdx, [ rsi + 0x40 ]
mov [ rsp - 0x8 ], r9
mov [ rsp + 0x0 ], r12
mulx r12, r9, rbx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x8 ], r11
mulx r11, rbx, r15
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x10 ], rdi
mov [ rsp + 0x18 ], r8
mulx r8, rdi, rax
mov rdx, r10
mov [ rsp + 0x20 ], r8
mulx r8, r10, [ rsi + 0x8 ]
mov [ rsp + 0x28 ], r8
mov r8, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x30 ], r10
mov [ rsp + 0x38 ], rdi
mulx rdi, r10, [ rcx + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x40 ], rdi
mov [ rsp + 0x48 ], r10
mulx r10, rdi, r15
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x50 ], r10
mov [ rsp + 0x58 ], rdi
mulx rdi, r10, [ rcx + 0x0 ]
imul rdx, [ rcx + 0x30 ], 0x2
mov [ rsp + 0x60 ], rdi
mov [ rsp + 0x68 ], r10
mulx r10, rdi, [ rsi + 0x20 ]
mov [ rsp + 0x70 ], r10
mov r10, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x78 ], rdi
mov [ rsp + 0x80 ], r11
mulx r11, rdi, rax
mov rdx, r10
mov [ rsp + 0x88 ], r11
mulx r11, r10, [ rsi + 0x30 ]
mov [ rsp + 0x90 ], r11
mov r11, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x98 ], r10
mov [ rsp + 0xa0 ], rdi
mulx rdi, r10, [ rcx + 0x30 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xa8 ], rdi
mov [ rsp + 0xb0 ], r10
mulx r10, rdi, rbp
add r9, r14
adcx r13, r12
xor rdx, rdx
adox r9, rdi
adox r10, r13
mov rdx, [ rsi + 0x0 ]
mulx r12, r14, [ rcx + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mulx r13, rdi, rax
adcx r9, rdi
adcx r13, r10
mov rdx, [ rsi + 0x18 ]
mulx rdi, r10, r11
mov rdx, r15
mov [ rsp + 0xb8 ], r12
mulx r12, r15, [ rsi + 0x20 ]
mov [ rsp + 0xc0 ], r14
mov r14, rbx
test al, al
adox r14, [ rsp + 0xa0 ]
mov [ rsp + 0xc8 ], rdi
mov rdi, [ rsp + 0x88 ]
adox rdi, [ rsp + 0x80 ]
adcx r9, r15
adcx r12, r13
mulx r13, rbx, [ rsi + 0x30 ]
xchg rdx, rbp
mov [ rsp + 0xd0 ], r12
mulx r12, r15, [ rsi + 0x38 ]
mov [ rsp + 0xd8 ], r9
mov [ rsp + 0xe0 ], r10
mulx r10, r9, [ rsi + 0x40 ]
xor rdx, rdx
adox r9, [ rsp + 0x38 ]
adox r10, [ rsp + 0x20 ]
mov rdx, rax
mov [ rsp + 0xe8 ], rdi
mulx rdi, rax, [ rsi + 0x30 ]
mov rdx, r15
adcx rdx, [ rsp + 0x18 ]
adcx r12, [ rsp + 0x10 ]
xor r15, r15
adox r9, rbx
adox r13, r10
adcx rdx, rax
adcx rdi, r12
mov rbx, rdx
mov rdx, [ rsi + 0x40 ]
mulx rax, r10, r11
mov rdx, r8
mulx r12, r8, [ rsi + 0x30 ]
mov r15, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xf0 ], rdi
mov [ rsp + 0xf8 ], rbx
mulx rbx, rdi, [ rsp + 0x8 ]
xor rdx, rdx
adox r10, rdi
adox rbx, rax
adcx r10, r8
adcx r12, rbx
mov rdx, [ rsi + 0x28 ]
mulx r8, rax, [ rcx + 0x0 ]
test al, al
adox r10, rax
adox r8, r12
mov rdx, rbp
mulx rdi, rbp, [ rsi + 0x40 ]
mov rdx, r11
mulx rbx, r11, [ rsi + 0x38 ]
adcx rbp, r11
adcx rbx, rdi
mulx rax, r12, [ rsi + 0x28 ]
add r9, r12
adcx rax, r13
mov rdx, [ rcx + 0x10 ]
mulx rdi, r13, [ rsi + 0x18 ]
xor rdx, rdx
adox r10, [ rsp + 0x48 ]
adox r8, [ rsp + 0x40 ]
adcx r10, r13
adcx rdi, r8
mov rdx, [ rsi + 0x30 ]
mulx r12, r11, [ rsp + 0x8 ]
test al, al
adox rbp, r11
adox r12, rbx
adcx rbp, [ rsp + 0x0 ]
adcx r12, [ rsp - 0x8 ]
mov rdx, [ rsi + 0x40 ]
mulx r13, rbx, r15
mov rdx, [ rcx + 0x18 ]
mulx r11, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x100 ], rax
mov [ rsp + 0x108 ], r9
mulx r9, rax, [ rcx + 0x8 ]
xor rdx, rdx
adox r10, r8
adox r11, rdi
mov rdx, [ rsp + 0x8 ]
mulx r8, rdi, [ rsi + 0x10 ]
adcx rbx, [ rsp + 0x68 ]
adcx r13, [ rsp + 0x60 ]
mov [ rsp + 0x110 ], r11
mov [ rsp + 0x118 ], r10
mulx r10, r11, [ rsi + 0x28 ]
add rbx, rax
adcx r9, r13
mov rax, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x120 ], r9
mulx r9, r13, [ rcx + 0x0 ]
xor rdx, rdx
adox r14, [ rsp + 0x98 ]
mov [ rsp + 0x128 ], rbx
mov rbx, [ rsp + 0xe8 ]
adox rbx, [ rsp + 0x90 ]
adcx rbp, r13
adcx r9, r12
mov r12, [ rsp + 0xd8 ]
xor r13, r13
adox r12, [ rsp + 0xe0 ]
mov rdx, [ rsp + 0xd0 ]
adox rdx, [ rsp + 0xc8 ]
adcx r12, rdi
adcx r8, rdx
mov rdx, [ rsi + 0x18 ]
mulx r13, rdi, [ rcx + 0x0 ]
test al, al
adox r12, [ rsp + 0x30 ]
adox r8, [ rsp + 0x28 ]
adcx r12, [ rsp - 0x10 ]
adcx r8, [ rsp - 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x130 ], r8
mov [ rsp + 0x138 ], r12
mulx r12, r8, [ rcx + 0x8 ]
add r14, r11
adcx r10, rbx
mov rdx, r15
mulx r11, r15, [ rsi + 0x20 ]
add r14, r15
adcx r11, r10
add rbp, r8
adcx r12, r9
mov rbx, rdx
mov rdx, [ rcx + 0x20 ]
mulx r8, r9, [ rsi + 0x8 ]
xor rdx, rdx
adox r14, rdi
adox r13, r11
mov rdx, rax
mulx rdi, rax, [ rsi + 0x18 ]
adcx r14, [ rsp - 0x20 ]
adcx r13, [ rsp - 0x28 ]
mov r10, [ rsp + 0xf8 ]
add r10, [ rsp + 0x58 ]
mov r15, [ rsp + 0xf0 ]
adcx r15, [ rsp + 0x50 ]
xor r11, r11
adox r10, [ rsp + 0x78 ]
adox r15, [ rsp + 0x70 ]
mov [ rsp + 0x140 ], r12
mulx r12, r11, [ rsi + 0x20 ]
adcx r10, rax
adcx rdi, r15
mov rax, r9
add rax, [ rsp + 0x118 ]
adcx r8, [ rsp + 0x110 ]
mov r9, r11
test al, al
adox r9, [ rsp + 0x108 ]
adox r12, [ rsp + 0x100 ]
adcx rax, [ rsp + 0xc0 ]
adcx r8, [ rsp + 0xb8 ]
xchg rdx, rbx
mulx r11, r15, [ rsi + 0x18 ]
test al, al
adox r9, r15
adox r11, r12
mulx r15, r12, [ rsi + 0x10 ]
adcx r10, r12
adcx r15, rdi
mov rdi, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x148 ], r8
mulx r8, r12, [ rcx + 0x0 ]
mov rdx, [ rcx + 0x8 ]
mov [ rsp + 0x150 ], rax
mov [ rsp + 0x158 ], rbp
mulx rbp, rax, [ rsi + 0x8 ]
test al, al
adox r9, r12
adox r8, r11
mov rdx, rbx
mulx r11, rbx, [ rsi + 0x40 ]
adcx r9, rax
adcx rbp, r8
mov rdx, [ rsi + 0x38 ]
mulx rax, r12, rdi
add rbx, r12
adcx rax, r11
mov rdx, [ rcx + 0x0 ]
mulx r8, rdi, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x8 ]
mulx r12, r11, [ rcx + 0x0 ]
test al, al
adox rbx, rdi
adox r8, rax
mov rdx, [ rcx + 0x8 ]
mulx rdi, rax, [ rsi + 0x0 ]
adcx r10, r11
adcx r12, r15
mov rdx, [ rcx + 0x10 ]
mulx r11, r15, [ rsi + 0x0 ]
add r10, rax
adcx rdi, r12
add r9, r15
adcx r11, rbp
mov rdx, [ rcx + 0x18 ]
mulx rax, rbp, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mulx r15, r12, [ rcx + 0x10 ]
add rbx, [ rsp - 0x30 ]
adcx r8, [ rsp - 0x38 ]
xor rdx, rdx
adox rbx, r12
adox r15, r8
mov r12, [ rsp + 0x130 ]
mov r8, [ rsp + 0x138 ]
shrd r8, r12, 58
shr r12, 58
mov [ rsp + 0x160 ], r13
xor r13, r13
adox r10, r8
adox r12, rdi
adcx rbx, rbp
adcx rax, r15
mov rdx, [ rcx + 0x10 ]
mulx rbp, rdi, [ rsi + 0x8 ]
mov rdx, [ rcx + 0x20 ]
mulx r8, r15, [ rsi + 0x10 ]
add rbx, r15
adcx r8, rax
mov rdx, r10
shrd rdx, r12, 58
shr r12, 58
add r9, rdx
adcx r12, r11
mov r11, 0x3ffffffffffffff 
and r10, r11
mov rax, r9
shrd rax, r12, 58
shr r12, 58
mov rdx, [ rcx + 0x10 ]
mulx r13, r15, [ rsi + 0x28 ]
and r9, r11
mov rdx, [ rcx + 0x28 ]
mov [ rsp + 0x168 ], r9
mulx r9, r11, [ rsi + 0x8 ]
adox rbx, r11
adox r9, r8
mov rdx, [ rcx + 0x18 ]
mulx r11, r8, [ rsi + 0x0 ]
mov rdx, [ rcx + 0x18 ]
mov [ rsp + 0x170 ], r10
mov [ rsp + 0x178 ], r9
mulx r9, r10, [ rsi + 0x20 ]
adcx r14, rdi
adcx rbp, [ rsp + 0x160 ]
test al, al
adox r14, r8
adox r11, rbp
mov rdx, r15
adcx rdx, [ rsp + 0x128 ]
adcx r13, [ rsp + 0x120 ]
mov rdi, rdx
mov rdx, [ rcx + 0x20 ]
mulx r8, r15, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x180 ], rbx
mulx rbx, rbp, [ rcx + 0x28 ]
xor rdx, rdx
adox r14, rax
adox r12, r11
adcx rdi, r10
adcx r9, r13
mov rdx, [ rcx + 0x18 ]
mulx r10, rax, [ rsi + 0x8 ]
mov rdx, 0x3a 
bzhi r11, r14, rdx
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x18 ], r11
mov rdx, [ rsi + 0x10 ]
mulx r13, r11, [ rcx + 0x10 ]
mov rdx, r11
adox rdx, [ rsp + 0x158 ]
adox r13, [ rsp + 0x140 ]
test al, al
adox rdx, rax
adox r10, r13
mov rax, rdx
mov rdx, [ rcx + 0x30 ]
mulx r13, r11, [ rsi + 0x10 ]
mov rdx, [ rcx + 0x20 ]
mov [ rsp + 0x188 ], r13
mov [ rsp + 0x190 ], r11
mulx r11, r13, [ rsi + 0x18 ]
adcx rdi, r13
adcx r11, r9
test al, al
adox rdi, rbp
adox rbx, r11
shrd r14, r12, 58
shr r12, 58
mov rdx, [ rcx + 0x30 ]
mulx r9, rbp, [ rsi + 0x8 ]
mov rdx, [ rcx + 0x8 ]
mulx r11, r13, [ rsi + 0x38 ]
xor rdx, rdx
adox rax, [ rsp - 0x40 ]
adox r10, [ rsp - 0x48 ]
adcx rdi, rbp
adcx r9, rbx
mov rdx, [ rsi + 0x40 ]
mulx rbp, rbx, [ rcx + 0x0 ]
xor rdx, rdx
adox rbx, r13
adox r11, rbp
adcx rax, r14
adcx r12, r10
mov rdx, [ rsi + 0x30 ]
mulx r13, r14, [ rcx + 0x10 ]
mov rdx, rax
shrd rdx, r12, 58
shr r12, 58
xor r10, r10
adox rbx, r14
adox r13, r11
mov rbp, rdx
mov rdx, [ rcx + 0x28 ]
mulx r14, r11, [ rsi + 0x18 ]
mov rdx, [ rcx + 0x38 ]
mov [ rsp + 0x198 ], r12
mulx r12, r10, [ rsi + 0x0 ]
adcx rdi, r10
adcx r12, r9
mov rdx, [ rsi + 0x8 ]
mulx r10, r9, [ rcx + 0x38 ]
mov rdx, [ rcx + 0x18 ]
mov [ rsp + 0x1a0 ], r12
mov [ rsp + 0x1a8 ], rdi
mulx rdi, r12, [ rsi + 0x28 ]
add rbx, r12
adcx rdi, r13
add rbx, r15
adcx r8, rdi
xor rdx, rdx
adox rbx, r11
adox r14, r8
mov rdx, [ rcx + 0x40 ]
mulx r13, r15, [ rsi + 0x0 ]
adcx rbx, [ rsp + 0x190 ]
adcx r14, [ rsp + 0x188 ]
test al, al
adox rbx, r9
adox r10, r14
mov rdx, rbp
adcx rdx, [ rsp + 0x150 ]
mov r11, [ rsp + 0x148 ]
adcx r11, [ rsp + 0x198 ]
mov rbp, [ rsp + 0x180 ]
add rbp, [ rsp + 0xb0 ]
mov r9, [ rsp + 0x178 ]
adcx r9, [ rsp + 0xa8 ]
mov r12, 0x3a 
bzhi rdi, rdx, r12
shrd rdx, r11, 58
shr r11, 58
xor r8, r8
adox rbp, rdx
adox r11, r9
adcx rbx, r15
adcx r13, r10
mov r15, rbp
shrd r15, r11, 58
shr r11, 58
mov r14, r15
add r14, [ rsp + 0x1a8 ]
adcx r11, [ rsp + 0x1a0 ]
mov r10, r14
shrd r10, r11, 58
shr r11, 58
xor r9, r9
adox rbx, r10
adox r11, r13
mov r8, rbx
shrd r8, r11, 57
shr r11, 57
bzhi rdx, r14, r12
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x38 ], rdx
bzhi r15, rbp, r12
mov rbp, 0x1ffffffffffffff 
and rbx, rbp
bzhi r14, [ rsp + 0x138 ], r12
adox r8, r14
adox r11, r9
mov r10, r8
shrd r10, r11, 58
add r10, [ rsp + 0x170 ]
bzhi rdx, r8, r12
mov [ r13 + 0x28 ], rdi
mov [ r13 + 0x0 ], rdx
bzhi rdi, r10, r12
bzhi r14, rax, r12
shr r10, 58
add r10, [ rsp + 0x168 ]
mov [ r13 + 0x8 ], rdi
mov [ r13 + 0x10 ], r10
mov [ r13 + 0x20 ], r14
mov [ r13 + 0x30 ], r15
mov [ r13 + 0x40 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 560
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.3006
; seed 0857063811643604 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 6626563 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=52, initial num_batches=31): 137673 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.020775928637515404
; number reverted permutation / tried permutation: 67514 / 89919 =75.083%
; number reverted decision / tried decision: 55793 / 90080 =61.937%
; validated in 4.916s
