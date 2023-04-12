SECTION .text
	GLOBAL fiat_p521_carry_mul
fiat_p521_carry_mul:
sub rsp, 688
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx r11, r10, [ rax + 0x18 ]
mov rdx, 0x1 
shlx rcx, [ rax + 0x18 ], rdx
mov r8, [ rax + 0x20 ]
lea r9, [r8 + r8]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r8, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, 0x1 
mov [ rsp - 0x68 ], r13
shlx r13, [ rax + 0x30 ], rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x10 ]
mov rdx, 0x1 
mov [ rsp - 0x50 ], rdi
shlx rdi, [ rax + 0x10 ], rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x48 ], r11
lea r11, [rdx + rdx]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x40 ], r10
mov [ rsp - 0x38 ], rbx
mulx rbx, r10, [ rsi + 0x0 ]
mov rdx, rdi
mov [ rsp - 0x30 ], r8
mulx r8, rdi, [ rsi + 0x38 ]
mov [ rsp - 0x28 ], rbx
mov rbx, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp - 0x20 ], r10
mov [ rsp - 0x18 ], r15
mulx r15, r10, rcx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x10 ], r14
mov [ rsp - 0x8 ], r12
mulx r12, r14, r13
imul rdx, [ rax + 0x38 ], 0x2
mov [ rsp + 0x0 ], rbp
mov [ rsp + 0x8 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
mov [ rsp + 0x10 ], r12
mov r12, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x18 ], rbp
mov [ rsp + 0x20 ], r14
mulx r14, rbp, [ rsi + 0x20 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x28 ], r14
mov r14, rdx
shl r14, 0x1
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x30 ], rbp
mov [ rsp + 0x38 ], r8
mulx r8, rbp, [ rax + 0x30 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x40 ], r8
mov [ rsp + 0x48 ], rbp
mulx rbp, r8, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x50 ], rbp
mov [ rsp + 0x58 ], r8
mulx r8, rbp, r12
mov rdx, r14
mov [ rsp + 0x60 ], r8
mulx r8, r14, [ rsi + 0x28 ]
mov [ rsp + 0x68 ], rbp
mov [ rsp + 0x70 ], r8
mulx r8, rbp, [ rsi + 0x20 ]
mov [ rsp + 0x78 ], r8
mov r8, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x80 ], rbp
mov [ rsp + 0x88 ], r14
mulx r14, rbp, r12
mov rdx, r9
mov [ rsp + 0x90 ], r14
mulx r14, r9, [ rsi + 0x38 ]
mov [ rsp + 0x98 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xa0 ], rdi
mov [ rsp + 0xa8 ], r11
mulx r11, rdi, [ rax + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xb0 ], r11
mov [ rsp + 0xb8 ], rdi
mulx rdi, r11, [ rax + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0xc0 ], rdi
mov [ rsp + 0xc8 ], r11
mulx r11, rdi, [ rsi + 0x20 ]
xor rdx, rdx
adox r10, r9
adox r14, r15
mov rdx, [ rax + 0x18 ]
mulx r9, r15, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0xd0 ], r11
mov [ rsp + 0xd8 ], rdi
mulx rdi, r11, [ rsp + 0xa8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xe0 ], r9
mov [ rsp + 0xe8 ], r15
mulx r15, r9, r13
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0xf0 ], r15
mov [ rsp + 0xf8 ], r9
mulx r9, r15, rbx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x100 ], r14
mulx r14, rbx, rcx
adcx r15, rbx
adcx r14, r9
xor rdx, rdx
adox r11, [ rsp + 0xa0 ]
adox rdi, [ rsp + 0x38 ]
mov rdx, rbp
mulx r9, rbp, [ rsi + 0x30 ]
mov rbx, [ rax + 0x40 ]
mov [ rsp + 0x108 ], r10
lea r10, [rbx + rbx]
adcx r15, rbp
adcx r9, r14
mulx r14, rbx, [ rsi + 0x28 ]
xchg rdx, rcx
mov [ rsp + 0x110 ], r14
mulx r14, rbp, [ rsi + 0x30 ]
mov rdx, r10
mov [ rsp + 0x118 ], rbx
mulx rbx, r10, [ rsi + 0x20 ]
mov [ rsp + 0x120 ], rbx
xor rbx, rbx
adox r15, [ rsp + 0x88 ]
adox r9, [ rsp + 0x70 ]
adcx r11, rbp
adcx r14, rdi
xor rdi, rdi
adox r11, [ rsp + 0x118 ]
adox r14, [ rsp + 0x110 ]
mov rbx, rdx
mov rdx, [ rsi + 0x0 ]
mulx rdi, rbp, [ rax + 0x40 ]
adcx r11, [ rsp + 0x80 ]
adcx r14, [ rsp + 0x78 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x128 ], rdi
mov [ rsp + 0x130 ], rbp
mulx rbp, rdi, r13
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x138 ], r10
mov [ rsp + 0x140 ], r9
mulx r9, r10, rbx
xor rdx, rdx
adox r11, rdi
adox rbp, r14
mov rdx, [ rsi + 0x8 ]
mulx rdi, r14, rbx
adcx r15, [ rsp + 0x20 ]
mov rdx, [ rsp + 0x8 ]
adcx rdx, [ rsp + 0x140 ]
add r15, [ rsp + 0x18 ]
adcx rdx, [ rsp + 0x10 ]
mov [ rsp + 0x148 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x150 ], r14
mov [ rsp + 0x158 ], rbp
mulx rbp, r14, r12
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x160 ], r11
mov [ rsp + 0x168 ], rbp
mulx rbp, r11, r13
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x170 ], rbp
mov [ rsp + 0x178 ], r11
mulx r11, rbp, rbx
add r15, rbp
adcx r11, rdi
add r14, r10
adcx r9, [ rsp + 0x168 ]
mov rdx, [ rsi + 0x10 ]
mulx rdi, r10, r12
mov rdx, r10
test al, al
adox rdx, [ rsp + 0x160 ]
adox rdi, [ rsp + 0x158 ]
mov rbp, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x180 ], r9
mulx r9, r10, r8
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x188 ], r14
mov [ rsp + 0x190 ], r9
mulx r9, r14, [ rax + 0x0 ]
adcx r15, r14
adcx r9, r11
add rbp, [ rsp + 0x150 ]
adcx rdi, [ rsp + 0x148 ]
mov rdx, [ rsi + 0x40 ]
mulx r14, r11, rcx
add r11, r10
adcx r14, [ rsp + 0x190 ]
mov rdx, [ rax + 0x0 ]
mulx r10, rcx, [ rsi + 0x0 ]
test al, al
adox rbp, rcx
adox r10, rdi
mov rdx, rbp
shrd rdx, r10, 58
shr r10, 58
xor rdi, rdi
adox r11, [ rsp + 0x178 ]
adox r14, [ rsp + 0x170 ]
adcx r15, [ rsp + 0x0 ]
adcx r9, [ rsp - 0x8 ]
mov rcx, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x198 ], r14
mulx r14, rdi, r8
add r15, rcx
adcx r10, r9
mov rdx, rdi
xor rcx, rcx
adox rdx, [ rsp + 0x108 ]
adox r14, [ rsp + 0x100 ]
adcx rdx, [ rsp + 0xf8 ]
adcx r14, [ rsp + 0xf0 ]
mov r9, 0x3a 
bzhi rdi, rbp, r9
bzhi rbp, r15, r9
mov rcx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x1a0 ], rbp
mulx rbp, r9, [ rax + 0x8 ]
mov rdx, r12
mov [ rsp + 0x1a8 ], rdi
mulx rdi, r12, [ rsi + 0x20 ]
adox rcx, r12
adox rdi, r14
mov r14, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x1b0 ], rbp
mulx rbp, r12, r13
xor rdx, rdx
adox r12, [ rsp + 0x68 ]
adox rbp, [ rsp + 0x60 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1b8 ], rbp
mov [ rsp + 0x1c0 ], r12
mulx r12, rbp, rbx
adcx rcx, rbp
adcx r12, rdi
test al, al
adox r11, [ rsp + 0x98 ]
mov rdx, [ rsp + 0x90 ]
adox rdx, [ rsp + 0x198 ]
adcx rcx, [ rsp - 0x10 ]
adcx r12, [ rsp - 0x18 ]
xor rdi, rdi
adox r11, [ rsp + 0x138 ]
adox rdx, [ rsp + 0x120 ]
adcx rcx, r9
adcx r12, [ rsp + 0x1b0 ]
mov r9, rdx
mov rdx, [ rax + 0x10 ]
mulx rdi, rbp, [ rsi + 0x0 ]
test al, al
adox rcx, rbp
adox rdi, r12
shrd r15, r10, 58
shr r10, 58
mov rdx, [ rsi + 0x10 ]
mulx rbp, r12, [ rax + 0x8 ]
test al, al
adox rcx, r15
adox r10, rdi
mov rdx, rcx
shrd rdx, r10, 58
shr r10, 58
mov rdi, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1c8 ], r10
mulx r10, r15, [ rax + 0x0 ]
add r11, r15
adcx r10, r9
mov rdx, [ rsi + 0x30 ]
mulx r15, r9, r14
mov rdx, r13
mulx r14, r13, [ rsi + 0x38 ]
mov rdx, r8
mov [ rsp + 0x1d0 ], rdi
mulx rdi, r8, [ rsi + 0x40 ]
add r8, r13
adcx r14, rdi
test al, al
adox r8, r9
adox r15, r14
mov rdx, [ rax + 0x8 ]
mulx r13, r9, [ rsi + 0x30 ]
mov rdx, 0x3a 
bzhi rdi, rcx, rdx
adox r11, r12
adox rbp, r10
mov rdx, [ rsi + 0x30 ]
mulx rcx, r12, rbx
mov rdx, [ rsi + 0x28 ]
mulx r14, r10, rbx
add r8, r10
adcx r14, r15
mov rdx, [ rsi + 0x20 ]
mulx r10, r15, [ rax + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1d8 ], rdi
mov [ rsp + 0x1e0 ], rcx
mulx rcx, rdi, [ rax + 0x20 ]
test al, al
adox r8, r15
adox r10, r14
mov rdx, [ rax + 0x8 ]
mulx r15, r14, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x1e8 ], r12
mov [ rsp + 0x1f0 ], rcx
mulx rcx, r12, rbx
adcx r8, r14
adcx r15, r10
mov rdx, [ rax + 0x0 ]
mulx r10, rbx, [ rsi + 0x38 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x1f8 ], r15
mulx r15, r14, [ rsi + 0x8 ]
test al, al
adox r12, rbx
adox r10, rcx
adcx r12, r9
adcx r13, r10
add r11, r14
adcx r15, rbp
mov rdx, [ rsi + 0x28 ]
mulx rbp, r9, [ rax + 0x0 ]
test al, al
adox r11, [ rsp - 0x20 ]
adox r15, [ rsp - 0x28 ]
mov rdx, [ rax + 0x10 ]
mulx rbx, rcx, [ rsi + 0x10 ]
mov rdx, [ rax + 0x10 ]
mulx r10, r14, [ rsi + 0x28 ]
adcx r11, [ rsp + 0x1d0 ]
adcx r15, [ rsp + 0x1c8 ]
xor rdx, rdx
adox r12, r14
adox r10, r13
mov rdx, [ rax + 0x18 ]
mulx r14, r13, [ rsi + 0x10 ]
adcx r12, [ rsp + 0xe8 ]
adcx r10, [ rsp + 0xe0 ]
xor rdx, rdx
adox r12, rdi
adox r10, [ rsp + 0x1f0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x200 ], r14
mulx r14, rdi, [ rax + 0x18 ]
adcx r12, [ rsp + 0xb8 ]
adcx r10, [ rsp + 0xb0 ]
add r8, rcx
adcx rbx, [ rsp + 0x1f8 ]
add r8, rdi
adcx r14, rbx
mov rdx, [ rax + 0x20 ]
mulx rdi, rcx, [ rsi + 0x0 ]
test al, al
adox r8, rcx
adox rdi, r14
mov rdx, 0x3ffffffffffffff 
mov rbx, r11
and rbx, rdx
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x18 ], rbx
shrd r11, r15, 58
shr r15, 58
test al, al
adox r8, r11
adox r15, rdi
mov rcx, r8
and rcx, rdx
mov [ r14 + 0x20 ], rcx
mov rdi, [ rsp + 0x1c0 ]
adox rdi, [ rsp + 0x1e8 ]
mov rbx, [ rsp + 0x1b8 ]
adox rbx, [ rsp + 0x1e0 ]
mov rdx, [ rsi + 0x40 ]
mulx rcx, r11, [ rax + 0x0 ]
adcx r11, [ rsp + 0x58 ]
adcx rcx, [ rsp + 0x50 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x208 ], r10
mulx r10, r14, [ rsi + 0x8 ]
test al, al
adox rdi, r9
adox rbp, rbx
adcx rdi, [ rsp + 0xd8 ]
adcx rbp, [ rsp + 0xd0 ]
mov rdx, [ rsi + 0x18 ]
mulx rbx, r9, [ rax + 0x10 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x210 ], r12
mov [ rsp + 0x218 ], r10
mulx r10, r12, [ rax + 0x10 ]
test al, al
adox rdi, r9
adox rbx, rbp
adcx r11, r12
adcx r10, rcx
add r11, [ rsp + 0xc8 ]
adcx r10, [ rsp + 0xc0 ]
xor rdx, rdx
adox rdi, r13
adox rbx, [ rsp + 0x200 ]
mov rdx, [ rsi + 0x10 ]
mulx rcx, r13, [ rax + 0x20 ]
mov rdx, [ rax + 0x0 ]
mulx r9, rbp, [ rsi + 0x30 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x220 ], r10
mulx r10, r12, [ rsi + 0x20 ]
mov rdx, rbp
adcx rdx, [ rsp + 0x188 ]
adcx r9, [ rsp + 0x180 ]
test al, al
adox rdx, [ rsp - 0x30 ]
adox r9, [ rsp - 0x38 ]
adcx rdx, r12
adcx r10, r9
xor rbp, rbp
adox rdx, [ rsp - 0x40 ]
adox r10, [ rsp - 0x48 ]
mov r12, rdx
mov rdx, [ rsi + 0x0 ]
mulx rbp, r9, [ rax + 0x28 ]
adcx rdi, r14
adcx rbx, [ rsp + 0x218 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x228 ], r11
mulx r11, r14, [ rsi + 0x8 ]
test al, al
adox rdi, r9
adox rbp, rbx
adcx r12, r13
adcx rcx, r10
xor rdx, rdx
adox r12, r14
adox r11, rcx
mov r13, [ rsp + 0x228 ]
adcx r13, [ rsp + 0x30 ]
mov r10, [ rsp + 0x220 ]
adcx r10, [ rsp + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mulx rbx, r9, [ rax + 0x30 ]
mov rdx, [ rsi + 0x18 ]
mulx rcx, r14, [ rax + 0x28 ]
shrd r8, r15, 58
shr r15, 58
test al, al
adox rdi, r8
adox r15, rbp
mov rdx, 0x3a 
bzhi rbp, rdi, rdx
adox r13, r14
adox rcx, r10
mov rdx, [ rsi + 0x0 ]
mulx r14, r10, [ rax + 0x30 ]
shrd rdi, r15, 58
shr r15, 58
test al, al
adox r12, r10
adox r14, r11
adcx r12, rdi
adcx r15, r14
mov rdx, r9
add rdx, [ rsp + 0x210 ]
adcx rbx, [ rsp + 0x208 ]
mov r11, rdx
mov rdx, [ rax + 0x38 ]
mulx r8, r9, [ rsi + 0x0 ]
mov rdx, r12
shrd rdx, r15, 58
shr r15, 58
xor r10, r10
adox r11, r9
adox r8, rbx
adcx r11, rdx
adcx r15, r8
mov rdx, [ rsi + 0x8 ]
mulx r14, rdi, [ rax + 0x38 ]
xor rdx, rdx
adox r13, [ rsp + 0x48 ]
adox rcx, [ rsp + 0x40 ]
mov r10, 0x3a 
bzhi rbx, r11, r10
adox r13, rdi
adox r14, rcx
shrd r11, r15, 58
shr r15, 58
test al, al
adox r13, [ rsp + 0x130 ]
adox r14, [ rsp + 0x128 ]
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x38 ], rbx
adcx r13, r11
adcx r15, r14
mov r8, 0x1ffffffffffffff 
mov rdi, r13
and rdi, r8
shrd r13, r15, 57
shr r15, 57
mov [ r9 + 0x40 ], rdi
test al, al
adox r13, [ rsp + 0x1a8 ]
adox r15, rdx
bzhi rcx, r13, r10
shrd r13, r15, 58
add r13, [ rsp + 0x1a0 ]
bzhi rbx, r13, r10
shr r13, 58
mov [ r9 + 0x0 ], rcx
bzhi r11, r12, r10
add r13, [ rsp + 0x1d8 ]
mov [ r9 + 0x28 ], rbp
mov [ r9 + 0x8 ], rbx
mov [ r9 + 0x10 ], r13
mov [ r9 + 0x30 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 688
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.3139
; seed 2408863105786879 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 9583082 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=94, initial num_batches=31): 217596 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.022706265061699357
; number reverted permutation / tried permutation: 66623 / 90066 =73.971%
; number reverted decision / tried decision: 55240 / 89933 =61.424%
; validated in 7.223s
