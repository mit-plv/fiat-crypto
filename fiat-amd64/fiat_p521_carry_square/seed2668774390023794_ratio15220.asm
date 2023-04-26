SECTION .text
	GLOBAL fiat_p521_carry_square
fiat_p521_carry_square:
sub rsp, 544
mov rax, [ rsi + 0x38 ]
lea r10, [rax + rax]
mov rdx, [ rsi + 0x20 ]
mulx r11, rax, rdx
mov rdx, 0x1 
shlx rcx, [ rsi + 0x28 ], rdx
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, 0x2 
mov [ rsp - 0x70 ], r12
shlx r12, [ rsi + 0x38 ], rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, r12
mov rdx, [ rsi + 0x40 ]
mov [ rsp - 0x58 ], r15
lea r15, [rdx + rdx]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbp
mulx rbp, rdi, r12
mov rdx, [ rsi + 0x40 ]
mov [ rsp - 0x40 ], rbx
mov [ rsp - 0x38 ], r9
mulx r9, rbx, r15
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], r9
mov [ rsp - 0x28 ], rbx
mulx rbx, r9, rcx
mov rdx, 0x1 
mov [ rsp - 0x20 ], rbx
shlx rbx, [ rsi + 0x10 ], rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x18 ], r9
mov [ rsp - 0x10 ], r8
mulx r8, r9, r12
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x8 ], rbp
mov [ rsp + 0x0 ], rdi
mulx rdi, rbp, rdx
mov rdx, rbx
mov [ rsp + 0x8 ], r14
mulx r14, rbx, [ rsi + 0x0 ]
mov [ rsp + 0x10 ], r14
mov r14, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x18 ], rbx
mov [ rsp + 0x20 ], r13
mulx r13, rbx, rcx
mov rdx, r10
mov [ rsp + 0x28 ], rdi
mulx rdi, r10, [ rsi + 0x38 ]
mov [ rsp + 0x30 ], rbp
mov rbp, [ rsi + 0x30 ]
mov [ rsp + 0x38 ], rdi
mov rdi, rbp
shl rdi, 0x2
mov rbp, 0x1 
mov [ rsp + 0x40 ], r10
shlx r10, [ rsi + 0x20 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x48 ], r10
mov [ rsp + 0x50 ], r8
mulx r8, r10, rcx
mov rdx, r15
mov [ rsp + 0x58 ], r8
mulx r8, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x60 ], r8
mov [ rsp + 0x68 ], r15
mulx r15, r8, rdi
xor rdx, rdx
adox rax, rbx
adox r13, r11
mov rdx, [ rsi + 0x20 ]
mulx rbx, r11, rdi
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x70 ], r10
mov [ rsp + 0x78 ], r15
mulx r15, r10, rbp
mov rdx, rcx
mov [ rsp + 0x80 ], r15
mulx r15, rcx, [ rsi + 0x28 ]
mov [ rsp + 0x88 ], r10
imul r10, [ rsi + 0x28 ], 0x4
mov [ rsp + 0x90 ], r8
xor r8, r8
adox rcx, r11
adox rbx, r15
xchg rdx, r12
mulx r15, r11, [ rsi + 0x18 ]
mov r8, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x98 ], r13
mov [ rsp + 0xa0 ], rax
mulx rax, r13, r10
mov rdx, r12
mulx r10, r12, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0xa8 ], r10
lea r10, [ 4 * rdx]
mov rdx, rdi
mov [ rsp + 0xb0 ], r12
mulx r12, rdi, [ rsi + 0x18 ]
adcx rcx, r11
adcx r15, rbx
mov rdx, r10
mulx rbx, r10, [ rsi + 0x18 ]
mov [ rsp + 0xb8 ], r15
mulx r15, r11, [ rsi + 0x8 ]
mov [ rsp + 0xc0 ], rcx
xor rcx, rcx
adox r13, rdi
adox r12, rax
mulx rdi, rax, [ rsi + 0x30 ]
mov [ rsp + 0xc8 ], rbx
mulx rbx, rcx, [ rsi + 0x38 ]
mov [ rsp + 0xd0 ], r10
mov [ rsp + 0xd8 ], r15
mulx r15, r10, [ rsi + 0x28 ]
mov [ rsp + 0xe0 ], r11
mov r11, [ rsi + 0x8 ]
mov [ rsp + 0xe8 ], r12
lea r12, [r11 + r11]
adcx r9, r10
adcx r15, [ rsp + 0x50 ]
mov r11, 0x1 
shlx r10, [ rsi + 0x30 ], r11
xchg rdx, r10
mov [ rsp + 0xf0 ], r15
mulx r15, r11, [ rsi + 0x0 ]
mov [ rsp + 0xf8 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x100 ], r11
mov [ rsp + 0x108 ], r9
mulx r9, r11, [ rsp + 0x48 ]
mov rdx, rax
mov [ rsp + 0x110 ], r9
xor r9, r9
adox rdx, [ rsp + 0x40 ]
adox rdi, [ rsp + 0x38 ]
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x118 ], rdi
mulx rdi, r9, r12
mov rdx, r15
mulx r12, r15, [ rsi + 0x8 ]
mov [ rsp + 0x120 ], rax
mov [ rsp + 0x128 ], rdi
mulx rdi, rax, [ rsi + 0x10 ]
mov [ rsp + 0x130 ], r9
mov r9, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x138 ], r12
mov [ rsp + 0x140 ], r15
mulx r15, r12, rbp
mov rdx, r8
mulx rbp, r8, [ rsi + 0x20 ]
mov rdx, rax
adcx rdx, [ rsp + 0xa0 ]
adcx rdi, [ rsp + 0x98 ]
mov rax, r8
add rax, [ rsp + 0x90 ]
adcx rbp, [ rsp + 0x78 ]
xor r8, r8
adox rdx, r12
adox r15, rdi
mov r12, rdx
mov rdx, [ rsi + 0x10 ]
mulx r8, rdi, [ rsp + 0x48 ]
adcx rcx, [ rsp + 0x30 ]
adcx rbx, [ rsp + 0x28 ]
mov rdx, r9
mov [ rsp + 0x148 ], r15
mulx r15, r9, [ rsi + 0x30 ]
add rcx, rdi
adcx r8, rbx
mov rdx, [ rsi + 0x10 ]
mulx rbx, rdi, r10
add r13, [ rsp + 0x20 ]
mov rdx, [ rsp + 0x8 ]
adcx rdx, [ rsp + 0xe8 ]
add r9, [ rsp + 0x0 ]
adcx r15, [ rsp - 0x8 ]
mov [ rsp + 0x150 ], r12
mov r12, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x158 ], r8
mov [ rsp + 0x160 ], rcx
mulx rcx, r8, r10
test al, al
adox r9, r8
adox rcx, r15
adcx r13, [ rsp + 0xe0 ]
adcx r12, [ rsp + 0xd8 ]
test al, al
adox r13, [ rsp - 0x10 ]
adox r12, [ rsp - 0x38 ]
mov rdx, 0x1 
shlx r10, [ rsi + 0x18 ], rdx
mov rdx, r10
mulx r15, r10, [ rsi + 0x8 ]
mov r8, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x168 ], rbx
mov [ rsp + 0x170 ], rdi
mulx rdi, rbx, r14
adcx rax, [ rsp + 0xd0 ]
adcx rbp, [ rsp + 0xc8 ]
test al, al
adox r9, rbx
adox rdi, rcx
mov rdx, r11
adcx rdx, [ rsp - 0x28 ]
mov r14, [ rsp - 0x30 ]
adcx r14, [ rsp + 0x110 ]
xor r11, r11
adox rdx, [ rsp - 0x18 ]
adox r14, [ rsp - 0x20 ]
mov rcx, rdx
mov rdx, [ rsi + 0x10 ]
mulx r11, rbx, rdx
adcx rcx, [ rsp + 0x140 ]
adcx r14, [ rsp + 0x138 ]
mov rdx, r13
shrd rdx, r12, 58
shr r12, 58
mov [ rsp + 0x178 ], r14
mov r14, 0x3a 
mov [ rsp + 0x180 ], rcx
bzhi rcx, r13, r14
mov r13, rbx
adox r13, [ rsp + 0x108 ]
adox r11, [ rsp + 0xf0 ]
xor rbx, rbx
adox r13, r10
adox r15, r11
mov r10, [ rsp + 0x170 ]
mov r11, r10
adcx r11, [ rsp + 0xc0 ]
mov r14, [ rsp + 0x168 ]
adcx r14, [ rsp + 0xb8 ]
mov r10, rdx
mov rdx, [ rsp + 0x48 ]
mov [ rsp + 0x188 ], rcx
mulx rcx, rbx, [ rsi + 0x0 ]
add r13, rbx
adcx rcx, r15
add r11, [ rsp + 0x130 ]
adcx r14, [ rsp + 0x128 ]
xchg rdx, r8
mulx rbx, r15, [ rsi + 0x0 ]
test al, al
adox r11, r10
adox r12, r14
adcx r9, r15
adcx rbx, rdi
mov rdi, [ rsp + 0x70 ]
mov r10, rdi
add r10, [ rsp + 0x160 ]
mov r14, [ rsp + 0x58 ]
adcx r14, [ rsp + 0x158 ]
mulx r15, rdi, [ rsi + 0x10 ]
add r10, [ rsp + 0x100 ]
adcx r14, [ rsp + 0xf8 ]
xor rdx, rdx
adox rax, [ rsp - 0x40 ]
adox rbp, [ rsp - 0x48 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x190 ], r14
mov [ rsp + 0x198 ], r10
mulx r10, r14, r8
mov rdx, rdi
adcx rdx, [ rsp + 0x120 ]
adcx r15, [ rsp + 0x118 ]
add rdx, r14
adcx r10, r15
mov r8, r11
shrd r8, r12, 58
shr r12, 58
add rdx, [ rsp + 0xb0 ]
adcx r10, [ rsp + 0xa8 ]
test al, al
adox rax, [ rsp + 0x18 ]
adox rbp, [ rsp + 0x10 ]
adcx rax, r8
adcx r12, rbp
mov rdi, rax
shrd rdi, r12, 58
shr r12, 58
test al, al
adox r9, rdi
adox r12, rbx
mov rbx, r9
shrd rbx, r12, 58
shr r12, 58
mov r14, 0x3ffffffffffffff 
and rax, r14
adox r13, rbx
adox r12, rcx
mov rcx, r13
and rcx, r14
and r9, r14
shrd r13, r12, 58
shr r12, 58
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x20 ], rcx
test al, al
adox rdx, r13
adox r12, r10
mov [ r15 + 0x18 ], r9
mov r8, [ rsp + 0x180 ]
adcx r8, [ rsp + 0x88 ]
mov r10, [ rsp + 0x178 ]
adcx r10, [ rsp + 0x80 ]
mov rbp, rdx
and rbp, r14
mov [ r15 + 0x28 ], rbp
shrd rdx, r12, 58
shr r12, 58
mov rdi, rdx
xor rbx, rbx
adox rdi, [ rsp + 0x198 ]
adox r12, [ rsp + 0x190 ]
mov rcx, rdi
shrd rcx, r12, 58
shr r12, 58
test al, al
adox r8, rcx
adox r12, r10
mov r9, [ rsp + 0x150 ]
adcx r9, [ rsp + 0x68 ]
mov r13, [ rsp + 0x148 ]
adcx r13, [ rsp + 0x60 ]
mov r10, r8
shrd r10, r12, 58
shr r12, 58
and r8, r14
adox r9, r10
adox r12, r13
mov [ r15 + 0x38 ], r8
and rdi, r14
mov rbp, r9
shrd rbp, r12, 57
shr r12, 57
mov [ r15 + 0x30 ], rdi
mov rdx, 0x39 
bzhi rcx, r9, rdx
adox rbp, [ rsp + 0x188 ]
adox r12, rbx
mov r13, rbp
shrd r13, r12, 58
and r11, r14
lea r13, [ r13 + r11 ]
mov r10, r13
shr r10, 58
and r13, r14
mov [ r15 + 0x8 ], r13
lea r10, [ r10 + rax ]
mov [ r15 + 0x10 ], r10
mov [ r15 + 0x40 ], rcx
and rbp, r14
mov [ r15 + 0x0 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 544
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.5220
; seed 2668774390023794 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 20111 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=88, initial num_batches=31): 587 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.029188006563572174
; number reverted permutation / tried permutation: 377 / 508 =74.213%
; number reverted decision / tried decision: 322 / 491 =65.580%
; validated in 2.637s
