SECTION .text
	GLOBAL fiat_p521_carry_mul
fiat_p521_carry_mul:
sub rsp, 568
mov rax, [ rdx + 0x40 ]
mov r10, rax
shl r10, 0x1
imul rax, [ rdx + 0x20 ], 0x2
mov r11, 0x1 
shlx rcx, [ rdx + 0x8 ], r11
mov r8, [ rdx + 0x38 ]
lea r9, [r8 + r8]
mov r8, [ rdx + 0x18 ]
lea r11, [r8 + r8]
mov r8, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, r11
mov rdx, [ r8 + 0x10 ]
mov [ rsp - 0x70 ], r12
lea r12, [rdx + rdx]
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, r12
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ r8 + 0x10 ]
mov rdx, [ r8 + 0x0 ]
mov [ rsp - 0x48 ], rdi
mov [ rsp - 0x40 ], r15
mulx r15, rdi, [ rsi + 0x0 ]
mov rdx, [ r8 + 0x0 ]
mov [ rsp - 0x38 ], r15
mov [ rsp - 0x30 ], rdi
mulx rdi, r15, [ rsi + 0x30 ]
mov rdx, [ r8 + 0x20 ]
mov [ rsp - 0x28 ], rdi
mov [ rsp - 0x20 ], r15
mulx r15, rdi, [ rsi + 0x20 ]
mov rdx, rax
mov [ rsp - 0x18 ], r15
mulx r15, rax, [ rsi + 0x28 ]
mov [ rsp - 0x10 ], rdi
mov [ rsp - 0x8 ], r15
mulx r15, rdi, [ rsi + 0x38 ]
mov [ rsp + 0x0 ], rax
mov rax, [ r8 + 0x30 ]
mov [ rsp + 0x8 ], r9
lea r9, [rax + rax]
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x10 ], r15
mov [ rsp + 0x18 ], rdi
mulx rdi, r15, [ r8 + 0x18 ]
mov rdx, r9
mov [ rsp + 0x20 ], rdi
mulx rdi, r9, [ rsi + 0x20 ]
mov [ rsp + 0x28 ], r15
mov r15, rdx
mov rdx, [ r8 + 0x30 ]
mov [ rsp + 0x30 ], rdi
mov [ rsp + 0x38 ], r9
mulx r9, rdi, [ rsi + 0x10 ]
mov rdx, [ r8 + 0x18 ]
mov [ rsp + 0x40 ], r9
mov [ rsp + 0x48 ], rdi
mulx rdi, r9, [ rsi + 0x8 ]
mov rdx, [ r8 + 0x0 ]
mov [ rsp + 0x50 ], rdi
mov [ rsp + 0x58 ], r9
mulx r9, rdi, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x60 ], r9
mov [ rsp + 0x68 ], rdi
mulx rdi, r9, r12
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x70 ], r14
mulx r14, r12, [ r8 + 0x8 ]
mov rdx, r15
mov [ rsp + 0x78 ], r14
mulx r14, r15, [ rsi + 0x40 ]
mov [ rsp + 0x80 ], r14
mov [ rsp + 0x88 ], r15
mulx r15, r14, [ rsi + 0x30 ]
mov [ rsp + 0x90 ], r12
mov r12, rdx
mov rdx, [ r8 + 0x8 ]
mov [ rsp + 0x98 ], r15
mov [ rsp + 0xa0 ], r14
mulx r14, r15, [ rsi + 0x20 ]
mov rdx, r10
mov [ rsp + 0xa8 ], r14
mulx r14, r10, [ rsi + 0x10 ]
mov [ rsp + 0xb0 ], r15
mov r15, rdx
mov rdx, [ r8 + 0x10 ]
mov [ rsp + 0xb8 ], r14
mov [ rsp + 0xc0 ], r10
mulx r10, r14, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xc8 ], r10
mov [ rsp + 0xd0 ], r14
mulx r14, r10, [ r8 + 0x8 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xd8 ], r14
mov [ rsp + 0xe0 ], r10
mulx r10, r14, r15
mov rdx, rax
mov [ rsp + 0xe8 ], r10
mulx r10, rax, [ rsi + 0x30 ]
add r9, rbx
adcx rbp, rdi
mov rbx, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0xf0 ], r14
mulx r14, rdi, rcx
mov rdx, [ r8 + 0x28 ]
lea rcx, [rdx + rdx]
xor rdx, rdx
adox r9, rax
adox r10, rbp
adcx rdi, r13
adcx r14, [ rsp + 0x70 ]
mov rdx, [ rsi + 0x40 ]
mulx rax, r13, r11
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xf8 ], r10
mulx r10, rbp, rcx
test al, al
adox r13, [ rsp + 0x18 ]
adox rax, [ rsp + 0x10 ]
adcx r13, rbp
adcx r10, rax
mov rdx, [ rsi + 0x28 ]
mulx rax, rbp, r12
add r13, rbp
adcx rax, r10
mov rdx, r11
mulx r10, r11, [ rsi + 0x30 ]
add rdi, r11
adcx r10, r14
mov rdx, rbx
mulx r14, rbx, [ rsi + 0x40 ]
mov rdx, [ rsi + 0x10 ]
mulx r11, rbp, [ rsp + 0x8 ]
mov rdx, rcx
mov [ rsp + 0x100 ], r9
mulx r9, rcx, [ rsi + 0x38 ]
add rbx, rcx
adcx r9, r14
xor r14, r14
adox rdi, [ rsp + 0x0 ]
adox r10, [ rsp - 0x8 ]
mov rcx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x108 ], r9
mulx r9, r14, [ rsp + 0x8 ]
adcx r13, r14
adcx r9, rax
mov rdx, [ rsi + 0x20 ]
mulx r14, rax, rcx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x110 ], r9
mov [ rsp + 0x118 ], r13
mulx r13, r9, r12
xor rdx, rdx
adox rdi, rax
adox r14, r10
adcx rdi, r9
adcx r13, r14
mov rdx, [ rsi + 0x28 ]
mulx rax, r10, [ rsp + 0x8 ]
xor rdx, rdx
adox rdi, rbp
adox r11, r13
adcx rbx, [ rsp + 0xa0 ]
mov rbp, [ rsp + 0x108 ]
adcx rbp, [ rsp + 0x98 ]
mov rdx, [ rsi + 0x28 ]
mulx r14, r9, rcx
xor rdx, rdx
adox rbx, r10
adox rax, rbp
mov rdx, [ rsi + 0x8 ]
mulx r10, r13, r15
adcx rdi, r13
adcx r10, r11
mov rdx, r9
add rdx, [ rsp + 0x100 ]
adcx r14, [ rsp + 0xf8 ]
mov r11, rdx
mov rdx, [ rsi + 0x18 ]
mulx r9, rbp, [ rsp + 0x8 ]
xor rdx, rdx
adox r11, [ rsp + 0x38 ]
adox r14, [ rsp + 0x30 ]
adcx rdi, [ rsp - 0x30 ]
adcx r10, [ rsp - 0x38 ]
mov rdx, rcx
mulx r13, rcx, [ rsi + 0x40 ]
add r11, rbp
adcx r9, r14
mov rdx, [ rsi + 0x20 ]
mulx r14, rbp, r15
add rbx, rbp
adcx r14, rax
mov rdx, [ r8 + 0x0 ]
mulx rbp, rax, [ rsi + 0x18 ]
add rbx, rax
adcx rbp, r14
add rbx, [ rsp + 0x90 ]
adcx rbp, [ rsp + 0x78 ]
mov rdx, [ rsi + 0x8 ]
mulx rax, r14, [ r8 + 0x10 ]
xor rdx, rdx
adox rbx, r14
adox rax, rbp
adcx rbx, [ rsp + 0x28 ]
adcx rax, [ rsp + 0x20 ]
mov rdx, r12
mulx rbp, r12, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x120 ], rax
mulx rax, r14, r15
mov rdx, r14
mov [ rsp + 0x128 ], rbx
xor rbx, rbx
adox rdx, [ rsp + 0x118 ]
adox rax, [ rsp + 0x110 ]
adcx rcx, r12
adcx rbp, r13
mov r13, rdx
mov rdx, [ r8 + 0x8 ]
mulx r14, r12, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x130 ], r10
mulx r10, rbx, [ rsp + 0x8 ]
xor rdx, rdx
adox rcx, rbx
adox r10, rbp
adcx r11, [ rsp + 0xc0 ]
adcx r9, [ rsp + 0xb8 ]
add r11, [ rsp + 0x68 ]
adcx r9, [ rsp + 0x60 ]
mov rdx, [ rsi + 0x28 ]
mulx rbx, rbp, r15
test al, al
adox rcx, rbp
adox rbx, r10
mov rdx, [ r8 + 0x8 ]
mulx rbp, r10, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x138 ], r9
mov [ rsp + 0x140 ], r11
mulx r11, r9, [ r8 + 0x0 ]
mov rdx, [ r8 + 0x0 ]
mov [ rsp + 0x148 ], rdi
mov [ rsp + 0x150 ], r14
mulx r14, rdi, [ rsi + 0x20 ]
adcx rcx, rdi
adcx r14, rbx
test al, al
adox rcx, r10
adox rbp, r14
mov rdx, [ r8 + 0x8 ]
mulx r10, rbx, [ rsi + 0x0 ]
adcx rcx, [ rsp - 0x40 ]
adcx rbp, [ rsp - 0x48 ]
xor rdx, rdx
adox r13, r9
adox r11, rax
adcx r13, r12
adcx r11, [ rsp + 0x150 ]
mov rax, [ rsp + 0x130 ]
mov r12, [ rsp + 0x148 ]
shrd r12, rax, 58
shr rax, 58
mov r9, rbx
test al, al
adox r9, [ rsp + 0x140 ]
adox r10, [ rsp + 0x138 ]
adcx r9, r12
adcx rax, r10
mov rdx, [ r8 + 0x10 ]
mulx r14, rdi, [ rsi + 0x0 ]
test al, al
adox r13, rdi
adox r14, r11
mov rdx, 0x3a 
bzhi rbx, r9, rdx
mov rdx, [ r8 + 0x20 ]
mulx r12, r11, [ rsi + 0x0 ]
mov rdx, [ r8 + 0x0 ]
mulx rdi, r10, [ rsi + 0x38 ]
shrd r9, rax, 58
shr rax, 58
add r13, r9
adcx rax, r14
add rcx, [ rsp + 0x58 ]
adcx rbp, [ rsp + 0x50 ]
mov rdx, 0x3ffffffffffffff 
mov r14, r13
and r14, rdx
mov rdx, [ r8 + 0x8 ]
mov [ rsp + 0x158 ], r14
mulx r14, r9, [ rsi + 0x30 ]
adox rcx, r11
adox r12, rbp
mov rdx, [ rsi + 0x40 ]
mulx rbp, r11, r15
adcx r11, r10
adcx rdi, rbp
shrd r13, rax, 58
shr rax, 58
mov rdx, [ rsi + 0x28 ]
mulx rbp, r10, [ r8 + 0x10 ]
test al, al
adox r11, r9
adox r14, rdi
adcx r11, r10
adcx rbp, r14
mov rdx, r13
add rdx, [ rsp + 0x128 ]
adcx rax, [ rsp + 0x120 ]
mov r9, rdx
shrd r9, rax, 58
shr rax, 58
mov rdi, rdx
mov rdx, [ rsi + 0x40 ]
mulx r10, r13, [ rsp + 0x8 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x160 ], rbx
mulx rbx, r14, [ rsp + 0x8 ]
test al, al
adox r13, [ rsp + 0xf0 ]
adox r10, [ rsp + 0xe8 ]
mov rdx, [ r8 + 0x0 ]
mov [ rsp + 0x168 ], rbp
mov [ rsp + 0x170 ], r11
mulx r11, rbp, [ rsi + 0x28 ]
mov rdx, r14
adcx rdx, [ rsp + 0x88 ]
adcx rbx, [ rsp + 0x80 ]
xor r14, r14
adox r13, [ rsp - 0x20 ]
adox r10, [ rsp - 0x28 ]
adcx rcx, r9
adcx rax, r12
mov r12, rdx
mov rdx, [ rsi + 0x20 ]
mulx r14, r9, [ r8 + 0x18 ]
mov rdx, r15
mov [ rsp + 0x178 ], r14
mulx r14, r15, [ rsi + 0x30 ]
xor rdx, rdx
adox r12, r15
adox r14, rbx
adcx r12, rbp
adcx r11, r14
add r12, [ rsp + 0xb0 ]
adcx r11, [ rsp + 0xa8 ]
mov rbp, 0x3ffffffffffffff 
mov rbx, rcx
and rbx, rbp
and rdi, rbp
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x20 ], rbx
mov rdx, [ rsi + 0x18 ]
mulx rbx, r14, [ r8 + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mulx r15, rbp, [ r8 + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x180 ], rdi
mov [ rsp + 0x188 ], r9
mulx r9, rdi, [ r8 + 0x10 ]
adox r13, [ rsp + 0xe0 ]
adox r10, [ rsp + 0xd8 ]
adcx r13, rdi
adcx r9, r10
mov rdx, [ r8 + 0x20 ]
mulx r10, rdi, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x190 ], r10
mov [ rsp + 0x198 ], rdi
mulx rdi, r10, [ r8 + 0x28 ]
test al, al
adox r13, rbp
adox r15, r9
mov rdx, [ r8 + 0x20 ]
mulx r9, rbp, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x1a0 ], r15
mov [ rsp + 0x1a8 ], r13
mulx r13, r15, [ r8 + 0x18 ]
adcx r12, r14
adcx rbx, r11
mov rdx, [ rsp + 0x170 ]
xor r11, r11
adox rdx, [ rsp + 0x188 ]
mov r14, [ rsp + 0x168 ]
adox r14, [ rsp + 0x178 ]
adcx r12, r15
adcx r13, rbx
xor r15, r15
adox r12, rbp
adox r9, r13
mov r11, rdx
mov rdx, [ r8 + 0x0 ]
mulx rbx, rbp, [ rsi + 0x40 ]
adcx r11, [ rsp + 0x198 ]
adcx r14, [ rsp + 0x190 ]
mov rdx, [ rsi + 0x38 ]
mulx r15, r13, [ r8 + 0x8 ]
add rbp, r13
adcx r15, rbx
add rbp, [ rsp + 0xd0 ]
adcx r15, [ rsp + 0xc8 ]
mov rdx, [ rsi + 0x10 ]
mulx r13, rbx, [ r8 + 0x20 ]
add r12, r10
adcx rdi, r9
shrd rcx, rax, 58
shr rax, 58
add r12, rcx
adcx rax, rdi
mov rdx, [ r8 + 0x18 ]
mulx r9, r10, [ rsi + 0x28 ]
xor rdx, rdx
adox rbp, r10
adox r9, r15
mov r15, r12
shrd r15, rax, 58
shr rax, 58
mov rdx, [ rsi + 0x10 ]
mulx rcx, rdi, [ r8 + 0x28 ]
test al, al
adox r11, rdi
adox rcx, r14
adcx rbp, [ rsp - 0x10 ]
adcx r9, [ rsp - 0x18 ]
mov rdx, [ r8 + 0x30 ]
mulx r10, r14, [ rsi + 0x8 ]
xor rdx, rdx
adox r11, r14
adox r10, rcx
mov rdx, [ r8 + 0x38 ]
mulx rcx, rdi, [ rsi + 0x0 ]
mov rdx, [ r8 + 0x30 ]
mov [ rsp + 0x1b0 ], r9
mulx r9, r14, [ rsi + 0x0 ]
mov rdx, rbx
adcx rdx, [ rsp + 0x1a8 ]
adcx r13, [ rsp + 0x1a0 ]
xor rbx, rbx
adox r11, rdi
adox rcx, r10
mov r10, rdx
mov rdx, [ r8 + 0x28 ]
mulx rbx, rdi, [ rsi + 0x8 ]
adcx r10, rdi
adcx rbx, r13
add r10, r14
adcx r9, rbx
add r10, r15
adcx rax, r9
mov rdx, r10
shrd rdx, rax, 58
shr rax, 58
mov r15, rdx
mov rdx, [ r8 + 0x40 ]
mulx r13, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mulx rbx, rdi, [ r8 + 0x28 ]
mov rdx, 0x3ffffffffffffff 
and r10, rdx
adox r11, r15
adox rax, rcx
adcx rbp, rdi
adcx rbx, [ rsp + 0x1b0 ]
mov rcx, r11
shrd rcx, rax, 58
shr rax, 58
add rbp, [ rsp + 0x48 ]
adcx rbx, [ rsp + 0x40 ]
mov r9, [ rsp + 0x148 ]
and r9, rdx
and r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx rdi, r15, [ r8 + 0x38 ]
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x38 ], r11
adox rbp, r15
adox rdi, rbx
adcx rbp, r14
adcx r13, rdi
xor r14, r14
adox rbp, rcx
adox rax, r13
mov rcx, 0x39 
bzhi rbx, rbp, rcx
mov [ rdx + 0x40 ], rbx
shrd rbp, rax, 57
shr rax, 57
xor r11, r11
adox rbp, r9
adox rax, r11
mov r14, 0x3ffffffffffffff 
mov r9, rbp
and r9, r14
shrd rbp, rax, 58
add rbp, [ rsp + 0x160 ]
mov r15, rbp
and r15, r14
mov [ rdx + 0x0 ], r9
shr rbp, 58
mov rdi, [ rsp + 0x180 ]
mov [ rdx + 0x18 ], rdi
add rbp, [ rsp + 0x158 ]
and r12, r14
mov [ rdx + 0x10 ], rbp
mov [ rdx + 0x8 ], r15
mov [ rdx + 0x28 ], r12
mov [ rdx + 0x30 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 568
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.3870
; seed 1547510975833449 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 9289998 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=98, initial num_batches=31): 215602 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.023207970550693336
; number reverted permutation / tried permutation: 64579 / 90032 =71.729%
; number reverted decision / tried decision: 54023 / 89967 =60.048%
; validated in 6.471s
