SECTION .text
	GLOBAL fiat_p521_carry_mul
fiat_p521_carry_mul:
sub rsp, 496
mov rax, rdx
mov rdx, [ rdx + 0x10 ]
mulx r11, r10, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x38 ]
mulx r8, rcx, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov r9, rdx
shl r9, 0x1
mov rdx, 0x1 
mov [ rsp - 0x80 ], rbx
shlx rbx, [ rax + 0x18 ], rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x20 ]
imul rdx, [ rax + 0x38 ], 0x2
mov [ rsp - 0x58 ], r15
mov r15, [ rax + 0x20 ]
mov [ rsp - 0x50 ], rdi
lea rdi, [r15 + r15]
mov [ rsp - 0x48 ], r14
mulx r14, r15, [ rsi + 0x30 ]
mov [ rsp - 0x40 ], r13
mov r13, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x38 ], r12
mov [ rsp - 0x30 ], rbp
mulx rbp, r12, [ rsi + 0x10 ]
mov rdx, rdi
mov [ rsp - 0x28 ], r11
mulx r11, rdi, [ rsi + 0x30 ]
mov [ rsp - 0x20 ], r10
mov r10, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x18 ], r14
mov [ rsp - 0x10 ], r15
mulx r15, r14, rbx
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x8 ], rbp
mov [ rsp + 0x0 ], r12
mulx r12, rbp, [ rsi + 0x20 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x8 ], r12
lea r12, [rdx + rdx]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x10 ], rbp
mov [ rsp + 0x18 ], r11
mulx r11, rbp, r12
mov rdx, 0x1 
mov [ rsp + 0x20 ], rdi
shlx rdi, [ rax + 0x40 ], rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x28 ], r11
mov [ rsp + 0x30 ], rbp
mulx rbp, r11, r12
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x38 ], rbp
mov [ rsp + 0x40 ], r11
mulx r11, rbp, rdi
mov rdx, rdi
mov [ rsp + 0x48 ], r15
mulx r15, rdi, [ rsi + 0x28 ]
mov [ rsp + 0x50 ], r15
xor r15, r15
adox rbp, rcx
adox r8, r11
mov rcx, rdx
mov rdx, [ rsi + 0x38 ]
mulx r15, r11, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x58 ], r15
mov [ rsp + 0x60 ], r11
mulx r11, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x68 ], r8
mov [ rsp + 0x70 ], rbp
mulx rbp, r8, r10
imul rdx, [ rax + 0x10 ], 0x2
mov [ rsp + 0x78 ], rdi
mov [ rsp + 0x80 ], r11
mulx r11, rdi, [ rsi + 0x38 ]
xchg rdx, r9
mov [ rsp + 0x88 ], r15
mov [ rsp + 0x90 ], rbp
mulx rbp, r15, [ rsi + 0x40 ]
mov rdx, r9
mov [ rsp + 0x98 ], r8
mulx r8, r9, [ rsi + 0x40 ]
xor rdx, rdx
adox r9, r14
adox r8, [ rsp + 0x48 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xa0 ], r8
mulx r8, r14, rbx
adcx r15, rdi
adcx r11, rbp
test al, al
adox r15, r14
adox r8, r11
mov rdx, r10
mulx rdi, r10, [ rsi + 0x40 ]
adcx r10, [ rsp + 0x30 ]
adcx rdi, [ rsp + 0x28 ]
mulx r14, rbp, [ rsi + 0x28 ]
add r15, rbp
adcx r14, r8
mov rdx, [ rax + 0x30 ]
lea r11, [rdx + rdx]
mov rdx, [ rsi + 0x40 ]
mulx rbp, r8, r13
mov rdx, rcx
mov [ rsp + 0xa8 ], r9
mulx r9, rcx, [ rsi + 0x38 ]
mov [ rsp + 0xb0 ], r14
xor r14, r14
adox r8, rcx
adox r9, rbp
mov rbp, rdx
mov rdx, [ rsi + 0x30 ]
mulx r14, rcx, r11
adcx r10, rcx
adcx r14, rdi
mov rdx, [ rsi + 0x28 ]
mulx rcx, rdi, r13
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xb8 ], r14
mov [ rsp + 0xc0 ], r10
mulx r10, r14, r12
mov rdx, rbx
mov [ rsp + 0xc8 ], rcx
mulx rcx, rbx, [ rsi + 0x40 ]
test al, al
adox rbx, [ rsp + 0x98 ]
adox rcx, [ rsp + 0x90 ]
adcx rbx, r14
adcx r10, rcx
mov rdx, [ rax + 0x0 ]
mulx rcx, r14, [ rsi + 0x30 ]
xor rdx, rdx
adox r8, r14
adox rcx, r9
mov rdx, [ rax + 0x8 ]
mulx r14, r9, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xd0 ], rdi
mov [ rsp + 0xd8 ], r15
mulx r15, rdi, r11
adcx rbx, rdi
adcx r15, r10
test al, al
adox r8, r9
adox r14, rcx
mov rdx, r12
mulx r10, r12, [ rsi + 0x20 ]
mov rcx, rdx
mov rdx, [ rsi + 0x18 ]
mulx rdi, r9, r11
mov rdx, r12
adcx rdx, [ rsp + 0xd8 ]
adcx r10, [ rsp + 0xb0 ]
xchg rdx, r11
mov [ rsp + 0xe0 ], r14
mulx r14, r12, [ rsi + 0x20 ]
test al, al
adox r11, r9
adox rdi, r10
mov r9, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xe8 ], r8
mulx r8, r10, r13
adcx rbx, r10
adcx r8, r15
mov rdx, [ rsi + 0x10 ]
mulx r10, r15, r13
mov rdx, [ rsp + 0x20 ]
mov [ rsp + 0xf0 ], rdi
mov rdi, rdx
add rdi, [ rsp + 0xa8 ]
mov [ rsp + 0xf8 ], r11
mov r11, [ rsp + 0x18 ]
adcx r11, [ rsp + 0xa0 ]
mov rdx, rcx
mov [ rsp + 0x100 ], r10
mulx r10, rcx, [ rsi + 0x28 ]
xor rdx, rdx
adox rdi, rcx
adox r10, r11
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, r13
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x108 ], r15
mov [ rsp + 0x110 ], rcx
mulx rcx, r15, rbp
adcx rbx, r15
adcx rcx, r8
test al, al
adox rdi, r12
adox r14, r10
mov rdx, [ rax + 0x0 ]
mulx r8, r12, [ rsi + 0x10 ]
adcx rbx, r12
adcx r8, rcx
mov rdx, [ rax + 0x8 ]
mulx r15, r10, [ rsi + 0x8 ]
add rbx, r10
adcx r15, r8
mov rdx, [ rsi + 0x20 ]
mulx r12, rcx, rbp
test al, al
adox rdi, r11
adox r14, [ rsp + 0x110 ]
mov rdx, [ rsp + 0xf8 ]
adcx rdx, [ rsp + 0x108 ]
mov r11, [ rsp + 0xf0 ]
adcx r11, [ rsp + 0x100 ]
xchg rdx, rbp
mulx r10, r8, [ rsi + 0x10 ]
mov [ rsp + 0x118 ], r12
xor r12, r12
adox rdi, r8
adox r10, r14
mulx r8, r14, [ rsi + 0x8 ]
adcx rbx, [ rsp + 0x88 ]
adcx r15, [ rsp + 0x80 ]
add rbp, r14
adcx r8, r11
mov r11, rdx
mov rdx, [ rsi + 0x0 ]
mulx r12, r14, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x120 ], r15
mov [ rsp + 0x128 ], rbx
mulx rbx, r15, [ rsi + 0x8 ]
xor rdx, rdx
adox rdi, r15
adox rbx, r10
mov r10, [ rsp + 0xc0 ]
adcx r10, [ rsp + 0xd0 ]
mov r15, [ rsp + 0xb8 ]
adcx r15, [ rsp + 0xc8 ]
test al, al
adox rdi, r14
adox r12, rbx
adcx r10, rcx
adcx r15, [ rsp + 0x118 ]
mov rdx, [ rax + 0x0 ]
mulx r14, rcx, [ rsi + 0x18 ]
xor rdx, rdx
adox r10, rcx
adox r14, r15
mov rdx, [ rax + 0x0 ]
mulx r15, rbx, [ rsi + 0x0 ]
adcx rbp, rbx
adcx r15, r8
mov rdx, rbp
shrd rdx, r15, 58
shr r15, 58
test al, al
adox rdi, rdx
adox r15, r12
mov r8, rdi
shrd r8, r15, 58
shr r15, 58
mov rdx, [ rsi + 0x0 ]
mulx rcx, r12, [ rax + 0x18 ]
mov rdx, r8
add rdx, [ rsp + 0x128 ]
adcx r15, [ rsp + 0x120 ]
mov rbx, 0x3ffffffffffffff 
and rbp, rbx
adox r10, [ rsp + 0x0 ]
adox r14, [ rsp - 0x8 ]
mov r8, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x130 ], rbp
mulx rbp, rbx, [ rax + 0x10 ]
adcx r10, rbx
adcx rbp, r14
xor rdx, rdx
adox r10, r12
adox rcx, rbp
mov rdx, r9
mulx r12, r9, [ rsi + 0x38 ]
mov r14, 0x3ffffffffffffff 
and rdi, r14
mov rbx, r9
adox rbx, [ rsp + 0x40 ]
adox r12, [ rsp + 0x38 ]
mov rbp, r8
shrd rbp, r15, 58
shr r15, 58
xor r9, r9
adox rbx, [ rsp - 0x10 ]
adox r12, [ rsp - 0x18 ]
adcx r10, rbp
adcx r15, rcx
mov rcx, r10
shrd rcx, r15, 58
shr r15, 58
and r10, r14
and r8, r14
mulx r9, rbp, [ rsi + 0x40 ]
mov rdx, [ rsp + 0xe8 ]
adox rdx, [ rsp - 0x20 ]
mov r14, [ rsp + 0xe0 ]
adox r14, [ rsp - 0x28 ]
mov [ rsp + 0x138 ], r8
mov r8, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x140 ], rdi
mov [ rsp + 0x148 ], r10
mulx r10, rdi, r13
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x150 ], r15
mulx r15, r13, [ rax + 0x0 ]
adcx rbx, [ rsp + 0x78 ]
adcx r12, [ rsp + 0x50 ]
add rbx, r13
adcx r15, r12
add rbp, rdi
adcx r10, r9
mov rdx, [ rax + 0x18 ]
mulx rdi, r9, [ rsi + 0x18 ]
mov rdx, r11
mulx r13, r11, [ rsi + 0x30 ]
add rbp, r11
adcx r13, r10
add rbx, [ rsp - 0x30 ]
adcx r15, [ rsp - 0x38 ]
mov rdx, [ rax + 0x0 ]
mulx r10, r12, [ rsi + 0x28 ]
add rbp, r12
adcx r10, r13
xor rdx, rdx
adox rbp, [ rsp + 0x10 ]
adox r10, [ rsp + 0x8 ]
adcx r8, r9
adcx rdi, r14
mov rdx, [ rax + 0x18 ]
mulx r9, r14, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx r13, r11, [ rax + 0x20 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x158 ], rcx
mulx rcx, r12, [ rsi + 0x18 ]
test al, al
adox rbp, r12
adox rcx, r10
mov rdx, [ rsi + 0x10 ]
mulx r12, r10, [ rax + 0x10 ]
adcx rbx, r10
adcx r12, r15
test al, al
adox r8, [ rsp - 0x40 ]
adox rdi, [ rsp - 0x48 ]
adcx rbx, r14
adcx r9, r12
mov rdx, [ rsi + 0x8 ]
mulx r14, r15, [ rax + 0x20 ]
mov rdx, [ rax + 0x18 ]
mulx r12, r10, [ rsi + 0x10 ]
xor rdx, rdx
adox rbp, r10
adox r12, rcx
mov rdx, [ rax + 0x18 ]
mulx r10, rcx, [ rsi + 0x28 ]
adcx rbp, r15
adcx r14, r12
mov rdx, [ rax + 0x10 ]
mulx r12, r15, [ rsi + 0x28 ]
test al, al
adox rbx, r11
adox r13, r9
mov rdx, [ rax + 0x8 ]
mulx r9, r11, [ rsi + 0x30 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x160 ], r10
mov [ rsp + 0x168 ], rcx
mulx rcx, r10, [ rsi + 0x0 ]
adcx rbx, [ rsp + 0x158 ]
adcx r13, [ rsp + 0x150 ]
mov rdx, r11
test al, al
adox rdx, [ rsp + 0x70 ]
adox r9, [ rsp + 0x68 ]
adcx rdx, r15
adcx r12, r9
mov r15, rdx
mov rdx, [ rax + 0x18 ]
mulx r9, r11, [ rsi + 0x20 ]
add r15, r11
adcx r9, r12
mov rdx, [ rax + 0x28 ]
mulx r11, r12, [ rsi + 0x0 ]
add rbp, r12
adcx r11, r14
mov rdx, [ rsi + 0x8 ]
mulx r12, r14, [ rax + 0x28 ]
add r8, r14
adcx r12, rdi
mov rdx, rbx
shrd rdx, r13, 58
shr r13, 58
test al, al
adox r8, r10
adox rcx, r12
adcx rbp, rdx
adcx r13, r11
mov rdi, rbp
shrd rdi, r13, 58
shr r13, 58
mov r10, 0x3ffffffffffffff 
and rbp, r10
mov rdx, [ rax + 0x0 ]
mulx r14, r11, [ rsi + 0x40 ]
adox r11, [ rsp + 0x60 ]
adox r14, [ rsp + 0x58 ]
and rbx, r10
mov rdx, [ rax + 0x20 ]
mulx r10, r12, [ rsi + 0x18 ]
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x28 ], rbp
adox r15, r12
adox r10, r9
mov [ rdx + 0x20 ], rbx
mov r9, rdx
mov rdx, [ rax + 0x28 ]
mulx rbx, rbp, [ rsi + 0x10 ]
adcx r15, rbp
adcx rbx, r10
mov rdx, [ rsi + 0x30 ]
mulx r10, r12, [ rax + 0x10 ]
test al, al
adox r11, r12
adox r10, r14
adcx r8, rdi
adcx r13, rcx
mov rdx, r8
shrd rdx, r13, 58
shr r13, 58
mov rcx, 0x3ffffffffffffff 
and r8, rcx
mov rdi, rdx
mov rdx, [ rsi + 0x20 ]
mulx rbp, r14, [ rax + 0x20 ]
mov [ r9 + 0x30 ], r8
adox r11, [ rsp + 0x168 ]
adox r10, [ rsp + 0x160 ]
adcx r11, r14
adcx rbp, r10
mov rdx, [ rax + 0x28 ]
mulx r8, r12, [ rsi + 0x18 ]
add r11, r12
adcx r8, rbp
mov rdx, [ rsi + 0x0 ]
mulx r10, r14, [ rax + 0x38 ]
mov rdx, [ rsi + 0x10 ]
mulx r12, rbp, [ rax + 0x30 ]
add r11, rbp
adcx r12, r8
mov rdx, [ rax + 0x30 ]
mulx rbp, r8, [ rsi + 0x8 ]
test al, al
adox r15, r8
adox rbp, rbx
adcx r15, r14
adcx r10, rbp
mov rdx, [ rax + 0x38 ]
mulx r14, rbx, [ rsi + 0x8 ]
xor rdx, rdx
adox r11, rbx
adox r14, r12
mov rdx, [ rsi + 0x0 ]
mulx r8, r12, [ rax + 0x40 ]
adcx r15, rdi
adcx r13, r10
add r11, r12
adcx r8, r14
mov rdx, r15
shrd rdx, r13, 58
shr r13, 58
test al, al
adox r11, rdx
adox r13, r8
and r15, rcx
mov [ r9 + 0x38 ], r15
mov rdi, [ rsp + 0x148 ]
mov [ r9 + 0x18 ], rdi
mov rdi, r11
shrd rdi, r13, 57
shr r13, 57
add rdi, [ rsp + 0x130 ]
adc r13, 0x0
mov rbp, rdi
and rbp, rcx
mov [ r9 + 0x0 ], rbp
shrd rdi, r13, 58
add rdi, [ rsp + 0x140 ]
mov r10, rdi
shr r10, 58
add r10, [ rsp + 0x138 ]
and rdi, rcx
mov [ r9 + 0x10 ], r10
mov [ r9 + 0x8 ], rdi
mov rbx, 0x1ffffffffffffff 
and r11, rbx
mov [ r9 + 0x40 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 496
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.3596
; seed 0785582825000784 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 6857126 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=53, initial num_batches=31): 137195 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.020007653352147825
; number reverted permutation / tried permutation: 65596 / 89874 =72.987%
; number reverted decision / tried decision: 55427 / 90125 =61.500%
; validated in 4.556s
