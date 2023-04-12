SECTION .text
	GLOBAL fiat_p521_carry_square
fiat_p521_carry_square:
sub rsp, 576
mov rax, [ rsi + 0x40 ]
mov r10, rax
shl r10, 0x1
mov rax, [ rsi + 0x18 ]
mov r11, rax
shl r11, 0x1
imul rax, [ rsi + 0x10 ], 0x2
mov rdx, [ rsi + 0x28 ]
mov rcx, rdx
shl rcx, 0x2
mov rdx, 0x1 
shlx r8, [ rsi + 0x20 ], rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x78 ], rbp
mov rbp, rdx
shl rbp, 0x2
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, r8
mov rdx, rbp
mov [ rsp - 0x60 ], r14
mulx r14, rbp, [ rsi + 0x20 ]
mov [ rsp - 0x58 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r14
mulx r14, rdi, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x40 ], rbp
mov [ rsp - 0x38 ], r14
mulx r14, rbp, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x30 ], r14
lea r14, [ 4 * rdx]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x28 ], rbp
mov [ rsp - 0x20 ], rdi
mulx rdi, rbp, rcx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x18 ], rdi
mulx rdi, rcx, r14
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], rbp
mov [ rsp - 0x8 ], r13
mulx r13, rbp, r14
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x0 ], r13
mov [ rsp + 0x8 ], rbp
mulx rbp, r13, r15
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x10 ], r12
mov r12, rdx
shl r12, 0x1
mov rdx, rax
mov [ rsp + 0x18 ], rbx
mulx rbx, rax, [ rsi + 0x0 ]
xchg rdx, r12
mov [ rsp + 0x20 ], rbx
mov [ rsp + 0x28 ], rax
mulx rax, rbx, [ rsi + 0x30 ]
mov [ rsp + 0x30 ], r9
mov r9, [ rsi + 0x8 ]
mov [ rsp + 0x38 ], r11
mov r11, r9
shl r11, 0x1
mov r9, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x40 ], rax
mov [ rsp + 0x48 ], rbx
mulx rbx, rax, r11
mov rdx, r10
mulx r11, r10, [ rsi + 0x0 ]
mov [ rsp + 0x50 ], rbx
mov rbx, [ rsi + 0x38 ]
mov [ rsp + 0x58 ], rax
mov rax, rbx
shl rax, 0x1
mov rbx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x60 ], r11
mov [ rsp + 0x68 ], r10
mulx r10, r11, rdx
xor rdx, rdx
adox r13, rcx
adox rdi, rbp
mov rdx, [ rsi + 0x8 ]
mulx rbp, rcx, rax
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x70 ], rbp
mov [ rsp + 0x78 ], rcx
mulx rcx, rbp, r14
mov rdx, rbp
adcx rdx, [ rsp + 0x48 ]
adcx rcx, [ rsp + 0x40 ]
xchg rdx, r12
mov [ rsp + 0x80 ], r10
mulx r10, rbp, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x88 ], r10
mov [ rsp + 0x90 ], rbp
mulx rbp, r10, r15
mov rdx, [ rsi + 0x40 ]
mov r15, rdx
shl r15, 0x2
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x98 ], r11
mov [ rsp + 0xa0 ], rbp
mulx rbp, r11, r15
mov rdx, r15
mov [ rsp + 0xa8 ], r10
mulx r10, r15, [ rsi + 0x8 ]
mov [ rsp + 0xb0 ], r10
mov [ rsp + 0xb8 ], r15
mulx r15, r10, [ rsi + 0x18 ]
xchg rdx, rbx
mov [ rsp + 0xc0 ], rdi
mov [ rsp + 0xc8 ], r13
mulx r13, rdi, [ rsi + 0x40 ]
mov rdx, r9
mov [ rsp + 0xd0 ], r15
mulx r15, r9, [ rsi + 0x0 ]
mov [ rsp + 0xd8 ], r15
mov [ rsp + 0xe0 ], r9
mulx r9, r15, [ rsi + 0x8 ]
xchg rdx, r8
mov [ rsp + 0xe8 ], r10
mov [ rsp + 0xf0 ], r9
mulx r9, r10, [ rsi + 0x18 ]
mov [ rsp + 0xf8 ], r15
xor r15, r15
adox rdi, r10
adox r9, r13
mulx r10, r13, [ rsi + 0x0 ]
mov r15, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x100 ], r10
mov [ rsp + 0x108 ], r13
mulx r13, r10, [ rsp + 0x38 ]
adcx r12, r11
adcx rbp, rcx
mov rdx, r15
mulx rcx, r15, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x110 ], r13
mulx r13, r11, rbx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x118 ], r10
mov r10, rdx
shl r10, 0x1
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x120 ], rbp
mov [ rsp + 0x128 ], r12
mulx r12, rbp, r10
test al, al
adox rdi, rbp
adox r12, r9
mov rdx, [ rsi + 0x30 ]
mulx rbp, r9, rbx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x130 ], rcx
mov [ rsp + 0x138 ], r15
mulx r15, rcx, rax
adcx rdi, [ rsp + 0xf8 ]
adcx r12, [ rsp + 0xf0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x140 ], r12
mov [ rsp + 0x148 ], rdi
mulx rdi, r12, r8
test al, al
adox rcx, r9
adox rbp, r15
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, [ rsp + 0x38 ]
mov rdx, r14
mulx r15, r14, [ rsi + 0x30 ]
adcx rcx, r8
adcx r9, rbp
test al, al
adox r11, [ rsp + 0x30 ]
adox r13, [ rsp + 0x18 ]
adcx rcx, [ rsp + 0x10 ]
adcx r9, [ rsp - 0x8 ]
test al, al
adox r11, [ rsp + 0x138 ]
adox r13, [ rsp + 0x130 ]
xchg rdx, rbx
mulx r8, rbp, [ rsi + 0x28 ]
adcx r14, rbp
adcx r8, r15
xor r15, r15
adox r14, [ rsp - 0x20 ]
adox r8, [ rsp - 0x38 ]
mov rbp, [ rsp + 0xe8 ]
mov [ rsp + 0x150 ], r9
mov r9, rbp
adcx r9, [ rsp + 0xc8 ]
mov [ rsp + 0x158 ], rcx
mov rcx, [ rsp + 0xd0 ]
adcx rcx, [ rsp + 0xc0 ]
mov rbp, [ rsp + 0xa8 ]
mov [ rsp + 0x160 ], rdi
mov rdi, rbp
mov [ rsp + 0x168 ], r12
xor r12, r12
adox rdi, [ rsp - 0x10 ]
mov r15, [ rsp + 0xa0 ]
adox r15, [ rsp - 0x18 ]
adcx r9, [ rsp + 0x98 ]
adcx rcx, [ rsp + 0x80 ]
xchg rdx, rbx
mulx r12, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x170 ], rcx
mov [ rsp + 0x178 ], r9
mulx r9, rcx, [ rsp + 0x38 ]
test al, al
adox rdi, rbp
adox r12, r15
adcx r14, rcx
adcx r9, r8
xor rdx, rdx
adox rdi, [ rsp + 0xb8 ]
adox r12, [ rsp + 0xb0 ]
mov rdx, [ rsi + 0x0 ]
mulx r15, r8, rdx
mov rdx, r10
mulx rbp, r10, [ rsi + 0x28 ]
adcx r10, [ rsp - 0x40 ]
adcx rbp, [ rsp - 0x48 ]
mov [ rsp + 0x180 ], rbp
mulx rbp, rcx, [ rsi + 0x18 ]
mov [ rsp + 0x188 ], r10
xor r10, r10
adox rdi, r8
adox r15, r12
mulx r8, r12, [ rsi + 0x8 ]
mov [ rsp + 0x190 ], r9
mov r9, rcx
adcx r9, [ rsp - 0x28 ]
adcx rbp, [ rsp - 0x30 ]
xor rcx, rcx
adox r11, r12
adox r8, r13
adcx r9, [ rsp + 0x168 ]
adcx rbp, [ rsp + 0x160 ]
test al, al
adox r9, [ rsp + 0x78 ]
adox rbp, [ rsp + 0x70 ]
mov r10, 0x3ffffffffffffff 
mov r13, rdi
and r13, r10
adox r14, [ rsp + 0x108 ]
mov r12, [ rsp + 0x100 ]
adox r12, [ rsp + 0x190 ]
mov rcx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x198 ], r13
mulx r13, r10, rbx
mov rdx, [ rsp + 0x90 ]
mov rbx, rdx
adcx rbx, [ rsp + 0x128 ]
mov [ rsp + 0x1a0 ], r8
mov r8, [ rsp + 0x88 ]
adcx r8, [ rsp + 0x120 ]
test al, al
adox rbx, [ rsp + 0x118 ]
adox r8, [ rsp + 0x110 ]
adcx r9, [ rsp + 0x68 ]
adcx rbp, [ rsp + 0x60 ]
mov rdx, [ rsp + 0x8 ]
mov [ rsp + 0x1a8 ], rbp
mov rbp, rdx
mov [ rsp + 0x1b0 ], r9
xor r9, r9
adox rbp, [ rsp + 0x188 ]
mov [ rsp + 0x1b8 ], r11
mov r11, [ rsp + 0x0 ]
adox r11, [ rsp + 0x180 ]
shrd rdi, r15, 58
shr r15, 58
xor rdx, rdx
adox rbp, r10
adox r13, r11
adcx rbp, [ rsp + 0x58 ]
adcx r13, [ rsp + 0x50 ]
add rbp, rdi
adcx r15, r13
mov r9, rbp
shrd r9, r15, 58
shr r15, 58
mov r10, [ rsp + 0x178 ]
add r10, [ rsp + 0x28 ]
mov r11, [ rsp + 0x170 ]
adcx r11, [ rsp + 0x20 ]
mov rdi, 0x3ffffffffffffff 
and rbp, rdi
adox r10, r9
adox r15, r11
mov rdx, rax
mulx r13, rax, [ rsi + 0x0 ]
mov rdx, r10
shrd rdx, r15, 58
shr r15, 58
mov r9, rax
xor r11, r11
adox r9, [ rsp + 0x148 ]
adox r13, [ rsp + 0x140 ]
xchg rdx, rcx
mulx r11, rax, [ rsi + 0x0 ]
adcx rbx, rcx
adcx r15, r8
and r10, rdi
mov rdx, rbx
shrd rdx, r15, 58
shr r15, 58
xor r8, r8
adox r14, rdx
adox r15, r12
mov r12, r14
shrd r12, r15, 58
shr r15, 58
and r14, rdi
mov rcx, rax
adox rcx, [ rsp + 0x158 ]
adox r11, [ rsp + 0x150 ]
and rbx, rdi
mov rax, [ rsp - 0x50 ]
mov [ rax + 0x18 ], rbx
adox rcx, r12
adox r15, r11
mov rdx, [ rsp + 0x1b8 ]
adcx rdx, [ rsp + 0xe0 ]
mov r12, [ rsp + 0x1a0 ]
adcx r12, [ rsp + 0xd8 ]
mov r11, rcx
and r11, rdi
shrd rcx, r15, 58
shr r15, 58
xor rbx, rbx
adox rdx, rcx
adox r15, r12
mov r8, rdx
shrd r8, r15, 58
shr r15, 58
xor r12, r12
adox r9, r8
adox r15, r13
mov rbx, r9
shrd rbx, r15, 58
shr r15, 58
and rdx, rdi
mov r13, rbx
adox r13, [ rsp + 0x1b0 ]
adox r15, [ rsp + 0x1a8 ]
mov [ rax + 0x30 ], rdx
mov rcx, r13
shrd rcx, r15, 57
shr r15, 57
and r9, rdi
adox rcx, [ rsp + 0x198 ]
adox r15, r12
mov r8, rcx
shrd r8, r15, 58
mov [ rax + 0x38 ], r9
and rcx, rdi
lea r8, [ r8 + rbp ]
mov rbp, r8
and rbp, rdi
mov [ rax + 0x8 ], rbp
shr r8, 58
lea r8, [ r8 + r10 ]
mov r10, 0x1ffffffffffffff 
and r13, r10
mov [ rax + 0x28 ], r11
mov [ rax + 0x10 ], r8
mov [ rax + 0x40 ], r13
mov [ rax + 0x20 ], r14
mov [ rax + 0x0 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 576
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.2032
; seed 0808168760228370 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 22384 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=109, initial num_batches=31): 683 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.03051286633309507
; number reverted permutation / tried permutation: 307 / 460 =66.739%
; number reverted decision / tried decision: 301 / 539 =55.844%
; validated in 2.084s
