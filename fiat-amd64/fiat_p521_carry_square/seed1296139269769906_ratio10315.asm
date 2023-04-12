SECTION .text
	GLOBAL fiat_p521_carry_square
fiat_p521_carry_square:
sub rsp, 576
imul rax, [ rsi + 0x38 ], 0x2
mov r10, 0x1 
shlx r11, [ rsi + 0x18 ], r10
mov rdx, [ rsi + 0x40 ]
lea rcx, [rdx + rdx]
mov rdx, [ rsi + 0x10 ]
mov r8, rdx
shl r8, 0x1
mov rdx, rcx
mulx r9, rcx, [ rsi + 0x0 ]
mov r10, 0x2 
mov [ rsp - 0x80 ], rbx
shlx rbx, [ rsi + 0x30 ], r10
mov [ rsp - 0x78 ], rbp
mov rbp, [ rsi + 0x28 ]
mov [ rsp - 0x70 ], r12
lea r12, [rbp + rbp]
xchg rdx, rbx
mov [ rsp - 0x68 ], r13
mulx r13, rbp, [ rsi + 0x28 ]
xchg rdx, r12
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x28 ]
xchg rdx, rax
mov [ rsp - 0x50 ], rdi
mulx rdi, r10, [ rsi + 0x38 ]
xchg rdx, rax
mov [ rsp - 0x48 ], r9
mov [ rsp - 0x40 ], rcx
mulx rcx, r9, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], r13
mov [ rsp - 0x30 ], rbp
mulx rbp, r13, [ rsi + 0x0 ]
mov [ rsp - 0x28 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x20 ], r13
mov [ rsp - 0x18 ], rdi
mulx rdi, r13, r11
mov rdx, [ rsi + 0x40 ]
mov [ rsp - 0x10 ], rdi
lea rdi, [ 4 * rdx]
mov rdx, rdi
mov [ rsp - 0x8 ], r13
mulx r13, rdi, [ rsi + 0x28 ]
mov [ rsp + 0x0 ], r13
imul r13, [ rsi + 0x30 ], 0x2
mov [ rsp + 0x8 ], rdi
mov [ rsp + 0x10 ], r10
mulx r10, rdi, [ rsi + 0x20 ]
xchg rdx, r13
mov [ rsp + 0x18 ], r10
mov [ rsp + 0x20 ], rdi
mulx rdi, r10, [ rsi + 0x8 ]
xchg rdx, r13
mov [ rsp + 0x28 ], rcx
mov [ rsp + 0x30 ], r9
mulx r9, rcx, [ rsi + 0x10 ]
mov [ rsp + 0x38 ], r9
mov [ rsp + 0x40 ], rcx
mulx rcx, r9, [ rsi + 0x8 ]
mov [ rsp + 0x48 ], rcx
mov rcx, [ rsi + 0x20 ]
mov [ rsp + 0x50 ], r9
mov r9, rcx
shl r9, 0x1
mov rcx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x58 ], rdi
mov [ rsp + 0x60 ], r10
mulx r10, rdi, rbp
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x68 ], r10
mov [ rsp + 0x70 ], rdi
mulx rdi, r10, r13
mov rdx, r8
mov [ rsp + 0x78 ], rdi
mulx rdi, r8, [ rsi + 0x8 ]
mov [ rsp + 0x80 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x88 ], r8
mov [ rsp + 0x90 ], r10
mulx r10, r8, rbx
mov rdx, 0x2 
shlx rbx, [ rsi + 0x28 ], rdx
mov rdx, r13
mov [ rsp + 0x98 ], rbx
mulx rbx, r13, [ rsi + 0x0 ]
mov [ rsp + 0xa0 ], rbx
mov rbx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xa8 ], r13
mov [ rsp + 0xb0 ], r10
mulx r10, r13, r12
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xb8 ], r8
mov [ rsp + 0xc0 ], r9
mulx r9, r8, rdx
xor rdx, rdx
adox r14, r13
adox r10, r15
mov rdx, [ rsi + 0x18 ]
mulx r13, r15, [ rsp + 0xc0 ]
mov rdx, r15
adcx rdx, [ rsp + 0xb8 ]
adcx r13, [ rsp + 0xb0 ]
mov r15, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xc8 ], r9
mov [ rsp + 0xd0 ], r8
mulx r8, r9, r12
mov rdx, 0x1 
shlx r12, [ rsi + 0x8 ], rdx
mov rdx, rbp
mov [ rsp + 0xd8 ], r10
mulx r10, rbp, [ rsi + 0x10 ]
test al, al
adox r15, rbp
adox r10, r13
mov rdx, [ rsi + 0x0 ]
mulx rbp, r13, r12
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xe0 ], rbp
mulx rbp, r12, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xe8 ], r13
mov [ rsp + 0xf0 ], r14
mulx r14, r13, rdx
mov rdx, rcx
mov [ rsp + 0xf8 ], r8
mulx r8, rcx, [ rsi + 0x30 ]
mov [ rsp + 0x100 ], r8
mov r8, rdx
mov rdx, [ rsp + 0x98 ]
mov [ rsp + 0x108 ], rcx
mov [ rsp + 0x110 ], r9
mulx r9, rcx, [ rsi + 0x20 ]
adcx r15, [ rsp + 0x60 ]
adcx r10, [ rsp + 0x58 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x118 ], r10
mov [ rsp + 0x120 ], r15
mulx r15, r10, r8
test al, al
adox r12, [ rsp + 0x30 ]
adox rbp, [ rsp + 0x28 ]
adcx r10, r13
adcx r14, r15
mov rdx, [ rsi + 0x10 ]
mulx r15, r13, rdx
add rcx, [ rsp + 0x110 ]
adcx r9, [ rsp + 0xf8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x128 ], r15
mov [ rsp + 0x130 ], r13
mulx r13, r15, rax
mov rdx, rbx
mov [ rsp + 0x138 ], r14
mulx r14, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x140 ], r10
lea r10, [ 4 * rdx]
xor rdx, rdx
adox r12, rbx
adox r14, rbp
adcx r12, r15
adcx r13, r14
mov rdx, [ rsi + 0x10 ]
mulx r15, rbp, r10
mov rdx, [ rsi + 0x28 ]
mulx r14, rbx, r10
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x148 ], r13
mov [ rsp + 0x150 ], r12
mulx r12, r13, r10
add rcx, rbp
adcx r15, r9
mov rdx, [ rsp + 0x10 ]
add rdx, [ rsp + 0x108 ]
mov r9, [ rsp - 0x18 ]
adcx r9, [ rsp + 0x100 ]
xor rbp, rbp
adox rcx, [ rsp + 0x50 ]
adox r15, [ rsp + 0x48 ]
xchg rdx, r8
mov [ rsp + 0x158 ], r15
mulx r15, rbp, [ rsi + 0x18 ]
adcx r8, [ rsp - 0x8 ]
adcx r9, [ rsp - 0x10 ]
mov rdx, r13
add rdx, [ rsp - 0x30 ]
adcx r12, [ rsp - 0x38 ]
xor r13, r13
adox rdx, rbp
adox r15, r12
xchg rdx, r10
mulx r12, rbp, [ rsi + 0x18 ]
mov r13, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x160 ], r15
mov [ rsp + 0x168 ], r10
mulx r10, r15, [ rsp + 0xc0 ]
mov rdx, r15
adcx rdx, [ rsp + 0x140 ]
adcx r10, [ rsp + 0x138 ]
mov r15, rbp
add r15, [ rsp + 0xf0 ]
adcx r12, [ rsp + 0xd8 ]
test al, al
adox rdx, [ rsp + 0x70 ]
adox r10, [ rsp + 0x68 ]
mov rbp, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x170 ], r10
mov [ rsp + 0x178 ], rcx
mulx rcx, r10, [ rsp + 0xc0 ]
adcx r15, [ rsp + 0x40 ]
adcx r12, [ rsp + 0x38 ]
mov rdx, r13
mov [ rsp + 0x180 ], rbp
mulx rbp, r13, [ rsi + 0x30 ]
test al, al
adox r8, r10
adox rcx, r9
mov rdx, [ rsi + 0x8 ]
mulx r10, r9, rdx
adcx r13, [ rsp + 0x8 ]
adcx rbp, [ rsp + 0x0 ]
test al, al
adox r13, [ rsp + 0x130 ]
adox rbp, [ rsp + 0x128 ]
adcx r8, [ rsp - 0x20 ]
adcx rcx, [ rsp - 0x28 ]
mov rdx, rbx
add rdx, [ rsp + 0x90 ]
adcx r14, [ rsp + 0x78 ]
xor rbx, rbx
adox rdx, [ rsp + 0x20 ]
adox r14, [ rsp + 0x18 ]
mov [ rsp + 0x188 ], rcx
mov rcx, [ rsp + 0xd0 ]
mov [ rsp + 0x190 ], r8
mov r8, rcx
adcx r8, [ rsp + 0x178 ]
mov [ rsp + 0x198 ], rbp
mov rbp, [ rsp + 0xc8 ]
adcx rbp, [ rsp + 0x158 ]
mov rcx, r9
add rcx, [ rsp + 0x168 ]
adcx r10, [ rsp + 0x160 ]
test al, al
adox rdx, [ rsp + 0x88 ]
adox r14, [ rsp + 0x80 ]
adcx r15, [ rsp + 0xe8 ]
adcx r12, [ rsp + 0xe0 ]
xchg rdx, r11
mulx rbx, r9, [ rsi + 0x8 ]
mov [ rsp + 0x1a0 ], r14
mov r14, r8
shrd r14, rbp, 58
shr rbp, 58
mov [ rsp + 0x1a8 ], r11
xor r11, r11
adox r13, r9
adox rbx, [ rsp + 0x198 ]
mov r9, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x1b0 ], rbx
mulx rbx, r11, [ rsp + 0xc0 ]
adcx r15, r14
adcx rbp, r12
mov rdx, [ rsi + 0x0 ]
mulx r14, r12, rdi
mov rdx, 0x3ffffffffffffff 
mov rdi, r15
and rdi, rdx
mov rdx, r9
mov [ rsp + 0x1b8 ], rdi
mulx rdi, r9, [ rsi + 0x0 ]
shrd r15, rbp, 58
shr rbp, 58
add rcx, r12
adcx r14, r10
test al, al
adox r13, r11
adox rbx, [ rsp + 0x1b0 ]
adcx rcx, r15
adcx rbp, r14
mov rdx, rcx
shrd rdx, rbp, 58
shr rbp, 58
mov r10, r9
xor r11, r11
adox r10, [ rsp + 0x1a8 ]
adox rdi, [ rsp + 0x1a0 ]
adcx r10, rdx
adcx rbp, rdi
mov r12, 0x3ffffffffffffff 
mov r9, r10
and r9, r12
shrd r10, rbp, 58
shr rbp, 58
add r13, r10
adcx rbp, rbx
mov r15, r13
shrd r15, rbp, 58
shr rbp, 58
mov r14, [ rsp + 0x180 ]
test al, al
adox r14, [ rsp + 0xa8 ]
mov rbx, [ rsp + 0x170 ]
adox rbx, [ rsp + 0xa0 ]
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x18 ], r9
mov rdi, r15
adcx rdi, [ rsp + 0x190 ]
adcx rbp, [ rsp + 0x188 ]
mov r9, rdi
shrd r9, rbp, 58
shr rbp, 58
and r13, r12
and rdi, r12
xchg rdx, rax
mulx r15, r10, [ rsi + 0x0 ]
adox r14, r9
adox rbp, rbx
mov rdx, r14
shrd rdx, rbp, 58
shr rbp, 58
mov rbx, r10
test al, al
adox rbx, [ rsp + 0x120 ]
adox r15, [ rsp + 0x118 ]
adcx rbx, rdx
adcx rbp, r15
mov r9, rbx
shrd r9, rbp, 58
shr rbp, 58
mov [ rax + 0x20 ], r13
and r14, r12
and rbx, r12
mov r13, [ rsp - 0x40 ]
mov r10, r13
adox r10, [ rsp + 0x150 ]
mov rdx, [ rsp - 0x48 ]
adox rdx, [ rsp + 0x148 ]
adcx r10, r9
adcx rbp, rdx
mov [ rax + 0x38 ], rbx
mov r13, r10
shrd r13, rbp, 57
shr rbp, 57
and r8, r12
adox r13, r8
adox rbp, r11
mov r15, r13
and r15, r12
mov r9, 0x1ffffffffffffff 
and r10, r9
shrd r13, rbp, 58
add r13, [ rsp + 0x1b8 ]
mov [ rax + 0x40 ], r10
mov rbx, r13
and rbx, r12
and rcx, r12
shr r13, 58
lea r13, [ r13 + rcx ]
mov [ rax + 0x10 ], r13
mov [ rax + 0x8 ], rbx
mov [ rax + 0x30 ], r14
mov [ rax + 0x28 ], rdi
mov [ rax + 0x0 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 576
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.0315
; seed 1296139269769906 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 35596 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=68, initial num_batches=31): 960 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.026969322395774806
; number reverted permutation / tried permutation: 303 / 496 =61.089%
; number reverted decision / tried decision: 240 / 503 =47.714%
; validated in 2.668s
