SECTION .text
	GLOBAL fiat_p521_carry_square
fiat_p521_carry_square:
sub rsp, 600
mov rax, [ rsi + 0x28 ]
lea r10, [rax + rax]
mov rdx, [ rsi + 0x20 ]
mulx r11, rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, rdx
mov rdx, [ rsi + 0x20 ]
mov r9, rdx
shl r9, 0x1
mov rdx, 0x2 
mov [ rsp - 0x80 ], rbx
shlx rbx, [ rsi + 0x38 ], rdx
mov [ rsp - 0x78 ], rbp
mov rbp, [ rsi + 0x18 ]
mov [ rsp - 0x70 ], r12
lea r12, [rbp + rbp]
imul rbp, [ rsi + 0x40 ], 0x4
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, r10
mov rdx, rbx
mov [ rsp - 0x58 ], r15
mulx r15, rbx, [ rsi + 0x28 ]
mov [ rsp - 0x50 ], rdi
mov rdi, [ rsi + 0x30 ]
mov [ rsp - 0x48 ], r8
mov r8, rdi
shl r8, 0x1
xchg rdx, rbp
mov [ rsp - 0x40 ], rcx
mulx rcx, rdi, [ rsi + 0x30 ]
mov [ rsp - 0x38 ], r12
mov [ rsp - 0x30 ], r14
mulx r14, r12, [ rsi + 0x28 ]
xchg rdx, r8
mov [ rsp - 0x28 ], r13
mov [ rsp - 0x20 ], r14
mulx r14, r13, [ rsi + 0x0 ]
mov [ rsp - 0x18 ], r14
mov r14, [ rsi + 0x40 ]
mov [ rsp - 0x10 ], r13
lea r13, [r14 + r14]
mov r14, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x8 ], r12
mov [ rsp + 0x0 ], r9
mulx r9, r12, rbp
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x8 ], r9
mov [ rsp + 0x10 ], r12
mulx r12, r9, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x18 ], r12
mov r12, rdx
shl r12, 0x2
mov rdx, r13
mov [ rsp + 0x20 ], r9
mulx r9, r13, [ rsi + 0x0 ]
mov [ rsp + 0x28 ], r9
imul r9, [ rsi + 0x8 ], 0x2
mov [ rsp + 0x30 ], r13
mov r13, [ rsi + 0x10 ]
mov [ rsp + 0x38 ], r12
mov r12, r13
shl r12, 0x1
xchg rdx, r14
mov [ rsp + 0x40 ], rcx
mulx rcx, r13, [ rsi + 0x10 ]
mov [ rsp + 0x48 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x50 ], rcx
mov [ rsp + 0x58 ], r13
mulx r13, rcx, r12
mov rdx, rbp
mov [ rsp + 0x60 ], r13
mulx r13, rbp, [ rsi + 0x10 ]
xchg rdx, r12
mov [ rsp + 0x68 ], rcx
mov [ rsp + 0x70 ], r13
mulx r13, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x78 ], r13
lea r13, [rdx + rdx]
mov rdx, rdi
mov [ rsp + 0x80 ], rcx
mulx rcx, rdi, [ rsi + 0x30 ]
mov [ rsp + 0x88 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x90 ], r11
mov [ rsp + 0x98 ], rax
mulx rax, r11, r9
mov rdx, r13
mulx r9, r13, [ rsi + 0x38 ]
mov [ rsp + 0xa0 ], r9
mov r9, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xa8 ], r13
mov [ rsp + 0xb0 ], rax
mulx rax, r13, r10
xor rdx, rdx
adox rdi, rbx
adox r15, rcx
mov rbx, 0x2 
shlx rcx, [ rsi + 0x30 ], rbx
mov rdx, rcx
mulx rbx, rcx, [ rsi + 0x20 ]
adcx r13, rcx
adcx rbx, rax
mov rax, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xb8 ], r15
mulx r15, rcx, r8
mov rdx, r12
mov [ rsp + 0xc0 ], rdi
mulx rdi, r12, [ rsi + 0x18 ]
mov [ rsp + 0xc8 ], r11
mov r11, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xd0 ], r15
mov [ rsp + 0xd8 ], rcx
mulx rcx, r15, r10
xor rdx, rdx
adox r13, r12
adox rdi, rbx
mov rdx, rax
mulx rbx, rax, [ rsi + 0x18 ]
mov r12, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xe0 ], rbx
mov [ rsp + 0xe8 ], rax
mulx rax, rbx, rdx
mov rdx, rbx
adcx rdx, [ rsp + 0xd8 ]
adcx rax, [ rsp + 0xd0 ]
mov rbx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xf0 ], rax
mov [ rsp + 0xf8 ], rcx
mulx rcx, rax, r10
mov rdx, r10
mov [ rsp + 0x100 ], rcx
mulx rcx, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x108 ], rcx
mov [ rsp + 0x110 ], r10
mulx r10, rcx, r8
mov rdx, r8
mov [ rsp + 0x118 ], rax
mulx rax, r8, [ rsi + 0x10 ]
test al, al
adox r13, r8
adox rax, rdi
xchg rdx, r9
mulx r8, rdi, [ rsi + 0x8 ]
adcx r13, [ rsp + 0xc8 ]
adcx rax, [ rsp + 0xb0 ]
mov [ rsp + 0x120 ], rax
mov rax, r15
add rax, [ rsp + 0x98 ]
mov [ rsp + 0x128 ], r13
mov r13, [ rsp + 0xf8 ]
adcx r13, [ rsp + 0x90 ]
xchg rdx, r9
mov [ rsp + 0x130 ], r10
mulx r10, r15, [ rsi + 0x20 ]
mov [ rsp + 0x138 ], rcx
xor rcx, rcx
adox rax, [ rsp + 0x58 ]
adox r13, [ rsp + 0x50 ]
adcx rax, rdi
adcx r8, r13
mov rdi, [ rsp + 0xa8 ]
xor r13, r13
adox rdi, [ rsp + 0x48 ]
mov rcx, [ rsp + 0xa0 ]
adox rcx, [ rsp + 0x40 ]
xchg rdx, r11
mov [ rsp + 0x140 ], r8
mulx r8, r13, [ rsi + 0x20 ]
mov rdx, [ rsp + 0x0 ]
mov [ rsp + 0x148 ], rax
mov [ rsp + 0x150 ], r8
mulx r8, rax, [ rsi + 0x10 ]
adcx rbx, rax
adcx r8, [ rsp + 0xf0 ]
xchg rdx, r11
mov [ rsp + 0x158 ], r13
mulx r13, rax, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x160 ], r13
mov [ rsp + 0x168 ], rax
mulx rax, r13, r14
mov rdx, r11
mulx r14, r11, [ rsi + 0x18 ]
add r13, r11
adcx r14, rax
mov rax, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x170 ], r14
mulx r14, r11, [ rsp + 0x38 ]
test al, al
adox r11, [ rsp + 0xe8 ]
adox r14, [ rsp + 0xe0 ]
adcx r11, [ rsp + 0x88 ]
adcx r14, [ rsp + 0x70 ]
mov rdx, r15
test al, al
adox rdx, [ rsp + 0xc0 ]
adox r10, [ rsp + 0xb8 ]
adcx r11, [ rsp + 0x138 ]
adcx r14, [ rsp + 0x130 ]
mov r15, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x178 ], r13
mov [ rsp + 0x180 ], rcx
mulx rcx, r13, rdx
test al, al
adox r11, r13
adox rcx, r14
adcx r15, [ rsp + 0x68 ]
adcx r10, [ rsp + 0x60 ]
mov rdx, [ rsi + 0x0 ]
mulx r13, r14, r9
mov rdx, [ rsp + 0x10 ]
xor r9, r9
adox rdx, [ rsp - 0x8 ]
mov [ rsp + 0x188 ], r13
mov r13, [ rsp + 0x8 ]
adox r13, [ rsp - 0x20 ]
adcx rbx, [ rsp - 0x28 ]
adcx r8, [ rsp - 0x30 ]
mov r9, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x190 ], r14
mov [ rsp + 0x198 ], r8
mulx r8, r14, rbp
mov rdx, [ rsp - 0x38 ]
mov [ rsp + 0x1a0 ], rbx
mulx rbx, rbp, [ rsi + 0x0 ]
mov [ rsp + 0x1a8 ], r8
xor r8, r8
adox r9, [ rsp + 0x20 ]
adox r13, [ rsp + 0x18 ]
adcx r15, rbp
adcx rbx, r10
mulx rbp, r10, [ rsi + 0x8 ]
mov r8, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x1b0 ], rbx
mov [ rsp + 0x1b8 ], r15
mulx r15, rbx, r12
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x1c0 ], r14
mulx r14, r12, r8
xor rdx, rdx
adox r9, r10
adox rbp, r13
adcx rdi, r12
adcx r14, [ rsp + 0x180 ]
mov r8, r11
shrd r8, rcx, 58
shr rcx, 58
xor r13, r13
adox rbx, [ rsp + 0x158 ]
adox r15, [ rsp + 0x150 ]
mov rdx, r8
adcx rdx, [ rsp + 0x128 ]
adcx rcx, [ rsp + 0x120 ]
test al, al
adox rbx, [ rsp + 0x168 ]
adox r15, [ rsp + 0x160 ]
mov r10, 0x3ffffffffffffff 
mov r12, rdx
and r12, r10
mov r8, [ rsp + 0x178 ]
adox r8, [ rsp + 0x118 ]
mov r10, [ rsp + 0x170 ]
adox r10, [ rsp + 0x100 ]
shrd rdx, rcx, 58
shr rcx, 58
mov [ rsp + 0x1c8 ], r12
xor r12, r12
adox r8, [ rsp + 0x1c0 ]
adox r10, [ rsp + 0x1a8 ]
adcx rbx, [ rsp - 0x40 ]
adcx r15, [ rsp - 0x48 ]
xchg rdx, rax
mulx r12, r13, [ rsi + 0x8 ]
mov [ rsp + 0x1d0 ], r10
xor r10, r10
adox rdi, r13
adox r12, r14
adcx rbx, [ rsp + 0x80 ]
adcx r15, [ rsp + 0x78 ]
add rbx, rax
adcx rcx, r15
mov r14, rbx
shrd r14, rcx, 58
shr rcx, 58
mov rax, r14
xor r13, r13
adox rax, [ rsp + 0x1b8 ]
adox rcx, [ rsp + 0x1b0 ]
mulx r15, r10, [ rsi + 0x0 ]
adcx rdi, [ rsp + 0x110 ]
adcx r12, [ rsp + 0x108 ]
mov rdx, 0x3ffffffffffffff 
and rbx, rdx
mov r14, rax
and r14, rdx
adox r9, r10
adox r15, rbp
shrd rax, rcx, 58
shr rcx, 58
xor rbp, rbp
adox r9, rax
adox rcx, r15
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x18 ], r14
mov r10, [ rsp + 0x1a0 ]
adcx r10, [ rsp - 0x10 ]
mov r14, [ rsp + 0x198 ]
adcx r14, [ rsp - 0x18 ]
mov r15, r9
and r15, rdx
shrd r9, rcx, 58
shr rcx, 58
mov [ r13 + 0x20 ], r15
add rdi, r9
adcx rcx, r12
mov r12, rdi
shrd r12, rcx, 58
shr rcx, 58
xor rax, rax
adox r10, r12
adox rcx, r14
mov rbp, r10
shrd rbp, rcx, 58
shr rcx, 58
xor r14, r14
adox r8, [ rsp + 0x190 ]
mov rax, [ rsp + 0x1d0 ]
adox rax, [ rsp + 0x188 ]
and rdi, rdx
adox r8, rbp
adox rcx, rax
mov r15, r8
and r15, rdx
and r10, rdx
mov [ r13 + 0x28 ], rdi
mov r9, [ rsp + 0x148 ]
adox r9, [ rsp + 0x30 ]
mov r12, [ rsp + 0x140 ]
adox r12, [ rsp + 0x28 ]
mov [ r13 + 0x30 ], r10
mov [ r13 + 0x38 ], r15
and r11, rdx
shrd r8, rcx, 58
shr rcx, 58
add r9, r8
adcx rcx, r12
mov rbp, 0x1ffffffffffffff 
mov rax, r9
and rax, rbp
shrd r9, rcx, 57
shr rcx, 57
xor rdi, rdi
adox r9, r11
adox rcx, rdi
mov r14, r9
shrd r14, rcx, 58
add r14, [ rsp + 0x1c8 ]
mov r15, r14
and r15, rdx
shr r14, 58
lea r14, [ r14 + rbx ]
mov [ r13 + 0x8 ], r15
and r9, rdx
mov [ r13 + 0x0 ], r9
mov [ r13 + 0x40 ], rax
mov [ r13 + 0x10 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 600
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.1796
; seed 3031528406711996 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 21076 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=110, initial num_batches=31): 650 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.03084076674890871
; number reverted permutation / tried permutation: 349 / 501 =69.661%
; number reverted decision / tried decision: 293 / 498 =58.835%
; validated in 2.173s
