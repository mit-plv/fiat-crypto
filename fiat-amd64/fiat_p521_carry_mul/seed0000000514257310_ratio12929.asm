SECTION .text
	GLOBAL fiat_p521_carry_mul
fiat_p521_carry_mul:
sub rsp, 664
mov rax, 0x1 
shlx r10, [ rdx + 0x30 ], rax
mov r11, rdx
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ r11 + 0x0 ]
mov rdx, [ r11 + 0x40 ]
lea r9, [rdx + rdx]
mov rdx, [ r11 + 0x38 ]
mov rax, rdx
shl rax, 0x1
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ r11 + 0x0 ]
mov rdx, [ r11 + 0x8 ]
mov [ rsp - 0x70 ], r12
lea r12, [rdx + rdx]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, r9
mov rdx, rax
mov [ rsp - 0x58 ], r15
mulx r15, rax, [ rsi + 0x10 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbp
mulx rbp, rdi, [ rsi + 0x38 ]
mov [ rsp - 0x40 ], rbx
mov rbx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x38 ], r14
mov [ rsp - 0x30 ], r13
mulx r13, r14, [ r11 + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x28 ], r13
mov [ rsp - 0x20 ], r14
mulx r14, r13, [ r11 + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x18 ], r14
mov [ rsp - 0x10 ], r13
mulx r13, r14, [ r11 + 0x10 ]
mov rdx, r9
mov [ rsp - 0x8 ], r13
mulx r13, r9, [ rsi + 0x38 ]
mov [ rsp + 0x0 ], r14
mov r14, rdx
mov rdx, [ r11 + 0x0 ]
mov [ rsp + 0x8 ], r8
mov [ rsp + 0x10 ], rcx
mulx rcx, r8, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x18 ], rcx
mov [ rsp + 0x20 ], r8
mulx r8, rcx, r14
mov rdx, [ r11 + 0x0 ]
mov [ rsp + 0x28 ], r8
mov [ rsp + 0x30 ], rcx
mulx rcx, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x38 ], rcx
mov [ rsp + 0x40 ], r8
mulx r8, rcx, [ r11 + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x48 ], r8
mov [ rsp + 0x50 ], rcx
mulx rcx, r8, [ r11 + 0x18 ]
mov rdx, [ r11 + 0x38 ]
mov [ rsp + 0x58 ], rcx
mov [ rsp + 0x60 ], r8
mulx r8, rcx, [ rsi + 0x8 ]
mov rdx, [ r11 + 0x0 ]
mov [ rsp + 0x68 ], r8
mov [ rsp + 0x70 ], rcx
mulx rcx, r8, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x78 ], r15
mov [ rsp + 0x80 ], rax
mulx rax, r15, [ r11 + 0x8 ]
mov rdx, [ r11 + 0x18 ]
mov [ rsp + 0x88 ], rax
mov rax, rdx
shl rax, 0x1
mov rdx, [ r11 + 0x10 ]
mov [ rsp + 0x90 ], r15
lea r15, [rdx + rdx]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x98 ], r13
mov [ rsp + 0xa0 ], r9
mulx r9, r13, rax
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0xa8 ], rcx
mov [ rsp + 0xb0 ], r8
mulx r8, rcx, r15
test al, al
adox rcx, r13
adox r9, r8
mov rdx, [ rsi + 0x30 ]
mulx r8, r13, [ r11 + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xb8 ], r8
mov [ rsp + 0xc0 ], r13
mulx r13, r8, rbx
imul rdx, [ r11 + 0x20 ], 0x2
mov [ rsp + 0xc8 ], r9
mov [ rsp + 0xd0 ], rcx
mulx rcx, r9, [ rsi + 0x28 ]
xchg rdx, r10
mov [ rsp + 0xd8 ], r13
mov [ rsp + 0xe0 ], r8
mulx r8, r13, [ rsi + 0x38 ]
xchg rdx, r12
mov [ rsp + 0xe8 ], r8
mov [ rsp + 0xf0 ], r13
mulx r13, r8, [ rsi + 0x40 ]
mov rdx, r15
mov [ rsp + 0xf8 ], rbp
mulx rbp, r15, [ rsi + 0x38 ]
xor rdx, rdx
adox r8, r15
adox rbp, r13
mov rdx, [ rsi + 0x30 ]
mulx r15, r13, rax
adcx r8, r13
adcx r15, rbp
mov rdx, [ rsi + 0x30 ]
mulx r13, rbp, r14
test al, al
adox r8, r9
adox rcx, r15
mov rdx, [ rsi + 0x40 ]
mulx r15, r9, r12
adcx r9, rdi
adcx r15, [ rsp + 0xf8 ]
add r9, rbp
adcx r13, r15
xor rdx, rdx
adox r9, [ rsp + 0xb0 ]
adox r13, [ rsp + 0xa8 ]
mov rdx, rbx
mulx rdi, rbx, [ rsi + 0x40 ]
mov rbp, 0x1 
shlx r15, [ r11 + 0x28 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x100 ], r13
mov [ rsp + 0x108 ], r9
mulx r9, r13, r15
mov rdx, r15
mov [ rsp + 0x110 ], r9
mulx r9, r15, [ rsi + 0x30 ]
xchg rdx, rax
mov [ rsp + 0x118 ], r9
mov [ rsp + 0x120 ], r15
mulx r15, r9, [ rsi + 0x40 ]
mov rdx, rax
mov [ rsp + 0x128 ], r15
mulx r15, rax, [ rsi + 0x28 ]
adcx rbx, [ rsp + 0xa0 ]
adcx rdi, [ rsp + 0x98 ]
mov [ rsp + 0x130 ], rdi
mov [ rsp + 0x138 ], rbx
mulx rbx, rdi, [ rsi + 0x20 ]
mov [ rsp + 0x140 ], r15
mov [ rsp + 0x148 ], rax
mulx rax, r15, [ rsi + 0x38 ]
add r8, rdi
adcx rbx, rcx
test al, al
adox r13, [ rsp + 0xf0 ]
mov rcx, [ rsp + 0xe8 ]
adox rcx, [ rsp + 0x110 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x150 ], rcx
mulx rcx, rdi, r10
adcx rdi, r15
adcx rax, rcx
mov rdx, [ rsi + 0x30 ]
mulx rcx, r15, r12
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x158 ], r13
mov [ rsp + 0x160 ], rbx
mulx rbx, r13, r10
add r9, r13
adcx rbx, [ rsp + 0x128 ]
add rdi, r15
adcx rcx, rax
mov rdx, [ rsi + 0x18 ]
mulx r15, rax, r12
xor rdx, rdx
adox r8, rax
adox r15, [ rsp + 0x160 ]
adcx r9, [ rsp + 0x120 ]
adcx rbx, [ rsp + 0x118 ]
add r8, [ rsp + 0x80 ]
adcx r15, [ rsp + 0x78 ]
mov rdx, [ rsi + 0x28 ]
mulx rax, r13, r12
xor rdx, rdx
adox rdi, [ rsp + 0xe0 ]
adox rcx, [ rsp + 0xd8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x168 ], rcx
mov [ rsp + 0x170 ], rdi
mulx rdi, rcx, r14
mov rdx, r10
mov [ rsp + 0x178 ], r15
mulx r15, r10, [ rsi + 0x30 ]
adcx r9, r13
adcx rax, rbx
add r8, rcx
adcx rdi, [ rsp + 0x178 ]
mov rdx, r10
add rdx, [ rsp + 0xd0 ]
adcx r15, [ rsp + 0xc8 ]
xor rbx, rbx
adox rdx, [ rsp + 0x148 ]
adox r15, [ rsp + 0x140 ]
adcx r8, [ rsp + 0x10 ]
adcx rdi, [ rsp + 0x8 ]
mov r13, [ rsp - 0x30 ]
mov rcx, r13
xor r10, r10
adox rcx, [ rsp + 0x170 ]
mov rbx, [ rsp - 0x38 ]
adox rbx, [ rsp + 0x168 ]
adcx rcx, [ rsp - 0x40 ]
adcx rbx, [ rsp - 0x48 ]
mov r13, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x180 ], rbx
mulx rbx, r10, r12
xor rdx, rdx
adox r13, r10
adox rbx, r15
mov rdx, [ rsi + 0x20 ]
mulx r15, r12, [ r11 + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x188 ], rcx
mulx rcx, r10, rbp
mov rdx, r14
mov [ rsp + 0x190 ], rax
mulx rax, r14, [ rsi + 0x10 ]
mov [ rsp + 0x198 ], r9
mov r9, 0x3a 
mov [ rsp + 0x1a0 ], r15
bzhi r15, r8, r9
adox r13, r10
adox rcx, rbx
mulx r10, rbx, [ rsi + 0x28 ]
xor r9, r9
adox r13, r14
adox rax, rcx
xchg rdx, rbp
mulx rcx, r14, [ rsi + 0x30 ]
mov [ rsp + 0x1a8 ], r15
mov r15, r14
adcx r15, [ rsp + 0x158 ]
adcx rcx, [ rsp + 0x150 ]
test al, al
adox r15, rbx
adox r10, rcx
adcx r15, [ rsp + 0x20 ]
adcx r10, [ rsp + 0x18 ]
mov rbx, rdx
mov rdx, [ rsi + 0x10 ]
mulx rcx, r14, [ r11 + 0x18 ]
mov rdx, r12
mov [ rsp + 0x1b0 ], r10
xor r10, r10
adox rdx, [ rsp + 0x108 ]
mov r9, [ rsp + 0x100 ]
adox r9, [ rsp + 0x1a0 ]
mov r12, rdx
mov rdx, [ r11 + 0x10 ]
mov [ rsp + 0x1b8 ], r15
mulx r15, r10, [ rsi + 0x18 ]
adcx r12, r10
adcx r15, r9
xor rdx, rdx
adox r12, r14
adox rcx, r15
mov rdx, [ r11 + 0x0 ]
mulx r9, r14, [ rsi + 0x8 ]
adcx r13, r14
adcx r9, rax
mov rdx, [ r11 + 0x20 ]
mulx r10, rax, [ rsi + 0x8 ]
mov rdx, rbx
mulx r15, rbx, [ rsi + 0x20 ]
add r12, rax
adcx r10, rcx
mov rdx, [ r11 + 0x8 ]
mulx r14, rcx, [ rsi + 0x0 ]
mov rdx, rbx
xor rax, rax
adox rdx, [ rsp + 0x198 ]
adox r15, [ rsp + 0x190 ]
xchg rdx, rbp
mulx rax, rbx, [ rsi + 0x18 ]
adcx rbp, rbx
adcx rax, r15
mov rdx, [ rsi + 0x10 ]
mulx rbx, r15, [ r11 + 0x8 ]
mov rdx, r15
mov [ rsp + 0x1c0 ], r10
xor r10, r10
adox rdx, [ rsp + 0x188 ]
adox rbx, [ rsp + 0x180 ]
adcx rbp, [ rsp + 0x40 ]
adcx rax, [ rsp + 0x38 ]
add rbp, [ rsp + 0x90 ]
adcx rax, [ rsp + 0x88 ]
xor r15, r15
adox rbp, [ rsp - 0x10 ]
adox rax, [ rsp - 0x18 ]
mov r10, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x1c8 ], r12
mulx r12, r15, [ r11 + 0x10 ]
adcx r13, rcx
adcx r14, r9
shrd r8, rdi, 58
shr rdi, 58
xor rdx, rdx
adox r10, r15
adox r12, rbx
adcx r13, r8
adcx rdi, r14
mov rdx, [ r11 + 0x8 ]
mulx rcx, r9, [ rsi + 0x18 ]
mov rdx, r9
add rdx, [ rsp + 0x1b8 ]
adcx rcx, [ rsp + 0x1b0 ]
mov rbx, r13
shrd rbx, rdi, 58
shr rdi, 58
mov r15, 0x3ffffffffffffff 
and r13, r15
adox rbp, rbx
adox rdi, rax
mov rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx r8, r14, [ r11 + 0x10 ]
adcx rax, r14
adcx r8, rcx
mov rdx, rbp
and rdx, r15
mov r9, rdx
mov rdx, [ r11 + 0x18 ]
mulx rbx, rcx, [ rsi + 0x0 ]
adox r10, rcx
adox rbx, r12
mov rdx, [ r11 + 0x20 ]
mulx r14, r12, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx r15, rcx, [ r11 + 0x18 ]
adcx rax, rcx
adcx r15, r8
add rax, r12
adcx r14, r15
mov rdx, [ rsi + 0x38 ]
mulx r12, r8, [ r11 + 0x8 ]
shrd rbp, rdi, 58
shr rdi, 58
test al, al
adox r10, rbp
adox rdi, rbx
mov rdx, [ r11 + 0x0 ]
mulx rcx, rbx, [ rsi + 0x40 ]
adcx rbx, r8
adcx r12, rcx
mov rdx, [ r11 + 0x0 ]
mulx r8, r15, [ rsi + 0x38 ]
mov rdx, r10
shrd rdx, rdi, 58
shr rdi, 58
mov rbp, rdx
mov rdx, [ r11 + 0x10 ]
mov [ rsp + 0x1d0 ], r9
mulx r9, rcx, [ rsi + 0x30 ]
mov rdx, [ r11 + 0x18 ]
mov [ rsp + 0x1d8 ], r13
mov [ rsp + 0x1e0 ], r8
mulx r8, r13, [ rsi + 0x18 ]
test al, al
adox rbx, rcx
adox r9, r12
adcx rax, rbp
adcx rdi, r14
mov rdx, 0x3ffffffffffffff 
mov r14, rax
and r14, rdx
mov rdx, [ r11 + 0x10 ]
mulx rbp, r12, [ rsi + 0x28 ]
mov rdx, 0x3a 
bzhi rcx, r10, rdx
shrd rax, rdi, 58
shr rdi, 58
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x18 ], rcx
mov rcx, r15
xor rdx, rdx
adox rcx, [ rsp + 0x30 ]
mov r10, [ rsp + 0x1e0 ]
adox r10, [ rsp + 0x28 ]
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x20 ], r14
adcx rcx, [ rsp + 0xc0 ]
adcx r10, [ rsp + 0xb8 ]
mov rdx, [ r11 + 0x8 ]
mulx r15, r14, [ rsi + 0x28 ]
mov rdx, [ r11 + 0x0 ]
mov [ rsp + 0x1e8 ], rdi
mov [ rsp + 0x1f0 ], rax
mulx rax, rdi, [ rsi + 0x30 ]
mov rdx, [ r11 + 0x28 ]
mov [ rsp + 0x1f8 ], r9
mov [ rsp + 0x200 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
mov rdx, rdi
add rdx, [ rsp + 0x138 ]
adcx rax, [ rsp + 0x130 ]
xor rdi, rdi
adox rdx, r14
adox r15, rax
adcx rdx, [ rsp + 0x0 ]
adcx r15, [ rsp - 0x8 ]
add rdx, r13
adcx r8, r15
mov r13, rdx
mov rdx, [ r11 + 0x20 ]
mulx rax, r14, [ rsi + 0x10 ]
add r13, r14
adcx rax, r8
mov rdx, [ r11 + 0x28 ]
mulx r8, r15, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mulx rdi, r14, [ r11 + 0x28 ]
mov rdx, [ r11 + 0x20 ]
mov [ rsp + 0x208 ], rbx
mov [ rsp + 0x210 ], r9
mulx r9, rbx, [ rsi + 0x18 ]
xor rdx, rdx
adox r13, r14
adox rdi, rax
mov rdx, [ r11 + 0x28 ]
mulx r14, rax, [ rsi + 0x0 ]
adcx rcx, r12
adcx rbp, r10
mov rdx, rax
xor r12, r12
adox rdx, [ rsp + 0x1c8 ]
adox r14, [ rsp + 0x1c0 ]
adcx rcx, [ rsp - 0x20 ]
adcx rbp, [ rsp - 0x28 ]
xor r10, r10
adox rcx, rbx
adox r9, rbp
mov r12, [ rsp + 0x200 ]
adcx r12, [ rsp + 0x60 ]
mov rbx, [ rsp + 0x1f8 ]
adcx rbx, [ rsp + 0x58 ]
mov rax, rdx
mov rdx, [ r11 + 0x30 ]
mulx r10, rbp, [ rsi + 0x0 ]
xor rdx, rdx
adox r13, rbp
adox r10, rdi
adcx r12, [ rsp + 0x50 ]
adcx rbx, [ rsp + 0x48 ]
mov rdx, [ rsi + 0x0 ]
mulx rbp, rdi, [ r11 + 0x38 ]
add r12, r15
adcx r8, rbx
add rax, [ rsp + 0x1f0 ]
adcx r14, [ rsp + 0x1e8 ]
test al, al
adox rcx, [ rsp + 0x210 ]
adox r9, [ rsp + 0x208 ]
mov rdx, [ r11 + 0x30 ]
mulx rbx, r15, [ rsi + 0x8 ]
adcx rcx, r15
adcx rbx, r9
test al, al
adox rcx, rdi
adox rbp, rbx
mov rdx, rax
shrd rdx, r14, 58
shr r14, 58
add r13, rdx
adcx r14, r10
mov r10, r13
shrd r10, r14, 58
shr r14, 58
add rcx, r10
adcx r14, rbp
mov rdx, [ r11 + 0x40 ]
mulx r9, rdi, [ rsi + 0x0 ]
mov rdx, 0x3ffffffffffffff 
and r13, rdx
mov rdx, [ r11 + 0x30 ]
mulx rbx, r15, [ rsi + 0x10 ]
adox r12, r15
adox rbx, r8
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x30 ], r13
adcx r12, [ rsp + 0x70 ]
adcx rbx, [ rsp + 0x68 ]
add r12, rdi
adcx r9, rbx
mov r8, rcx
shrd r8, r14, 58
shr r14, 58
mov rbp, 0x3ffffffffffffff 
and rax, rbp
mov [ rdx + 0x28 ], rax
adox r12, r8
adox r14, r9
mov r10, r12
shrd r10, r14, 57
shr r14, 57
mov rdi, 0x39 
bzhi r13, r12, rdi
adox r10, [ rsp + 0x1a8 ]
mov r15, 0x0 
adox r14, r15
mov rbx, r10
shrd rbx, r14, 58
add rbx, [ rsp + 0x1d8 ]
mov r9, rbx
shr r9, 58
add r9, [ rsp + 0x1d0 ]
mov [ rdx + 0x10 ], r9
and rcx, rbp
mov [ rdx + 0x38 ], rcx
mov [ rdx + 0x40 ], r13
and r10, rbp
mov [ rdx + 0x0 ], r10
and rbx, rbp
mov [ rdx + 0x8 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 664
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.2929
; seed 0552810167605294 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 9818078 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=97, initial num_batches=31): 219283 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.02233461579751149
; number reverted permutation / tried permutation: 64260 / 89737 =71.609%
; number reverted decision / tried decision: 54288 / 90262 =60.145%
; validated in 6.962s
