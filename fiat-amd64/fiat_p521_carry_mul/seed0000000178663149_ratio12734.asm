SECTION .text
	GLOBAL fiat_p521_carry_mul
fiat_p521_carry_mul:
sub rsp, 624
imul rax, [ rdx + 0x30 ], 0x2
imul r10, [ rdx + 0x18 ], 0x2
mov r11, 0x1 
shlx rcx, [ rdx + 0x20 ], r11
mov r8, rdx
mov rdx, [ rsi + 0x40 ]
mulx r11, r9, r10
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rcx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rax
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ r8 + 0x18 ]
mov rdx, [ r8 + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r15
mulx r15, rdi, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x40 ], r15
mov [ rsp - 0x38 ], rdi
mulx rdi, r15, [ r8 + 0x0 ]
mov rdx, [ r8 + 0x0 ]
mov [ rsp - 0x30 ], rdi
mov [ rsp - 0x28 ], r15
mulx r15, rdi, [ rsi + 0x0 ]
mov rdx, [ r8 + 0x28 ]
mov [ rsp - 0x20 ], r14
lea r14, [rdx + rdx]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x18 ], r15
mov [ rsp - 0x10 ], rdi
mulx rdi, r15, r14
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x8 ], rdi
mov [ rsp + 0x0 ], r15
mulx r15, rdi, r14
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x8 ], r15
mov [ rsp + 0x10 ], rdi
mulx rdi, r15, [ r8 + 0x20 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x18 ], rdi
mov [ rsp + 0x20 ], r15
mulx r15, rdi, r14
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x28 ], r15
mov [ rsp + 0x30 ], rdi
mulx rdi, r15, [ r8 + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x38 ], rdi
mov [ rsp + 0x40 ], r15
mulx r15, rdi, rax
xor rdx, rdx
adox r9, rbx
adox rbp, r11
mov rdx, [ r8 + 0x0 ]
mulx rbx, r11, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x48 ], rbx
mov [ rsp + 0x50 ], r11
mulx r11, rbx, r14
adcx r9, rbx
adcx r11, rbp
mov rdx, [ rsi + 0x10 ]
mulx rbx, rbp, [ r8 + 0x30 ]
imul rdx, [ r8 + 0x40 ], 0x2
mov [ rsp + 0x58 ], rbx
mov [ rsp + 0x60 ], rbp
mulx rbp, rbx, [ rsi + 0x18 ]
test al, al
adox r9, r12
adox r13, r11
mulx r11, r12, [ rsi + 0x10 ]
mov [ rsp + 0x68 ], r11
mov r11, rdx
mov rdx, [ r8 + 0x28 ]
mov [ rsp + 0x70 ], r12
mov [ rsp + 0x78 ], rbp
mulx rbp, r12, [ rsi + 0x18 ]
imul rdx, [ r8 + 0x10 ], 0x2
mov [ rsp + 0x80 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x88 ], r12
mov [ rsp + 0x90 ], rbx
mulx rbx, r12, [ r8 + 0x0 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x98 ], r13
mov [ rsp + 0xa0 ], r9
mulx r9, r13, [ r8 + 0x10 ]
mov rdx, [ r8 + 0x8 ]
mov [ rsp + 0xa8 ], r9
mov r9, rdx
shl r9, 0x1
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xb0 ], r13
mov [ rsp + 0xb8 ], rbx
mulx rbx, r13, rbp
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0xc0 ], r12
mov [ rsp + 0xc8 ], r15
mulx r15, r12, r9
add r12, r13
adcx rbx, r15
mov rdx, r10
mulx r9, r10, [ rsi + 0x30 ]
mov r13, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xd0 ], rdi
mulx rdi, r15, rcx
add r12, r10
adcx r9, rbx
add r12, r15
adcx rdi, r9
mov rdx, r14
mulx rbx, r14, [ rsi + 0x20 ]
mov rdx, rax
mulx r10, rax, [ rsi + 0x38 ]
xor r15, r15
adox r12, r14
adox rbx, rdi
mov r9, rdx
mov rdx, [ rsi + 0x40 ]
mulx r14, rdi, rbp
adcx r12, [ rsp + 0xd0 ]
adcx rbx, [ rsp + 0xc8 ]
mov rdx, rax
xor rbp, rbp
adox rdx, [ rsp + 0x30 ]
adox r10, [ rsp + 0x28 ]
xchg rdx, r13
mulx rax, r15, [ rsi + 0x38 ]
mov rdx, rcx
mulx rbp, rcx, [ rsi + 0x30 ]
adcx rdi, r15
adcx rax, r14
mov r14, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xd8 ], r10
mulx r10, r15, [ r8 + 0x10 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0xe0 ], r13
mov [ rsp + 0xe8 ], rbx
mulx rbx, r13, r11
add rdi, rcx
adcx rbp, rax
add r13, [ rsp + 0xc0 ]
adcx rbx, [ rsp + 0xb8 ]
add rdi, [ rsp + 0x0 ]
adcx rbp, [ rsp - 0x8 ]
mov rdx, [ r8 + 0x8 ]
mulx rax, rcx, [ rsi + 0x30 ]
test al, al
adox r13, rcx
adox rax, rbx
mov rdx, [ rsi + 0x20 ]
mulx rcx, rbx, [ r8 + 0x18 ]
adcx r13, r15
adcx r10, rax
mov rdx, [ rsi + 0x30 ]
mulx rax, r15, r9
mov rdx, r14
mov [ rsp + 0xf0 ], r12
mulx r12, r14, [ rsi + 0x40 ]
imul rdx, [ r8 + 0x38 ], 0x2
test al, al
adox r14, [ rsp + 0x10 ]
adox r12, [ rsp + 0x8 ]
mov [ rsp + 0xf8 ], rbp
mov [ rsp + 0x100 ], rdi
mulx rdi, rbp, [ rsi + 0x18 ]
adcx r13, rbx
adcx rcx, r10
test al, al
adox r14, r15
adox rax, r12
mulx r10, rbx, [ rsi + 0x38 ]
xchg rdx, r9
mulx r12, r15, [ rsi + 0x40 ]
mov [ rsp + 0x108 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x110 ], rbp
mov [ rsp + 0x118 ], rcx
mulx rcx, rbp, r11
adcx r15, rbx
adcx r10, r12
xor rdx, rdx
adox r15, rbp
adox rcx, r10
mov rdx, rdi
mulx rbx, rdi, [ rsi + 0x20 ]
mov rdx, rdi
adcx rdx, [ rsp + 0x100 ]
adcx rbx, [ rsp + 0xf8 ]
mov r12, rdx
mov rdx, [ r8 + 0x0 ]
mulx r10, rbp, [ rsi + 0x28 ]
mov rdx, r9
mulx rdi, r9, [ rsi + 0x28 ]
test al, al
adox r15, rbp
adox r10, rcx
adcx r14, r9
adcx rdi, rax
mov rax, rdx
mov rdx, [ rsi + 0x20 ]
mulx rbp, rcx, [ r8 + 0x8 ]
mov rdx, rax
mulx r9, rax, [ rsi + 0x20 ]
mov [ rsp + 0x120 ], rdi
mov rdi, rax
test al, al
adox rdi, [ rsp + 0xa0 ]
adox r9, [ rsp + 0x98 ]
adcx r15, rcx
adcx rbp, r10
mov r10, rdx
mov rdx, [ rsi + 0x18 ]
mulx rax, rcx, [ r8 + 0x10 ]
xor rdx, rdx
adox r15, rcx
adox rax, rbp
mov rdx, [ rsi + 0x18 ]
mulx rcx, rbp, [ r8 + 0x20 ]
adcx rdi, [ rsp + 0x90 ]
adcx r9, [ rsp + 0x78 ]
mov rdx, r10
mov [ rsp + 0x128 ], r14
mulx r14, r10, [ rsi + 0x10 ]
mov [ rsp + 0x130 ], rbx
mov rbx, r10
test al, al
adox rbx, [ rsp + 0xf0 ]
adox r14, [ rsp + 0xe8 ]
mov r10, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x138 ], r12
mov [ rsp + 0x140 ], r9
mulx r9, r12, r11
adcx rbx, r12
adcx r9, r14
mov rdx, [ rsi + 0x30 ]
mulx r12, r14, r10
add r13, rbp
adcx rcx, [ rsp + 0x118 ]
xor rdx, rdx
adox rbx, [ rsp - 0x10 ]
adox r9, [ rsp - 0x18 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x148 ], rcx
mulx rcx, rbp, [ r8 + 0x0 ]
mov rdx, r14
adcx rdx, [ rsp + 0xe0 ]
adcx r12, [ rsp + 0xd8 ]
test al, al
adox r15, [ rsp - 0x20 ]
adox rax, [ rsp - 0x48 ]
adcx rdi, [ rsp - 0x28 ]
mov r14, [ rsp - 0x30 ]
adcx r14, [ rsp + 0x140 ]
mov [ rsp + 0x150 ], rax
mov rax, rdx
mov rdx, [ r8 + 0x0 ]
mov [ rsp + 0x158 ], r15
mov [ rsp + 0x160 ], r13
mulx r13, r15, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x168 ], r12
mov [ rsp + 0x170 ], rax
mulx rax, r12, [ r8 + 0x8 ]
xor rdx, rdx
adox rdi, r12
adox rax, r14
mov rdx, [ rsi + 0x38 ]
mulx r12, r14, r11
mov rdx, 0x3ffffffffffffff 
mov [ rsp + 0x178 ], rax
mov rax, rbx
and rax, rdx
mov rdx, r10
mov [ rsp + 0x180 ], rax
mulx rax, r10, [ rsi + 0x40 ]
adox r10, r14
adox r12, rax
mov rdx, [ rsp + 0x110 ]
mov r14, rdx
adcx r14, [ rsp + 0x138 ]
mov rax, [ rsp + 0x108 ]
adcx rax, [ rsp + 0x130 ]
add r14, [ rsp + 0x70 ]
adcx rax, [ rsp + 0x68 ]
test al, al
adox r10, rbp
adox rcx, r12
mov rdx, [ r8 + 0x10 ]
mulx r12, rbp, [ rsi + 0x0 ]
adcx r14, r15
adcx r13, rax
mov rdx, [ r8 + 0x8 ]
mulx rax, r15, [ rsi + 0x0 ]
shrd rbx, r9, 58
shr r9, 58
add r14, r15
adcx rax, r13
add r14, rbx
adcx r9, rax
mov rdx, r11
mulx r13, r11, [ rsi + 0x28 ]
mov r15, r11
xor rbx, rbx
adox r15, [ rsp + 0x170 ]
adox r13, [ rsp + 0x168 ]
adcx r15, [ rsp + 0x50 ]
adcx r13, [ rsp + 0x48 ]
mov rax, r14
shrd rax, r9, 58
shr r9, 58
test al, al
adox rdi, rbp
adox r12, [ rsp + 0x178 ]
adcx rdi, rax
adcx r9, r12
mulx r11, rbp, [ rsi + 0x20 ]
mov rdx, 0x3a 
bzhi rax, rdi, rdx
mov rdx, [ rsi + 0x0 ]
mulx rbx, r12, [ r8 + 0x20 ]
mov rdx, [ r8 + 0x18 ]
mov [ rsp + 0x188 ], rax
mov [ rsp + 0x190 ], rbx
mulx rbx, rax, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x198 ], rbx
mov [ rsp + 0x1a0 ], rax
mulx rax, rbx, [ r8 + 0x10 ]
adox r15, [ rsp - 0x38 ]
adox r13, [ rsp - 0x40 ]
add r15, rbx
adcx rax, r13
shrd rdi, r9, 58
shr r9, 58
mov rdx, [ r8 + 0x8 ]
mulx r13, rbx, [ rsi + 0x28 ]
mov rdx, [ r8 + 0x18 ]
mov [ rsp + 0x1a8 ], r9
mov [ rsp + 0x1b0 ], rdi
mulx rdi, r9, [ rsi + 0x8 ]
add r15, r9
adcx rdi, rax
test al, al
adox r10, rbx
adox r13, rcx
mov rdx, 0x3a 
bzhi rcx, r14, rdx
mov rdx, [ rsi + 0x10 ]
mulx rax, r14, [ r8 + 0x8 ]
mov rdx, rbp
adox rdx, [ rsp + 0x128 ]
adox r11, [ rsp + 0x120 ]
mov rbp, rdx
mov rdx, [ rsi + 0x0 ]
mulx r9, rbx, [ r8 + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1b8 ], rcx
mov [ rsp + 0x1c0 ], r9
mulx r9, rcx, [ r8 + 0x0 ]
test al, al
adox rbp, rcx
adox r9, r11
mov rdx, [ rsi + 0x20 ]
mulx rcx, r11, [ r8 + 0x10 ]
adcx r15, r12
adcx rdi, [ rsp + 0x190 ]
xor rdx, rdx
adox r10, r11
adox rcx, r13
adcx r10, [ rsp + 0x1a0 ]
adcx rcx, [ rsp + 0x198 ]
add rbp, r14
adcx rax, r9
mov rdx, [ rsi + 0x0 ]
mulx r13, r12, [ r8 + 0x18 ]
mov rdx, [ r8 + 0x10 ]
mulx r9, r14, [ rsi + 0x8 ]
mov rdx, [ r8 + 0x8 ]
mov [ rsp + 0x1c8 ], rbx
mulx rbx, r11, [ rsi + 0x38 ]
xor rdx, rdx
adox rbp, r14
adox r9, rax
adcx rbp, r12
adcx r13, r9
mov rdx, [ rsi + 0x10 ]
mulx r12, rax, [ r8 + 0x28 ]
xor rdx, rdx
adox rbp, [ rsp + 0x1b0 ]
adox r13, [ rsp + 0x1a8 ]
mov r14, rax
adcx r14, [ rsp + 0x160 ]
adcx r12, [ rsp + 0x148 ]
mov r9, 0x3ffffffffffffff 
mov rax, rbp
and rax, r9
shrd rbp, r13, 58
shr r13, 58
xor r9, r9
adox r15, rbp
adox r13, rdi
mov rdx, [ rsi + 0x40 ]
mulx rbp, rdi, [ r8 + 0x0 ]
adcx rdi, r11
adcx rbx, rbp
test al, al
adox rdi, [ rsp + 0xb0 ]
adox rbx, [ rsp + 0xa8 ]
mov rdx, [ rsi + 0x28 ]
mulx rbp, r11, [ r8 + 0x18 ]
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x18 ], rax
mov rax, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x1d0 ], r12
mulx r12, r9, [ r8 + 0x20 ]
adcx rdi, r11
adcx rbp, rbx
mov rdx, r9
xor rbx, rbx
adox rdx, [ rsp + 0x158 ]
adox r12, [ rsp + 0x150 ]
mov r11, rdx
mov rdx, [ rsi + 0x10 ]
mulx rbx, r9, [ r8 + 0x20 ]
adcx r10, r9
adcx rbx, rcx
mov rdx, [ rsi + 0x0 ]
mulx r9, rcx, [ r8 + 0x38 ]
test al, al
adox r10, [ rsp + 0x40 ]
adox rbx, [ rsp + 0x38 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x1d8 ], r9
mulx r9, rax, [ r8 + 0x30 ]
adcx r10, rax
adcx r9, rbx
mov rdx, r15
shrd rdx, r13, 58
shr r13, 58
test al, al
adox r11, [ rsp + 0x1c8 ]
adox r12, [ rsp + 0x1c0 ]
adcx r11, rdx
adcx r13, r12
mov rbx, r11
shrd rbx, r13, 58
shr r13, 58
add r10, rbx
adcx r13, r9
mov rdx, [ rsi + 0x8 ]
mulx r9, rax, [ r8 + 0x30 ]
mov rdx, [ r8 + 0x40 ]
mulx rbx, r12, [ rsi + 0x0 ]
add r14, rax
adcx r9, [ rsp + 0x1d0 ]
mov rdx, [ r8 + 0x38 ]
mov [ rsp + 0x1e0 ], rbx
mulx rbx, rax, [ rsi + 0x8 ]
mov rdx, 0x3ffffffffffffff 
mov [ rsp + 0x1e8 ], r12
mov r12, r10
and r12, rdx
adox rdi, [ rsp + 0x20 ]
adox rbp, [ rsp + 0x18 ]
adcx rdi, [ rsp + 0x88 ]
adcx rbp, [ rsp + 0x80 ]
add rdi, [ rsp + 0x60 ]
adcx rbp, [ rsp + 0x58 ]
shrd r10, r13, 58
shr r13, 58
add rdi, rax
adcx rbx, rbp
add r14, rcx
adcx r9, [ rsp + 0x1d8 ]
add r14, r10
adcx r13, r9
mov rcx, r14
shrd rcx, r13, 58
shr r13, 58
test al, al
adox rdi, [ rsp + 0x1e8 ]
adox rbx, [ rsp + 0x1e0 ]
and r14, rdx
adox rdi, rcx
adox r13, rbx
mov rax, rdi
shrd rax, r13, 57
shr r13, 57
mov rbp, 0x39 
bzhi r10, rdi, rbp
adox rax, [ rsp + 0x180 ]
mov r9, 0x0 
adox r13, r9
mov rcx, rax
shrd rcx, r13, 58
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x40 ], r10
and rax, rdx
add rcx, [ rsp + 0x1b8 ]
mov rdi, rcx
and rdi, rdx
and r15, rdx
shr rcx, 58
add rcx, [ rsp + 0x188 ]
mov [ rbx + 0x10 ], rcx
and r11, rdx
mov [ rbx + 0x28 ], r11
mov [ rbx + 0x30 ], r12
mov [ rbx + 0x0 ], rax
mov [ rbx + 0x20 ], r15
mov [ rbx + 0x8 ], rdi
mov [ rbx + 0x38 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 624
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.2734
; seed 2578705781852188 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 9980651 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=44, initial num_batches=31): 213063 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.021347605481846825
; number reverted permutation / tried permutation: 67261 / 90127 =74.629%
; number reverted decision / tried decision: 56670 / 89872 =63.056%
; validated in 4.946s
