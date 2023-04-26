SECTION .text
	GLOBAL fiat_p521_carry_square
fiat_p521_carry_square:
sub rsp, 488
mov rax, [ rsi + 0x38 ]
mov r10, rax
shl r10, 0x2
mov rdx, r10
mulx r10, rax, [ rsi + 0x30 ]
mulx rcx, r11, [ rsi + 0x10 ]
mulx r9, r8, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mov rbx, [ rsi + 0x28 ]
mov [ rsp - 0x78 ], rbp
lea rbp, [ 4 * rbx]
xchg rdx, rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbx, [ rsi + 0x20 ]
mov rdx, rbp
mov [ rsp - 0x68 ], r13
mulx r13, rbp, [ rsi + 0x20 ]
mov [ rsp - 0x60 ], r14
mov r14, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x48 ], r9
lea r9, [rdx + rdx]
mov rdx, r9
mov [ rsp - 0x40 ], r8
mulx r8, r9, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], r8
mov r8, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], r9
mov [ rsp - 0x28 ], r13
mulx r13, r9, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x20 ], r13
mov [ rsp - 0x18 ], r9
mulx r9, r13, r8
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x10 ], rbp
mov rbp, rdx
shl rbp, 0x1
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x8 ], r9
mov [ rsp + 0x0 ], r13
mulx r13, r9, rbp
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x8 ], r13
lea r13, [rdx + rdx]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x10 ], r9
mov [ rsp + 0x18 ], rdi
mulx rdi, r9, r13
mov rdx, r13
mov [ rsp + 0x20 ], rdi
mulx rdi, r13, [ rsi + 0x8 ]
mov [ rsp + 0x28 ], r9
imul r9, [ rsi + 0x40 ], 0x4
mov [ rsp + 0x30 ], rdi
mov rdi, [ rsi + 0x30 ]
mov [ rsp + 0x38 ], r13
mov r13, rdi
shl r13, 0x2
mov rdi, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x40 ], r15
mov [ rsp + 0x48 ], rcx
mulx rcx, r15, r9
mov rdx, r8
mov [ rsp + 0x50 ], rcx
mulx rcx, r8, [ rsi + 0x0 ]
xchg rdx, rbp
mov [ rsp + 0x58 ], rcx
mov [ rsp + 0x60 ], r8
mulx r8, rcx, [ rsi + 0x18 ]
mov [ rsp + 0x68 ], r8
mov r8, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x70 ], rcx
mov [ rsp + 0x78 ], r15
mulx r15, rcx, r13
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x80 ], r11
mov r11, rdx
shl r11, 0x1
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x88 ], r10
mov [ rsp + 0x90 ], rax
mulx rax, r10, rbp
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x98 ], rax
mulx rax, rbp, r11
test al, al
adox rbx, rcx
adox r15, r12
mov rdx, [ rsi + 0x18 ]
mov r12, rdx
shl r12, 0x1
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xa0 ], rax
mulx rax, rcx, r9
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xa8 ], rbp
mov [ rsp + 0xb0 ], r10
mulx r10, rbp, rdx
mov rdx, rcx
mov [ rsp + 0xb8 ], r12
xor r12, r12
adox rdx, [ rsp + 0x90 ]
adox rax, [ rsp + 0x88 ]
adcx rbx, [ rsp + 0x80 ]
adcx r15, [ rsp + 0x48 ]
add rbx, [ rsp + 0x78 ]
adcx r15, [ rsp + 0x50 ]
xor rcx, rcx
adox rbx, rbp
adox r10, r15
adcx rdx, [ rsp + 0x40 ]
adcx rax, [ rsp + 0x18 ]
mov r12, rbx
shrd r12, r10, 58
shr r10, 58
xchg rdx, rdi
mulx r15, rbp, [ rsi + 0x38 ]
mov rdx, r11
mulx rcx, r11, [ rsi + 0x40 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xc0 ], r10
lea r10, [rdx + rdx]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xc8 ], r12
mov [ rsp + 0xd0 ], r14
mulx r14, r12, r9
mov rdx, r10
mov [ rsp + 0xd8 ], r15
mulx r15, r10, [ rsi + 0x10 ]
mov [ rsp + 0xe0 ], r15
mov r15, 0x3ffffffffffffff 
and rbx, r15
mov r15, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xe8 ], rbx
mov [ rsp + 0xf0 ], r10
mulx r10, rbx, [ rsp + 0xb8 ]
adox r11, [ rsp + 0x0 ]
adox rcx, [ rsp - 0x8 ]
adcx rdi, rbx
adcx r10, rax
mov rdx, r15
mulx rax, r15, [ rsi + 0x30 ]
mov [ rsp + 0xf8 ], r10
mulx r10, rbx, [ rsi + 0x0 ]
mov [ rsp + 0x100 ], r10
mov r10, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x108 ], rbx
mov [ rsp + 0x110 ], rdi
mulx rdi, rbx, [ rsp + 0xb8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x118 ], rax
mov [ rsp + 0x120 ], r15
mulx r15, rax, r8
test al, al
adox rbp, r12
adox r14, [ rsp + 0xd8 ]
adcx rbp, rbx
adcx rdi, r14
mov rdx, [ rsi + 0x28 ]
mulx rbx, r12, r13
xor rdx, rdx
adox r12, [ rsp - 0x10 ]
adox rbx, [ rsp - 0x28 ]
mov rdx, r10
mulx r14, r10, [ rsi + 0x8 ]
adcx rbp, [ rsp - 0x30 ]
adcx rdi, [ rsp - 0x38 ]
imul rdx, [ rsi + 0x8 ], 0x2
add r11, rax
adcx r15, rcx
add r11, r10
adcx r14, r15
mov rcx, 0x1 
shlx rax, [ rsi + 0x10 ], rcx
mov r10, rdx
mov rdx, [ rsi + 0x20 ]
mulx rcx, r15, r13
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x128 ], r14
mulx r14, r13, rax
mov rdx, r15
test al, al
adox rdx, [ rsp + 0x10 ]
adox rcx, [ rsp + 0x8 ]
mov r15, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x130 ], r11
mov [ rsp + 0x138 ], rdi
mulx rdi, r11, r9
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x140 ], rbp
mov [ rsp + 0x148 ], r14
mulx r14, rbp, r9
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x150 ], r13
mov [ rsp + 0x158 ], r14
mulx r14, r13, r9
adcx r15, [ rsp - 0x40 ]
adcx rcx, [ rsp - 0x48 ]
xor rdx, rdx
adox r15, r11
adox rdi, rcx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, r10
mov rdx, [ rsp + 0xd0 ]
mov [ rsp + 0x160 ], rbp
mulx rbp, r10, [ rsi + 0x28 ]
adcx r15, r11
adcx rcx, rdi
mov rdx, r10
add rdx, [ rsp + 0x120 ]
adcx rbp, [ rsp + 0x118 ]
xor rdi, rdi
adox r15, [ rsp + 0xc8 ]
adox rcx, [ rsp + 0xc0 ]
mov r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx rdi, r10, rdx
adcx r12, r13
adcx r14, rbx
test al, al
adox r12, r10
adox rdi, r14
mov rdx, [ rsp + 0xb8 ]
mulx r13, rbx, [ rsi + 0x0 ]
mov rdx, rax
mulx r10, rax, [ rsi + 0x0 ]
adcx r11, [ rsp + 0x160 ]
adcx rbp, [ rsp + 0x158 ]
add r12, rax
adcx r10, rdi
mov rdx, r15
shrd rdx, rcx, 58
shr rcx, 58
xor r14, r14
adox r12, rdx
adox rcx, r10
mov rdi, r12
shrd rdi, rcx, 58
shr rcx, 58
xor rax, rax
adox r11, [ rsp + 0x150 ]
adox rbp, [ rsp + 0x148 ]
adcx r11, rbx
adcx r13, rbp
xor r14, r14
adox r11, rdi
adox rcx, r13
mov rax, r11
shrd rax, rcx, 58
shr rcx, 58
mov rdx, [ rsi + 0x38 ]
mulx r10, rbx, r9
xor rdx, rdx
adox rbx, [ rsp - 0x18 ]
adox r10, [ rsp - 0x20 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r14, r8
mov rdx, [ rsp + 0x110 ]
adcx rdx, [ rsp + 0x60 ]
mov rdi, [ rsp + 0xf8 ]
adcx rdi, [ rsp + 0x58 ]
test al, al
adox rdx, rax
adox rcx, rdi
mov rbp, 0x3ffffffffffffff 
mov r13, rdx
and r13, rbp
shrd rdx, rcx, 58
shr rcx, 58
mov rax, r14
add rax, [ rsp + 0x140 ]
adcx r9, [ rsp + 0x138 ]
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x20 ], r13
mov rdi, rdx
mov rdx, [ rsi + 0x20 ]
mulx rbp, r13, rdx
test al, al
adox r13, [ rsp + 0x70 ]
adox rbp, [ rsp + 0x68 ]
adcx r13, [ rsp + 0xf0 ]
adcx rbp, [ rsp + 0xe0 ]
xor rdx, rdx
adox r13, [ rsp + 0x38 ]
adox rbp, [ rsp + 0x30 ]
adcx rax, rdi
adcx rcx, r9
test al, al
adox rbx, [ rsp + 0xb0 ]
adox r10, [ rsp + 0x98 ]
mov rdx, [ rsi + 0x8 ]
mulx r9, rdi, r8
mov rdx, 0x3a 
bzhi r8, rax, rdx
adox rbx, rdi
adox r9, r10
test al, al
adox rbx, [ rsp + 0x108 ]
adox r9, [ rsp + 0x100 ]
shrd rax, rcx, 58
shr rcx, 58
test al, al
adox rbx, rax
adox rcx, r9
mov r10, [ rsp + 0x28 ]
mov rdi, r10
adcx rdi, [ rsp + 0x130 ]
mov r9, [ rsp + 0x20 ]
adcx r9, [ rsp + 0x128 ]
mov r10, rbx
shrd r10, rcx, 58
shr rcx, 58
xor rax, rax
adox r13, [ rsp + 0xa8 ]
adox rbp, [ rsp + 0xa0 ]
adcx rdi, r10
adcx rcx, r9
mov r9, rdi
shrd r9, rcx, 58
shr rcx, 58
add r13, r9
adcx rcx, rbp
bzhi r10, r15, rdx
bzhi r15, rdi, rdx
mov rbp, 0x39 
bzhi rdi, r13, rbp
mov [ r14 + 0x38 ], r15
shrd r13, rcx, 57
shr rcx, 57
test al, al
adox r13, [ rsp + 0xe8 ]
adox rcx, rax
mov r9, r13
shrd r9, rcx, 58
bzhi r15, r12, rdx
lea r9, [ r9 + r10 ]
mov r12, r9
shr r12, 58
lea r12, [ r12 + r15 ]
bzhi r10, r11, rdx
mov [ r14 + 0x10 ], r12
bzhi r11, rbx, rdx
mov [ r14 + 0x30 ], r11
bzhi rbx, r13, rdx
mov [ r14 + 0x0 ], rbx
mov [ r14 + 0x28 ], r8
bzhi r8, r9, rdx
mov [ r14 + 0x40 ], rdi
mov [ r14 + 0x18 ], r10
mov [ r14 + 0x8 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 488
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.5442
; seed 1322193827504674 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3247041 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=89, initial num_batches=31): 98737 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.030408300973101356
; number reverted permutation / tried permutation: 62000 / 89952 =68.926%
; number reverted decision / tried decision: 57454 / 90047 =63.804%
; validated in 2.261s
