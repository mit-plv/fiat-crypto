SECTION .text
	GLOBAL fiat_p521_carry_square
fiat_p521_carry_square:
sub rsp, 544
mov rax, [ rsi + 0x38 ]
lea r10, [rax + rax]
mov rax, [ rsi + 0x38 ]
mov r11, rax
shl r11, 0x2
mov rdx, [ rsi + 0x38 ]
mulx rcx, rax, r10
mov rdx, 0x2 
shlx r8, [ rsi + 0x30 ], rdx
mov rdx, r10
mulx r9, r10, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov rbx, 0x1 
mov [ rsp - 0x78 ], rbp
shlx rbp, [ rsi + 0x40 ], rbx
mov rbx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, r11
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x50 ], rdi
mov rdi, rdx
shl rdi, 0x1
mov rdx, 0x1 
mov [ rsp - 0x48 ], r9
shlx r9, [ rsi + 0x28 ], rdx
mov rdx, rbx
mov [ rsp - 0x40 ], r10
mulx r10, rbx, [ rsi + 0x8 ]
mov rdx, r11
mov [ rsp - 0x38 ], r15
mulx r15, r11, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], r14
mov r14, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], r10
mov [ rsp - 0x20 ], rbx
mulx rbx, r10, r9
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x18 ], rbx
mov [ rsp - 0x10 ], r10
mulx r10, rbx, r9
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x8 ], r10
mov [ rsp + 0x0 ], rbx
mulx rbx, r10, rdx
mov rdx, rbp
mov [ rsp + 0x8 ], r13
mulx r13, rbp, [ rsi + 0x40 ]
mov [ rsp + 0x10 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x18 ], rbp
mov [ rsp + 0x20 ], r12
mulx r12, rbp, r9
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x28 ], rbx
mov [ rsp + 0x30 ], r10
mulx r10, rbx, r8
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x38 ], rcx
mov rcx, rdx
shl rcx, 0x1
mov rdx, rdi
mov [ rsp + 0x40 ], rax
mulx rax, rdi, [ rsi + 0x0 ]
mov [ rsp + 0x48 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x50 ], r11
mov [ rsp + 0x58 ], r10
mulx r10, r11, rcx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x60 ], r10
mulx r10, rcx, rdx
imul rdx, [ rsi + 0x40 ], 0x4
xchg rdx, r14
mov [ rsp + 0x68 ], r11
mov [ rsp + 0x70 ], r10
mulx r10, r11, [ rsi + 0x20 ]
mov [ rsp + 0x78 ], rcx
mov rcx, [ rsi + 0x18 ]
mov [ rsp + 0x80 ], rbx
mov rbx, rcx
shl rbx, 0x1
xchg rdx, r9
mov [ rsp + 0x88 ], rax
mulx rax, rcx, [ rsi + 0x8 ]
mov [ rsp + 0x90 ], rax
mov rax, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x98 ], rcx
mov [ rsp + 0xa0 ], rdi
mulx rdi, rcx, r8
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xa8 ], r12
mov [ rsp + 0xb0 ], rbp
mulx rbp, r12, r14
mov rdx, rbx
mov [ rsp + 0xb8 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
mov [ rsp + 0xc0 ], r12
mov r12, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xc8 ], rbp
mov [ rsp + 0xd0 ], rbx
mulx rbx, rbp, r14
mov rdx, r14
mov [ rsp + 0xd8 ], rbx
mulx rbx, r14, [ rsi + 0x10 ]
mov [ rsp + 0xe0 ], rbp
mov [ rsp + 0xe8 ], rbx
mulx rbx, rbp, [ rsi + 0x18 ]
test al, al
adox rcx, r11
adox r10, rdi
adcx rcx, rbp
adcx rbx, r10
mov r11, [ rsi + 0x28 ]
lea rdi, [ 4 * r11]
mov r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx r10, rbp, rdx
mov rdx, 0x1 
mov [ rsp + 0xf0 ], r14
shlx r14, [ rsi + 0x30 ], rdx
test al, al
adox rcx, rbp
adox r10, rbx
mov rdx, r15
mulx rbx, r15, [ rsi + 0x8 ]
mov rdx, r8
mulx rbp, r8, [ rsi + 0x20 ]
mov rdx, r8
adcx rdx, [ rsp + 0xb0 ]
adcx rbp, [ rsp + 0xa8 ]
mov r8, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xf8 ], rbx
mov [ rsp + 0x100 ], r15
mulx r15, rbx, r14
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x108 ], rbp
mov [ rsp + 0x110 ], r8
mulx r8, rbp, r14
add rcx, [ rsp + 0xa0 ]
adcx r10, [ rsp + 0x88 ]
mov rdx, r11
mov [ rsp + 0x118 ], r8
mulx r8, r11, [ rsi + 0x38 ]
mov [ rsp + 0x120 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x128 ], r10
mov [ rsp + 0x130 ], rcx
mulx rcx, r10, rdi
add r10, [ rsp + 0x80 ]
adcx rcx, [ rsp + 0x58 ]
test al, al
adox r10, [ rsp + 0x50 ]
adox rcx, [ rsp + 0x48 ]
mov rdx, rbp
mulx rdi, rbp, [ rsi + 0x30 ]
mov [ rsp + 0x138 ], r15
mov r15, rbp
adcx r15, [ rsp + 0x40 ]
adcx rdi, [ rsp + 0x38 ]
mov [ rsp + 0x140 ], rbx
mulx rbx, rbp, [ rsi + 0x8 ]
test al, al
adox r10, rbp
adox rbx, rcx
adcx r11, [ rsp + 0x30 ]
adcx r8, [ rsp + 0x28 ]
test al, al
adox r15, [ rsp + 0xd0 ]
adox rdi, [ rsp + 0xc8 ]
mov rdx, rax
mulx rcx, rax, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x148 ], rdi
mulx rdi, rbp, rdx
adcx rbp, rax
adcx rcx, rdi
mov rdx, [ rsi + 0x18 ]
mulx rdi, rax, r9
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x150 ], r15
mov [ rsp + 0x158 ], r8
mulx r8, r15, r9
test al, al
adox r15, [ rsp + 0xc0 ]
adox r8, [ rsp + 0xb8 ]
adcx rbp, [ rsp + 0x140 ]
adcx rcx, [ rsp + 0x138 ]
test al, al
adox r10, [ rsp + 0x20 ]
adox rbx, [ rsp + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x160 ], r11
mulx r11, r9, r12
adcx r15, [ rsp + 0x78 ]
adcx r8, [ rsp + 0x70 ]
test al, al
adox r15, r9
adox r11, r8
mov rdx, rax
adcx rdx, [ rsp + 0x110 ]
adcx rdi, [ rsp + 0x108 ]
test al, al
adox rdx, [ rsp + 0xf0 ]
adox rdi, [ rsp + 0xe8 ]
adcx rbp, [ rsp - 0x20 ]
adcx rcx, [ rsp - 0x28 ]
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r8, r9, r13
mov rdx, r14
mulx r13, r14, [ rsi + 0x30 ]
test al, al
adox r14, [ rsp - 0x30 ]
adox r13, [ rsp - 0x38 ]
adcx rax, [ rsp + 0x68 ]
adcx rdi, [ rsp + 0x60 ]
mov [ rsp + 0x168 ], rcx
mov rcx, [ rsi + 0x20 ]
mov [ rsp + 0x170 ], rbp
mov rbp, rcx
shl rbp, 0x1
xor rcx, rcx
adox r14, [ rsp + 0xe0 ]
adox r13, [ rsp + 0xd8 ]
xchg rdx, rbp
mov [ rsp + 0x178 ], r8
mulx r8, rcx, [ rsi + 0x10 ]
xchg rdx, r12
mov [ rsp + 0x180 ], r9
mov [ rsp + 0x188 ], r11
mulx r11, r9, [ rsi + 0x0 ]
mov rdx, 0x3ffffffffffffff 
mov [ rsp + 0x190 ], r15
mov r15, r10
and r15, rdx
shrd r10, rbx, 58
shr rbx, 58
xor rdx, rdx
adox rax, r10
adox rbx, rdi
mov rdi, rax
shrd rdi, rbx, 58
shr rbx, 58
mov rdx, r12
mulx r10, r12, [ rsi + 0x18 ]
add r14, [ rsp + 0x100 ]
adcx r13, [ rsp + 0xf8 ]
mov [ rsp + 0x198 ], r15
mov r15, r12
test al, al
adox r15, [ rsp + 0x18 ]
adox r10, [ rsp + 0x10 ]
adcx r15, [ rsp - 0x10 ]
adcx r10, [ rsp - 0x18 ]
add r14, r9
adcx r11, r13
mov r9, rdx
mov rdx, [ rsi + 0x8 ]
mulx r13, r12, rbp
add r15, r12
adcx r13, r10
mov rdx, rcx
add rdx, [ rsp + 0x160 ]
adcx r8, [ rsp + 0x158 ]
xor rbp, rbp
adox rdx, [ rsp + 0x98 ]
adox r8, [ rsp + 0x90 ]
mov rcx, rdi
adcx rcx, [ rsp + 0x130 ]
adcx rbx, [ rsp + 0x128 ]
mov rdi, 0x3ffffffffffffff 
mov r10, rcx
and r10, rdi
shrd rcx, rbx, 58
shr rbx, 58
xchg rdx, r9
mulx rbp, r12, [ rsi + 0x0 ]
test al, al
adox r14, rcx
adox rbx, r11
mov r11, r14
shrd r11, rbx, 58
shr rbx, 58
mov rcx, r12
test al, al
adox rcx, [ rsp + 0x190 ]
adox rbp, [ rsp + 0x188 ]
and r14, rdi
adox rcx, r11
adox rbx, rbp
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x18 ], r14
mulx rbp, r11, [ rsi + 0x8 ]
mov rdx, r11
adcx rdx, [ rsp + 0x150 ]
adcx rbp, [ rsp + 0x148 ]
add rdx, [ rsp + 0x0 ]
adcx rbp, [ rsp - 0x8 ]
mov r14, rcx
shrd r14, rbx, 58
shr rbx, 58
test al, al
adox rdx, r14
adox rbx, rbp
adcx r9, [ rsp + 0x120 ]
adcx r8, [ rsp + 0x118 ]
mov r11, rdx
shrd r11, rbx, 58
shr rbx, 58
xor rbp, rbp
adox r9, r11
adox rbx, r8
mov r14, r9
shrd r14, rbx, 58
shr rbx, 58
and rdx, rdi
mov [ r12 + 0x28 ], rdx
adox r15, [ rsp - 0x40 ]
adox r13, [ rsp - 0x48 ]
adcx r15, r14
adcx rbx, r13
mov r8, r15
shrd r8, rbx, 58
shr rbx, 58
mov r11, [ rsp + 0x170 ]
test al, al
adox r11, [ rsp + 0x180 ]
mov r14, [ rsp + 0x168 ]
adox r14, [ rsp + 0x178 ]
and r9, rdi
adox r11, r8
adox rbx, r14
and r15, rdi
mov rdx, 0x39 
bzhi r13, r11, rdx
shrd r11, rbx, 57
shr rbx, 57
xor r8, r8
adox r11, [ rsp + 0x198 ]
adox rbx, r8
mov rbp, r11
and rbp, rdi
and rax, rdi
mov [ r12 + 0x0 ], rbp
shrd r11, rbx, 58
lea r11, [ r11 + rax ]
mov r14, r11
shr r14, 58
and r11, rdi
lea r14, [ r14 + r10 ]
and rcx, rdi
mov [ r12 + 0x20 ], rcx
mov [ r12 + 0x30 ], r9
mov [ r12 + 0x38 ], r15
mov [ r12 + 0x10 ], r14
mov [ r12 + 0x8 ], r11
mov [ r12 + 0x40 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 544
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.2100
; seed 1134653670191079 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 20556 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=97, initial num_batches=31): 607 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.02952909126289161
; number reverted permutation / tried permutation: 341 / 507 =67.258%
; number reverted decision / tried decision: 253 / 492 =51.423%
; validated in 2.06s
