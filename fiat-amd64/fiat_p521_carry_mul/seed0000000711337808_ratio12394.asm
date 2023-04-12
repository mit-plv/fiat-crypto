SECTION .text
	GLOBAL fiat_p521_carry_mul
fiat_p521_carry_mul:
sub rsp, 696
mov rax, [ rdx + 0x18 ]
mov r10, rax
shl r10, 0x1
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rax + 0x0 ]
mov rdx, 0x1 
shlx r8, [ rax + 0x28 ], rdx
mov rdx, r8
mulx r9, r8, [ rsi + 0x20 ]
mov [ rsp - 0x80 ], rbx
mov rbx, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x20 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x48 ], r12
mov [ rsp - 0x40 ], rbp
mulx rbp, r12, rbx
mov rdx, rbx
mov [ rsp - 0x38 ], rdi
mulx rdi, rbx, [ rsi + 0x30 ]
mov [ rsp - 0x30 ], r15
imul r15, [ rax + 0x20 ], 0x2
mov [ rsp - 0x28 ], rbp
mov rbp, [ rax + 0x10 ]
mov [ rsp - 0x20 ], r12
lea r12, [rbp + rbp]
mov rbp, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp - 0x18 ], r14
mov [ rsp - 0x10 ], r13
mulx r13, r14, r15
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x8 ], r13
mov r13, rdx
shl r13, 0x1
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x0 ], r14
mov [ rsp + 0x8 ], rcx
mulx rcx, r14, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x10 ], rcx
mov [ rsp + 0x18 ], r14
mulx r14, rcx, r13
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x20 ], r11
mov [ rsp + 0x28 ], r14
mulx r14, r11, r12
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x30 ], rcx
mov [ rsp + 0x38 ], r9
mulx r9, rcx, [ rax + 0x28 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x40 ], r9
mov [ rsp + 0x48 ], rcx
mulx rcx, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x50 ], rcx
mov [ rsp + 0x58 ], r9
mulx r9, rcx, r13
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x60 ], r9
mov [ rsp + 0x68 ], rcx
mulx rcx, r9, [ rax + 0x38 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x70 ], rcx
mov [ rsp + 0x78 ], r9
mulx r9, rcx, [ rax + 0x8 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x80 ], r9
mov r9, rdx
shl r9, 0x1
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x88 ], rcx
mov [ rsp + 0x90 ], r8
mulx r8, rcx, r9
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x98 ], r14
mov [ rsp + 0xa0 ], r11
mulx r11, r14, r9
mov rdx, r13
mov [ rsp + 0xa8 ], r11
mulx r11, r13, [ rsi + 0x38 ]
mov [ rsp + 0xb0 ], r11
mov [ rsp + 0xb8 ], r13
mulx r13, r11, [ rsi + 0x40 ]
mov [ rsp + 0xc0 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xc8 ], r11
mov [ rsp + 0xd0 ], r14
mulx r14, r11, r15
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xd8 ], r8
mov [ rsp + 0xe0 ], rcx
mulx rcx, r8, r9
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0xe8 ], rcx
mov [ rsp + 0xf0 ], r8
mulx r8, rcx, r10
xor rdx, rdx
adox rcx, r11
adox r14, r8
adcx rcx, rbx
adcx rdi, r14
mov rdx, r12
mulx rbx, r12, [ rsi + 0x40 ]
mov rdx, r10
mulx r11, r10, [ rsi + 0x38 ]
mov r8, [ rax + 0x8 ]
lea r14, [r8 + r8]
mov r8, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xf8 ], r14
mov [ rsp + 0x100 ], rdi
mulx rdi, r14, r15
add r12, r10
adcx r11, rbx
add r12, r14
adcx rdi, r11
mov rdx, [ rsi + 0x28 ]
mulx r10, rbx, r15
add rcx, [ rsp + 0xe0 ]
mov rdx, [ rsp + 0x100 ]
adcx rdx, [ rsp + 0xd8 ]
mov r15, rdx
mov rdx, [ rsp + 0xf8 ]
mulx r11, r14, [ rsi + 0x40 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x108 ], r15
mov [ rsp + 0x110 ], rcx
mulx rcx, r15, r8
add r14, [ rsp + 0xa0 ]
adcx r11, [ rsp + 0x98 ]
test al, al
adox r14, r15
adox rcx, r11
adcx r14, rbx
adcx r10, rcx
xor rdx, rdx
adox r14, [ rsp + 0x90 ]
adox r10, [ rsp + 0x38 ]
imul r8, [ rax + 0x40 ], 0x2
mov rdx, r8
mulx rbx, r8, [ rsi + 0x8 ]
test al, al
adox r14, [ rsp + 0xd0 ]
adox r10, [ rsp + 0xa8 ]
adcx r14, [ rsp + 0x30 ]
adcx r10, [ rsp + 0x28 ]
xor r15, r15
adox r14, r8
adox rbx, r10
mulx rcx, r11, [ rsi + 0x18 ]
adcx r14, [ rsp + 0x20 ]
adcx rbx, [ rsp + 0x8 ]
mov r8, rdx
mov rdx, [ rsi + 0x28 ]
mulx r15, r10, rbp
xor rdx, rdx
adox r12, r10
adox r15, rdi
mov rdx, [ rsi + 0x10 ]
mulx r10, rdi, r8
mov rdx, r9
mov [ rsp + 0x118 ], rcx
mulx rcx, r9, [ rsi + 0x20 ]
adcx r12, r9
adcx rcx, r15
mov r15, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x120 ], r11
mulx r11, r9, r13
test al, al
adox r12, r9
adox r11, rcx
adcx r12, rdi
adcx r10, r11
mov rdx, [ rsi + 0x8 ]
mulx rcx, rdi, [ rax + 0x0 ]
add r12, rdi
adcx rcx, r10
test al, al
adox r12, [ rsp - 0x10 ]
adox rcx, [ rsp - 0x18 ]
mov rdx, r8
mulx r9, r8, [ rsi + 0x20 ]
mov r11, rdx
mov rdx, [ rsi + 0x10 ]
mulx rdi, r10, [ rax + 0x8 ]
mov rdx, r13
mov [ rsp + 0x128 ], rdi
mulx rdi, r13, [ rsi + 0x20 ]
mov [ rsp + 0x130 ], r10
mov r10, r14
shrd r10, rbx, 58
shr rbx, 58
test al, al
adox r12, r10
adox rbx, rcx
mov rcx, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x138 ], r9
mulx r9, r10, r15
mov rdx, r13
adcx rdx, [ rsp + 0x110 ]
adcx rdi, [ rsp + 0x108 ]
mov r13, r12
shrd r13, rbx, 58
shr rbx, 58
mov [ rsp + 0x140 ], rbx
mov rbx, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x148 ], r13
mov [ rsp + 0x150 ], rdi
mulx rdi, r13, rbp
xor rdx, rdx
adox r13, r10
adox r9, rdi
mov rdx, [ rsi + 0x30 ]
mulx r10, rbp, rcx
mov rdx, 0x3ffffffffffffff 
and r12, rdx
mov rcx, [ rsp + 0x0 ]
adox rcx, [ rsp - 0x20 ]
mov rdi, [ rsp - 0x8 ]
adox rdi, [ rsp - 0x28 ]
adcx rcx, [ rsp + 0xf0 ]
adcx rdi, [ rsp + 0xe8 ]
test al, al
adox rcx, [ rsp + 0x68 ]
adox rdi, [ rsp + 0x60 ]
adcx rcx, r8
adcx rdi, [ rsp + 0x138 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x158 ], r12
mulx r12, r8, [ rax + 0x0 ]
add rcx, r8
adcx r12, rdi
test al, al
adox rbx, [ rsp + 0x120 ]
mov rdx, [ rsp + 0x118 ]
adox rdx, [ rsp + 0x150 ]
adcx rcx, [ rsp + 0x130 ]
adcx r12, [ rsp + 0x128 ]
add rbx, [ rsp + 0x58 ]
adcx rdx, [ rsp + 0x50 ]
mov rdi, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x160 ], r12
mulx r12, r8, [ rsi + 0x8 ]
xor rdx, rdx
adox rbx, r8
adox r12, rdi
mov rdx, [ rsi + 0x40 ]
mulx r8, rdi, r15
adcx rdi, [ rsp + 0xb8 ]
adcx r8, [ rsp + 0xb0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x168 ], rcx
mulx rcx, r15, [ rax + 0x10 ]
xor rdx, rdx
adox r13, rbp
adox r10, r9
mov rdx, [ rsi + 0x8 ]
mulx rbp, r9, [ rax + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x170 ], r8
mov [ rsp + 0x178 ], rdi
mulx rdi, r8, [ rax + 0x0 ]
adcx rbx, r15
adcx rcx, r12
mov rdx, [ rsi + 0x28 ]
mulx r15, r12, r11
test al, al
adox rbx, [ rsp + 0x148 ]
adox rcx, [ rsp + 0x140 ]
mov rdx, rbx
shrd rdx, rcx, 58
shr rcx, 58
mov [ rsp + 0x180 ], rcx
xor rcx, rcx
adox r13, r12
adox r15, r10
adcx r13, r8
adcx rdi, r15
test al, al
adox r13, [ rsp - 0x30 ]
adox rdi, [ rsp - 0x38 ]
mov r10, rdx
mov rdx, [ rax + 0x10 ]
mulx r12, r8, [ rsi + 0x10 ]
adcx r13, r8
adcx r12, rdi
mov rdx, [ rax + 0x8 ]
mulx rdi, r15, [ rsi + 0x20 ]
xor rdx, rdx
adox r13, r9
adox rbp, r12
mov rdx, [ rsi + 0x18 ]
mulx r9, rcx, [ rax + 0x10 ]
mov rdx, r11
mulx r8, r11, [ rsi + 0x30 ]
mov r12, 0x3a 
mov [ rsp + 0x188 ], r10
bzhi r10, rbx, r12
mov rbx, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x190 ], r10
mulx r10, r12, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x198 ], r10
mov [ rsp + 0x1a0 ], r12
mulx r12, r10, [ rax + 0x20 ]
mov rdx, r11
adox rdx, [ rsp + 0x178 ]
adox r8, [ rsp + 0x170 ]
add r13, r10
adcx r12, rbp
xor rbp, rbp
adox rdx, [ rsp + 0x18 ]
adox r8, [ rsp + 0x10 ]
adcx rdx, r15
adcx rdi, r8
mov r15, rdx
mov rdx, [ rsi + 0x38 ]
mulx r10, r11, [ rax + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx rbp, r8, [ rax + 0x18 ]
add r15, rcx
adcx r9, rdi
mov rdx, [ rax + 0x10 ]
mulx rdi, rcx, [ rsi + 0x8 ]
mov rdx, rcx
add rdx, [ rsp + 0x168 ]
adcx rdi, [ rsp + 0x160 ]
mov rcx, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x1a8 ], r10
mov [ rsp + 0x1b0 ], r11
mulx r11, r10, rbx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x1b8 ], r9
mov [ rsp + 0x1c0 ], r15
mulx r15, r9, [ rax + 0x18 ]
add rcx, r8
adcx rbp, rdi
add rcx, [ rsp + 0x188 ]
adcx rbp, [ rsp + 0x180 ]
mov rdx, rcx
shrd rdx, rbp, 58
shr rbp, 58
add r10, [ rsp + 0x1a0 ]
adcx r11, [ rsp + 0x198 ]
add r13, rdx
adcx rbp, r12
mov r12, 0x3a 
bzhi r8, r13, r12
shrd r13, rbp, 58
shr rbp, 58
mov rdx, [ rsi + 0x30 ]
mulx r12, rdi, [ rax + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x1c8 ], rbp
mov [ rsp + 0x1d0 ], r13
mulx r13, rbp, [ rax + 0x18 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x1d8 ], r15
mov [ rsp + 0x1e0 ], r9
mulx r9, r15, rbx
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x20 ], r8
mov rbx, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x1e8 ], r13
mulx r13, r8, [ rsi + 0x28 ]
xor rdx, rdx
adox r10, rdi
adox r12, r11
mov rdx, [ rsi + 0x30 ]
mulx rdi, r11, [ rax + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x1f0 ], rdi
mulx rdi, rbx, [ rsi + 0x30 ]
adcx r10, r8
adcx r13, r12
mov rdx, [ rax + 0x18 ]
mulx r12, r8, [ rsi + 0x28 ]
mov rdx, 0x3a 
mov [ rsp + 0x1f8 ], r12
bzhi r12, rcx, rdx
mov rcx, r15
adox rcx, [ rsp + 0xc8 ]
adox r9, [ rsp + 0xc0 ]
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x18 ], r12
add r10, rbp
adcx r13, [ rsp + 0x1e8 ]
mov rbp, [ rsp + 0x1e0 ]
mov r12, rbp
test al, al
adox r12, [ rsp + 0x1c0 ]
mov rdx, [ rsp + 0x1d8 ]
adox rdx, [ rsp + 0x1b8 ]
mov rbp, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x200 ], r13
mulx r13, r15, [ rax + 0x20 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x208 ], r10
mov [ rsp + 0x210 ], r8
mulx r8, r10, [ rsi + 0x40 ]
adcx r12, r15
adcx r13, rbp
add rcx, rbx
adcx rdi, r9
xor rdx, rdx
adox r10, [ rsp + 0x1b0 ]
adox r8, [ rsp + 0x1a8 ]
mov rdx, [ rsi + 0x20 ]
mulx r9, rbx, [ rax + 0x10 ]
adcx r10, r11
adcx r8, [ rsp + 0x1f0 ]
mov rdx, [ rsi + 0x18 ]
mulx rbp, r11, [ rax + 0x28 ]
add r10, [ rsp + 0x210 ]
adcx r8, [ rsp + 0x1f8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x218 ], r13
mulx r13, r15, [ rax + 0x28 ]
add r10, [ rsp - 0x40 ]
adcx r8, [ rsp - 0x48 ]
xor rdx, rdx
adox r10, r11
adox rbp, r8
adcx rcx, [ rsp + 0x88 ]
adcx rdi, [ rsp + 0x80 ]
mov rdx, [ rsi + 0x18 ]
mulx r8, r11, [ rax + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x220 ], rbp
mov [ rsp + 0x228 ], r10
mulx r10, rbp, [ rax + 0x20 ]
add rcx, rbx
adcx r9, rdi
mov rdx, [ rax + 0x20 ]
mulx rdi, rbx, [ rsi + 0x18 ]
xor rdx, rdx
adox rcx, r11
adox r8, r9
mov rdx, [ rsi + 0x0 ]
mulx r9, r11, [ rax + 0x30 ]
adcx rcx, rbp
adcx r10, r8
mov rdx, [ rsi + 0x0 ]
mulx r8, rbp, [ rax + 0x28 ]
xor rdx, rdx
adox r12, rbp
adox r8, [ rsp + 0x218 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x230 ], r9
mulx r9, rbp, [ rax + 0x38 ]
mov rdx, rbx
adcx rdx, [ rsp + 0x208 ]
adcx rdi, [ rsp + 0x200 ]
xor rbx, rbx
adox r12, [ rsp + 0x1d0 ]
adox r8, [ rsp + 0x1c8 ]
adcx rdx, r15
adcx r13, rdi
mov r15, rdx
mov rdx, [ rsi + 0x8 ]
mulx rbx, rdi, [ rax + 0x30 ]
xor rdx, rdx
adox r15, rdi
adox rbx, r13
adcx r15, rbp
adcx r9, rbx
mov rbp, 0x3a 
bzhi r13, r12, rbp
adox rcx, [ rsp + 0x48 ]
adox r10, [ rsp + 0x40 ]
test al, al
adox rcx, r11
adox r10, [ rsp + 0x230 ]
shrd r12, r8, 58
shr r8, 58
add rcx, r12
adcx r8, r10
mov r11, rcx
shrd r11, r8, 58
shr r8, 58
mov rdx, [ rax + 0x30 ]
mulx rbx, rdi, [ rsi + 0x10 ]
mov rdx, rdi
test al, al
adox rdx, [ rsp + 0x228 ]
adox rbx, [ rsp + 0x220 ]
adcx r15, r11
adcx r8, r9
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x28 ], r13
bzhi r13, r15, rbp
mov r10, rdx
mov rdx, [ rax + 0x40 ]
mulx r11, r12, [ rsi + 0x0 ]
adox r10, [ rsp + 0x78 ]
adox rbx, [ rsp + 0x70 ]
xor rdx, rdx
adox r10, r12
adox r11, rbx
bzhi rdi, r14, rbp
shrd r15, r8, 58
shr r8, 58
test al, al
adox r10, r15
adox r8, r11
bzhi r14, rcx, rbp
mov [ r9 + 0x30 ], r14
mov rcx, 0x39 
bzhi r12, r10, rcx
mov [ r9 + 0x40 ], r12
shrd r10, r8, 57
shr r8, 57
xor rbx, rbx
adox r10, rdi
adox r8, rbx
bzhi rdx, r10, rbp
shrd r10, r8, 58
mov [ r9 + 0x0 ], rdx
add r10, [ rsp + 0x158 ]
mov r11, r10
shr r11, 58
bzhi rdi, r10, rbp
mov [ r9 + 0x8 ], rdi
mov [ r9 + 0x38 ], r13
add r11, [ rsp + 0x190 ]
mov [ r9 + 0x10 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 696
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.2394
; seed 2731862199105512 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 6577009 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=71, initial num_batches=31): 132372 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.020126473903259064
; number reverted permutation / tried permutation: 62082 / 90327 =68.730%
; number reverted decision / tried decision: 51985 / 89672 =57.972%
; validated in 4.123s
