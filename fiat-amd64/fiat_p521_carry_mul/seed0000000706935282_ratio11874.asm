SECTION .text
	GLOBAL fiat_p521_carry_mul
fiat_p521_carry_mul:
sub rsp, 704
mov rax, rdx
mov rdx, [ rdx + 0x10 ]
mulx r11, r10, [ rsi + 0x10 ]
mov rdx, [ rax + 0x28 ]
mov rcx, rdx
shl rcx, 0x1
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rax + 0x10 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rax + 0x20 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x50 ], rdi
lea rdi, [rdx + rdx]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x48 ], rbp
mov rbp, rdx
shl rbp, 0x1
imul rdx, [ rax + 0x20 ], 0x2
mov [ rsp - 0x40 ], rbx
mov rbx, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x38 ], r15
mov [ rsp - 0x30 ], r14
mulx r14, r15, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], r14
mov [ rsp - 0x20 ], r15
mulx r15, r14, [ rax + 0x18 ]
mov rdx, rdi
mov [ rsp - 0x18 ], r15
mulx r15, rdi, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], r14
mov r14, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x8 ], r11
mov [ rsp + 0x0 ], r10
mulx r10, r11, [ rsi + 0x18 ]
mov rdx, rcx
mov [ rsp + 0x8 ], r13
mulx r13, rcx, [ rsi + 0x20 ]
mov [ rsp + 0x10 ], r12
mov r12, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x18 ], r9
mov [ rsp + 0x20 ], r8
mulx r8, r9, [ rsi + 0x10 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x28 ], r8
mov r8, rdx
shl r8, 0x1
mov rdx, r8
mov [ rsp + 0x30 ], r9
mulx r9, r8, [ rsi + 0x18 ]
mov [ rsp + 0x38 ], r15
mov r15, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x40 ], rdi
mov [ rsp + 0x48 ], r10
mulx r10, rdi, [ rsi + 0x38 ]
mov rdx, r15
mov [ rsp + 0x50 ], r11
mulx r11, r15, [ rsi + 0x28 ]
mov [ rsp + 0x58 ], r11
mov r11, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x60 ], r15
mov [ rsp + 0x68 ], r9
mulx r9, r15, [ rsi + 0x40 ]
mov rdx, r11
mov [ rsp + 0x70 ], r8
mulx r8, r11, [ rsi + 0x38 ]
mov [ rsp + 0x78 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x80 ], rcx
mov [ rsp + 0x88 ], rbx
mulx rbx, rcx, r14
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x90 ], rbx
mov [ rsp + 0x98 ], rcx
mulx rcx, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0xa0 ], rcx
mov [ rsp + 0xa8 ], rbx
mulx rbx, rcx, rbp
mov rdx, [ rax + 0x10 ]
lea rbp, [rdx + rdx]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xb0 ], r8
mov [ rsp + 0xb8 ], r11
mulx r11, r8, rbp
imul rdx, [ rax + 0x40 ], 0x2
xchg rdx, r12
mov [ rsp + 0xc0 ], r12
mov [ rsp + 0xc8 ], rbx
mulx rbx, r12, [ rsi + 0x38 ]
xchg rdx, rbp
mov [ rsp + 0xd0 ], rbx
mov [ rsp + 0xd8 ], r12
mulx r12, rbx, [ rsi + 0x40 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0xe0 ], r12
mov r12, rdx
shl r12, 0x1
xor rdx, rdx
adox r15, rdi
adox r10, r9
mov rdx, r12
mulx rdi, r12, [ rsi + 0x30 ]
adcx rcx, r8
adcx r11, [ rsp + 0xc8 ]
xor r9, r9
adox rcx, r12
adox rdi, r11
mov r8, rdx
mov rdx, [ rsp + 0xc0 ]
mulx r11, r12, [ rsi + 0x8 ]
mov r9, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xe8 ], r10
mov [ rsp + 0xf0 ], r15
mulx r15, r10, r14
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0xf8 ], r15
mov [ rsp + 0x100 ], r10
mulx r10, r15, rbp
mov rdx, r8
mov [ rsp + 0x108 ], r11
mulx r11, r8, [ rsi + 0x38 ]
adcx r15, [ rsp + 0xb8 ]
adcx r10, [ rsp + 0xb0 ]
mov [ rsp + 0x110 ], r12
xor r12, r12
adox rbx, r8
adox r11, [ rsp + 0xe0 ]
mov r8, rdx
mov rdx, [ rsp + 0x88 ]
mov [ rsp + 0x118 ], r11
mulx r11, r12, [ rsi + 0x28 ]
xchg rdx, r14
mov [ rsp + 0x120 ], rbx
mov [ rsp + 0x128 ], r10
mulx r10, rbx, [ rsi + 0x30 ]
adcx rcx, r12
adcx r11, rdi
xor rdi, rdi
adox r15, rbx
adox r10, [ rsp + 0x128 ]
mulx rbx, r12, [ rsi + 0x10 ]
adcx rcx, [ rsp + 0x80 ]
adcx r11, [ rsp + 0x78 ]
mov [ rsp + 0x130 ], r10
xor r10, r10
adox rcx, [ rsp + 0x70 ]
adox r11, [ rsp + 0x68 ]
adcx rcx, r12
adcx rbx, r11
mov rdi, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r12, [ rax + 0x0 ]
mov rdx, r9
mulx r10, r9, [ rsi + 0x40 ]
mov [ rsp + 0x138 ], r10
mov r10, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x140 ], r9
mov [ rsp + 0x148 ], r15
mulx r15, r9, r13
test al, al
adox rcx, [ rsp + 0x110 ]
adox rbx, [ rsp + 0x108 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x150 ], r15
mov [ rsp + 0x158 ], r9
mulx r9, r15, r8
mov rdx, rbp
mulx r8, rbp, [ rsi + 0x30 ]
xchg rdx, r14
mov [ rsp + 0x160 ], rbx
mov [ rsp + 0x168 ], rcx
mulx rcx, rbx, [ rsi + 0x38 ]
adcx r15, rbx
adcx rcx, r9
xor r9, r9
adox r15, rbp
adox r8, rcx
mulx rbx, rbp, [ rsi + 0x40 ]
adcx r15, [ rsp + 0x60 ]
adcx r8, [ rsp + 0x58 ]
mov rcx, r12
add rcx, [ rsp + 0x168 ]
adcx r11, [ rsp + 0x160 ]
xor r12, r12
adox rbp, [ rsp + 0xd8 ]
adox rbx, [ rsp + 0xd0 ]
mov r9, 0x3a 
bzhi r12, rcx, r9
shrd rcx, r11, 58
shr r11, 58
mov [ rsp + 0x170 ], r12
mulx r12, r9, [ rsi + 0x30 ]
mov rdx, r9
add rdx, [ rsp + 0x120 ]
adcx r12, [ rsp + 0x118 ]
mov r9, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x178 ], r11
mov [ rsp + 0x180 ], rcx
mulx rcx, r11, r14
test al, al
adox r9, r11
adox rcx, r12
adcx r15, [ rsp + 0x100 ]
adcx r8, [ rsp + 0xf8 ]
mov rdx, [ rsi + 0x18 ]
mulx r12, r14, r10
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x188 ], rbx
mulx rbx, r11, r13
xor rdx, rdx
adox r15, r14
adox r12, r8
adcx r9, r11
adcx rbx, rcx
mov rdx, [ rsi + 0x20 ]
mulx r8, rcx, r10
mov rdx, rdi
mulx r14, rdi, [ rsi + 0x28 ]
mov r11, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x190 ], r12
mov [ rsp + 0x198 ], r15
mulx r15, r12, r13
xor rdx, rdx
adox rbp, r12
adox r15, [ rsp + 0x188 ]
adcx rbp, rdi
adcx r14, r15
mov rdx, [ rsi + 0x8 ]
mulx rdi, r13, [ rax + 0x8 ]
add rbp, rcx
adcx r8, r14
mov rdx, [ rax + 0x0 ]
mulx r12, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mulx r14, r15, r10
test al, al
adox rbp, [ rsp + 0x50 ]
adox r8, [ rsp + 0x48 ]
adcx r9, [ rsp + 0x40 ]
adcx rbx, [ rsp + 0x38 ]
mov rdx, rcx
mov [ rsp + 0x1a0 ], r8
xor r8, r8
adox rdx, [ rsp + 0x198 ]
adox r12, [ rsp + 0x190 ]
adcx r9, r15
adcx r14, rbx
mov rcx, rdx
mov rdx, [ rax + 0x0 ]
mulx rbx, r15, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x1a8 ], rbp
mulx rbp, r8, [ rax + 0x8 ]
add r9, r15
adcx rbx, r14
xor rdx, rdx
adox rcx, r13
adox rdi, r12
adcx rcx, [ rsp + 0x20 ]
adcx rdi, [ rsp + 0x18 ]
mov rdx, [ rax + 0x10 ]
mulx r12, r13, [ rsi + 0x8 ]
mov rdx, [ rsp + 0x30 ]
mov r14, rdx
xor r15, r15
adox r14, [ rsp + 0x1a8 ]
mov [ rsp + 0x1b0 ], rdi
mov rdi, [ rsp + 0x28 ]
adox rdi, [ rsp + 0x1a0 ]
adcx r14, r13
adcx r12, rdi
mov rdx, r10
mulx r13, r10, [ rsi + 0x28 ]
mov rdi, r10
test al, al
adox rdi, [ rsp + 0x148 ]
adox r13, [ rsp + 0x130 ]
adcx r9, r8
adcx rbp, rbx
xor r8, r8
adox r9, [ rsp + 0x180 ]
adox rbp, [ rsp + 0x178 ]
xchg rdx, r11
mulx rbx, r15, [ rsi + 0x38 ]
mov rdx, 0x3a 
bzhi r10, r9, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x1b8 ], r10
mulx r10, r8, [ rax + 0x0 ]
adox rdi, r8
adox r10, r13
add rdi, [ rsp + 0x10 ]
adcx r10, [ rsp + 0x8 ]
mov rdx, [ rax + 0x20 ]
mulx r8, r13, [ rsi + 0x0 ]
shrd r9, rbp, 58
shr rbp, 58
test al, al
adox rcx, r9
adox rbp, [ rsp + 0x1b0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x1c0 ], rbx
mulx rbx, r9, [ rax + 0x18 ]
adcx r14, r9
adcx rbx, r12
mov rdx, rcx
shrd rdx, rbp, 58
shr rbp, 58
xor r12, r12
adox r14, rdx
adox rbp, rbx
mov r9, r14
shrd r9, rbp, 58
shr rbp, 58
test al, al
adox rdi, [ rsp + 0x0 ]
adox r10, [ rsp - 0x8 ]
adcx rdi, [ rsp - 0x10 ]
adcx r10, [ rsp - 0x18 ]
mov rdx, [ rax + 0x0 ]
mulx r12, rbx, [ rsi + 0x30 ]
mov rdx, 0x3ffffffffffffff 
and r14, rdx
mov rdx, r11
mov [ rsp + 0x1c8 ], r14
mulx r14, r11, [ rsi + 0x30 ]
mov [ rsp + 0x1d0 ], rbp
mov [ rsp + 0x1d8 ], r9
mulx r9, rbp, [ rsi + 0x38 ]
adox rdi, r13
adox r8, r10
mov rdx, rbp
adcx rdx, [ rsp + 0x98 ]
adcx r9, [ rsp + 0x90 ]
mov r13, r15
test al, al
adox r13, [ rsp + 0x158 ]
mov r10, [ rsp + 0x1c0 ]
adox r10, [ rsp + 0x150 ]
mov r15, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x1e0 ], r8
mulx r8, rbp, [ rax + 0x0 ]
adcx r13, r11
adcx r14, r10
mov rdx, [ rsi + 0x28 ]
mulx r10, r11, [ rax + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x1e8 ], rdi
mov [ rsp + 0x1f0 ], r10
mulx r10, rdi, [ rax + 0x8 ]
add r13, rbp
adcx r8, r14
add r13, rdi
adcx r10, r8
mov rdx, [ rax + 0x18 ]
mulx r14, rbp, [ rsi + 0x18 ]
xor rdx, rdx
adox r15, rbx
adox r12, r9
mov rdx, [ rax + 0x10 ]
mulx r9, rbx, [ rsi + 0x20 ]
adcx r15, r11
adcx r12, [ rsp + 0x1f0 ]
mov rdx, 0x3a 
bzhi r11, rcx, rdx
adox r15, rbx
adox r9, r12
test al, al
adox r15, rbp
adox r14, r9
adcx r15, [ rsp - 0x30 ]
adcx r14, [ rsp - 0x38 ]
mov rdx, [ rsi + 0x28 ]
mulx rdi, rcx, [ rax + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mulx rbp, r8, [ rax + 0x20 ]
mov rdx, [ rsi + 0x30 ]
mulx r12, rbx, [ rax + 0x10 ]
mov rdx, rbx
add rdx, [ rsp + 0xf0 ]
adcx r12, [ rsp + 0xe8 ]
mov r9, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x1f8 ], r11
mulx r11, rbx, [ rsi + 0x20 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x200 ], rbp
mov [ rsp + 0x208 ], r8
mulx r8, rbp, [ rsi + 0x0 ]
xor rdx, rdx
adox r9, rcx
adox rdi, r12
mov rdx, [ rsi + 0x18 ]
mulx r12, rcx, [ rax + 0x10 ]
adcx r13, rcx
adcx r12, r10
xor rdx, rdx
adox r13, [ rsp - 0x20 ]
adox r12, [ rsp - 0x28 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r10, [ rax + 0x20 ]
adcx r9, rbx
adcx r11, rdi
mov rdx, [ rsi + 0x8 ]
mulx rdi, rbx, [ rax + 0x28 ]
add r13, r10
adcx rcx, r12
mov rdx, [ rsi + 0x18 ]
mulx r10, r12, [ rax + 0x28 ]
test al, al
adox r15, rbx
adox rdi, r14
mov rdx, [ rsp + 0x1e8 ]
adcx rdx, [ rsp + 0x1d8 ]
mov r14, [ rsp + 0x1e0 ]
adcx r14, [ rsp + 0x1d0 ]
mov rbx, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x210 ], rdi
mov [ rsp + 0x218 ], r15
mulx r15, rdi, [ rax + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x220 ], r11
mov [ rsp + 0x228 ], r9
mulx r9, r11, [ rax + 0x30 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x230 ], r9
mov [ rsp + 0x238 ], r11
mulx r11, r9, [ rax + 0x8 ]
xor rdx, rdx
adox r13, rbp
adox r8, rcx
mov rbp, rbx
shrd rbp, r14, 58
shr r14, 58
test al, al
adox r13, rbp
adox r14, r8
mov rcx, rdi
adcx rcx, [ rsp + 0x140 ]
adcx r15, [ rsp + 0x138 ]
mov rdi, 0x3ffffffffffffff 
mov r8, r13
and r8, rdi
adox rcx, r9
adox r11, r15
mov rdx, [ rsi + 0x28 ]
mulx rbp, r9, [ rax + 0x10 ]
adcx rcx, r9
adcx rbp, r11
mov rdx, [ rsi + 0x10 ]
mulx r11, r15, [ rax + 0x28 ]
mov rdx, [ rax + 0x18 ]
mulx rdi, r9, [ rsi + 0x20 ]
xor rdx, rdx
adox rcx, r9
adox rdi, rbp
adcx rcx, [ rsp + 0x208 ]
adcx rdi, [ rsp + 0x200 ]
add rcx, r15
adcx r11, rdi
mov rbp, r12
test al, al
adox rbp, [ rsp + 0x228 ]
adox r10, [ rsp + 0x220 ]
adcx rcx, [ rsp + 0x238 ]
adcx r11, [ rsp + 0x230 ]
mov rdx, [ rsi + 0x10 ]
mulx r15, r12, [ rax + 0x30 ]
xor rdx, rdx
adox rbp, r12
adox r15, r10
mov r9, [ rsp + 0xa8 ]
mov rdi, r9
adcx rdi, [ rsp + 0x218 ]
mov r10, [ rsp + 0xa0 ]
adcx r10, [ rsp + 0x210 ]
shrd r13, r14, 58
shr r14, 58
add rdi, r13
adcx r14, r10
mov r9, 0x3ffffffffffffff 
mov r12, rdi
and r12, r9
mov rdx, [ rsi + 0x0 ]
mulx r13, r10, [ rax + 0x40 ]
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x30 ], r12
mov [ rdx + 0x28 ], r8
mov r8, rdx
mov rdx, [ rax + 0x38 ]
mulx r9, r12, [ rsi + 0x8 ]
adox rbp, r12
adox r9, r15
adcx rcx, [ rsp - 0x40 ]
adcx r11, [ rsp - 0x48 ]
shrd rdi, r14, 58
shr r14, 58
test al, al
adox rcx, rdi
adox r14, r11
adcx rbp, r10
adcx r13, r9
mov rdx, rcx
shrd rdx, r14, 58
shr r14, 58
xor r15, r15
adox rbp, rdx
adox r14, r13
mov r10, rbp
shrd r10, r14, 57
shr r14, 57
mov r12, 0x3ffffffffffffff 
and rcx, r12
mov [ r8 + 0x38 ], rcx
adox r10, [ rsp + 0x170 ]
adox r14, r15
mov r9, r10
shrd r9, r14, 58
mov r11, 0x39 
bzhi rdi, rbp, r11
mov [ r8 + 0x40 ], rdi
add r9, [ rsp + 0x1b8 ]
mov r13, r9
and r13, r12
mov [ r8 + 0x8 ], r13
shr r9, 58
mov rdx, [ rsp + 0x1c8 ]
mov [ r8 + 0x18 ], rdx
and rbx, r12
and r10, r12
mov [ r8 + 0x0 ], r10
mov [ r8 + 0x20 ], rbx
add r9, [ rsp + 0x1f8 ]
mov [ r8 + 0x10 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 704
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.1874
; seed 3463897773646674 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 6348764 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=69, initial num_batches=31): 130151 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.02050021074968293
; number reverted permutation / tried permutation: 61060 / 89931 =67.896%
; number reverted decision / tried decision: 51835 / 90068 =57.551%
; validated in 3.889s
