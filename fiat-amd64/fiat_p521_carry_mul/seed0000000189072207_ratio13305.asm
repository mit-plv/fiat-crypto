SECTION .text
	GLOBAL fiat_p521_carry_mul
fiat_p521_carry_mul:
sub rsp, 544
mov rax, rdx
mov rdx, [ rdx + 0x8 ]
mulx r11, r10, [ rsi + 0x20 ]
mov rdx, [ rax + 0x10 ]
mov rcx, rdx
shl rcx, 0x1
mov rdx, [ rsi + 0x30 ]
mulx r9, r8, [ rax + 0x8 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rax + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r15
mulx r15, rdi, [ rax + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x40 ], r14
mov [ rsp - 0x38 ], r11
mulx r11, r14, [ rax + 0x10 ]
imul rdx, [ rax + 0x40 ], 0x2
mov [ rsp - 0x30 ], r10
mov r10, [ rax + 0x20 ]
mov [ rsp - 0x28 ], rbp
lea rbp, [r10 + r10]
imul r10, [ rax + 0x8 ], 0x2
mov [ rsp - 0x20 ], rbx
mov rbx, [ rax + 0x18 ]
mov [ rsp - 0x18 ], r13
lea r13, [rbx + rbx]
mov rbx, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x10 ], r12
mov [ rsp - 0x8 ], r11
mulx r11, r12, r13
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x0 ], r14
mov [ rsp + 0x8 ], r9
mulx r9, r14, [ rax + 0x28 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x10 ], r9
mov [ rsp + 0x18 ], r14
mulx r14, r9, rcx
add r9, r12
adcx r11, r14
mov rdx, [ rsi + 0x40 ]
mulx r14, r12, rbx
imul rdx, [ rax + 0x30 ], 0x2
mov [ rsp + 0x20 ], r8
mov [ rsp + 0x28 ], r15
mulx r15, r8, [ rsi + 0x40 ]
mov [ rsp + 0x30 ], rdi
mov rdi, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x38 ], r14
mov [ rsp + 0x40 ], r12
mulx r12, r14, [ rsi + 0x20 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x48 ], r12
mov [ rsp + 0x50 ], r14
mulx r14, r12, [ rsi + 0x20 ]
mov rdx, 0x1 
mov [ rsp + 0x58 ], r14
shlx r14, [ rax + 0x28 ], rdx
mov rdx, r14
mov [ rsp + 0x60 ], r12
mulx r12, r14, [ rsi + 0x40 ]
mov [ rsp + 0x68 ], r11
mov [ rsp + 0x70 ], r9
mulx r9, r11, [ rsi + 0x38 ]
mov [ rsp + 0x78 ], r10
mov [ rsp + 0x80 ], r9
mulx r9, r10, [ rsi + 0x20 ]
mov [ rsp + 0x88 ], r9
imul r9, [ rax + 0x38 ], 0x2
mov [ rsp + 0x90 ], r10
mov r10, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x98 ], r11
mov [ rsp + 0xa0 ], rbp
mulx rbp, r11, r9
xor rdx, rdx
adox r8, r11
adox rbp, r15
mov rdx, rdi
mulx r15, rdi, [ rsi + 0x38 ]
adcx r14, rdi
adcx r15, r12
mov r12, rdx
mov rdx, [ rsi + 0x30 ]
mulx rdi, r11, r9
xor rdx, rdx
adox r14, r11
adox rdi, r15
mov rdx, [ rsp + 0xa0 ]
mulx r11, r15, [ rsi + 0x38 ]
mov [ rsp + 0xa8 ], rbp
mov [ rsp + 0xb0 ], r8
mulx r8, rbp, [ rsi + 0x40 ]
mov [ rsp + 0xb8 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xc0 ], r14
mov [ rsp + 0xc8 ], r11
mulx r11, r14, rbx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xd0 ], r11
mov [ rsp + 0xd8 ], r14
mulx r14, r11, rbx
adcx rbp, [ rsp + 0x98 ]
adcx r8, [ rsp + 0x80 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0xe0 ], r14
mov [ rsp + 0xe8 ], r11
mulx r11, r14, r13
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xf0 ], r8
mov [ rsp + 0xf8 ], rbp
mulx rbp, r8, r13
add r14, r15
adcx r11, [ rsp + 0xc8 ]
mov rdx, [ rsi + 0x38 ]
mulx r15, r13, rcx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x100 ], r11
mulx r11, rcx, [ rax + 0x20 ]
mov rdx, [ rsp + 0x78 ]
mov [ rsp + 0x108 ], r11
mov [ rsp + 0x110 ], rcx
mulx rcx, r11, [ rsi + 0x40 ]
xor rdx, rdx
adox r11, r13
adox r15, rcx
adcx r11, r8
adcx rbp, r15
mov rdx, rdi
mulx r8, rdi, [ rsi + 0x28 ]
test al, al
adox r11, rdi
adox r8, rbp
mulx rcx, r13, [ rsi + 0x30 ]
mov rdx, r13
adcx rdx, [ rsp + 0x70 ]
adcx rcx, [ rsp + 0x68 ]
xchg rdx, r10
mulx rbp, r15, [ rsi + 0x30 ]
mulx r13, rdi, [ rsi + 0x28 ]
xor rdx, rdx
adox r14, r15
adox rbp, [ rsp + 0x100 ]
adcx r10, rdi
adcx r13, rcx
mov rdx, r12
mulx rcx, r12, [ rsi + 0x20 ]
mulx rdi, r15, [ rsi + 0x28 ]
add r14, r15
adcx rdi, rbp
test al, al
adox r10, r12
adox rcx, r13
mov rbp, rdx
mov rdx, [ rsi + 0x10 ]
mulx r12, r13, r9
mov rdx, rbp
mulx r15, rbp, [ rsi + 0x18 ]
adcx r11, [ rsp + 0x90 ]
adcx r8, [ rsp + 0x88 ]
add r11, rbp
adcx r15, r8
add r11, r13
adcx r12, r15
mov r13, rdx
mov rdx, [ rsi + 0x20 ]
mulx r8, rbp, r9
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x118 ], r12
mulx r12, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x120 ], r12
mov [ rsp + 0x128 ], r15
mulx r15, r12, rbx
xor rdx, rdx
adox r14, rbp
adox r8, rdi
adcx r14, r12
adcx r15, r8
mov rdx, [ rsi + 0x18 ]
mulx rbp, rdi, r9
xor rdx, rdx
adox r10, rdi
adox rbp, rcx
adcx r11, [ rsp + 0xd8 ]
mov rcx, [ rsp + 0xd0 ]
adcx rcx, [ rsp + 0x118 ]
add r11, [ rsp + 0x128 ]
adcx rcx, [ rsp + 0x120 ]
mov rdx, r13
mulx r12, r13, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x10 ]
mulx rdi, r8, rbx
test al, al
adox r10, r8
adox rdi, rbp
mov rdx, [ rax + 0x0 ]
mulx r8, rbp, [ rsi + 0x8 ]
mov rdx, r13
adcx rdx, [ rsp + 0xf8 ]
adcx r12, [ rsp + 0xf0 ]
xchg rdx, r9
mov [ rsp + 0x130 ], r15
mulx r15, r13, [ rsi + 0x28 ]
add r10, rbp
adcx r8, rdi
xor rdi, rdi
adox r9, r13
adox r15, r12
mov rbp, 0x3a 
bzhi r12, r11, rbp
mov r13, rdx
mov rdx, [ rsi + 0x0 ]
mulx rbp, rdi, [ rax + 0x8 ]
adox r10, rdi
adox rbp, r8
shrd r11, rcx, 58
shr rcx, 58
mov rdx, [ rsi + 0x10 ]
mulx rdi, r8, [ rax + 0x0 ]
test al, al
adox r10, r11
adox rcx, rbp
mov rdx, [ rax + 0x8 ]
mulx r11, rbp, [ rsi + 0x8 ]
adcx r14, r8
adcx rdi, [ rsp + 0x130 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x138 ], r12
mulx r12, r8, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x140 ], r15
mov [ rsp + 0x148 ], r9
mulx r9, r15, [ rsi + 0x38 ]
test al, al
adox r14, rbp
adox r11, rdi
adcx r14, r8
adcx r12, r11
mov rdx, [ rsi + 0x20 ]
mulx rdi, rbp, rbx
mov rdx, 0x3a 
bzhi r8, r10, rdx
mov r11, r15
adox r11, [ rsp + 0x40 ]
adox r9, [ rsp + 0x38 ]
mov r15, rbp
add r15, [ rsp + 0x148 ]
adcx rdi, [ rsp + 0x140 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x150 ], r8
mulx r8, rbp, [ rax + 0x0 ]
xor rdx, rdx
adox r15, rbp
adox r8, rdi
adcx r15, [ rsp + 0x30 ]
adcx r8, [ rsp + 0x28 ]
test al, al
adox r11, [ rsp + 0x20 ]
adox r9, [ rsp + 0x8 ]
mov rdx, [ rax + 0x8 ]
mulx rbp, rdi, [ rsi + 0x28 ]
shrd r10, rcx, 58
shr rcx, 58
xor rdx, rdx
adox r14, r10
adox rcx, r12
mov rdx, [ rsi + 0x38 ]
mulx r10, r12, rbx
mov rdx, r13
mov [ rsp + 0x158 ], r9
mulx r9, r13, [ rsi + 0x40 ]
adcx r13, r12
adcx r10, r9
test al, al
adox r15, [ rsp + 0x0 ]
adox r8, [ rsp - 0x8 ]
adcx r15, [ rsp - 0x10 ]
adcx r8, [ rsp - 0x18 ]
mov rdx, r14
shrd rdx, rcx, 58
shr rcx, 58
add r15, rdx
adcx rcx, r8
mov rdx, [ rax + 0x0 ]
mulx r9, r12, [ rsi + 0x30 ]
mov rdx, 0x3ffffffffffffff 
and r14, rdx
mov r8, r15
and r8, rdx
adox r13, r12
adox r9, r10
adcx r13, rdi
adcx rbp, r9
shrd r15, rcx, 58
shr rcx, 58
mov rdx, [ rax + 0x8 ]
mulx r10, rdi, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mulx r9, r12, [ rsi + 0x28 ]
xor rdx, rdx
adox r13, [ rsp + 0x50 ]
adox rbp, [ rsp + 0x48 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x160 ], r14
mov [ rsp + 0x168 ], r8
mulx r8, r14, rbx
adcx r11, r12
adcx r9, [ rsp + 0x158 ]
mov rdx, [ rsi + 0x20 ]
mulx r12, rbx, [ rax + 0x18 ]
test al, al
adox r11, rbx
adox r12, r9
mov rdx, r14
adcx rdx, [ rsp + 0xc0 ]
adcx r8, [ rsp + 0xb8 ]
mov r14, rdx
mov rdx, [ rax + 0x0 ]
mulx rbx, r9, [ rsi + 0x20 ]
xor rdx, rdx
adox r14, r9
adox rbx, r8
adcx r14, rdi
adcx r10, rbx
xor rdi, rdi
adox r11, [ rsp - 0x20 ]
adox r12, [ rsp - 0x28 ]
mov rdx, [ rax + 0x18 ]
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx rdi, rbx, [ rax + 0x10 ]
adcx r14, rbx
adcx rdi, r10
test al, al
adox r14, r8
adox r9, rdi
mov rdx, [ rsi + 0x28 ]
mulx r8, r10, [ rax + 0x0 ]
adcx r14, [ rsp + 0x110 ]
adcx r9, [ rsp + 0x108 ]
mov rdx, [ rsi + 0x10 ]
mulx rdi, rbx, [ rax + 0x20 ]
xor rdx, rdx
adox r14, r15
adox rcx, r9
mov r15, [ rsp + 0xb0 ]
adcx r15, [ rsp + 0xe8 ]
mov r9, [ rsp + 0xa8 ]
adcx r9, [ rsp + 0xe0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x170 ], r12
mov [ rsp + 0x178 ], r11
mulx r11, r12, [ rax + 0x18 ]
add r13, r12
adcx r11, rbp
test al, al
adox r15, r10
adox r8, r9
mov rdx, [ rsp + 0x168 ]
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x18 ], rdx
adcx r15, [ rsp - 0x30 ]
adcx r8, [ rsp - 0x38 ]
mov rdx, [ rax + 0x10 ]
mulx r9, r10, [ rsi + 0x18 ]
add r13, rbx
adcx rdi, r11
mov rdx, [ rsi + 0x10 ]
mulx r12, rbx, [ rax + 0x18 ]
test al, al
adox r15, r10
adox r9, r8
adcx r13, [ rsp - 0x40 ]
adcx rdi, [ rsp - 0x48 ]
xor rdx, rdx
adox r15, rbx
adox r12, r9
mov rdx, [ rax + 0x8 ]
mulx r8, r11, [ rsi + 0x38 ]
mov rdx, 0x3a 
bzhi r10, r14, rdx
mov rdx, [ rax + 0x0 ]
mulx r9, rbx, [ rsi + 0x40 ]
adox rbx, r11
adox r8, r9
mov [ rbp + 0x20 ], r10
mov rdx, [ rax + 0x28 ]
mulx r10, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx rbp, r9, [ rax + 0x20 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x180 ], rdi
mov [ rsp + 0x188 ], r13
mulx r13, rdi, [ rsi + 0x28 ]
test al, al
adox r15, r9
adox rbp, r12
adcx r15, r11
adcx r10, rbp
mov rdx, [ rsi + 0x30 ]
mulx r11, r12, [ rax + 0x10 ]
xor rdx, rdx
adox rbx, r12
adox r11, r8
adcx rbx, rdi
adcx r13, r11
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, [ rax + 0x30 ]
mov rdx, [ rax + 0x28 ]
mulx rbp, rdi, [ rsi + 0x18 ]
add rbx, [ rsp + 0x60 ]
adcx r13, [ rsp + 0x58 ]
mov rdx, [ rsi + 0x0 ]
mulx r11, r12, [ rax + 0x30 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x190 ], r9
mov [ rsp + 0x198 ], r8
mulx r8, r9, [ rax + 0x38 ]
shrd r14, rcx, 58
shr rcx, 58
test al, al
adox r15, r14
adox rcx, r10
mov rdx, r12
adcx rdx, [ rsp + 0x188 ]
adcx r11, [ rsp + 0x180 ]
xor r10, r10
adox rbx, rdi
adox rbp, r13
adcx rbx, [ rsp + 0x198 ]
adcx rbp, [ rsp + 0x190 ]
xor rdi, rdi
adox rbx, r9
adox r8, rbp
mov r10, r15
shrd r10, rcx, 58
shr rcx, 58
xor r13, r13
adox rdx, r10
adox rcx, r11
mov rdi, 0x3ffffffffffffff 
and r15, rdi
mov r12, [ rsp + 0x18 ]
mov r9, r12
adox r9, [ rsp + 0x178 ]
mov r14, [ rsp + 0x10 ]
adox r14, [ rsp + 0x170 ]
mov r12, rdx
mov rdx, [ rax + 0x40 ]
mulx rbp, r11, [ rsi + 0x0 ]
adcx rbx, r11
adcx rbp, r8
mov rdx, [ rsi + 0x8 ]
mulx r10, r8, [ rax + 0x30 ]
add r9, r8
adcx r10, r14
mov rdx, [ rsi + 0x0 ]
mulx r11, r14, [ rax + 0x38 ]
mov rdx, r12
shrd rdx, rcx, 58
shr rcx, 58
test al, al
adox r9, r14
adox r11, r10
adcx r9, rdx
adcx rcx, r11
mov r8, r9
shrd r8, rcx, 58
shr rcx, 58
xor r10, r10
adox rbx, r8
adox rcx, rbp
and r9, rdi
mov r13, rbx
shrd r13, rcx, 57
shr rcx, 57
xor rbp, rbp
adox r13, [ rsp + 0x138 ]
adox rcx, rbp
mov r10, r13
shrd r10, rcx, 58
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x38 ], r9
mov rdx, 0x39 
bzhi r11, rbx, rdx
add r10, [ rsp + 0x150 ]
mov r8, r10
and r8, rdi
shr r10, 58
mov [ r14 + 0x40 ], r11
mov [ r14 + 0x8 ], r8
add r10, [ rsp + 0x160 ]
and r13, rdi
mov [ r14 + 0x10 ], r10
mov [ r14 + 0x0 ], r13
and r12, rdi
mov [ r14 + 0x28 ], r15
mov [ r14 + 0x30 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 544
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.3305
; seed 4202494371071887 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 9985697 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=49, initial num_batches=31): 211805 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.02121083786139315
; number reverted permutation / tried permutation: 66463 / 89873 =73.952%
; number reverted decision / tried decision: 55620 / 90126 =61.714%
; validated in 4.722s
