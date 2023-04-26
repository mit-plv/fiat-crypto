SECTION .text
	GLOBAL fiat_p448_solinas_carry_mul
fiat_p448_solinas_carry_mul:
sub rsp, 632
mov rax, rdx
mov rdx, [ rsi + 0x38 ]
mulx r11, r10, [ rax + 0x8 ]
mov rdx, [ rax + 0x30 ]
mulx r8, rcx, [ rsi + 0x8 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x38 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x38 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x38 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], rdi
mov [ rsp - 0x40 ], r15
mulx r15, rdi, [ rax + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x38 ], r8
mov [ rsp - 0x30 ], rcx
mulx rcx, r8, [ rax + 0x20 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x28 ], r15
mov [ rsp - 0x20 ], rdi
mulx rdi, r15, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x18 ], rcx
mov [ rsp - 0x10 ], r8
mulx r8, rcx, [ rax + 0x20 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x8 ], r8
mov [ rsp + 0x0 ], rcx
mulx rcx, r8, [ rsi + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x8 ], rcx
mov [ rsp + 0x10 ], r8
mulx r8, rcx, [ rsi + 0x18 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x18 ], r8
mov [ rsp + 0x20 ], rcx
mulx rcx, r8, [ rsi + 0x30 ]
mov rdx, r15
test al, al
adox rdx, r8
mov [ rsp + 0x28 ], rbx
mov rbx, rcx
adox rbx, rdi
mov [ rsp + 0x30 ], r9
mov r9, rdx
adcx r9, r13
mov [ rsp + 0x38 ], r11
mov r11, r14
adcx r11, rbx
mov [ rsp + 0x40 ], r10
mov r10, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x48 ], r12
mov [ rsp + 0x50 ], rbp
mulx rbp, r12, [ rax + 0x18 ]
xor rdx, rdx
adox r10, r15
adox rdi, rbx
adcx r10, r8
adcx rcx, rdi
mov rdx, [ rsi + 0x10 ]
mulx r8, r15, [ rax + 0x38 ]
mov rdx, [ rax + 0x10 ]
mulx rdi, rbx, [ rsi + 0x0 ]
xor rdx, rdx
adox r10, r13
adox r14, rcx
mov rdx, [ rax + 0x18 ]
mulx rcx, r13, [ rsi + 0x30 ]
adcx r9, r13
mov rdx, rcx
adcx rdx, r11
xor r11, r11
adox r10, r13
adox rcx, r14
mov r14, rdx
mov rdx, [ rsi + 0x30 ]
mulx r11, r13, [ rax + 0x30 ]
mov rdx, r13
adcx rdx, [ rsp + 0x50 ]
mov [ rsp + 0x58 ], rdi
mov rdi, r11
adcx rdi, [ rsp + 0x48 ]
mov [ rsp + 0x60 ], rbx
mov rbx, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x68 ], r8
mov [ rsp + 0x70 ], r15
mulx r15, r8, [ rsi + 0x8 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x78 ], r15
mov [ rsp + 0x80 ], r8
mulx r8, r15, [ rsi + 0x28 ]
add rbx, r15
mov rdx, r8
adcx rdx, rdi
mov rdi, rbx
test al, al
adox rdi, [ rsp + 0x50 ]
mov [ rsp + 0x88 ], rbp
mov rbp, rdx
adox rbp, [ rsp + 0x48 ]
adcx rdi, r13
adcx r11, rbp
xor r13, r13
adox rdi, r15
adox r8, r11
mov r15, rdx
mov rdx, [ rsi + 0x30 ]
mulx r11, rbp, [ rax + 0x28 ]
adcx rdi, [ rsp + 0x40 ]
adcx r8, [ rsp + 0x38 ]
mov rdx, rbp
test al, al
adox rdx, [ rsp + 0x30 ]
adox r11, [ rsp + 0x28 ]
mov rbp, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x90 ], r12
mulx r12, r13, [ rax + 0x10 ]
adcx r9, [ rsp - 0x10 ]
adcx r14, [ rsp - 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x98 ], r14
mov [ rsp + 0xa0 ], r9
mulx r9, r14, [ rsi + 0x0 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0xa8 ], r9
mov [ rsp + 0xb0 ], r14
mulx r14, r9, [ rsi + 0x28 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xb8 ], rcx
mov [ rsp + 0xc0 ], r10
mulx r10, rcx, [ rsi + 0x20 ]
test al, al
adox rbp, r9
adox r14, r11
mov rdx, [ rax + 0x18 ]
mulx r9, r11, [ rsi + 0x28 ]
adcx rdi, r13
mov rdx, r12
adcx rdx, r8
mov r8, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xc8 ], r10
mov [ rsp + 0xd0 ], rcx
mulx rcx, r10, [ rax + 0x38 ]
xor rdx, rdx
adox rbp, r10
adox rcx, r14
adcx rdi, r11
mov r14, r9
adcx r14, r8
test al, al
adox rdi, [ rsp + 0x0 ]
adox r14, [ rsp - 0x8 ]
adcx rbx, [ rsp + 0x40 ]
adcx r15, [ rsp + 0x38 ]
xor r8, r8
adox rbx, r13
adox r12, r15
adcx rbx, r11
adcx r9, r12
mov rdx, [ rsi + 0x38 ]
mulx r11, r13, [ rax + 0x38 ]
mov rdx, r13
xor r10, r10
adox rdx, r13
mov r8, r11
adox r8, r11
mov r15, rdx
mov rdx, [ rax + 0x0 ]
mulx r10, r12, [ rsi + 0x38 ]
adcx rbx, [ rsp + 0x0 ]
adcx r9, [ rsp - 0x8 ]
mov rdx, [ rsp + 0xc0 ]
test al, al
adox rdx, [ rsp - 0x10 ]
mov [ rsp + 0xd8 ], rcx
mov rcx, [ rsp + 0xb8 ]
adox rcx, [ rsp - 0x18 ]
adcx r13, [ rsp + 0x90 ]
adcx r11, [ rsp + 0x88 ]
mov [ rsp + 0xe0 ], r11
xor r11, r11
adox rdx, [ rsp + 0xd0 ]
adox rcx, [ rsp + 0xc8 ]
mov r11, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xe8 ], rcx
mov [ rsp + 0xf0 ], r13
mulx r13, rcx, [ rax + 0x10 ]
adcx r15, [ rsp + 0x90 ]
adcx r8, [ rsp + 0x88 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xf8 ], r11
mov [ rsp + 0x100 ], r8
mulx r8, r11, [ rax + 0x28 ]
test al, al
adox rdi, r11
mov rdx, r8
adox rdx, r14
mov r14, rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x108 ], r15
mov [ rsp + 0x110 ], r13
mulx r13, r15, [ rsi + 0x10 ]
adcx rdi, r15
mov rdx, r13
adcx rdx, r14
mov r14, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x118 ], rcx
mov [ rsp + 0x120 ], rbp
mulx rbp, rcx, [ rsi + 0x30 ]
test al, al
adox rbx, r11
adox r8, r9
mov rdx, [ rax + 0x38 ]
mulx r11, r9, [ rsi + 0x8 ]
adcx rbx, r15
adcx r13, r8
mov rdx, [ rsi + 0x10 ]
mulx r8, r15, [ rax + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x128 ], r8
mov [ rsp + 0x130 ], r15
mulx r15, r8, [ rax + 0x0 ]
test al, al
adox rdi, r9
mov rdx, r11
adox rdx, r14
mov r14, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x138 ], rdi
mov [ rsp + 0x140 ], rbp
mulx rbp, rdi, [ rax + 0x10 ]
mov rdx, r12
adcx rdx, [ rsp + 0x120 ]
adcx r10, [ rsp + 0xd8 ]
mov r12, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x148 ], r14
mov [ rsp + 0x150 ], rbp
mulx rbp, r14, [ rax + 0x20 ]
test al, al
adox rbx, r9
adox r11, r13
mov rdx, r8
adcx rdx, [ rsp + 0x120 ]
adcx r15, [ rsp + 0xd8 ]
mov r9, rdx
mov rdx, [ rsi + 0x20 ]
mulx r8, r13, [ rax + 0x18 ]
add r9, [ rsp - 0x20 ]
adcx r15, [ rsp - 0x28 ]
xor rdx, rdx
adox r9, [ rsp + 0x118 ]
adox r15, [ rsp + 0x110 ]
adcx r12, rcx
adcx r10, [ rsp + 0x140 ]
test al, al
adox r12, rdi
adox r10, [ rsp + 0x150 ]
adcx r12, r13
adcx r8, r10
mov rdx, [ rsi + 0x0 ]
mulx rdi, rcx, [ rax + 0x38 ]
test al, al
adox r12, r14
adox rbp, r8
adcx r12, [ rsp + 0x130 ]
adcx rbp, [ rsp + 0x128 ]
add r12, [ rsp - 0x30 ]
adcx rbp, [ rsp - 0x38 ]
mov rdx, [ rax + 0x20 ]
mulx r13, r14, [ rsi + 0x30 ]
mov rdx, r14
xor r10, r10
adox rdx, [ rsp + 0x108 ]
mov r8, r13
adox r8, [ rsp + 0x100 ]
mov r10, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x158 ], r11
mov [ rsp + 0x160 ], rbx
mulx rbx, r11, [ rsi + 0x28 ]
adcx r12, rcx
adcx rdi, rbp
mov rdx, r12
shrd rdx, rdi, 56
mov rcx, 0xffffffffffffff 
and r12, rcx
mov rbp, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, rdi, [ rax + 0x18 ]
mov rdx, r14
adox rdx, [ rsp + 0xf0 ]
adox r13, [ rsp + 0xe0 ]
adcx rdx, r11
mov r14, rbx
adcx r14, r13
mov r13, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x168 ], r12
mov [ rsp + 0x170 ], rbp
mulx rbp, r12, [ rax + 0x30 ]
xor rdx, rdx
adox r9, rdi
adox rcx, r15
mov rdx, [ rsi + 0x20 ]
mulx rdi, r15, [ rax + 0x0 ]
adcx r10, r11
adcx rbx, r8
mov rdx, 0x38 
bzhi r8, r9, rdx
adox r13, r12
mov r11, rbp
adox r11, r14
add r10, r12
adcx rbp, rbx
xor r14, r14
adox r13, [ rsp + 0x10 ]
adox r11, [ rsp + 0x8 ]
adcx r10, [ rsp + 0x10 ]
adcx rbp, [ rsp + 0x8 ]
mov r12, r15
xor rbx, rbx
adox r12, [ rsp + 0x138 ]
adox rdi, [ rsp + 0x148 ]
adcx r12, [ rsp + 0x20 ]
adcx rdi, [ rsp + 0x18 ]
mov rdx, [ rax + 0x10 ]
mulx r15, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x178 ], r8
mulx r8, rbx, [ rax + 0x18 ]
xor rdx, rdx
adox r12, r14
adox r15, rdi
mov rdi, [ rsp + 0xa0 ]
adcx rdi, [ rsp + 0xd0 ]
mov r14, [ rsp + 0x98 ]
adcx r14, [ rsp + 0xc8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x180 ], rbp
mov [ rsp + 0x188 ], r10
mulx r10, rbp, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x190 ], r10
mov [ rsp + 0x198 ], rbp
mulx rbp, r10, [ rax + 0x0 ]
mov rdx, r10
add rdx, [ rsp + 0x160 ]
adcx rbp, [ rsp + 0x158 ]
mov r10, rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x1a0 ], rbp
mov [ rsp + 0x1a8 ], r14
mulx r14, rbp, [ rsi + 0x18 ]
add r13, [ rsp - 0x40 ]
adcx r11, [ rsp - 0x48 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x1b0 ], r11
mov [ rsp + 0x1b8 ], r13
mulx r13, r11, [ rsi + 0x28 ]
xor rdx, rdx
adox r12, rbx
adox r8, r15
mov rdx, [ rsi + 0x0 ]
mulx r15, rbx, [ rax + 0x20 ]
adcx r12, rbx
adcx r15, r8
test al, al
adox rdi, rbp
mov rdx, r14
adox rdx, [ rsp + 0x1a8 ]
shrd r9, rcx, 56
xor rcx, rcx
adox r12, r9
adox r15, rcx
mov r8, rdx
mov rdx, [ rax + 0x10 ]
mulx r9, rbx, [ rsi + 0x20 ]
mov rdx, rbp
adcx rdx, [ rsp + 0xf8 ]
adcx r14, [ rsp + 0xe8 ]
mov rbp, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x1c0 ], r10
mulx r10, rcx, [ rsi + 0x18 ]
test al, al
adox rbp, [ rsp + 0x70 ]
adox r14, [ rsp + 0x68 ]
mov rdx, r12
adcx rdx, [ rsp + 0x170 ]
adc r15, 0x0
mov r12, rdx
shrd r12, r15, 56
test al, al
adox rbp, r11
adox r13, r14
mov r11, rdx
mov rdx, [ rsi + 0x18 ]
mulx r15, r14, [ rax + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x1c8 ], r12
mov [ rsp + 0x1d0 ], r8
mulx r8, r12, [ rax + 0x8 ]
mov rdx, 0xffffffffffffff 
and r11, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x1d8 ], r11
mov [ rsp + 0x1e0 ], rdi
mulx rdi, r11, [ rax + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x1e8 ], r15
mov [ rsp + 0x1f0 ], r14
mulx r14, r15, [ rax + 0x28 ]
mov rdx, r11
adox rdx, [ rsp + 0x188 ]
adox rdi, [ rsp + 0x180 ]
adcx rdx, [ rsp + 0x198 ]
adcx rdi, [ rsp + 0x190 ]
xor r11, r11
adox rdx, rbx
adox r9, rdi
adcx rbp, r12
adcx r8, r13
xor rbx, rbx
adox rbp, rcx
adox r10, r8
adcx rdx, [ rsp + 0x1f0 ]
adcx r9, [ rsp + 0x1e8 ]
mov r11, rdx
mov rdx, [ rsi + 0x10 ]
mulx r13, rcx, [ rax + 0x20 ]
xor rdx, rdx
adox r11, rcx
adox r13, r9
mov rdx, [ rax + 0x30 ]
mulx r12, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rdi, [ rax + 0x28 ]
adcx r11, r15
adcx r14, r13
mov rdx, [ rax + 0x18 ]
mulx r9, r15, [ rsi + 0x10 ]
test al, al
adox rbp, r15
adox r9, r10
mov rdx, [ rsi + 0x8 ]
mulx rcx, r10, [ rax + 0x20 ]
adcx rbp, r10
adcx rcx, r9
mov rdx, [ rsp + 0x70 ]
mov r13, rdx
add r13, [ rsp + 0x1e0 ]
mov r15, [ rsp + 0x68 ]
adcx r15, [ rsp + 0x1d0 ]
add r13, [ rsp + 0x80 ]
adcx r15, [ rsp + 0x78 ]
xor rdx, rdx
adox rbp, rdi
adox r8, rcx
adcx rbp, [ rsp + 0x1c8 ]
adc r8, 0x0
xor rdi, rdi
adox r11, rbx
adox r12, r14
mov rdx, rbp
shrd rdx, r8, 56
mov rbx, [ rsp + 0x1c0 ]
mov r14, rbx
test al, al
adox r14, [ rsp + 0x170 ]
mov r9, [ rsp + 0x1a0 ]
adox r9, rdi
adcx r11, rdx
adc r12, 0x0
mov rbx, 0xffffffffffffff 
and rbp, rbx
mov r10, r11
shrd r10, r12, 56
add r10, [ rsp + 0x168 ]
mov rcx, r10
and rcx, rbx
mov rdx, [ rax + 0x8 ]
mulx r12, r8, [ rsi + 0x8 ]
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x38 ], rcx
mov rcx, r8
adox rcx, [ rsp + 0x1b8 ]
adox r12, [ rsp + 0x1b0 ]
adcx rcx, [ rsp + 0x60 ]
adcx r12, [ rsp + 0x58 ]
shr r10, 56
mov r8, r14
shrd r8, r9, 56
xor r9, r9
adox r13, [ rsp + 0xb0 ]
adox r15, [ rsp + 0xa8 ]
adcx r13, r8
adc r15, 0x0
mov rdi, r13
shrd rdi, r15, 56
xor r8, r8
adox rcx, rdi
adox r12, r8
and r14, rbx
lea r14, [ r14 + r10 ]
mov r9, rcx
shrd r9, r12, 56
add r9, [ rsp + 0x178 ]
mov r15, r9
shr r15, 56
mov rdi, r14
shr rdi, 56
and r9, rbx
add r10, [ rsp + 0x1d8 ]
lea r15, [ r15 + r10 ]
mov r12, r15
shr r12, 56
and r15, rbx
and r11, rbx
and r14, rbx
mov [ rdx + 0x30 ], r11
mov [ rdx + 0x0 ], r14
mov [ rdx + 0x18 ], r9
lea r12, [ r12 + rbp ]
and rcx, rbx
mov [ rdx + 0x10 ], rcx
mov [ rdx + 0x28 ], r12
and r13, rbx
lea rdi, [ rdi + r13 ]
mov [ rdx + 0x8 ], rdi
mov [ rdx + 0x20 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 632
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.0090
; seed 2477751952128472 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4555516 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=78, initial num_batches=31): 108786 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.02388006100735899
; number reverted permutation / tried permutation: 58282 / 89769 =64.924%
; number reverted decision / tried decision: 41369 / 90230 =45.848%
; validated in 2.371s
