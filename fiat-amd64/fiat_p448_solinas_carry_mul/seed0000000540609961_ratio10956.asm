SECTION .text
	GLOBAL fiat_p448_solinas_carry_mul
fiat_p448_solinas_carry_mul:
sub rsp, 616
mov rax, rdx
mov rdx, [ rdx + 0x10 ]
mulx r11, r10, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x30 ]
mulx r8, rcx, [ rax + 0x30 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x30 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x38 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x20 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x48 ], rdi
mov [ rsp - 0x40 ], r15
mulx r15, rdi, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x38 ], r15
mov [ rsp - 0x30 ], rdi
mulx rdi, r15, [ rax + 0x38 ]
mov rdx, rbp
add rdx, rcx
mov [ rsp - 0x28 ], r11
mov r11, r8
adcx r11, r12
mov [ rsp - 0x20 ], r10
xor r10, r10
adox rdx, r15
mov [ rsp - 0x18 ], rbx
mov rbx, rdi
adox rbx, r11
mov r11, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x10 ], r9
mulx r9, r10, [ rax + 0x28 ]
mov rdx, r11
adcx rdx, rbp
adcx r12, rbx
add rdx, rcx
adcx r8, r12
mov rcx, rdx
mov rdx, [ rsi + 0x18 ]
mulx r12, rbp, [ rax + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x8 ], r12
mov [ rsp + 0x0 ], rbp
mulx rbp, r12, [ rsi + 0x38 ]
add r11, r12
mov rdx, rbp
adcx rdx, rbx
mov rbx, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x8 ], r9
mov [ rsp + 0x10 ], r10
mulx r10, r9, [ rax + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x18 ], r14
mov [ rsp + 0x20 ], r13
mulx r13, r14, [ rax + 0x8 ]
add rcx, r15
adcx rdi, r8
test al, al
adox rcx, r12
adox rbp, rdi
adcx rcx, r9
mov rdx, r10
adcx rdx, rbp
mov r15, rdx
mov rdx, [ rax + 0x18 ]
mulx r12, r8, [ rsi + 0x28 ]
test al, al
adox rcx, r8
mov rdx, r12
adox rdx, r15
adcx r11, r9
adcx r10, rbx
mov rbx, rdx
mov rdx, [ rax + 0x38 ]
mulx rdi, r9, [ rsi + 0x8 ]
test al, al
adox r11, r8
adox r12, r10
mov rdx, [ rsi + 0x18 ]
mulx r15, rbp, [ rax + 0x10 ]
mov rdx, [ rax + 0x20 ]
mulx r10, r8, [ rsi + 0x20 ]
adcx rcx, r8
mov rdx, r10
adcx rdx, rbx
test al, al
adox r11, r8
adox r10, r12
mov rbx, rdx
mov rdx, [ rax + 0x0 ]
mulx r8, r12, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x28 ], r15
mov [ rsp + 0x30 ], rbp
mulx rbp, r15, [ rax + 0x8 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x38 ], r13
mov [ rsp + 0x40 ], r14
mulx r14, r13, [ rax + 0x30 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x48 ], rbp
mov [ rsp + 0x50 ], r15
mulx r15, rbp, [ rax + 0x38 ]
mov rdx, r13
adcx rdx, rbp
mov [ rsp + 0x58 ], r8
mov r8, r15
adcx r8, r14
mov [ rsp + 0x60 ], r12
mov r12, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x68 ], rdi
mov [ rsp + 0x70 ], r9
mulx r9, rdi, [ rsi + 0x38 ]
mov rdx, r12
mov [ rsp + 0x78 ], rbx
xor rbx, rbx
adox rdx, r13
adox r14, r8
adcx rdx, rbp
adcx r15, r14
mov r13, rdx
mov rdx, [ rax + 0x18 ]
mulx r14, rbp, [ rsi + 0x10 ]
xor rdx, rdx
adox r13, rdi
mov rbx, r9
adox rbx, r15
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x80 ], r14
mulx r14, r15, [ rax + 0x28 ]
adcx r11, r15
mov rdx, r14
adcx rdx, r10
mov r10, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x88 ], rbp
mov [ rsp + 0x90 ], r11
mulx r11, rbp, [ rsi + 0x30 ]
xor rdx, rdx
adox rcx, r15
adox r14, [ rsp + 0x78 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x98 ], r10
mulx r10, r15, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xa0 ], r14
mov [ rsp + 0xa8 ], rcx
mulx rcx, r14, [ rax + 0x20 ]
adcx r12, rdi
adcx r9, r8
test al, al
adox r12, rbp
mov rdx, r11
adox rdx, r9
mov r8, rdx
mov rdx, [ rax + 0x30 ]
mulx r9, rdi, [ rsi + 0x18 ]
adcx r12, r14
mov rdx, rcx
adcx rdx, r8
test al, al
adox r13, rbp
adox r11, rbx
adcx r12, r15
mov rbx, r10
adcx rbx, rdx
xor rbp, rbp
adox r12, rdi
mov r8, r9
adox r8, rbx
adcx r13, r14
adcx rcx, r11
xor r14, r14
adox r13, r15
adox r10, rcx
mov rdx, [ rsi + 0x38 ]
mulx r15, rbp, [ rax + 0x38 ]
mov rdx, [ rax + 0x30 ]
mulx rbx, r11, [ rsi + 0x10 ]
mov rdx, r11
adcx rdx, [ rsp + 0xa8 ]
mov rcx, rbx
adcx rcx, [ rsp + 0xa0 ]
mov r14, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xb0 ], r8
mov [ rsp + 0xb8 ], r12
mulx r12, r8, [ rax + 0x38 ]
mov rdx, r11
test al, al
adox rdx, [ rsp + 0x90 ]
adox rbx, [ rsp + 0x98 ]
adcx rdx, [ rsp + 0x70 ]
adcx rbx, [ rsp + 0x68 ]
xor r11, r11
adox r13, rdi
adox r9, r10
mov rdi, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, rbp
adcx rdx, rbp
mov [ rsp + 0xc0 ], r9
mov r9, r15
adcx r9, r15
mov [ rsp + 0xc8 ], r13
mov r13, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xd0 ], r12
mov [ rsp + 0xd8 ], r8
mulx r8, r12, [ rsi + 0x38 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0xe0 ], r9
mov [ rsp + 0xe8 ], r13
mulx r13, r9, [ rsi + 0x10 ]
test al, al
adox r14, [ rsp + 0x70 ]
adox rcx, [ rsp + 0x68 ]
adcx rdi, r10
adcx r11, rbx
mov rdx, [ rsi + 0x8 ]
mulx r10, rbx, [ rax + 0x10 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xf0 ], r11
mov [ rsp + 0xf8 ], rdi
mulx rdi, r11, [ rsi + 0x30 ]
xor rdx, rdx
adox r12, r11
adox rdi, r8
mov rdx, [ rax + 0x38 ]
mulx r11, r8, [ rsi + 0x20 ]
adcx r14, [ rsp + 0x20 ]
adcx rcx, [ rsp + 0x18 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x100 ], rcx
mov [ rsp + 0x108 ], r14
mulx r14, rcx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x110 ], r10
mov [ rsp + 0x118 ], rbx
mulx rbx, r10, [ rax + 0x18 ]
test al, al
adox r12, rcx
adox r14, rdi
mov rdx, r10
adcx rdx, [ rsp + 0xe8 ]
mov rdi, rbx
adcx rdi, [ rsp + 0xe0 ]
xor rcx, rcx
adox r12, r8
adox r11, r14
mov r8, rdx
mov rdx, [ rax + 0x0 ]
mulx rcx, r14, [ rsi + 0x18 ]
mov rdx, r12
adcx rdx, r14
adcx rcx, r11
test al, al
adox rdx, r9
adox r13, rcx
adcx rdx, [ rsp + 0x118 ]
adcx r13, [ rsp + 0x110 ]
mov r9, rdx
mov rdx, [ rsi + 0x38 ]
mulx rcx, r14, [ rax + 0x0 ]
xor rdx, rdx
adox r12, r14
adox rcx, r11
mov rdx, [ rsi + 0x0 ]
mulx r14, r11, [ rax + 0x18 ]
adcx rbp, r10
adcx rbx, r15
test al, al
adox r12, [ rsp - 0x10 ]
adox rcx, [ rsp - 0x18 ]
mov rdx, [ rsi + 0x18 ]
mulx r10, r15, [ rax + 0x20 ]
adcx r9, r11
adcx r14, r13
mov rdx, [ rsp + 0xd8 ]
mov r13, rdx
xor r11, r11
adox r13, [ rsp + 0xb8 ]
mov [ rsp + 0x120 ], rbx
mov rbx, [ rsp + 0xd0 ]
mov [ rsp + 0x128 ], rbp
mov rbp, rbx
adox rbp, [ rsp + 0xb0 ]
mov r11, r9
shrd r11, r14, 56
mov r14, rdx
mov [ rsp + 0x130 ], r11
xor r11, r11
adox r14, [ rsp + 0xc8 ]
adox rbx, [ rsp + 0xc0 ]
adcx r12, [ rsp - 0x20 ]
adcx rcx, [ rsp - 0x28 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x138 ], rbx
mulx rbx, r11, [ rsi + 0x20 ]
xor rdx, rdx
adox r12, r11
adox rbx, rcx
mov rdx, [ rsi + 0x0 ]
mulx r11, rcx, [ rax + 0x38 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x140 ], r14
mov [ rsp + 0x148 ], rdi
mulx rdi, r14, [ rax + 0x10 ]
mov rdx, 0x38 
mov [ rsp + 0x150 ], rdi
bzhi rdi, r9, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x158 ], rdi
mulx rdi, r9, [ rax + 0x20 ]
adox r13, [ rsp + 0x60 ]
adox rbp, [ rsp + 0x58 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x160 ], rbp
mov [ rsp + 0x168 ], r13
mulx r13, rbp, [ rax + 0x28 ]
add r12, r15
adcx r10, rbx
xor rdx, rdx
adox r12, rbp
adox r13, r10
mov rdx, [ rax + 0x30 ]
mulx rbx, r15, [ rsi + 0x8 ]
adcx r12, r15
adcx rbx, r13
add r12, rcx
adcx r11, rbx
mov rdx, r12
shrd rdx, r11, 56
mov rcx, rdx
mov rdx, [ rax + 0x0 ]
mulx r10, rbp, [ rsi + 0x10 ]
mov rdx, rcx
test al, al
adox rdx, [ rsp + 0xf8 ]
mov r13, [ rsp + 0xf0 ]
mov r15, 0x0 
adox r13, r15
adcx r8, r9
mov rbx, rdi
adcx rbx, [ rsp + 0x148 ]
mov r11, rdx
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x170 ], r10
mulx r10, r15, [ rsi + 0x18 ]
add r8, [ rsp + 0x10 ]
adcx rbx, [ rsp + 0x8 ]
mov rdx, 0xffffffffffffff 
and r12, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x178 ], r12
mov [ rsp + 0x180 ], rbp
mulx rbp, r12, [ rax + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x188 ], rbp
mov [ rsp + 0x190 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, r11
shrd rdx, r13, 56
mov r13, rbp
add r13, [ rsp + 0x108 ]
adcx r12, [ rsp + 0x100 ]
mov rbp, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x198 ], rbx
mov [ rsp + 0x1a0 ], r8
mulx r8, rbx, [ rsi + 0x0 ]
xor rdx, rdx
adox r13, r14
adox r12, [ rsp + 0x150 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x1a8 ], rbp
mulx rbp, r14, [ rax + 0x18 ]
adcx r13, r14
adcx rbp, r12
mov rdx, r9
add rdx, [ rsp + 0x128 ]
adcx rdi, [ rsp + 0x120 ]
xor r9, r9
adox rdx, [ rsp + 0x10 ]
adox rdi, [ rsp + 0x8 ]
adcx rdx, [ rsp - 0x30 ]
adcx rdi, [ rsp - 0x38 ]
xor r12, r12
adox rdx, r15
mov r9, r10
adox r9, rdi
adcx r13, rbx
adcx r8, rbp
mov rbx, [ rsp + 0x1a0 ]
xor r14, r14
adox rbx, [ rsp - 0x30 ]
mov r12, [ rsp + 0x198 ]
adox r12, [ rsp - 0x38 ]
adcx rdx, [ rsp + 0x180 ]
adcx r9, [ rsp + 0x170 ]
add rbx, r15
adcx r10, r12
mov r15, rdx
mov rdx, [ rsi + 0x30 ]
mulx rdi, rbp, [ rax + 0x0 ]
add rbx, rbp
adcx rdi, r10
mov rdx, [ rsi + 0x0 ]
mulx r10, r12, [ rax + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mulx r14, rbp, [ rax + 0x8 ]
xor rdx, rdx
adox rbx, [ rsp + 0x50 ]
adox rdi, [ rsp + 0x48 ]
adcx r15, [ rsp + 0x190 ]
adcx r9, [ rsp + 0x188 ]
test al, al
adox r15, r12
adox r10, r9
mov r12, rbp
adcx r12, [ rsp + 0x168 ]
adcx r14, [ rsp + 0x160 ]
test al, al
adox r12, [ rsp + 0x1a8 ]
adox r14, rdx
adcx r13, [ rsp + 0x130 ]
adc r8, 0x0
mov rdx, [ rax + 0x20 ]
mulx r9, rbp, [ rsi + 0x8 ]
add rcx, r13
adc r8, 0x0
mov rdx, r12
shrd rdx, r14, 56
mov r14, 0x38 
bzhi r13, rcx, r14
mov r14, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x1b0 ], r13
mov [ rsp + 0x1b8 ], r9
mulx r9, r13, [ rsi + 0x8 ]
adox r15, r14
mov rdx, 0x0 
adox r10, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x1c0 ], r9
mulx r9, r14, [ rax + 0x0 ]
mov rdx, r14
test al, al
adox rdx, [ rsp + 0x140 ]
adox r9, [ rsp + 0x138 ]
mov r14, r15
shrd r14, r10, 56
xor r10, r10
adox rdx, [ rsp + 0x40 ]
adox r9, [ rsp + 0x38 ]
mov r10, rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x1c8 ], r14
mov [ rsp + 0x1d0 ], r13
mulx r13, r14, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x1d8 ], r13
mov [ rsp + 0x1e0 ], r14
mulx r14, r13, [ rsi + 0x20 ]
adcx rbx, r13
adcx r14, rdi
xor rdx, rdx
adox r10, [ rsp + 0x30 ]
adox r9, [ rsp + 0x28 ]
adcx r10, [ rsp + 0x88 ]
adcx r9, [ rsp + 0x80 ]
test al, al
adox r10, rbp
adox r9, [ rsp + 0x1b8 ]
mov rdi, 0xffffffffffffff 
and r12, rdi
adox rbx, [ rsp + 0x0 ]
adox r14, [ rsp - 0x8 ]
adcx rbx, [ rsp - 0x40 ]
adcx r14, [ rsp - 0x48 ]
shrd rcx, r8, 56
test al, al
adox rbx, [ rsp + 0x1d0 ]
adox r14, [ rsp + 0x1c0 ]
adcx rbx, [ rsp + 0x1e0 ]
adcx r14, [ rsp + 0x1d8 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rbp, [ rax + 0x28 ]
xor rdx, rdx
adox r10, rbp
adox r8, r9
adcx r10, rcx
adc r8, 0x0
mov r13, r10
shrd r13, r8, 56
and r10, rdi
adox rbx, r13
adox r14, rdx
mov r9, rbx
and r9, rdi
shrd rbx, r14, 56
add rbx, [ rsp + 0x178 ]
mov rcx, [ rsp + 0x1c8 ]
add rcx, [ rsp + 0x158 ]
mov rbp, rcx
and rbp, rdi
and r11, rdi
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x18 ], rbp
mov r13, rbx
and r13, rdi
shr rbx, 56
mov [ r8 + 0x30 ], r9
mov r14, rbx
add r14, [ rsp + 0x1b0 ]
shr rcx, 56
lea rcx, [ rcx + r14 ]
lea r11, [ r11 + rbx ]
mov r9, r11
and r9, rdi
mov rbp, rcx
and rbp, rdi
mov [ r8 + 0x0 ], r9
shr rcx, 56
lea rcx, [ rcx + r10 ]
and r15, rdi
mov [ r8 + 0x20 ], rbp
shr r11, 56
lea r11, [ r11 + r12 ]
mov [ r8 + 0x28 ], rcx
mov [ r8 + 0x10 ], r15
mov [ r8 + 0x38 ], r13
mov [ r8 + 0x8 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 616
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.0956
; seed 0857726244457124 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5239474 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=86, initial num_batches=31): 142514 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.02720005863183976
; number reverted permutation / tried permutation: 58775 / 89873 =65.398%
; number reverted decision / tried decision: 33408 / 90126 =37.068%
; validated in 3.688s
