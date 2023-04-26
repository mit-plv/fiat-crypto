SECTION .text
	GLOBAL fiat_p448_solinas_carry_mul
fiat_p448_solinas_carry_mul:
sub rsp, 560
mov rax, rdx
mov rdx, [ rdx + 0x20 ]
mulx r11, r10, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x30 ]
mulx r8, rcx, [ rax + 0x10 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x38 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x38 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x48 ], r11
mov [ rsp - 0x40 ], r10
mulx r10, r11, [ rax + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x38 ], r12
mov [ rsp - 0x30 ], rbp
mulx rbp, r12, [ rax + 0x20 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x28 ], r8
mov [ rsp - 0x20 ], rcx
mulx rcx, r8, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], rcx
mov [ rsp - 0x10 ], r8
mulx r8, rcx, [ rax + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x8 ], r8
mov [ rsp + 0x0 ], rcx
mulx rcx, r8, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x8 ], rcx
mov [ rsp + 0x10 ], r8
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x18 ], r8
mov [ rsp + 0x20 ], rcx
mulx rcx, r8, [ rax + 0x8 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x28 ], rcx
mov [ rsp + 0x30 ], r8
mulx r8, rcx, [ rax + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x38 ], r10
mov [ rsp + 0x40 ], r11
mulx r11, r10, [ rsi + 0x8 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x48 ], r11
mov [ rsp + 0x50 ], r10
mulx r10, r11, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x58 ], rbp
mov [ rsp + 0x60 ], r12
mulx r12, rbp, [ rax + 0x38 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x68 ], r12
mov [ rsp + 0x70 ], rbp
mulx rbp, r12, [ rax + 0x28 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x78 ], rbp
mov [ rsp + 0x80 ], r12
mulx r12, rbp, [ rsi + 0x28 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x88 ], r12
mov [ rsp + 0x90 ], rbp
mulx rbp, r12, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x98 ], rbp
mov [ rsp + 0xa0 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0xa8 ], r12
mov [ rsp + 0xb0 ], rbp
mulx rbp, r12, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xb8 ], rbp
mov [ rsp + 0xc0 ], r12
mulx r12, rbp, [ rax + 0x28 ]
mov rdx, r13
add rdx, r9
mov [ rsp + 0xc8 ], r12
mov r12, rbx
adcx r12, r14
mov [ rsp + 0xd0 ], rbp
mov rbp, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xd8 ], r8
mov [ rsp + 0xe0 ], rcx
mulx rcx, r8, [ rsi + 0x30 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xe8 ], rdi
mov [ rsp + 0xf0 ], r15
mulx r15, rdi, [ rsi + 0x38 ]
mov rdx, r13
test al, al
adox rdx, r13
adox r14, r14
adcx rdi, r8
adcx rcx, r15
mov r13, rdx
mov rdx, [ rsi + 0x28 ]
mulx r15, r8, [ rax + 0x28 ]
add r13, r9
adcx rbx, r14
mov rdx, [ rax + 0x20 ]
mulx r14, r9, [ rsi + 0x30 ]
add rbp, r9
mov rdx, r14
adcx rdx, r12
test al, al
adox r13, r9
adox r14, rbx
adcx rbp, r8
mov r12, r15
adcx r12, rdx
mov rdx, [ rax + 0x30 ]
mulx r9, rbx, [ rsi + 0x38 ]
mov rdx, rbx
mov [ rsp + 0xf8 ], rcx
xor rcx, rcx
adox rdx, r11
mov [ rsp + 0x100 ], rdi
mov rdi, r10
adox rdi, r9
mov [ rsp + 0x108 ], r12
mov r12, rdx
adcx r12, rbx
adcx r9, rdi
xor rbx, rbx
adox r12, r11
adox r10, r9
adcx r13, r8
adcx r15, r14
mov rcx, rdx
mov rdx, [ rax + 0x30 ]
mulx r8, r11, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mulx r9, r14, [ rax + 0x28 ]
xor rdx, rdx
adox rbp, r11
mov rbx, r8
adox rbx, [ rsp + 0x108 ]
adcx r13, r11
adcx r8, r15
mov rdx, [ rax + 0x18 ]
mulx r11, r15, [ rsi + 0x30 ]
add r13, [ rsp + 0xf0 ]
adcx r8, [ rsp + 0xe8 ]
xor rdx, rdx
adox r12, [ rsp + 0xe0 ]
adox r10, [ rsp + 0xd8 ]
adcx r12, r15
mov [ rsp + 0x110 ], r9
mov r9, r11
adcx r9, r10
xor r10, r10
adox rcx, [ rsp + 0xe0 ]
adox rdi, [ rsp + 0xd8 ]
adcx rcx, r15
adcx r11, rdi
add rcx, [ rsp + 0x60 ]
adcx r11, [ rsp + 0x58 ]
mov rdx, [ rsi + 0x18 ]
mulx rdi, r15, [ rax + 0x30 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x118 ], r14
mulx r14, r10, [ rax + 0x30 ]
xor rdx, rdx
adox rcx, [ rsp + 0x40 ]
adox r11, [ rsp + 0x38 ]
adcx rcx, r15
mov [ rsp + 0x120 ], r8
mov r8, rdi
adcx r8, r11
xor r11, r11
adox r12, [ rsp + 0x60 ]
adox r9, [ rsp + 0x58 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x128 ], r13
mulx r13, r11, [ rax + 0x38 ]
adcx rbp, [ rsp + 0xf0 ]
adcx rbx, [ rsp + 0xe8 ]
test al, al
adox r12, [ rsp + 0x40 ]
adox r9, [ rsp + 0x38 ]
mov rdx, r10
adcx rdx, [ rsp + 0xd0 ]
mov [ rsp + 0x130 ], rbx
mov rbx, r14
adcx rbx, [ rsp + 0xc8 ]
test al, al
adox r12, r15
adox rdi, r9
adcx rdx, r11
mov r15, r13
adcx r15, rbx
mov r9, rdx
test al, al
adox r9, [ rsp - 0x10 ]
mov rbx, r15
adox rbx, [ rsp - 0x18 ]
adcx r9, [ rsp - 0x20 ]
adcx rbx, [ rsp - 0x28 ]
add rdx, [ rsp + 0xd0 ]
adcx r15, [ rsp + 0xc8 ]
mov [ rsp + 0x138 ], rbp
xor rbp, rbp
adox r9, [ rsp + 0x90 ]
adox rbx, [ rsp + 0x88 ]
adcx rcx, [ rsp + 0x70 ]
adcx r8, [ rsp + 0x68 ]
test al, al
adox rdx, r10
adox r14, r15
adcx rdx, r11
adcx r13, r14
add rdx, [ rsp - 0x10 ]
adcx r13, [ rsp - 0x18 ]
mov r10, rdx
mov rdx, [ rsi + 0x28 ]
mulx r15, r11, [ rax + 0x30 ]
mov rdx, r11
test al, al
adox rdx, [ rsp + 0x100 ]
adox r15, [ rsp + 0xf8 ]
mov r14, rdx
mov rdx, [ rsi + 0x20 ]
mulx rbp, r11, [ rax + 0x20 ]
adcx r9, r11
mov rdx, rbp
adcx rdx, rbx
mov rbx, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x140 ], r8
mov [ rsp + 0x148 ], rcx
mulx rcx, r8, [ rsi + 0x38 ]
xor rdx, rdx
adox r12, [ rsp + 0x70 ]
adox rdi, [ rsp + 0x68 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x150 ], rdi
mov [ rsp + 0x158 ], r12
mulx r12, rdi, [ rax + 0x28 ]
adcx r14, [ rsp + 0xa0 ]
adcx r15, [ rsp + 0x98 ]
add r9, rdi
mov rdx, r12
adcx rdx, rbx
add r10, [ rsp - 0x20 ]
adcx r13, [ rsp - 0x28 ]
test al, al
adox r10, [ rsp + 0x90 ]
adox r13, [ rsp + 0x88 ]
adcx r10, r11
adcx rbp, r13
add r10, rdi
adcx r12, rbp
mov r11, rdx
mov rdx, [ rsi + 0x20 ]
mulx rdi, rbx, [ rax + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mulx rbp, r13, [ rax + 0x30 ]
add r10, r13
mov rdx, rbp
adcx rdx, r12
add r10, [ rsp - 0x30 ]
adcx rdx, [ rsp - 0x38 ]
mov r12, r14
test al, al
adox r12, r8
adox rcx, r15
adcx r9, r13
adcx rbp, r11
test al, al
adox r12, [ rsp + 0xb0 ]
adox rcx, [ rsp + 0xa8 ]
adcx r10, rbx
adcx rdi, rdx
mov rdx, [ rax + 0x10 ]
mulx r11, r8, [ rsi + 0x28 ]
add r12, r8
adcx r11, rcx
test al, al
adox r12, [ rsp + 0x10 ]
adox r11, [ rsp + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mulx r13, rbx, [ rax + 0x0 ]
adcx r14, rbx
adcx r13, r15
mov rdx, [ rsi + 0x10 ]
mulx rcx, r15, [ rax + 0x28 ]
add r9, [ rsp - 0x30 ]
adcx rbp, [ rsp - 0x38 ]
mov rdx, [ rsi + 0x18 ]
mulx rbx, r8, [ rax + 0x8 ]
xor rdx, rdx
adox r12, [ rsp - 0x40 ]
adox r11, [ rsp - 0x48 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x160 ], rbp
mov [ rsp + 0x168 ], r9
mulx r9, rbp, [ rax + 0x30 ]
adcx r12, r15
adcx rcx, r11
mov rdx, [ rsi + 0x10 ]
mulx r11, r15, [ rax + 0x10 ]
test al, al
adox r12, rbp
adox r9, rcx
mov rdx, [ rsi + 0x10 ]
mulx rcx, rbp, [ rax + 0x8 ]
adcx r14, rbp
adcx rcx, r13
xor rdx, rdx
adox r10, r8
adox rbx, rdi
mov rdx, [ rax + 0x20 ]
mulx r13, rdi, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mulx rbp, r8, [ rsi + 0x8 ]
adcx r10, r15
adcx r11, rbx
add r14, r8
adcx rbp, rcx
mov rdx, [ rax + 0x18 ]
mulx rcx, r15, [ rsi + 0x0 ]
add r14, r15
adcx rcx, rbp
mov rdx, [ rax + 0x38 ]
mulx r8, rbx, [ rsi + 0x0 ]
mov rdx, r14
shrd rdx, rcx, 56
mov rbp, rdx
mov rdx, [ rax + 0x0 ]
mulx rcx, r15, [ rsi + 0x10 ]
add r12, rbx
adcx r8, r9
add r10, [ rsp + 0x50 ]
adcx r11, [ rsp + 0x48 ]
test al, al
adox r10, rdi
adox r13, r11
mov rdx, [ rax + 0x0 ]
mulx rdi, r9, [ rsi + 0x8 ]
mov rdx, r9
adcx rdx, [ rsp + 0x148 ]
adcx rdi, [ rsp + 0x140 ]
mov rbx, rdx
mov rdx, [ rax + 0x0 ]
mulx r9, r11, [ rsi + 0x0 ]
mov rdx, r15
add rdx, [ rsp + 0x138 ]
adcx rcx, [ rsp + 0x130 ]
xor r15, r15
adox rdx, [ rsp + 0xc0 ]
adox rcx, [ rsp + 0xb8 ]
mov [ rsp + 0x170 ], rcx
mov rcx, r11
adcx rcx, [ rsp + 0x168 ]
adcx r9, [ rsp + 0x160 ]
add r10, rbp
adc r13, 0x0
mov rbp, r12
shrd rbp, r8, 56
mov r8, rdx
mov rdx, [ rax + 0x8 ]
mulx r15, r11, [ rsi + 0x0 ]
mov rdx, rbp
add rdx, rcx
adc r9, 0x0
xor rcx, rcx
adox rbp, r10
adox r13, rcx
mov r10, rdx
shrd r10, r9, 56
mov r9, rbp
shrd r9, r13, 56
mov r13, 0xffffffffffffff 
and rbp, r13
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x178 ], rbp
mulx rbp, r13, [ rax + 0x10 ]
mov rdx, 0x38 
mov [ rsp + 0x180 ], r9
bzhi r9, rcx, rdx
adox rbx, r11
adox r15, rdi
mov rdx, [ rax + 0x0 ]
mulx r11, rdi, [ rsi + 0x30 ]
add rbx, r10
adc r15, 0x0
mov rdx, rbx
shrd rdx, r15, 56
mov rcx, rdi
xor r10, r10
adox rcx, [ rsp + 0x128 ]
adox r11, [ rsp + 0x120 ]
mov rdi, rdx
mov rdx, [ rax + 0x0 ]
mulx r10, r15, [ rsi + 0x28 ]
adcx r8, r13
adcx rbp, [ rsp + 0x170 ]
mov rdx, 0x38 
bzhi r13, rbx, rdx
adox rcx, [ rsp + 0x20 ]
adox r11, [ rsp + 0x18 ]
mov rbx, r15
test al, al
adox rbx, [ rsp + 0x158 ]
adox r10, [ rsp + 0x150 ]
adcx rbx, [ rsp + 0x30 ]
adcx r10, [ rsp + 0x28 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x188 ], r13
mulx r13, r15, [ rsi + 0x20 ]
xor rdx, rdx
adox rbx, [ rsp + 0x0 ]
adox r10, [ rsp - 0x8 ]
adcx rcx, r15
adcx r13, r11
mov rdx, [ rax + 0x20 ]
mulx r15, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x190 ], r9
mov [ rsp + 0x198 ], r15
mulx r15, r9, [ rax + 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x1a0 ], r11
mov [ rsp + 0x1a8 ], r13
mulx r13, r11, [ rsi + 0x18 ]
test al, al
adox rbx, r9
adox r15, r10
adcx r8, rdi
adc rbp, 0x0
mov rdx, r8
shrd rdx, rbp, 56
mov rdi, rdx
mov rdx, [ rax + 0x30 ]
mulx r9, r10, [ rsi + 0x0 ]
mov rdx, 0x38 
bzhi rbp, r14, rdx
bzhi r14, r8, rdx
lea rdi, [ rdi + rbp ]
bzhi r8, rdi, rdx
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x18 ], r8
shr rdi, 56
mov rdx, [ rsi + 0x8 ]
mulx rbp, r8, [ rax + 0x20 ]
add rbx, r8
adcx rbp, r15
add rcx, r11
adcx r13, [ rsp + 0x1a8 ]
test al, al
adox rbx, [ rsp + 0x80 ]
adox rbp, [ rsp + 0x78 ]
adcx rbx, [ rsp + 0x180 ]
adc rbp, 0x0
test al, al
adox rcx, [ rsp + 0x1a0 ]
adox r13, [ rsp + 0x198 ]
adcx rcx, [ rsp + 0x118 ]
adcx r13, [ rsp + 0x110 ]
mov rdx, 0x38 
bzhi r11, rbx, rdx
shrd rbx, rbp, 56
xor r15, r15
adox rcx, r10
adox r9, r13
adcx rcx, rbx
adc r9, 0x0
bzhi r10, r12, rdx
mov r12, rcx
shrd r12, r9, 56
lea r12, [ r12 + r10 ]
bzhi r8, r12, rdx
bzhi rbp, rcx, rdx
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x38 ], r8
shr r12, 56
mov rbx, r12
add rbx, [ rsp + 0x178 ]
lea rdi, [ rdi + rbx ]
mov rcx, rdi
shr rcx, 56
bzhi r9, rdi, rdx
add r12, [ rsp + 0x190 ]
mov r10, r12
shr r10, 56
mov [ r13 + 0x20 ], r9
bzhi r8, r12, rdx
add r10, [ rsp + 0x188 ]
mov [ r13 + 0x0 ], r8
lea rcx, [ rcx + r11 ]
mov [ r13 + 0x28 ], rcx
mov [ r13 + 0x10 ], r14
mov [ r13 + 0x8 ], r10
mov [ r13 + 0x30 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 560
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.2241
; seed 1642362508925318 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 9159825 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=60, initial num_batches=31): 206007 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.022490276833891477
; number reverted permutation / tried permutation: 64269 / 89986 =71.421%
; number reverted decision / tried decision: 51198 / 90013 =56.878%
; validated in 3.711s
