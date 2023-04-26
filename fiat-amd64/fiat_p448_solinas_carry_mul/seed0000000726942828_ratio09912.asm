SECTION .text
	GLOBAL fiat_p448_solinas_carry_mul
fiat_p448_solinas_carry_mul:
sub rsp, 680
mov rax, rdx
mov rdx, [ rsi + 0x28 ]
mulx r11, r10, [ rax + 0x38 ]
mov rdx, [ rax + 0x30 ]
mulx r8, rcx, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x38 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x0 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x48 ], r14
mov [ rsp - 0x40 ], r13
mulx r13, r14, [ rax + 0x38 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], r13
mov [ rsp - 0x30 ], r14
mulx r14, r13, [ rax + 0x0 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x28 ], r14
mov [ rsp - 0x20 ], r13
mulx r13, r14, [ rsi + 0x38 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x18 ], r11
mov [ rsp - 0x10 ], r10
mulx r10, r11, [ rsi + 0x20 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x8 ], r10
mov [ rsp + 0x0 ], r11
mulx r11, r10, [ rsi + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x8 ], r11
mov [ rsp + 0x10 ], r10
mulx r10, r11, [ rsi + 0x38 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x18 ], r10
mov [ rsp + 0x20 ], r11
mulx r11, r10, [ rsi + 0x18 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x28 ], r11
mov [ rsp + 0x30 ], r10
mulx r10, r11, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x38 ], r10
mov [ rsp + 0x40 ], r11
mulx r11, r10, [ rax + 0x30 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x48 ], r11
mov [ rsp + 0x50 ], r10
mulx r10, r11, [ rax + 0x28 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x58 ], r10
mov [ rsp + 0x60 ], r11
mulx r11, r10, [ rsi + 0x30 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x68 ], r11
mov [ rsp + 0x70 ], r10
mulx r10, r11, [ rsi + 0x28 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x78 ], r10
mov [ rsp + 0x80 ], r11
mulx r11, r10, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x88 ], r11
mov [ rsp + 0x90 ], r10
mulx r10, r11, [ rax + 0x0 ]
mov rdx, r9
add rdx, r9
mov [ rsp + 0x98 ], r10
mov r10, rbx
adcx r10, rbx
mov [ rsp + 0xa0 ], r11
mov r11, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xa8 ], r13
mov [ rsp + 0xb0 ], r14
mulx r14, r13, [ rax + 0x0 ]
test al, al
adox r9, rbp
mov rdx, r12
adox rdx, rbx
adcx r11, rbp
adcx r12, r10
mov rbx, rdx
mov rdx, [ rsi + 0x8 ]
mulx r10, rbp, [ rax + 0x0 ]
xor rdx, rdx
adox r11, r15
mov [ rsp + 0xb8 ], r14
mov r14, rdi
adox r14, r12
mov r12, rcx
adcx r12, [ rsp + 0xb0 ]
mov [ rsp + 0xc0 ], r13
mov r13, r8
adcx r13, [ rsp + 0xa8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xc8 ], r10
mov [ rsp + 0xd0 ], rbp
mulx rbp, r10, [ rax + 0x28 ]
xor rdx, rdx
adox r12, [ rsp - 0x10 ]
adox r13, [ rsp - 0x18 ]
mov [ rsp + 0xd8 ], rbp
mov rbp, r12
adcx rbp, [ rsp + 0xb0 ]
mov [ rsp + 0xe0 ], r10
mov r10, r13
adcx r10, [ rsp + 0xa8 ]
mov [ rsp + 0xe8 ], r14
xor r14, r14
adox rbp, rcx
adox r8, r10
mov rdx, [ rsi + 0x28 ]
mulx r10, rcx, [ rax + 0x18 ]
adcx rbp, [ rsp - 0x10 ]
adcx r8, [ rsp - 0x18 ]
test al, al
adox r9, r15
adox rdi, rbx
mov rdx, [ rsi + 0x0 ]
mulx rbx, r15, [ rax + 0x30 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xf0 ], rbx
mulx rbx, r14, [ rax + 0x8 ]
adcx r12, r14
mov rdx, rbx
adcx rdx, r13
test al, al
adox r12, [ rsp + 0x70 ]
adox rdx, [ rsp + 0x68 ]
mov r13, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0xf8 ], r15
mov [ rsp + 0x100 ], rdi
mulx rdi, r15, [ rsi + 0x28 ]
adcx r12, rcx
mov rdx, r10
adcx rdx, r13
xor r13, r13
adox rbp, r14
adox rbx, r8
adcx rbp, [ rsp + 0x70 ]
adcx rbx, [ rsp + 0x68 ]
add rbp, rcx
adcx r10, rbx
xor rcx, rcx
adox r12, [ rsp + 0x0 ]
adox rdx, [ rsp - 0x8 ]
mov r13, rdx
mov rdx, [ rax + 0x28 ]
mulx r14, r8, [ rsi + 0x18 ]
mov rdx, [ rax + 0x30 ]
mulx rcx, rbx, [ rsi + 0x10 ]
adcx rbp, [ rsp + 0x0 ]
adcx r10, [ rsp - 0x8 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x108 ], rdi
mov [ rsp + 0x110 ], r15
mulx r15, rdi, [ rsi + 0x8 ]
test al, al
adox rbp, r8
mov rdx, r14
adox rdx, r10
adcx r12, r8
adcx r14, r13
xor r13, r13
adox r12, rbx
mov r8, rcx
adox r8, r14
mov r10, rdx
mov rdx, [ rsi + 0x30 ]
mulx r13, r14, [ rax + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x118 ], r9
mov [ rsp + 0x120 ], r11
mulx r11, r9, [ rax + 0x0 ]
mov rdx, r14
adcx rdx, [ rsp + 0x20 ]
adcx r13, [ rsp + 0x18 ]
add r12, rdi
mov r14, r15
adcx r14, r8
mov r8, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x128 ], r14
mov [ rsp + 0x130 ], r12
mulx r12, r14, [ rax + 0x30 ]
add r8, r14
adcx r12, r13
test al, al
adox rbp, rbx
adox rcx, r10
mov rdx, [ rsi + 0x20 ]
mulx r10, rbx, [ rax + 0x0 ]
mov rdx, [ rax + 0x38 ]
mulx r14, r13, [ rsi + 0x20 ]
adcx r8, r13
adcx r14, r12
mov rdx, r8
add rdx, [ rsp - 0x20 ]
mov r12, r14
adcx r12, [ rsp - 0x28 ]
mov r13, r9
test al, al
adox r13, [ rsp + 0x130 ]
adox r11, [ rsp + 0x128 ]
adcx rbp, rdi
adcx r15, rcx
mov rdi, rdx
mov rdx, [ rsi + 0x38 ]
mulx rcx, r9, [ rax + 0x30 ]
xor rdx, rdx
adox rbp, rbx
adox r10, r15
mov rdx, [ rsi + 0x38 ]
mulx r15, rbx, [ rax + 0x0 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x138 ], r11
mov [ rsp + 0x140 ], r13
mulx r13, r11, [ rax + 0x8 ]
adcx r8, rbx
adcx r15, r14
xor rdx, rdx
adox r8, r11
adox r13, r15
mov r14, r9
adcx r14, [ rsp - 0x30 ]
mov rbx, rcx
adcx rbx, [ rsp - 0x38 ]
mov r11, r14
test al, al
adox r11, r9
adox rcx, rbx
mov rdx, [ rsi + 0x38 ]
mulx r15, r9, [ rax + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x148 ], r10
mov [ rsp + 0x150 ], rbp
mulx rbp, r10, [ rax + 0x28 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x158 ], r13
mov [ rsp + 0x160 ], r8
mulx r8, r13, [ rsi + 0x30 ]
adcx r11, [ rsp - 0x30 ]
adcx rcx, [ rsp - 0x38 ]
mov rdx, r10
test al, al
adox rdx, [ rsp + 0x120 ]
mov [ rsp + 0x168 ], r8
mov r8, rbp
adox r8, [ rsp + 0xe8 ]
adcx r11, r9
mov [ rsp + 0x170 ], r13
mov r13, r15
adcx r13, rcx
test al, al
adox r14, r9
adox r15, rbx
mov rbx, rdx
mov rdx, [ rax + 0x30 ]
mulx rcx, r9, [ rsi + 0x20 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x178 ], r15
mov [ rsp + 0x180 ], r14
mulx r14, r15, [ rsi + 0x10 ]
mov rdx, r10
adcx rdx, [ rsp + 0x118 ]
adcx rbp, [ rsp + 0x100 ]
test al, al
adox rdi, r15
adox r14, r12
mov r12, rdx
mov rdx, [ rsi + 0x28 ]
mulx r15, r10, [ rax + 0x10 ]
adcx r12, r9
mov rdx, rcx
adcx rdx, rbp
add rbx, r9
adcx rcx, r8
mov r8, rdx
mov rdx, [ rax + 0x10 ]
mulx rbp, r9, [ rsi + 0x8 ]
add rdi, r9
adcx rbp, r14
test al, al
adox rbx, [ rsp + 0x10 ]
adox rcx, [ rsp + 0x8 ]
adcx r12, [ rsp + 0x10 ]
adcx r8, [ rsp + 0x8 ]
xor rdx, rdx
adox rdi, [ rsp - 0x40 ]
adox rbp, [ rsp - 0x48 ]
mov rdx, [ rsi + 0x20 ]
mulx r9, r14, [ rax + 0x18 ]
mov rdx, r10
adcx rdx, [ rsp + 0x160 ]
adcx r15, [ rsp + 0x158 ]
mov r10, 0x38 
mov [ rsp + 0x188 ], r8
bzhi r8, rdi, r10
mov r10, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x190 ], r8
mov [ rsp + 0x198 ], r12
mulx r12, r8, [ rax + 0x20 ]
adox r10, r14
adox r9, r15
xor rdx, rdx
adox r10, r8
adox r12, r9
adcx r11, [ rsp + 0x170 ]
adcx r13, [ rsp + 0x168 ]
mov rdx, [ rsi + 0x8 ]
mulx r15, r14, [ rax + 0x30 ]
add r11, [ rsp + 0x80 ]
adcx r13, [ rsp + 0x78 ]
xor rdx, rdx
adox r11, [ rsp + 0x40 ]
adox r13, [ rsp + 0x38 ]
adcx r11, [ rsp + 0x50 ]
adcx r13, [ rsp + 0x48 ]
mov rdx, [ rax + 0x38 ]
mulx r9, r8, [ rsi + 0x10 ]
test al, al
adox r10, [ rsp + 0x60 ]
adox r12, [ rsp + 0x58 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x1a0 ], rcx
mov [ rsp + 0x1a8 ], rbx
mulx rbx, rcx, [ rsi + 0x10 ]
adcx r10, r14
adcx r15, r12
mov rdx, [ rax + 0x8 ]
mulx r12, r14, [ rsi + 0x18 ]
mov rdx, r14
mov [ rsp + 0x1b0 ], rbx
xor rbx, rbx
adox rdx, [ rsp + 0x150 ]
adox r12, [ rsp + 0x148 ]
mov r14, rdx
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x1b8 ], rcx
mulx rcx, rbx, [ rsi + 0x0 ]
adcx r10, rbx
adcx rcx, r15
mov rdx, [ rsi + 0x10 ]
mulx rbx, r15, [ rax + 0x10 ]
xor rdx, rdx
adox r11, r8
mov [ rsp + 0x1c0 ], r12
mov r12, r9
adox r12, r13
mov r13, r10
shrd r13, rcx, 56
add r14, r15
adcx rbx, [ rsp + 0x1c0 ]
mov rcx, [ rsp + 0x170 ]
mov r15, rcx
mov [ rsp + 0x1c8 ], r13
xor r13, r13
adox r15, [ rsp + 0x180 ]
mov rdx, [ rsp + 0x168 ]
adox rdx, [ rsp + 0x178 ]
adcx r15, [ rsp + 0x80 ]
adcx rdx, [ rsp + 0x78 ]
mov rcx, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x1d0 ], rbx
mulx rbx, r13, [ rsi + 0x20 ]
xor rdx, rdx
adox r15, [ rsp + 0x40 ]
adox rcx, [ rsp + 0x38 ]
shrd rdi, rbp, 56
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x1d8 ], rdi
mulx rdi, rbp, [ rsi + 0x0 ]
add r11, [ rsp + 0xa0 ]
adcx r12, [ rsp + 0x98 ]
test al, al
adox r11, r13
adox rbx, r12
mov rdx, [ rax + 0x18 ]
mulx r12, r13, [ rsi + 0x18 ]
adcx r11, [ rsp + 0x30 ]
adcx rbx, [ rsp + 0x28 ]
xor rdx, rdx
adox r14, [ rsp + 0x90 ]
mov [ rsp + 0x1e0 ], r12
mov r12, [ rsp + 0x88 ]
adox r12, [ rsp + 0x1d0 ]
adcx r15, [ rsp + 0x50 ]
adcx rcx, [ rsp + 0x48 ]
test al, al
adox r14, rbp
adox rdi, r12
adcx r14, [ rsp + 0x1d8 ]
adc rdi, 0x0
xor rbp, rbp
adox r15, r8
adox r9, rcx
mov rdx, [ rsi + 0x10 ]
mulx r12, r8, [ rax + 0x0 ]
mov rdx, r14
adcx rdx, [ rsp + 0x1c8 ]
adc rdi, 0x0
test al, al
adox r15, [ rsp + 0xd0 ]
adox r9, [ rsp + 0xc8 ]
mov rcx, 0x38 
bzhi r14, rdx, rcx
mov rbp, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x1e8 ], r9
mulx r9, rcx, [ rsi + 0x8 ]
shrd rbp, rdi, 56
add r11, [ rsp + 0x1b8 ]
adcx rbx, [ rsp + 0x1b0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x1f0 ], r15
mulx r15, rdi, [ rax + 0x28 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x1f8 ], r9
mov [ rsp + 0x200 ], rcx
mulx rcx, r9, [ rsi + 0x20 ]
mov rdx, [ rsp + 0xc0 ]
mov [ rsp + 0x208 ], r14
mov r14, rdx
mov [ rsp + 0x210 ], rbp
xor rbp, rbp
adox r14, [ rsp + 0x1a8 ]
mov [ rsp + 0x218 ], r15
mov r15, [ rsp + 0xb8 ]
adox r15, [ rsp + 0x1a0 ]
adcx r14, [ rsp + 0x110 ]
adcx r15, [ rsp + 0x108 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x220 ], rdi
mulx rdi, rbp, [ rsi + 0x10 ]
xor rdx, rdx
adox r14, r9
adox rcx, r15
adcx r14, r13
adcx rcx, [ rsp + 0x1e0 ]
mov r13, r8
xor r9, r9
adox r13, [ rsp + 0x198 ]
adox r12, [ rsp + 0x188 ]
mov rdx, [ rax + 0x20 ]
mulx r15, r8, [ rsi + 0x8 ]
adcx r11, r8
adcx r15, rbx
mov rdx, [ rsp + 0x140 ]
mov rbx, rdx
xor r8, r8
adox rbx, [ rsp + 0x1c8 ]
mov r9, [ rsp + 0x138 ]
adox r9, r8
adcx r11, [ rsp + 0x220 ]
adcx r15, [ rsp + 0x218 ]
test al, al
adox r11, [ rsp + 0x210 ]
adox r15, r8
adcx r14, rbp
adcx rdi, rcx
add r14, [ rsp + 0xe0 ]
adcx rdi, [ rsp + 0xd8 ]
xor rdx, rdx
adox r14, [ rsp + 0xf8 ]
adox rdi, [ rsp + 0xf0 ]
mov r8, r11
shrd r8, r15, 56
mov rbp, rbx
shrd rbp, r9, 56
mov rcx, 0xffffffffffffff 
and r10, rcx
adox r14, r8
adox rdi, rdx
mov r9, r14
shrd r9, rdi, 56
lea r9, [ r9 + r10 ]
and r11, rcx
mov r15, r9
shr r15, 56
and rbx, rcx
and r14, rcx
and r9, rcx
lea rbx, [ rbx + r15 ]
mov rdx, [ rsi + 0x0 ]
mulx r10, r8, [ rax + 0x8 ]
add r15, [ rsp + 0x208 ]
mov rdx, [ rax + 0x10 ]
mulx rcx, rdi, [ rsi + 0x0 ]
test al, al
adox r13, [ rsp + 0x200 ]
adox r12, [ rsp + 0x1f8 ]
mov rdx, r8
adcx rdx, [ rsp + 0x1f0 ]
adcx r10, [ rsp + 0x1e8 ]
xor r8, r8
adox rdx, rbp
adox r10, r8
adcx r13, rdi
adcx rcx, r12
mov rbp, rdx
shrd rbp, r10, 56
test al, al
adox r13, rbp
adox rcx, r8
mov rdi, r13
shrd rdi, rcx, 56
add rdi, [ rsp + 0x190 ]
mov r12, rdi
shr r12, 56
lea r12, [ r12 + r15 ]
mov r15, rbx
shr r15, 56
mov r10, 0xffffffffffffff 
mov rbp, r12
and rbp, r10
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x20 ], rbp
and rdx, r10
shr r12, 56
and rbx, r10
lea r12, [ r12 + r11 ]
mov [ rcx + 0x28 ], r12
mov [ rcx + 0x0 ], rbx
and rdi, r10
mov [ rcx + 0x38 ], r9
mov [ rcx + 0x18 ], rdi
and r13, r10
mov [ rcx + 0x10 ], r13
mov [ rcx + 0x30 ], r14
lea r15, [ r15 + rdx ]
mov [ rcx + 0x8 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 680
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 0.9912
; seed 1198338359697364 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4455242 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=77, initial num_batches=31): 108094 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.024262206183188254
; number reverted permutation / tried permutation: 57843 / 89774 =64.432%
; number reverted decision / tried decision: 40832 / 90225 =45.256%
; validated in 2.76s
