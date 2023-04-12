SECTION .text
	GLOBAL fiat_p448_solinas_carry_mul
fiat_p448_solinas_carry_mul:
sub rsp, 608
mov rax, rdx
mov rdx, [ rsi + 0x38 ]
mulx r11, r10, [ rax + 0x20 ]
mov rdx, [ rsi + 0x38 ]
mulx r8, rcx, [ rax + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x38 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x28 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x30 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x48 ], r12
mov [ rsp - 0x40 ], rbp
mulx rbp, r12, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x38 ], rbx
mov [ rsp - 0x30 ], r9
mulx r9, rbx, [ rax + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x28 ], r8
mov [ rsp - 0x20 ], rcx
mulx rcx, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], rcx
mov [ rsp - 0x10 ], r8
mulx r8, rcx, [ rax + 0x10 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x8 ], r8
mov [ rsp + 0x0 ], rcx
mulx rcx, r8, [ rsi + 0x30 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x8 ], r14
mov [ rsp + 0x10 ], r13
mulx r13, r14, [ rsi + 0x28 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x18 ], r13
mov [ rsp + 0x20 ], r14
mulx r14, r13, [ rsi + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x28 ], r14
mov [ rsp + 0x30 ], r13
mulx r13, r14, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x38 ], r13
mov [ rsp + 0x40 ], r14
mulx r14, r13, [ rax + 0x18 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x48 ], r14
mov [ rsp + 0x50 ], r13
mulx r13, r14, [ rax + 0x8 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x58 ], r13
mov [ rsp + 0x60 ], r14
mulx r14, r13, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x68 ], rbp
mov [ rsp + 0x70 ], r12
mulx r12, rbp, [ rax + 0x0 ]
mov rdx, r13
add rdx, r13
mov [ rsp + 0x78 ], r12
mov r12, r14
adcx r12, r14
mov [ rsp + 0x80 ], rbp
xor rbp, rbp
adox r13, rbx
mov [ rsp + 0x88 ], rdi
mov rdi, r9
adox rdi, r14
mov r14, rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x90 ], rdi
mulx rdi, rbp, [ rsi + 0x10 ]
adcx r14, rbx
adcx r9, r12
mov rdx, [ rsi + 0x18 ]
mulx r12, rbx, [ rax + 0x38 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x98 ], r12
mov [ rsp + 0xa0 ], rbx
mulx rbx, r12, [ rax + 0x28 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xa8 ], rdi
mov [ rsp + 0xb0 ], rbp
mulx rbp, rdi, [ rax + 0x38 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0xb8 ], rbp
mov [ rsp + 0xc0 ], rdi
mulx rdi, rbp, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xc8 ], rdi
mov [ rsp + 0xd0 ], rbp
mulx rbp, rdi, [ rax + 0x30 ]
test al, al
adox r10, r8
adox rcx, r11
mov rdx, r12
adcx rdx, r15
mov r11, rbx
adcx r11, [ rsp + 0x88 ]
add rdx, [ rsp + 0x70 ]
adcx r11, [ rsp + 0x68 ]
mov r8, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xd8 ], rcx
mov [ rsp + 0xe0 ], r10
mulx r10, rcx, [ rsi + 0x30 ]
mov rdx, r8
mov [ rsp + 0xe8 ], rbp
xor rbp, rbp
adox rdx, r12
adox rbx, r11
adcx rdx, r15
adcx rbx, [ rsp + 0x88 ]
xor r15, r15
adox rdx, [ rsp + 0x70 ]
adox rbx, [ rsp + 0x68 ]
adcx r13, rcx
mov rbp, r10
adcx rbp, [ rsp + 0x90 ]
test al, al
adox r14, rcx
adox r10, r9
mov r9, rdx
mov rdx, [ rsi + 0x38 ]
mulx rcx, r12, [ rax + 0x8 ]
adcx r9, r12
mov rdx, rcx
adcx rdx, rbx
mov rbx, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xf0 ], r9
mulx r9, r15, [ rax + 0x10 ]
xor rdx, rdx
adox r14, [ rsp + 0x10 ]
adox r10, [ rsp + 0x8 ]
adcx r8, r12
adcx rcx, r11
add r13, [ rsp + 0x10 ]
adcx rbp, [ rsp + 0x8 ]
mov rdx, [ rax + 0x18 ]
mulx r12, r11, [ rsi + 0x28 ]
test al, al
adox r8, r15
mov rdx, r9
adox rdx, rcx
adcx r14, rdi
adcx r10, [ rsp + 0xe8 ]
add r13, rdi
adcx rbp, [ rsp + 0xe8 ]
test al, al
adox r8, r11
mov rdi, r12
adox rdi, rdx
adcx r8, [ rsp + 0x40 ]
adcx rdi, [ rsp + 0x38 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xf8 ], rbp
mulx rbp, rcx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x100 ], r13
mov [ rsp + 0x108 ], r10
mulx r10, r13, [ rax + 0x30 ]
mov rdx, r15
test al, al
adox rdx, [ rsp + 0xf0 ]
adox r9, rbx
mov rbx, r13
adcx rbx, [ rsp + 0xc0 ]
mov r15, r10
adcx r15, [ rsp + 0xb8 ]
test al, al
adox rdx, r11
adox r12, r9
mov r11, rbx
adcx r11, r13
adcx r10, r15
xor r13, r13
adox rdx, [ rsp + 0x40 ]
adox r12, [ rsp + 0x38 ]
adcx r8, rcx
mov r9, rbp
adcx r9, rdi
xor rdi, rdi
adox r8, [ rsp + 0xb0 ]
adox r9, [ rsp + 0xa8 ]
adcx r11, [ rsp + 0xc0 ]
adcx r10, [ rsp + 0xb8 ]
xor r13, r13
adox r11, [ rsp - 0x20 ]
adox r10, [ rsp - 0x28 ]
mov rdi, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x110 ], r14
mulx r14, r13, [ rax + 0x0 ]
adcx rbx, [ rsp - 0x20 ]
adcx r15, [ rsp - 0x28 ]
xor rdx, rdx
adox r8, [ rsp - 0x30 ]
adox r9, [ rsp - 0x38 ]
adcx rdi, rcx
adcx rbp, r12
mov rdx, [ rax + 0x18 ]
mulx r12, rcx, [ rsi + 0x30 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x118 ], rbp
mov [ rsp + 0x120 ], rdi
mulx rdi, rbp, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x128 ], r9
mov [ rsp + 0x130 ], r8
mulx r8, r9, [ rax + 0x38 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x138 ], rdi
mov [ rsp + 0x140 ], rbp
mulx rbp, rdi, [ rax + 0x28 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x148 ], rbp
mov [ rsp + 0x150 ], rdi
mulx rdi, rbp, [ rsi + 0x28 ]
mov rdx, rbp
test al, al
adox rdx, [ rsp + 0xe0 ]
adox rdi, [ rsp + 0xd8 ]
adcx rdx, r9
adcx r8, rdi
add rbx, rcx
mov r9, r12
adcx r9, r15
add rbx, [ rsp + 0x20 ]
adcx r9, [ rsp + 0x18 ]
add r11, rcx
adcx r12, r10
test al, al
adox r11, [ rsp + 0x20 ]
adox r12, [ rsp + 0x18 ]
mov r10, rdx
adcx r10, r13
adcx r14, r8
add r10, [ rsp + 0x60 ]
adcx r14, [ rsp + 0x58 ]
xor r13, r13
adox r11, [ rsp + 0x150 ]
adox r12, [ rsp + 0x148 ]
mov r15, rdx
mov rdx, [ rax + 0x0 ]
mulx rbp, rcx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mulx r13, rdi, [ rax + 0x8 ]
adcx r15, rcx
adcx rbp, r8
test al, al
adox r15, rdi
adox r13, rbp
adcx r11, [ rsp - 0x40 ]
adcx r12, [ rsp - 0x48 ]
test al, al
adox rbx, [ rsp + 0x150 ]
adox r9, [ rsp + 0x148 ]
mov rdx, [ rax + 0x18 ]
mulx rcx, r8, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mulx rbp, rdi, [ rsi + 0x8 ]
adcx r15, rdi
adcx rbp, r13
mov rdx, [ rsi + 0x20 ]
mulx rdi, r13, [ rax + 0x18 ]
xor rdx, rdx
adox r15, r8
adox rcx, rbp
adcx r10, [ rsp + 0x140 ]
adcx r14, [ rsp + 0x138 ]
mov rdx, [ rsi + 0x10 ]
mulx rbp, r8, [ rax + 0x28 ]
test al, al
adox r10, r13
adox rdi, r14
adcx r10, [ rsp + 0x30 ]
adcx rdi, [ rsp + 0x28 ]
mov rdx, [ rax + 0x38 ]
mulx r14, r13, [ rsi + 0x10 ]
xor rdx, rdx
adox r10, r8
adox rbp, rdi
adcx rbx, [ rsp - 0x40 ]
adcx r9, [ rsp - 0x48 ]
mov rdx, [ rax + 0x0 ]
mulx rdi, r8, [ rsi + 0x8 ]
test al, al
adox rbx, r13
mov rdx, r14
adox rdx, r9
adcx r11, r13
adcx r14, r12
test al, al
adox rbx, r8
adox rdi, rdx
mov rdx, [ rsi + 0x8 ]
mulx r13, r12, [ rax + 0x30 ]
adcx r10, r12
adcx r13, rbp
mov rdx, [ rsp + 0x110 ]
test al, al
adox rdx, [ rsp + 0xa0 ]
mov rbp, [ rsp + 0x108 ]
adox rbp, [ rsp + 0x98 ]
mov r9, rdx
mov rdx, [ rsi + 0x30 ]
mulx r12, r8, [ rax + 0x0 ]
adcx r9, r8
adcx r12, rbp
mov rdx, [ rax + 0x38 ]
mulx r8, rbp, [ rsi + 0x0 ]
test al, al
adox r10, rbp
adox r8, r13
mov rdx, r10
shrd rdx, r8, 56
mov r13, rdx
mov rdx, [ rax + 0x8 ]
mulx r8, rbp, [ rsi + 0x28 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x158 ], r14
mov [ rsp + 0x160 ], r11
mulx r11, r14, [ rsi + 0x18 ]
test al, al
adox r9, rbp
adox r8, r12
mov rdx, [ rax + 0x8 ]
mulx rbp, r12, [ rsi + 0x0 ]
mov rdx, [ rsp - 0x10 ]
mov [ rsp + 0x168 ], rcx
mov rcx, rdx
adcx rcx, [ rsp + 0x130 ]
mov [ rsp + 0x170 ], r15
mov r15, [ rsp - 0x18 ]
adcx r15, [ rsp + 0x128 ]
xor rdx, rdx
adox rbx, r12
adox rbp, rdi
mov rdi, 0xffffffffffffff 
and r10, rdi
mov r12, r13
adox r12, rcx
adox r15, rdx
mov rdx, [ rsi + 0x20 ]
mulx rdi, rcx, [ rax + 0x8 ]
mov rdx, r12
shrd rdx, r15, 56
mov r15, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x178 ], r10
mov [ rsp + 0x180 ], rdi
mulx rdi, r10, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x188 ], rcx
mov [ rsp + 0x190 ], rdi
mulx rdi, rcx, [ rax + 0x18 ]
mov rdx, [ rsp + 0x120 ]
add rdx, [ rsp + 0xb0 ]
mov [ rsp + 0x198 ], rdi
mov rdi, [ rsp + 0x118 ]
adcx rdi, [ rsp + 0xa8 ]
mov [ rsp + 0x1a0 ], rcx
xor rcx, rcx
adox rdx, [ rsp - 0x30 ]
adox rdi, [ rsp - 0x38 ]
adcx rdx, [ rsp + 0x80 ]
adcx rdi, [ rsp + 0x78 ]
test al, al
adox rdx, r14
adox r11, rdi
adcx rbx, r15
adc rbp, 0x0
mov r14, rdx
mov rdx, [ rax + 0x10 ]
mulx rdi, r15, [ rsi + 0x20 ]
mov rdx, 0xffffffffffffff 
and r12, rdx
adox r9, r15
adox rdi, r8
mov r8, rbx
shrd r8, rbp, 56
add r14, r10
adcx r11, [ rsp + 0x190 ]
mov r10, [ rsp + 0x170 ]
mov rbp, [ rsp + 0x168 ]
mov r15, r10
shrd r15, rbp, 56
and rbx, rdx
mov rdx, [ rax + 0x20 ]
mulx rcx, rbp, [ rsi + 0x0 ]
adox r14, [ rsp + 0x1a0 ]
adox r11, [ rsp + 0x198 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1a8 ], rbx
mov [ rsp + 0x1b0 ], r8
mulx r8, rbx, [ rax + 0x18 ]
adcx r14, rbp
adcx rcx, r11
mov rdx, [ rsi + 0x10 ]
mulx r11, rbp, [ rax + 0x0 ]
add r14, r15
adc rcx, 0x0
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x1b8 ], r12
mulx r12, r15, [ rax + 0x20 ]
test al, al
adox r9, rbx
adox r8, rdi
mov rdx, [ rsp + 0xd0 ]
mov rdi, rdx
adcx rdi, [ rsp + 0x160 ]
mov rbx, [ rsp + 0xc8 ]
adcx rbx, [ rsp + 0x158 ]
xor rdx, rdx
adox r13, r14
adox rcx, rdx
mov r14, r13
shrd r14, rcx, 56
xor rcx, rcx
adox rdi, [ rsp + 0x188 ]
adox rbx, [ rsp + 0x180 ]
adcx rdi, [ rsp + 0x0 ]
adcx rbx, [ rsp - 0x8 ]
mov rdx, 0x38 
bzhi rcx, r13, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x1c0 ], rcx
mulx rcx, r13, [ rsi + 0x10 ]
adox rdi, [ rsp + 0x50 ]
adox rbx, [ rsp + 0x48 ]
test al, al
adox rdi, r15
adox r12, rbx
adcx r9, r13
adcx rcx, r8
mov rdx, [ rsi + 0x0 ]
mulx r8, r15, [ rax + 0x28 ]
test al, al
adox rdi, r15
adox r8, r12
adcx rdi, r14
adc r8, 0x0
mov rdx, [ rax + 0x28 ]
mulx r13, r14, [ rsi + 0x8 ]
mov rdx, [ rax + 0x30 ]
mulx r12, rbx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x1c8 ], r12
mulx r12, r15, [ rsi + 0x8 ]
mov rdx, [ rsp + 0x100 ]
mov [ rsp + 0x1d0 ], r12
xor r12, r12
adox rdx, [ rsp + 0xa0 ]
mov [ rsp + 0x1d8 ], r15
mov r15, [ rsp + 0xf8 ]
adox r15, [ rsp + 0x98 ]
adcx rdx, rbp
adcx r11, r15
mov rbp, rdi
shrd rbp, r8, 56
test al, al
adox r9, r14
adox r13, rcx
adcx r9, rbx
adcx r13, [ rsp + 0x1c8 ]
test al, al
adox r9, rbp
adox r13, r12
mov rcx, 0xffffffffffffff 
mov r8, r9
and r8, rcx
shrd r9, r13, 56
mov r14, rdx
mov rdx, [ rsi + 0x0 ]
mulx r15, rbx, [ rax + 0x10 ]
xor rdx, rdx
adox r14, [ rsp + 0x1d8 ]
adox r11, [ rsp + 0x1d0 ]
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x30 ], r8
add r9, [ rsp + 0x178 ]
xor rbp, rbp
adox r14, rbx
adox r15, r11
mov rdx, r9
shr rdx, 56
mov r13, rdx
add r13, [ rsp + 0x1c0 ]
add rdx, [ rsp + 0x1b8 ]
xor r8, r8
adox r14, [ rsp + 0x1b0 ]
adox r15, r8
mov rbp, r14
shrd rbp, r15, 56
and r14, rcx
mov rbx, rdx
and rbx, rcx
mov [ r12 + 0x10 ], r14
and r10, rcx
lea rbp, [ rbp + r10 ]
mov r11, rbp
shr r11, 56
and rdi, rcx
shr rdx, 56
lea r11, [ r11 + r13 ]
mov r13, r11
shr r13, 56
lea r13, [ r13 + rdi ]
and r11, rcx
mov [ r12 + 0x20 ], r11
and r9, rcx
mov [ r12 + 0x0 ], rbx
mov [ r12 + 0x38 ], r9
add rdx, [ rsp + 0x1a8 ]
and rbp, rcx
mov [ r12 + 0x18 ], rbp
mov [ r12 + 0x28 ], r13
mov [ r12 + 0x8 ], rdx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 608
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.1863
; seed 2267774496026450 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5517803 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=77, initial num_batches=31): 127365 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.023082556590005115
; number reverted permutation / tried permutation: 58749 / 90223 =65.115%
; number reverted decision / tried decision: 48094 / 89776 =53.571%
; validated in 4.455s
