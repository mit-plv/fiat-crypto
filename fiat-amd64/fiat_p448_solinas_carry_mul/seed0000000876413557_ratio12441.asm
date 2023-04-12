SECTION .text
	GLOBAL fiat_p448_solinas_carry_mul
fiat_p448_solinas_carry_mul:
sub rsp, 472
mov rax, rdx
mov rdx, [ rsi + 0x38 ]
mulx r11, r10, [ rax + 0x30 ]
mov rdx, [ rsi + 0x30 ]
mulx r8, rcx, [ rax + 0x38 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x48 ], r14
mov [ rsp - 0x40 ], r13
mulx r13, r14, [ rsi + 0x28 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x38 ], r12
mov [ rsp - 0x30 ], rbp
mulx rbp, r12, [ rsi + 0x20 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x28 ], rdi
mov [ rsp - 0x20 ], r15
mulx r15, rdi, [ rsi + 0x0 ]
mov rdx, r10
test al, al
adox rdx, rcx
mov [ rsp - 0x18 ], r15
mov r15, r8
adox r15, r11
mov [ rsp - 0x10 ], rdi
mov rdi, rdx
adcx rdi, r10
adcx r11, r15
mov r10, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x8 ], rbp
mov [ rsp + 0x0 ], r12
mulx r12, rbp, [ rax + 0x30 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x8 ], r13
mov [ rsp + 0x10 ], r14
mulx r14, r13, [ rax + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x18 ], r14
mov [ rsp + 0x20 ], r13
mulx r13, r14, [ rsi + 0x20 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x28 ], r13
mov [ rsp + 0x30 ], r14
mulx r14, r13, [ rsi + 0x28 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x38 ], r14
mov [ rsp + 0x40 ], r13
mulx r13, r14, [ rsi + 0x28 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x48 ], r13
mov [ rsp + 0x50 ], r14
mulx r14, r13, [ rsi + 0x20 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x58 ], r14
mov [ rsp + 0x60 ], r13
mulx r13, r14, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x68 ], r13
mov [ rsp + 0x70 ], r14
mulx r14, r13, [ rax + 0x20 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x78 ], r14
mov [ rsp + 0x80 ], r13
mulx r13, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x88 ], r13
mov [ rsp + 0x90 ], r14
mulx r14, r13, [ rax + 0x28 ]
add rdi, rcx
adcx r8, r11
mov rdx, [ rax + 0x28 ]
mulx r11, rcx, [ rsi + 0x20 ]
test al, al
adox rdi, r9
mov rdx, rbx
adox rdx, r8
mov r8, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x98 ], r14
mov [ rsp + 0xa0 ], r13
mulx r13, r14, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xa8 ], r12
mov [ rsp + 0xb0 ], rbp
mulx rbp, r12, [ rax + 0x20 ]
adcx rdi, r14
mov rdx, r13
adcx rdx, r8
add rdi, r12
mov r8, rbp
adcx r8, rdx
xor rdx, rdx
adox r10, r9
adox rbx, r15
adcx rdi, rcx
mov r9, r11
adcx r9, r8
test al, al
adox r10, r14
adox r13, rbx
adcx r10, r12
adcx rbp, r13
test al, al
adox r10, rcx
adox r11, rbp
adcx rdi, [ rsp + 0xb0 ]
adcx r9, [ rsp + 0xa8 ]
test al, al
adox r10, [ rsp + 0xb0 ]
adox r11, [ rsp + 0xa8 ]
mov rdx, [ rax + 0x38 ]
mulx rcx, r15, [ rsi + 0x28 ]
mov rdx, [ rax + 0x30 ]
mulx r12, r14, [ rsi + 0x30 ]
mov rdx, [ rax + 0x28 ]
mulx rbx, r8, [ rsi + 0x38 ]
mov rdx, r8
adcx rdx, r14
mov r13, r12
adcx r13, rbx
add rdx, r15
mov rbp, rcx
adcx rbp, r13
mov r13, rdx
add r13, r8
adcx rbx, rbp
test al, al
adox r13, r14
adox r12, rbx
mov r14, rdx
mov rdx, [ rsi + 0x10 ]
mulx rbx, r8, [ rax + 0x38 ]
adcx r14, [ rsp + 0x20 ]
adcx rbp, [ rsp + 0x18 ]
xor rdx, rdx
adox rdi, r8
mov [ rsp + 0xb8 ], rbp
mov rbp, rbx
adox rbp, r9
adcx r10, r8
adcx rbx, r11
mov rdx, [ rsi + 0x38 ]
mulx r11, r9, [ rax + 0x18 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xc0 ], rbx
mulx rbx, r8, [ rax + 0x20 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xc8 ], r10
mov [ rsp + 0xd0 ], r14
mulx r14, r10, [ rax + 0x38 ]
mov rdx, r10
test al, al
adox rdx, r10
mov [ rsp + 0xd8 ], r12
mov r12, r14
adox r12, r14
adcx r10, r9
mov [ rsp + 0xe0 ], r13
mov r13, r11
adcx r13, r14
add rdx, r9
adcx r11, r12
xor r9, r9
adox rdi, [ rsp + 0x10 ]
adox rbp, [ rsp + 0x8 ]
mov r14, rdx
mov rdx, [ rax + 0x8 ]
mulx r9, r12, [ rsi + 0x20 ]
adcx rdi, r12
adcx r9, rbp
test al, al
adox r14, r8
mov rdx, rbx
adox rdx, r11
adcx r14, [ rsp + 0x50 ]
adcx rdx, [ rsp + 0x48 ]
mov r11, rdx
mov rdx, [ rax + 0x30 ]
mulx r12, rbp, [ rsi + 0x28 ]
add r10, r8
adcx rbx, r13
mov rdx, [ rsi + 0x38 ]
mulx r13, r8, [ rax + 0x20 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xe8 ], r9
mov [ rsp + 0xf0 ], rdi
mulx rdi, r9, [ rsi + 0x30 ]
xor rdx, rdx
adox r14, [ rsp + 0x60 ]
adox r11, [ rsp + 0x58 ]
adcx r8, r9
adcx rdi, r13
mov rdx, [ rsi + 0x30 ]
mulx r9, r13, [ rax + 0x0 ]
xor rdx, rdx
adox r10, [ rsp + 0x50 ]
adox rbx, [ rsp + 0x48 ]
adcx r8, rbp
adcx r12, rdi
test al, al
adox r10, [ rsp + 0x60 ]
adox rbx, [ rsp + 0x58 ]
mov rdx, [ rax + 0x38 ]
mulx rdi, rbp, [ rsi + 0x18 ]
adcx r10, rbp
mov rdx, rdi
adcx rdx, rbx
xor rbx, rbx
adox r14, rbp
adox rdi, r11
mov r11, r15
adcx r11, [ rsp + 0xe0 ]
adcx rcx, [ rsp + 0xd8 ]
mov r15, rdx
mov rdx, [ rax + 0x38 ]
mulx rbx, rbp, [ rsi + 0x20 ]
test al, al
adox r14, r13
adox r9, rdi
mov rdx, [ rsi + 0x30 ]
mulx rdi, r13, [ rax + 0x10 ]
mov rdx, r13
adcx rdx, [ rsp + 0xd0 ]
mov [ rsp + 0xf8 ], r15
mov r15, rdi
adcx r15, [ rsp + 0xb8 ]
mov [ rsp + 0x100 ], r10
mov r10, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x108 ], r9
mov [ rsp + 0x110 ], r14
mulx r14, r9, [ rsi + 0x18 ]
test al, al
adox r11, [ rsp + 0x20 ]
adox rcx, [ rsp + 0x18 ]
adcx r8, rbp
adcx rbx, r12
xor rdx, rdx
adox r11, r13
adox rdi, rcx
adcx r11, [ rsp + 0x70 ]
adcx rdi, [ rsp + 0x68 ]
test al, al
adox r11, [ rsp + 0x0 ]
adox rdi, [ rsp - 0x8 ]
mov r12, r9
adcx r12, [ rsp + 0xf0 ]
adcx r14, [ rsp + 0xe8 ]
mov rdx, [ rax + 0x18 ]
mulx r13, rbp, [ rsi + 0x10 ]
add r10, [ rsp + 0x70 ]
adcx r15, [ rsp + 0x68 ]
add r12, rbp
adcx r13, r14
test al, al
adox r10, [ rsp + 0x0 ]
adox r15, [ rsp - 0x8 ]
mov rdx, [ rax + 0x28 ]
mulx rcx, r9, [ rsi + 0x18 ]
adcx r11, r9
mov rdx, rcx
adcx rdx, rdi
mov rdi, rdx
mov rdx, [ rsi + 0x10 ]
mulx rbp, r14, [ rax + 0x30 ]
test al, al
adox r10, r9
adox rcx, r15
adcx r11, r14
mov rdx, rbp
adcx rdx, rdi
test al, al
adox r10, r14
adox rbp, rcx
mov r15, rdx
mov rdx, [ rax + 0x38 ]
mulx rdi, r9, [ rsi + 0x8 ]
mov rdx, r8
adcx rdx, [ rsp - 0x20 ]
mov r14, rbx
adcx r14, [ rsp - 0x28 ]
test al, al
adox r10, r9
mov rcx, rdi
adox rcx, rbp
mov rbp, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x118 ], r13
mov [ rsp + 0x120 ], r12
mulx r12, r13, [ rax + 0x8 ]
adcx rbp, r13
adcx r12, r14
add r11, r9
adcx rdi, r15
mov rdx, [ rax + 0x0 ]
mulx r9, r15, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x8 ]
mulx r13, r14, [ rax + 0x10 ]
add r8, r15
adcx r9, rbx
add r10, [ rsp - 0x30 ]
adcx rcx, [ rsp - 0x38 ]
mov rdx, [ rsi + 0x0 ]
mulx r15, rbx, [ rax + 0x18 ]
test al, al
adox rbp, r14
adox r13, r12
adcx rbp, rbx
adcx r15, r13
mov rdx, [ rax + 0x0 ]
mulx r14, r12, [ rsi + 0x20 ]
mov rdx, [ rax + 0x0 ]
mulx r13, rbx, [ rsi + 0x8 ]
mov rdx, rbx
test al, al
adox rdx, [ rsp + 0xc8 ]
adox r13, [ rsp + 0xc0 ]
mov rbx, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x128 ], rcx
mov [ rsp + 0x130 ], r10
mulx r10, rcx, [ rsi + 0x10 ]
adcx r11, r12
adcx r14, rdi
mov rdx, [ rax + 0x8 ]
mulx r12, rdi, [ rsi + 0x18 ]
test al, al
adox r11, rdi
adox r12, r14
adcx r11, rcx
adcx r10, r12
mov rdx, [ rax + 0x18 ]
mulx r14, rcx, [ rsi + 0x8 ]
test al, al
adox r11, rcx
adox r14, r10
mov rdx, [ rax + 0x8 ]
mulx r12, rdi, [ rsi + 0x30 ]
mov rdx, [ rax + 0x20 ]
mulx rcx, r10, [ rsi + 0x0 ]
adcx r11, r10
adcx rcx, r14
mov rdx, [ rax + 0x8 ]
mulx r10, r14, [ rsi + 0x0 ]
mov rdx, rbp
shrd rdx, r15, 56
add rbx, r14
adcx r10, r13
test al, al
adox r8, rdi
adox r12, r9
adcx r11, rdx
adc rcx, 0x0
mov rdx, [ rax + 0x38 ]
mulx r15, r9, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx rdi, r13, [ rax + 0x30 ]
add r8, [ rsp + 0x40 ]
adcx r12, [ rsp + 0x38 ]
xor rdx, rdx
adox r8, [ rsp + 0x30 ]
adox r12, [ rsp + 0x28 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x138 ], rcx
mulx rcx, r14, [ rsi + 0x10 ]
adcx r8, [ rsp + 0x80 ]
adcx r12, [ rsp + 0x78 ]
xor rdx, rdx
adox r8, r14
adox rcx, r12
adcx r8, r13
adcx rdi, rcx
add r8, r9
adcx r15, rdi
mov r9, r8
shrd r9, r15, 56
mov r13, r9
test al, al
adox r13, [ rsp + 0x130 ]
mov r14, [ rsp + 0x128 ]
adox r14, rdx
mov rdx, [ rsi + 0x8 ]
mulx rcx, r12, [ rax + 0x20 ]
mov rdx, r12
adcx rdx, [ rsp + 0x120 ]
adcx rcx, [ rsp + 0x118 ]
mov rdi, 0xffffffffffffff 
and r8, rdi
mov r15, r13
shrd r15, r14, 56
and r13, rdi
mov r14, rdx
mov rdx, [ rax + 0x10 ]
mulx rdi, r12, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x140 ], r13
mov [ rsp + 0x148 ], r8
mulx r8, r13, [ rax + 0x8 ]
mov rdx, r13
adox rdx, [ rsp + 0x110 ]
adox r8, [ rsp + 0x108 ]
adcx rdx, r12
adcx rdi, r8
mov r12, rdx
mov rdx, [ rsi + 0x10 ]
mulx r8, r13, [ rax + 0x0 ]
add rbx, r15
adc r10, 0x0
mov rdx, rbx
shrd rdx, r10, 56
add r12, [ rsp - 0x40 ]
adcx rdi, [ rsp - 0x48 ]
mov r15, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x150 ], r8
mulx r8, r10, [ rax + 0x20 ]
add r12, r10
adcx r8, rdi
test al, al
adox r12, [ rsp + 0xa0 ]
adox r8, [ rsp + 0x98 ]
mov rdx, [ rsi + 0x0 ]
mulx r10, rdi, [ rax + 0x30 ]
adcx r9, r11
mov rdx, [ rsp + 0x138 ]
adc rdx, 0x0
mov r11, r9
shrd r11, rdx, 56
xor rdx, rdx
adox r12, rdi
adox r10, r8
adcx r14, [ rsp - 0x10 ]
adcx rcx, [ rsp - 0x18 ]
xor r8, r8
adox r14, r11
adox rcx, r8
mov rdx, r14
shrd rdx, rcx, 56
mov rdi, 0x38 
bzhi r11, r9, rdi
adox r12, rdx
adox r10, r8
mov rdx, [ rax + 0x8 ]
mulx rcx, r9, [ rsi + 0x8 ]
mov rdx, r12
shrd rdx, r10, 56
mov r10, r13
add r10, [ rsp + 0x100 ]
mov rdi, [ rsp + 0xf8 ]
adcx rdi, [ rsp + 0x150 ]
add r10, r9
adcx rcx, rdi
add rdx, [ rsp + 0x148 ]
mov r13, 0x38 
bzhi r9, rdx, r13
shr rdx, 56
lea r11, [ r11 + rdx ]
add rdx, [ rsp + 0x140 ]
mov rdi, rdx
shr rdi, 56
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x38 ], r9
test al, al
adox r10, [ rsp + 0x90 ]
adox rcx, [ rsp + 0x88 ]
adcx r10, r15
adc rcx, 0x0
bzhi r15, rbp, r13
mov rbp, r10
shrd rbp, rcx, 56
bzhi r9, r10, r13
lea rbp, [ rbp + r15 ]
mov [ r8 + 0x10 ], r9
mov r10, rbp
shr r10, 56
bzhi rcx, r14, r13
lea r10, [ r10 + r11 ]
bzhi r14, r10, r13
shr r10, 56
mov [ r8 + 0x20 ], r14
lea r10, [ r10 + rcx ]
bzhi r11, rbp, r13
mov [ r8 + 0x18 ], r11
mov [ r8 + 0x28 ], r10
bzhi r15, r12, r13
bzhi r12, rbx, r13
lea rdi, [ rdi + r12 ]
mov [ r8 + 0x8 ], rdi
bzhi rbx, rdx, r13
mov [ r8 + 0x30 ], r15
mov [ r8 + 0x0 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 472
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.2441
; seed 3215512751068493 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 8618387 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=54, initial num_batches=31): 206331 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.023940790776742795
; number reverted permutation / tried permutation: 65330 / 90374 =72.288%
; number reverted decision / tried decision: 51142 / 89625 =57.062%
; validated in 4.531s
