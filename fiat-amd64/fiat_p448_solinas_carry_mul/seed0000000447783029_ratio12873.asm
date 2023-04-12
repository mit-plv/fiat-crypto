SECTION .text
	GLOBAL fiat_p448_solinas_carry_mul
fiat_p448_solinas_carry_mul:
sub rsp, 504
mov rax, rdx
mov rdx, [ rsi + 0x28 ]
mulx r11, r10, [ rax + 0x38 ]
mov rdx, [ rax + 0x20 ]
mulx r8, rcx, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x10 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x10 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x48 ], r14
mov [ rsp - 0x40 ], r13
mulx r13, r14, [ rsi + 0x38 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x38 ], r12
mov [ rsp - 0x30 ], rbp
mulx rbp, r12, [ rsi + 0x18 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x28 ], rdi
mov [ rsp - 0x20 ], r15
mulx r15, rdi, [ rsi + 0x38 ]
mov rdx, rdi
add rdx, rdi
mov [ rsp - 0x18 ], rbp
mov rbp, r15
adcx rbp, r15
test al, al
adox rdx, r14
mov [ rsp - 0x10 ], r12
mov r12, r13
adox r12, rbp
mov rbp, rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x8 ], r11
mov [ rsp + 0x0 ], r10
mulx r10, r11, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x8 ], r10
mov [ rsp + 0x10 ], r11
mulx r11, r10, [ rax + 0x10 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x18 ], r11
mov [ rsp + 0x20 ], r10
mulx r10, r11, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x28 ], r10
mov [ rsp + 0x30 ], r11
mulx r11, r10, [ rax + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x38 ], r11
mov [ rsp + 0x40 ], r10
mulx r10, r11, [ rax + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x48 ], r10
mov [ rsp + 0x50 ], r11
mulx r11, r10, [ rax + 0x20 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x58 ], r11
mov [ rsp + 0x60 ], r10
mulx r10, r11, [ rsi + 0x18 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x68 ], r10
mov [ rsp + 0x70 ], r11
mulx r11, r10, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x78 ], r11
mov [ rsp + 0x80 ], r10
mulx r10, r11, [ rax + 0x10 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x88 ], r10
mov [ rsp + 0x90 ], r11
mulx r11, r10, [ rsi + 0x8 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x98 ], r11
mov [ rsp + 0xa0 ], r10
mulx r10, r11, [ rsi + 0x30 ]
adcx rdi, r14
adcx r13, r15
add rbp, rcx
mov rdx, r8
adcx rdx, r12
mov r14, r9
xor r15, r15
adox r14, r11
mov r12, r10
adox r12, rbx
adcx rdi, rcx
adcx r8, r13
add r14, [ rsp + 0x0 ]
adcx r12, [ rsp - 0x8 ]
mov rcx, r14
xor r13, r13
adox rcx, r9
adox rbx, r12
mov r15, rdx
mov rdx, [ rsi + 0x38 ]
mulx r13, r9, [ rax + 0x30 ]
adcx rcx, r11
adcx r10, rbx
xor rdx, rdx
adox rcx, [ rsp + 0x0 ]
adox r10, [ rsp - 0x8 ]
mov rdx, [ rsi + 0x30 ]
mulx rbx, r11, [ rax + 0x38 ]
mov rdx, r9
adcx rdx, r11
mov [ rsp + 0xa8 ], r15
mov r15, rbx
adcx r15, r13
mov [ rsp + 0xb0 ], rbp
mov rbp, rdx
test al, al
adox rbp, r9
adox r13, r15
adcx rbp, r11
adcx rbx, r13
test al, al
adox rdi, [ rsp + 0x40 ]
adox r8, [ rsp + 0x38 ]
adcx rdi, [ rsp + 0x80 ]
adcx r8, [ rsp + 0x78 ]
mov r9, rdx
mov rdx, [ rax + 0x10 ]
mulx r13, r11, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xb8 ], r8
mov [ rsp + 0xc0 ], rdi
mulx rdi, r8, [ rax + 0x8 ]
xor rdx, rdx
adox rcx, r8
mov [ rsp + 0xc8 ], rbx
mov rbx, rdi
adox rbx, r10
adcx r9, r11
mov r10, r13
adcx r10, r15
xor r15, r15
adox rbp, r11
adox r13, [ rsp + 0xc8 ]
adcx rcx, [ rsp + 0x90 ]
adcx rbx, [ rsp + 0x88 ]
mov rdx, [ rsi + 0x30 ]
mulx r15, r11, [ rax + 0x18 ]
add rbp, r11
mov rdx, r15
adcx rdx, r13
add r9, r11
adcx r15, r10
test al, al
adox r9, [ rsp + 0x60 ]
adox r15, [ rsp + 0x58 ]
adcx rbp, [ rsp + 0x60 ]
adcx rdx, [ rsp + 0x58 ]
mov r10, rdx
mov rdx, [ rsi + 0x20 ]
mulx r11, r13, [ rax + 0x20 ]
test al, al
adox r14, r8
adox rdi, r12
adcx r14, [ rsp + 0x90 ]
adcx rdi, [ rsp + 0x88 ]
mov rdx, [ rsi + 0x28 ]
mulx r8, r12, [ rax + 0x18 ]
test al, al
adox r14, r12
mov rdx, r8
adox rdx, rdi
adcx rcx, r12
adcx r8, rbx
add rcx, r13
mov rbx, r11
adcx rbx, r8
add r14, r13
adcx r11, rdx
mov r13, [ rsp + 0xb0 ]
test al, al
adox r13, [ rsp + 0x40 ]
mov rdi, [ rsp + 0xa8 ]
adox rdi, [ rsp + 0x38 ]
adcx r13, [ rsp + 0x80 ]
adcx rdi, [ rsp + 0x78 ]
test al, al
adox r14, [ rsp + 0x70 ]
adox r11, [ rsp + 0x68 ]
mov rdx, [ rax + 0x30 ]
mulx r8, r12, [ rsi + 0x10 ]
adcx r13, [ rsp - 0x10 ]
adcx rdi, [ rsp - 0x18 ]
add r14, r12
mov rdx, r8
adcx rdx, r11
add rcx, [ rsp + 0x70 ]
adcx rbx, [ rsp + 0x68 ]
mov r11, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xd0 ], rdi
mov [ rsp + 0xd8 ], r13
mulx r13, rdi, [ rsi + 0x38 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xe0 ], r11
mov [ rsp + 0xe8 ], r14
mulx r14, r11, [ rsi + 0x30 ]
test al, al
adox rcx, r12
adox r8, rbx
adcx rdi, r11
adcx r14, r13
mov rdx, [ rsi + 0x20 ]
mulx rbx, r12, [ rax + 0x28 ]
xor rdx, rdx
adox rbp, r12
mov r13, rbx
adox r13, r10
mov rdx, [ rsi + 0x18 ]
mulx r11, r10, [ rax + 0x0 ]
adcx r9, r12
adcx rbx, r15
add rdi, [ rsp + 0x10 ]
adcx r14, [ rsp + 0x8 ]
mov rdx, [ rax + 0x0 ]
mulx r12, r15, [ rsi + 0x38 ]
xor rdx, rdx
adox rdi, [ rsp + 0x30 ]
adox r14, [ rsp + 0x28 ]
mov [ rsp + 0xf0 ], rbx
mov rbx, rdi
adcx rbx, r10
adcx r11, r14
add rdi, r15
adcx r12, r14
mov rdx, [ rax + 0x0 ]
mulx r15, r10, [ rsi + 0x20 ]
xor rdx, rdx
adox rbp, [ rsp - 0x20 ]
adox r13, [ rsp - 0x28 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0xf8 ], r9
mulx r9, r14, [ rsi + 0x10 ]
adcx rbx, r14
adcx r9, r11
xor rdx, rdx
adox rcx, [ rsp + 0xa0 ]
adox r8, [ rsp + 0x98 ]
adcx rcx, r10
adcx r15, r8
mov rdx, [ rax + 0x8 ]
mulx r10, r11, [ rsi + 0x18 ]
add rcx, r11
adcx r10, r15
mov rdx, [ rax + 0x18 ]
mulx r8, r14, [ rsi + 0x8 ]
xor rdx, rdx
adox rcx, [ rsp + 0x50 ]
adox r10, [ rsp + 0x48 ]
adcx rcx, r14
adcx r8, r10
mov rdx, [ rsi + 0x30 ]
mulx r11, r15, [ rax + 0x8 ]
test al, al
adox rbx, [ rsp - 0x30 ]
adox r9, [ rsp - 0x38 ]
mov rdx, [ rax + 0x18 ]
mulx r10, r14, [ rsi + 0x0 ]
adcx rbx, r14
adcx r10, r9
xor rdx, rdx
adox rdi, r15
adox r11, r12
mov r12, 0xffffffffffffff 
mov r15, rbx
and r15, r12
mov rdx, [ rsi + 0x28 ]
mulx r14, r9, [ rax + 0x10 ]
adox rdi, r9
adox r14, r11
mov rdx, [ rsi + 0x28 ]
mulx r9, r11, [ rax + 0x0 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x100 ], r15
mulx r15, r12, [ rsi + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x108 ], r9
mov [ rsp + 0x110 ], r11
mulx r11, r9, [ rsi + 0x20 ]
adcx rdi, r9
adcx r11, r14
xor rdx, rdx
adox rbp, [ rsp - 0x40 ]
adox r13, [ rsp - 0x48 ]
mov rdx, [ rax + 0x20 ]
mulx r9, r14, [ rsi + 0x18 ]
adcx rcx, r12
adcx r15, r8
mov rdx, [ rax + 0x30 ]
mulx r12, r8, [ rsi + 0x8 ]
mov rdx, [ rsp + 0xf8 ]
mov [ rsp + 0x118 ], r15
xor r15, r15
adox rdx, [ rsp - 0x20 ]
mov [ rsp + 0x120 ], rcx
mov rcx, [ rsp + 0xf0 ]
adox rcx, [ rsp - 0x28 ]
adcx rdx, [ rsp - 0x40 ]
adcx rcx, [ rsp - 0x48 ]
add rbp, [ rsp + 0x110 ]
adcx r13, [ rsp + 0x108 ]
mov r15, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x128 ], rcx
mov [ rsp + 0x130 ], r13
mulx r13, rcx, [ rax + 0x28 ]
test al, al
adox rdi, r14
adox r9, r11
adcx rdi, rcx
adcx r13, r9
mov rdx, [ rsi + 0x20 ]
mulx r14, r11, [ rax + 0x8 ]
shrd rbx, r10, 56
xor rdx, rdx
adox rdi, r8
adox r12, r13
mov r10, rbx
adcx r10, [ rsp + 0x120 ]
mov r8, [ rsp + 0x118 ]
adc r8, 0x0
mov rdx, [ rsi + 0x18 ]
mulx r9, rcx, [ rax + 0x10 ]
mov rdx, [ rax + 0x0 ]
mulx rbx, r13, [ rsi + 0x10 ]
test al, al
adox rbp, r11
adox r14, [ rsp + 0x130 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x138 ], r15
mulx r15, r11, [ rsi + 0x0 ]
adcx rdi, r11
adcx r15, r12
mov rdx, [ rax + 0x18 ]
mulx r11, r12, [ rsi + 0x10 ]
mov rdx, 0x38 
mov [ rsp + 0x140 ], rbx
bzhi rbx, rdi, rdx
shrd rdi, r15, 56
mov r15, rdi
xor rdx, rdx
adox r15, r10
adox r8, rdx
mov r10, [ rsp + 0xe8 ]
adcx r10, [ rsp + 0xa0 ]
mov [ rsp + 0x148 ], rbx
mov rbx, [ rsp + 0xe0 ]
adcx rbx, [ rsp + 0x98 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x150 ], r13
mov [ rsp + 0x158 ], rbx
mulx rbx, r13, [ rsi + 0x0 ]
add rbp, rcx
adcx r9, r14
mov rdx, [ rax + 0x8 ]
mulx r14, rcx, [ rsi + 0x8 ]
add rbp, r12
adcx r11, r9
mov rdx, 0x38 
bzhi r12, r15, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x160 ], r12
mulx r12, r9, [ rsi + 0x0 ]
adox r10, r9
adox r12, [ rsp + 0x158 ]
test al, al
adox rdi, r10
mov rdx, 0x0 
adox r12, rdx
mov rdx, [ rax + 0x8 ]
mulx r10, r9, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x168 ], r14
mov [ rsp + 0x170 ], rcx
mulx rcx, r14, [ rax + 0x0 ]
mov rdx, r14
adcx rdx, [ rsp + 0xd8 ]
adcx rcx, [ rsp + 0xd0 ]
test al, al
adox rdx, r9
adox r10, rcx
adcx rdx, [ rsp + 0x20 ]
adcx r10, [ rsp + 0x18 ]
mov r9, rdi
shrd r9, r12, 56
mov r12, rdx
mov rdx, [ rsi + 0x8 ]
mulx rcx, r14, [ rax + 0x20 ]
xor rdx, rdx
adox rbp, r14
adox rcx, r11
mov rdx, [ rax + 0x18 ]
mulx r14, r11, [ rsi + 0x18 ]
shrd r15, r8, 56
test al, al
adox rbp, r13
adox rbx, rcx
mov rdx, [ rsi + 0x8 ]
mulx r13, r8, [ rax + 0x28 ]
adcx rbp, r15
adc rbx, 0x0
mov rdx, [ rax + 0x20 ]
mulx r15, rcx, [ rsi + 0x10 ]
add r12, r11
adcx r14, r10
xor rdx, rdx
adox r12, rcx
adox r15, r14
adcx r12, r8
adcx r13, r15
mov r10, [ rsp + 0xc0 ]
test al, al
adox r10, [ rsp - 0x10 ]
mov r11, [ rsp + 0xb8 ]
adox r11, [ rsp - 0x18 ]
adcx r10, [ rsp + 0x150 ]
adcx r11, [ rsp + 0x140 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r8, [ rax + 0x8 ]
test al, al
adox r10, [ rsp + 0x170 ]
adox r11, [ rsp + 0x168 ]
mov rdx, [ rsi + 0x8 ]
mulx r15, r14, [ rax + 0x0 ]
mov rdx, r14
adcx rdx, [ rsp + 0x138 ]
adcx r15, [ rsp + 0x128 ]
xor r14, r14
adox rdx, r8
adox rcx, r15
mov r8, rdx
mov rdx, [ rax + 0x30 ]
mulx r14, r15, [ rsi + 0x0 ]
mov rdx, rbp
shrd rdx, rbx, 56
add r12, r15
adcx r14, r13
xor rbx, rbx
adox r12, rdx
adox r14, rbx
mov r13, 0xffffffffffffff 
mov r15, r12
and r15, r13
shrd r12, r14, 56
and rdi, r13
add r12, [ rsp + 0x148 ]
mov rdx, r12
shr rdx, 56
lea rdi, [ rdi + rdx ]
add r8, r9
adc rcx, 0x0
and r12, r13
mov r9, rdx
mov rdx, [ rax + 0x10 ]
mulx rbx, r14, [ rsi + 0x0 ]
adox r10, r14
adox rbx, r11
mov rdx, r8
and rdx, r13
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x38 ], r12
shrd r8, rcx, 56
add r10, r8
adc rbx, 0x0
mov rcx, r10
shrd rcx, rbx, 56
add rcx, [ rsp + 0x100 ]
and r10, r13
mov r12, rdi
and r12, r13
shr rdi, 56
lea rdi, [ rdi + rdx ]
mov [ r11 + 0x0 ], r12
mov r14, rcx
shr r14, 56
add r9, [ rsp + 0x160 ]
lea r14, [ r14 + r9 ]
and rbp, r13
mov rdx, r14
shr rdx, 56
lea rdx, [ rdx + rbp ]
and r14, r13
and rcx, r13
mov [ r11 + 0x8 ], rdi
mov [ r11 + 0x30 ], r15
mov [ r11 + 0x18 ], rcx
mov [ r11 + 0x20 ], r14
mov [ r11 + 0x10 ], r10
mov [ r11 + 0x28 ], rdx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 504
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.2873
; seed 1548127196532130 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 8578981 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=109, initial num_batches=31): 215050 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.02506707964500679
; number reverted permutation / tried permutation: 64709 / 90151 =71.778%
; number reverted decision / tried decision: 51478 / 89848 =57.295%
; validated in 5.963s
