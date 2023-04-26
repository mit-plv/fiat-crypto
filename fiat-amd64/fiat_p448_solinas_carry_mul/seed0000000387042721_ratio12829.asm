SECTION .text
	GLOBAL fiat_p448_solinas_carry_mul
fiat_p448_solinas_carry_mul:
sub rsp, 504
mov rax, rdx
mov rdx, [ rdx + 0x28 ]
mulx r11, r10, [ rsi + 0x28 ]
mov rdx, [ rax + 0x28 ]
mulx r8, rcx, [ rsi + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x28 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x8 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x48 ], rbx
mov [ rsp - 0x40 ], r9
mulx r9, rbx, [ rsi + 0x28 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x38 ], r12
mov [ rsp - 0x30 ], rbp
mulx rbp, r12, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x28 ], rbp
mov [ rsp - 0x20 ], r12
mulx r12, rbp, [ rsi + 0x38 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x18 ], r12
mov [ rsp - 0x10 ], rbp
mulx rbp, r12, [ rsi + 0x20 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x8 ], rbp
mov [ rsp + 0x0 ], r12
mulx r12, rbp, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x8 ], r11
mov [ rsp + 0x10 ], r10
mulx r10, r11, [ rax + 0x30 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x18 ], r10
mov [ rsp + 0x20 ], r11
mulx r11, r10, [ rax + 0x38 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x28 ], r11
mov [ rsp + 0x30 ], r10
mulx r10, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x38 ], r10
mov [ rsp + 0x40 ], r11
mulx r11, r10, [ rax + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x48 ], r11
mov [ rsp + 0x50 ], r10
mulx r10, r11, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x58 ], r8
mov [ rsp + 0x60 ], rcx
mulx rcx, r8, [ rax + 0x30 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x68 ], rcx
mov [ rsp + 0x70 ], r8
mulx r8, rcx, [ rax + 0x28 ]
mov rdx, rcx
mov [ rsp + 0x78 ], r10
xor r10, r10
adox rdx, rbp
mov [ rsp + 0x80 ], r11
mov r11, r12
adox r11, r8
adcx rdx, rbx
mov [ rsp + 0x88 ], r14
mov r14, r9
adcx r14, r11
mov r11, rdx
add r11, rcx
adcx r8, r14
test al, al
adox rdx, r15
mov rcx, rdi
adox rcx, r14
adcx r11, rbp
adcx r12, r8
add r11, rbx
adcx r9, r12
mov rbx, rdx
mov rdx, [ rax + 0x10 ]
mulx r14, rbp, [ rsi + 0x30 ]
add r11, r15
adcx rdi, r9
mov rdx, [ rax + 0x10 ]
mulx r8, r15, [ rsi + 0x0 ]
xor rdx, rdx
adox r11, rbp
mov r10, r14
adox r10, rdi
mov rdx, [ rsi + 0x38 ]
mulx r9, r12, [ rax + 0x38 ]
adcx rbx, rbp
adcx r14, rcx
mov rdx, [ rsi + 0x28 ]
mulx rbp, rcx, [ rax + 0x18 ]
mov rdx, r12
xor rdi, rdi
adox rdx, r12
mov [ rsp + 0x90 ], r8
mov r8, r9
adox r8, r9
adcx r11, rcx
mov [ rsp + 0x98 ], r15
mov r15, rbp
adcx r15, r10
xor r10, r10
adox rdx, r13
adox r8, [ rsp + 0x88 ]
adcx rbx, rcx
adcx rbp, r14
test al, al
adox rbx, [ rsp + 0x80 ]
adox rbp, [ rsp + 0x78 ]
adcx rbx, [ rsp + 0x60 ]
adcx rbp, [ rsp + 0x58 ]
mov rdi, rdx
mov rdx, [ rsi + 0x8 ]
mulx rcx, r14, [ rax + 0x8 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xa0 ], rcx
mulx rcx, r10, [ rsi + 0x30 ]
xor rdx, rdx
adox r12, r13
adox r9, [ rsp + 0x88 ]
adcx r12, r10
mov r13, rcx
adcx r13, r9
test al, al
adox rbx, [ rsp + 0x70 ]
adox rbp, [ rsp + 0x68 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0xa8 ], r14
mulx r14, r9, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xb0 ], r15
mov [ rsp + 0xb8 ], r11
mulx r11, r15, [ rax + 0x38 ]
mov rdx, r9
adcx rdx, r15
mov [ rsp + 0xc0 ], rbp
mov rbp, r11
adcx rbp, r14
mov [ rsp + 0xc8 ], rbx
mov rbx, rdx
add rbx, r9
adcx r14, rbp
test al, al
adox rdi, r10
adox rcx, r8
adcx rdi, [ rsp + 0x10 ]
adcx rcx, [ rsp + 0x8 ]
xor r8, r8
adox r12, [ rsp + 0x10 ]
adox r13, [ rsp + 0x8 ]
adcx rbx, r15
adcx r11, r14
xor r10, r10
adox rbx, [ rsp - 0x10 ]
adox r11, [ rsp - 0x18 ]
mov r8, rdx
mov rdx, [ rax + 0x28 ]
mulx r15, r9, [ rsi + 0x30 ]
mov rdx, [ rax + 0x18 ]
mulx r10, r14, [ rsi + 0x30 ]
adcx rdi, [ rsp + 0x0 ]
adcx rcx, [ rsp - 0x8 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xd0 ], rcx
mov [ rsp + 0xd8 ], rdi
mulx rdi, rcx, [ rax + 0x20 ]
xor rdx, rdx
adox r8, [ rsp - 0x10 ]
adox rbp, [ rsp - 0x18 ]
adcx rcx, r9
adcx r15, rdi
test al, al
adox r8, r14
mov r9, r10
adox r9, rbp
mov rdx, [ rsi + 0x20 ]
mulx rbp, rdi, [ rax + 0x28 ]
adcx rbx, r14
adcx r10, r11
mov rdx, [ rsi + 0x28 ]
mulx r14, r11, [ rax + 0x20 ]
test al, al
adox rbx, r11
mov rdx, r14
adox rdx, r10
adcx rbx, rdi
mov r10, rbp
adcx r10, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xe0 ], r13
mov [ rsp + 0xe8 ], r12
mulx r12, r13, [ rax + 0x38 ]
test al, al
adox r8, r11
adox r14, r9
adcx r8, rdi
adcx rbp, r14
mov rdx, [ rsi + 0x20 ]
mulx rdi, r9, [ rax + 0x38 ]
mov rdx, [ rsi + 0x30 ]
mulx r14, r11, [ rax + 0x8 ]
add rcx, [ rsp + 0x20 ]
adcx r15, [ rsp + 0x18 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xf0 ], r12
mov [ rsp + 0xf8 ], r13
mulx r13, r12, [ rax + 0x0 ]
xor rdx, rdx
adox rcx, r9
adox rdi, r15
mov r9, rcx
adcx r9, r12
adcx r13, rdi
test al, al
adox r8, [ rsp - 0x20 ]
adox rbp, [ rsp - 0x28 ]
adcx rbx, [ rsp - 0x20 ]
adcx r10, [ rsp - 0x28 ]
xor r15, r15
adox r9, r11
adox r14, r13
mov rdx, [ rax + 0x10 ]
mulx r12, r11, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mulx r15, r13, [ rax + 0x38 ]
mov rdx, r13
adcx rdx, [ rsp + 0xc8 ]
mov [ rsp + 0x100 ], rbp
mov rbp, r15
adcx rbp, [ rsp + 0xc0 ]
mov [ rsp + 0x108 ], r8
mov r8, [ rsp + 0x80 ]
mov [ rsp + 0x110 ], r10
mov r10, r8
test al, al
adox r10, [ rsp + 0xb8 ]
mov [ rsp + 0x118 ], rbx
mov rbx, [ rsp + 0x78 ]
adox rbx, [ rsp + 0xb0 ]
adcx r10, [ rsp + 0x60 ]
adcx rbx, [ rsp + 0x58 ]
xor r8, r8
adox r10, [ rsp + 0x70 ]
adox rbx, [ rsp + 0x68 ]
mov r8, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x120 ], rbx
mov [ rsp + 0x128 ], r10
mulx r10, rbx, [ rax + 0x20 ]
adcx r9, r11
adcx r12, r14
mov rdx, [ rax + 0x18 ]
mulx r11, r14, [ rsi + 0x20 ]
add r9, r14
adcx r11, r12
mov rdx, [ rsi + 0x10 ]
mulx r14, r12, [ rax + 0x8 ]
add r9, rbx
adcx r10, r11
xor rdx, rdx
adox r9, [ rsp - 0x30 ]
adox r10, [ rsp - 0x38 ]
mov rdx, [ rax + 0x30 ]
mulx r11, rbx, [ rsi + 0x8 ]
adcx r9, rbx
adcx r11, r10
add r9, [ rsp + 0xf8 ]
adcx r11, [ rsp + 0xf0 ]
mov rdx, r9
shrd rdx, r11, 56
mov r10, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, rbx, [ rax + 0x0 ]
xor rdx, rdx
adox r8, rbx
adox r11, rbp
mov rbp, r10
adcx rbp, r8
adc r11, 0x0
mov rbx, 0xffffffffffffff 
and r9, rbx
mov rdx, [ rsi + 0x18 ]
mulx rbx, r8, [ rax + 0x0 ]
adox rcx, r8
adox rbx, rdi
adcx rcx, r12
adcx r14, rbx
mov rdx, rbp
shrd rdx, r11, 56
mov rdi, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, r12, [ rax + 0x10 ]
xor rdx, rdx
adox rcx, r12
adox r11, r14
mov rdx, [ rsi + 0x0 ]
mulx rbx, r8, [ rax + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mulx r12, r14, [ rax + 0x8 ]
mov rdx, 0x38 
mov [ rsp + 0x130 ], r9
bzhi r9, rbp, rdx
adox rcx, r8
adox rbx, r11
mov rdx, [ rsi + 0x10 ]
mulx r11, rbp, [ rax + 0x10 ]
mov rdx, rcx
shrd rdx, rbx, 56
mov r8, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x138 ], r9
mulx r9, rbx, [ rax + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x140 ], rdi
mov [ rsp + 0x148 ], r8
mulx r8, rdi, [ rsi + 0x28 ]
mov rdx, r13
add rdx, [ rsp + 0x128 ]
adcx r15, [ rsp + 0x120 ]
mov r13, 0xffffffffffffff 
and rcx, r13
adox rdx, rbx
adox r9, r15
adcx rdx, r14
adcx r12, r9
mov r14, rdx
mov rdx, [ rax + 0x8 ]
mulx r15, rbx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mulx r13, r9, [ rax + 0x38 ]
mov rdx, r9
test al, al
adox rdx, [ rsp + 0x118 ]
mov [ rsp + 0x150 ], rcx
mov rcx, r13
adox rcx, [ rsp + 0x110 ]
adcx rdx, rdi
adcx r8, rcx
test al, al
adox rdx, rbx
adox r15, r8
mov rdi, rdx
mov rdx, [ rsi + 0x8 ]
mulx rcx, rbx, [ rax + 0x18 ]
adcx r14, rbp
adcx r11, r12
mov rdx, [ rax + 0x8 ]
mulx r12, rbp, [ rsi + 0x0 ]
test al, al
adox r14, rbx
adox rcx, r11
adcx r14, [ rsp + 0x40 ]
adcx rcx, [ rsp + 0x38 ]
mov rdx, [ rax + 0x0 ]
mulx rbx, r8, [ rsi + 0x10 ]
xor rdx, rdx
adox r14, [ rsp + 0x148 ]
adox rcx, rdx
adcx r10, r14
adc rcx, 0x0
mov r11, r10
shrd r11, rcx, 56
mov r14, r9
xor rcx, rcx
adox r14, [ rsp + 0x108 ]
adox r13, [ rsp + 0x100 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r9, [ rax + 0x0 ]
adcx r14, r9
adcx rcx, r13
mov rdx, [ rsi + 0x10 ]
mulx r9, r13, [ rax + 0x18 ]
xor rdx, rdx
adox r14, rbp
adox r12, rcx
adcx r14, [ rsp + 0x140 ]
adc r12, 0x0
mov rbp, r14
shrd rbp, r12, 56
mov rcx, [ rsp + 0x0 ]
mov r12, rcx
add r12, [ rsp + 0xe8 ]
mov [ rsp + 0x158 ], r11
mov r11, [ rsp - 0x8 ]
adcx r11, [ rsp + 0xe0 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x160 ], r9
mulx r9, rcx, [ rsi + 0x0 ]
test al, al
adox r12, [ rsp + 0x30 ]
adox r11, [ rsp + 0x28 ]
adcx r12, r8
adcx rbx, r11
add r12, [ rsp + 0xa8 ]
adcx rbx, [ rsp + 0xa0 ]
add r12, [ rsp + 0x98 ]
adcx rbx, [ rsp + 0x90 ]
mov rdx, [ rsp + 0xd8 ]
add rdx, [ rsp + 0x30 ]
mov r8, [ rsp + 0xd0 ]
adcx r8, [ rsp + 0x28 ]
mov r11, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x168 ], r8
mov [ rsp + 0x170 ], r9
mulx r9, r8, [ rax + 0x10 ]
add r12, rbp
adc rbx, 0x0
mov rdx, 0x38 
bzhi rbp, r14, rdx
adox rdi, r8
adox r9, r15
mov rdx, [ rsi + 0x8 ]
mulx r14, r15, [ rax + 0x20 ]
test al, al
adox rdi, r13
adox r9, [ rsp + 0x160 ]
adcx rdi, r15
adcx r14, r9
test al, al
adox rdi, rcx
adox r14, [ rsp + 0x170 ]
mov rdx, [ rsi + 0x28 ]
mulx rcx, r13, [ rax + 0x8 ]
mov rdx, [ rsi + 0x30 ]
mulx r15, r8, [ rax + 0x0 ]
adcx rdi, [ rsp + 0x158 ]
adc r14, 0x0
xor rdx, rdx
adox r11, r8
adox r15, [ rsp + 0x168 ]
adcx r11, r13
adcx rcx, r15
mov r9, rdi
shrd r9, r14, 56
mov rdx, [ rax + 0x28 ]
mulx r8, r13, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mulx r15, r14, [ rax + 0x10 ]
xor rdx, rdx
adox r11, r14
adox r15, rcx
adcx r11, [ rsp + 0x50 ]
adcx r15, [ rsp + 0x48 ]
test al, al
adox r11, [ rsp - 0x40 ]
adox r15, [ rsp - 0x48 ]
adcx r11, r13
adcx r8, r15
mov rdx, [ rax + 0x30 ]
mulx r13, rcx, [ rsi + 0x0 ]
add r11, rcx
adcx r13, r8
add r11, r9
adc r13, 0x0
mov rdx, r11
shrd rdx, r13, 56
mov r9, 0x38 
bzhi r14, r11, r9
add rdx, [ rsp + 0x130 ]
bzhi r15, r10, r9
mov r10, r12
shrd r10, rbx, 56
add r10, [ rsp + 0x150 ]
mov rbx, rdx
shr rbx, 56
lea r15, [ r15 + rbx ]
add rbx, [ rsp + 0x138 ]
bzhi r8, rbx, r9
mov rcx, r10
shr rcx, 56
lea rcx, [ rcx + r15 ]
shr rbx, 56
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x0 ], r8
bzhi r13, r12, r9
bzhi r12, rdi, r9
mov rdi, rcx
shr rdi, 56
lea rdi, [ rdi + r12 ]
bzhi r15, r10, r9
mov [ r11 + 0x28 ], rdi
lea rbx, [ rbx + rbp ]
bzhi rbp, rcx, r9
bzhi r10, rdx, r9
mov [ r11 + 0x38 ], r10
mov [ r11 + 0x30 ], r14
mov [ r11 + 0x10 ], r13
mov [ r11 + 0x20 ], rbp
mov [ r11 + 0x18 ], r15
mov [ r11 + 0x8 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 504
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.2829
; seed 0762853763636643 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 8141209 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=109, initial num_batches=31): 213651 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.02624315381167588
; number reverted permutation / tried permutation: 65609 / 90004 =72.896%
; number reverted decision / tried decision: 50063 / 89995 =55.629%
; validated in 5.552s
