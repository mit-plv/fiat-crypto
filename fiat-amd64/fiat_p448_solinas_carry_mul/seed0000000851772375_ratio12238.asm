SECTION .text
	GLOBAL fiat_p448_solinas_carry_mul
fiat_p448_solinas_carry_mul:
sub rsp, 560
mov rax, rdx
mov rdx, [ rsi + 0x20 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rax + 0x30 ]
mulx r8, rcx, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x28 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x28 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x30 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x48 ], r11
mov [ rsp - 0x40 ], r10
mulx r10, r11, [ rsi + 0x28 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x38 ], r10
mov [ rsp - 0x30 ], r11
mulx r11, r10, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], rdi
mov [ rsp - 0x20 ], r15
mulx r15, rdi, [ rax + 0x38 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], r15
mov [ rsp - 0x10 ], rdi
mulx rdi, r15, [ rax + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x8 ], rdi
mov [ rsp + 0x0 ], r15
mulx r15, rdi, [ rax + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x8 ], r15
mov [ rsp + 0x10 ], rdi
mulx rdi, r15, [ rsi + 0x0 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x18 ], rdi
mov [ rsp + 0x20 ], r15
mulx r15, rdi, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x28 ], r15
mov [ rsp + 0x30 ], rdi
mulx rdi, r15, [ rax + 0x20 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x38 ], r11
mov [ rsp + 0x40 ], r10
mulx r10, r11, [ rsi + 0x8 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x48 ], r10
mov [ rsp + 0x50 ], r11
mulx r11, r10, [ rsi + 0x10 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x58 ], rdi
mov [ rsp + 0x60 ], r15
mulx r15, rdi, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x68 ], r15
mov [ rsp + 0x70 ], rdi
mulx rdi, r15, [ rax + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x78 ], rdi
mov [ rsp + 0x80 ], r15
mulx r15, rdi, [ rax + 0x30 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x88 ], r15
mov [ rsp + 0x90 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x98 ], rdi
mov [ rsp + 0xa0 ], r15
mulx r15, rdi, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xa8 ], r15
mov [ rsp + 0xb0 ], rdi
mulx rdi, r15, [ rax + 0x20 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xb8 ], rdi
mov [ rsp + 0xc0 ], r15
mulx r15, rdi, [ rax + 0x28 ]
mov rdx, rdi
mov [ rsp + 0xc8 ], r11
xor r11, r11
adox rdx, rcx
mov [ rsp + 0xd0 ], r10
mov r10, r8
adox r10, r15
mov r11, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0xd8 ], rbx
mov [ rsp + 0xe0 ], r9
mulx r9, rbx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xe8 ], r9
mov [ rsp + 0xf0 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
adcx r11, rbp
mov rdx, r12
adcx rdx, r10
mov r10, r11
mov [ rsp + 0xf8 ], r14
xor r14, r14
adox r10, rdi
adox r15, rdx
adcx r10, rcx
adcx r8, r15
test al, al
adox r10, rbp
adox r12, r8
adcx r11, r9
mov rcx, rbx
adcx rcx, rdx
mov rdx, [ rax + 0x28 ]
mulx rdi, rbp, [ rsi + 0x10 ]
xor rdx, rdx
adox r10, r9
adox rbx, r12
adcx r11, r13
adcx rcx, [ rsp + 0xf8 ]
test al, al
adox r10, r13
adox rbx, [ rsp + 0xf8 ]
mov rdx, [ rax + 0x18 ]
mulx r13, r14, [ rsi + 0x28 ]
adcx r10, r14
mov rdx, r13
adcx rdx, rbx
test al, al
adox r11, r14
adox r13, rcx
mov r9, rdx
mov rdx, [ rax + 0x20 ]
mulx r8, r15, [ rsi + 0x20 ]
mov rdx, [ rax + 0x38 ]
mulx rcx, r12, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x38 ]
mulx r14, rbx, [ rax + 0x30 ]
adcx r10, r15
mov rdx, r8
adcx rdx, r9
add r10, [ rsp + 0xe0 ]
adcx rdx, [ rsp + 0xd8 ]
test al, al
adox r11, r15
adox r8, r13
mov r9, rbx
adcx r9, r12
mov r13, rcx
adcx r13, r14
mov r15, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x100 ], rdi
mov [ rsp + 0x108 ], rbp
mulx rbp, rdi, [ rsi + 0x28 ]
mov rdx, r9
add rdx, rbx
adcx r14, r13
test al, al
adox rdx, r12
adox rcx, r14
adcx r11, [ rsp + 0xe0 ]
adcx r8, [ rsp + 0xd8 ]
mov r12, rdx
mov rdx, [ rsi + 0x38 ]
mulx r14, rbx, [ rax + 0x10 ]
xor rdx, rdx
adox r12, rbx
mov [ rsp + 0x110 ], r15
mov r15, r14
adox r15, rcx
adcx r11, [ rsp + 0xd0 ]
adcx r8, [ rsp + 0xc8 ]
test al, al
adox r9, rbx
adox r14, r13
adcx r9, [ rsp + 0x80 ]
adcx r14, [ rsp + 0x78 ]
mov rdx, [ rax + 0x38 ]
mulx rcx, r13, [ rsi + 0x38 ]
test al, al
adox r12, [ rsp + 0x80 ]
adox r15, [ rsp + 0x78 ]
adcx r9, rdi
mov rdx, rbp
adcx rdx, r14
test al, al
adox r12, rdi
adox rbp, r15
mov rdi, rdx
mov rdx, [ rsi + 0x38 ]
mulx r14, rbx, [ rax + 0x0 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x118 ], rbp
mulx rbp, r15, [ rax + 0x18 ]
mov rdx, r13
adcx rdx, r15
mov [ rsp + 0x120 ], r12
mov r12, rbp
adcx r12, rcx
mov [ rsp + 0x128 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x130 ], r9
mov [ rsp + 0x138 ], r14
mulx r14, r9, [ rax + 0x28 ]
mov rdx, r13
test al, al
adox rdx, r13
adox rcx, rcx
adcx r11, [ rsp + 0x70 ]
adcx r8, [ rsp + 0x68 ]
xor r13, r13
adox r10, [ rsp + 0xd0 ]
mov [ rsp + 0x140 ], rbx
mov rbx, [ rsp + 0x110 ]
adox rbx, [ rsp + 0xc8 ]
adcx rdx, r15
adcx rbp, rcx
mov r15, rdx
mov rdx, [ rax + 0x20 ]
mulx r13, rcx, [ rsi + 0x38 ]
xor rdx, rdx
adox rcx, r9
adox r14, r13
adcx r10, [ rsp + 0x70 ]
adcx rbx, [ rsp + 0x68 ]
mov rdx, [ rax + 0x28 ]
mulx r13, r9, [ rsi + 0x28 ]
test al, al
adox rdi, [ rsp + 0x60 ]
adox r12, [ rsp + 0x58 ]
adcx rdi, r9
mov rdx, r13
adcx rdx, r12
xor r12, r12
adox rcx, [ rsp + 0x40 ]
adox r14, [ rsp + 0x38 ]
mov r12, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x148 ], rbx
mov [ rsp + 0x150 ], r10
mulx r10, rbx, [ rax + 0x38 ]
adcx rcx, rbx
adcx r10, r14
xor rdx, rdx
adox rdi, [ rsp + 0x90 ]
adox r12, [ rsp + 0x88 ]
adcx r11, [ rsp - 0x20 ]
adcx r8, [ rsp - 0x28 ]
mov rdx, [ rsi + 0x30 ]
mulx rbx, r14, [ rax + 0x8 ]
mov rdx, rcx
add rdx, [ rsp + 0x140 ]
mov [ rsp + 0x158 ], r8
mov r8, r10
adcx r8, [ rsp + 0x138 ]
test al, al
adox rdx, r14
adox rbx, r8
mov r14, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x160 ], r11
mulx r11, r8, [ rax + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x168 ], r11
mov [ rsp + 0x170 ], r8
mulx r8, r11, [ rax + 0x0 ]
adcx rcx, r11
adcx r8, r10
xor rdx, rdx
adox r14, [ rsp - 0x30 ]
adox rbx, [ rsp - 0x38 ]
adcx r15, [ rsp + 0x60 ]
adcx rbp, [ rsp + 0x58 ]
mov rdx, [ rsi + 0x30 ]
mulx r11, r10, [ rax + 0x0 ]
add r15, r9
adcx r13, rbp
add r15, [ rsp + 0x90 ]
adcx r13, [ rsp + 0x88 ]
mov rdx, [ rax + 0x10 ]
mulx rbp, r9, [ rsi + 0x8 ]
add r15, [ rsp + 0x30 ]
adcx r13, [ rsp + 0x28 ]
add rdi, [ rsp + 0x30 ]
adcx r12, [ rsp + 0x28 ]
xor rdx, rdx
adox r15, r10
adox r11, r13
mov rdx, [ rax + 0x8 ]
mulx r13, r10, [ rsi + 0x8 ]
adcx rdi, [ rsp + 0x170 ]
adcx r12, [ rsp + 0x168 ]
xor rdx, rdx
adox rcx, [ rsp + 0xa0 ]
adox r8, [ rsp + 0x98 ]
adcx rdi, r10
adcx r13, r12
add rcx, r9
adcx rbp, r8
xor r9, r9
adox rcx, [ rsp + 0x20 ]
adox rbp, [ rsp + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mulx r12, r10, [ rax + 0x30 ]
mov rdx, [ rsi + 0x20 ]
mulx r9, r8, [ rax + 0x18 ]
adcx r14, r8
adcx r9, rbx
mov rdx, [ rax + 0x20 ]
mulx r8, rbx, [ rsi + 0x18 ]
test al, al
adox r14, rbx
adox r8, r9
mov rdx, [ rax + 0x8 ]
mulx rbx, r9, [ rsi + 0x28 ]
mov rdx, 0x38 
mov [ rsp + 0x178 ], r13
bzhi r13, rcx, rdx
adox r14, [ rsp + 0x108 ]
adox r8, [ rsp + 0x100 ]
shrd rcx, rbp, 56
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x180 ], r13
mulx r13, rbp, [ rsi + 0x20 ]
add r15, r9
adcx rbx, r11
xor rdx, rdx
adox r15, rbp
adox r13, rbx
mov r11, [ rsp + 0x150 ]
adcx r11, [ rsp - 0x40 ]
mov r9, [ rsp + 0x148 ]
adcx r9, [ rsp - 0x48 ]
test al, al
adox r11, [ rsp + 0xf0 ]
adox r9, [ rsp + 0xe8 ]
mov rdx, [ rax + 0x28 ]
mulx rbx, rbp, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x188 ], r13
mov [ rsp + 0x190 ], r15
mulx r15, r13, [ rax + 0x38 ]
adcx r14, r10
adcx r12, r8
mov rdx, [ rax + 0x18 ]
mulx r8, r10, [ rsi + 0x8 ]
add r14, r13
adcx r15, r12
mov rdx, [ rsi + 0x0 ]
mulx r12, r13, [ rax + 0x20 ]
xor rdx, rdx
adox r11, [ rsp + 0x10 ]
adox r9, [ rsp + 0x8 ]
adcx r11, r10
adcx r8, r9
xor r10, r10
adox r11, r13
adox r12, r8
mov rdx, r14
shrd rdx, r15, 56
add r11, rcx
adc r12, 0x0
mov rcx, rdx
test al, al
adox rcx, r11
adox r12, r10
mov r15, rbp
adcx r15, [ rsp + 0x130 ]
mov r13, rbx
adcx r13, [ rsp + 0x128 ]
mov r9, 0x38 
bzhi r8, rcx, r9
bzhi r11, r14, r9
shrd rcx, r12, 56
mov r14, rbp
add r14, [ rsp + 0x120 ]
adcx rbx, [ rsp + 0x118 ]
mov rbp, rdx
mov rdx, [ rsi + 0x8 ]
mulx r10, r12, [ rax + 0x20 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x198 ], r8
mulx r8, r9, [ rsi + 0x8 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x1a0 ], r11
mov [ rsp + 0x1a8 ], rdi
mulx rdi, r11, [ rsi + 0x18 ]
add r14, r11
mov rdx, rdi
adcx rdx, rbx
add r14, [ rsp - 0x10 ]
adcx rdx, [ rsp - 0x18 ]
add r15, r11
adcx rdi, r13
mov r13, rdx
mov rdx, [ rax + 0x0 ]
mulx r11, rbx, [ rsi + 0x28 ]
add r15, [ rsp - 0x10 ]
adcx rdi, [ rsp - 0x18 ]
test al, al
adox r14, rbx
adox r11, r13
adcx r14, [ rsp + 0xb0 ]
adcx r11, [ rsp + 0xa8 ]
xor rdx, rdx
adox r14, [ rsp + 0x0 ]
adox r11, [ rsp - 0x8 ]
mov rdx, [ rax + 0x18 ]
mulx rbx, r13, [ rsi + 0x10 ]
adcx r14, r13
adcx rbx, r11
mov rdx, [ rsi + 0x0 ]
mulx r13, r11, [ rax + 0x8 ]
xor rdx, rdx
adox r14, r12
adox r10, rbx
adcx r15, r9
adcx r8, rdi
mov rdx, [ rax + 0x10 ]
mulx r9, r12, [ rsi + 0x0 ]
test al, al
adox r15, r11
adox r13, r8
adcx rbp, [ rsp + 0x160 ]
mov rdx, [ rsp + 0x158 ]
adc rdx, 0x0
mov rdi, rdx
mov rdx, [ rax + 0x28 ]
mulx r11, rbx, [ rsi + 0x0 ]
add r14, rbx
adcx r11, r10
add r14, rcx
adc r11, 0x0
mov rdx, rbp
shrd rdx, rdi, 56
mov rcx, r12
add rcx, [ rsp + 0x1a8 ]
adcx r9, [ rsp + 0x178 ]
add r15, rdx
adc r13, 0x0
mov r10, r14
shrd r10, r11, 56
mov rdx, [ rsi + 0x18 ]
mulx r12, r8, [ rax + 0x18 ]
mov rdx, r8
add rdx, [ rsp + 0x190 ]
adcx r12, [ rsp + 0x188 ]
xor rdi, rdi
adox rdx, [ rsp + 0xc0 ]
adox r12, [ rsp + 0xb8 ]
adcx rdx, [ rsp + 0x50 ]
adcx r12, [ rsp + 0x48 ]
mov rbx, r15
shrd rbx, r13, 56
mov r11, rdx
mov rdx, [ rsi + 0x0 ]
mulx r8, r13, [ rax + 0x30 ]
add rcx, rbx
adc r9, 0x0
mov rdx, 0x38 
bzhi rbx, rcx, rdx
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x10 ], rbx
shrd rcx, r9, 56
test al, al
adox r11, r13
adox r8, r12
adcx r11, r10
adc r8, 0x0
mov r10, r11
shrd r10, r8, 56
add r10, [ rsp + 0x1a0 ]
add rcx, [ rsp + 0x180 ]
mov r12, r10
shr r12, 56
bzhi r13, r11, rdx
bzhi r9, r10, rdx
mov [ rdi + 0x30 ], r13
bzhi rbx, rcx, rdx
mov [ rdi + 0x18 ], rbx
bzhi r11, rbp, rdx
mov [ rdi + 0x38 ], r9
lea r11, [ r11 + r12 ]
bzhi rbp, r11, rdx
shr rcx, 56
add r12, [ rsp + 0x198 ]
lea rcx, [ rcx + r12 ]
bzhi r8, r15, rdx
bzhi r15, rcx, rdx
mov [ rdi + 0x20 ], r15
bzhi r10, r14, rdx
shr r11, 56
lea r11, [ r11 + r8 ]
shr rcx, 56
lea rcx, [ rcx + r10 ]
mov [ rdi + 0x28 ], rcx
mov [ rdi + 0x8 ], r11
mov [ rdi + 0x0 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 560
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.2238
; seed 4241218557479214 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 6098104 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=61, initial num_batches=31): 134799 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.022105067411116636
; number reverted permutation / tried permutation: 63736 / 89947 =70.860%
; number reverted decision / tried decision: 49864 / 90052 =55.372%
; validated in 4.696s
