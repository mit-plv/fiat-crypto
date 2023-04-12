SECTION .text
	GLOBAL fiat_p448_solinas_carry_mul
fiat_p448_solinas_carry_mul:
sub rsp, 552
mov rax, rdx
mov rdx, [ rdx + 0x38 ]
mulx r11, r10, [ rsi + 0x20 ]
mov rdx, [ rax + 0x38 ]
mulx r8, rcx, [ rsi + 0x38 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x28 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x48 ], r12
mov [ rsp - 0x40 ], rbp
mulx rbp, r12, [ rsi + 0x20 ]
mov rdx, rcx
test al, al
adox rdx, rcx
mov [ rsp - 0x38 ], rdi
mov rdi, r8
adox rdi, r8
mov [ rsp - 0x30 ], r15
mov r15, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x28 ], r14
mov [ rsp - 0x20 ], r13
mulx r13, r14, [ rsi + 0x0 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x18 ], r13
mov [ rsp - 0x10 ], r14
mulx r14, r13, [ rsi + 0x20 ]
adcx rcx, r9
mov rdx, rbx
adcx rdx, r8
mov r8, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x8 ], rcx
mov [ rsp + 0x0 ], rbp
mulx rbp, rcx, [ rax + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x8 ], r8
mov [ rsp + 0x10 ], r12
mulx r12, r8, [ rax + 0x30 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x18 ], r12
mov [ rsp + 0x20 ], r8
mulx r8, r12, [ rsi + 0x38 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x28 ], r14
mov [ rsp + 0x30 ], r13
mulx r13, r14, [ rsi + 0x8 ]
xor rdx, rdx
adox r15, r9
adox rbx, rdi
mov rdx, [ rsi + 0x30 ]
mulx rdi, r9, [ rax + 0x30 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x38 ], r13
mov [ rsp + 0x40 ], r14
mulx r14, r13, [ rsi + 0x28 ]
mov rdx, r12
adcx rdx, r9
mov [ rsp + 0x48 ], rbx
mov rbx, rdi
adcx rbx, r8
mov [ rsp + 0x50 ], r15
xor r15, r15
adox rdx, r13
mov [ rsp + 0x58 ], rbp
mov rbp, r14
adox rbp, rbx
mov rbx, rdx
adcx rbx, r12
adcx r8, rbp
xor r12, r12
adox rbx, r9
adox rdi, r8
mov r15, rdx
mov rdx, [ rax + 0x8 ]
mulx r8, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x60 ], r8
mulx r8, r12, [ rax + 0x18 ]
adcx rbx, r13
adcx r14, rdi
mov rdx, [ rax + 0x8 ]
mulx rdi, r13, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x68 ], r8
mov [ rsp + 0x70 ], r12
mulx r12, r8, [ rax + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x78 ], r9
mov [ rsp + 0x80 ], rcx
mulx rcx, r9, [ rax + 0x30 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x88 ], r11
mov [ rsp + 0x90 ], r10
mulx r10, r11, [ rsi + 0x38 ]
xor rdx, rdx
adox r11, r8
adox r12, r10
adcx rbx, r13
mov r8, rdi
adcx r8, r14
test al, al
adox r11, r9
adox rcx, r12
mov rdx, [ rsi + 0x30 ]
mulx r9, r14, [ rax + 0x10 ]
mov rdx, [ rsi + 0x38 ]
mulx r12, r10, [ rax + 0x30 ]
adcx r15, r13
adcx rdi, rbp
add r11, [ rsp + 0x90 ]
adcx rcx, [ rsp + 0x88 ]
mov rdx, [ rsi + 0x30 ]
mulx r13, rbp, [ rax + 0x38 ]
mov rdx, r10
mov [ rsp + 0x98 ], r8
xor r8, r8
adox rdx, rbp
mov [ rsp + 0xa0 ], rbx
mov rbx, r13
adox rbx, r12
mov r8, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xa8 ], rcx
mov [ rsp + 0xb0 ], r11
mulx r11, rcx, [ rax + 0x10 ]
adcx r15, r14
mov rdx, r9
adcx rdx, rdi
mov rdi, r8
mov [ rsp + 0xb8 ], rdx
xor rdx, rdx
adox rdi, r10
adox r12, rbx
adcx r8, rcx
mov r10, r11
adcx r10, rbx
add rdi, rbp
adcx r13, r12
xor rbp, rbp
adox rdi, rcx
adox r11, r13
mov rdx, [ rax + 0x18 ]
mulx rcx, rbx, [ rsi + 0x30 ]
adcx rdi, rbx
mov rdx, rcx
adcx rdx, r11
mov r12, rdx
mov rdx, [ rax + 0x20 ]
mulx r11, r13, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xc0 ], r15
mulx r15, rbp, [ rax + 0x28 ]
add rdi, r13
mov rdx, r11
adcx rdx, r12
test al, al
adox r8, rbx
adox rcx, r10
adcx r8, r13
adcx r11, rcx
mov r10, rdx
mov rdx, [ rsi + 0x38 ]
mulx r12, rbx, [ rax + 0x0 ]
mov rdx, [ rsi + 0x30 ]
mulx rcx, r13, [ rax + 0x8 ]
mov rdx, rbx
mov [ rsp + 0xc8 ], r10
xor r10, r10
adox rdx, [ rsp + 0xb0 ]
adox r12, [ rsp + 0xa8 ]
adcx rdx, r13
adcx rcx, r12
add r8, rbp
mov rbx, r15
adcx rbx, r11
mov r11, rdx
mov rdx, [ rsi + 0x18 ]
mulx r12, r13, [ rax + 0x30 ]
add r8, r13
mov rdx, r12
adcx rdx, rbx
xor rbx, rbx
adox rdi, rbp
adox r15, [ rsp + 0xc8 ]
adcx rdi, r13
adcx r12, r15
mov r10, rdx
mov rdx, [ rsi + 0x10 ]
mulx r13, rbp, [ rax + 0x38 ]
mov rdx, [ rsi + 0x28 ]
mulx rbx, r15, [ rax + 0x18 ]
mov rdx, r14
test al, al
adox rdx, [ rsp + 0xa0 ]
adox r9, [ rsp + 0x98 ]
adcx r8, rbp
mov r14, r13
adcx r14, r10
xor r10, r10
adox rdi, rbp
adox r13, r12
mov r12, rdx
mov rdx, [ rax + 0x20 ]
mulx r10, rbp, [ rsi + 0x18 ]
adcx r11, [ rsp + 0x80 ]
adcx rcx, [ rsp + 0x58 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xd0 ], r13
mov [ rsp + 0xd8 ], rdi
mulx rdi, r13, [ rax + 0x38 ]
mov rdx, r15
add rdx, [ rsp + 0xc0 ]
mov [ rsp + 0xe0 ], r14
mov r14, rbx
adcx r14, [ rsp + 0xb8 ]
test al, al
adox r12, r15
adox rbx, r9
adcx r12, [ rsp + 0x30 ]
adcx rbx, [ rsp + 0x28 ]
xor r15, r15
adox rdx, [ rsp + 0x30 ]
adox r14, [ rsp + 0x28 ]
adcx r11, [ rsp + 0x10 ]
adcx rcx, [ rsp + 0x0 ]
xor r9, r9
adox r11, rbp
adox r10, rcx
adcx r12, [ rsp - 0x20 ]
adcx rbx, [ rsp - 0x28 ]
test al, al
adox r11, [ rsp - 0x30 ]
adox r10, [ rsp - 0x38 ]
mov r15, rdx
mov rdx, [ rax + 0x30 ]
mulx rcx, rbp, [ rsi + 0x8 ]
adcx r15, [ rsp - 0x20 ]
adcx r14, [ rsp - 0x28 ]
add r11, rbp
adcx rcx, r10
add r15, [ rsp + 0x20 ]
adcx r14, [ rsp + 0x18 ]
add r15, r13
mov rdx, rdi
adcx rdx, r14
test al, al
adox r12, [ rsp + 0x20 ]
adox rbx, [ rsp + 0x18 ]
mov r10, rdx
mov rdx, [ rax + 0x38 ]
mulx r14, rbp, [ rsi + 0x0 ]
adcx r12, r13
adcx rdi, rbx
mov rdx, [ rax + 0x20 ]
mulx rbx, r13, [ rsi + 0x30 ]
mov rdx, r13
add rdx, [ rsp - 0x8 ]
mov [ rsp + 0xe8 ], rdi
mov rdi, rbx
adcx rdi, [ rsp + 0x8 ]
mov [ rsp + 0xf0 ], r12
mov r12, r13
mov [ rsp + 0xf8 ], r8
xor r8, r8
adox r12, [ rsp + 0x50 ]
adox rbx, [ rsp + 0x48 ]
mov r9, rdx
mov rdx, [ rsi + 0x28 ]
mulx r8, r13, [ rax + 0x28 ]
adcx r11, rbp
adcx r14, rcx
xor rdx, rdx
adox r12, r13
mov rcx, r8
adox rcx, rbx
adcx r9, r13
adcx r8, rdi
mov rbp, 0xffffffffffffff 
mov rdi, r11
and rdi, rbp
mov rdx, [ rax + 0x0 ]
mulx r13, rbx, [ rsi + 0x0 ]
shrd r11, r14, 56
mov rdx, [ rax + 0x30 ]
mulx rbp, r14, [ rsi + 0x20 ]
add r15, rbx
adcx r13, r10
mov rdx, [ rax + 0x0 ]
mulx rbx, r10, [ rsi + 0x8 ]
mov rdx, r10
mov [ rsp + 0x100 ], rdi
xor rdi, rdi
adox rdx, [ rsp + 0xf8 ]
adox rbx, [ rsp + 0xe0 ]
mov r10, r11
adcx r10, r15
adc r13, 0x0
mov r15, rdx
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x108 ], rbx
mulx rbx, rdi, [ rsi + 0x18 ]
mov rdx, 0xffffffffffffff 
mov [ rsp + 0x110 ], r15
mov r15, r10
and r15, rdx
shrd r10, r13, 56
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x118 ], r15
mulx r15, r13, [ rsi + 0x18 ]
xor rdx, rdx
adox r12, r14
mov [ rsp + 0x120 ], r15
mov r15, rbp
adox r15, rcx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x128 ], r13
mulx r13, rcx, [ rsi + 0x20 ]
adcx r9, r14
adcx rbp, r8
test al, al
adox r9, rdi
mov rdx, rbx
adox rdx, rbp
adcx r12, rdi
adcx rbx, r15
xor r8, r8
adox r9, [ rsp - 0x40 ]
adox rdx, [ rsp - 0x48 ]
mov r14, rdx
mov rdx, [ rax + 0x10 ]
mulx r15, rdi, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rbp, [ rax + 0x8 ]
mov rdx, rbp
adcx rdx, [ rsp + 0x110 ]
adcx r8, [ rsp + 0x108 ]
xor rbp, rbp
adox rdx, r10
adox r8, rbp
mov r10, rdx
shrd r10, r8, 56
mov r8, [ rsp + 0x128 ]
mov [ rsp + 0x130 ], r15
mov r15, r8
mov [ rsp + 0x138 ], rdi
xor rdi, rdi
adox r15, [ rsp + 0xb0 ]
mov rbp, [ rsp + 0x120 ]
adox rbp, [ rsp + 0xa8 ]
mov r8, rcx
adcx r8, [ rsp + 0xf0 ]
adcx r13, [ rsp + 0xe8 ]
mov rcx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x140 ], r13
mulx r13, rdi, [ rax + 0x8 ]
test al, al
adox r9, [ rsp + 0x40 ]
adox r14, [ rsp + 0x38 ]
adcx r9, [ rsp - 0x10 ]
adcx r14, [ rsp - 0x18 ]
test al, al
adox r9, r10
mov rdx, 0x0 
adox r14, rdx
adcx r15, rdi
adcx r13, rbp
mov rdx, [ rsi + 0x8 ]
mulx rbp, r10, [ rax + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x148 ], r8
mulx r8, rdi, [ rsi + 0x28 ]
mov rdx, 0xffffffffffffff 
and rcx, rdx
adox r15, r10
adox rbp, r13
mov rdx, [ rax + 0x0 ]
mulx r10, r13, [ rsi + 0x30 ]
mov rdx, 0x38 
mov [ rsp + 0x150 ], rcx
bzhi rcx, r9, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x158 ], rbp
mov [ rsp + 0x160 ], r15
mulx r15, rbp, [ rsi + 0x28 ]
shrd r9, r14, 56
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x10 ], rcx
test al, al
adox r12, r13
adox r10, rbx
mov rbx, rdx
mov rdx, [ rax + 0x18 ]
mulx r13, r14, [ rsi + 0x18 ]
adcx r12, rdi
adcx r8, r10
test al, al
adox r12, [ rsp + 0x138 ]
adox r8, [ rsp + 0x130 ]
mov rdx, [ rsp + 0x78 ]
mov rdi, rdx
adcx rdi, [ rsp + 0x148 ]
mov rcx, [ rsp + 0x60 ]
adcx rcx, [ rsp + 0x140 ]
mov rdx, [ rax + 0x28 ]
mulx rbx, r10, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x168 ], r9
mov [ rsp + 0x170 ], rbx
mulx rbx, r9, [ rax + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x178 ], r10
mov [ rsp + 0x180 ], r15
mulx r15, r10, [ rax + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x188 ], rbp
mov [ rsp + 0x190 ], rbx
mulx rbx, rbp, [ rax + 0x18 ]
test al, al
adox r12, r14
adox r13, r8
mov rdx, [ rax + 0x20 ]
mulx r8, r14, [ rsi + 0x8 ]
mov rdx, rbp
adcx rdx, [ rsp + 0x160 ]
adcx rbx, [ rsp + 0x158 ]
mov rbp, rdx
shrd rbp, rbx, 56
mov [ rsp + 0x198 ], r8
mov r8, 0x38 
mov [ rsp + 0x1a0 ], r14
bzhi r14, rdx, r8
mov rdx, [ rsi + 0x0 ]
mulx r8, rbx, [ rax + 0x28 ]
adox rdi, r10
adox r15, rcx
mov rdx, [ rsi + 0x0 ]
mulx r10, rcx, [ rax + 0x20 ]
test al, al
adox rdi, r9
adox r15, [ rsp + 0x190 ]
adcx rdi, rcx
adcx r10, r15
mov rdx, [ rsi + 0x20 ]
mulx rcx, r9, [ rax + 0x8 ]
add rdi, rbp
adc r10, 0x0
xor rdx, rdx
adox r11, rdi
adox r10, rdx
mov rdx, [ rsi + 0x10 ]
mulx r15, rbp, [ rax + 0x20 ]
adcx r12, rbp
adcx r15, r13
mov rdx, [ rsp + 0xd8 ]
add rdx, [ rsp + 0x188 ]
mov r13, [ rsp + 0xd0 ]
adcx r13, [ rsp + 0x180 ]
mov rdi, r11
shrd rdi, r10, 56
xor r10, r10
adox rdx, r9
adox rcx, r13
mov r9, 0x38 
bzhi rbp, r11, r9
mov r11, rdx
mov rdx, [ rsi + 0x18 ]
mulx r10, r13, [ rax + 0x10 ]
adox r11, r13
adox r10, rcx
test al, al
adox r11, [ rsp + 0x70 ]
adox r10, [ rsp + 0x68 ]
adcx r11, [ rsp + 0x1a0 ]
adcx r10, [ rsp + 0x198 ]
test al, al
adox r11, rbx
adox r8, r10
adcx r12, [ rsp + 0x178 ]
adcx r15, [ rsp + 0x170 ]
mov rdx, [ rax + 0x30 ]
mulx rcx, rbx, [ rsi + 0x0 ]
xor rdx, rdx
adox r12, rbx
adox rcx, r15
adcx r11, rdi
adc r8, 0x0
mov rdi, r11
shrd rdi, r8, 56
test al, al
adox r12, rdi
adox rcx, rdx
mov r13, r12
shrd r13, rcx, 56
add r13, [ rsp + 0x100 ]
bzhi r10, r11, r9
bzhi r15, r13, r9
shr r13, 56
add r14, [ rsp + 0x168 ]
lea rbp, [ rbp + r13 ]
bzhi rbx, r14, r9
add r13, [ rsp + 0x118 ]
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x18 ], rbx
bzhi r8, r13, r9
shr r13, 56
shr r14, 56
mov [ r11 + 0x0 ], r8
lea r14, [ r14 + rbp ]
bzhi rdi, r14, r9
add r13, [ rsp + 0x150 ]
mov [ r11 + 0x8 ], r13
bzhi rbp, r12, r9
shr r14, 56
mov [ r11 + 0x20 ], rdi
lea r14, [ r14 + r10 ]
mov [ r11 + 0x38 ], r15
mov [ r11 + 0x28 ], r14
mov [ r11 + 0x30 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 552
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.0833
; seed 2305302204777095 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5359945 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=87, initial num_batches=31): 140639 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.026238888645312593
; number reverted permutation / tried permutation: 58425 / 89480 =65.294%
; number reverted decision / tried decision: 33985 / 90519 =37.545%
; validated in 3.329s
