SECTION .text
	GLOBAL fiat_p448_solinas_carry_mul
fiat_p448_solinas_carry_mul:
sub rsp, 688
mov rax, rdx
mov rdx, [ rdx + 0x38 ]
mulx r11, r10, [ rsi + 0x30 ]
mov rdx, [ rax + 0x18 ]
mulx r8, rcx, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x38 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x48 ], rbx
mov [ rsp - 0x40 ], r9
mulx r9, rbx, [ rax + 0x8 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x38 ], rdi
mov [ rsp - 0x30 ], r15
mulx r15, rdi, [ rsi + 0x38 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x28 ], r12
mov [ rsp - 0x20 ], rbp
mulx rbp, r12, [ rsi + 0x28 ]
mov rdx, rdi
test al, al
adox rdx, rdi
mov [ rsp - 0x18 ], r9
mov r9, r15
adox r9, r15
adcx rdx, rcx
mov [ rsp - 0x10 ], rbx
mov rbx, r8
adcx rbx, r9
mov r9, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x8 ], rbx
mov [ rsp + 0x0 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x8 ], rbp
mov [ rsp + 0x10 ], rbx
mulx rbx, rbp, [ rax + 0x30 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x18 ], r9
mov [ rsp + 0x20 ], r12
mulx r12, r9, [ rax + 0x30 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x28 ], r12
mov [ rsp + 0x30 ], r9
mulx r9, r12, [ rsi + 0x28 ]
mov rdx, rbp
mov [ rsp + 0x38 ], r9
xor r9, r9
adox rdx, r10
mov [ rsp + 0x40 ], r12
mov r12, r11
adox r12, rbx
adcx rdi, rcx
adcx r8, r15
mov rcx, rdx
mov rdx, [ rax + 0x10 ]
mulx r9, r15, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x48 ], r9
mov [ rsp + 0x50 ], r15
mulx r15, r9, [ rax + 0x20 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x58 ], r15
mov [ rsp + 0x60 ], r9
mulx r9, r15, [ rsi + 0x38 ]
mov rdx, rcx
mov [ rsp + 0x68 ], r8
xor r8, r8
adox rdx, rbp
adox rbx, r12
adcx rdx, r10
adcx r11, rbx
mov r10, rdx
mov rdx, [ rsi + 0x18 ]
mulx rbx, rbp, [ rax + 0x38 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x70 ], rbx
mulx rbx, r8, [ rsi + 0x38 ]
test al, al
adox r10, r15
mov rdx, r9
adox rdx, r11
mov r11, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x78 ], rbp
mov [ rsp + 0x80 ], rdi
mulx rdi, rbp, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x88 ], r11
mov [ rsp + 0x90 ], r10
mulx r10, r11, [ rax + 0x0 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x98 ], r10
mov [ rsp + 0xa0 ], r11
mulx r11, r10, [ rax + 0x30 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xa8 ], rdi
mov [ rsp + 0xb0 ], rbp
mulx rbp, rdi, [ rax + 0x20 ]
mov rdx, r8
adcx rdx, r10
mov [ rsp + 0xb8 ], rbp
mov rbp, r11
adcx rbp, rbx
mov [ rsp + 0xc0 ], rdi
xor rdi, rdi
adox rdx, r13
mov [ rsp + 0xc8 ], rbx
mov rbx, r14
adox rbx, rbp
adcx rcx, r15
adcx r9, r12
xor r12, r12
adox rcx, [ rsp + 0xb0 ]
adox r9, [ rsp + 0xa8 ]
mov rdi, rdx
mov rdx, [ rax + 0x8 ]
mulx rbp, r15, [ rsi + 0x38 ]
mov rdx, rdi
adcx rdx, r8
mov [ rsp + 0xd0 ], r9
mov r9, rbx
adcx r9, [ rsp + 0xc8 ]
xor r8, r8
adox rdx, r10
adox r11, r9
adcx rdx, r13
adcx r14, r11
mov r12, rdx
mov rdx, [ rsi + 0x30 ]
mulx r10, r13, [ rax + 0x28 ]
test al, al
adox r12, r15
mov rdx, rbp
adox rdx, r14
mov r9, rdx
mov rdx, [ rax + 0x20 ]
mulx r14, r11, [ rsi + 0x38 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0xd8 ], rcx
mulx rcx, r8, [ rsi + 0x28 ]
adcx rdi, r15
adcx rbp, rbx
mov rdx, [ rax + 0x20 ]
mulx r15, rbx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xe0 ], r15
mov [ rsp + 0xe8 ], rbx
mulx rbx, r15, [ rax + 0x10 ]
test al, al
adox r12, r15
mov rdx, rbx
adox rdx, r9
adcx rdi, r15
adcx rbx, rbp
xor r9, r9
adox rdi, r8
mov rbp, rcx
adox rbp, rbx
adcx r11, r13
adcx r10, r14
mov r13, rdx
mov rdx, [ rsi + 0x18 ]
mulx r15, r14, [ rax + 0x28 ]
add rdi, [ rsp + 0xe8 ]
adcx rbp, [ rsp + 0xe0 ]
xor rdx, rdx
adox r12, r8
adox rcx, r13
adcx rdi, r14
mov r9, r15
adcx r9, rbp
xor r8, r8
adox r12, [ rsp + 0xe8 ]
adox rcx, [ rsp + 0xe0 ]
mov rdx, [ rax + 0x30 ]
mulx rbx, r13, [ rsi + 0x10 ]
adcx r12, r14
adcx r15, rcx
mov rdx, [ rsp + 0x90 ]
xor r14, r14
adox rdx, [ rsp + 0xb0 ]
mov r8, [ rsp + 0x88 ]
adox r8, [ rsp + 0xa8 ]
adcx r12, r13
mov rbp, rbx
adcx rbp, r15
mov rcx, rdx
mov rdx, [ rax + 0x38 ]
mulx r14, r15, [ rsi + 0x20 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0xf0 ], rbp
mov [ rsp + 0xf8 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
test al, al
adox r11, [ rsp + 0x20 ]
adox r10, [ rsp + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x100 ], r9
mov [ rsp + 0x108 ], rdi
mulx rdi, r9, [ rsi + 0x20 ]
adcx r11, r15
adcx r14, r10
add rcx, [ rsp + 0x40 ]
adcx r8, [ rsp + 0x38 ]
mov rdx, [ rax + 0x0 ]
mulx r10, r15, [ rsi + 0x38 ]
mov rdx, r11
test al, al
adox rdx, r15
adox r10, r14
adcx rdx, [ rsp - 0x10 ]
adcx r10, [ rsp - 0x18 ]
test al, al
adox r11, rbp
adox r12, r14
mov rbp, rdx
mov rdx, [ rax + 0x10 ]
mulx r15, r14, [ rsi + 0x28 ]
adcx rbp, r14
adcx r15, r10
mov rdx, [ rax + 0x20 ]
mulx r14, r10, [ rsi + 0x30 ]
mov rdx, r10
add rdx, [ rsp + 0x80 ]
mov [ rsp + 0x110 ], r8
mov r8, r14
adcx r8, [ rsp + 0x68 ]
mov [ rsp + 0x118 ], rcx
xor rcx, rcx
adox rbp, r9
adox rdi, r15
mov r9, rdx
mov rdx, [ rax + 0x28 ]
mulx rcx, r15, [ rsi + 0x10 ]
mov rdx, r13
adcx rdx, [ rsp + 0x108 ]
adcx rbx, [ rsp + 0x100 ]
mov r13, r10
mov [ rsp + 0x120 ], r12
xor r12, r12
adox r13, [ rsp + 0x18 ]
adox r14, [ rsp - 0x8 ]
mov r10, [ rsp + 0x40 ]
mov [ rsp + 0x128 ], r14
mov r14, r10
adcx r14, [ rsp + 0xd8 ]
mov [ rsp + 0x130 ], r13
mov r13, [ rsp + 0x38 ]
adcx r13, [ rsp + 0xd0 ]
xor r10, r10
adox rbp, [ rsp - 0x20 ]
adox rdi, [ rsp - 0x28 ]
mov r12, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x138 ], r13
mulx r13, r10, [ rax + 0x30 ]
adcx rbp, r15
adcx rcx, rdi
mov rdx, [ rax + 0x28 ]
mulx rdi, r15, [ rsi + 0x20 ]
xor rdx, rdx
adox r12, [ rsp - 0x30 ]
adox rbx, [ rsp - 0x38 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x140 ], rbx
mov [ rsp + 0x148 ], r12
mulx r12, rbx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x150 ], r14
mov [ rsp + 0x158 ], rdi
mulx rdi, r14, [ rax + 0x30 ]
adcx r9, rbx
mov rdx, r12
adcx rdx, r8
mov r8, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x160 ], r15
mov [ rsp + 0x168 ], r9
mulx r9, r15, [ rax + 0x8 ]
add r11, r15
adcx r9, [ rsp + 0x120 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x170 ], r9
mulx r9, r15, [ rax + 0x0 ]
test al, al
adox rbp, r10
adox r13, rcx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r10, [ rax + 0x38 ]
adcx rbp, r10
adcx rcx, r13
mov rdx, rbp
shrd rdx, rcx, 56
mov r13, r14
xor r10, r10
adox r13, [ rsp + 0x168 ]
mov rcx, rdi
adox rcx, r8
adcx r13, [ rsp + 0x78 ]
adcx rcx, [ rsp + 0x70 ]
mov r8, rbx
mov [ rsp + 0x178 ], rdx
xor rdx, rdx
adox r8, [ rsp + 0x130 ]
adox r12, [ rsp + 0x128 ]
adcx r8, r14
adcx rdi, r12
test al, al
adox r13, r15
adox r9, rcx
mov r10, [ rsp + 0x160 ]
mov rbx, r10
adcx rbx, [ rsp + 0x150 ]
mov r14, [ rsp + 0x158 ]
mov r15, r14
adcx r15, [ rsp + 0x138 ]
add rbx, [ rsp + 0x30 ]
adcx r15, [ rsp + 0x28 ]
mov rcx, r10
add rcx, [ rsp + 0x118 ]
adcx r14, [ rsp + 0x110 ]
mov rdx, [ rsi + 0x10 ]
mulx r12, r10, [ rax + 0x38 ]
mov rdx, 0x38 
mov [ rsp + 0x180 ], r11
bzhi r11, rbp, rdx
adox rcx, [ rsp + 0x30 ]
adox r14, [ rsp + 0x28 ]
test al, al
adox rbx, r10
mov rbp, r12
adox rbp, r15
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x188 ], r11
mulx r11, r15, [ rax + 0x0 ]
adcx rcx, r10
adcx r12, r14
test al, al
adox rbx, r15
adox r11, rbp
mov rdx, [ rax + 0x0 ]
mulx r14, r10, [ rsi + 0x28 ]
adcx rcx, r10
adcx r14, r12
mov rdx, [ rsi + 0x28 ]
mulx r15, rbp, [ rax + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx r10, r12, [ rax + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x190 ], r10
mov [ rsp + 0x198 ], r12
mulx r12, r10, [ rax + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x1a0 ], r15
mov [ rsp + 0x1a8 ], rbp
mulx rbp, r15, [ rsi + 0x20 ]
add rcx, r15
adcx rbp, r14
test al, al
adox rcx, [ rsp + 0x50 ]
adox rbp, [ rsp + 0x48 ]
mov rdx, [ rsi + 0x8 ]
mulx r15, r14, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x1b0 ], rbp
mov [ rsp + 0x1b8 ], rcx
mulx rcx, rbp, [ rsi + 0x8 ]
adcx r13, r14
adcx r15, r9
add rbx, [ rsp - 0x40 ]
adcx r11, [ rsp - 0x48 ]
mov rdx, [ rsi + 0x20 ]
mulx r14, r9, [ rax + 0x0 ]
mov rdx, [ rsp + 0x10 ]
mov [ rsp + 0x1c0 ], r15
mov r15, rdx
test al, al
adox r15, [ rsp + 0x148 ]
mov [ rsp + 0x1c8 ], r13
mov r13, [ rsp + 0x8 ]
adox r13, [ rsp + 0x140 ]
adcx r8, [ rsp + 0x78 ]
adcx rdi, [ rsp + 0x70 ]
mov rdx, rbp
add rdx, [ rsp + 0x180 ]
adcx rcx, [ rsp + 0x170 ]
mov rbp, [ rsp - 0x30 ]
mov [ rsp + 0x1d0 ], rcx
mov rcx, rbp
test al, al
adox rcx, [ rsp + 0xf8 ]
mov [ rsp + 0x1d8 ], rdx
mov rdx, [ rsp - 0x38 ]
adox rdx, [ rsp + 0xf0 ]
mov rbp, r15
adcx rbp, [ rsp + 0x178 ]
adc r13, 0x0
add rcx, r9
adcx r14, rdx
xor r9, r9
adox rcx, r10
adox r12, r14
adcx r8, [ rsp + 0xa0 ]
adcx rdi, [ rsp + 0x98 ]
mov r10, rbp
shrd r10, r13, 56
test al, al
adox rbx, r10
adox r11, r9
adcx r8, [ rsp + 0x1a8 ]
adcx rdi, [ rsp + 0x1a0 ]
mov rdx, [ rsi + 0x8 ]
mulx r13, r15, [ rax + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mulx r10, r14, [ rax + 0x10 ]
mov rdx, rbx
shrd rdx, r11, 56
mov r11, [ rsp + 0x1c8 ]
mov [ rsp + 0x1e0 ], rdi
xor rdi, rdi
adox r11, [ rsp + 0x198 ]
mov r9, [ rsp + 0x1c0 ]
adox r9, [ rsp + 0x190 ]
adcx rcx, r14
adcx r10, r12
mov r12, rdx
mov rdx, [ rax + 0x18 ]
mulx rdi, r14, [ rsi + 0x10 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x1e8 ], r8
mov [ rsp + 0x1f0 ], r10
mulx r10, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x1f8 ], r10
mov [ rsp + 0x200 ], r8
mulx r8, r10, [ rax + 0x18 ]
mov rdx, r10
test al, al
adox rdx, [ rsp + 0x1d8 ]
adox r8, [ rsp + 0x1d0 ]
mov r10, r14
adcx r10, [ rsp + 0x1b8 ]
adcx rdi, [ rsp + 0x1b0 ]
xor r14, r14
adox r10, [ rsp + 0x60 ]
adox rdi, [ rsp + 0x58 ]
adcx r11, r12
adc r9, 0x0
mov r12, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x208 ], r9
mulx r9, r14, [ rax + 0x18 ]
test al, al
adox rcx, r15
adox r13, [ rsp + 0x1f0 ]
adcx rcx, [ rsp + 0xc0 ]
adcx r13, [ rsp + 0xb8 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x210 ], r9
mulx r9, r15, [ rsi + 0x0 ]
add r10, r15
adcx r9, rdi
mov rdx, r12
shrd rdx, r8, 56
mov r8, 0xffffffffffffff 
mov rdi, r11
and rdi, r8
adox rcx, rdx
mov r15, 0x0 
adox r13, r15
mov rdx, [ rsi + 0x20 ]
mulx r8, r15, [ rax + 0x10 ]
mov rdx, rcx
adcx rdx, [ rsp + 0x178 ]
adc r13, 0x0
mov rcx, r15
mov [ rsp + 0x218 ], r9
xor r9, r9
adox rcx, [ rsp + 0x1e8 ]
adox r8, [ rsp + 0x1e0 ]
mov r15, rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x220 ], r10
mulx r10, r9, [ rsi + 0x0 ]
adcx rcx, r14
adcx r8, [ rsp + 0x210 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x228 ], r10
mulx r10, r14, [ rsi + 0x10 ]
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x10 ], rdi
mov rdi, r15
shrd rdi, r13, 56
xor r13, r13
adox rcx, r14
adox r10, r8
mov r8, rdi
adcx r8, [ rsp + 0x220 ]
mov r14, [ rsp + 0x218 ]
adc r14, 0x0
mov rdi, 0x38 
bzhi r13, r8, rdi
adox rcx, [ rsp + 0x200 ]
adox r10, [ rsp + 0x1f8 ]
test al, al
adox rcx, r9
adox r10, [ rsp + 0x228 ]
shrd r8, r14, 56
xor r9, r9
adox rcx, r8
adox r10, r9
bzhi r14, rcx, rdi
bzhi r8, rbp, rdi
shrd rcx, r10, 56
add rcx, [ rsp + 0x188 ]
mov rbp, rcx
shr rbp, 56
lea r8, [ r8 + rbp ]
mov r10, [ rsp + 0x208 ]
shrd r11, r10, 56
bzhi r10, r12, rdi
bzhi r12, rcx, rdi
bzhi rcx, r8, rdi
mov [ rdx + 0x38 ], r12
lea r11, [ r11 + r10 ]
bzhi r10, r11, rdi
mov [ rdx + 0x18 ], r10
shr r8, 56
bzhi r12, rbx, rdi
bzhi rbx, r15, rdi
lea rbx, [ rbx + rbp ]
lea r8, [ r8 + r12 ]
shr r11, 56
lea r11, [ r11 + rbx ]
bzhi r15, r11, rdi
mov [ rdx + 0x20 ], r15
shr r11, 56
lea r11, [ r11 + r13 ]
mov [ rdx + 0x28 ], r11
mov [ rdx + 0x8 ], r8
mov [ rdx + 0x30 ], r14
mov [ rdx + 0x0 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 688
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 0.9868
; seed 1206788280631743 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4571080 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=80, initial num_batches=31): 109167 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.02388210226029735
; number reverted permutation / tried permutation: 58608 / 89837 =65.238%
; number reverted decision / tried decision: 41367 / 90162 =45.881%
; validated in 2.964s
