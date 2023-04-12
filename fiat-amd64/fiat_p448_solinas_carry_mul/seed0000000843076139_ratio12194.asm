SECTION .text
	GLOBAL fiat_p448_solinas_carry_mul
fiat_p448_solinas_carry_mul:
sub rsp, 520
mov rax, rdx
mov rdx, [ rsi + 0x38 ]
mulx r11, r10, [ rax + 0x18 ]
mov rdx, [ rax + 0x38 ]
mulx r8, rcx, [ rsi + 0x30 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x38 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x10 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x38 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x48 ], r12
mov [ rsp - 0x40 ], rbp
mulx rbp, r12, [ rax + 0x28 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x38 ], rbp
mov [ rsp - 0x30 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x28 ], r12
mov [ rsp - 0x20 ], rbp
mulx rbp, r12, [ rax + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x18 ], rbp
mov [ rsp - 0x10 ], r12
mulx r12, rbp, [ rsi + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x8 ], r12
mov [ rsp + 0x0 ], rbp
mulx rbp, r12, [ rsi + 0x0 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x8 ], rbp
mov [ rsp + 0x10 ], r12
mulx r12, rbp, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x18 ], r12
mov [ rsp + 0x20 ], rbp
mulx rbp, r12, [ rax + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x28 ], rbx
mov [ rsp + 0x30 ], r9
mulx r9, rbx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x38 ], r9
mov [ rsp + 0x40 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x48 ], rbx
mov [ rsp + 0x50 ], r9
mulx r9, rbx, [ rsi + 0x8 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x58 ], r9
mov [ rsp + 0x60 ], rbx
mulx rbx, r9, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x68 ], rbx
mov [ rsp + 0x70 ], r9
mulx r9, rbx, [ rax + 0x8 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x78 ], r9
mov [ rsp + 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
mov rdx, r13
test al, al
adox rdx, r13
mov [ rsp + 0x88 ], rbx
mov rbx, r14
adox rbx, r14
mov [ rsp + 0x90 ], r9
mov r9, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x98 ], r8
mov [ rsp + 0xa0 ], rcx
mulx rcx, r8, [ rax + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xa8 ], rcx
mov [ rsp + 0xb0 ], r8
mulx r8, rcx, [ rax + 0x10 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xb8 ], r8
mov [ rsp + 0xc0 ], rcx
mulx rcx, r8, [ rsi + 0x30 ]
adcx r9, r10
mov rdx, r11
adcx rdx, rbx
test al, al
adox r9, r8
mov rbx, rcx
adox rbx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xc8 ], rbp
mov [ rsp + 0xd0 ], r12
mulx r12, rbp, [ rax + 0x38 ]
adcx r13, r10
adcx r11, r14
mov rdx, [ rax + 0x28 ]
mulx r14, r10, [ rsi + 0x28 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xd8 ], r12
mov [ rsp + 0xe0 ], rbp
mulx rbp, r12, [ rsi + 0x38 ]
xor rdx, rdx
adox r9, r10
mov [ rsp + 0xe8 ], rdi
mov rdi, r14
adox rdi, rbx
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0xf0 ], rdi
mulx rdi, rbx, [ rsi + 0x30 ]
adcx r13, r8
adcx rcx, r11
test al, al
adox r13, r10
adox r14, rcx
mov rdx, r12
adcx rdx, rbx
mov r8, rdi
adcx r8, rbp
add rdx, r15
adcx r8, [ rsp + 0xe8 ]
mov r11, rdx
xor r10, r10
adox r11, r12
adox rbp, r8
adcx r11, rbx
adcx rdi, rbp
test al, al
adox r11, r15
adox rdi, [ rsp + 0xe8 ]
mov r15, rdx
mov rdx, [ rsi + 0x38 ]
mulx rbx, r12, [ rax + 0x8 ]
adcx r15, r12
mov rdx, rbx
adcx rdx, r8
xor rcx, rcx
adox r11, r12
adox rbx, rdi
mov r10, rdx
mov rdx, [ rsi + 0x30 ]
mulx rbp, r8, [ rax + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mulx r12, rdi, [ rax + 0x30 ]
adcx r13, rdi
mov rdx, r12
adcx rdx, r14
test al, al
adox r11, r8
mov r14, rbp
adox r14, rbx
adcx r11, [ rsp + 0xd0 ]
adcx r14, [ rsp + 0xc8 ]
test al, al
adox r15, r8
adox rbp, r10
mov r10, rdx
mov rdx, [ rsi + 0x18 ]
mulx r8, rbx, [ rax + 0x38 ]
adcx r15, [ rsp + 0xd0 ]
adcx rbp, [ rsp + 0xc8 ]
add r9, rdi
adcx r12, [ rsp + 0xf0 ]
xor rdx, rdx
adox r9, rbx
mov rcx, r8
adox rcx, r12
adcx r13, rbx
adcx r8, r10
mov rdx, [ rsi + 0x30 ]
mulx r10, rdi, [ rax + 0x0 ]
mov rdx, [ rsi + 0x38 ]
mulx r12, rbx, [ rax + 0x30 ]
test al, al
adox r9, rdi
adox r10, rcx
mov rdx, rbx
adcx rdx, [ rsp + 0xa0 ]
mov rcx, r12
adcx rcx, [ rsp + 0x98 ]
mov rdi, rdx
mov [ rsp + 0xf8 ], r8
xor r8, r8
adox rdi, rbx
adox r12, rcx
adcx rdi, [ rsp + 0xa0 ]
adcx r12, [ rsp + 0x98 ]
add rdi, [ rsp + 0x30 ]
adcx r12, [ rsp + 0x28 ]
add rdx, [ rsp + 0x30 ]
adcx rcx, [ rsp + 0x28 ]
xor rbx, rbx
adox rdi, [ rsp + 0xb0 ]
adox r12, [ rsp + 0xa8 ]
mov r8, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x100 ], r13
mulx r13, rbx, [ rsi + 0x28 ]
adcx r9, rbx
adcx r13, r10
mov rdx, [ rax + 0x28 ]
mulx rbx, r10, [ rsi + 0x18 ]
add r15, [ rsp + 0x20 ]
adcx rbp, [ rsp + 0x18 ]
xor rdx, rdx
adox r15, r10
mov [ rsp + 0x108 ], r13
mov r13, rbx
adox r13, rbp
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x110 ], r9
mulx r9, rbp, [ rax + 0x20 ]
adcx r8, [ rsp + 0xb0 ]
adcx rcx, [ rsp + 0xa8 ]
test al, al
adox r11, [ rsp + 0x20 ]
adox r14, [ rsp + 0x18 ]
adcx rdi, rbp
mov rdx, r9
adcx rdx, r12
test al, al
adox rdi, [ rsp - 0x30 ]
adox rdx, [ rsp - 0x38 ]
adcx r8, rbp
adcx r9, rcx
test al, al
adox r11, r10
adox rbx, r14
adcx r8, [ rsp - 0x30 ]
adcx r9, [ rsp - 0x38 ]
test al, al
adox r11, [ rsp + 0x90 ]
adox rbx, [ rsp + 0x88 ]
mov r12, rdx
mov rdx, [ rax + 0x20 ]
mulx rbp, r10, [ rsi + 0x38 ]
adcx r10, [ rsp + 0x70 ]
adcx rbp, [ rsp + 0x68 ]
test al, al
adox r11, [ rsp + 0x60 ]
adox rbx, [ rsp + 0x58 ]
mov rdx, [ rsi + 0x18 ]
mulx r14, rcx, [ rax + 0x30 ]
adcx r15, [ rsp + 0x90 ]
adcx r13, [ rsp + 0x88 ]
xor rdx, rdx
adox r15, [ rsp + 0x60 ]
adox r13, [ rsp + 0x58 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x118 ], r13
mov [ rsp + 0x120 ], r15
mulx r15, r13, [ rsi + 0x20 ]
adcx r8, rcx
mov rdx, r14
adcx rdx, r9
add rdi, rcx
adcx r14, r12
test al, al
adox rdi, [ rsp + 0xe0 ]
adox r14, [ rsp + 0xd8 ]
mov r12, rdx
mov rdx, [ rax + 0x30 ]
mulx rcx, r9, [ rsi + 0x28 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x128 ], r12
mov [ rsp + 0x130 ], r8
mulx r8, r12, [ rsi + 0x28 ]
adcx r10, r9
adcx rcx, rbp
xor rdx, rdx
adox r11, r13
adox r15, rbx
mov rdx, [ rax + 0x38 ]
mulx rbx, rbp, [ rsi + 0x20 ]
mov rdx, [ rax + 0x0 ]
mulx r9, r13, [ rsi + 0x18 ]
adcx r10, rbp
adcx rbx, rcx
mov rdx, [ rax + 0x8 ]
mulx rbp, rcx, [ rsi + 0x30 ]
mov rdx, r10
mov [ rsp + 0x138 ], r15
xor r15, r15
adox rdx, r13
adox r9, rbx
mov r13, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x140 ], r11
mulx r11, r15, [ rax + 0x0 ]
adcx r10, r15
adcx r11, rbx
xor rdx, rdx
adox r10, rcx
adox rbp, r11
mov rdx, [ rsi + 0x0 ]
mulx rcx, rbx, [ rax + 0x18 ]
adcx r10, [ rsp + 0xc0 ]
adcx rbp, [ rsp + 0xb8 ]
xor rdx, rdx
adox rdi, r12
adox r8, r14
adcx rdi, [ rsp - 0x10 ]
adcx r8, [ rsp - 0x18 ]
mov rdx, [ rsi + 0x18 ]
mulx r12, r14, [ rax + 0x10 ]
mov rdx, [ rax + 0x18 ]
mulx r11, r15, [ rsi + 0x20 ]
test al, al
adox rdi, r14
adox r12, r8
adcx r10, r15
adcx r11, rbp
test al, al
adox r13, [ rsp + 0x80 ]
adox r9, [ rsp + 0x78 ]
mov rdx, [ rsi + 0x18 ]
mulx r8, rbp, [ rax + 0x20 ]
mov rdx, [ rax + 0x10 ]
mulx r15, r14, [ rsi + 0x8 ]
adcx r13, r14
adcx r15, r9
test al, al
adox r10, rbp
adox r8, r11
adcx r13, rbx
adcx rcx, r15
mov rdx, 0xffffffffffffff 
mov rbx, r13
and rbx, rdx
shrd r13, rcx, 56
mov rdx, [ rax + 0x28 ]
mulx r9, r11, [ rsi + 0x10 ]
add r10, r11
adcx r9, r8
mov rdx, [ rax + 0x10 ]
mulx r14, rbp, [ rsi + 0x20 ]
mov rdx, rbp
xor r15, r15
adox rdx, [ rsp + 0x110 ]
adox r14, [ rsp + 0x108 ]
mov r8, rdx
mov rdx, [ rax + 0x8 ]
mulx r11, rcx, [ rsi + 0x18 ]
mov rdx, rcx
adcx rdx, [ rsp + 0x140 ]
adcx r11, [ rsp + 0x138 ]
xor rbp, rbp
adox rdx, [ rsp + 0x50 ]
adox r11, [ rsp + 0x48 ]
adcx r8, [ rsp - 0x20 ]
adcx r14, [ rsp - 0x28 ]
mov r15, rdx
mov rdx, [ rax + 0x18 ]
mulx rbp, rcx, [ rsi + 0x8 ]
test al, al
adox r15, rcx
adox rbp, r11
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rax + 0x38 ]
adcx rdi, [ rsp - 0x40 ]
adcx r12, [ rsp - 0x48 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x148 ], rbx
mov [ rsp + 0x150 ], rcx
mulx rcx, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x158 ], r11
mov [ rsp + 0x160 ], r9
mulx r9, r11, [ rax + 0x20 ]
test al, al
adox r15, [ rsp + 0x40 ]
adox rbp, [ rsp + 0x38 ]
adcx r15, r13
adc rbp, 0x0
add rdi, r11
adcx r9, r12
mov rdx, [ rax + 0x20 ]
mulx r12, r13, [ rsi + 0x10 ]
test al, al
adox r8, r13
adox r12, r14
adcx rdi, rbx
adcx rcx, r9
mov rdx, [ rax + 0x0 ]
mulx rbx, r14, [ rsi + 0x8 ]
mov rdx, [ rax + 0x30 ]
mulx r9, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x168 ], rbx
mulx rbx, r13, [ rax + 0x30 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x170 ], r14
mov [ rsp + 0x178 ], r9
mulx r9, r14, [ rax + 0x28 ]
xor rdx, rdx
adox r10, r13
adox rbx, [ rsp + 0x160 ]
adcx r10, [ rsp + 0x158 ]
adcx rbx, [ rsp + 0x150 ]
mov r13, r10
shrd r13, rbx, 56
mov rbx, r13
test al, al
adox rbx, r15
adox rbp, rdx
mov r15, rbx
shrd r15, rbp, 56
test al, al
adox rdi, r15
adox rcx, rdx
adcx r8, r14
adcx r9, r12
test al, al
adox r8, r11
adox r9, [ rsp + 0x178 ]
mov r12, 0x38 
bzhi r11, rbx, r12
mov rdx, [ rax + 0x0 ]
mulx rbx, r14, [ rsi + 0x0 ]
mov rdx, r14
adox rdx, [ rsp + 0x120 ]
adox rbx, [ rsp + 0x118 ]
mov rbp, [ rsp + 0xe0 ]
mov r15, rbp
test al, al
adox r15, [ rsp + 0x130 ]
mov r14, [ rsp + 0xd8 ]
adox r14, [ rsp + 0x128 ]
bzhi rbp, rdi, r12
shrd rdi, rcx, 56
test al, al
adox r15, [ rsp + 0x170 ]
adox r14, [ rsp + 0x168 ]
adcx r8, rdi
adc r9, 0x0
xor rcx, rcx
adox r13, rdx
adox rbx, rcx
bzhi rdx, r13, r12
shrd r13, rbx, 56
mov rdi, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, rbx, [ rax + 0x8 ]
bzhi rdx, r8, r12
mov [ rsp + 0x180 ], rbp
bzhi rbp, r10, r12
shrd r8, r9, 56
lea r8, [ r8 + rbp ]
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x30 ], rdx
mov rdx, [ rsi + 0x10 ]
mulx rbp, r9, [ rax + 0x0 ]
mov rdx, r9
add rdx, [ rsp + 0x100 ]
adcx rbp, [ rsp + 0xf8 ]
test al, al
adox rdx, [ rsp + 0x0 ]
adox rbp, [ rsp - 0x8 ]
mov r9, r8
shr r9, 56
lea rdi, [ rdi + r9 ]
add r15, rbx
adcx rcx, r14
test al, al
adox rdx, [ rsp + 0x10 ]
adox rbp, [ rsp + 0x8 ]
adcx r15, r13
adc rcx, 0x0
mov r14, r15
shrd r14, rcx, 56
bzhi r13, rdi, r12
adox rdx, r14
mov rbx, 0x0 
adox rbp, rbx
mov rcx, rdx
shrd rcx, rbp, 56
add rcx, [ rsp + 0x148 ]
bzhi r14, rcx, r12
shr rcx, 56
mov [ r10 + 0x18 ], r14
lea r11, [ r11 + r9 ]
lea rcx, [ rcx + r11 ]
bzhi r9, rcx, r12
shr rcx, 56
add rcx, [ rsp + 0x180 ]
bzhi rbp, r15, r12
shr rdi, 56
mov [ r10 + 0x28 ], rcx
bzhi r15, r8, r12
lea rdi, [ rdi + rbp ]
mov [ r10 + 0x20 ], r9
bzhi r8, rdx, r12
mov [ r10 + 0x10 ], r8
mov [ r10 + 0x8 ], rdi
mov [ r10 + 0x0 ], r13
mov [ r10 + 0x38 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 520
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.2194
; seed 0065847206224748 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5908969 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=59, initial num_batches=31): 134640 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.022785700855766887
; number reverted permutation / tried permutation: 63648 / 90110 =70.634%
; number reverted decision / tried decision: 50316 / 89889 =55.976%
; validated in 3.862s
