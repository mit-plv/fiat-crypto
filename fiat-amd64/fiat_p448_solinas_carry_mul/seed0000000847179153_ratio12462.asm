SECTION .text
	GLOBAL fiat_p448_solinas_carry_mul
fiat_p448_solinas_carry_mul:
sub rsp, 504
mov rax, rdx
mov rdx, [ rdx + 0x18 ]
mulx r11, r10, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x28 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x30 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x20 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x48 ], r8
mov [ rsp - 0x40 ], rcx
mulx rcx, r8, [ rax + 0x10 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x38 ], r12
mov [ rsp - 0x30 ], rbp
mulx rbp, r12, [ rax + 0x30 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], r14
mov [ rsp - 0x20 ], r13
mulx r13, r14, [ rax + 0x8 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x18 ], r13
mov [ rsp - 0x10 ], r14
mulx r14, r13, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x8 ], r14
mov [ rsp + 0x0 ], r13
mulx r13, r14, [ rax + 0x38 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x8 ], r13
mov [ rsp + 0x10 ], r14
mulx r14, r13, [ rax + 0x38 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x18 ], r14
mov [ rsp + 0x20 ], r13
mulx r13, r14, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x28 ], r13
mov [ rsp + 0x30 ], r14
mulx r14, r13, [ rax + 0x38 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x38 ], rdi
mov [ rsp + 0x40 ], r15
mulx r15, rdi, [ rax + 0x30 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x48 ], rcx
mov [ rsp + 0x50 ], r8
mulx r8, rcx, [ rsi + 0x28 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x58 ], r8
mov [ rsp + 0x60 ], rcx
mulx rcx, r8, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x68 ], rcx
mov [ rsp + 0x70 ], r8
mulx r8, rcx, [ rsi + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x78 ], r8
mov [ rsp + 0x80 ], rcx
mulx rcx, r8, [ rsi + 0x38 ]
mov rdx, r9
mov [ rsp + 0x88 ], rcx
xor rcx, rcx
adox rdx, r13
mov [ rsp + 0x90 ], r8
mov r8, r14
adox r8, rbx
mov [ rsp + 0x98 ], r15
mov r15, rdx
adcx r15, r9
adcx rbx, r8
mov r9, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xa0 ], rdi
mulx rdi, rcx, [ rax + 0x38 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xa8 ], rdi
mov [ rsp + 0xb0 ], rcx
mulx rcx, rdi, [ rax + 0x28 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xb8 ], rcx
mov [ rsp + 0xc0 ], rdi
mulx rdi, rcx, [ rax + 0x10 ]
test al, al
adox r15, r13
adox r14, rbx
mov rdx, [ rsi + 0x28 ]
mulx rbx, r13, [ rax + 0x20 ]
adcx r15, rcx
mov rdx, rdi
adcx rdx, r14
add r9, rcx
adcx rdi, r8
add r9, r10
mov r8, r11
adcx r8, rdi
xor rcx, rcx
adox r15, r10
adox r11, rdx
adcx r9, r13
mov r10, rbx
adcx r10, r8
mov rdx, [ rax + 0x38 ]
mulx rdi, r14, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x38 ]
mulx rcx, r8, [ rax + 0x28 ]
add r15, r13
adcx rbx, r11
mov rdx, r8
add rdx, r12
mov r13, rbp
adcx r13, rcx
test al, al
adox rdx, r14
mov r11, rdi
adox r11, r13
mov r13, rdx
adcx r13, r8
adcx rcx, r11
add r13, r12
adcx rbp, rcx
add r13, r14
adcx rdi, rbp
mov r12, rdx
mov rdx, [ rax + 0x28 ]
mulx r8, r14, [ rsi + 0x20 ]
xor rdx, rdx
adox r9, r14
mov rcx, r8
adox rcx, r10
adcx r15, r14
adcx r8, rbx
mov rdx, [ rax + 0x8 ]
mulx rbx, r10, [ rsi + 0x38 ]
add r9, [ rsp + 0xa0 ]
adcx rcx, [ rsp + 0x98 ]
test al, al
adox r13, r10
mov rdx, rbx
adox rdx, rdi
adcx r13, [ rsp + 0x50 ]
adcx rdx, [ rsp + 0x48 ]
test al, al
adox r15, [ rsp + 0xa0 ]
adox r8, [ rsp + 0x98 ]
mov rbp, rdx
mov rdx, [ rsi + 0x10 ]
mulx r14, rdi, [ rax + 0x38 ]
adcx r12, r10
adcx rbx, r11
test al, al
adox r12, [ rsp + 0x50 ]
adox rbx, [ rsp + 0x48 ]
mov rdx, [ rax + 0x18 ]
mulx r10, r11, [ rsi + 0x28 ]
adcx r12, r11
mov rdx, r10
adcx rdx, rbx
add r13, r11
adcx r10, rbp
mov rbp, rdx
mov rdx, [ rax + 0x38 ]
mulx r11, rbx, [ rsi + 0x38 ]
add r9, rdi
mov rdx, r14
adcx rdx, rcx
mov rcx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xc8 ], r9
mov [ rsp + 0xd0 ], r10
mulx r10, r9, [ rax + 0x20 ]
add r12, r9
mov rdx, r10
adcx rdx, rbp
mov rbp, rbx
mov [ rsp + 0xd8 ], rcx
xor rcx, rcx
adox rbp, rbx
mov [ rsp + 0xe0 ], rdx
mov rdx, r11
adox rdx, r11
adcx r15, rdi
adcx r14, r8
xor r8, r8
adox rbp, [ rsp + 0x40 ]
adox rdx, [ rsp + 0x38 ]
adcx rbp, [ rsp - 0x20 ]
adcx rdx, [ rsp - 0x28 ]
mov rcx, rdx
mov rdx, [ rsi + 0x20 ]
mulx r8, rdi, [ rax + 0x30 ]
add r13, r9
adcx r10, [ rsp + 0xd0 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xe8 ], r14
mulx r14, r9, [ rsi + 0x30 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xf0 ], r15
mov [ rsp + 0xf8 ], r10
mulx r10, r15, [ rsi + 0x28 ]
add rbp, r15
mov rdx, r10
adcx rdx, rcx
mov rcx, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x100 ], r13
mov [ rsp + 0x108 ], r12
mulx r12, r13, [ rax + 0x20 ]
xor rdx, rdx
adox r13, r9
adox r14, r12
adcx rbx, [ rsp + 0x40 ]
adcx r11, [ rsp + 0x38 ]
xor r9, r9
adox rbx, [ rsp - 0x20 ]
adox r11, [ rsp - 0x28 ]
adcx rbx, r15
adcx r10, r11
mov rdx, [ rsi + 0x28 ]
mulx r12, r15, [ rax + 0x30 ]
test al, al
adox r13, r15
adox r12, r14
adcx r13, [ rsp + 0x20 ]
adcx r12, [ rsp + 0x18 ]
mov rdx, [ rax + 0x28 ]
mulx r11, r14, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mulx r9, r15, [ rax + 0x18 ]
test al, al
adox rbp, rdi
mov rdx, r8
adox rdx, rcx
mov rcx, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x110 ], rbp
mov [ rsp + 0x118 ], r9
mulx r9, rbp, [ rax + 0x8 ]
mov rdx, r13
adcx rdx, [ rsp + 0x90 ]
mov [ rsp + 0x120 ], rcx
mov rcx, r12
adcx rcx, [ rsp + 0x88 ]
add rbx, rdi
adcx r8, r10
test al, al
adox rdx, rbp
adox r9, rcx
mov rdi, rdx
mov rdx, [ rsi + 0x18 ]
mulx rbp, r10, [ rax + 0x8 ]
mov rdx, r14
adcx rdx, [ rsp + 0x108 ]
mov rcx, r11
adcx rcx, [ rsp + 0xe0 ]
mov [ rsp + 0x128 ], r8
mov r8, r14
add r8, [ rsp + 0x100 ]
adcx r11, [ rsp + 0xf8 ]
xor r14, r14
adox r8, [ rsp + 0x0 ]
adox r11, [ rsp - 0x8 ]
adcx r8, [ rsp + 0xb0 ]
adcx r11, [ rsp + 0xa8 ]
mov r14, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x130 ], rbx
mov [ rsp + 0x138 ], rbp
mulx rbp, rbx, [ rax + 0x28 ]
xor rdx, rdx
adox r14, [ rsp + 0x0 ]
adox rcx, [ rsp - 0x8 ]
adcx rdi, [ rsp + 0x60 ]
adcx r9, [ rsp + 0x58 ]
test al, al
adox rdi, r15
adox r9, [ rsp + 0x118 ]
adcx r14, [ rsp + 0xb0 ]
adcx rcx, [ rsp + 0xa8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x140 ], rcx
mulx rcx, r15, [ rax + 0x20 ]
add rdi, r15
adcx rcx, r9
add r8, [ rsp + 0x30 ]
adcx r11, [ rsp + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mulx r15, r9, [ rax + 0x0 ]
test al, al
adox rdi, rbx
adox rbp, rcx
mov rdx, [ rax + 0x30 ]
mulx rcx, rbx, [ rsi + 0x8 ]
adcx r13, r9
adcx r15, r12
mov rdx, [ rax + 0x8 ]
mulx r9, r12, [ rsi + 0x10 ]
xor rdx, rdx
adox r8, r10
adox r11, [ rsp + 0x138 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x148 ], r14
mulx r14, r10, [ rax + 0x10 ]
adcx r8, r10
adcx r14, r11
test al, al
adox rdi, rbx
adox rcx, rbp
mov rdx, [ rax + 0x18 ]
mulx rbx, rbp, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mulx r10, r11, [ rsi + 0x0 ]
adcx r13, r12
adcx r9, r15
mov rdx, [ rax + 0x20 ]
mulx r12, r15, [ rsi + 0x0 ]
add r13, [ rsp + 0x80 ]
adcx r9, [ rsp + 0x78 ]
test al, al
adox r13, rbp
adox rbx, r9
mov rdx, [ rax + 0x18 ]
mulx r9, rbp, [ rsi + 0x8 ]
adcx r8, rbp
adcx r9, r14
xor rdx, rdx
adox r8, r15
adox r12, r9
mov r14, 0x38 
bzhi r15, r13, r14
mov rdx, [ rax + 0x38 ]
mulx r9, rbp, [ rsi + 0x18 ]
adox rdi, [ rsp + 0x10 ]
adox rcx, [ rsp + 0x8 ]
mov rdx, rdi
shrd rdx, rcx, 56
shrd r13, rbx, 56
mov rbx, r11
add rbx, [ rsp + 0x148 ]
adcx r10, [ rsp + 0x140 ]
xor r11, r11
adox r8, r13
adox r12, r11
mov rcx, rdx
adcx rcx, r8
adc r12, 0x0
add rdx, rbx
adc r10, 0x0
bzhi r13, rdx, r14
mov rbx, rbp
adox rbx, [ rsp + 0x130 ]
mov r8, r9
adox r8, [ rsp + 0x128 ]
bzhi r11, rdi, r14
mov rdi, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x150 ], r13
mulx r13, r14, [ rax + 0x0 ]
mov rdx, r14
adox rdx, [ rsp + 0xc8 ]
adox r13, [ rsp + 0xd8 ]
mov r14, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x158 ], r11
mov [ rsp + 0x160 ], r15
mulx r15, r11, [ rax + 0x8 ]
add r14, r11
adcx r15, r13
mov rdx, [ rax + 0x0 ]
mulx r11, r13, [ rsi + 0x10 ]
test al, al
adox rbx, r13
adox r11, r8
mov rdx, rcx
shrd rdx, r12, 56
mov r12, rdx
mov rdx, [ rsi + 0x0 ]
mulx r13, r8, [ rax + 0x10 ]
shrd rdi, r10, 56
test al, al
adox r14, rdi
mov rdx, 0x0 
adox r15, rdx
mov r10, r14
shrd r10, r15, 56
mov rdi, rbp
test al, al
adox rdi, [ rsp + 0x110 ]
adox r9, [ rsp + 0x120 ]
adcx rbx, [ rsp - 0x10 ]
adcx r11, [ rsp - 0x18 ]
test al, al
adox rbx, r8
adox r13, r11
mov rdx, [ rax + 0x0 ]
mulx r8, rbp, [ rsi + 0x30 ]
adcx rbx, r10
adc r13, 0x0
mov rdx, [ rax + 0x0 ]
mulx r10, r15, [ rsi + 0x28 ]
mov rdx, r15
xor r11, r11
adox rdx, [ rsp + 0xf0 ]
adox r10, [ rsp + 0xe8 ]
adcx rdi, rbp
adcx r8, r9
mov r9, rdx
mov rdx, [ rax + 0x8 ]
mulx r15, rbp, [ rsi + 0x28 ]
add rdi, rbp
adcx r15, r8
mov rdx, [ rsi + 0x20 ]
mulx rbp, r8, [ rax + 0x8 ]
test al, al
adox r9, r8
adox rbp, r10
adcx r9, [ rsp - 0x30 ]
adcx rbp, [ rsp - 0x38 ]
mov rdx, [ rax + 0x18 ]
mulx r8, r10, [ rsi + 0x10 ]
mov rdx, rbx
shrd rdx, r13, 56
add rdx, [ rsp + 0x160 ]
add r9, r10
adcx r8, rbp
mov r13, rdx
mov rdx, [ rsi + 0x0 ]
mulx r10, rbp, [ rax + 0x30 ]
mov rdx, r13
shr rdx, 56
mov r11, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x168 ], r10
mov [ rsp + 0x170 ], rbp
mulx rbp, r10, [ rax + 0x20 ]
add r9, r10
adcx rbp, r8
add r9, [ rsp - 0x40 ]
adcx rbp, [ rsp - 0x48 ]
add r9, r12
adc rbp, 0x0
mov rdx, r9
shrd rdx, rbp, 56
mov r12, 0x38 
bzhi r8, rcx, r12
mov rcx, rdx
mov rdx, [ rax + 0x10 ]
mulx rbp, r10, [ rsi + 0x20 ]
adox rdi, r10
adox rbp, r15
add rdi, [ rsp + 0x70 ]
adcx rbp, [ rsp + 0x68 ]
mov rdx, [ rax + 0x20 ]
mulx r10, r15, [ rsi + 0x10 ]
xor rdx, rdx
adox rdi, r15
adox r10, rbp
adcx rdi, [ rsp + 0xc0 ]
adcx r10, [ rsp + 0xb8 ]
add rdi, [ rsp + 0x170 ]
adcx r10, [ rsp + 0x168 ]
add rdi, rcx
adc r10, 0x0
mov rcx, rdi
shrd rcx, r10, 56
add rcx, [ rsp + 0x158 ]
bzhi rbp, rcx, r12
shr rcx, 56
lea r8, [ r8 + rcx ]
bzhi r15, rdi, r12
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x30 ], r15
lea r11, [ r11 + r8 ]
add rcx, [ rsp + 0x150 ]
bzhi r10, rcx, r12
bzhi r8, r11, r12
shr r11, 56
bzhi r15, r14, r12
bzhi r14, r9, r12
bzhi r9, rbx, r12
mov [ rdi + 0x10 ], r9
shr rcx, 56
bzhi rbx, r13, r12
mov [ rdi + 0x18 ], rbx
lea rcx, [ rcx + r15 ]
mov [ rdi + 0x20 ], r8
lea r11, [ r11 + r14 ]
mov [ rdi + 0x8 ], rcx
mov [ rdi + 0x0 ], r10
mov [ rdi + 0x38 ], rbp
mov [ rdi + 0x28 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 504
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.2462
; seed 1835793221116328 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 6252868 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=61, initial num_batches=31): 136795 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.021877161008356485
; number reverted permutation / tried permutation: 64015 / 90005 =71.124%
; number reverted decision / tried decision: 51136 / 89994 =56.822%
; validated in 3.743s
