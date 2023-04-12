SECTION .text
	GLOBAL fiat_p521_carry_mul
fiat_p521_carry_mul:
sub rsp, 784
mov rax, rdx
mov rdx, [ rdx + 0x18 ]
mulx r11, r10, [ rsi + 0x18 ]
mov rdx, 0x1 
shlx rcx, [ rax + 0x40 ], rdx
mov r8, [ rax + 0x18 ]
lea r9, [r8 + r8]
imul r8, [ rax + 0x10 ], 0x2
mov rdx, r9
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x38 ]
mov [ rsp - 0x78 ], rbp
mov rbp, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rax + 0x28 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x50 ], rdi
mov rdi, rdx
shl rdi, 0x1
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x48 ], r15
lea r15, [rdx + rdx]
imul rdx, [ rax + 0x38 ], 0x2
xchg rdx, r15
mov [ rsp - 0x40 ], r14
mov [ rsp - 0x38 ], r11
mulx r11, r14, [ rsi + 0x40 ]
mov [ rsp - 0x30 ], r10
mov r10, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x28 ], r13
mov [ rsp - 0x20 ], r12
mulx r12, r13, [ rax + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x18 ], r12
mov [ rsp - 0x10 ], r13
mulx r13, r12, r10
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x8 ], r11
mov [ rsp + 0x0 ], r14
mulx r14, r11, r15
mov rdx, r10
mov [ rsp + 0x8 ], r14
mulx r14, r10, [ rsi + 0x30 ]
mov [ rsp + 0x10 ], r11
mov r11, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x18 ], r14
mov [ rsp + 0x20 ], r10
mulx r10, r14, r15
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x28 ], r10
mov [ rsp + 0x30 ], r14
mulx r14, r10, [ rax + 0x8 ]
mov rdx, rcx
mov [ rsp + 0x38 ], r14
mulx r14, rcx, [ rsi + 0x20 ]
mov [ rsp + 0x40 ], r10
mov r10, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x48 ], r14
mov [ rsp + 0x50 ], rcx
mulx rcx, r14, r8
mov rdx, 0x1 
mov [ rsp + 0x58 ], rbx
shlx rbx, [ rax + 0x28 ], rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x60 ], r9
mov [ rsp + 0x68 ], r13
mulx r13, r9, r10
mov rdx, rbx
mov [ rsp + 0x70 ], r13
mulx r13, rbx, [ rsi + 0x20 ]
xchg rdx, r10
mov [ rsp + 0x78 ], r9
mov [ rsp + 0x80 ], r13
mulx r13, r9, [ rsi + 0x38 ]
mov [ rsp + 0x88 ], r13
mov r13, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x90 ], r9
mov [ rsp + 0x98 ], rbx
mulx rbx, r9, [ rsi + 0x18 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0xa0 ], rbx
mov [ rsp + 0xa8 ], r9
mulx r9, rbx, [ rsi + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0xb0 ], r9
lea r9, [rdx + rdx]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xb8 ], rbx
mov [ rsp + 0xc0 ], r12
mulx r12, rbx, r10
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xc8 ], r12
mov [ rsp + 0xd0 ], rbx
mulx rbx, r12, [ rax + 0x10 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0xd8 ], rbx
mov [ rsp + 0xe0 ], r12
mulx r12, rbx, r9
mov rdx, r13
mulx r9, r13, [ rsi + 0x40 ]
mov [ rsp + 0xe8 ], r9
mov r9, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xf0 ], r13
mov [ rsp + 0xf8 ], rdi
mulx rdi, r13, r10
mov rdx, rbp
mov [ rsp + 0x100 ], rdi
mulx rdi, rbp, [ rsi + 0x30 ]
add rbx, r14
adcx rcx, r12
xor r14, r14
adox rbx, rbp
adox rdi, rcx
mov r12, rdx
mov rdx, [ rsp + 0xf8 ]
mulx rcx, rbp, [ rsi + 0x38 ]
mov r14, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x108 ], r13
mov [ rsp + 0x110 ], rdi
mulx rdi, r13, r10
adcx r13, rbp
adcx rcx, rdi
test al, al
adox rbx, [ rsp + 0xc0 ]
mov rdx, [ rsp + 0x110 ]
adox rdx, [ rsp + 0x68 ]
mov rbp, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x118 ], rcx
mulx rcx, rdi, r14
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x120 ], r13
mov [ rsp + 0x128 ], rcx
mulx rcx, r13, r8
adcx r13, [ rsp + 0x60 ]
adcx rcx, [ rsp + 0x58 ]
test al, al
adox rbx, [ rsp + 0x98 ]
adox rbp, [ rsp + 0x80 ]
adcx rbx, rdi
adcx rbp, [ rsp + 0x128 ]
mov rdx, [ rsi + 0x20 ]
mulx rdi, r8, r14
add rbx, [ rsp + 0x30 ]
adcx rbp, [ rsp + 0x28 ]
xor rdx, rdx
adox r13, [ rsp + 0x20 ]
adox rcx, [ rsp + 0x18 ]
adcx r13, [ rsp + 0xd0 ]
adcx rcx, [ rsp + 0xc8 ]
mov [ rsp + 0x130 ], rbp
xor rbp, rbp
adox r13, r8
adox rdi, rcx
mov rdx, [ rsi + 0x8 ]
mulx rcx, r8, r9
mov rdx, r11
mulx rbp, r11, [ rsi + 0x38 ]
mov rdx, r12
mov [ rsp + 0x138 ], rdi
mulx rdi, r12, [ rsi + 0x40 ]
adcx r12, r11
adcx rbp, rdi
mov rdx, r10
mulx r11, r10, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x140 ], r13
mulx r13, rdi, r14
xor rdx, rdx
adox r12, r10
adox r11, rbp
adcx r12, rdi
adcx r13, r11
test al, al
adox r12, [ rsp + 0x10 ]
adox r13, [ rsp + 0x8 ]
adcx rbx, r8
adcx rcx, [ rsp + 0x130 ]
mov rdx, r14
mulx r8, r14, [ rsi + 0x30 ]
xchg rdx, r9
mulx r10, rbp, [ rsi + 0x18 ]
mov rdi, [ rsp + 0x0 ]
xor r11, r11
adox rdi, [ rsp + 0x108 ]
mov [ rsp + 0x148 ], r8
mov r8, [ rsp - 0x8 ]
adox r8, [ rsp + 0x100 ]
adcx r12, rbp
adcx r10, r13
xor r13, r13
adox rbx, [ rsp - 0x20 ]
adox rcx, [ rsp - 0x28 ]
adcx rdi, r14
adcx r8, [ rsp + 0x148 ]
mov r11, rdx
mov rdx, [ rax + 0x0 ]
mulx rbp, r14, [ rsi + 0x10 ]
add r12, r14
adcx rbp, r10
mov rdx, r15
mulx r10, r15, [ rsi + 0x28 ]
mulx r13, r14, [ rsi + 0x18 ]
add rdi, r15
adcx r10, r8
xor r8, r8
adox rdi, [ rsp + 0x50 ]
adox r10, [ rsp + 0x48 ]
mov r15, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x150 ], rbp
mulx rbp, r8, [ rsi + 0x18 ]
adcx rdi, r8
adcx rbp, r10
mov rdx, r14
test al, al
adox rdx, [ rsp + 0x140 ]
adox r13, [ rsp + 0x138 ]
adcx rdi, [ rsp + 0x40 ]
adcx rbp, [ rsp + 0x38 ]
mov r14, rdx
mov rdx, [ rsi + 0x10 ]
mulx r8, r10, r11
xor rdx, rdx
adox r14, r10
adox r8, r13
mov rdx, [ rsi + 0x18 ]
mulx r10, r13, [ rax + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x158 ], r12
mov [ rsp + 0x160 ], rbp
mulx rbp, r12, [ rax + 0x0 ]
adcx r14, r12
adcx rbp, r8
mov rdx, rbx
shrd rdx, rcx, 58
shr rcx, 58
xor r8, r8
adox r14, [ rsp - 0x10 ]
adox rbp, [ rsp - 0x18 ]
adcx r14, rdx
adcx rcx, rbp
mov rdx, r15
mulx r12, r15, [ rsi + 0x30 ]
mov rbp, r14
shrd rbp, rcx, 58
shr rcx, 58
mov [ rsp + 0x168 ], rcx
mov rcx, r15
add rcx, [ rsp + 0x120 ]
adcx r12, [ rsp + 0x118 ]
mov r15, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x170 ], rbp
mulx rbp, r8, [ rsi + 0x8 ]
mov rdx, 0x3ffffffffffffff 
and rbx, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x178 ], rbx
mov [ rsp + 0x180 ], rdi
mulx rdi, rbx, [ rsi + 0x20 ]
adox rcx, [ rsp + 0x78 ]
adox r12, [ rsp + 0x70 ]
adcx rcx, rbx
adcx rdi, r12
xor rdx, rdx
adox rcx, r13
adox r10, rdi
mov rdx, [ rsi + 0x10 ]
mulx rbx, r13, [ rax + 0x10 ]
adcx rcx, r13
adcx rbx, r10
test al, al
adox rcx, r8
adox rbp, rbx
mov rdx, [ rax + 0x20 ]
mulx r12, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx r10, rdi, [ rax + 0x18 ]
adcx rcx, r8
adcx r12, rbp
mov rdx, [ rax + 0x10 ]
mulx rbx, r13, [ rsi + 0x8 ]
mov rdx, r13
test al, al
adox rdx, [ rsp + 0x180 ]
adox rbx, [ rsp + 0x160 ]
adcx rdx, rdi
adcx r10, rbx
mov rbp, rdx
mov rdx, [ rax + 0x8 ]
mulx rdi, r8, [ rsi + 0x8 ]
mov rdx, r8
xor r13, r13
adox rdx, [ rsp + 0x158 ]
adox rdi, [ rsp + 0x150 ]
mov rbx, rdx
mov rdx, [ rsi + 0x0 ]
mulx r13, r8, [ rax + 0x10 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x188 ], r12
mov [ rsp + 0x190 ], rcx
mulx rcx, r12, r15
mov rdx, r11
mov [ rsp + 0x198 ], rcx
mulx rcx, r11, [ rsi + 0x30 ]
adcx rbx, r8
adcx r13, rdi
add rbx, [ rsp + 0x170 ]
adcx r13, [ rsp + 0x168 ]
mov rdx, [ rsi + 0x38 ]
mulx r8, rdi, [ rax + 0x0 ]
mov rdx, rbx
shrd rdx, r13, 58
shr r13, 58
mov [ rsp + 0x1a0 ], r8
mov r8, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x1a8 ], rdi
mov [ rsp + 0x1b0 ], rcx
mulx rcx, rdi, r9
xor rdx, rdx
adox rbp, r8
adox r13, r10
mov r9, rbp
shrd r9, r13, 58
shr r13, 58
mov r10, 0x3a 
bzhi r8, rbp, r10
adox rdi, r12
adox rcx, [ rsp + 0x198 ]
mov rdx, [ rsi + 0x40 ]
mulx rbp, r12, [ rax + 0x0 ]
mov rdx, r9
test al, al
adox rdx, [ rsp + 0x190 ]
adox r13, [ rsp + 0x188 ]
bzhi r9, rbx, r10
mov rbx, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x1b8 ], r9
mulx r9, r10, [ rsi + 0x20 ]
adox rdi, r11
adox rcx, [ rsp + 0x1b0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x1c0 ], r13
mulx r13, r11, [ rax + 0x0 ]
test al, al
adox rdi, r11
adox r13, rcx
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x18 ], r8
mov r8, [ rsp + 0xf0 ]
adcx r8, [ rsp + 0x1a8 ]
mov rcx, [ rsp + 0xe8 ]
adcx rcx, [ rsp + 0x1a0 ]
mov r11, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x1c8 ], rbx
mov [ rsp + 0x1d0 ], r9
mulx r9, rbx, [ rax + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x1d8 ], r10
mulx r10, r11, [ rsi + 0x30 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x1e0 ], rcx
mov [ rsp + 0x1e8 ], r8
mulx r8, rcx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x1f0 ], r8
mov [ rsp + 0x1f8 ], rcx
mulx rcx, r8, r15
test al, al
adox r8, [ rsp + 0x90 ]
adox rcx, [ rsp + 0x88 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x200 ], r10
mulx r10, r15, [ rax + 0x8 ]
adcx r12, r15
adcx r10, rbp
mov rdx, [ rsi + 0x30 ]
mulx r15, rbp, [ rax + 0x10 ]
add rdi, rbx
adcx r9, r13
test al, al
adox rdi, [ rsp + 0xe0 ]
adox r9, [ rsp + 0xd8 ]
adcx r12, rbp
adcx r15, r10
mov rdx, [ rax + 0x0 ]
mulx rbx, r13, [ rsi + 0x30 ]
test al, al
adox r8, r13
adox rbx, rcx
mov rdx, [ rax + 0x10 ]
mulx r10, rcx, [ rsi + 0x20 ]
mov rdx, [ rax + 0x20 ]
mulx r13, rbp, [ rsi + 0x10 ]
mov rdx, r11
adcx rdx, [ rsp + 0x1e8 ]
mov [ rsp + 0x208 ], r13
mov r13, [ rsp + 0x200 ]
adcx r13, [ rsp + 0x1e0 ]
mov r11, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x210 ], rbp
mov [ rsp + 0x218 ], r9
mulx r9, rbp, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x220 ], rdi
mov [ rsp + 0x228 ], r10
mulx r10, rdi, [ rax + 0x30 ]
add r12, rbp
adcx r9, r15
add r12, [ rsp + 0x1d8 ]
adcx r9, [ rsp + 0x1d0 ]
mov rdx, [ rsi + 0x28 ]
mulx rbp, r15, [ rax + 0x10 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x230 ], r10
mov [ rsp + 0x238 ], rdi
mulx rdi, r10, [ rsi + 0x10 ]
add r12, [ rsp + 0xa8 ]
adcx r9, [ rsp + 0xa0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x240 ], rdi
mov [ rsp + 0x248 ], r10
mulx r10, rdi, [ rax + 0x30 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x250 ], r10
mov [ rsp + 0x258 ], rdi
mulx rdi, r10, [ rsi + 0x10 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x260 ], r9
mov [ rsp + 0x268 ], r12
mulx r12, r9, [ rsi + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x270 ], r12
mov [ rsp + 0x278 ], r9
mulx r9, r12, [ rsi + 0x20 ]
add r11, r15
adcx rbp, r13
add r8, [ rsp + 0x1f8 ]
adcx rbx, [ rsp + 0x1f0 ]
mov rdx, [ rax + 0x28 ]
mulx r15, r13, [ rsi + 0x8 ]
test al, al
adox r8, rcx
adox rbx, [ rsp + 0x228 ]
mov rdx, r10
adcx rdx, [ rsp + 0x220 ]
adcx rdi, [ rsp + 0x218 ]
add r8, [ rsp - 0x30 ]
adcx rbx, [ rsp - 0x38 ]
xor rcx, rcx
adox r8, [ rsp + 0x210 ]
adox rbx, [ rsp + 0x208 ]
adcx r8, r13
adcx r15, rbx
test al, al
adox r8, [ rsp + 0x238 ]
adox r15, [ rsp + 0x230 ]
mov r10, rdx
mov rdx, [ rsi + 0x10 ]
mulx rbx, r13, [ rax + 0x30 ]
mov rdx, r13
adcx rdx, [ rsp + 0x268 ]
adcx rbx, [ rsp + 0x260 ]
mov r13, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x280 ], r15
mulx r15, rcx, [ rax + 0x20 ]
add r10, [ rsp + 0x278 ]
adcx rdi, [ rsp + 0x270 ]
test al, al
adox r10, [ rsp - 0x40 ]
adox rdi, [ rsp - 0x48 ]
adcx r11, r12
adcx r9, rbp
mov rdx, [ rsp + 0x1c0 ]
mov r12, [ rsp + 0x1c8 ]
shrd r12, rdx, 58
shr rdx, 58
test al, al
adox r10, r12
adox rdx, rdi
adcx r11, rcx
adcx r15, r9
add r11, [ rsp + 0x248 ]
adcx r15, [ rsp + 0x240 ]
mov rbp, rdx
mov rdx, [ rsi + 0x0 ]
mulx rdi, rcx, [ rax + 0x40 ]
xor rdx, rdx
adox r11, [ rsp + 0x258 ]
adox r15, [ rsp + 0x250 ]
adcx r13, [ rsp + 0xb8 ]
adcx rbx, [ rsp + 0xb0 ]
mov r9, r10
shrd r9, rbp, 58
shr rbp, 58
xor r12, r12
adox r8, r9
adox rbp, [ rsp + 0x280 ]
mov rdx, 0x3ffffffffffffff 
mov r9, r8
and r9, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x288 ], r9
mulx r9, r12, [ rax + 0x38 ]
shrd r8, rbp, 58
shr rbp, 58
test al, al
adox r11, r12
adox r9, r15
adcx r11, r8
adcx rbp, r9
mov rdx, r11
shrd rdx, rbp, 58
shr rbp, 58
mov r15, 0x3a 
bzhi r12, r14, r15
adox r13, rcx
adox rdi, rbx
test al, al
adox r13, rdx
adox rbp, rdi
mov r14, r13
shrd r14, rbp, 57
shr rbp, 57
add r14, [ rsp + 0x178 ]
adc rbp, 0x0
bzhi rcx, r14, r15
shrd r14, rbp, 58
lea r14, [ r14 + r12 ]
bzhi rbx, [ rsp + 0x1c8 ], r15
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x0 ], rcx
bzhi r9, r14, r15
shr r14, 58
add r14, [ rsp + 0x1b8 ]
mov [ r8 + 0x20 ], rbx
mov rdx, 0x1ffffffffffffff 
and r13, rdx
mov [ r8 + 0x40 ], r13
bzhi r12, r10, r15
bzhi r10, r11, r15
mov [ r8 + 0x38 ], r10
mov [ r8 + 0x28 ], r12
mov r11, [ rsp + 0x288 ]
mov [ r8 + 0x30 ], r11
mov [ r8 + 0x8 ], r9
mov [ r8 + 0x10 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 784
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.1667
; seed 0482643503319368 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 6525269 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=69, initial num_batches=31): 132002 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.020229357594299942
; number reverted permutation / tried permutation: 60949 / 89779 =67.888%
; number reverted decision / tried decision: 52046 / 90220 =57.688%
; validated in 5.706s
