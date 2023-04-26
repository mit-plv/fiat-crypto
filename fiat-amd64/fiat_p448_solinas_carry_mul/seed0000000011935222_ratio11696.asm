SECTION .text
	GLOBAL fiat_p448_solinas_carry_mul
fiat_p448_solinas_carry_mul:
sub rsp, 608
mov rax, rdx
mov rdx, [ rsi + 0x30 ]
mulx r11, r10, [ rax + 0x28 ]
mov rdx, [ rsi + 0x38 ]
mulx r8, rcx, [ rax + 0x38 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x38 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], r12
mov [ rsp - 0x40 ], rbp
mulx rbp, r12, [ rax + 0x38 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x38 ], rbx
mov [ rsp - 0x30 ], r9
mulx r9, rbx, [ rax + 0x20 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x28 ], rbp
mov [ rsp - 0x20 ], r12
mulx r12, rbp, [ rax + 0x30 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x18 ], rdi
mov [ rsp - 0x10 ], r15
mulx r15, rdi, [ rax + 0x28 ]
mov rdx, rcx
test al, al
adox rdx, rcx
mov [ rsp - 0x8 ], r14
mov r14, r8
adox r14, r8
mov [ rsp + 0x0 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x8 ], r12
mov [ rsp + 0x10 ], rbp
mulx rbp, r12, [ rax + 0x10 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x18 ], rbp
mov [ rsp + 0x20 ], r12
mulx r12, rbp, [ rax + 0x20 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x28 ], r15
mov [ rsp + 0x30 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x38 ], rdi
mov [ rsp + 0x40 ], r15
mulx r15, rdi, [ rax + 0x8 ]
adcx rbp, r10
adcx r11, r12
mov rdx, [ rsi + 0x18 ]
mulx r12, r10, [ rax + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x48 ], r12
mov [ rsp + 0x50 ], r10
mulx r10, r12, [ rsi + 0x28 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x58 ], r11
mov [ rsp + 0x60 ], rbp
mulx rbp, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x68 ], rbp
mov [ rsp + 0x70 ], r11
mulx r11, rbp, [ rax + 0x20 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x78 ], r10
mov [ rsp + 0x80 ], r12
mulx r12, r10, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x88 ], r12
mov [ rsp + 0x90 ], r10
mulx r10, r12, [ rax + 0x28 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x98 ], r10
mov [ rsp + 0xa0 ], r12
mulx r12, r10, [ rax + 0x18 ]
test al, al
adox r13, r10
mov rdx, r12
adox rdx, r14
adcx r13, rbx
mov r14, r9
adcx r14, rdx
test al, al
adox rcx, r10
adox r12, r8
adcx r13, [ rsp + 0x30 ]
adcx r14, [ rsp + 0x28 ]
mov rdx, [ rax + 0x38 ]
mulx r10, r8, [ rsi + 0x28 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xa8 ], r14
mov [ rsp + 0xb0 ], r13
mulx r13, r14, [ rsi + 0x38 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0xb8 ], r11
mov [ rsp + 0xc0 ], rbp
mulx rbp, r11, [ rsi + 0x30 ]
mov rdx, r14
test al, al
adox rdx, r11
mov [ rsp + 0xc8 ], r15
mov r15, rbp
adox r15, r13
adcx rcx, rbx
adcx r9, r12
add rdx, r8
mov rbx, r10
adcx rbx, r15
mov r12, rdx
test al, al
adox r12, r14
adox r13, rbx
adcx r12, r11
adcx rbp, r13
mov r14, rdx
mov rdx, [ rsi + 0x30 ]
mulx r15, r11, [ rax + 0x10 ]
add r12, r8
adcx r10, rbp
test al, al
adox r12, rdi
adox r10, [ rsp + 0xc8 ]
mov rdx, [ rsi + 0x28 ]
mulx r13, r8, [ rax + 0x18 ]
adcx r12, r11
mov rdx, r15
adcx rdx, r10
xor rbp, rbp
adox r14, rdi
adox rbx, [ rsp + 0xc8 ]
mov rdi, rdx
mov rdx, [ rsi + 0x30 ]
mulx rbp, r10, [ rax + 0x38 ]
adcx r14, r11
adcx r15, rbx
mov rdx, r10
xor r11, r11
adox rdx, [ rsp + 0x10 ]
mov rbx, rbp
adox rbx, [ rsp + 0x8 ]
mov [ rsp + 0xd0 ], r15
mov r15, rdx
adcx r15, [ rsp + 0x10 ]
mov [ rsp + 0xd8 ], r14
mov r14, rbx
adcx r14, [ rsp + 0x8 ]
test al, al
adox r12, r8
mov [ rsp + 0xe0 ], r9
mov r9, r13
adox r9, rdi
adcx r15, r10
adcx rbp, r14
xor rdi, rdi
adox rdx, [ rsp + 0x0 ]
adox rbx, [ rsp - 0x8 ]
mov r11, rdx
mov rdx, [ rax + 0x18 ]
mulx r14, r10, [ rsi + 0x30 ]
adcx r11, r10
mov rdx, r14
adcx rdx, rbx
add r12, [ rsp + 0xc0 ]
adcx r9, [ rsp + 0xb8 ]
xor rbx, rbx
adox r11, [ rsp + 0x80 ]
adox rdx, [ rsp + 0x78 ]
adcx r12, [ rsp - 0x10 ]
adcx r9, [ rsp - 0x18 ]
test al, al
adox r15, [ rsp + 0x0 ]
adox rbp, [ rsp - 0x8 ]
mov rdi, rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0xe8 ], r9
mulx r9, rbx, [ rsi + 0x20 ]
adcx rcx, [ rsp + 0x30 ]
mov rdx, [ rsp + 0x28 ]
adcx rdx, [ rsp + 0xe0 ]
test al, al
adox r15, r10
adox r14, rbp
adcx r11, [ rsp + 0x90 ]
adcx rdi, [ rsp + 0x88 ]
add r15, [ rsp + 0x80 ]
adcx r14, [ rsp + 0x78 ]
xor r10, r10
adox rcx, rbx
mov rbp, r9
adox rbp, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xf0 ], rdi
mulx rdi, r10, [ rax + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xf8 ], r11
mov [ rsp + 0x100 ], r14
mulx r14, r11, [ rax + 0x30 ]
mov rdx, r11
adcx rdx, [ rsp + 0x60 ]
adcx r14, [ rsp + 0x58 ]
mov r11, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x108 ], r15
mov [ rsp + 0x110 ], r12
mulx r12, r15, [ rax + 0x38 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x118 ], rdi
mov [ rsp + 0x120 ], r10
mulx r10, rdi, [ rsi + 0x10 ]
xor rdx, rdx
adox r11, r15
adox r12, r14
mov rdx, [ rsi + 0x30 ]
mulx r15, r14, [ rax + 0x8 ]
adcx rcx, [ rsp - 0x20 ]
adcx rbp, [ rsp - 0x28 ]
mov rdx, rbx
add rdx, [ rsp + 0xb0 ]
adcx r9, [ rsp + 0xa8 ]
mov rbx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x128 ], rbp
mov [ rsp + 0x130 ], rcx
mulx rcx, rbp, [ rax + 0x0 ]
mov rdx, r11
mov [ rsp + 0x138 ], r9
xor r9, r9
adox rdx, rbp
adox rcx, r12
adcx rdx, rdi
adcx r10, rcx
xor rdi, rdi
adox r11, [ rsp + 0x120 ]
adox r12, [ rsp + 0x118 ]
adcx r11, r14
adcx r15, r12
test al, al
adox rdx, [ rsp + 0x20 ]
adox r10, [ rsp + 0x18 ]
mov r9, r8
adcx r9, [ rsp + 0xd8 ]
adcx r13, [ rsp + 0xd0 ]
mov r8, rdx
mov rdx, [ rax + 0x10 ]
mulx rbp, r14, [ rsi + 0x28 ]
xor rdx, rdx
adox r11, r14
adox rbp, r15
adcx r9, [ rsp + 0xc0 ]
adcx r13, [ rsp + 0xb8 ]
mov rdx, [ rax + 0x0 ]
mulx rcx, rdi, [ rsi + 0x0 ]
test al, al
adox r9, [ rsp - 0x10 ]
adox r13, [ rsp - 0x18 ]
mov rdx, [ rax + 0x18 ]
mulx r15, r12, [ rsi + 0x20 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x140 ], rbx
mulx rbx, r14, [ rsi + 0x8 ]
adcx r11, r12
adcx r15, rbp
mov rdx, [ rsi + 0x18 ]
mulx r12, rbp, [ rax + 0x20 ]
mov rdx, [ rsp + 0x110 ]
test al, al
adox rdx, [ rsp + 0x40 ]
mov [ rsp + 0x148 ], r10
mov r10, [ rsp + 0xe8 ]
adox r10, [ rsp + 0x38 ]
adcx r9, [ rsp + 0x40 ]
adcx r13, [ rsp + 0x38 ]
mov [ rsp + 0x150 ], r8
xor r8, r8
adox r11, rbp
adox r12, r15
mov r15, [ rsp + 0x90 ]
mov rbp, r15
adcx rbp, [ rsp + 0x108 ]
mov [ rsp + 0x158 ], r12
mov r12, [ rsp + 0x88 ]
adcx r12, [ rsp + 0x100 ]
test al, al
adox r9, r14
mov r15, rbx
adox r15, r13
adcx rdx, r14
adcx rbx, r10
xor r14, r14
adox r9, rdi
adox rcx, r15
mov r8, rdx
mov rdx, [ rsi + 0x8 ]
mulx r10, rdi, [ rax + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mulx r15, r13, [ rax + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x160 ], rcx
mulx rcx, r14, [ rax + 0x30 ]
adcx r8, r13
adcx r15, rbx
mov rdx, [ rsi + 0x28 ]
mulx r13, rbx, [ rax + 0x0 ]
test al, al
adox rbp, r14
mov rdx, rcx
adox rdx, r12
adcx rbp, [ rsp - 0x30 ]
adcx rdx, [ rsp - 0x38 ]
mov r12, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x168 ], r9
mov [ rsp + 0x170 ], r10
mulx r10, r9, [ rsi + 0x0 ]
mov rdx, r14
mov [ rsp + 0x178 ], r10
xor r10, r10
adox rdx, [ rsp + 0xf8 ]
adox rcx, [ rsp + 0xf0 ]
adcx rdx, [ rsp - 0x30 ]
adcx rcx, [ rsp - 0x38 ]
mov r14, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x180 ], rcx
mulx rcx, r10, [ rsi + 0x18 ]
add r8, r10
adcx rcx, r15
test al, al
adox rbp, rbx
adox r13, r12
mov rdx, [ rax + 0x38 ]
mulx rbx, r15, [ rsi + 0x0 ]
mov rdx, [ rax + 0x30 ]
mulx r10, r12, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x188 ], r14
mov [ rsp + 0x190 ], r9
mulx r9, r14, [ rax + 0x18 ]
mov rdx, r14
adcx rdx, [ rsp + 0x150 ]
adcx r9, [ rsp + 0x148 ]
mov r14, 0x38 
mov [ rsp + 0x198 ], rdi
bzhi rdi, rdx, r14
shrd rdx, r9, 56
add r11, [ rsp + 0xa0 ]
mov r9, [ rsp + 0x98 ]
adcx r9, [ rsp + 0x158 ]
xor r14, r14
adox r11, r12
adox r10, r9
adcx r11, r15
adcx rbx, r10
mov r15, rdx
mov rdx, [ rsi + 0x10 ]
mulx r9, r12, [ rax + 0x10 ]
mov rdx, [ rax + 0x8 ]
mulx r14, r10, [ rsi + 0x20 ]
test al, al
adox rbp, r10
adox r14, r13
mov rdx, r11
shrd rdx, rbx, 56
mov r13, rdx
mov rdx, [ rsi + 0x0 ]
mulx r10, rbx, [ rax + 0x20 ]
xor rdx, rdx
adox r8, r12
adox r9, rcx
adcx r8, [ rsp + 0x198 ]
adcx r9, [ rsp + 0x170 ]
mov rdx, [ rsi + 0x20 ]
mulx r12, rcx, [ rax + 0x10 ]
add r8, rbx
adcx r10, r9
mov rdx, [ rsi + 0x30 ]
mulx r9, rbx, [ rax + 0x0 ]
mov rdx, 0xffffffffffffff 
and r11, rdx
mov rdx, [ rsp - 0x20 ]
mov [ rsp + 0x1a0 ], rdi
mov rdi, rdx
adox rdi, [ rsp + 0x140 ]
mov [ rsp + 0x1a8 ], r11
mov r11, [ rsp - 0x28 ]
adox r11, [ rsp + 0x138 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x1b0 ], r13
mov [ rsp + 0x1b8 ], r10
mulx r10, r13, [ rsi + 0x28 ]
adcx rdi, rbx
adcx r9, r11
mov rdx, [ rax + 0x20 ]
mulx r11, rbx, [ rsi + 0x8 ]
xor rdx, rdx
adox rdi, r13
adox r10, r9
mov rdx, [ rsi + 0x8 ]
mulx r9, r13, [ rax + 0x28 ]
adcx rbp, [ rsp + 0x70 ]
adcx r14, [ rsp + 0x68 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x1c0 ], r9
mov [ rsp + 0x1c8 ], r13
mulx r13, r9, [ rsi + 0x10 ]
add rbp, r9
adcx r13, r14
test al, al
adox rdi, rcx
adox r12, r10
adcx rdi, [ rsp + 0x50 ]
adcx r12, [ rsp + 0x48 ]
mov rdx, [ rsi + 0x10 ]
mulx r10, rcx, [ rax + 0x20 ]
xor rdx, rdx
adox r8, r15
mov r14, [ rsp + 0x1b8 ]
adox r14, rdx
adcx rdi, rcx
adcx r10, r12
mov rdx, [ rax + 0x0 ]
mulx r9, r15, [ rsi + 0x8 ]
mov rdx, r8
test al, al
adox rdx, [ rsp + 0x1b0 ]
mov r12, 0x0 
adox r14, r12
mov rcx, rdx
shrd rcx, r14, 56
mov r8, rdx
mov rdx, [ rsi + 0x0 ]
mulx r12, r14, [ rax + 0x30 ]
add rbp, rbx
adcx r11, r13
test al, al
adox rbp, [ rsp + 0x190 ]
adox r11, [ rsp + 0x178 ]
mov rdx, [ rsi + 0x0 ]
mulx r13, rbx, [ rax + 0x10 ]
adcx rbp, rcx
adc r11, 0x0
mov rdx, 0xffffffffffffff 
mov rcx, rbp
and rcx, rdx
shrd rbp, r11, 56
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x1d0 ], rcx
mulx rcx, r11, [ rax + 0x0 ]
mov rdx, r11
mov [ rsp + 0x1d8 ], r13
xor r13, r13
adox rdx, [ rsp + 0x130 ]
adox rcx, [ rsp + 0x128 ]
adcx rdi, [ rsp + 0x1c8 ]
adcx r10, [ rsp + 0x1c0 ]
test al, al
adox rdi, r14
adox r12, r10
mov r14, rdx
mov rdx, [ rax + 0x8 ]
mulx r10, r11, [ rsi + 0x0 ]
mov rdx, r15
adcx rdx, [ rsp + 0x188 ]
adcx r9, [ rsp + 0x180 ]
test al, al
adox rdx, r11
adox r10, r9
adcx rdi, rbp
adc r12, 0x0
xor r15, r15
adox r14, [ rsp - 0x40 ]
adox rcx, [ rsp - 0x48 ]
mov r13, 0xffffffffffffff 
mov rbp, rdi
and rbp, r13
shrd rdi, r12, 56
add rdi, [ rsp + 0x1a8 ]
mov r11, rdi
shr r11, 56
mov r9, [ rsp + 0x168 ]
mov r12, r9
xor r13, r13
adox r12, [ rsp + 0x1b0 ]
mov r15, [ rsp + 0x160 ]
adox r15, r13
mov r9, r12
shrd r9, r15, 56
test al, al
adox rdx, r9
adox r10, r13
adcx r14, rbx
adcx rcx, [ rsp + 0x1d8 ]
mov rbx, rdx
shrd rbx, r10, 56
test al, al
adox r14, rbx
adox rcx, r13
mov r15, 0xffffffffffffff 
mov r9, r14
and r9, r15
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x10 ], r9
and r8, r15
lea r8, [ r8 + r11 ]
shrd r14, rcx, 56
add r14, [ rsp + 0x1a0 ]
mov rbx, r14
and rbx, r15
and r12, r15
and rdi, r15
mov [ r10 + 0x38 ], rdi
lea r12, [ r12 + r11 ]
mov [ r10 + 0x18 ], rbx
mov r11, r12
and r11, r15
shr r12, 56
shr r14, 56
lea r14, [ r14 + r8 ]
mov rcx, r14
and rcx, r15
and rdx, r15
mov [ r10 + 0x20 ], rcx
lea r12, [ r12 + rdx ]
shr r14, 56
mov [ r10 + 0x8 ], r12
add r14, [ rsp + 0x1d0 ]
mov [ r10 + 0x28 ], r14
mov [ r10 + 0x0 ], r11
mov [ r10 + 0x30 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 608
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.1696
; seed 1375376648550693 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5515260 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=77, initial num_batches=31): 127509 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.02311930897183451
; number reverted permutation / tried permutation: 57643 / 89800 =64.190%
; number reverted decision / tried decision: 47918 / 90199 =53.125%
; validated in 4.562s
