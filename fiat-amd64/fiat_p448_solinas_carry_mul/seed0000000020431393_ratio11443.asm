SECTION .text
	GLOBAL fiat_p448_solinas_carry_mul
fiat_p448_solinas_carry_mul:
sub rsp, 592
mov rax, rdx
mov rdx, [ rdx + 0x38 ]
mulx r11, r10, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x30 ]
mulx r8, rcx, [ rax + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x30 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x28 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], r14
mov [ rsp - 0x40 ], r13
mulx r13, r14, [ rax + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x38 ], r13
mov [ rsp - 0x30 ], r14
mulx r14, r13, [ rax + 0x20 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x28 ], rdi
mov [ rsp - 0x20 ], r15
mulx r15, rdi, [ rax + 0x18 ]
mov rdx, r10
add rdx, rdi
mov [ rsp - 0x18 ], r12
mov r12, r15
adcx r12, r11
mov [ rsp - 0x10 ], rbp
mov rbp, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x8 ], rbx
mov [ rsp + 0x0 ], r9
mulx r9, rbx, [ rsi + 0x30 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x8 ], r8
mov [ rsp + 0x10 ], rcx
mulx rcx, r8, [ rsi + 0x10 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x18 ], rcx
mov [ rsp + 0x20 ], r8
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x28 ], r8
mov [ rsp + 0x30 ], rcx
mulx rcx, r8, [ rax + 0x10 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x38 ], r12
mov [ rsp + 0x40 ], rbp
mulx rbp, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x48 ], rbp
mov [ rsp + 0x50 ], r12
mulx r12, rbp, [ rax + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x58 ], r9
mov [ rsp + 0x60 ], rbx
mulx rbx, r9, [ rax + 0x38 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x68 ], r14
mov [ rsp + 0x70 ], r13
mulx r13, r14, [ rax + 0x28 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x78 ], r12
mov [ rsp + 0x80 ], rbp
mulx rbp, r12, [ rsi + 0x30 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x88 ], rcx
mov [ rsp + 0x90 ], r8
mulx r8, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x98 ], r8
mov [ rsp + 0xa0 ], rcx
mulx rcx, r8, [ rax + 0x8 ]
mov rdx, r14
test al, al
adox rdx, r12
mov [ rsp + 0xa8 ], rcx
mov rcx, rbp
adox rcx, r13
adcx rdx, r9
mov [ rsp + 0xb0 ], r8
mov r8, rbx
adcx r8, rcx
mov rcx, rdx
add rcx, r14
adcx r13, r8
add rcx, r12
adcx rbp, r13
test al, al
adox rcx, r9
adox rbx, rbp
mov r9, rdx
mov rdx, [ rsi + 0x20 ]
mulx r12, r14, [ rax + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mulx rbp, r13, [ rax + 0x10 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xb8 ], rbp
mov [ rsp + 0xc0 ], r13
mulx r13, rbp, [ rax + 0x8 ]
adcx rcx, rbp
mov rdx, r13
adcx rdx, rbx
mov rbx, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xc8 ], r12
mov [ rsp + 0xd0 ], r14
mulx r14, r12, [ rax + 0x28 ]
xor rdx, rdx
adox r9, rbp
adox r13, r8
mov rdx, [ rsi + 0x38 ]
mulx rbp, r8, [ rax + 0x20 ]
adcx r9, [ rsp + 0x90 ]
adcx r13, [ rsp + 0x88 ]
xor rdx, rdx
adox r8, r12
adox r14, rbp
adcx r9, [ rsp + 0x80 ]
adcx r13, [ rsp + 0x78 ]
test al, al
adox rcx, [ rsp + 0x90 ]
adox rbx, [ rsp + 0x88 ]
adcx r9, [ rsp + 0x70 ]
adcx r13, [ rsp + 0x68 ]
xor r12, r12
adox rcx, [ rsp + 0x80 ]
adox rbx, [ rsp + 0x78 ]
mov rdx, [ rsi + 0x20 ]
mulx r12, rbp, [ rax + 0x38 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xd8 ], rbx
mov [ rsp + 0xe0 ], rcx
mulx rcx, rbx, [ rax + 0x30 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xe8 ], r13
mov [ rsp + 0xf0 ], r9
mulx r9, r13, [ rax + 0x38 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xf8 ], r9
mov [ rsp + 0x100 ], r13
mulx r13, r9, [ rax + 0x10 ]
adcx r8, rbx
adcx rcx, r14
mov rdx, [ rsp + 0x40 ]
xor r14, r14
adox rdx, [ rsp + 0x60 ]
mov rbx, [ rsp + 0x38 ]
adox rbx, [ rsp + 0x58 ]
adcx r8, rbp
adcx r12, rcx
mov rbp, rdx
mov rdx, [ rax + 0x30 ]
mulx r14, rcx, [ rsi + 0x38 ]
mov rdx, rcx
test al, al
adox rdx, [ rsp + 0x100 ]
mov [ rsp + 0x108 ], r12
mov r12, r14
adox r12, [ rsp + 0xf8 ]
mov [ rsp + 0x110 ], r8
mov r8, rdx
adcx r8, r9
mov [ rsp + 0x118 ], rbx
mov rbx, r13
adcx rbx, r12
test al, al
adox rdx, rcx
adox r14, r12
adcx rdx, [ rsp + 0x100 ]
adcx r14, [ rsp + 0xf8 ]
test al, al
adox rdx, r9
adox r13, r14
adcx r8, [ rsp + 0x10 ]
adcx rbx, [ rsp + 0x8 ]
add rdx, [ rsp + 0x10 ]
adcx r13, [ rsp + 0x8 ]
mov r9, r10
xor rcx, rcx
adox r9, r10
adox r11, r11
adcx r9, rdi
adcx r15, r11
mov r10, rdx
mov rdx, [ rax + 0x28 ]
mulx r12, rdi, [ rsi + 0x28 ]
test al, al
adox rbp, rdi
mov rdx, r12
adox rdx, [ rsp + 0x118 ]
adcx rbp, [ rsp + 0x0 ]
adcx rdx, [ rsp - 0x8 ]
xor r14, r14
adox r9, [ rsp + 0x60 ]
adox r15, [ rsp + 0x58 ]
mov rcx, rdx
mov rdx, [ rax + 0x28 ]
mulx r14, r11, [ rsi + 0x18 ]
adcx r9, rdi
adcx r12, r15
mov rdx, [ rsi + 0x18 ]
mulx r15, rdi, [ rax + 0x38 ]
test al, al
adox rbp, rdi
mov rdx, r15
adox rdx, rcx
adcx r9, [ rsp + 0x0 ]
adcx r12, [ rsp - 0x8 ]
mov rcx, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x120 ], rbp
mov [ rsp + 0x128 ], r14
mulx r14, rbp, [ rax + 0x20 ]
test al, al
adox r8, rbp
mov rdx, r14
adox rdx, rbx
mov rbx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x130 ], r8
mov [ rsp + 0x138 ], rcx
mulx rcx, r8, [ rax + 0x0 ]
adcx r10, rbp
adcx r14, r13
add r9, rdi
adcx r15, r12
mov rdx, r11
add rdx, [ rsp + 0xf0 ]
mov r13, [ rsp + 0x128 ]
mov rdi, r13
adcx rdi, [ rsp + 0xe8 ]
mov r12, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x140 ], r15
mulx r15, rbp, [ rax + 0x30 ]
mov rdx, r8
add rdx, [ rsp + 0x120 ]
adcx rcx, [ rsp + 0x138 ]
test al, al
adox r12, rbp
mov r8, r15
adox r8, rdi
mov rdi, [ rsp + 0xe0 ]
adcx rdi, [ rsp + 0x70 ]
mov [ rsp + 0x148 ], rcx
mov rcx, [ rsp + 0xd8 ]
adcx rcx, [ rsp + 0x68 ]
add rdi, r11
adcx r13, rcx
mov r11, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x150 ], r9
mulx r9, rcx, [ rsi + 0x38 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x158 ], r11
mov [ rsp + 0x160 ], rbx
mulx rbx, r11, [ rsi + 0x8 ]
xor rdx, rdx
adox rdi, rbp
adox r15, r13
mov rdx, [ rsi + 0x28 ]
mulx r13, rbp, [ rax + 0x10 ]
adcx rdi, r11
mov rdx, rbx
adcx rdx, r15
mov r15, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x168 ], r14
mov [ rsp + 0x170 ], r10
mulx r10, r14, [ rax + 0x0 ]
xor rdx, rdx
adox r12, r11
adox rbx, r8
mov r8, rcx
adcx r8, [ rsp + 0x110 ]
adcx r9, [ rsp + 0x108 ]
mov rdx, [ rsi + 0x20 ]
mulx r11, rcx, [ rax + 0x18 ]
test al, al
adox r8, [ rsp + 0xb0 ]
adox r9, [ rsp + 0xa8 ]
adcx r8, rbp
adcx r13, r9
test al, al
adox r8, rcx
adox r11, r13
mov rdx, [ rax + 0x20 ]
mulx rcx, rbp, [ rsi + 0x18 ]
mov rdx, r14
adcx rdx, [ rsp + 0x110 ]
adcx r10, [ rsp + 0x108 ]
test al, al
adox r8, rbp
adox rcx, r11
mov r14, rdx
mov rdx, [ rsi + 0x18 ]
mulx r13, r9, [ rax + 0x8 ]
adcx r8, [ rsp - 0x10 ]
adcx rcx, [ rsp - 0x18 ]
mov rdx, [ rsi + 0x10 ]
mulx rbp, r11, [ rax + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x178 ], r10
mov [ rsp + 0x180 ], r14
mulx r14, r10, [ rax + 0x30 ]
xor rdx, rdx
adox rdi, [ rsp - 0x20 ]
adox r15, [ rsp - 0x28 ]
adcx r8, r10
adcx r14, rcx
add rdi, r9
adcx r13, r15
mov rdx, [ rax + 0x0 ]
mulx rcx, r9, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx r15, r10, [ rax + 0x10 ]
xor rdx, rdx
adox rdi, r11
adox rbp, r13
mov rdx, [ rax + 0x18 ]
mulx r13, r11, [ rsi + 0x8 ]
adcx rdi, r11
adcx r13, rbp
xor rdx, rdx
adox r12, r9
adox rcx, rbx
mov rdx, [ rax + 0x38 ]
mulx r9, rbx, [ rsi + 0x0 ]
adcx r8, rbx
adcx r9, r14
mov rdx, r8
shrd rdx, r9, 56
mov r14, 0xffffffffffffff 
and r8, r14
mov rbp, [ rsp + 0x180 ]
adox rbp, [ rsp + 0x20 ]
mov r11, [ rsp + 0x178 ]
adox r11, [ rsp + 0x18 ]
mov rbx, rdx
mov rdx, [ rax + 0x20 ]
mulx r14, r9, [ rsi + 0x0 ]
adcx rdi, r9
adcx r14, r13
mov rdx, [ rsi + 0x20 ]
mulx r9, r13, [ rax + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x188 ], r8
mov [ rsp + 0x190 ], rcx
mulx rcx, r8, [ rax + 0x18 ]
test al, al
adox rbp, r10
adox r15, r11
adcx rbp, r8
adcx rcx, r15
mov rdx, rbp
shrd rdx, rcx, 56
mov r10, 0xffffffffffffff 
and rbp, r10
mov r11, r13
adox r11, [ rsp + 0x170 ]
mov r8, r9
adox r8, [ rsp + 0x168 ]
adcx rdi, rdx
adc r14, 0x0
mov rdx, [ rax + 0x30 ]
mulx rcx, r15, [ rsi + 0x18 ]
test al, al
adox r11, r15
mov rdx, rcx
adox rdx, r8
adcx r11, [ rsp + 0x50 ]
adcx rdx, [ rsp + 0x48 ]
mov r8, rbx
add r8, rdi
adc r14, 0x0
mov rdi, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x198 ], rbp
mulx rbp, r10, [ rax + 0x10 ]
mov rdx, r13
test al, al
adox rdx, [ rsp + 0x130 ]
adox r9, [ rsp + 0x160 ]
adcx rdx, r15
adcx rcx, r9
mov r13, rdx
mov rdx, [ rax + 0x20 ]
mulx r9, r15, [ rsi + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x1a0 ], r9
mov [ rsp + 0x1a8 ], r15
mulx r15, r9, [ rsi + 0x28 ]
xor rdx, rdx
adox r11, r9
adox r15, rdi
adcx r11, [ rsp + 0xd0 ]
adcx r15, [ rsp + 0xc8 ]
xor rdi, rdi
adox r11, r10
adox rbp, r15
adcx r11, [ rsp + 0xa0 ]
adcx rbp, [ rsp + 0x98 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r10, [ rax + 0x10 ]
xor rdx, rdx
adox r11, [ rsp - 0x30 ]
adox rbp, [ rsp - 0x38 ]
adcx r11, [ rsp + 0x30 ]
adcx rbp, [ rsp + 0x28 ]
add r13, [ rsp + 0x50 ]
adcx rcx, [ rsp + 0x48 ]
mov rdx, [ rax + 0x0 ]
mulx r15, rdi, [ rsi + 0x8 ]
mov rdx, 0x38 
mov [ rsp + 0x1b0 ], r9
bzhi r9, r8, rdx
shrd r8, r14, 56
xor r14, r14
adox rbx, r12
mov rdx, [ rsp + 0x190 ]
adox rdx, r14
adcx r11, r8
adc rbp, 0x0
test al, al
adox r13, rdi
adox r15, rcx
mov r12, rdx
mov rdx, [ rax + 0x0 ]
mulx rdi, rcx, [ rsi + 0x30 ]
mov rdx, rcx
adcx rdx, [ rsp + 0x150 ]
adcx rdi, [ rsp + 0x140 ]
xor r8, r8
adox rdx, [ rsp - 0x40 ]
adox rdi, [ rsp - 0x48 ]
mov r14, 0x38 
bzhi rcx, r11, r14
mov r8, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x1b8 ], rcx
mulx rcx, r14, [ rsi + 0x0 ]
shrd r11, rbp, 56
mov rdx, rbx
shrd rdx, r12, 56
test al, al
adox r13, r14
adox rcx, r15
adcx r13, rdx
adc rcx, 0x0
mov rdx, [ rsi + 0x8 ]
mulx rbp, r12, [ rax + 0x28 ]
test al, al
adox r8, [ rsp + 0xc0 ]
adox rdi, [ rsp + 0xb8 ]
mov rdx, r13
shrd rdx, rcx, 56
mov r15, 0x38 
bzhi r14, r13, r15
mov r13, rdx
mov rdx, [ rax + 0x18 ]
mulx r15, rcx, [ rsi + 0x18 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x1c0 ], r14
mov [ rsp + 0x1c8 ], r9
mulx r9, r14, [ rsi + 0x0 ]
adox r8, rcx
adox r15, rdi
test al, al
adox r8, [ rsp + 0x1a8 ]
adox r15, [ rsp + 0x1a0 ]
adcx r8, r12
adcx rbp, r15
add r8, r14
adcx r9, rbp
mov rdx, [ rax + 0x8 ]
mulx rdi, r12, [ rsi + 0x8 ]
mov rdx, r12
test al, al
adox rdx, [ rsp + 0x158 ]
adox rdi, [ rsp + 0x148 ]
adcx rdx, r10
adcx rdi, [ rsp + 0x1b0 ]
test al, al
adox r8, r11
mov r10, 0x0 
adox r9, r10
mov r11, 0x38 
bzhi rcx, r8, r11
adox rdx, r13
adox rdi, r10
mov r13, rdx
shrd r13, rdi, 56
shrd r8, r9, 56
add r8, [ rsp + 0x188 ]
add r13, [ rsp + 0x198 ]
bzhi r14, r8, r11
bzhi r15, r13, r11
shr r8, 56
bzhi rbp, rbx, r11
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x38 ], r14
mov [ rbx + 0x18 ], r15
mov r12, r8
add r12, [ rsp + 0x1c8 ]
lea rbp, [ rbp + r8 ]
shr r13, 56
bzhi r9, rbp, r11
lea r13, [ r13 + r12 ]
bzhi rdi, r13, r11
mov [ rbx + 0x20 ], rdi
shr r13, 56
shr rbp, 56
add rbp, [ rsp + 0x1c0 ]
bzhi r14, rdx, r11
mov [ rbx + 0x10 ], r14
add r13, [ rsp + 0x1b8 ]
mov [ rbx + 0x28 ], r13
mov [ rbx + 0x0 ], r9
mov [ rbx + 0x8 ], rbp
mov [ rbx + 0x30 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 592
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.1443
; seed 0600789956224162 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5545397 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=78, initial num_batches=31): 127293 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.022954713612028138
; number reverted permutation / tried permutation: 60626 / 90010 =67.355%
; number reverted decision / tried decision: 49042 / 89989 =54.498%
; validated in 4.484s
