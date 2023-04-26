SECTION .text
	GLOBAL fiat_p521_carry_square
fiat_p521_carry_square:
sub rsp, 480
mov rax, 0x2 
shlx r10, [ rsi + 0x30 ], rax
mov r11, [ rsi + 0x40 ]
mov rdx, r11
shl rdx, 0x1
mov r11, [ rsi + 0x40 ]
lea rcx, [ 4 * r11]
mov r11, rdx
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, rdx
mov rdx, rcx
mov [ rsp - 0x80 ], rbx
mulx rbx, rcx, [ rsi + 0x30 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x28 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mov r15, [ rsi + 0x38 ]
lea rax, [ 4 * r15]
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], r14
mov [ rsp - 0x40 ], r13
mulx r13, r14, [ rsi + 0x20 ]
mov [ rsp - 0x38 ], r12
mov [ rsp - 0x30 ], rbp
mulx rbp, r12, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x20 ], r14
mov [ rsp - 0x18 ], r9
mulx r9, r14, rax
mov rdx, rax
mov [ rsp - 0x10 ], r9
mulx r9, rax, [ rsi + 0x18 ]
mov [ rsp - 0x8 ], r14
mov r14, [ rsi + 0x28 ]
mov [ rsp + 0x0 ], r8
lea r8, [r14 + r14]
mov r14, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x8 ], rbp
mov [ rsp + 0x10 ], r12
mulx r12, rbp, rdx
mov rdx, r8
mov [ rsp + 0x18 ], r9
mulx r9, r8, [ rsi + 0x18 ]
mov [ rsp + 0x20 ], r9
mov [ rsp + 0x28 ], r8
mulx r8, r9, [ rsi + 0x0 ]
mov [ rsp + 0x30 ], r8
mov r8, 0x1 
mov [ rsp + 0x38 ], r9
shlx r9, [ rsi + 0x30 ], r8
xchg rdx, r13
mov [ rsp + 0x40 ], rax
mulx rax, r8, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x48 ], r11
mov [ rsp + 0x50 ], rbx
mulx rbx, r11, r9
test al, al
adox r8, rbp
adox r12, rax
mov rdx, [ rsi + 0x30 ]
mulx rax, rbp, r14
mov rdx, r14
mov [ rsp + 0x58 ], rbx
mulx rbx, r14, [ rsi + 0x10 ]
mov [ rsp + 0x60 ], r11
mov r11, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x68 ], r12
mov [ rsp + 0x70 ], r8
mulx r8, r12, r9
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x78 ], r8
mov r8, rdx
shl r8, 0x2
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x80 ], r12
lea r12, [rdx + rdx]
mov rdx, r8
mov [ rsp + 0x88 ], rax
mulx rax, r8, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x90 ], rbp
mov [ rsp + 0x98 ], r12
mulx r12, rbp, r10
xor rdx, rdx
adox r8, rbp
adox r12, rax
mov rax, [ rsi + 0x38 ]
lea rbp, [rax + rax]
adcx r8, r14
adcx rbx, r12
mov rdx, r10
mulx r10, rax, [ rsi + 0x28 ]
mov r14, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xa0 ], r10
mulx r10, r12, r11
mov rdx, rbp
mulx r11, rbp, [ rsi + 0x38 ]
mov [ rsp + 0xa8 ], rax
mov rax, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xb0 ], r10
mov [ rsp + 0xb8 ], r12
mulx r12, r10, r13
xor rdx, rdx
adox r8, r15
adox rdi, rbx
adcx rbp, rcx
adcx r11, [ rsp + 0x50 ]
mov rcx, [ rsp + 0xb8 ]
mov r15, rcx
test al, al
adox r15, [ rsp + 0xa8 ]
mov rbx, [ rsp + 0xb0 ]
adox rbx, [ rsp + 0xa0 ]
mov rcx, [ rsi + 0x18 ]
lea rdx, [rcx + rcx]
mov rcx, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0xc0 ], rbx
mov [ rsp + 0xc8 ], r15
mulx r15, rbx, [ rsp + 0x48 ]
mov rdx, r14
mov [ rsp + 0xd0 ], r15
mulx r15, r14, [ rsi + 0x20 ]
adcx r10, r14
adcx r15, r12
mov rdx, [ rsi + 0x10 ]
mulx r14, r12, rcx
test al, al
adox r10, [ rsp + 0x40 ]
adox r15, [ rsp + 0x18 ]
adcx r10, [ rsp + 0x10 ]
adcx r15, [ rsp + 0x8 ]
xor rdx, rdx
adox rbp, r12
adox r14, r11
mov r11, 0x1 
shlx r12, [ rsi + 0x10 ], r11
adcx r8, [ rsp + 0x0 ]
adcx rdi, [ rsp - 0x18 ]
mov rdx, r8
shrd rdx, rdi, 58
shr rdi, 58
mov r11, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xd8 ], rbx
mov [ rsp + 0xe0 ], r14
mulx r14, rbx, [ rsp + 0x98 ]
add r10, rbx
adcx r14, r15
test al, al
adox r10, r11
adox rdi, r14
mov rdx, [ rsi + 0x30 ]
mulx r11, r15, r9
mov rdx, 0x3ffffffffffffff 
and r8, rdx
adox r15, [ rsp - 0x8 ]
adox r11, [ rsp - 0x10 ]
mov rdx, [ rsi + 0x8 ]
mulx r14, rbx, r12
adcx r15, [ rsp - 0x20 ]
adcx r11, [ rsp - 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xe8 ], r8
mov [ rsp + 0xf0 ], rbp
mulx rbp, r8, rcx
xor rdx, rdx
adox r15, rbx
adox r14, r11
mov rbx, 0x3ffffffffffffff 
mov r11, r10
and r11, rbx
adox r15, r8
adox rbp, r14
mov rdx, [ rsi + 0x8 ]
mulx r14, r8, rdx
mov rdx, r12
mulx rbx, r12, [ rsi + 0x0 ]
mov rdx, [ rsp + 0x90 ]
adcx rdx, [ rsp - 0x30 ]
mov [ rsp + 0xf8 ], r11
mov r11, [ rsp + 0x88 ]
adcx r11, [ rsp - 0x38 ]
mov [ rsp + 0x100 ], r11
mov r11, [ rsp + 0xc8 ]
test al, al
adox r11, [ rsp - 0x40 ]
mov [ rsp + 0x108 ], rdx
mov rdx, [ rsp + 0xc0 ]
adox rdx, [ rsp - 0x48 ]
adcx r11, r8
adcx r14, rdx
xor r8, r8
adox r11, r12
adox rbx, r14
shrd r10, rdi, 58
shr rdi, 58
xor r12, r12
adox r11, r10
adox rdi, rbx
mov r8, [ rsi + 0x20 ]
lea rdx, [r8 + r8]
mulx r14, r8, [ rsi + 0x0 ]
mov rbx, r11
shrd rbx, rdi, 58
shr rdi, 58
mov r10, 0x3a 
bzhi r12, r11, r10
adox r15, rbx
adox rdi, rbp
mov rbp, r15
shrd rbp, rdi, 58
shr rdi, 58
bzhi r11, r15, r10
mov rbx, rdx
mov rdx, [ rsi + 0x10 ]
mulx r10, r15, rdx
mov rdx, r15
adox rdx, [ rsp + 0x108 ]
adox r10, [ rsp + 0x100 ]
mov r15, rdx
mov rdx, [ rsp + 0x48 ]
mov [ rsp + 0x110 ], r12
mov [ rsp + 0x118 ], r11
mulx r11, r12, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x120 ], r11
mov [ rsp + 0x128 ], r12
mulx r12, r11, rbx
mov rdx, r11
mov [ rsp + 0x130 ], rdi
xor rdi, rdi
adox rdx, [ rsp + 0x70 ]
adox r12, [ rsp + 0x68 ]
mov r11, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x138 ], r12
mulx r12, rdi, rcx
adcx r15, rdi
adcx r12, r10
mov rdx, r13
mulx rcx, r13, [ rsi + 0x8 ]
xor r10, r10
adox r15, r8
adox r14, r12
adcx r15, rbp
adcx r14, [ rsp + 0x130 ]
mov r8, r15
shrd r8, r14, 58
shr r14, 58
mov rbp, rdx
mov rdx, [ rsi + 0x8 ]
mulx r12, rdi, rax
mov rdx, rbx
mulx r10, rbx, [ rsi + 0x8 ]
mov [ rsp + 0x140 ], r12
mov r12, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x148 ], rdi
mov [ rsp + 0x150 ], r14
mulx r14, rdi, rdx
mov rdx, rbx
mov [ rsp + 0x158 ], r14
xor r14, r14
adox rdx, [ rsp + 0xf0 ]
adox r10, [ rsp + 0xe0 ]
adcx r11, r13
adcx rcx, [ rsp + 0x138 ]
xor r13, r13
adox r11, [ rsp + 0x60 ]
adox rcx, [ rsp + 0x58 ]
adcx rdx, [ rsp + 0x38 ]
adcx r10, [ rsp + 0x30 ]
xor r14, r14
adox rdx, r8
adox r10, [ rsp + 0x150 ]
mov r13, rdx
shrd r13, r10, 58
shr r10, 58
add r11, r13
adcx r10, rcx
mov r8, 0x3a 
bzhi rbx, r11, r8
bzhi rcx, rdx, r8
shrd r11, r10, 58
shr r10, 58
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x28 ], rcx
test al, al
adox rdi, [ rsp + 0x28 ]
mov r13, [ rsp + 0x20 ]
adox r13, [ rsp + 0x158 ]
xchg rdx, rbp
mulx r14, rcx, [ rsi + 0x10 ]
mov [ rbp + 0x30 ], rbx
mov rdx, [ rsi + 0x18 ]
mulx r8, rbx, r12
adcx rdi, [ rsp + 0x80 ]
adcx r13, [ rsp + 0x78 ]
mov rdx, [ rsi + 0x0 ]
mulx rbp, r12, rax
mov rdx, r9
mulx rax, r9, [ rsi + 0x8 ]
add rdi, [ rsp + 0x148 ]
adcx r13, [ rsp + 0x140 ]
mov rdx, rbx
add rdx, [ rsp + 0xd8 ]
adcx r8, [ rsp + 0xd0 ]
xor rbx, rbx
adox rdx, rcx
adox r14, r8
adcx rdx, r9
adcx rax, r14
test al, al
adox rdi, [ rsp + 0x128 ]
adox r13, [ rsp + 0x120 ]
adcx rdx, r12
adcx rbp, rax
test al, al
adox rdx, r11
adox r10, rbp
mov r11, rdx
shrd r11, r10, 58
shr r10, 58
add rdi, r11
adcx r10, r13
mov rcx, 0x3a 
bzhi r12, rdx, rcx
mov r9, rdi
shrd r9, r10, 57
shr r10, 57
add r9, [ rsp + 0xe8 ]
adc r10, 0x0
mov r8, [ rsp + 0x118 ]
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x18 ], r8
bzhi r8, r9, rcx
shrd r9, r10, 58
add r9, [ rsp + 0xf8 ]
mov rax, r9
shr rax, 58
bzhi r13, r15, rcx
add rax, [ rsp + 0x110 ]
mov [ r14 + 0x20 ], r13
bzhi r15, r9, rcx
mov [ r14 + 0x8 ], r15
mov rbp, 0x1ffffffffffffff 
and rdi, rbp
mov [ r14 + 0x40 ], rdi
mov [ r14 + 0x0 ], r8
mov [ r14 + 0x10 ], rax
mov [ r14 + 0x38 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 480
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.5575
; seed 0351661431439591 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3148321 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=87, initial num_batches=31): 97872 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.03108704607948173
; number reverted permutation / tried permutation: 63209 / 89698 =70.469%
; number reverted decision / tried decision: 58248 / 90301 =64.504%
; validated in 2.356s
