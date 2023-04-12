SECTION .text
	GLOBAL fiat_p521_carry_square
fiat_p521_carry_square:
sub rsp, 336
mov rax, [ rsi + 0x38 ]
lea r10, [ 4 * rax]
imul rax, [ rsi + 0x30 ], 0x2
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, r10
imul rdx, [ rsi + 0x28 ], 0x2
mov r8, [ rsi + 0x40 ]
lea r9, [r8 + r8]
mov [ rsp - 0x80 ], rbx
mulx rbx, r8, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rdx
mov rdx, 0x1 
mov [ rsp - 0x50 ], rdi
shlx rdi, [ rsi + 0x20 ], rdx
mov [ rsp - 0x48 ], r15
shlx r15, [ rsi + 0x38 ], rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x40 ], r14
mov [ rsp - 0x38 ], rbx
mulx rbx, r14, r10
mov rdx, r15
mov [ rsp - 0x30 ], r8
mulx r8, r15, [ rsi + 0x38 ]
mov [ rsp - 0x28 ], r9
mov r9, [ rsi + 0x10 ]
mov [ rsp - 0x20 ], rbx
lea rbx, [r9 + r9]
imul r9, [ rsi + 0x40 ], 0x4
mov [ rsp - 0x18 ], r14
mov r14, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], rdi
mov [ rsp - 0x8 ], rbx
mulx rbx, rdi, r9
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x0 ], rax
lea rax, [rdx + rdx]
mov rdx, rax
mov [ rsp + 0x8 ], r13
mulx r13, rax, [ rsi + 0x0 ]
mov rdx, r14
mov [ rsp + 0x10 ], r13
mulx r13, r14, [ rsi + 0x8 ]
mov [ rsp + 0x18 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x20 ], r14
mov [ rsp + 0x28 ], rax
mulx rax, r14, r9
imul rdx, [ rsi + 0x18 ], 0x2
mov [ rsp + 0x30 ], rax
mov rax, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x38 ], r14
mov [ rsp + 0x40 ], r12
mulx r12, r14, rbp
imul rdx, [ rsi + 0x30 ], 0x4
mov [ rsp + 0x48 ], r12
mov [ rsp + 0x50 ], r14
mulx r14, r12, [ rsi + 0x18 ]
mov [ rsp + 0x58 ], rax
imul rax, [ rsi + 0x28 ], 0x4
mov [ rsp + 0x60 ], rbx
mov rbx, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x68 ], rdi
mov [ rsp + 0x70 ], rcx
mulx rcx, rdi, r9
test al, al
adox r15, rdi
adox rcx, r8
mov rdx, rbx
mulx r8, rbx, [ rsi + 0x20 ]
mov [ rsp + 0x78 ], rcx
mulx rcx, rdi, [ rsi + 0x28 ]
mov rdx, rax
mov [ rsp + 0x80 ], r15
mulx r15, rax, [ rsi + 0x20 ]
adcx rax, r12
adcx r14, r15
test al, al
adox rax, r11
adox r14, [ rsp + 0x70 ]
mov rdx, r10
mulx r11, r10, [ rsi + 0x20 ]
mov r12, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x88 ], r8
mulx r8, r15, r9
adcx rax, r15
adcx r8, r14
xor rdx, rdx
adox rdi, r10
adox r11, rcx
adcx rdi, [ rsp + 0x68 ]
adcx r11, [ rsp + 0x60 ]
add rax, [ rsp + 0x40 ]
adcx r8, [ rsp + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx r14, rcx, rdx
test al, al
adox rdi, rcx
adox r14, r11
mov rdx, 0x3a 
bzhi r10, rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx r11, r15, r9
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x90 ], r10
mulx r10, rcx, rbp
mov rdx, r12
mov [ rsp + 0x98 ], r14
mulx r14, r12, [ rsi + 0x18 ]
adox rcx, rbx
adox r10, [ rsp + 0x88 ]
xor rbx, rbx
adox rcx, r12
adox r14, r10
adcx rcx, r15
adcx r11, r14
add rcx, [ rsp + 0x28 ]
adcx r11, [ rsp + 0x10 ]
shrd rax, r8, 58
shr r8, 58
mulx r12, r15, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x30 ]
mulx r14, r10, [ rsp + 0x0 ]
add r10, r15
adcx r12, r14
test al, al
adox rcx, rax
adox r8, r11
adcx r10, [ rsp + 0x38 ]
adcx r12, [ rsp + 0x30 ]
mov rdx, 0x3a 
bzhi r11, rcx, rdx
mov rdx, [ rsi + 0x18 ]
mulx r15, rax, rdx
mov rdx, [ rsi + 0x38 ]
mulx rbx, r14, r9
adox r14, rax
adox r15, rbx
mov rdx, [ rsp - 0x8 ]
mulx rbx, rax, [ rsi + 0x8 ]
mov [ rsp + 0xa0 ], r11
mov [ rsp + 0xa8 ], r15
mulx r15, r11, [ rsi + 0x0 ]
xor rdx, rdx
adox rdi, r11
adox r15, [ rsp + 0x98 ]
adcx r10, rax
adcx rbx, r12
shrd rcx, r8, 58
shr r8, 58
test al, al
adox rdi, rcx
adox r8, r15
mov r12, rdi
shrd r12, r8, 58
shr r8, 58
mov rdx, [ rsi + 0x0 ]
mulx r11, rax, [ rsp + 0x58 ]
test al, al
adox r10, rax
adox r11, rbx
adcx r10, r12
adcx r8, r11
mov rdx, [ rsi + 0x10 ]
mulx rbx, r15, [ rsp - 0x10 ]
mov rdx, [ rsi + 0x0 ]
mulx r12, rcx, [ rsp - 0x10 ]
mov rdx, [ rsi + 0x10 ]
mulx r11, rax, rdx
mov rdx, 0x3a 
mov [ rsp + 0xb0 ], r12
bzhi r12, r10, rdx
adox r14, r15
adox rbx, [ rsp + 0xa8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xb8 ], rbx
mulx rbx, r15, r9
mov rdx, r15
add rdx, [ rsp - 0x18 ]
adcx rbx, [ rsp - 0x20 ]
mov r9, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xc0 ], r14
mulx r14, r15, [ rsp + 0x58 ]
xor rdx, rdx
adox r9, rax
adox r11, rbx
adcx r9, r15
adcx r14, r11
mov rdx, [ rsi + 0x10 ]
mulx rbx, rax, [ rsp + 0x58 ]
shrd r10, r8, 58
shr r8, 58
mov rdx, [ rsi + 0x0 ]
mulx r11, r15, rbp
xor rdx, rdx
adox r9, rcx
adox r14, [ rsp + 0xb0 ]
adcx r9, r10
adcx r8, r14
mov rdx, [ rsp - 0x10 ]
mulx r10, rcx, [ rsi + 0x8 ]
mov r14, rax
add r14, [ rsp + 0x80 ]
adcx rbx, [ rsp + 0x78 ]
mov rax, [ rsp - 0x50 ]
mov [ rax + 0x18 ], r12
mov r12, 0x3a 
bzhi rax, r9, r12
adox r14, rcx
adox r10, rbx
shrd r9, r8, 58
shr r8, 58
xor rcx, rcx
adox r14, r15
adox r11, r10
adcx r14, r9
adcx r8, r11
mulx rbx, r15, [ rsi + 0x18 ]
mov rdx, [ rsp + 0xc0 ]
xor r10, r10
adox rdx, [ rsp + 0x50 ]
mov rcx, [ rsp + 0xb8 ]
adox rcx, [ rsp + 0x48 ]
mov r9, r14
shrd r9, r8, 58
shr r8, 58
bzhi r11, r14, r12
mov r14, rdx
mov rdx, [ rsi + 0x40 ]
mulx r12, r10, [ rsp - 0x28 ]
adox r10, r15
adox rbx, r12
add r10, [ rsp - 0x30 ]
adcx rbx, [ rsp - 0x38 ]
mov rdx, [ rsi + 0x0 ]
mulx r12, r15, [ rsp + 0x0 ]
xor rdx, rdx
adox r14, r15
adox r12, rcx
adcx r14, r9
adcx r8, r12
mov rdx, r13
mulx rcx, r13, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx r15, r9, [ rsp + 0x0 ]
mov rdx, r14
shrd rdx, r8, 58
shr r8, 58
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x28 ], r11
mov r11, rdx
mov rdx, [ rsp - 0x28 ]
mov [ rsp + 0xc8 ], rax
mulx rax, r12, [ rsi + 0x0 ]
mov rdx, 0x3ffffffffffffff 
and r14, rdx
adox r10, r9
adox r15, rbx
adcx r10, r13
adcx rcx, r15
mov rdx, [ rsi + 0x18 ]
mulx r13, rbx, rbp
mov rdx, rbx
xor rbp, rbp
adox rdx, [ rsp - 0x40 ]
adox r13, [ rsp - 0x48 ]
adcx r10, r11
adcx r8, rcx
mov r9, rdx
mov rdx, [ rsp + 0x0 ]
mulx r15, r11, [ rsi + 0x10 ]
add r9, r11
adcx r15, r13
xor rdx, rdx
adox r9, [ rsp + 0x20 ]
adox r15, [ rsp + 0x18 ]
adcx r9, r12
adcx rax, r15
mov rbp, r10
shrd rbp, r8, 58
shr r8, 58
xor r12, r12
adox r9, rbp
adox r8, rax
mov rdx, r9
shrd rdx, r8, 57
shr r8, 57
mov rcx, 0x39 
bzhi rbx, r9, rcx
adox rdx, [ rsp + 0x90 ]
adox r8, r12
mov r13, rdx
shrd r13, r8, 58
add r13, [ rsp + 0xa0 ]
mov r11, 0x3a 
bzhi r15, r13, r11
bzhi rax, rdx, r11
bzhi rbp, rdi, r11
shr r13, 58
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x8 ], r15
lea r13, [ r13 + rbp ]
mov [ rdi + 0x10 ], r13
mov r9, [ rsp + 0xc8 ]
mov [ rdi + 0x20 ], r9
bzhi r9, r10, r11
mov [ rdi + 0x38 ], r9
mov [ rdi + 0x40 ], rbx
mov [ rdi + 0x0 ], rax
mov [ rdi + 0x30 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 336
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.4259
; seed 0656211593196418 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4750372 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=69, initial num_batches=31): 160904 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.0338718736132665
; number reverted permutation / tried permutation: 65630 / 90075 =72.862%
; number reverted decision / tried decision: 60469 / 89924 =67.245%
; validated in 2.188s
