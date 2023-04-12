SECTION .text
	GLOBAL fiat_p521_carry_square
fiat_p521_carry_square:
sub rsp, 304
mov rax, [ rsi + 0x30 ]
lea r10, [ 4 * rax]
mov rax, 0x1 
shlx r11, [ rsi + 0x38 ], rax
mov rdx, 0x2 
shlx rcx, [ rsi + 0x40 ], rdx
shlx r8, [ rsi + 0x28 ], rax
imul r9, [ rsi + 0x40 ], 0x2
imul rax, [ rsi + 0x30 ], 0x2
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, r10
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rax
mov rdx, r8
mov [ rsp - 0x60 ], r14
mulx r14, r8, [ rsi + 0x28 ]
mov [ rsp - 0x58 ], r15
mov r15, [ rsi + 0x38 ]
mov [ rsp - 0x50 ], rdi
mov rdi, r15
shl rdi, 0x2
mov r15, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], r9
mov [ rsp - 0x40 ], r11
mulx r11, r9, rdi
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x38 ], rbp
mov [ rsp - 0x30 ], rbx
mulx rbx, rbp, rdi
mov rdx, 0x2 
mov [ rsp - 0x28 ], r13
shlx r13, [ rsi + 0x28 ], rdx
mov rdx, rcx
mov [ rsp - 0x20 ], r12
mulx r12, rcx, [ rsi + 0x8 ]
mov [ rsp - 0x18 ], r12
mov [ rsp - 0x10 ], rcx
mulx rcx, r12, [ rsi + 0x10 ]
mov [ rsp - 0x8 ], rcx
mov rcx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x0 ], r12
mov [ rsp + 0x8 ], rbx
mulx rbx, r12, r13
mov rdx, r10
mulx r13, r10, [ rsi + 0x18 ]
mov [ rsp + 0x10 ], rbp
xor rbp, rbp
adox r12, r10
adox r13, rbx
adcx r12, r9
adcx r11, r13
mulx rbx, r9, [ rsi + 0x20 ]
xor rdx, rdx
adox r8, r9
adox rbx, r14
mov rbp, [ rsp + 0x10 ]
mov r14, rbp
adcx r14, [ rsp - 0x20 ]
mov r10, [ rsp + 0x8 ]
adcx r10, [ rsp - 0x28 ]
mov rdx, [ rsi + 0x20 ]
mulx r13, rbp, rdx
imul rdx, [ rsi + 0x8 ], 0x2
mov [ rsp + 0x18 ], r13
mulx r13, r9, [ rsi + 0x0 ]
add r12, [ rsp - 0x10 ]
adcx r11, [ rsp - 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x20 ], rbp
mov [ rsp + 0x28 ], r10
mulx r10, rbp, rdx
xor rdx, rdx
adox r12, rbp
adox r10, r11
mov r11, r12
shrd r11, r10, 58
shr r10, 58
mov rdx, rdi
mulx rbp, rdi, [ rsi + 0x18 ]
mov [ rsp + 0x30 ], r14
mov [ rsp + 0x38 ], r10
mulx r10, r14, [ rsi + 0x20 ]
add r8, rdi
adcx rbp, rbx
test al, al
adox r8, [ rsp + 0x0 ]
adox rbp, [ rsp - 0x8 ]
mov rbx, r14
adcx rbx, [ rsp - 0x30 ]
adcx r10, [ rsp - 0x38 ]
xor rdi, rdi
adox r8, r9
adox r13, rbp
adcx r8, r11
adcx r13, [ rsp + 0x38 ]
mov r9, [ rsi + 0x10 ]
lea r11, [r9 + r9]
mov r9, rdx
mov rdx, [ rsi + 0x8 ]
mulx rbp, r14, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x40 ], r13
mulx r13, rdi, rcx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x48 ], r8
lea r8, [rdx + rdx]
mov rdx, rcx
mov [ rsp + 0x50 ], rax
mulx rax, rcx, [ rsi + 0x18 ]
mov [ rsp + 0x58 ], r8
mov r8, rdi
mov [ rsp + 0x60 ], rbp
xor rbp, rbp
adox r8, [ rsp + 0x30 ]
adox r13, [ rsp + 0x28 ]
mov rdi, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x68 ], r13
mulx r13, rbp, r11
adcx rbx, rcx
adcx rax, r10
mov rdx, [ rsi + 0x0 ]
mulx rcx, r10, r11
test al, al
adox rbx, r14
adox rax, [ rsp + 0x60 ]
adcx rbx, r10
adcx rcx, rax
mov rdx, [ rsp + 0x40 ]
mov r11, [ rsp + 0x48 ]
shrd r11, rdx, 58
shr rdx, 58
mov r14, 0x3ffffffffffffff 
mov r10, [ rsp + 0x48 ]
and r10, r14
mov rax, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x70 ], r10
mulx r10, r14, rdx
adox rbx, r11
adox rax, rcx
mov rdx, 0x3ffffffffffffff 
and r12, rdx
mov rcx, rbx
shrd rcx, rax, 58
shr rax, 58
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x78 ], r12
mulx r12, r11, r9
mov rdx, [ rsp - 0x40 ]
mov [ rsp + 0x80 ], rax
mulx rax, r9, [ rsi + 0x38 ]
mov [ rsp + 0x88 ], rcx
mov rcx, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x90 ], r15
mov [ rsp + 0x98 ], r8
mulx r8, r15, rdi
xor rdx, rdx
adox r11, r15
adox r8, r12
adcx r11, r14
adcx r10, r8
mov rdx, rdi
mulx r14, rdi, [ rsi + 0x30 ]
mov r12, [ rsi + 0x20 ]
lea r15, [r12 + r12]
mov r12, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xa0 ], r10
mulx r10, r8, [ rsp + 0x58 ]
xor rdx, rdx
adox r9, rdi
adox r14, rax
mov rdx, [ rsi + 0x8 ]
mulx rdi, rax, r15
adcx r9, r8
adcx r10, r14
mov rdx, [ rsp + 0x58 ]
mulx r14, r8, [ rsi + 0x8 ]
add r9, rax
adcx rdi, r10
mov rax, rbp
test al, al
adox rax, [ rsp + 0x98 ]
adox r13, [ rsp + 0x68 ]
adcx r11, r8
adcx r14, [ rsp + 0xa0 ]
mulx r10, rbp, [ rsi + 0x0 ]
test al, al
adox rax, rbp
adox r10, r13
mov rdx, [ rsi + 0x0 ]
mulx r13, r8, [ rsp + 0x90 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xa8 ], r14
mulx r14, rbp, r12
adcx rax, [ rsp + 0x88 ]
adcx r10, [ rsp + 0x80 ]
test al, al
adox r9, r8
adox r13, rdi
mov rdx, r15
mulx r12, r15, [ rsi + 0x0 ]
adcx r11, r15
adcx r12, [ rsp + 0xa8 ]
mov rdi, rax
shrd rdi, r10, 58
shr r10, 58
xor r8, r8
adox r11, rdi
adox r10, r12
mulx r12, r15, [ rsi + 0x10 ]
mov rdi, 0x3ffffffffffffff 
mov r8, r11
and r8, rdi
shrd r11, r10, 58
shr r10, 58
test al, al
adox r9, r11
adox r10, r13
mov r13, rdx
mov rdx, [ rsi + 0x18 ]
mulx rdi, r11, rdx
adcx rbp, r11
adcx rdi, r14
mov rdx, 0x3a 
bzhi r14, r9, rdx
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x28 ], r14
mov [ r11 + 0x20 ], r8
mov rdx, [ rsi + 0x0 ]
mulx r14, r8, [ rsp + 0x50 ]
shrd r9, r10, 58
shr r10, 58
test al, al
adox rbp, r15
adox r12, rdi
mov rdx, [ rsi + 0x8 ]
mulx rdi, r15, [ rsp + 0x90 ]
adcx rbp, r15
adcx rdi, r12
mov rdx, [ rsi + 0x10 ]
mulx r15, r12, [ rsp + 0x90 ]
test al, al
adox rbp, r8
adox r14, rdi
mov rdx, r13
mulx r8, r13, [ rsi + 0x18 ]
adcx rbp, r9
adcx r10, r14
mov rdx, [ rsi + 0x40 ]
mulx rdi, r9, [ rsp - 0x48 ]
add r9, r13
adcx r8, rdi
mov rdx, [ rsp + 0x50 ]
mulx r13, r14, [ rsi + 0x8 ]
test al, al
adox r9, r12
adox r15, r8
adcx r9, r14
adcx r13, r15
mov r12, rdx
mov rdx, [ rsi + 0x18 ]
mulx r8, rdi, [ rsp + 0x90 ]
mov rdx, rdi
xor r14, r14
adox rdx, [ rsp + 0x20 ]
adox r8, [ rsp + 0x18 ]
mov r15, rdx
mov rdx, [ rsi + 0x0 ]
mulx r14, rdi, rcx
adcx r9, rdi
adcx r14, r13
mov rdx, 0x3a 
bzhi r13, rbp, rdx
mov [ r11 + 0x30 ], r13
mov rdx, r12
mulx rdi, r12, [ rsi + 0x10 ]
shrd rbp, r10, 58
shr r10, 58
mov rdx, rcx
mulx r13, rcx, [ rsi + 0x8 ]
add r9, rbp
adcx r10, r14
xor rdx, rdx
adox r15, r12
adox rdi, r8
mov rdx, [ rsp - 0x48 ]
mulx r14, r8, [ rsi + 0x0 ]
adcx r15, rcx
adcx r13, rdi
mov rdx, r9
shrd rdx, r10, 58
shr r10, 58
xor r12, r12
adox r15, r8
adox r14, r13
adcx r15, rdx
adcx r10, r14
mov rbp, r15
shrd rbp, r10, 57
shr r10, 57
mov rcx, 0x1ffffffffffffff 
and r15, rcx
adox rbp, [ rsp + 0x78 ]
adox r10, r12
mov rdi, rbp
shrd rdi, r10, 58
add rdi, [ rsp + 0x70 ]
mov r8, 0x3ffffffffffffff 
and rbx, r8
and rbp, r8
mov r13, rdi
and r13, r8
shr rdi, 58
lea rdi, [ rdi + rbx ]
mov [ r11 + 0x10 ], rdi
mov [ r11 + 0x0 ], rbp
and rax, r8
mov [ r11 + 0x18 ], rax
and r9, r8
mov [ r11 + 0x38 ], r9
mov [ r11 + 0x8 ], r13
mov [ r11 + 0x40 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 304
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.4200
; seed 2481746652189929 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2399337 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=150, initial num_batches=31): 98803 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.04117929244620493
; number reverted permutation / tried permutation: 73796 / 89918 =82.070%
; number reverted decision / tried decision: 67199 / 90081 =74.598%
; validated in 1.255s
