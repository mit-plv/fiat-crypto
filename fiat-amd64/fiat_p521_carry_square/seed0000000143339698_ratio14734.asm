SECTION .text
	GLOBAL fiat_p521_carry_square
fiat_p521_carry_square:
sub rsp, 280
imul rax, [ rsi + 0x38 ], 0x2
mov r10, [ rsi + 0x38 ]
mov r11, r10
shl r11, 0x2
mov rdx, [ rsi + 0x38 ]
mulx rcx, r10, rax
imul rdx, [ rsi + 0x30 ], 0x4
mov r8, 0x1 
shlx r9, [ rsi + 0x18 ], r8
mov [ rsp - 0x80 ], rbx
mulx rbx, r8, [ rsi + 0x28 ]
mov [ rsp - 0x78 ], rbp
mov rbp, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
lea r12, [rbp + rbp]
mov [ rsp - 0x68 ], r13
mulx r13, rbp, [ rsi + 0x20 ]
xchg rdx, r12
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x0 ]
mov [ rsp - 0x50 ], rdi
imul rdi, [ rsi + 0x30 ], 0x2
mov [ rsp - 0x48 ], rcx
imul rcx, [ rsi + 0x40 ], 0x2
mov [ rsp - 0x40 ], r10
mov [ rsp - 0x38 ], r9
mulx r9, r10, [ rsi + 0x8 ]
mov rdx, rcx
mov [ rsp - 0x30 ], r9
mulx r9, rcx, [ rsi + 0x40 ]
xchg rdx, rax
mov [ rsp - 0x28 ], r9
mov [ rsp - 0x20 ], rcx
mulx rcx, r9, [ rsi + 0x0 ]
mov [ rsp - 0x18 ], rcx
mov rcx, [ rsi + 0x28 ]
mov [ rsp - 0x10 ], r9
lea r9, [rcx + rcx]
mov [ rsp - 0x8 ], r10
mulx r10, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x0 ], r10
mov [ rsp + 0x8 ], rcx
mulx rcx, r10, r11
mov rdx, r9
mov [ rsp + 0x10 ], rcx
mulx rcx, r9, [ rsi + 0x28 ]
mov [ rsp + 0x18 ], r10
xor r10, r10
adox r9, rbp
adox r13, rcx
mov rbp, rdx
mov rdx, [ rsi + 0x18 ]
mulx r10, rcx, r11
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x20 ], r15
lea r15, [ 4 * rdx]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x28 ], r14
mov [ rsp + 0x30 ], rdi
mulx rdi, r14, r11
adcx r9, rcx
adcx r10, r13
add r8, r14
adcx rdi, rbx
mov rdx, r12
mulx rbx, r12, [ rsi + 0x18 ]
mov rdx, r15
mulx r13, r15, [ rsi + 0x20 ]
xor rcx, rcx
adox r15, r12
adox rbx, r13
mov rdx, r11
mulx r14, r11, [ rsi + 0x10 ]
imul r12, [ rsi + 0x40 ], 0x4
test al, al
adox r15, r11
adox r14, rbx
mov r13, rdx
mov rdx, [ rsi + 0x10 ]
mulx r11, rbx, r12
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x38 ], rdi
mulx rdi, rcx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x40 ], r8
mov [ rsp + 0x48 ], r10
mulx r10, r8, r12
adcx r15, r8
adcx r10, r14
add r15, rcx
adcx rdi, r10
mov rdx, r15
shrd rdx, rdi, 58
shr rdi, 58
imul r14, [ rsi + 0x8 ], 0x2
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mulx r10, r8, r14
xor rdx, rdx
adox r9, rbx
adox r11, [ rsp + 0x48 ]
adcx r9, r8
adcx r10, r11
add r9, rcx
adcx rdi, r10
mov rdx, [ rsi + 0x18 ]
mulx rcx, rbx, r12
mov rdx, 0x3a 
bzhi r14, r9, rdx
shrd r9, rdi, 58
shr rdi, 58
mov rdx, [ rsi + 0x10 ]
mulx r11, r8, [ rsp + 0x30 ]
mov rdx, rbx
xor r10, r10
adox rdx, [ rsp + 0x40 ]
adox rcx, [ rsp + 0x38 ]
xchg rdx, r13
mulx r10, rbx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x50 ], r14
mov [ rsp + 0x58 ], r11
mulx r11, r14, rdx
adcx r13, r14
adcx r11, rcx
mov rdx, [ rsi + 0x30 ]
mulx r14, rcx, [ rsp + 0x30 ]
xor rdx, rdx
adox r13, [ rsp + 0x28 ]
adox r11, [ rsp + 0x20 ]
adcx r13, r9
adcx rdi, r11
xor r9, r9
adox rcx, rbx
adox r10, r14
mov rdx, [ rsp - 0x38 ]
mulx r14, rbx, [ rsi + 0x8 ]
imul r11, [ rsi + 0x20 ], 0x2
mov r9, 0x3a 
mov [ rsp + 0x60 ], r8
bzhi r8, r15, r9
mov r15, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x68 ], r8
mulx r8, r9, rdx
mov rdx, r12
mov [ rsp + 0x70 ], rdi
mulx rdi, r12, [ rsi + 0x28 ]
mov [ rsp + 0x78 ], r13
mov r13, r12
adox r13, [ rsp + 0x18 ]
adox rdi, [ rsp + 0x10 ]
xor r12, r12
adox r13, r9
adox r8, rdi
adcx r13, rbx
adcx r14, r8
mulx r9, rbx, [ rsi + 0x20 ]
add rcx, rbx
adcx r9, r10
mov r10, rdx
mov rdx, [ rsi + 0x0 ]
mulx r8, rdi, r11
xor rdx, rdx
adox rcx, [ rsp - 0x8 ]
adox r9, [ rsp - 0x30 ]
adcx r13, rdi
adcx r8, r14
mov rdx, r15
mulx r15, r12, [ rsi + 0x0 ]
mov r14, [ rsp + 0x70 ]
mov rbx, [ rsp + 0x78 ]
shrd rbx, r14, 58
shr r14, 58
add rcx, r12
adcx r15, r9
test al, al
adox rcx, rbx
adox r14, r15
mov rdi, 0x3a 
bzhi r9, rcx, rdi
mov r12, rdx
mov rdx, [ rsi + 0x30 ]
mulx r15, rbx, r10
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x18 ], r9
mov r9, rbx
adox r9, [ rsp - 0x40 ]
adox r15, [ rsp - 0x48 ]
shrd rcx, r14, 58
shr r14, 58
xchg rdx, r10
mulx rdi, rbx, [ rsi + 0x38 ]
add r13, rcx
adcx r14, r8
mov rdx, [ rsi + 0x10 ]
mulx rcx, r8, r12
mov rdx, [ rsi + 0x8 ]
mulx r10, r12, r11
add r9, r8
adcx rcx, r15
mov rdx, r11
mulx r15, r11, [ rsi + 0x10 ]
mov r8, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x80 ], rax
mov [ rsp + 0x88 ], r15
mulx r15, rax, rbp
test al, al
adox r9, r12
adox r10, rcx
mov rdx, [ rsi + 0x18 ]
mulx rcx, r12, rdx
adcx r9, rax
adcx r15, r10
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, rbp
mov rdx, r13
shrd rdx, r14, 58
shr r14, 58
mov [ rsp + 0x90 ], r10
xor r10, r10
adox r9, rdx
adox r14, r15
mov rdx, [ rsi + 0x10 ]
mulx r10, r15, rbp
adcx rbx, r12
adcx rcx, rdi
xor rdx, rdx
adox rbx, r11
adox rcx, [ rsp + 0x88 ]
adcx rbx, rax
adcx rcx, [ rsp + 0x90 ]
mov rdx, [ rsp + 0x30 ]
mulx r11, rdi, [ rsi + 0x0 ]
test al, al
adox rbx, rdi
adox r11, rcx
mov r12, r9
shrd r12, r14, 58
shr r14, 58
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx rdi, rcx, r8
add rbx, r12
adcx r14, r11
mov rdx, 0x3a 
bzhi r8, r9, rdx
mov r9, rcx
adox r9, [ rsp - 0x20 ]
adox rdi, [ rsp - 0x28 ]
mov rdx, [ rsi + 0x18 ]
mulx r12, r11, rbp
xor rdx, rdx
adox r9, r15
adox r10, rdi
mov rdx, [ rsi + 0x8 ]
mulx r15, rbp, rax
adcx r9, rbp
adcx r15, r10
xor rdx, rdx
adox r9, [ rsp - 0x10 ]
adox r15, [ rsp - 0x18 ]
mov rax, 0x3a 
bzhi rcx, rbx, rax
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x30 ], rcx
mov rdx, [ rsi + 0x20 ]
mulx rbp, r10, rdx
adox r10, r11
adox r12, rbp
shrd rbx, r14, 58
shr r14, 58
xor rdx, rdx
adox r9, rbx
adox r14, r15
bzhi r11, r9, rax
shrd r9, r14, 58
shr r14, 58
test al, al
adox r10, [ rsp + 0x60 ]
adox r12, [ rsp + 0x58 ]
adcx r10, [ rsp + 0x8 ]
adcx r12, [ rsp + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r15, [ rsp + 0x80 ]
xor rdx, rdx
adox r10, r15
adox rcx, r12
adcx r10, r9
adcx r14, rcx
mov rbp, r10
shrd rbp, r14, 57
shr r14, 57
xor rbx, rbx
adox rbp, [ rsp + 0x68 ]
adox r14, rbx
bzhi rdx, rbp, rax
shrd rbp, r14, 58
bzhi r9, [ rsp + 0x78 ], rax
bzhi r12, r13, rax
mov [ rdi + 0x0 ], rdx
add rbp, [ rsp + 0x50 ]
mov r13, rbp
shr r13, 58
lea r13, [ r13 + r9 ]
mov r15, 0x1ffffffffffffff 
and r10, r15
mov [ rdi + 0x40 ], r10
mov [ rdi + 0x20 ], r12
bzhi rcx, rbp, rax
mov [ rdi + 0x8 ], rcx
mov [ rdi + 0x38 ], r11
mov [ rdi + 0x28 ], r8
mov [ rdi + 0x10 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 280
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.4734
; seed 3643036718930907 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4455994 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=145, initial num_batches=31): 177639 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.039865179351677764
; number reverted permutation / tried permutation: 67166 / 90229 =74.439%
; number reverted decision / tried decision: 61046 / 89770 =68.003%
; validated in 2.816s
