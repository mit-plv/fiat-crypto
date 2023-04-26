SECTION .text
	GLOBAL fiat_p521_carry_square
fiat_p521_carry_square:
sub rsp, 360
mov rax, [ rsi + 0x28 ]
lea r10, [rax + rax]
mov rax, 0x2 
shlx r11, [ rsi + 0x40 ], rax
imul rdx, [ rsi + 0x10 ], 0x2
imul rcx, [ rsi + 0x30 ], 0x4
mov r8, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rcx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rcx
mov rdx, [ rsi + 0x40 ]
mov [ rsp - 0x58 ], r15
lea r15, [rdx + rdx]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, rax, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x48 ], r15
mov [ rsp - 0x40 ], rbx
mulx rbx, r15, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], r9
lea r9, [rdx + rdx]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x30 ], rdi
mov [ rsp - 0x28 ], rax
mulx rax, rdi, r10
mov rdx, 0x1 
mov [ rsp - 0x20 ], rax
shlx rax, [ rsi + 0x38 ], rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x18 ], rdi
mov [ rsp - 0x10 ], rax
mulx rax, rdi, r9
imul rdx, [ rsi + 0x30 ], 0x2
mov [ rsp - 0x8 ], rax
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x0 ], rdi
mov [ rsp + 0x8 ], r8
mulx r8, rdi, r9
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x10 ], r8
lea r8, [ 4 * rdx]
mov rdx, r8
mov [ rsp + 0x18 ], rdi
mulx rdi, r8, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x20 ], rax
mov [ rsp + 0x28 ], r14
mulx r14, rax, r9
imul rdx, [ rsi + 0x38 ], 0x4
mov [ rsp + 0x30 ], r14
mulx r14, r9, [ rsi + 0x10 ]
xchg rdx, r11
mov [ rsp + 0x38 ], rax
mov [ rsp + 0x40 ], r13
mulx r13, rax, [ rsi + 0x18 ]
mov [ rsp + 0x48 ], r13
mov [ rsp + 0x50 ], rax
mulx rax, r13, [ rsi + 0x28 ]
mov [ rsp + 0x58 ], rax
mov [ rsp + 0x60 ], r13
mulx r13, rax, [ rsi + 0x20 ]
xchg rdx, r10
mov [ rsp + 0x68 ], r13
mov [ rsp + 0x70 ], rax
mulx rax, r13, [ rsi + 0x18 ]
test al, al
adox r15, r13
adox rax, rbx
mov rbx, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x78 ], rax
mulx rax, r13, r11
mov rdx, r10
mov [ rsp + 0x80 ], r15
mulx r15, r10, [ rsi + 0x8 ]
adcx r8, rbp
adcx r12, rdi
xchg rdx, rcx
mulx rdi, rbp, [ rsi + 0x20 ]
xor rdx, rdx
adox r8, r9
adox r14, r12
adcx r8, r10
adcx r15, r14
mov rdx, [ rsi + 0x28 ]
mulx r10, r9, rbx
mov rdx, r11
mulx r12, r11, [ rsi + 0x18 ]
xor r14, r14
adox r9, rbp
adox rdi, r10
adcx r9, r11
adcx r12, rdi
mov rbp, rdx
mov rdx, [ rsi + 0x10 ]
mulx r11, r10, rcx
mov rdx, [ rsi + 0x20 ]
mulx r14, rdi, rbp
add r9, r10
adcx r11, r12
mov rdx, rdi
xor r12, r12
adox rdx, [ rsp + 0x40 ]
adox r14, [ rsp + 0x28 ]
imul r10, [ rsi + 0x8 ], 0x2
add rdx, [ rsp + 0x50 ]
adcx r14, [ rsp + 0x48 ]
mov rdi, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x88 ], rax
mulx rax, r12, r10
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x90 ], r13
mulx r13, r10, rdx
test al, al
adox r8, r10
adox r13, r15
mov rdx, rbp
mulx r15, rbp, [ rsi + 0x30 ]
adcx r9, r12
adcx rax, r11
mov rdx, r8
shrd rdx, r13, 58
shr r13, 58
xor r11, r11
adox r9, rdx
adox r13, rax
adcx rbp, [ rsp + 0x60 ]
adcx r15, [ rsp + 0x58 ]
mov rdx, [ rsp + 0x8 ]
mulx r10, r12, [ rsi + 0x8 ]
mov rax, 0x3a 
bzhi r11, r8, rax
mulx rax, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x98 ], r11
mov [ rsp + 0xa0 ], r10
mulx r10, r11, rdx
adox rdi, r11
adox r10, r14
imul rdx, [ rsi + 0x20 ], 0x2
mulx r11, r14, [ rsi + 0x0 ]
mov [ rsp + 0xa8 ], r12
mov r12, r9
shrd r12, r13, 58
shr r13, 58
mov [ rsp + 0xb0 ], r11
xor r11, r11
adox rdi, r8
adox rax, r10
adcx rdi, r12
adcx r13, rax
mulx r10, r8, [ rsi + 0x10 ]
mov r12, rdi
shrd r12, r13, 58
shr r13, 58
add rbp, [ rsp - 0x28 ]
adcx r15, [ rsp - 0x30 ]
xor rax, rax
adox rbp, [ rsp + 0x0 ]
adox r15, [ rsp - 0x8 ]
mov r11, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xb8 ], r10
mulx r10, rax, [ rsp + 0x20 ]
adcx rax, [ rsp + 0x90 ]
adcx r10, [ rsp + 0x88 ]
add rax, [ rsp + 0x70 ]
adcx r10, [ rsp + 0x68 ]
mov rdx, rcx
mov [ rsp + 0xc0 ], r8
mulx r8, rcx, [ rsi + 0x38 ]
add rbp, r14
adcx r15, [ rsp + 0xb0 ]
xor r14, r14
adox rax, [ rsp + 0xa8 ]
adox r10, [ rsp + 0xa0 ]
adcx rax, [ rsp + 0x18 ]
adcx r10, [ rsp + 0x10 ]
add rax, r12
adcx r13, r10
mov r12, rax
shrd r12, r13, 58
shr r13, 58
mov r10, 0x3a 
bzhi r14, rax, r10
bzhi rax, rdi, r10
adox rbp, r12
adox r13, r15
xor rdi, rdi
adox rcx, [ rsp - 0x38 ]
adox r8, [ rsp - 0x40 ]
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x18 ], r14
mov r12, rdx
mov rdx, [ rsp - 0x10 ]
mulx rdi, r14, [ rsi + 0x38 ]
mov r10, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xc8 ], rax
mulx rax, r15, r12
adcx r14, r15
adcx rax, rdi
mov rdx, [ rsi + 0x8 ]
mulx rdi, r12, rbx
xor rdx, rdx
adox r14, [ rsp + 0x38 ]
adox rax, [ rsp + 0x30 ]
mov rdx, r11
mulx r15, r11, [ rsi + 0x8 ]
adcx r14, r11
adcx r15, rax
xor rax, rax
adox rcx, [ rsp + 0xc0 ]
adox r8, [ rsp + 0xb8 ]
adcx rcx, r12
adcx rdi, r8
xor r12, r12
adox r14, [ rsp - 0x18 ]
adox r15, [ rsp - 0x20 ]
mov rax, rbp
shrd rax, r13, 58
shr r13, 58
add r14, rax
adcx r13, r15
mov r11, r14
shrd r11, r13, 58
shr r13, 58
mov r8, rdx
mov rdx, [ rsi + 0x10 ]
mulx rax, r15, rbx
mov rdx, [ rsi + 0x18 ]
mulx r12, rbx, r8
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0xd0 ], r13
mulx r13, r8, [ rsp - 0x48 ]
xor rdx, rdx
adox r8, rbx
adox r12, r13
mov rdx, [ rsp + 0x20 ]
mulx r13, rbx, [ rsi + 0x0 ]
adcx r8, r15
adcx rax, r12
mulx r12, r15, [ rsi + 0x10 ]
mov [ rsp + 0xd8 ], r11
mov r11, r15
mov [ rsp + 0xe0 ], rdi
xor rdi, rdi
adox r11, [ rsp + 0x80 ]
adox r12, [ rsp + 0x78 ]
mulx rdi, r15, [ rsi + 0x8 ]
adcx r8, r15
adcx rdi, rax
add rcx, rbx
adcx r13, [ rsp + 0xe0 ]
add rcx, [ rsp + 0xd8 ]
adcx r13, [ rsp + 0xd0 ]
mov rdx, 0x3ffffffffffffff 
and r14, rdx
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x28 ], r14
mov rax, rcx
and rax, rdx
shrd rcx, r13, 58
shr r13, 58
mov rdx, r10
mulx r15, r10, [ rsi + 0x0 ]
test al, al
adox r8, r10
adox r15, rdi
adcx r8, rcx
adcx r13, r15
mov rdi, r8
shrd rdi, r13, 58
shr r13, 58
mulx rcx, r14, [ rsi + 0x8 ]
add r11, r14
adcx rcx, r12
mov rdx, [ rsp - 0x48 ]
mulx r10, r12, [ rsi + 0x0 ]
mov rdx, 0x3ffffffffffffff 
and r9, rdx
adox r11, r12
adox r10, rcx
adcx r11, rdi
adcx r13, r10
mov r15, r11
shrd r15, r13, 57
shr r13, 57
test al, al
adox r15, [ rsp + 0x98 ]
mov rdi, 0x0 
adox r13, rdi
mov r14, r15
shrd r14, r13, 58
and r15, rdx
and r8, rdx
lea r14, [ r14 + r9 ]
mov [ rbx + 0x38 ], r8
mov rcx, 0x39 
bzhi r12, r11, rcx
mov r9, r14
shr r9, 58
and rbp, rdx
add r9, [ rsp + 0xc8 ]
mov [ rbx + 0x10 ], r9
mov [ rbx + 0x20 ], rbp
mov [ rbx + 0x30 ], rax
mov [ rbx + 0x0 ], r15
and r14, rdx
mov [ rbx + 0x8 ], r14
mov [ rbx + 0x40 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 360
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.4312
; seed 4289756610930396 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4759501 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=74, initial num_batches=31): 160367 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.03369407843385262
; number reverted permutation / tried permutation: 65592 / 90001 =72.879%
; number reverted decision / tried decision: 60483 / 89998 =67.205%
; validated in 2.131s
