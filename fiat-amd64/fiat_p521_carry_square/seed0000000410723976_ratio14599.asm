SECTION .text
	GLOBAL fiat_p521_carry_square
fiat_p521_carry_square:
sub rsp, 280
imul rax, [ rsi + 0x28 ], 0x2
mov r10, [ rsi + 0x38 ]
lea r11, [r10 + r10]
mov rdx, [ rsi + 0x10 ]
mulx rcx, r10, rdx
mov rdx, 0x2 
shlx r8, [ rsi + 0x38 ], rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, r11
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x78 ], rbp
lea rbp, [rdx + rdx]
imul rdx, [ rsi + 0x30 ], 0x2
mov [ rsp - 0x70 ], r12
mov r12, [ rsi + 0x28 ]
mov [ rsp - 0x68 ], r13
lea r13, [ 4 * r12]
mov r12, 0x2 
mov [ rsp - 0x60 ], r14
shlx r14, [ rsi + 0x40 ], r12
mov [ rsp - 0x58 ], r15
imul r15, [ rsi + 0x8 ], 0x2
mov r12, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rcx
mulx rcx, rdi, r14
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x40 ], r10
mov [ rsp - 0x38 ], rbp
mulx rbp, r10, r13
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], r15
mulx r15, r13, r14
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x28 ], r15
mov [ rsp - 0x20 ], r13
mulx r13, r15, r14
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x18 ], r13
mov [ rsp - 0x10 ], r15
mulx r15, r13, r11
imul rdx, [ rsi + 0x10 ], 0x2
mov [ rsp - 0x8 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x0 ], r13
mov [ rsp + 0x8 ], r12
mulx r12, r13, rdx
imul rdx, [ rsi + 0x30 ], 0x4
test al, al
adox r9, rdi
adox rcx, rbx
mov rbx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x10 ], rcx
mulx rcx, rdi, rax
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x18 ], r9
mov [ rsp + 0x20 ], r8
mulx r8, r9, rbx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x28 ], r8
mov [ rsp + 0x30 ], r9
mulx r9, r8, rbx
adcx r10, r8
adcx r9, rbp
xor rdx, rdx
adox r13, rdi
adox rcx, r12
mov rdx, [ rsi + 0x0 ]
mulx r12, rbp, r11
mov rdx, r15
mulx r11, r15, [ rsi + 0x8 ]
mov rdi, [ rsi + 0x40 ]
lea r8, [rdi + rdi]
mov rdi, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x38 ], r12
mov [ rsp + 0x40 ], rbp
mulx rbp, r12, r14
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x48 ], r8
mov [ rsp + 0x50 ], r11
mulx r11, r8, [ rsp + 0x20 ]
adcx r10, r8
adcx r11, r9
test al, al
adox r10, r12
adox rbp, r11
mov rdx, [ rsi + 0x28 ]
mulx r12, r9, rax
mov rdx, [ rsi + 0x10 ]
mulx r11, r8, [ rsp + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x58 ], r15
mov [ rsp + 0x60 ], rbp
mulx rbp, r15, rdx
adcx r13, r8
adcx r11, rcx
xor rdx, rdx
adox r9, [ rsp + 0x30 ]
adox r12, [ rsp + 0x28 ]
adcx r10, r15
adcx rbp, [ rsp + 0x60 ]
mov rcx, r10
shrd rcx, rbp, 58
shr rbp, 58
mov rdx, [ rsi + 0x18 ]
mulx r15, r8, [ rsp + 0x20 ]
test al, al
adox r9, r8
adox r15, r12
mov rdx, [ rsi + 0x0 ]
mulx r8, r12, [ rsp - 0x30 ]
mov rdx, r14
mov [ rsp + 0x68 ], r11
mulx r11, r14, [ rsi + 0x10 ]
mov [ rsp + 0x70 ], r13
mov r13, 0x3ffffffffffffff 
and r10, r13
adox r9, r14
adox r11, r15
adcx r9, r12
adcx r8, r11
xor r15, r15
adox r9, rcx
adox rbp, r8
mov rcx, rdx
mov rdx, [ rsp + 0x20 ]
mulx r14, r12, [ rsi + 0x20 ]
mov r11, rdx
mov rdx, [ rsi + 0x28 ]
mulx r15, r8, rbx
adcx r8, r12
adcx r14, r15
mov rdx, rdi
mulx rbx, rdi, [ rsi + 0x0 ]
mov rdx, r11
mulx r12, r11, [ rsi + 0x30 ]
xor r15, r15
adox r8, [ rsp - 0x20 ]
adox r14, [ rsp - 0x28 ]
mov r15, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x78 ], r10
mulx r10, r13, rdx
adcx r8, r13
adcx r10, r14
add r8, rdi
adcx rbx, r10
mov rdx, 0x3a 
bzhi rdi, r9, rdx
mov rdx, [ rsi + 0x28 ]
mulx r13, r14, rcx
adox r11, r14
adox r13, r12
mov rdx, [ rsi + 0x8 ]
mulx r10, r12, [ rsp - 0x38 ]
xor rdx, rdx
adox r11, [ rsp - 0x40 ]
adox r13, [ rsp - 0x48 ]
adcx r11, r12
adcx r10, r13
mov rdx, [ rsi + 0x28 ]
mulx r12, r14, r15
mov rdx, [ rsp + 0x8 ]
mulx r13, r15, [ rsi + 0x30 ]
shrd r9, rbp, 58
shr rbp, 58
add r15, r14
adcx r12, r13
xor r14, r14
adox r15, [ rsp - 0x10 ]
adox r12, [ rsp - 0x18 ]
adcx r15, [ rsp + 0x58 ]
adcx r12, [ rsp + 0x50 ]
test al, al
adox r8, r9
adox rbp, rbx
mov rbx, r8
shrd rbx, rbp, 58
shr rbp, 58
mov r13, rdx
mov rdx, [ rsi + 0x18 ]
mulx r14, r9, rdx
mov rdx, 0x3a 
mov [ rsp + 0x80 ], rdi
bzhi rdi, r8, rdx
mov rdx, rcx
mulx r8, rcx, [ rsi + 0x38 ]
adox rcx, r9
adox r14, r8
mov rdx, [ rsp - 0x38 ]
mulx r8, r9, [ rsi + 0x0 ]
add r15, r9
adcx r8, r12
imul r12, [ rsi + 0x20 ], 0x2
xor r9, r9
adox r15, rbx
adox rbp, r8
mov rbx, 0x3a 
bzhi r8, r15, rbx
shrd r15, rbp, 58
shr rbp, 58
mulx rbx, r9, [ rsi + 0x10 ]
mov rdx, r12
mov [ rsp + 0x88 ], rdi
mulx rdi, r12, [ rsi + 0x0 ]
mov [ rsp + 0x90 ], r14
mov r14, r9
test al, al
adox r14, [ rsp + 0x18 ]
adox rbx, [ rsp + 0x10 ]
adcx r11, r12
adcx rdi, r10
xor r10, r10
adox r11, r15
adox rbp, rdi
mov r15, rdx
mov rdx, [ rsi + 0x0 ]
mulx r12, r9, rax
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x18 ], r8
xchg rdx, r15
mulx rdi, r8, [ rsi + 0x8 ]
adcx r14, r8
adcx rdi, rbx
mov rbx, 0x3ffffffffffffff 
mov r8, r11
and r8, rbx
adox r14, r9
adox r12, rdi
mov [ r15 + 0x20 ], r8
mulx rdi, r9, [ rsi + 0x10 ]
adcx rcx, r9
adcx rdi, [ rsp + 0x90 ]
mov r8, rdx
mov rdx, [ rsi + 0x40 ]
mulx r10, r9, [ rsp + 0x48 ]
mov rdx, rax
mulx rbx, rax, [ rsi + 0x8 ]
shrd r11, rbp, 58
shr rbp, 58
xor r15, r15
adox r14, r11
adox rbp, r12
adcx rcx, rax
adcx rbx, rdi
mov r12, r14
shrd r12, rbp, 58
shr rbp, 58
mov rdi, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, rax, r13
xor rdx, rdx
adox rcx, rax
adox r11, rbx
mov rdx, rdi
mulx r15, rdi, [ rsi + 0x10 ]
mov rdx, r8
mulx rbx, r8, [ rsi + 0x18 ]
adcx r9, r8
adcx rbx, r10
add r9, rdi
adcx r15, rbx
xor rdx, rdx
adox rcx, r12
adox rbp, r11
mov r10, 0x3ffffffffffffff 
mov r12, rcx
and r12, r10
mov rdx, [ rsi + 0x8 ]
mulx r11, rax, r13
mov rdx, [ rsp + 0x70 ]
adox rdx, [ rsp + 0x0 ]
mov r13, [ rsp + 0x68 ]
adox r13, [ rsp - 0x8 ]
shrd rcx, rbp, 58
shr rbp, 58
xor rdi, rdi
adox r9, rax
adox r11, r15
adcx r9, [ rsp + 0x40 ]
adcx r11, [ rsp + 0x38 ]
add r9, rcx
adcx rbp, r11
mov r8, r9
shrd r8, rbp, 58
shr rbp, 58
and r9, r10
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x38 ], r9
and r14, r10
mov r15, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, rax, [ rsp + 0x48 ]
adox r15, rax
adox rcx, r13
adcx r15, r8
adcx rbp, rcx
mov [ rbx + 0x28 ], r14
mov rdx, r15
shrd rdx, rbp, 57
shr rbp, 57
mov r13, 0x39 
bzhi r11, r15, r13
mov [ rbx + 0x40 ], r11
adox rdx, [ rsp + 0x78 ]
adox rbp, rdi
mov r8, rdx
shrd r8, rbp, 58
add r8, [ rsp + 0x80 ]
and rdx, r10
mov r9, r8
and r9, r10
shr r8, 58
mov [ rbx + 0x0 ], rdx
add r8, [ rsp + 0x88 ]
mov [ rbx + 0x30 ], r12
mov [ rbx + 0x10 ], r8
mov [ rbx + 0x8 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 280
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.4599
; seed 2458047739678936 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3338908 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=80, initial num_batches=31): 108538 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.0325070352342742
; number reverted permutation / tried permutation: 65667 / 90284 =72.734%
; number reverted decision / tried decision: 59916 / 89715 =66.785%
; validated in 2.013s
