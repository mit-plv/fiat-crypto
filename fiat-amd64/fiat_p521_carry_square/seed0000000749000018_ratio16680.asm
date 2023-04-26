SECTION .text
	GLOBAL fiat_p521_carry_square
fiat_p521_carry_square:
sub rsp, 240
mov rax, 0x2 
shlx r10, [ rsi + 0x40 ], rax
mov r11, [ rsi + 0x30 ]
lea rdx, [ 4 * r11]
mulx rcx, r11, [ rsi + 0x18 ]
mov r8, [ rsi + 0x18 ]
lea r9, [r8 + r8]
mov r8, 0x1 
mov [ rsp - 0x80 ], rbx
shlx rbx, [ rsi + 0x38 ], r8
mov r8, [ rsi + 0x38 ]
mov [ rsp - 0x78 ], rbp
mov rbp, r8
shl rbp, 0x2
imul r8, [ rsi + 0x30 ], 0x2
mov [ rsp - 0x70 ], r12
imul r12, [ rsi + 0x8 ], 0x2
mov [ rsp - 0x68 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rbp
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x50 ], rdi
lea rdi, [rdx + rdx]
shlx rdx, [ rsi + 0x28 ], rax
mov [ rsp - 0x48 ], rbx
mulx rbx, rax, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x40 ], r15
mov [ rsp - 0x38 ], r14
mulx r14, r15, rdi
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x30 ], r14
mov [ rsp - 0x28 ], r15
mulx r15, r14, rbp
mov rdx, r13
mov [ rsp - 0x20 ], r12
mulx r12, r13, [ rsi + 0x28 ]
xchg rdx, r9
mov [ rsp - 0x18 ], r10
mov [ rsp - 0x10 ], r8
mulx r8, r10, [ rsi + 0x8 ]
test al, al
adox r13, r14
adox r15, r12
adcx rax, r11
adcx rcx, rbx
imul r11, [ rsi + 0x28 ], 0x2
mulx r14, rbx, [ rsi + 0x0 ]
mov [ rsp - 0x8 ], r14
mulx r14, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x0 ], r14
mov [ rsp + 0x8 ], r12
mulx r12, r14, r11
mov rdx, r9
mov [ rsp + 0x10 ], rbx
mulx rbx, r9, [ rsi + 0x20 ]
mov rdx, rbp
mov [ rsp + 0x18 ], r8
mulx r8, rbp, [ rsi + 0x28 ]
test al, al
adox r14, r9
adox rbx, r12
mov r12, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x20 ], r10
mulx r10, r9, [ rsp - 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x28 ], rbx
mov [ rsp + 0x30 ], r14
mulx r14, rbx, r12
adcx r9, rbp
adcx r8, r10
test al, al
adox rax, rbx
adox r14, rcx
mov rdx, [ rsi + 0x8 ]
mulx rbp, rcx, [ rsp - 0x18 ]
adcx rax, rcx
adcx rbp, r14
mov rdx, [ rsi + 0x18 ]
mulx rbx, r10, [ rsp - 0x18 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r14, rdx
add r13, r10
adcx rbx, r15
mov rdx, [ rsi + 0x20 ]
mulx r10, r15, [ rsp - 0x18 ]
add r9, r15
adcx r10, r8
mov rdx, [ rsi + 0x0 ]
mulx r15, r8, rdx
xor rdx, rdx
adox rax, r8
adox r15, rbp
mov rdx, [ rsi + 0x0 ]
mulx r8, rbp, rdi
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x38 ], r10
mulx r10, rdi, r12
adcx r13, r14
adcx rcx, rbx
mov rdx, 0x3ffffffffffffff 
mov r12, rax
and r12, rdx
mov rdx, [ rsp - 0x18 ]
mulx rbx, r14, [ rsi + 0x10 ]
mov [ rsp + 0x40 ], r12
mov r12, rdi
adox r12, [ rsp + 0x30 ]
adox r10, [ rsp + 0x28 ]
adcx r13, rbp
adcx r8, rcx
xor rbp, rbp
adox r12, r14
adox rbx, r10
mov rdi, rdx
mov rdx, [ rsp - 0x20 ]
mulx r14, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mulx rbp, r10, rdi
adcx r12, rcx
adcx r14, rbx
mov rdx, [ rsi + 0x10 ]
mulx rcx, rbx, rdx
shrd rax, r15, 58
shr r15, 58
test al, al
adox r12, rax
adox r15, r14
mov rdx, r12
shrd rdx, r15, 58
shr r15, 58
mov r14, r10
test al, al
adox r14, [ rsp - 0x38 ]
adox rbp, [ rsp - 0x40 ]
mov r10, 0x3ffffffffffffff 
and r12, r10
mov rax, [ rsi + 0x20 ]
lea r10, [rax + rax]
adox r14, rbx
adox rcx, rbp
adcx r14, [ rsp + 0x20 ]
adcx rcx, [ rsp + 0x18 ]
xchg rdx, r10
mulx rbx, rax, [ rsi + 0x18 ]
xor rbp, rbp
adox r9, [ rsp - 0x28 ]
mov [ rsp + 0x48 ], r12
mov r12, [ rsp - 0x30 ]
adox r12, [ rsp + 0x38 ]
adcx r13, r10
adcx r15, r8
xor r8, r8
adox r9, [ rsp + 0x10 ]
adox r12, [ rsp - 0x8 ]
mulx r10, rbp, [ rsi + 0x0 ]
mov r8, r13
shrd r8, r15, 58
shr r15, 58
mov [ rsp + 0x50 ], rbx
mov [ rsp + 0x58 ], rax
mulx rax, rbx, [ rsi + 0x10 ]
mov [ rsp + 0x60 ], rax
mov [ rsp + 0x68 ], rbx
mulx rbx, rax, [ rsi + 0x8 ]
xor rdx, rdx
adox r14, rbp
adox r10, rcx
adcx r9, r8
adcx r15, r12
mov rdx, rdi
mulx rcx, rdi, [ rsi + 0x30 ]
mov r12, r9
shrd r12, r15, 58
shr r15, 58
xor rbp, rbp
adox r14, r12
adox r15, r10
mov r8, 0x3a 
bzhi r10, r9, r8
mov r9, rdx
mov rdx, [ rsi + 0x38 ]
mulx rbp, r12, [ rsp - 0x48 ]
adox r12, rdi
adox rcx, rbp
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x18 ], r10
xor rdi, rdi
adox r12, [ rsp + 0x8 ]
adox rcx, [ rsp + 0x0 ]
adcx r12, rax
adcx rbx, rcx
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx rbp, r10, r11
add r12, r10
adcx rbp, rbx
bzhi rdx, r14, r8
mov rcx, rdx
mov rdx, [ rsi + 0x38 ]
mulx r10, rbx, r9
mov [ rax + 0x20 ], rcx
shrd r14, r15, 58
shr r15, 58
xor rdx, rdx
adox r12, r14
adox r15, rbp
mov rdi, r12
shrd rdi, r15, 58
shr r15, 58
bzhi r9, r12, r8
mov rdx, [ rsi + 0x18 ]
mulx rcx, rbp, rdx
mov rdx, [ rsi + 0x0 ]
mulx r12, r14, [ rsp - 0x10 ]
mov [ rax + 0x28 ], r9
mov rdx, [ rsi + 0x20 ]
mulx r8, r9, rdx
adox rbx, rbp
adox rcx, r10
mov rdx, [ rsi + 0x8 ]
mulx rbp, r10, r11
xor rdx, rdx
adox rbx, [ rsp + 0x68 ]
adox rcx, [ rsp + 0x60 ]
adcx rbx, r10
adcx rbp, rcx
xor r10, r10
adox rbx, r14
adox r12, rbp
mov rdx, 0x1 
shlx r14, [ rsi + 0x40 ], rdx
adcx rbx, rdi
adcx r15, r12
mov rdx, r11
mulx rdi, r11, [ rsi + 0x10 ]
mulx rbp, rcx, [ rsi + 0x18 ]
add r9, rcx
adcx rbp, r8
mov rdx, [ rsi + 0x8 ]
mulx r12, r8, [ rsp - 0x10 ]
mov rdx, [ rsi + 0x40 ]
mulx r10, rcx, r14
test al, al
adox rcx, [ rsp + 0x58 ]
adox r10, [ rsp + 0x50 ]
adcx rcx, r11
adcx rdi, r10
mov rdx, [ rsi + 0x10 ]
mulx r10, r11, [ rsp - 0x10 ]
test al, al
adox r9, r11
adox r10, rbp
adcx rcx, r8
adcx r12, rdi
mov rdx, [ rsp - 0x48 ]
mulx r8, rbp, [ rsi + 0x0 ]
xor rdi, rdi
adox rcx, rbp
adox r8, r12
mov r11, rbx
shrd r11, r15, 58
shr r15, 58
add rcx, r11
adcx r15, r8
mulx rbp, r12, [ rsi + 0x8 ]
mov rdx, rcx
shrd rdx, r15, 58
shr r15, 58
mov r8, rdx
mov rdx, [ rsi + 0x0 ]
mulx rdi, r11, r14
test al, al
adox r9, r12
adox rbp, r10
mov rdx, 0x3a 
bzhi r14, rcx, rdx
adox r9, r11
adox rdi, rbp
mov [ rax + 0x38 ], r14
xor r10, r10
adox r9, r8
adox r15, rdi
mov rcx, 0x39 
bzhi r12, r9, rcx
shrd r9, r15, 57
shr r15, 57
test al, al
adox r9, [ rsp + 0x40 ]
adox r15, r10
bzhi r8, r9, rdx
shrd r9, r15, 58
bzhi r11, r13, rdx
add r9, [ rsp + 0x48 ]
bzhi r13, r9, rdx
bzhi rbp, rbx, rdx
mov [ rax + 0x8 ], r13
mov [ rax + 0x30 ], rbp
shr r9, 58
lea r9, [ r9 + r11 ]
mov [ rax + 0x10 ], r9
mov [ rax + 0x40 ], r12
mov [ rax + 0x0 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 240
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.6680
; seed 3212282186721815 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4905417 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=70, initial num_batches=31): 157691 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.03214629867348688
; number reverted permutation / tried permutation: 64620 / 89682 =72.055%
; number reverted decision / tried decision: 59933 / 90317 =66.358%
; validated in 1.955s
