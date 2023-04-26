SECTION .text
	GLOBAL fiat_p521_carry_square
fiat_p521_carry_square:
sub rsp, 376
mov rax, [ rsi + 0x30 ]
lea r10, [rax + rax]
imul rax, [ rsi + 0x10 ], 0x2
mov r11, 0x2 
shlx rdx, [ rsi + 0x40 ], r11
mulx r8, rcx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov rbp, [ rsi + 0x28 ]
mov [ rsp - 0x70 ], r12
mov r12, rbp
shl r12, 0x2
mov [ rsp - 0x68 ], r13
mulx r13, rbp, [ rsi + 0x20 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x18 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, r11, [ rsi + 0x28 ]
xchg rdx, r12
mov [ rsp - 0x48 ], rdi
mov [ rsp - 0x40 ], r11
mulx r11, rdi, [ rsi + 0x20 ]
mov rdx, 0x2 
mov [ rsp - 0x38 ], r13
shlx r13, [ rsi + 0x30 ], rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x30 ], rbp
mov [ rsp - 0x28 ], r10
mulx r10, rbp, rax
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x20 ], rbx
mov rbx, rdx
shl rbx, 0x1
mov rdx, r13
mov [ rsp - 0x18 ], rbx
mulx rbx, r13, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], r9
mov r9, [ rsi + 0x28 ]
mov [ rsp - 0x8 ], r8
mov r8, r9
shl r8, 0x1
mov [ rsp + 0x0 ], rcx
mulx rcx, r9, [ rsi + 0x28 ]
mov [ rsp + 0x8 ], r10
mov [ rsp + 0x10 ], rbp
mulx rbp, r10, [ rsi + 0x20 ]
mov rdx, r8
mov [ rsp + 0x18 ], rbp
mulx rbp, r8, [ rsi + 0x28 ]
mov [ rsp + 0x20 ], rbp
mov rbp, [ rsi + 0x8 ]
mov [ rsp + 0x28 ], r8
mov r8, rbp
shl r8, 0x1
mov rbp, [ rsi + 0x38 ]
mov [ rsp + 0x30 ], r10
mov r10, rbp
shl r10, 0x2
mov rbp, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x38 ], r11
mov [ rsp + 0x40 ], rdi
mulx rdi, r11, r10
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x48 ], rbx
mov [ rsp + 0x50 ], r13
mulx r13, rbx, rbp
xor rdx, rdx
adox r9, r11
adox rdi, rcx
adcx r9, r14
adcx r15, rdi
mov rdx, [ rsi + 0x8 ]
mulx rcx, r14, rax
mov rdx, r8
mulx rax, r8, [ rsi + 0x0 ]
mov rdx, rbp
mulx r11, rbp, [ rsi + 0x18 ]
mov rdi, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x58 ], r11
mov [ rsp + 0x60 ], rbp
mulx rbp, r11, rdx
mov rdx, [ rsp + 0x50 ]
mov [ rsp + 0x68 ], r13
mov r13, rdx
mov [ rsp + 0x70 ], rbx
xor rbx, rbx
adox r13, [ rsp + 0x40 ]
mov [ rsp + 0x78 ], rcx
mov rcx, [ rsp + 0x48 ]
adox rcx, [ rsp + 0x38 ]
adcx r9, r11
adcx rbp, r15
mov rdx, r10
mulx r15, r10, [ rsi + 0x10 ]
xor r11, r11
adox r9, [ rsp + 0x10 ]
adox rbp, [ rsp + 0x8 ]
adcx r13, r10
adcx r15, rcx
mulx rcx, rbx, [ rsi + 0x18 ]
mov r10, [ rsp + 0x28 ]
mov [ rsp + 0x80 ], r14
xor r14, r14
adox r10, [ rsp + 0x30 ]
mov r11, [ rsp + 0x20 ]
adox r11, [ rsp + 0x18 ]
adcx r10, rbx
adcx rcx, r11
test al, al
adox r10, [ rsp + 0x0 ]
adox rcx, [ rsp - 0x8 ]
mov rbx, rdx
mov rdx, [ rsi + 0x0 ]
mulx r14, r11, rdx
adcx r13, [ rsp - 0x10 ]
adcx r15, [ rsp - 0x20 ]
xor rdx, rdx
adox r13, r11
adox r14, r15
adcx r10, r8
adcx rax, rcx
mov r8, r13
shrd r8, r14, 58
shr r14, 58
test al, al
adox r10, r8
adox r14, rax
mov rcx, r10
shrd rcx, r14, 58
shr r14, 58
mov rdx, [ rsi + 0x28 ]
mulx r15, r11, rbx
mov rdx, [ rsi + 0x30 ]
mulx r8, rax, [ rsp - 0x28 ]
mov rdx, 0x1 
mov [ rsp + 0x88 ], rbp
shlx rbp, [ rsi + 0x18 ], rdx
xor rdx, rdx
adox rax, r11
adox r15, r8
adcx rax, [ rsp - 0x30 ]
adcx r15, [ rsp - 0x38 ]
add r9, rcx
adcx r14, [ rsp + 0x88 ]
mov rdx, [ rsi + 0x30 ]
mulx r11, rcx, rbx
mov rdx, rbp
mulx rbx, rbp, [ rsi + 0x0 ]
xor r8, r8
adox rax, [ rsp + 0x80 ]
adox r15, [ rsp + 0x78 ]
adcx rax, rbp
adcx rbx, r15
add rcx, [ rsp - 0x40 ]
adcx r11, [ rsp - 0x48 ]
mov rbp, r9
shrd rbp, r14, 58
shr r14, 58
add rax, rbp
adcx r14, rbx
mov r15, 0x3a 
bzhi rbx, r10, r15
mov r10, rdx
mov rdx, [ rsi + 0x38 ]
mulx r8, rbp, [ rsp - 0x18 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x90 ], rbx
mulx rbx, r15, r12
mov rdx, 0x3ffffffffffffff 
and r9, rdx
adox rbp, r15
adox rbx, r8
mov r8, [ rsi + 0x40 ]
lea r15, [r8 + r8]
mov rdx, r10
mulx r8, r10, [ rsi + 0x10 ]
mov [ rsp + 0x98 ], r9
mov r9, [ rsi + 0x20 ]
mov [ rsp + 0xa0 ], r15
lea r15, [r9 + r9]
adcx rbp, r10
adcx r8, rbx
mulx rbx, r9, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xa8 ], r8
mulx r8, r10, rdx
test al, al
adox rcx, r10
adox r8, r11
adcx rcx, r9
adcx rbx, r8
mov rdx, rdi
mulx r11, rdi, [ rsi + 0x0 ]
mov r9, rdx
mov rdx, [ rsi + 0x0 ]
mulx r8, r10, r15
mov rdx, rax
shrd rdx, r14, 58
shr r14, 58
mov [ rsp + 0xb0 ], r11
xor r11, r11
adox rcx, r10
adox r8, rbx
adcx rcx, rdx
adcx r14, r8
mov rdx, [ rsi + 0x8 ]
mulx r10, rbx, r15
xor rdx, rdx
adox rbp, rbx
adox r10, [ rsp + 0xa8 ]
mov rdx, [ rsi + 0x40 ]
mulx r8, r11, [ rsp + 0xa0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xb8 ], r14
mulx r14, rbx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xc0 ], r14
mov [ rsp + 0xc8 ], rbx
mulx rbx, r14, r9
mov rdx, r15
mulx r9, r15, [ rsi + 0x10 ]
mov [ rsp + 0xd0 ], r9
mov [ rsp + 0xd8 ], r15
mulx r15, r9, [ rsi + 0x18 ]
adcx r11, r9
adcx r15, r8
mov rdx, [ rsi + 0x38 ]
mulx r9, r8, r12
xor rdx, rdx
adox r11, r14
adox rbx, r15
adcx rbp, rdi
adcx r10, [ rsp + 0xb0 ]
mov r12, [ rsp + 0xb8 ]
mov rdi, rcx
shrd rdi, r12, 58
shr r12, 58
mov rdx, [ rsi + 0x20 ]
mulx r15, r14, rdx
mov rdx, 0x3a 
mov [ rsp + 0xe0 ], r15
bzhi r15, rcx, rdx
adox rbp, rdi
adox r12, r10
mov rcx, rbp
shrd rcx, r12, 58
shr r12, 58
xor r10, r10
adox r8, [ rsp + 0xc8 ]
adox r9, [ rsp + 0xc0 ]
adcx r8, [ rsp + 0xd8 ]
adcx r9, [ rsp + 0xd0 ]
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x20 ], r15
mov rdx, [ rsi + 0x8 ]
mulx r10, r15, [ rsp - 0x28 ]
xor rdx, rdx
adox r11, r15
adox r10, rbx
adcx r8, [ rsp + 0x70 ]
adcx r9, [ rsp + 0x68 ]
mov rbx, 0x3a 
bzhi r15, rbp, rbx
mov rdx, [ rsp - 0x28 ]
mulx rbx, rbp, [ rsi + 0x0 ]
adox r8, rbp
adox rbx, r9
mulx rbp, r9, [ rsi + 0x10 ]
xor rdx, rdx
adox r8, rcx
adox r12, rbx
mov rcx, 0x3a 
bzhi rbx, r8, rcx
mov rdx, [ rsi + 0x8 ]
mulx rdi, rcx, [ rsp - 0x18 ]
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x30 ], rbx
mov rbx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xe8 ], r15
mov [ rsp + 0xf0 ], rdi
mulx rdi, r15, [ rsp - 0x18 ]
adox r11, r15
adox rdi, r10
xor rdx, rdx
adox r14, [ rsp + 0x60 ]
mov r10, [ rsp + 0x58 ]
adox r10, [ rsp + 0xe0 ]
adcx r14, r9
adcx rbp, r10
shrd r8, r12, 58
shr r12, 58
xor r9, r9
adox r14, rcx
adox rbp, [ rsp + 0xf0 ]
adcx r11, r8
adcx r12, rdi
mov rdx, 0x3a 
bzhi rcx, r13, rdx
mov rdx, [ rsp + 0xa0 ]
mulx r15, r13, [ rsi + 0x0 ]
mov rdx, r11
shrd rdx, r12, 58
shr r12, 58
xor rdi, rdi
adox r14, r13
adox r15, rbp
adcx r14, rdx
adcx r12, r15
mov r9, 0x1ffffffffffffff 
mov r10, r14
and r10, r9
shrd r14, r12, 57
shr r12, 57
xor r8, r8
adox r14, rcx
adox r12, r8
mov rdi, 0x3ffffffffffffff 
mov rbp, r14
and rbp, rdi
shrd r14, r12, 58
add r14, [ rsp + 0x90 ]
mov rcx, r14
and rcx, rdi
mov [ rbx + 0x8 ], rcx
mov [ rbx + 0x0 ], rbp
and rax, rdi
mov [ rbx + 0x18 ], rax
shr r14, 58
add r14, [ rsp + 0x98 ]
mov [ rbx + 0x10 ], r14
and r11, rdi
mov r13, [ rsp + 0xe8 ]
mov [ rbx + 0x28 ], r13
mov [ rbx + 0x38 ], r11
mov [ rbx + 0x40 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 376
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.3573
; seed 2328606217238938 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2322632 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=180, initial num_batches=31): 99501 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.04283976109861571
; number reverted permutation / tried permutation: 69439 / 90077 =77.088%
; number reverted decision / tried decision: 62911 / 89922 =69.962%
; validated in 1.137s
