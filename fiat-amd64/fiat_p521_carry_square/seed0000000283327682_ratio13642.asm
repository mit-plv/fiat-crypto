SECTION .text
	GLOBAL fiat_p521_carry_square
fiat_p521_carry_square:
sub rsp, 408
mov rax, [ rsi + 0x38 ]
mov r10, rax
shl r10, 0x2
mov rdx, r10
mulx r10, rax, [ rsi + 0x28 ]
mov r11, [ rsi + 0x28 ]
lea rcx, [r11 + r11]
mulx r8, r11, [ rsi + 0x10 ]
mov r9, 0x1 
mov [ rsp - 0x80 ], rbx
shlx rbx, [ rsi + 0x10 ], r9
mov r9, [ rsi + 0x28 ]
mov [ rsp - 0x78 ], rbp
lea rbp, [ 4 * r9]
mov r9, [ rsi + 0x20 ]
mov [ rsp - 0x70 ], r12
mov r12, r9
shl r12, 0x1
mov r9, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mov r13, r9
shl r13, 0x1
imul r9, [ rsi + 0x40 ], 0x4
mov [ rsp - 0x60 ], r14
mov r14, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r9
mov rdx, r9
mov [ rsp - 0x48 ], r12
mulx r12, r9, [ rsi + 0x20 ]
mov [ rsp - 0x40 ], r13
mov [ rsp - 0x38 ], r12
mulx r12, r13, [ rsi + 0x8 ]
mov [ rsp - 0x30 ], r9
mov r9, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], rbx
mov [ rsp - 0x20 ], r10
mulx r10, rbx, rdx
mov rdx, r9
mov [ rsp - 0x18 ], r10
mulx r10, r9, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], rbx
mov rbx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x8 ], r10
mov [ rsp + 0x0 ], r9
mulx r9, r10, r14
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x8 ], r9
lea r9, [ 4 * rdx]
mov rdx, rcx
mov [ rsp + 0x10 ], r10
mulx r10, rcx, [ rsi + 0x28 ]
mov [ rsp + 0x18 ], rax
mov rax, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x20 ], r12
mov [ rsp + 0x28 ], r13
mulx r13, r12, r9
xor rdx, rdx
adox rcx, r12
adox r13, r10
mov rdx, r14
mulx r10, r14, [ rsi + 0x18 ]
mov r12, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x30 ], r8
mov [ rsp + 0x38 ], r11
mulx r11, r8, rbp
adcx rcx, r14
adcx r10, r13
test al, al
adox rcx, r15
adox rdi, r10
mov rdx, r9
mulx rbp, r9, [ rsi + 0x18 ]
adcx r8, r9
adcx rbp, r11
test al, al
adox r8, [ rsp + 0x38 ]
adox rbp, [ rsp + 0x30 ]
mov r15, rdx
mov rdx, [ rsi + 0x30 ]
mulx r14, r13, r12
mov rdx, [ rsi + 0x28 ]
mulx r11, r12, rbx
adcx r13, r12
adcx r11, r14
mov rdx, [ rsi + 0x10 ]
mulx r9, r10, rdx
test al, al
adox r13, r10
adox r9, r11
mov rdx, [ rsi + 0x0 ]
mulx r12, r14, rdx
adcx r8, [ rsp + 0x28 ]
adcx rbp, [ rsp + 0x20 ]
xor rdx, rdx
adox r8, r14
adox r12, rbp
mov r11, r8
shrd r11, r12, 58
shr r12, 58
mov r10, [ rsi + 0x30 ]
mov r14, r10
shl r14, 0x1
mov rdx, [ rsi + 0x30 ]
mulx rbp, r10, r14
xor rdx, rdx
adox r10, [ rsp + 0x18 ]
adox rbp, [ rsp - 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x40 ], r9
mov [ rsp + 0x48 ], r13
mulx r13, r9, r14
mov rdx, 0x1 
mov [ rsp + 0x50 ], r13
shlx r13, [ rsi + 0x8 ], rdx
mov rdx, r13
mov [ rsp + 0x58 ], r9
mulx r9, r13, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x60 ], rbp
mov [ rsp + 0x68 ], r10
mulx r10, rbp, r15
adcx rbp, [ rsp + 0x10 ]
adcx r10, [ rsp + 0x8 ]
mov rdx, 0x3ffffffffffffff 
and r8, rdx
adox rbp, [ rsp + 0x0 ]
adox r10, [ rsp - 0x8 ]
adcx rcx, r13
adcx r9, rdi
mov rdx, [ rsp - 0x28 ]
mulx rdi, r15, [ rsi + 0x8 ]
mov r13, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x70 ], r8
mov [ rsp + 0x78 ], r10
mulx r10, r8, r14
add rcx, r11
adcx r12, r9
mov rdx, [ rsp - 0x30 ]
mov r11, rdx
add r11, [ rsp + 0x68 ]
mov r9, [ rsp - 0x38 ]
adcx r9, [ rsp + 0x60 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x80 ], r10
mov [ rsp + 0x88 ], r8
mulx r8, r10, rdx
test al, al
adox r11, r15
adox rdi, r9
mov rdx, 0x3ffffffffffffff 
mov r15, rcx
and r15, rdx
mov rdx, r13
mulx r9, r13, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x90 ], r15
mov [ rsp + 0x98 ], rdi
mulx rdi, r15, [ rsp - 0x40 ]
adox rbp, r10
adox r8, [ rsp + 0x78 ]
mov rdx, [ rsp - 0x48 ]
mov [ rsp + 0xa0 ], r11
mulx r11, r10, [ rsi + 0x0 ]
adcx rbp, r13
adcx r9, r8
mov r13, r15
add r13, [ rsp + 0xa0 ]
adcx rdi, [ rsp + 0x98 ]
shrd rcx, r12, 58
shr r12, 58
xor r15, r15
adox rbp, rcx
adox r12, r9
mulx r9, r8, [ rsi + 0x10 ]
mov rcx, rbp
shrd rcx, r12, 58
shr r12, 58
mov [ rsp + 0xa8 ], r9
mulx r9, r15, [ rsi + 0x8 ]
mov [ rsp + 0xb0 ], r9
mov r9, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xb8 ], r15
mov [ rsp + 0xc0 ], r8
mulx r8, r15, [ rsp - 0x40 ]
mov rdx, rbx
mov [ rsp + 0xc8 ], r11
mulx r11, rbx, [ rsi + 0x38 ]
mov [ rsp + 0xd0 ], r11
mov r11, r15
add r11, [ rsp + 0x48 ]
adcx r8, [ rsp + 0x40 ]
xor r15, r15
adox r13, rcx
adox r12, rdi
mov rdi, 0x3ffffffffffffff 
mov rcx, r13
and rcx, rdi
adox r11, r10
adox r8, [ rsp + 0xc8 ]
mulx r15, r10, [ rsi + 0x30 ]
adcx rbx, [ rsp - 0x10 ]
mov rdx, [ rsp + 0xd0 ]
adcx rdx, [ rsp - 0x18 ]
xor rdi, rdi
adox rbx, [ rsp + 0xc0 ]
adox rdx, [ rsp + 0xa8 ]
mov rdi, [ rsi + 0x38 ]
mov [ rsp + 0xd8 ], rdx
mov rdx, rdi
shl rdx, 0x1
mov [ rsp + 0xe0 ], rbx
mulx rbx, rdi, [ rsi + 0x38 ]
test al, al
adox rdi, r10
adox r15, rbx
shrd r13, r12, 58
shr r12, 58
mulx rbx, r10, [ rsi + 0x8 ]
mov [ rsp + 0xe8 ], rbx
mov rbx, 0x3a 
mov [ rsp + 0xf0 ], r10
bzhi r10, rbp, rbx
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x18 ], rcx
mulx rbx, rcx, [ rsi + 0x0 ]
adox r11, r13
adox r12, r8
mov rdx, [ rsi + 0x10 ]
mulx r13, r8, [ rsp - 0x40 ]
test al, al
adox rdi, r8
adox r13, r15
mov rdx, rax
mulx r15, rax, [ rsi + 0x8 ]
xchg rdx, r14
mulx rbp, r8, [ rsi + 0x0 ]
adcx rdi, [ rsp + 0xb8 ]
adcx r13, [ rsp + 0xb0 ]
mov rdx, r14
mov [ rsp + 0xf8 ], r10
mulx r10, r14, [ rsi + 0x0 ]
mov [ rsp + 0x100 ], rbx
xor rbx, rbx
adox rdi, r14
adox r10, r13
mov r13, r11
shrd r13, r12, 58
shr r12, 58
imul r14, [ rsi + 0x40 ], 0x2
mov [ rsp + 0x108 ], rcx
xor rcx, rcx
adox rdi, r13
adox r12, r10
mov rbx, rdi
shrd rbx, r12, 58
shr r12, 58
mov r10, rdx
mov rdx, [ rsi + 0x18 ]
mulx rcx, r13, r9
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x110 ], rcx
mulx rcx, r9, r14
mov rdx, 0x3ffffffffffffff 
and rdi, rdx
mov rdx, rax
adox rdx, [ rsp + 0xe0 ]
adox r15, [ rsp + 0xd8 ]
adcx rdx, r8
adcx rbp, r15
add rdx, rbx
adcx r12, rbp
mov rax, 0x3ffffffffffffff 
mov r8, rdx
and r8, rax
shrd rdx, r12, 58
shr r12, 58
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x30 ], r8
mov [ rbx + 0x28 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x40 ]
mulx rbp, r15, r14
add r15, r13
adcx rbp, [ rsp + 0x110 ]
mov rdx, [ rsi + 0x10 ]
mulx r13, r14, r10
xor rdx, rdx
adox r15, r14
adox r13, rbp
adcx r15, [ rsp + 0x58 ]
adcx r13, [ rsp + 0x50 ]
xor r8, r8
adox r15, [ rsp + 0x108 ]
adox r13, [ rsp + 0x100 ]
mov rdx, [ rsi + 0x20 ]
mulx r14, rbp, rdx
adcx r15, rdi
adcx r12, r13
mov rdx, [ rsi + 0x18 ]
mulx r13, rdi, r10
test al, al
adox rbp, rdi
adox r13, r14
adcx rbp, [ rsp + 0x88 ]
adcx r13, [ rsp + 0x80 ]
xor rdx, rdx
adox rbp, [ rsp + 0xf0 ]
adox r13, [ rsp + 0xe8 ]
adcx rbp, r9
adcx rcx, r13
and r11, rax
mov r8, r15
shrd r8, r12, 58
shr r12, 58
mov [ rbx + 0x20 ], r11
add rbp, r8
adcx r12, rcx
mov r10, rbp
shrd r10, r12, 57
shr r12, 57
add r10, [ rsp + 0x70 ]
adc r12, 0x0
mov r9, r10
shrd r9, r12, 58
and r10, rax
add r9, [ rsp + 0x90 ]
mov r14, r9
shr r14, 58
add r14, [ rsp + 0xf8 ]
mov rdi, 0x1ffffffffffffff 
and rbp, rdi
mov [ rbx + 0x10 ], r14
mov [ rbx + 0x40 ], rbp
and r15, rax
and r9, rax
mov [ rbx + 0x8 ], r9
mov [ rbx + 0x38 ], r15
mov [ rbx + 0x0 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 408
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.3642
; seed 1850417181977866 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2515962 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=153, initial num_batches=31): 99445 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.03952563671470396
; number reverted permutation / tried permutation: 72285 / 89948 =80.363%
; number reverted decision / tried decision: 65715 / 90051 =72.975%
; validated in 1.209s
