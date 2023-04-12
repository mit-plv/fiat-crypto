SECTION .text
	GLOBAL fiat_curve25519_solinas_mul
fiat_curve25519_solinas_mul:
sub rsp, 136
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mulx r8, rcx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], r12
mov [ rsp - 0x40 ], r15
mulx r15, r12, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x38 ], r13
mov [ rsp - 0x30 ], r8
mulx r8, r13, [ rax + 0x10 ]
test al, al
adox r10, r8
adox rcx, rdi
mov rdx, [ rsi + 0x10 ]
mulx r8, rdi, [ rax + 0x8 ]
adcx rdi, r10
adcx r11, rcx
mov rdx, [ rax + 0x10 ]
mulx rcx, r10, [ rsi + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x28 ], rcx
mov [ rsp - 0x20 ], r14
mulx r14, rcx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x18 ], rcx
mov [ rsp - 0x10 ], r13
mulx r13, rcx, [ rsi + 0x8 ]
mov rdx, 0x0 
adox r13, rdx
mov [ rsp - 0x8 ], rcx
mov rcx, -0x3 
inc rcx
adox r12, rbx
mov rbx, rdx
adcx rbx, r13
adox r15, rdi
adox rbp, r11
mov rdx, [ rax + 0x0 ]
mulx r11, rdi, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r13, [ rax + 0x8 ]
adox r10, rbx
seto dl
mov rbx, -0x2 
inc rbx
adox rdi, r14
setc r14b
clc
adcx r13, r12
adox r11, r13
seto r12b
inc rbx
adox r9, rdi
mov dil, dl
mov rdx, [ rax + 0x10 ]
mulx rbx, r13, [ rsi + 0x8 ]
adcx r13, r15
adcx r8, rbp
adox r11, [ rsp - 0x10 ]
mov rdx, [ rsi + 0x10 ]
mulx rbp, r15, [ rax + 0x18 ]
setc dl
clc
mov [ rsp + 0x0 ], r11
mov r11, -0x1 
movzx r12, r12b
adcx r12, r11
adcx r13, rcx
movzx rcx, r14b
lea rcx, [ rcx + rbp ]
mov r14, 0x0 
setc r12b
clc
movzx rdi, dil
adcx rdi, r11
adcx rcx, r14
mov rdi, [ rsp - 0x20 ]
adcx rdi, r14
clc
movzx rdx, dl
adcx rdx, r11
adcx r10, [ rsp - 0x30 ]
mov rdx, r14
adcx rdx, rcx
setc bpl
clc
movzx r12, r12b
adcx r12, r11
adcx r8, [ rsp - 0x8 ]
adcx r15, r10
movzx rbp, bpl
lea rdi, [ rdi + r14 ]
lea rdi, [ rdi + rbp ]
adcx rdx, [ rsp - 0x38 ]
adox r13, [ rsp - 0x40 ]
adox rbx, r8
adox r15, [ rsp - 0x48 ]
mov r12, 0x26 
xchg rdx, r12
mulx r10, rcx, r15
adox r12, [ rsp - 0x28 ]
mulx r8, rbp, r12
adcx rdi, r14
adox rdi, r14
mulx r12, r15, rdi
test al, al
adox rcx, r9
mulx rdi, r9, rbx
adcx r9, [ rsp - 0x18 ]
adox rbp, [ rsp + 0x0 ]
adcx rdi, rcx
adcx r10, rbp
adox r15, r13
adox r12, r14
adcx r8, r15
adc r12, 0x0
mulx rbx, r13, r12
test al, al
adox r13, r9
mov rbx, r14
adox rbx, rdi
mov rcx, r14
adox rcx, r10
mov r9, r14
adox r9, r8
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x10 ], rcx
mov [ rbp + 0x8 ], rbx
mov [ rbp + 0x18 ], r9
mov rdi, r14
cmovo rdi, rdx
adcx r13, rdi
mov [ rbp + 0x0 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 136
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.6214
; seed 0105761285843815 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3539 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=168, initial num_batches=31): 323 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.09126871997739475
; number reverted permutation / tried permutation: 389 / 488 =79.713%
; number reverted decision / tried decision: 301 / 511 =58.904%
; validated in 0.351s
