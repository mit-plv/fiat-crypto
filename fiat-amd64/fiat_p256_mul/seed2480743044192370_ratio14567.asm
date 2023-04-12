SECTION .text
	GLOBAL fiat_p256_mul
fiat_p256_mul:
sub rsp, 184
mov rax, rdx
mov rdx, [ rdx + 0x8 ]
mulx r11, r10, [ rsi + 0x8 ]
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x8 ]
test al, al
adox r9, r8
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x48 ], r9
mulx r9, r8, [ rax + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x40 ], rcx
mov [ rsp - 0x38 ], r14
mulx r14, rcx, [ rax + 0x0 ]
adcx r10, r14
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x30 ], r10
mulx r10, r14, [ rsi + 0x18 ]
adox r14, rbx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], r14
mulx r14, rbx, [ rax + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x20 ], rcx
mov [ rsp - 0x18 ], r13
mulx r13, rcx, [ rax + 0x8 ]
adcx rbx, r11
adox rbp, r10
mov rdx, [ rsi + 0x0 ]
mulx r10, r11, [ rax + 0x0 ]
adcx r15, r14
mov rdx, 0xffffffff 
mov [ rsp - 0x10 ], rbp
mulx rbp, r14, r11
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x8 ], r15
mov [ rsp + 0x0 ], rbx
mulx rbx, r15, r11
mov rdx, 0x0 
adcx rdi, rdx
clc
adcx r14, rbx
adcx rbp, rdx
clc
adcx rcx, r10
adcx r8, r13
adox r12, rdx
adcx r9, [ rsp - 0x18 ]
mov r13, [ rsp - 0x38 ]
adc r13, 0x0
add r15, r11
adcx r14, rcx
adcx rbp, r8
mov r15, -0x3 
inc r15
adox r14, [ rsp - 0x20 ]
mov r10, 0xffffffff00000001 
mov rdx, r11
mulx rbx, r11, r10
adcx r11, r9
mov rdx, 0xffffffffffffffff 
mulx r8, rcx, r14
adox rbp, [ rsp - 0x30 ]
adcx rbx, r13
adox r11, [ rsp + 0x0 ]
mov rdx, [ rax + 0x8 ]
mulx r13, r9, [ rsi + 0x10 ]
adox rbx, [ rsp - 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx r10, r15, [ rax + 0x0 ]
setc dl
clc
adcx rcx, r14
setc cl
clc
adcx r9, r10
mov r10b, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x8 ], r12
mov [ rsp + 0x10 ], rbx
mulx rbx, r12, [ rax + 0x10 ]
adcx r12, r13
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x18 ], r12
mulx r12, r13, [ rsi + 0x10 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x20 ], r12
mov [ rsp + 0x28 ], r9
mulx r9, r12, r14
adcx r13, rbx
mov rbx, 0xffffffff00000001 
mov rdx, rbx
mov [ rsp + 0x30 ], r13
mulx r13, rbx, r14
movzx r14, r10b
adox r14, rdi
setc dil
clc
adcx r12, r8
mov r8, 0x0 
adcx r9, r8
clc
mov r10, -0x1 
movzx rcx, cl
adcx rcx, r10
adcx rbp, r12
seto cl
mov r12, -0x3 
inc r12
adox r15, rbp
adcx r9, r11
adox r9, [ rsp + 0x28 ]
adcx rbx, [ rsp + 0x10 ]
adcx r13, r14
adox rbx, [ rsp + 0x18 ]
mov r11, 0xffffffffffffffff 
mov rdx, r15
mulx r14, r15, r11
setc bpl
clc
adcx r15, rdx
movzx r15, bpl
movzx rcx, cl
lea r15, [ r15 + rcx ]
movzx rcx, dil
mov rbp, [ rsp + 0x20 ]
lea rcx, [ rcx + rbp ]
adox r13, [ rsp + 0x30 ]
mov rbp, 0xffffffff 
mulx r8, rdi, rbp
adox rcx, r15
seto r15b
inc r10
adox rdi, r14
adox r8, r10
adcx rdi, r9
mov r9, -0x3 
inc r9
adox rdi, [ rsp - 0x40 ]
mov r9, 0xffffffff00000001 
mulx r10, r14, r9
mov rdx, rdi
mulx r12, rdi, r9
adcx r8, rbx
adcx r14, r13
adcx r10, rcx
adox r8, [ rsp - 0x48 ]
movzx rbx, r15b
mov r13, 0x0 
adcx rbx, r13
mulx rcx, r15, rbp
adox r14, [ rsp - 0x28 ]
adox r10, [ rsp - 0x10 ]
mulx r9, r13, r11
clc
adcx r15, r9
mov r9, 0x0 
adcx rcx, r9
clc
adcx r13, rdx
adcx r15, r8
adox rbx, [ rsp + 0x8 ]
adcx rcx, r14
adcx rdi, r10
adcx r12, rbx
seto r13b
adc r13b, 0x0
movzx r13, r13b
mov rdx, r15
sub rdx, r11
mov r8, rcx
sbb r8, rbp
mov r14, rdi
sbb r14, 0x00000000
mov r10, r12
mov rbx, 0xffffffff00000001 
sbb r10, rbx
movzx rbx, r13b
sbb rbx, 0x00000000
cmovc r8, rcx
cmovc rdx, r15
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x0 ], rdx
cmovc r14, rdi
cmovc r10, r12
mov [ rbx + 0x18 ], r10
mov [ rbx + 0x10 ], r14
mov [ rbx + 0x8 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 184
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.4567
; seed 2480743044192370 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 11215 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=218, initial num_batches=31): 822 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.07329469460543915
; number reverted permutation / tried permutation: 378 / 542 =69.742%
; number reverted decision / tried decision: 278 / 457 =60.832%
; validated in 3.048s
