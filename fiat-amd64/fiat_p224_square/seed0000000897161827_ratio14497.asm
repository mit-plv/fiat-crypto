SECTION .text
	GLOBAL fiat_p224_square
fiat_p224_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rax
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rbx
mov [ rsp - 0x68 ], r13
mov r13, rbx
mov [ rsp - 0x60 ], r14
xor r14, r14
adox r13, rax
mov rdx, [ rsi + 0x18 ]
mulx rax, r13, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x8 ]
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rax
mulx rax, rdi, rbx
adcx rbp, rax
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], r13
mulx r13, rax, rdx
mov rdx, 0xffffffff 
mov [ rsp - 0x38 ], r13
mov [ rsp - 0x30 ], rax
mulx rax, r13, rbx
seto bl
mov rdx, -0x2 
inc rdx
adox r8, r10
adcx r13, r12
mov rdx, [ rsi + 0x0 ]
mulx r12, r10, [ rsi + 0x10 ]
adox r10, r9
adox r11, r12
mov rdx, 0x0 
adox rcx, rdx
dec rdx
movzx rbx, bl
adox rbx, rdx
adox r8, rdi
adox rbp, r10
adox r13, r11
mov rdx, [ rsi + 0x8 ]
mulx rbx, r9, rdx
mov rdx, [ rsi + 0x0 ]
mulx r12, rdi, [ rsi + 0x8 ]
setc dl
clc
adcx rdi, r8
mov r10, 0xffffffffffffffff 
xchg rdx, r10
mulx r8, r11, rdi
movzx r8, r10b
lea r8, [ r8 + rax ]
mov rdx, [ rsi + 0x18 ]
mulx r10, rax, [ rsi + 0x8 ]
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x28 ], r10
mov [ rsp - 0x20 ], r13
mulx r13, r10, r11
adox r8, rcx
seto cl
mov rdx, -0x2 
inc rdx
adox r9, r12
adox r14, rbx
adox rax, r15
adcx r9, rbp
adcx r14, [ rsp - 0x20 ]
adcx rax, r8
mov r15, [ rsp - 0x28 ]
mov rbp, 0x0 
adox r15, rbp
movzx rbx, cl
adcx rbx, r15
mov r12, 0xffffffffffffffff 
mov rdx, r12
mulx rcx, r12, r11
mov r8, -0x3 
inc r8
adox r12, r13
mov r13, 0xffffffff 
mov rdx, r11
mulx r15, r11, r13
adox r11, rcx
adox r15, rbp
mov rcx, -0x3 
inc rcx
adox rdx, rdi
mov rdx, [ rsi + 0x10 ]
mulx rdi, rcx, [ rsi + 0x0 ]
adox r10, r9
adox r12, r14
adox r11, rax
mov rdx, [ rsi + 0x8 ]
mulx r14, r9, [ rsi + 0x10 ]
adox r15, rbx
seto dl
mov rax, -0x3 
inc rax
adox rcx, r10
movzx rax, dl
adcx rax, rbp
clc
adcx r9, rdi
adox r9, r12
mov rdx, [ rsi + 0x10 ]
mulx rdi, rbx, rdx
adcx rbx, r14
adox rbx, r11
mov rdx, 0xffffffffffffffff 
mulx r12, r10, rcx
adcx rdi, [ rsp - 0x40 ]
mov r12, [ rsp - 0x48 ]
adcx r12, rbp
adox rdi, r15
mulx r14, r11, r10
adox r12, rax
mov r15, 0xffffffff00000000 
mov rdx, r15
mulx rax, r15, r10
mov rdx, r10
mulx rbp, r10, r13
clc
adcx r11, rax
adcx r10, r14
mov r14, rdx
mov rdx, [ rsi + 0x18 ]
mulx r8, rax, [ rsi + 0x0 ]
setc dl
clc
adcx r14, rcx
adcx r15, r9
seto r14b
mov rcx, -0x2 
inc rcx
adox rax, r15
adcx r11, rbx
adcx r10, rdi
movzx r9, dl
lea r9, [ r9 + rbp ]
adcx r9, r12
movzx rbx, r14b
mov rdi, 0x0 
adcx rbx, rdi
mov rdx, [ rsi + 0x8 ]
mulx r12, r14, [ rsi + 0x18 ]
clc
adcx r14, r8
mov rdx, [ rsi + 0x10 ]
mulx r8, rbp, [ rsi + 0x18 ]
adcx rbp, r12
adcx r8, [ rsp - 0x30 ]
mov rdx, 0xffffffffffffffff 
mulx r12, r15, rax
mov r12, [ rsp - 0x38 ]
adcx r12, rdi
mulx rcx, rdi, r15
adox r14, r11
adox rbp, r10
adox r8, r9
adox r12, rbx
mov r11, r15
clc
adcx r11, rax
mov r11, 0xffffffff00000000 
mov rdx, r15
mulx rax, r15, r11
adcx r15, r14
mulx r9, r10, r13
seto bl
mov rdx, -0x2 
inc rdx
adox rdi, rax
adcx rdi, rbp
adox r10, rcx
mov rcx, 0x0 
adox r9, rcx
adcx r10, r8
adcx r9, r12
movzx r14, bl
adc r14, 0x0
mov rbp, r15
sub rbp, 0x00000001
mov r8, rdi
sbb r8, r11
mov rbx, r10
mov r12, 0xffffffffffffffff 
sbb rbx, r12
mov rax, r9
sbb rax, r13
sbb r14, 0x00000000
cmovc r8, rdi
cmovc rax, r9
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x18 ], rax
cmovc rbp, r15
mov [ r14 + 0x0 ], rbp
mov [ r14 + 0x8 ], r8
cmovc rbx, r10
mov [ r14 + 0x10 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.4497
; seed 1016329181939556 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1146740 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=154, initial num_batches=31): 80010 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06977170064705164
; number reverted permutation / tried permutation: 70482 / 90203 =78.137%
; number reverted decision / tried decision: 60648 / 89796 =67.540%
; validated in 2.922s
