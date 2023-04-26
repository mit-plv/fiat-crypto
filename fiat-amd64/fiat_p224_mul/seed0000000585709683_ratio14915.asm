SECTION .text
	GLOBAL fiat_p224_mul
fiat_p224_mul:
sub rsp, 200
mov rax, rdx
mov rdx, [ rdx + 0x18 ]
mulx r11, r10, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], r11
mov [ rsp - 0x40 ], r10
mulx r10, r11, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x38 ], r11
mov [ rsp - 0x30 ], r10
mulx r10, r11, [ rax + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x28 ], r8
mov [ rsp - 0x20 ], r15
mulx r15, r8, [ rsi + 0x18 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x18 ], r15
mov [ rsp - 0x10 ], r8
mulx r8, r15, r11
mov r8, r15
test al, al
adox r8, r11
mov rdx, [ rsi + 0x10 ]
mulx r11, r8, [ rax + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x8 ], r11
mov [ rsp + 0x0 ], r8
mulx r8, r11, [ rsi + 0x8 ]
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x8 ], r12
mov [ rsp + 0x10 ], rbp
mulx rbp, r12, r15
adcx r11, rdi
adcx r9, r8
adcx rcx, rbx
setc bl
clc
adcx r13, r10
adox r12, r13
mov rdx, [ rax + 0x18 ]
mulx r10, rdi, [ rsi + 0x0 ]
adcx r14, [ rsp + 0x10 ]
adcx rdi, [ rsp + 0x8 ]
mov rdx, 0x0 
adcx r10, rdx
mov r8, 0xffffffffffffffff 
mov rdx, r15
mulx r13, r15, r8
mov r8, 0xffffffff 
mov [ rsp + 0x18 ], rcx
mov byte [ rsp + 0x20 ], bl
mulx rbx, rcx, r8
clc
adcx r15, rbp
adcx rcx, r13
adox r15, r14
mov rdx, 0x0 
adcx rbx, rdx
adox rcx, rdi
clc
adcx r12, [ rsp - 0x20 ]
adcx r11, r15
adcx r9, rcx
mov rbp, 0xffffffffffffffff 
mov rdx, r12
mulx r14, r12, rbp
adox rbx, r10
mov r14, rdx
mov rdx, [ rsi + 0x10 ]
mulx r10, rdi, [ rax + 0x0 ]
movzx rdx, byte [ rsp + 0x20 ]
mov r13, [ rsp - 0x28 ]
lea rdx, [ rdx + r13 ]
mov r13, 0xffffffff00000000 
xchg rdx, r13
mulx rcx, r15, r12
adcx rbx, [ rsp + 0x18 ]
seto r8b
movzx r8, r8b
adcx r8, r13
mov rdx, [ rsi + 0x10 ]
mulx rbp, r13, [ rax + 0x10 ]
mov rdx, r12
mov [ rsp + 0x28 ], r8
mov r8, -0x2 
inc r8
adox rdx, r14
setc dl
clc
adcx r10, [ rsp + 0x0 ]
adox r15, r11
adcx r13, [ rsp - 0x8 ]
adcx rbp, [ rsp - 0x40 ]
mov r14, 0xffffffff 
xchg rdx, r14
mulx r8, r11, r12
mov rdx, [ rsp - 0x48 ]
mov byte [ rsp + 0x30 ], r14b
mov r14, 0x0 
adcx rdx, r14
mov r14, 0xffffffffffffffff 
xchg rdx, r14
mov [ rsp + 0x38 ], r14
mov [ rsp + 0x40 ], rbp
mulx rbp, r14, r12
clc
adcx r14, rcx
adcx r11, rbp
adox r14, r9
mov r9, 0x0 
adcx r8, r9
clc
adcx rdi, r15
mulx rcx, r12, rdi
mulx r15, rcx, r12
adox r11, rbx
adcx r10, r14
adox r8, [ rsp + 0x28 ]
adcx r13, r11
adcx r8, [ rsp + 0x40 ]
movzx rbx, byte [ rsp + 0x30 ]
adox rbx, r9
adcx rbx, [ rsp + 0x38 ]
mov rbp, 0xffffffff00000000 
mov rdx, rbp
mulx r14, rbp, r12
mov r11, r12
mov rdx, -0x3 
inc rdx
adox r11, rdi
setc r11b
clc
adcx rcx, r14
mov rdi, 0xffffffff 
mov rdx, rdi
mulx r14, rdi, r12
adcx rdi, r15
adox rbp, r10
adox rcx, r13
adox rdi, r8
adcx r14, r9
mov rdx, [ rax + 0x18 ]
mulx r15, r12, [ rsi + 0x18 ]
adox r14, rbx
mov rdx, [ rsi + 0x18 ]
mulx r13, r10, [ rax + 0x8 ]
clc
adcx r10, [ rsp - 0x30 ]
adcx r13, [ rsp - 0x10 ]
adcx r12, [ rsp - 0x18 ]
movzx rdx, r11b
adox rdx, r9
mov r8, -0x3 
inc r8
adox rbp, [ rsp - 0x38 ]
adox r10, rcx
mov r11, 0xffffffffffffffff 
xchg rdx, r11
mulx rcx, rbx, rbp
mov rcx, 0xffffffff00000000 
mov rdx, rbx
mulx r9, rbx, rcx
adox r13, rdi
mov rdi, 0xffffffff 
mulx rcx, r8, rdi
mov rdi, 0x0 
adcx r15, rdi
adox r12, r14
mov r14, rdx
clc
adcx r14, rbp
adox r15, r11
adcx rbx, r10
mov r14, 0xffffffffffffffff 
mulx rbp, r11, r14
seto r10b
mov rdx, -0x3 
inc rdx
adox r11, r9
adox r8, rbp
adcx r11, r13
adox rcx, rdi
adcx r8, r12
adcx rcx, r15
setc r9b
mov r13, rbx
sub r13, 0x00000001
movzx r12, r9b
movzx r10, r10b
lea r12, [ r12 + r10 ]
mov r10, r11
mov r15, 0xffffffff00000000 
sbb r10, r15
mov rbp, r8
sbb rbp, r14
mov r9, rcx
mov rdi, 0xffffffff 
sbb r9, rdi
sbb r12, 0x00000000
cmovc r10, r11
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x8 ], r10
cmovc rbp, r8
mov [ r12 + 0x10 ], rbp
cmovc r9, rcx
cmovc r13, rbx
mov [ r12 + 0x0 ], r13
mov [ r12 + 0x18 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 200
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.4915
; seed 1613813625477780 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1378569 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=118, initial num_batches=31): 81912 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.05941813576251896
; number reverted permutation / tried permutation: 65686 / 90351 =72.701%
; number reverted decision / tried decision: 46451 / 89648 =51.815%
; validated in 3.004s
