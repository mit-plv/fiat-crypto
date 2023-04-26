SECTION .text
	GLOBAL fiat_p256_square
fiat_p256_square:
sub rsp, 144
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, r8
mov [ rsp - 0x70 ], r12
mov r12, 0xffffffff 
mov rdx, r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, r8
test al, al
adox r12, rbp
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mulx r14, rbp, [ rsi + 0x18 ]
mov rdx, 0x0 
adox r13, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], rbp
mov [ rsp - 0x40 ], r13
mulx r13, rbp, [ rsi + 0x10 ]
adcx r15, r14
adcx rbp, rdi
adcx r11, r13
mov rdx, [ rsi + 0x10 ]
mulx rdi, r14, [ rsi + 0x0 ]
mov rdx, -0x2 
inc rdx
adox rax, r9
adox r14, r10
mov rdx, [ rsi + 0x0 ]
mulx r9, r10, [ rsi + 0x18 ]
adox r10, rdi
mov rdx, [ rsi + 0x8 ]
mulx rdi, r13, [ rsi + 0x10 ]
mov rdx, 0x0 
adcx rcx, rdx
adox r9, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], rcx
mov [ rsp - 0x30 ], r11
mulx r11, rcx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x28 ], rbp
mov [ rsp - 0x20 ], r15
mulx r15, rbp, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], r9
mov [ rsp - 0x10 ], r10
mulx r10, r9, [ rsi + 0x0 ]
add rcx, r15
mov rdx, -0x2 
inc rdx
adox r13, r10
mov rdx, [ rsi + 0x10 ]
mulx r10, r15, rdx
adox r15, rdi
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x8 ], r15
mulx r15, rdi, [ rsi + 0x8 ]
adcx rdi, r11
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x0 ], r13
mulx r13, r11, [ rsi + 0x8 ]
adcx r11, r15
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x8 ], r9
mulx r9, r15, [ rsi + 0x18 ]
adox r15, r10
mov rdx, 0x0 
adcx r13, rdx
adox r9, rdx
xor r10, r10
adox rbx, r8
adox r12, rax
adcx rbp, r12
adox r14, [ rsp - 0x40 ]
mov rdx, 0xffffffff00000001 
mulx rax, rbx, r8
mov r8, 0xffffffffffffffff 
mov rdx, rbp
mulx r12, rbp, r8
adcx rcx, r14
adox rbx, [ rsp - 0x10 ]
adox rax, [ rsp - 0x18 ]
adcx rdi, rbx
adcx r11, rax
mov r14, 0xffffffff 
mulx rax, rbx, r14
seto r14b
mov r8, -0x3 
inc r8
adox rbx, r12
movzx r12, r14b
adcx r12, r13
setc r13b
clc
adcx rbp, rdx
adcx rbx, rcx
adox rax, r10
mov rbp, -0x3 
inc rbp
adox rbx, [ rsp + 0x8 ]
mov rbp, 0xffffffff00000001 
mulx r14, rcx, rbp
mov rdx, 0xffffffffffffffff 
mulx r8, r10, rbx
adcx rax, rdi
adox rax, [ rsp + 0x0 ]
adcx rcx, r11
adox rcx, [ rsp - 0x8 ]
adcx r14, r12
movzx rdi, r13b
mov r11, 0x0 
adcx rdi, r11
mov r13, 0xffffffff 
mov rdx, rbx
mulx r12, rbx, r13
adox r15, r14
clc
adcx rbx, r8
adcx r12, r11
clc
adcx r10, rdx
adcx rbx, rax
adcx r12, rcx
adox r9, rdi
seto r10b
mov r8, -0x3 
inc r8
adox rbx, [ rsp - 0x48 ]
adox r12, [ rsp - 0x20 ]
mulx rcx, rax, rbp
mov rdx, rbx
mulx r14, rbx, r13
adcx rax, r15
adcx rcx, r9
adox rax, [ rsp - 0x28 ]
adox rcx, [ rsp - 0x30 ]
movzx rdi, r10b
adcx rdi, r11
mov r15, 0xffffffffffffffff 
mulx r9, r10, r15
adox rdi, [ rsp - 0x38 ]
clc
adcx rbx, r9
seto r9b
mov r8, -0x3 
inc r8
adox r10, rdx
adox rbx, r12
adcx r14, r11
adox r14, rax
mulx r12, r10, rbp
adox r10, rcx
adox r12, rdi
movzx rdx, r9b
adox rdx, r11
mov rax, rbx
sub rax, r15
mov rcx, r14
sbb rcx, r13
mov r9, r10
sbb r9, 0x00000000
mov rdi, r12
sbb rdi, rbp
sbb rdx, 0x00000000
cmovc rax, rbx
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x0 ], rax
cmovc rcx, r14
cmovc r9, r10
cmovc rdi, r12
mov [ rdx + 0x18 ], rdi
mov [ rdx + 0x8 ], rcx
mov [ rdx + 0x10 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 144
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.8198
; seed 3614002477212517 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 819103 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=231, initial num_batches=31): 70709 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.08632491884415025
; number reverted permutation / tried permutation: 76346 / 90047 =84.785%
; number reverted decision / tried decision: 60686 / 89952 =67.465%
; validated in 0.917s
