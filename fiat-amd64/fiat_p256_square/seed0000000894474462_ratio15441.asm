SECTION .text
	GLOBAL fiat_p256_square
fiat_p256_square:
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x0 ]
test al, al
adox r11, rbp
mov rdx, 0xffffffff 
mov [ rsp - 0x60 ], r14
mulx r14, rbp, rbx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], r15
mov [ rsp - 0x40 ], rdi
mulx rdi, r15, [ rsi + 0x8 ]
adcx rax, r13
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], rax
mulx rax, r13, [ rsi + 0x10 ]
adcx r13, r10
adcx r15, rax
mov rdx, 0xffffffff00000001 
mulx rax, r10, rbx
mov rdx, 0x0 
adcx rdi, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x30 ], rdi
mov [ rsp - 0x28 ], r15
mulx r15, rdi, [ rsi + 0x10 ]
adox rdi, rcx
adox r8, r15
mov rdx, 0xffffffffffffffff 
mulx r15, rcx, rbx
mov rdx, 0x0 
adox r9, rdx
mov [ rsp - 0x20 ], rax
xor rax, rax
adox rcx, rbx
adcx rbp, r15
adox rbp, r11
adcx r14, rax
adox r14, rdi
clc
adcx r12, rbp
adox r10, r8
mov rdx, 0xffffffff 
mulx rbx, rcx, r12
mov r11, 0xffffffffffffffff 
mov rdx, r12
mulx rdi, r12, r11
adcx r14, [ rsp - 0x38 ]
adcx r13, r10
adox r9, [ rsp - 0x20 ]
adcx r9, [ rsp - 0x28 ]
setc r8b
movzx r8, r8b
adox r8, [ rsp - 0x30 ]
mov r15, rdx
mov rdx, [ rsi + 0x18 ]
mulx r10, rbp, [ rsi + 0x8 ]
clc
adcx rcx, rdi
adcx rbx, rax
clc
adcx r12, r15
mov rdx, [ rsi + 0x10 ]
mulx rdi, r12, [ rsi + 0x18 ]
seto dl
mov r11, -0x3 
inc r11
adox rbp, [ rsp - 0x40 ]
adox r12, r10
adcx rcx, r14
mov r14b, dl
mov rdx, [ rsi + 0x18 ]
mulx rax, r10, rdx
adox r10, rdi
adcx rbx, r13
mov rdx, 0xffffffff00000001 
mulx rdi, r13, r15
mov rdx, [ rsi + 0x10 ]
mulx r11, r15, [ rsi + 0x8 ]
adcx r13, r9
adcx rdi, r8
mov rdx, [ rsi + 0x10 ]
mulx r8, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x18 ], r10
mov [ rsp - 0x10 ], r12
mulx r12, r10, [ rsi + 0x10 ]
mov rdx, 0x0 
adox rax, rdx
mov [ rsp - 0x8 ], rax
mov rax, -0x3 
inc rax
adox r10, rcx
setc cl
clc
adcx r15, r12
mov rdx, [ rsi + 0x10 ]
mulx rax, r12, rdx
adcx r12, r11
adcx r9, rax
mov rdx, 0x0 
adcx r8, rdx
mov r11, 0xffffffffffffffff 
mov rdx, r10
mulx rax, r10, r11
adox r15, rbx
adox r12, r13
adox r9, rdi
movzx rbx, cl
movzx r14, r14b
lea rbx, [ rbx + r14 ]
adox r8, rbx
mov r14, 0xffffffff 
mulx rcx, r13, r14
clc
adcx r10, rdx
seto r10b
mov rdi, -0x2 
inc rdi
adox r13, rax
adcx r13, r15
seto al
inc rdi
adox r13, [ rsp - 0x48 ]
movzx r15, al
lea r15, [ r15 + rcx ]
mov rbx, 0xffffffff00000001 
mulx rax, rcx, rbx
adcx r15, r12
adox rbp, r15
mov rdx, r13
mulx r12, r13, r11
adcx rcx, r9
adcx rax, r8
adox rcx, [ rsp - 0x10 ]
mulx r8, r9, r14
movzx r15, r10b
adcx r15, rdi
adox rax, [ rsp - 0x18 ]
adox r15, [ rsp - 0x8 ]
clc
adcx r9, r12
adcx r8, rdi
clc
adcx r13, rdx
adcx r9, rbp
mulx r10, r13, rbx
adcx r8, rcx
adcx r13, rax
adcx r10, r15
seto dl
adc dl, 0x0
movzx rdx, dl
mov rbp, r9
sub rbp, r11
mov r12, r8
sbb r12, r14
mov rcx, r13
sbb rcx, 0x00000000
mov rax, r10
sbb rax, rbx
movzx r15, dl
sbb r15, 0x00000000
cmovc r12, r8
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x8 ], r12
cmovc rax, r10
mov [ r15 + 0x18 ], rax
cmovc rcx, r13
cmovc rbp, r9
mov [ r15 + 0x10 ], rcx
mov [ r15 + 0x0 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.5441
; seed 1619630275387938 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1252943 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=125, initial num_batches=31): 80067 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.0639031464320404
; number reverted permutation / tried permutation: 67630 / 90082 =75.076%
; number reverted decision / tried decision: 55646 / 89917 =61.886%
; validated in 1.882s
