SECTION .text
	GLOBAL fiat_p256_mul
fiat_p256_mul:
mov rax, rdx
mov rdx, [ rdx + 0x8 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, [ rax + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rbp
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x10 ]
mov rdx, 0xffffffff 
mov [ rsp - 0x48 ], rdi
mov [ rsp - 0x40 ], r15
mulx r15, rdi, rbp
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x38 ], rbx
mov [ rsp - 0x30 ], r9
mulx r9, rbx, [ rsi + 0x0 ]
xor rdx, rdx
adox r13, rbp
adcx rdi, r14
adcx r15, rdx
clc
adcx r10, r12
adcx rbx, r11
mov r13, 0xffffffff00000001 
mov rdx, r13
mulx r11, r13, rbp
adox rdi, r10
mov rdx, [ rsi + 0x0 ]
mulx r12, rbp, [ rax + 0x18 ]
adox r15, rbx
adcx rbp, r9
mov rdx, [ rax + 0x8 ]
mulx r9, r14, [ rsi + 0x8 ]
mov rdx, 0x0 
adcx r12, rdx
mov rdx, [ rax + 0x10 ]
mulx rbx, r10, [ rsi + 0x8 ]
clc
adcx r14, r8
adcx r10, r9
mov rdx, [ rax + 0x18 ]
mulx r9, r8, [ rsi + 0x8 ]
adox r13, rbp
adox r11, r12
adcx r8, rbx
mov rdx, 0x0 
adcx r9, rdx
clc
adcx rcx, rdi
adcx r14, r15
adcx r10, r13
mov rdi, 0xffffffff00000001 
mov rdx, rcx
mulx r15, rcx, rdi
mov rbp, 0xffffffffffffffff 
mulx rbx, r12, rbp
adcx r8, r11
seto r13b
mov r11, -0x2 
inc r11
adox r12, rdx
movzx r12, r13b
adcx r12, r9
mov r13, rdx
mov rdx, [ rax + 0x0 ]
mulx r11, r9, [ rsi + 0x10 ]
mov rdx, 0xffffffff 
mulx rdi, rbp, r13
setc r13b
clc
adcx rbp, rbx
mov rdx, [ rax + 0x10 ]
mov byte [ rsp - 0x28 ], r13b
mulx r13, rbx, [ rsi + 0x10 ]
mov rdx, 0x0 
adcx rdi, rdx
clc
adcx r11, [ rsp - 0x30 ]
adcx rbx, [ rsp - 0x38 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x20 ], rbx
mov [ rsp - 0x18 ], r11
mulx r11, rbx, [ rsi + 0x10 ]
adcx rbx, r13
adox rbp, r14
mov rdx, 0x0 
adcx r11, rdx
clc
adcx r9, rbp
mov r14, 0xffffffffffffffff 
mov rdx, r9
mulx r13, r9, r14
adox rdi, r10
adox rcx, r8
adox r15, r12
adcx rdi, [ rsp - 0x18 ]
seto r10b
mov r8, -0x2 
inc r8
adox r9, rdx
mov r9, 0xffffffff 
mulx rbp, r12, r9
setc r8b
clc
adcx r12, r13
movzx r13, r10b
movzx r9, byte [ rsp - 0x28 ]
lea r13, [ r13 + r9 ]
seto r9b
mov r10, 0x0 
dec r10
movzx r8, r8b
adox r8, r10
adox rcx, [ rsp - 0x20 ]
adox rbx, r15
adox r11, r13
mov r15, 0x0 
adcx rbp, r15
mov r8, 0xffffffff00000001 
mulx r15, r13, r8
clc
movzx r9, r9b
adcx r9, r10
adcx rdi, r12
adcx rbp, rcx
adcx r13, rbx
adcx r15, r11
mov rdx, [ rax + 0x0 ]
mulx r12, r9, [ rsi + 0x18 ]
mov rdx, [ rax + 0x18 ]
mulx rbx, rcx, [ rsi + 0x18 ]
mov rdx, [ rax + 0x8 ]
mulx r10, r11, [ rsi + 0x18 ]
setc dl
clc
adcx r9, rdi
seto dil
mov r14, -0x2 
inc r14
adox r11, r12
adox r10, [ rsp - 0x40 ]
adox rcx, [ rsp - 0x48 ]
adcx r11, rbp
adcx r10, r13
movzx rbp, dl
movzx rdi, dil
lea rbp, [ rbp + rdi ]
adcx rcx, r15
mov rdi, 0x0 
adox rbx, rdi
adcx rbx, rbp
mov r13, 0xffffffffffffffff 
mov rdx, r13
mulx r15, r13, r9
mov r12, 0xffffffff 
mov rdx, r9
mulx rbp, r9, r12
mov r14, -0x3 
inc r14
adox r9, r15
setc r15b
clc
adcx r13, rdx
adox rbp, rdi
adcx r9, r11
mulx r11, r13, r8
adcx rbp, r10
adcx r13, rcx
adcx r11, rbx
movzx rdx, r15b
adc rdx, 0x0
mov r10, r9
mov rcx, 0xffffffffffffffff 
sub r10, rcx
mov r15, rbp
sbb r15, r12
mov rbx, r13
sbb rbx, 0x00000000
mov rdi, r11
sbb rdi, r8
sbb rdx, 0x00000000
cmovc r15, rbp
cmovc rbx, r13
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x8 ], r15
cmovc rdi, r11
mov [ rdx + 0x18 ], rdi
cmovc r10, r9
mov [ rdx + 0x0 ], r10
mov [ rdx + 0x10 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.6868
; seed 1534484059402022 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1112844 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=143, initial num_batches=31): 75736 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.0680562594577497
; number reverted permutation / tried permutation: 66670 / 90086 =74.007%
; number reverted decision / tried decision: 57940 / 89913 =64.440%
; validated in 1.924s
