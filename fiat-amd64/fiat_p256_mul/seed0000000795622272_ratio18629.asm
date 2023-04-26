SECTION .text
	GLOBAL fiat_p256_mul
fiat_p256_mul:
sub rsp, 184
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mulx r8, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x18 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, r10
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x0 ]
mov rdx, 0xffffffff 
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r10
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x48 ], r13
mov [ rsp - 0x40 ], rbp
mulx rbp, r13, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], r11
mov [ rsp - 0x30 ], r8
mulx r8, r11, [ rax + 0x0 ]
add r13, r8
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x28 ], r13
mulx r13, r8, [ rsi + 0x18 ]
adcx r8, rbp
adcx r9, r13
adc rbx, 0x0
mov rdx, [ rsi + 0x10 ]
mulx r13, rbp, [ rax + 0x8 ]
add r15, r12
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x20 ], rbx
mulx rbx, r12, [ rsi + 0x10 ]
adc rdi, 0x0
xor rdx, rdx
adox rbp, rbx
adox rcx, r13
mov rdx, [ rax + 0x10 ]
mulx rbx, r13, [ rsi + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x18 ], r9
mov [ rsp - 0x10 ], r8
mulx r8, r9, [ rsi + 0x8 ]
adcx r9, r14
adcx r13, r8
mov rdx, [ rax + 0x18 ]
mulx r8, r14, [ rsi + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x8 ], r11
mov [ rsp + 0x0 ], rcx
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x8 ], rbp
mov [ rsp + 0x10 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
adcx r11, rbx
adox r14, [ rsp - 0x30 ]
mov rdx, 0x0 
adcx rcx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x18 ], r14
mulx r14, rbx, [ rax + 0x10 ]
clc
adcx rbp, [ rsp - 0x38 ]
mov rdx, 0x0 
adox r8, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x20 ], r8
mov [ rsp + 0x28 ], rcx
mulx rcx, r8, [ rsi + 0x0 ]
mov rdx, r10
mov [ rsp + 0x30 ], r11
mov r11, -0x2 
inc r11
adox rdx, [ rsp - 0x40 ]
adox r15, rbp
adcx rbx, r12
adcx r8, r14
mov rdx, 0x0 
adcx rcx, rdx
clc
adcx r15, [ rsp - 0x48 ]
adox rdi, rbx
mov r12, 0xffffffff 
mov rdx, r12
mulx r14, r12, r15
mov rbp, 0xffffffff00000001 
mov rdx, r10
mulx rbx, r10, rbp
adcx r9, rdi
adox r10, r8
adox rbx, rcx
adcx r13, r10
adcx rbx, [ rsp + 0x30 ]
mov rdx, 0xffffffffffffffff 
mulx rcx, r8, r15
seto dil
inc r11
adox r12, rcx
adox r14, r11
mov r10, -0x3 
inc r10
adox r8, r15
adox r12, r9
adox r14, r13
movzx rdi, dil
movzx r8, dil
adcx r8, [ rsp + 0x28 ]
setc r9b
clc
adcx r12, [ rsp + 0x10 ]
adcx r14, [ rsp + 0x8 ]
mov rdx, r15
mulx rdi, r15, rbp
mov rdx, 0xffffffffffffffff 
mulx rcx, r13, r12
adox r15, rbx
adox rdi, r8
adcx r15, [ rsp + 0x0 ]
adcx rdi, [ rsp + 0x18 ]
movzx rbx, r9b
adox rbx, r11
mov r9, 0xffffffff 
mov rdx, r12
mulx r8, r12, r9
adcx rbx, [ rsp + 0x20 ]
mov r10, -0x3 
inc r10
adox r13, rdx
setc r13b
clc
adcx r12, rcx
adcx r8, r11
adox r12, r14
adox r8, r15
clc
adcx r12, [ rsp - 0x8 ]
mulx rcx, r14, rbp
adox r14, rdi
adcx r8, [ rsp - 0x28 ]
mov rdx, r12
mulx r15, r12, r9
adox rcx, rbx
movzx rdi, r13b
adox rdi, r11
adcx r14, [ rsp - 0x10 ]
mov r13, 0xffffffffffffffff 
mulx r11, rbx, r13
adcx rcx, [ rsp - 0x18 ]
adcx rdi, [ rsp - 0x20 ]
inc r10
adox rbx, rdx
setc bl
clc
adcx r12, r11
mulx r10, r11, rbp
adox r12, r8
mov rdx, 0x0 
adcx r15, rdx
adox r15, r14
adox r11, rcx
adox r10, rdi
movzx r8, bl
adox r8, rdx
mov r14, r12
sub r14, r13
mov rcx, r15
sbb rcx, r9
mov rbx, r11
sbb rbx, 0x00000000
mov rdi, r10
sbb rdi, rbp
sbb r8, 0x00000000
cmovc rbx, r11
cmovc rdi, r10
cmovc r14, r12
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x0 ], r14
mov [ r8 + 0x10 ], rbx
cmovc rcx, r15
mov [ r8 + 0x8 ], rcx
mov [ r8 + 0x18 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 184
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.8629
; seed 3671492532430407 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 932299 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=184, initial num_batches=31): 71617 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.0768176303953989
; number reverted permutation / tried permutation: 75711 / 89738 =84.369%
; number reverted decision / tried decision: 62053 / 90261 =68.748%
; validated in 1.22s
