SECTION .text
	GLOBAL fiat_p256_mul
fiat_p256_mul:
sub rsp, 184
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x10 ]
xor rdx, rdx
adox r9, r11
mov r11, 0xffffffffffffffff 
mov rdx, r10
mov [ rsp - 0x68 ], r13
mulx r13, r10, r11
mov [ rsp - 0x60 ], r14
mov r14, 0xffffffff 
mov [ rsp - 0x58 ], r15
mulx r11, r15, r14
adcx r15, r13
mov r13, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, r14, [ rsi + 0x0 ]
mov rdx, 0xffffffff00000001 
mov [ rsp - 0x48 ], rcx
mov [ rsp - 0x40 ], rdi
mulx rdi, rcx, r13
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], rdi
mov [ rsp - 0x30 ], rcx
mulx rcx, rdi, [ rax + 0x0 ]
setc dl
clc
adcx r10, r13
movzx r10, dl
lea r10, [ r10 + r11 ]
mov rdx, [ rax + 0x8 ]
mulx r11, r13, [ rsi + 0x18 ]
adcx r15, r9
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], rdi
mulx rdi, r9, [ rax + 0x8 ]
seto dl
mov [ rsp - 0x20 ], r10
mov r10, -0x2 
inc r10
adox r9, r8
adox rbp, rdi
mov r8b, dl
mov rdx, [ rax + 0x18 ]
mulx r10, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], rbp
mov [ rsp - 0x10 ], r9
mulx r9, rbp, [ rax + 0x10 ]
setc dl
clc
adcx r13, rcx
mov cl, dl
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x8 ], r13
mov [ rsp + 0x0 ], r14
mulx r14, r13, [ rsi + 0x18 ]
adcx rbp, r11
adcx r13, r9
mov rdx, [ rax + 0x0 ]
mulx r9, r11, [ rsi + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x8 ], r13
mov [ rsp + 0x10 ], rbp
mulx rbp, r13, [ rsi + 0x8 ]
mov rdx, 0x0 
adcx r14, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x18 ], r14
mov byte [ rsp + 0x20 ], cl
mulx rcx, r14, [ rsi + 0x8 ]
clc
adcx r13, r9
adcx r14, rbp
adox rdi, r12
mov rdx, [ rax + 0x18 ]
mulx r9, r12, [ rsi + 0x8 ]
adcx r12, rcx
mov rdx, 0x0 
adcx r9, rdx
adox r10, rdx
xor rbp, rbp
adox r11, r15
mov rdx, 0xffffffffffffffff 
mulx rcx, r15, r11
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x28 ], r10
mulx r10, rbp, [ rsi + 0x0 ]
mov rdx, -0x1 
movzx r8, r8b
adcx r8, rdx
adcx rbx, [ rsp + 0x0 ]
adcx rbp, [ rsp - 0x40 ]
mov r8, 0x0 
adcx r10, r8
mov r8, 0xffffffff 
mov rdx, r11
mov [ rsp + 0x30 ], rdi
mulx rdi, r11, r8
clc
adcx r11, rcx
mov rcx, 0x0 
adcx rdi, rcx
movzx rcx, byte [ rsp + 0x20 ]
clc
mov r8, -0x1 
adcx rcx, r8
adcx rbx, [ rsp - 0x20 ]
adcx rbp, [ rsp - 0x30 ]
adox r13, rbx
adcx r10, [ rsp - 0x38 ]
adox r14, rbp
setc cl
clc
adcx r15, rdx
adcx r11, r13
mov r15, 0xffffffff00000001 
mulx rbp, rbx, r15
adox r12, r10
movzx rdx, cl
adox rdx, r9
adcx rdi, r14
seto r9b
inc r8
adox r11, [ rsp - 0x48 ]
adox rdi, [ rsp - 0x10 ]
adcx rbx, r12
adox rbx, [ rsp - 0x18 ]
adcx rbp, rdx
movzx r13, r9b
adcx r13, r8
adox rbp, [ rsp + 0x30 ]
mov rcx, 0xffffffffffffffff 
mov rdx, rcx
mulx r10, rcx, r11
adox r13, [ rsp + 0x28 ]
clc
adcx rcx, r11
mov rcx, 0xffffffff 
mov rdx, r11
mulx r14, r11, rcx
seto r12b
mov r9, -0x3 
inc r9
adox r11, r10
adox r14, r8
adcx r11, rdi
adcx r14, rbx
mov rdi, -0x3 
inc rdi
adox r11, [ rsp - 0x28 ]
adox r14, [ rsp - 0x8 ]
mulx rbx, rdi, r15
adcx rdi, rbp
adcx rbx, r13
adox rdi, [ rsp + 0x10 ]
adox rbx, [ rsp + 0x8 ]
mov rdx, 0xffffffffffffffff 
mulx r10, rbp, r11
mov rdx, r11
mulx r13, r11, rcx
movzx r8, r12b
mov r9, 0x0 
adcx r8, r9
clc
adcx r11, r10
adcx r13, r9
clc
adcx rbp, rdx
adcx r11, r14
adcx r13, rdi
mulx r12, rbp, r15
adox r8, [ rsp + 0x18 ]
adcx rbp, rbx
adcx r12, r8
seto dl
adc dl, 0x0
movzx rdx, dl
mov r14, r11
mov rdi, 0xffffffffffffffff 
sub r14, rdi
mov rbx, r13
sbb rbx, rcx
mov r10, rbp
sbb r10, 0x00000000
mov r8, r12
sbb r8, r15
movzx r15, dl
sbb r15, 0x00000000
cmovc r10, rbp
cmovc rbx, r13
cmovc r8, r12
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x8 ], rbx
cmovc r14, r11
mov [ r15 + 0x0 ], r14
mov [ r15 + 0x18 ], r8
mov [ r15 + 0x10 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 184
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.8298
; seed 3521535126772019 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 876641 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=215, initial num_batches=31): 73273 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.08358381595202598
; number reverted permutation / tried permutation: 76038 / 90266 =84.238%
; number reverted decision / tried decision: 63305 / 89733 =70.548%
; validated in 1.065s
