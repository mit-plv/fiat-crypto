SECTION .text
	GLOBAL fiat_p224_mul
fiat_p224_mul:
sub rsp, 208
mov rax, rdx
mov rdx, [ rdx + 0x18 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mulx r8, rcx, [ rsi + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r9
mov rdi, 0xffffffff00000000 
mov rdx, r15
mov [ rsp - 0x48 ], r8
mulx r8, r15, rdi
mov rdi, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x40 ], rcx
mov [ rsp - 0x38 ], r11
mulx r11, rcx, [ rsi + 0x8 ]
mov rdx, rdi
mov [ rsp - 0x30 ], r11
xor r11, r11
adox rdx, r9
mov rdx, 0xffffffffffffffff 
mulx r11, r9, rdi
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], rcx
mov [ rsp - 0x20 ], r11
mulx r11, rcx, [ rax + 0x18 ]
adcx r9, r8
seto dl
mov r8, -0x2 
inc r8
adox rbp, rbx
setc bl
clc
movzx rdx, dl
adcx rdx, r8
adcx rbp, r15
adox r13, r12
adcx r9, r13
adox r10, r14
mov rdx, [ rsi + 0x18 ]
mulx r14, r12, [ rax + 0x18 ]
mov rdx, 0xffffffff 
mulx r13, r15, rdi
seto dil
inc r8
mov r8, -0x1 
movzx rbx, bl
adox rbx, r8
adox r15, [ rsp - 0x20 ]
movzx rbx, dil
mov r8, [ rsp - 0x38 ]
lea rbx, [ rbx + r8 ]
mov rdx, [ rax + 0x0 ]
mulx rdi, r8, [ rsi + 0x8 ]
adcx r15, r10
mov rdx, 0x0 
adox r13, rdx
mov r10, -0x3 
inc r10
adox r8, rbp
mov rbp, 0xffffffffffffffff 
mov rdx, r8
mulx r10, r8, rbp
mov r10, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], r14
mulx r14, rbp, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x10 ], r12
mov [ rsp - 0x8 ], rbp
mulx rbp, r12, [ rsi + 0x10 ]
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x0 ], r15
mov [ rsp + 0x8 ], r9
mulx r9, r15, r8
setc dl
clc
adcx r12, r14
adcx rbp, [ rsp - 0x40 ]
mov r14b, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x10 ], rbp
mov [ rsp + 0x18 ], r12
mulx r12, rbp, [ rax + 0x18 ]
adcx rbp, [ rsp - 0x48 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x20 ], rbp
mov [ rsp + 0x28 ], r15
mulx r15, rbp, [ rsi + 0x8 ]
seto dl
mov [ rsp + 0x30 ], r9
mov r9, -0x2 
inc r9
adox rbp, rdi
adox r15, [ rsp - 0x28 ]
mov rdi, 0x0 
adcx r12, rdi
adox rcx, [ rsp - 0x30 ]
adox r11, rdi
add r14b, 0xFF
adcx rbx, r13
movzx rdx, dl
adox rdx, r9
adox rbp, [ rsp + 0x8 ]
adox r15, [ rsp + 0x0 ]
adox rcx, rbx
mov r14, 0xffffffffffffffff 
mov rdx, r14
mulx r13, r14, r8
setc bl
movzx rbx, bl
adox rbx, r11
mov r11, r8
clc
adcx r11, r10
mov r11, 0xffffffff 
mov rdx, r8
mulx r10, r8, r11
seto dl
mov r9, -0x3 
inc r9
adox r14, [ rsp + 0x30 ]
adox r8, r13
mov r13b, dl
mov rdx, [ rsi + 0x18 ]
mulx r9, rdi, [ rax + 0x10 ]
adcx rbp, [ rsp + 0x28 ]
mov rdx, 0x0 
adox r10, rdx
adcx r14, r15
mov r15, -0x3 
inc r15
adox rbp, [ rsp - 0x8 ]
adox r14, [ rsp + 0x18 ]
mov rdx, 0xffffffffffffffff 
mulx r11, r15, rbp
mov r11, 0xffffffff00000000 
mov rdx, r11
mov [ rsp + 0x38 ], r9
mulx r9, r11, r15
adcx r8, rcx
adcx r10, rbx
adox r8, [ rsp + 0x10 ]
adox r10, [ rsp + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mulx rbx, rcx, [ rax + 0x0 ]
movzx rdx, r13b
mov [ rsp + 0x40 ], rcx
mov rcx, 0x0 
adcx rdx, rcx
mov r13, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x48 ], r10
mulx r10, rcx, [ rsi + 0x18 ]
adox r12, r13
clc
adcx rcx, rbx
adcx rdi, r10
mov rdx, r15
setc bl
clc
adcx rdx, rbp
mov rdx, 0xffffffffffffffff 
mulx r13, rbp, r15
seto r10b
mov rdx, -0x2 
inc rdx
adox rbp, r9
adcx r11, r14
adcx rbp, r8
mov r14, 0xffffffff 
mov rdx, r14
mulx r9, r14, r15
adox r14, r13
adcx r14, [ rsp + 0x48 ]
mov r15, 0x0 
adox r9, r15
mov r8, -0x3 
inc r8
adox r11, [ rsp + 0x40 ]
adcx r9, r12
movzx r12, r10b
adcx r12, r15
mov r10, 0xffffffffffffffff 
mov rdx, r11
mulx r13, r11, r10
xchg rdx, r11
mulx r15, r13, r10
mov r8, [ rsp - 0x10 ]
clc
mov r10, -0x1 
movzx rbx, bl
adcx rbx, r10
adcx r8, [ rsp + 0x38 ]
mov rbx, [ rsp - 0x18 ]
mov r10, 0x0 
adcx rbx, r10
adox rcx, rbp
adox rdi, r14
adox r8, r9
mov rbp, 0xffffffff 
mulx r9, r14, rbp
adox rbx, r12
mov r12, 0xffffffff00000000 
mulx rbp, r10, r12
clc
adcx rdx, r11
adcx r10, rcx
seto dl
mov r11, -0x2 
inc r11
adox r13, rbp
adcx r13, rdi
adox r14, r15
mov r15, 0x0 
adox r9, r15
adcx r14, r8
adcx r9, rbx
movzx rcx, dl
adc rcx, 0x0
mov rdi, r10
sub rdi, 0x00000001
mov r8, r13
sbb r8, r12
mov rdx, r14
mov rbx, 0xffffffffffffffff 
sbb rdx, rbx
mov rbp, r9
mov r15, 0xffffffff 
sbb rbp, r15
sbb rcx, 0x00000000
cmovc r8, r13
cmovc rdi, r10
cmovc rdx, r14
cmovc rbp, r9
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x18 ], rbp
mov [ rcx + 0x0 ], rdi
mov [ rcx + 0x8 ], r8
mov [ rcx + 0x10 ], rdx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 208
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.3660
; seed 0783055846594993 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2208234 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=86, initial num_batches=31): 122762 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.055592840251531314
; number reverted permutation / tried permutation: 69465 / 90094 =77.103%
; number reverted decision / tried decision: 46765 / 89905 =52.016%
; validated in 3.854s
