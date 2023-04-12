SECTION .text
	GLOBAL fiat_p256_mul
fiat_p256_mul:
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mulx r8, rcx, [ rsi + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
xor rdx, rdx
adox r9, r12
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x48 ], rdi
mulx rdi, r12, [ rsi + 0x0 ]
adox r12, rbx
adox r10, rdi
mov rdx, [ rsi + 0x8 ]
mulx rdi, rbx, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x40 ], r15
mov [ rsp - 0x38 ], r13
mulx r13, r15, [ rsi + 0x8 ]
adcx rbx, r13
adcx rcx, rdi
mov rdx, 0x0 
adox r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx r13, rdi, [ rax + 0x18 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x30 ], r14
mov [ rsp - 0x28 ], rcx
mulx rcx, r14, rbp
mov rdx, 0xffffffff 
mov [ rsp - 0x20 ], r11
mov [ rsp - 0x18 ], r10
mulx r10, r11, rbp
adcx rdi, r8
adc r13, 0x0
add r11, rcx
mov r8, -0x2 
inc r8
adox r14, rbp
mov r14, 0x0 
adcx r10, r14
adox r11, r9
clc
adcx r15, r11
mulx rcx, r9, r15
adox r10, r12
adcx rbx, r10
mov r12, 0xffffffffffffffff 
mov rdx, r12
mulx r11, r12, r15
setc r10b
clc
adcx r9, r11
mov r11, 0xffffffff00000001 
mov rdx, rbp
mulx r14, rbp, r11
adox rbp, [ rsp - 0x18 ]
adox r14, [ rsp - 0x20 ]
setc dl
clc
movzx r10, r10b
adcx r10, r8
adcx rbp, [ rsp - 0x28 ]
adcx rdi, r14
movzx r10, dl
lea r10, [ r10 + rcx ]
seto cl
inc r8
adox r12, r15
mov rdx, r11
mulx r12, r11, r15
adox r9, rbx
adox r10, rbp
adox r11, rdi
movzx r15, cl
adcx r15, r13
adox r12, r15
mov rdx, [ rsi + 0x10 ]
mulx rbx, r13, [ rax + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mulx r14, rcx, [ rax + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mulx rdi, rbp, [ rax + 0x8 ]
setc dl
clc
adcx rbp, [ rsp - 0x30 ]
adcx r13, rdi
seto r15b
mov rdi, -0x3 
inc rdi
adox r9, [ rsp - 0x38 ]
adox rbp, r10
movzx r10, r15b
movzx rdx, dl
lea r10, [ r10 + rdx ]
adox r13, r11
adcx rcx, rbx
adox rcx, r12
adcx r14, r8
mov r11, 0xffffffff 
mov rdx, r11
mulx r15, r11, r9
mov r12, 0xffffffffffffffff 
mov rdx, r12
mulx rbx, r12, r9
clc
adcx r11, rbx
adcx r15, r8
clc
adcx r12, r9
adcx r11, rbp
mov rdx, [ rax + 0x8 ]
mulx rbp, r12, [ rsi + 0x18 ]
adcx r15, r13
mov rdx, [ rax + 0x0 ]
mulx rbx, r13, [ rsi + 0x18 ]
mov rdx, 0xffffffff00000001 
mulx rdi, r8, r9
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x10 ], r15
mulx r15, r9, [ rsi + 0x18 ]
setc dl
clc
adcx r12, rbx
adox r14, r10
adcx rbp, [ rsp - 0x40 ]
adcx r9, [ rsp - 0x48 ]
setc r10b
clc
mov rbx, -0x1 
movzx rdx, dl
adcx rdx, rbx
adcx rcx, r8
seto dl
inc rbx
adox r13, r11
adcx rdi, r14
adox r12, [ rsp - 0x10 ]
adox rbp, rcx
adox r9, rdi
movzx r11, dl
adcx r11, rbx
mov r8, 0xffffffff 
mov rdx, r13
mulx r14, r13, r8
mov rcx, 0xffffffffffffffff 
mulx rbx, rdi, rcx
clc
adcx r13, rbx
movzx rbx, r10b
lea rbx, [ rbx + r15 ]
adox rbx, r11
seto r15b
mov r10, -0x2 
inc r10
adox rdi, rdx
adox r13, r12
mov rdi, 0x0 
adcx r14, rdi
adox r14, rbp
mov r12, 0xffffffff00000001 
mulx r11, rbp, r12
seto dl
mov r10, r13
sub r10, rcx
dec rdi
movzx rdx, dl
adox rdx, rdi
adox r9, rbp
adox r11, rbx
movzx rbx, r15b
mov rdx, 0x0 
adox rbx, rdx
mov r15, r14
sbb r15, r8
mov rbp, r9
sbb rbp, 0x00000000
mov rdx, r11
sbb rdx, r12
sbb rbx, 0x00000000
cmovc rbp, r9
cmovc rdx, r11
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x10 ], rbp
cmovc r15, r14
mov [ rbx + 0x18 ], rdx
mov [ rbx + 0x8 ], r15
cmovc r10, r13
mov [ rbx + 0x0 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.5764
; seed 1934505747809342 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1600061 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=213, initial num_batches=31): 134924 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.08432428513662917
; number reverted permutation / tried permutation: 66598 / 90107 =73.910%
; number reverted decision / tried decision: 54820 / 89892 =60.984%
; validated in 3.043s
