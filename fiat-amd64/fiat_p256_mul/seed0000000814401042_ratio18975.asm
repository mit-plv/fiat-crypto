SECTION .text
	GLOBAL fiat_p256_mul
fiat_p256_mul:
sub rsp, 160
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rax + 0x10 ]
mulx r8, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], r10
mov [ rsp - 0x40 ], r13
mulx r13, r10, [ rax + 0x8 ]
add rbp, r14
adcx rcx, r12
mov rdx, -0x2 
inc rdx
adox r10, r11
mov rdx, [ rax + 0x10 ]
mulx r12, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], r10
mulx r10, r14, [ rax + 0x18 ]
adox r11, r13
adox r9, r12
mov rdx, 0x0 
adox rbx, rdx
mov rdx, [ rsi + 0x0 ]
mulx r12, r13, [ rax + 0x0 ]
adcx r14, r8
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x30 ], rbx
mulx rbx, r8, r13
adc r10, 0x0
mov rdx, 0xffffffff 
mov [ rsp - 0x28 ], r9
mov [ rsp - 0x20 ], r11
mulx r11, r9, r13
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x18 ], r10
mov [ rsp - 0x10 ], r14
mulx r14, r10, [ rax + 0x10 ]
add r15, r12
adcx r10, rdi
mov rdx, [ rsi + 0x0 ]
mulx r12, rdi, [ rax + 0x18 ]
mov rdx, -0x2 
inc rdx
adox r9, rbx
adcx rdi, r14
mov rbx, 0x0 
adcx r12, rbx
mov rdx, [ rsi + 0x10 ]
mulx rbx, r14, [ rax + 0x10 ]
mov rdx, 0x0 
adox r11, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x8 ], r12
mov [ rsp + 0x0 ], rcx
mulx rcx, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x8 ], r12
mov [ rsp + 0x10 ], rdi
mulx rdi, r12, [ rax + 0x8 ]
test al, al
adox r12, rcx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x18 ], r12
mulx r12, rcx, [ rax + 0x18 ]
adox r14, rdi
adox rcx, rbx
mov rdx, 0x0 
adox r12, rdx
mov rbx, 0xffffffff00000001 
mov rdx, rbx
mulx rdi, rbx, r13
adcx r8, r13
adcx r9, r15
mov r8, -0x2 
inc r8
adox r9, [ rsp - 0x40 ]
adcx r11, r10
adox rbp, r11
adcx rbx, [ rsp + 0x10 ]
adox rbx, [ rsp + 0x0 ]
adcx rdi, [ rsp - 0x8 ]
mov r13, 0xffffffffffffffff 
mov rdx, r9
mulx r15, r9, r13
adox rdi, [ rsp - 0x10 ]
mov r10, 0xffffffff 
mulx r8, r11, r10
setc r10b
clc
adcx r11, r15
mov r15, 0x0 
adcx r8, r15
clc
adcx r9, rdx
adcx r11, rbp
adcx r8, rbx
mov r9, 0xffffffff00000001 
mulx rbx, rbp, r9
adcx rbp, rdi
movzx r10, r10b
movzx rdx, r10b
adox rdx, [ rsp - 0x18 ]
adcx rbx, rdx
seto r10b
mov rdi, -0x3 
inc rdi
adox r11, [ rsp + 0x8 ]
adox r8, [ rsp + 0x18 ]
adox r14, rbp
adox rcx, rbx
mov rdx, r11
mulx rbp, r11, r13
mov rbx, 0xffffffff 
mulx rdi, r15, rbx
setc r9b
clc
adcx r15, rbp
movzx rbp, r9b
movzx r10, r10b
lea rbp, [ rbp + r10 ]
adox r12, rbp
mov r10, 0x0 
adcx rdi, r10
clc
adcx r11, rdx
adcx r15, r8
adcx rdi, r14
mov r11, 0xffffffff00000001 
mulx r8, r9, r11
adcx r9, rcx
adcx r8, r12
seto dl
mov r14, -0x3 
inc r14
adox r15, [ rsp - 0x48 ]
adox rdi, [ rsp - 0x38 ]
movzx rcx, dl
adcx rcx, r10
mov rdx, r13
mulx rbp, r13, r15
mov rdx, r15
mulx r12, r15, rbx
clc
adcx r15, rbp
adcx r12, r10
clc
adcx r13, rdx
adcx r15, rdi
adox r9, [ rsp - 0x20 ]
adox r8, [ rsp - 0x28 ]
adox rcx, [ rsp - 0x30 ]
mulx rdi, r13, r11
adcx r12, r9
adcx r13, r8
adcx rdi, rcx
seto dl
adc dl, 0x0
movzx rdx, dl
mov rbp, r15
mov r9, 0xffffffffffffffff 
sub rbp, r9
mov r8, r12
sbb r8, rbx
mov rcx, r13
sbb rcx, 0x00000000
mov r10, rdi
sbb r10, r11
movzx r14, dl
sbb r14, 0x00000000
cmovc rcx, r13
cmovc r8, r12
cmovc rbp, r15
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x8 ], r8
mov [ r14 + 0x10 ], rcx
cmovc r10, rdi
mov [ r14 + 0x0 ], rbp
mov [ r14 + 0x18 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 160
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.8975
; seed 0259566595013758 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 854108 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=216, initial num_batches=31): 71361 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.08355032384663298
; number reverted permutation / tried permutation: 74443 / 89913 =82.794%
; number reverted decision / tried decision: 60833 / 90086 =67.528%
; validated in 1.087s
