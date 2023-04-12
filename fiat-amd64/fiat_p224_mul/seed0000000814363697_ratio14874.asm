SECTION .text
	GLOBAL fiat_p224_mul
fiat_p224_mul:
sub rsp, 208
mov rax, rdx
mov rdx, [ rdx + 0x8 ]
mulx r11, r10, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x48 ], r14
mov [ rsp - 0x40 ], r13
mulx r13, r14, [ rsi + 0x8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x38 ], rbp
mov [ rsp - 0x30 ], r13
mulx r13, rbp, r9
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], r14
mulx r14, r13, [ rax + 0x10 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x20 ], r14
mov [ rsp - 0x18 ], r13
mulx r13, r14, rbp
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x10 ], r13
mov [ rsp - 0x8 ], r14
mulx r14, r13, [ rax + 0x10 ]
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x0 ], r11
mov [ rsp + 0x8 ], r10
mulx r10, r11, rbp
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x10 ], r10
mov [ rsp + 0x18 ], r8
mulx r8, r10, [ rax + 0x0 ]
mov rdx, rbp
test al, al
adox rdx, r9
adcx r15, rbx
mov rdx, [ rax + 0x8 ]
mulx rbx, r9, [ rsi + 0x10 ]
adox r11, r15
seto dl
mov r15, -0x2 
inc r15
adox r9, r12
mov r12b, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x20 ], r9
mulx r9, r15, [ rax + 0x10 ]
adox r15, rbx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x28 ], r15
mulx r15, rbx, [ rsi + 0x10 ]
adcx r13, rdi
adcx rcx, r14
mov rdx, [ rax + 0x10 ]
mulx r14, rdi, [ rsi + 0x8 ]
adox rbx, r9
mov rdx, [ rsp + 0x18 ]
mov r9, 0x0 
adcx rdx, r9
clc
adcx r8, [ rsp + 0x8 ]
adcx rdi, [ rsp + 0x0 ]
adcx r14, [ rsp - 0x28 ]
adox r15, r9
mov r9, 0xffffffff 
xchg rdx, rbp
mov [ rsp + 0x30 ], r15
mov [ rsp + 0x38 ], rbx
mulx rbx, r15, r9
mov rdx, [ rsp - 0x30 ]
adc rdx, 0x0
mov r9, [ rsp + 0x10 ]
test al, al
adox r9, [ rsp - 0x8 ]
adox r15, [ rsp - 0x10 ]
adcx r10, r11
mov r11, 0x0 
adox rbx, r11
dec r11
movzx r12, r12b
adox r12, r11
adox r13, r9
adcx r8, r13
adox r15, rcx
adcx rdi, r15
adox rbx, rbp
mov r12, 0xffffffffffffffff 
xchg rdx, r12
mulx rbp, rcx, r10
mov rbp, 0xffffffff00000000 
mov rdx, rcx
mulx r9, rcx, rbp
adcx r14, rbx
mov r13, 0xffffffff 
mulx rbx, r15, r13
mov r11, rdx
seto r13b
mov rbp, -0x2 
inc rbp
adox r11, r10
mov r11, 0xffffffffffffffff 
mulx rbp, r10, r11
movzx rdx, r13b
adcx rdx, r12
setc r12b
clc
adcx r10, r9
adcx r15, rbp
mov r13, 0x0 
adcx rbx, r13
adox rcx, r8
clc
adcx rcx, [ rsp - 0x38 ]
xchg rdx, r11
mulx r9, r8, rcx
mov r9, 0xffffffff 
mov rdx, r8
mulx rbp, r8, r9
adox r10, rdi
adcx r10, [ rsp + 0x20 ]
adox r15, r14
adcx r15, [ rsp + 0x28 ]
adox rbx, r11
movzx rdi, r12b
adox rdi, r13
adcx rbx, [ rsp + 0x38 ]
mov r14, rdx
mov rdx, [ rsi + 0x18 ]
mulx r11, r12, [ rax + 0x0 ]
adcx rdi, [ rsp + 0x30 ]
mov rdx, 0xffffffff00000000 
mulx r9, r13, r14
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x40 ], r11
mov [ rsp + 0x48 ], rdi
mulx rdi, r11, r14
mov rdx, -0x2 
inc rdx
adox r11, r9
setc r9b
clc
adcx r14, rcx
adcx r13, r10
adcx r11, r15
adox r8, rdi
adcx r8, rbx
seto r14b
inc rdx
adox r12, r13
movzx rcx, r14b
lea rcx, [ rcx + rbp ]
adcx rcx, [ rsp + 0x48 ]
mov rdx, [ rax + 0x18 ]
mulx r10, rbp, [ rsi + 0x18 ]
mov rdx, 0xffffffffffffffff 
mulx rbx, r15, r12
mulx rdi, rbx, r15
movzx r13, r9b
mov r14, 0x0 
adcx r13, r14
mov r9, 0xffffffff00000000 
mov rdx, r15
mulx r14, r15, r9
mov r9, [ rsp - 0x40 ]
clc
adcx r9, [ rsp + 0x40 ]
adox r9, r11
mov r11, [ rsp - 0x48 ]
adcx r11, [ rsp - 0x18 ]
adox r11, r8
adcx rbp, [ rsp - 0x20 ]
adox rbp, rcx
mov r8, 0x0 
adcx r10, r8
adox r10, r13
clc
adcx rbx, r14
mov rcx, 0xffffffff 
mulx r14, r13, rcx
adcx r13, rdi
adcx r14, r8
clc
adcx rdx, r12
adcx r15, r9
adcx rbx, r11
adcx r13, rbp
setc dl
seto r12b
mov rdi, r15
sub rdi, 0x00000001
dec r8
movzx rdx, dl
adox rdx, r8
adox r10, r14
movzx r9, r12b
mov r11, 0x0 
adox r9, r11
mov rbp, rbx
mov r12, 0xffffffff00000000 
sbb rbp, r12
mov r14, r13
mov rdx, 0xffffffffffffffff 
sbb r14, rdx
mov r11, r10
sbb r11, rcx
sbb r9, 0x00000000
cmovc r14, r13
cmovc r11, r10
cmovc rdi, r15
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x10 ], r14
cmovc rbp, rbx
mov [ r9 + 0x18 ], r11
mov [ r9 + 0x8 ], rbp
mov [ r9 + 0x0 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 208
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.4874
; seed 0342135808811738 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1370833 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=135, initial num_batches=31): 87972 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06417411894811403
; number reverted permutation / tried permutation: 68589 / 89708 =76.458%
; number reverted decision / tried decision: 47229 / 90291 =52.308%
; validated in 2.909s
