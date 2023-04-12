SECTION .text
	GLOBAL fiat_p224_mul
fiat_p224_mul:
mov rax, rdx
mov rdx, [ rdx + 0x8 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rax + 0x18 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, r9
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x0 ]
mov rdx, 0xffffffff 
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rbp
add r10, rbx
adcx r12, r11
mov r11, 0xffffffff00000000 
mov rdx, r11
mulx rbx, r11, rbp
adcx rcx, r13
mov r13, 0xffffffffffffffff 
mov rdx, rbp
mov [ rsp - 0x50 ], rdi
mulx rdi, rbp, r13
adc r8, 0x0
add rbp, rbx
adcx r14, rdi
adc r15, 0x0
test al, al
adox rdx, r9
adox r11, r10
adox rbp, r12
mov rdx, [ rsi + 0x8 ]
mulx r10, r9, [ rax + 0x0 ]
adox r14, rcx
mov rdx, [ rax + 0x8 ]
mulx rbx, r12, [ rsi + 0x8 ]
mov rdx, [ rax + 0x10 ]
mulx rdi, rcx, [ rsi + 0x8 ]
adox r15, r8
adcx r12, r10
mov rdx, [ rsi + 0x8 ]
mulx r10, r8, [ rax + 0x18 ]
adcx rcx, rbx
adcx r8, rdi
mov rdx, 0x0 
adcx r10, rdx
mov rdx, [ rsi + 0x10 ]
mulx rdi, rbx, [ rax + 0x0 ]
clc
adcx r9, r11
mov rdx, r13
mulx r11, r13, r9
mov [ rsp - 0x48 ], rbx
mulx rbx, r11, r13
adcx r12, rbp
adcx rcx, r14
adcx r8, r15
mov rdx, [ rax + 0x10 ]
mulx r14, rbp, [ rsi + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x40 ], r8
mulx r8, r15, [ rsi + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x38 ], rcx
mov [ rsp - 0x30 ], r12
mulx r12, rcx, [ rsi + 0x10 ]
setc dl
clc
adcx r15, rdi
movzx rdi, dl
adox rdi, r10
adcx rbp, r8
adcx rcx, r14
mov r10, 0xffffffff00000000 
mov rdx, r13
mulx r14, r13, r10
mov r8, 0xffffffff 
mov [ rsp - 0x28 ], rcx
mulx rcx, r10, r8
mov r8, 0x0 
adcx r12, r8
clc
adcx r11, r14
adcx r10, rbx
adcx rcx, r8
clc
adcx rdx, r9
adcx r13, [ rsp - 0x30 ]
adcx r11, [ rsp - 0x38 ]
seto dl
mov r9, -0x3 
inc r9
adox r13, [ rsp - 0x48 ]
adox r15, r11
adcx r10, [ rsp - 0x40 ]
adcx rcx, rdi
movzx rbx, dl
adcx rbx, r8
adox rbp, r10
adox rcx, [ rsp - 0x28 ]
mov rdx, [ rax + 0x8 ]
mulx r14, rdi, [ rsi + 0x18 ]
adox r12, rbx
mov rdx, 0xffffffffffffffff 
mulx r10, r11, r13
mov r10, r11
clc
adcx r10, r13
mulx r13, r10, r11
mov rbx, 0xffffffff00000000 
mov rdx, r11
mulx r8, r11, rbx
adcx r11, r15
seto r15b
inc r9
adox r10, r8
adcx r10, rbp
mov rbp, rdx
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, [ rax + 0x0 ]
mov rdx, 0xffffffff 
mov [ rsp - 0x20 ], r14
mulx r14, rbx, rbp
adox rbx, r13
mov rbp, 0x0 
adox r14, rbp
adcx rbx, rcx
adcx r14, r12
mov rcx, -0x3 
inc rcx
adox r8, r11
movzx r12, r15b
adcx r12, rbp
clc
adcx rdi, r9
mov r15, 0xffffffffffffffff 
mov rdx, r15
mulx r13, r15, r8
mulx r11, r13, r15
adox rdi, r10
mov rdx, [ rax + 0x10 ]
mulx r9, r10, [ rsi + 0x18 ]
adcx r10, [ rsp - 0x20 ]
adox r10, rbx
mov rdx, [ rax + 0x18 ]
mulx rbp, rbx, [ rsi + 0x18 ]
adcx rbx, r9
adox rbx, r14
mov rdx, 0x0 
adcx rbp, rdx
mov r14, r15
clc
adcx r14, r8
mov r14, 0xffffffff00000000 
mov rdx, r15
mulx r8, r15, r14
adcx r15, rdi
adox rbp, r12
seto r12b
inc rcx
adox r13, r8
mov rdi, 0xffffffff 
mulx r8, r9, rdi
adox r9, r11
adcx r13, r10
adcx r9, rbx
mov rdx, 0x0 
adox r8, rdx
adcx r8, rbp
movzx r11, r12b
adc r11, 0x0
mov r10, r15
sub r10, 0x00000001
mov rbx, r13
sbb rbx, r14
mov r12, r9
mov rbp, 0xffffffffffffffff 
sbb r12, rbp
mov rdx, r8
sbb rdx, rdi
sbb r11, 0x00000000
cmovc r10, r15
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x0 ], r10
cmovc r12, r9
cmovc rdx, r8
cmovc rbx, r13
mov [ r11 + 0x18 ], rdx
mov [ r11 + 0x8 ], rbx
mov [ r11 + 0x10 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.6031
; seed 2692315411387443 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2164927 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=99, initial num_batches=31): 130883 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06045608004334557
; number reverted permutation / tried permutation: 64719 / 89925 =71.970%
; number reverted decision / tried decision: 57508 / 90074 =63.845%
; validated in 4.167s
