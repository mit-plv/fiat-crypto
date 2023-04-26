SECTION .text
	GLOBAL fiat_p224_square
fiat_p224_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rax
mov [ rsp - 0x60 ], r14
mulx r14, r13, r12
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x0 ]
xor rdx, rdx
adox r15, r10
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], rbx
mulx rbx, r10, [ rsi + 0x0 ]
adox r10, rdi
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], r9
mulx r9, rdi, [ rsi + 0x0 ]
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x38 ], r8
mov [ rsp - 0x30 ], rcx
mulx rcx, r8, r12
adcx r13, rcx
adox rdi, rbx
mov rbx, 0xffffffff 
mov rdx, rbx
mulx rcx, rbx, r12
adcx rbx, r14
mov r14, 0x0 
adcx rcx, r14
clc
adcx r12, rax
adcx r8, r15
adcx r13, r10
adox r9, r14
adcx rbx, rdi
mov rdx, [ rsi + 0x8 ]
mulx rax, r12, [ rsi + 0x0 ]
mov rdx, -0x3 
inc rdx
adox r12, r8
mov rdx, [ rsi + 0x18 ]
mulx r10, r15, [ rsi + 0x8 ]
adcx rcx, r9
mov rdx, [ rsi + 0x18 ]
mulx r8, rdi, rdx
mov rdx, 0xffffffffffffffff 
mulx r14, r9, r12
setc r14b
clc
adcx r15, rbp
adcx r11, r10
mov rdx, [ rsi + 0x8 ]
mulx r10, rbp, rdx
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x28 ], r11
mov [ rsp - 0x20 ], r15
mulx r15, r11, r9
adcx rdi, [ rsp - 0x30 ]
mov rdx, 0x0 
adcx r8, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], r8
mov [ rsp - 0x10 ], rdi
mulx rdi, r8, [ rsi + 0x8 ]
clc
adcx rbp, rax
adox rbp, r13
adcx r8, r10
adox r8, rbx
mov rdx, [ rsi + 0x8 ]
mulx rbx, r13, [ rsi + 0x18 ]
adcx r13, rdi
mov rdx, 0x0 
adcx rbx, rdx
adox r13, rcx
movzx rax, r14b
adox rax, rbx
mov r14, 0xffffffffffffffff 
mov rdx, r9
mulx rcx, r9, r14
mov r10, 0xffffffff 
mulx rbx, rdi, r10
clc
adcx r9, r15
adcx rdi, rcx
mov r15, 0x0 
adcx rbx, r15
clc
adcx rdx, r12
adcx r11, rbp
adcx r9, r8
adcx rdi, r13
mov rdx, [ rsi + 0x10 ]
mulx rbp, r12, [ rsi + 0x18 ]
adcx rbx, rax
mov rdx, [ rsi + 0x8 ]
mulx r13, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, rax, [ rsi + 0x10 ]
seto dl
mov r14, -0x3 
inc r14
adox r8, rcx
adox r13, [ rsp - 0x38 ]
adox r12, [ rsp - 0x40 ]
adox rbp, r15
movzx rcx, dl
adc rcx, 0x0
add rax, r11
mov rdx, 0xffffffffffffffff 
mulx r15, r11, rax
adcx r8, r9
mov rdx, r11
mulx r15, r11, r10
adcx r13, rdi
adcx r12, rbx
mov r9, 0xffffffff00000000 
mulx rbx, rdi, r9
mov r14, 0xffffffffffffffff 
mulx r9, r10, r14
mov r14, -0x2 
inc r14
adox r10, rbx
adcx rbp, rcx
setc cl
clc
adcx rdx, rax
adox r11, r9
mov rdx, 0x0 
adox r15, rdx
adcx rdi, r8
adcx r10, r13
mov rax, -0x3 
inc rax
adox rdi, [ rsp - 0x48 ]
adcx r11, r12
adox r10, [ rsp - 0x20 ]
mov r8, 0xffffffffffffffff 
mov rdx, r8
mulx r13, r8, rdi
adcx r15, rbp
mulx r12, r13, r8
mov rbx, 0xffffffff 
mov rdx, r8
mulx r9, r8, rbx
movzx rbp, cl
mov rax, 0x0 
adcx rbp, rax
adox r11, [ rsp - 0x28 ]
mov rcx, 0xffffffff00000000 
mulx r14, rax, rcx
adox r15, [ rsp - 0x10 ]
clc
adcx rdx, rdi
seto dl
mov rdi, -0x2 
inc rdi
adox r13, r14
adox r8, r12
adcx rax, r10
adcx r13, r11
setc r10b
clc
movzx rdx, dl
adcx rdx, rdi
adcx rbp, [ rsp - 0x18 ]
setc r12b
clc
movzx r10, r10b
adcx r10, rdi
adcx r15, r8
mov r11, 0x0 
adox r9, r11
adcx r9, rbp
movzx r14, r12b
adc r14, 0x0
mov rdx, rax
sub rdx, 0x00000001
mov r8, r13
sbb r8, rcx
mov r10, r15
mov rbp, 0xffffffffffffffff 
sbb r10, rbp
mov r12, r9
sbb r12, rbx
sbb r14, 0x00000000
cmovc r10, r15
cmovc rdx, rax
cmovc r12, r9
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x0 ], rdx
cmovc r8, r13
mov [ r14 + 0x8 ], r8
mov [ r14 + 0x18 ], r12
mov [ r14 + 0x10 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.4642
; seed 2497142193122632 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1833135 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=225, initial num_batches=31): 143113 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07807008212706647
; number reverted permutation / tried permutation: 66608 / 89908 =74.085%
; number reverted decision / tried decision: 58669 / 90091 =65.122%
; validated in 4.421s
