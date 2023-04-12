SECTION .text
	GLOBAL fiat_p256_square
fiat_p256_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, 0xffffffff00000001 
mulx r9, r8, rax
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r15
mulx r15, rdi, rax
mov rdx, 0xffffffff 
mov [ rsp - 0x40 ], r14
mov [ rsp - 0x38 ], rcx
mulx rcx, r14, rax
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x30 ], r11
mov [ rsp - 0x28 ], r9
mulx r9, r11, [ rsi + 0x0 ]
xor rdx, rdx
adox rdi, rax
mov rdx, [ rsi + 0x8 ]
mulx rax, rdi, [ rsi + 0x10 ]
adcx r11, r10
adcx rbx, r9
adcx r12, rbp
mov rdx, 0x0 
adcx r13, rdx
clc
adcx r14, r15
adox r14, r11
adcx rcx, rdx
adox rcx, rbx
mov rdx, [ rsi + 0x8 ]
mulx rbp, r10, rdx
mov rdx, [ rsi + 0x0 ]
mulx r9, r15, [ rsi + 0x8 ]
clc
adcx r10, r9
adox r8, r12
adox r13, [ rsp - 0x28 ]
setc dl
clc
adcx r15, r14
seto r11b
mov rbx, -0x1 
inc rbx
mov r12, -0x1 
movzx rdx, dl
adox rdx, r12
adox rbp, rdi
adcx r10, rcx
adcx rbp, r8
mov rdx, [ rsi + 0x8 ]
mulx r14, rdi, [ rsi + 0x18 ]
adox rdi, rax
adcx rdi, r13
mov rdx, 0xffffffffffffffff 
mulx rcx, rax, r15
adox r14, rbx
mov r9, -0x3 
inc r9
adox rax, r15
mov rax, 0xffffffff 
mov rdx, rax
mulx r8, rax, r15
movzx r13, r11b
adcx r13, r14
setc r11b
clc
adcx rax, rcx
adox rax, r10
adcx r8, rbx
adox r8, rbp
mov r10, 0xffffffff00000001 
mov rdx, r15
mulx rbp, r15, r10
adox r15, rdi
adox rbp, r13
mov rdx, [ rsi + 0x0 ]
mulx rcx, rdi, [ rsi + 0x10 ]
movzx rdx, r11b
adox rdx, rbx
test al, al
adox rdi, rax
mov r14, rdx
mov rdx, [ rsi + 0x10 ]
mulx r13, r11, rdx
adcx rcx, [ rsp - 0x30 ]
mov rdx, 0xffffffffffffffff 
mulx rbx, rax, rdi
adcx r11, [ rsp - 0x38 ]
adox rcx, r8
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, [ rsi + 0x18 ]
adcx r8, r13
adox r11, r15
mov rdx, 0xffffffff 
mulx r13, r15, rdi
mov r12, 0x0 
adcx r9, r12
clc
adcx r15, rbx
adcx r13, r12
clc
adcx rax, rdi
adcx r15, rcx
mov rdx, rdi
mulx rdi, rax, r10
adox r8, rbp
adcx r13, r11
adcx rax, r8
adox r9, r14
adcx rdi, r9
seto bpl
adc bpl, 0x0
movzx rbp, bpl
mov rdx, [ rsi + 0x18 ]
mulx rbx, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mulx r11, rcx, [ rsi + 0x8 ]
adox r14, r15
mov rdx, 0xffffffff 
mulx r8, r15, r14
adcx rcx, rbx
adox rcx, r13
mov rdx, [ rsi + 0x18 ]
mulx r9, r13, [ rsi + 0x10 ]
adcx r13, r11
adox r13, rax
adcx r9, [ rsp - 0x40 ]
mov rdx, [ rsp - 0x48 ]
adcx rdx, r12
adox r9, rdi
mov rax, 0xffffffffffffffff 
xchg rdx, r14
mulx rbx, rdi, rax
clc
adcx r15, rbx
movzx r11, bpl
adox r11, r14
seto bpl
mov r14, -0x3 
inc r14
adox rdi, rdx
adox r15, rcx
adcx r8, r12
adox r8, r13
mulx rcx, rdi, r10
adox rdi, r9
adox rcx, r11
movzx rdx, bpl
adox rdx, r12
mov r13, r15
sub r13, rax
mov r9, r8
mov rbx, 0xffffffff 
sbb r9, rbx
mov rbp, rdi
sbb rbp, 0x00000000
mov r11, rcx
sbb r11, r10
sbb rdx, 0x00000000
cmovc r9, r8
cmovc r13, r15
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x0 ], r13
cmovc rbp, rdi
mov [ rdx + 0x8 ], r9
mov [ rdx + 0x10 ], rbp
cmovc r11, rcx
mov [ rdx + 0x18 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.5447
; seed 3838385892797306 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1753190 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=107, initial num_batches=31): 121012 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06902389358825911
; number reverted permutation / tried permutation: 66708 / 89790 =74.293%
; number reverted decision / tried decision: 54988 / 90209 =60.956%
; validated in 2.191s
