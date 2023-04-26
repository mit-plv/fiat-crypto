SECTION .text
	GLOBAL fiat_p224_mul
fiat_p224_mul:
sub rsp, 136
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx r11, r10, [ rax + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, [ rax + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x10 ]
xor rdx, rdx
adox rbp, rbx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mulx r15, rbx, [ rax + 0x10 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r15
mulx r15, rdi, r9
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x40 ], rbx
mulx rbx, r15, [ rax + 0x18 ]
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x38 ], r11
mov [ rsp - 0x30 ], r10
mulx r10, r11, rdi
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x28 ], rbx
mov [ rsp - 0x20 ], r15
mulx r15, rbx, rdi
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x18 ], r14
mov [ rsp - 0x10 ], r13
mulx r13, r14, [ rax + 0x10 ]
adox r14, r12
adcx rbx, r10
mov rdx, [ rax + 0x18 ]
mulx r10, r12, [ rsi + 0x0 ]
adox r12, r13
mov rdx, 0x0 
adox r10, rdx
mov r13, rdi
mov [ rsp - 0x8 ], r8
mov r8, -0x3 
inc r8
adox r13, r9
adox r11, rbp
mov r13, 0xffffffff 
mov rdx, rdi
mulx r9, rdi, r13
adcx rdi, r15
mov rbp, 0x0 
adcx r9, rbp
clc
adcx rcx, r11
adox rbx, r14
mov rdx, 0xffffffffffffffff 
mulx r14, r15, rcx
adox rdi, r12
mov rdx, [ rsi + 0x8 ]
mulx r12, r14, [ rax + 0x10 ]
mov rdx, [ rax + 0x8 ]
mulx rbp, r11, [ rsi + 0x8 ]
adox r9, r10
seto dl
inc r8
adox r11, [ rsp - 0x8 ]
adcx r11, rbx
adox r14, rbp
adcx r14, rdi
mov r10b, dl
mov rdx, [ rax + 0x18 ]
mulx rdi, rbx, [ rsi + 0x8 ]
adox rbx, r12
mov rdx, 0x0 
adox rdi, rdx
mov r12, 0xffffffffffffffff 
mov rdx, r12
mulx rbp, r12, r15
adcx rbx, r9
mov r9, 0xffffffff00000000 
mov rdx, r15
mulx r8, r15, r9
mov r13, -0x2 
inc r13
adox r12, r8
mov r8, 0xffffffff 
mulx r9, r13, r8
adox r13, rbp
mov rbp, 0x0 
adox r9, rbp
movzx rbp, r10b
adcx rbp, rdi
mov r10, -0x2 
inc r10
adox rdx, rcx
adox r15, r11
adox r12, r14
adox r13, rbx
mov rdx, [ rax + 0x0 ]
mulx r11, rcx, [ rsi + 0x10 ]
setc dl
clc
adcx rcx, r15
adox r9, rbp
movzx r14, dl
mov rdi, 0x0 
adox r14, rdi
mov rdx, [ rax + 0x8 ]
mulx rbp, rbx, [ rsi + 0x10 ]
mov rdx, -0x3 
inc rdx
adox rbx, r11
adox rbp, [ rsp - 0x10 ]
mov r15, [ rsp - 0x20 ]
adox r15, [ rsp - 0x18 ]
mov r11, [ rsp - 0x28 ]
adox r11, rdi
mov rdi, 0xffffffffffffffff 
mov rdx, rdi
mulx r10, rdi, rcx
adcx rbx, r12
mov rdx, r8
mulx r8, r10, rdi
adcx rbp, r13
adcx r15, r9
mov r12, 0xffffffff00000000 
mov rdx, rdi
mulx r13, rdi, r12
adcx r11, r14
mov r9, rdx
mov rdx, [ rax + 0x0 ]
mulx r12, r14, [ rsi + 0x18 ]
mov rdx, r9
mov [ rsp + 0x0 ], r12
mov r12, -0x2 
inc r12
adox rdx, rcx
adox rdi, rbx
mov rdx, 0xffffffffffffffff 
mulx rbx, rcx, r9
setc r9b
clc
adcx rcx, r13
adox rcx, rbp
adcx r10, rbx
seto bpl
inc r12
adox r14, rdi
mov rdx, [ rsi + 0x18 ]
mulx rdi, r13, [ rax + 0x18 ]
adcx r8, r12
clc
mov rdx, -0x1 
movzx rbp, bpl
adcx rbp, rdx
adcx r15, r10
adcx r8, r11
movzx r11, r9b
adcx r11, r12
mov r9, [ rsp + 0x0 ]
clc
adcx r9, [ rsp - 0x30 ]
mov rbx, [ rsp - 0x38 ]
adcx rbx, [ rsp - 0x40 ]
adox r9, rcx
mov rbp, 0xffffffffffffffff 
mov rdx, rbp
mulx rcx, rbp, r14
mulx r10, rcx, rbp
adox rbx, r15
adcx r13, [ rsp - 0x48 ]
mov r15, 0xffffffff00000000 
mov rdx, rbp
mulx r12, rbp, r15
adox r13, r8
mov r8, 0x0 
adcx rdi, r8
adox rdi, r11
mov r11, rdx
clc
adcx r11, r14
adcx rbp, r9
seto r11b
mov r14, -0x3 
inc r14
adox rcx, r12
mov r9, 0xffffffff 
mulx r8, r12, r9
adcx rcx, rbx
adox r12, r10
mov rdx, 0x0 
adox r8, rdx
adcx r12, r13
adcx r8, rdi
movzx r10, r11b
adc r10, 0x0
mov rbx, rbp
sub rbx, 0x00000001
mov r13, rcx
sbb r13, r15
mov r11, r12
mov rdi, 0xffffffffffffffff 
sbb r11, rdi
mov rdx, r8
sbb rdx, r9
sbb r10, 0x00000000
cmovc rdx, r8
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x18 ], rdx
cmovc r13, rcx
mov [ r10 + 0x8 ], r13
cmovc rbx, rbp
cmovc r11, r12
mov [ r10 + 0x10 ], r11
mov [ r10 + 0x0 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 136
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.6124
; seed 1961170693819869 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1291193 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=140, initial num_batches=31): 81428 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06306415849528305
; number reverted permutation / tried permutation: 68448 / 90005 =76.049%
; number reverted decision / tried decision: 61488 / 89994 =68.325%
; validated in 3.232s
