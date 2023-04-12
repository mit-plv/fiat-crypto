SECTION .text
	GLOBAL fiat_p224_square
fiat_p224_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
xor rdx, rdx
adox rbx, r9
adox r12, rbp
mov rdx, [ rsi + 0x8 ]
mulx rbp, r9, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x18 ]
adox r14, r13
adcx r9, r10
mov rdx, 0xffffffffffffffff 
mulx r13, r10, rax
mov [ rsp - 0x50 ], rdi
mulx rdi, r13, r10
mov rdx, 0x0 
adox r15, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], r15
mov [ rsp - 0x40 ], r14
mulx r14, r15, [ rsi + 0x0 ]
adcx r15, rbp
adcx r11, r14
mov rdx, 0xffffffff00000000 
mulx r14, rbp, r10
adc rcx, 0x0
mov rdx, 0xffffffff 
mov [ rsp - 0x38 ], r12
mov [ rsp - 0x30 ], rbx
mulx rbx, r12, r10
add r13, r14
mov r14, -0x2 
inc r14
adox r10, rax
adcx r12, rdi
mov r10, 0x0 
adcx rbx, r10
adox rbp, r9
adox r13, r15
adox r12, r11
mov rdx, [ rsi + 0x10 ]
mulx r9, rax, [ rsi + 0x8 ]
adox rbx, rcx
mov rdx, [ rsi + 0x0 ]
mulx r15, rdi, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, rdx
clc
adcx r11, r15
adcx rax, rcx
mov rdx, [ rsi + 0x8 ]
mulx rcx, r15, [ rsi + 0x18 ]
adcx r15, r9
adcx rcx, r10
clc
adcx rdi, rbp
adcx r11, r13
adcx rax, r12
mov rdx, 0xffffffffffffffff 
mulx r13, rbp, rdi
adcx r15, rbx
setc r13b
movzx r13, r13b
adox r13, rcx
mov rdx, [ rsi + 0x0 ]
mulx r9, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, rbx, [ rsi + 0x18 ]
clc
adcx rbx, r9
mov rdx, [ rsi + 0x10 ]
mulx r10, r9, [ rsi + 0x18 ]
adcx r9, rcx
mov rdx, [ rsi + 0x18 ]
mulx r14, rcx, rdx
adcx rcx, r10
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x28 ], rcx
mulx rcx, r10, rbp
mov rdx, 0x0 
adcx r14, rdx
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x20 ], r14
mov [ rsp - 0x18 ], r9
mulx r9, r14, rbp
mov rdx, rbp
clc
adcx rdx, rdi
mov rdx, 0xffffffff 
mov [ rsp - 0x10 ], rbx
mulx rbx, rdi, rbp
adcx r14, r11
seto r11b
mov rbp, -0x2 
inc rbp
adox r10, r9
adcx r10, rax
adox rdi, rcx
mov rax, 0x0 
adox rbx, rax
adcx rdi, r15
adcx rbx, r13
movzx r15, r11b
adc r15, 0x0
xor r13, r13
adox r8, r14
adox r10, [ rsp - 0x30 ]
mov rax, 0xffffffffffffffff 
mov rdx, r8
mulx r11, r8, rax
mov r11, r8
adcx r11, rdx
adox rdi, [ rsp - 0x38 ]
mov r11, 0xffffffff 
mov rdx, r8
mulx rcx, r8, r11
adox rbx, [ rsp - 0x40 ]
mov r9, 0xffffffff00000000 
mulx r13, r14, r9
adox r15, [ rsp - 0x48 ]
mulx r11, rbp, rax
adcx r14, r10
seto r10b
mov rdx, -0x2 
inc rdx
adox r12, r14
seto r14b
inc rdx
adox rbp, r13
adox r8, r11
adcx rbp, rdi
adox rcx, rdx
mov rdx, rax
mulx rdi, rax, r12
mov rdx, r9
mulx r9, rdi, rax
mov r13, 0xffffffffffffffff 
mov rdx, rax
mulx r11, rax, r13
adcx r8, rbx
adcx rcx, r15
movzx rbx, r10b
adc rbx, 0x0
add r14b, 0xFF
adcx rbp, [ rsp - 0x10 ]
mov r10, 0xffffffff 
mulx r14, r15, r10
adcx r8, [ rsp - 0x18 ]
adcx rcx, [ rsp - 0x28 ]
adox rax, r9
adox r15, r11
mov r9, 0x0 
adox r14, r9
mov r11, -0x3 
inc r11
adox rdx, r12
adox rdi, rbp
adcx rbx, [ rsp - 0x20 ]
adox rax, r8
adox r15, rcx
adox r14, rbx
seto dl
adc dl, 0x0
movzx rdx, dl
mov r12, rdi
sub r12, 0x00000001
mov rbp, rax
mov r8, 0xffffffff00000000 
sbb rbp, r8
mov rcx, r15
sbb rcx, r13
mov rbx, r14
sbb rbx, r10
movzx r11, dl
sbb r11, 0x00000000
cmovc rbx, r14
cmovc r12, rdi
cmovc rbp, rax
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x0 ], r12
cmovc rcx, r15
mov [ r11 + 0x10 ], rcx
mov [ r11 + 0x18 ], rbx
mov [ r11 + 0x8 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.4810
; seed 1952596488080213 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2180195 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=121, initial num_batches=31): 130932 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.060055178550542494
; number reverted permutation / tried permutation: 68018 / 89870 =75.685%
; number reverted decision / tried decision: 59986 / 90129 =66.556%
; validated in 3.383s
