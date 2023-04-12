SECTION .text
	GLOBAL fiat_p224_square
fiat_p224_square:
sub rsp, 152
mov rdx, [ rsi + 0x18 ]
mulx r10, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x18 ]
test al, al
adox rax, rbp
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rdx
adox rbp, r10
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x58 ], r15
mulx r15, r10, r13
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, rdx
mov rdx, 0xffffffff 
mov [ rsp - 0x48 ], rbp
mov [ rsp - 0x40 ], rax
mulx rax, rbp, r10
adox r15, r12
mov r12, 0xffffffff00000000 
mov rdx, r12
mov [ rsp - 0x38 ], r15
mulx r15, r12, r10
adcx r11, r9
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x30 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
adcx r9, rcx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x28 ], r9
mulx r9, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x20 ], rcx
mov [ rsp - 0x18 ], r11
mulx r11, rcx, [ rsi + 0x10 ]
mov rdx, 0x0 
adox rdi, rdx
mov [ rsp - 0x10 ], rdi
mov rdi, -0x3 
inc rdi
adox rcx, r9
mov rdx, [ rsi + 0x10 ]
mulx rdi, r9, rdx
adox r9, r11
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x8 ], r9
mulx r9, r11, [ rsi + 0x18 ]
adox r11, rdi
mov rdx, 0x0 
adox r9, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x0 ], r9
mulx r9, rdi, [ rsi + 0x18 ]
adcx rdi, rbx
adc r9, 0x0
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x8 ], r11
mulx r11, rbx, [ rsi + 0x0 ]
xor rdx, rdx
adox rbx, r14
mov r14, r10
adcx r14, r13
adcx r12, rbx
mov rdx, [ rsi + 0x0 ]
mulx r13, r14, [ rsi + 0x10 ]
adox r14, r11
mov rdx, [ rsi + 0x0 ]
mulx rbx, r11, [ rsi + 0x18 ]
adox r11, r13
mov rdx, 0x0 
adox rbx, rdx
mov r13, 0xffffffffffffffff 
mov rdx, r13
mov [ rsp + 0x10 ], rcx
mulx rcx, r13, r10
mov r10, -0x2 
inc r10
adox r13, r15
adox rbp, rcx
mov r15, 0x0 
adox rax, r15
mov rcx, -0x3 
inc rcx
adox r8, r12
mulx r15, r12, r8
mov r15, 0xffffffff00000000 
mov rdx, r12
mulx rcx, r12, r15
adcx r13, r14
adcx rbp, r11
adox r13, [ rsp - 0x18 ]
adox rbp, [ rsp - 0x28 ]
adcx rax, rbx
adox rdi, rax
mov r14, rdx
seto r11b
inc r10
adox r14, r8
adox r12, r13
movzx r14, r11b
adcx r14, r9
mov r9, 0xffffffffffffffff 
mulx r8, rbx, r9
mov r13, 0xffffffff 
mulx r11, rax, r13
setc dl
clc
adcx rbx, rcx
adcx rax, r8
adox rbx, rbp
adcx r11, r10
adox rax, rdi
adox r11, r14
movzx rcx, dl
adox rcx, r10
add r12, [ rsp - 0x20 ]
adcx rbx, [ rsp + 0x10 ]
mov rdx, r9
mulx rbp, r9, r12
adcx rax, [ rsp - 0x8 ]
adcx r11, [ rsp + 0x8 ]
adcx rcx, [ rsp + 0x0 ]
mulx rdi, rbp, r9
mov rdx, r9
mulx r14, r9, r15
mov r8, -0x3 
inc r8
adox rbp, r14
mulx r10, r14, r13
setc r8b
clc
adcx rdx, r12
adcx r9, rbx
adox r14, rdi
adcx rbp, rax
mov rdx, 0x0 
adox r10, rdx
adcx r14, r11
adcx r10, rcx
movzx r12, r8b
adc r12, 0x0
test al, al
adox r9, [ rsp - 0x30 ]
mov rbx, 0xffffffffffffffff 
mov rdx, rbx
mulx rax, rbx, r9
adox rbp, [ rsp - 0x40 ]
mov rdx, r15
mulx r15, rax, rbx
mov r11, 0xffffffffffffffff 
mov rdx, r11
mulx r8, r11, rbx
adcx r11, r15
mov rdx, r13
mulx rcx, r13, rbx
adcx r13, r8
mov rdi, 0x0 
adcx rcx, rdi
clc
adcx rbx, r9
adox r14, [ rsp - 0x48 ]
adox r10, [ rsp - 0x38 ]
adcx rax, rbp
adcx r11, r14
adox r12, [ rsp - 0x10 ]
adcx r13, r10
adcx rcx, r12
seto bl
adc bl, 0x0
movzx rbx, bl
mov r9, rax
sub r9, 0x00000001
mov rbp, r11
mov r15, 0xffffffff00000000 
sbb rbp, r15
mov r8, r13
mov r14, 0xffffffffffffffff 
sbb r8, r14
mov r10, rcx
sbb r10, rdx
movzx r12, bl
sbb r12, 0x00000000
cmovc r10, rcx
cmovc rbp, r11
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x8 ], rbp
cmovc r8, r13
mov [ r12 + 0x10 ], r8
mov [ r12 + 0x18 ], r10
cmovc r9, rax
mov [ r12 + 0x0 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 152
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.5792
; seed 1685822895642171 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 995310 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=202, initial num_batches=31): 77035 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07739799660407311
; number reverted permutation / tried permutation: 75791 / 90328 =83.906%
; number reverted decision / tried decision: 64099 / 89671 =71.482%
; validated in 1.777s
