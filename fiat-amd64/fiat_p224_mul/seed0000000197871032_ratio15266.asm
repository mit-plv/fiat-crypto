SECTION .text
	GLOBAL fiat_p224_mul
fiat_p224_mul:
sub rsp, 216
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mulx r8, rcx, [ rax + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r10
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x48 ], r13
mulx r13, rdi, [ rsi + 0x18 ]
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x40 ], rdi
mov [ rsp - 0x38 ], r13
mulx r13, rdi, r15
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x30 ], r13
mov [ rsp - 0x28 ], rdi
mulx rdi, r13, [ rax + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x20 ], r8
mov [ rsp - 0x18 ], rcx
mulx rcx, r8, [ rax + 0x18 ]
xor rdx, rdx
adox r13, r11
adox r9, rdi
adox r8, rbx
mov r11, r15
adcx r11, r10
mov r11, 0xffffffff 
mov rdx, r15
mulx r10, r15, r11
seto bl
mov rdi, -0x2 
inc rdi
adox rbp, r14
adox r12, [ rsp - 0x18 ]
mov r14, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, rdi, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x10 ], r12
mov [ rsp - 0x8 ], rbp
mulx rbp, r12, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x0 ], r10
mov [ rsp + 0x8 ], r8
mulx r8, r10, [ rax + 0x0 ]
setc dl
clc
adcx rdi, r8
movzx r8, bl
lea r8, [ r8 + rcx ]
mov cl, dl
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x10 ], r8
mulx r8, rbx, [ rsi + 0x10 ]
adcx r12, r11
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x18 ], r12
mulx r12, r11, [ rax + 0x18 ]
adox rbx, [ rsp - 0x20 ]
adcx r11, rbp
mov rdx, 0x0 
adox r8, rdx
adc r12, 0x0
add cl, 0x7F
adox r13, [ rsp - 0x28 ]
mov rdx, [ rax + 0x8 ]
mulx rbp, rcx, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x20 ], r8
mov [ rsp + 0x28 ], rbx
mulx rbx, r8, [ rsi + 0x18 ]
adcx rcx, [ rsp - 0x38 ]
adcx r8, rbp
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x30 ], r8
mulx r8, rbp, [ rax + 0x18 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x38 ], rcx
mov [ rsp + 0x40 ], r12
mulx r12, rcx, r14
adcx rbp, rbx
mov r14, 0x0 
adcx r8, r14
clc
adcx rcx, [ rsp - 0x30 ]
adcx r15, r12
setc bl
clc
adcx r10, r13
mulx r12, r13, r10
mov r12, 0xffffffff00000000 
mov rdx, r13
mulx r14, r13, r12
mov r12, 0xffffffffffffffff 
mov [ rsp + 0x48 ], r8
mov [ rsp + 0x50 ], rbp
mulx rbp, r8, r12
adox rcx, r9
adox r15, [ rsp + 0x8 ]
movzx r9, bl
mov r12, [ rsp + 0x0 ]
lea r9, [ r9 + r12 ]
adcx rdi, rcx
adox r9, [ rsp + 0x10 ]
adcx r15, [ rsp + 0x18 ]
adcx r11, r9
setc r12b
movzx r12, r12b
adox r12, [ rsp + 0x40 ]
mov rbx, 0xffffffff 
mulx r9, rcx, rbx
clc
adcx r8, r14
adcx rcx, rbp
seto r14b
mov rbp, -0x2 
inc rbp
adox rdx, r10
adox r13, rdi
mov rdx, 0x0 
adcx r9, rdx
adox r8, r15
adox rcx, r11
adox r9, r12
movzx r10, r14b
adox r10, rdx
xor rdi, rdi
adox r13, [ rsp - 0x48 ]
adox r8, [ rsp - 0x8 ]
mov rdx, 0xffffffffffffffff 
mulx r11, r15, r13
adox rcx, [ rsp - 0x10 ]
adox r9, [ rsp + 0x28 ]
adox r10, [ rsp + 0x20 ]
mov r11, r15
adcx r11, r13
mov r11, 0xffffffff00000000 
mov rdx, r15
mulx r12, r15, r11
mov r14, 0xffffffffffffffff 
mulx rdi, r13, r14
adcx r15, r8
seto r8b
inc rbp
adox r13, r12
adcx r13, rcx
mulx r12, rcx, rbx
adox rcx, rdi
adcx rcx, r9
adox r12, rbp
mov rdx, -0x3 
inc rdx
adox r15, [ rsp - 0x40 ]
adox r13, [ rsp + 0x38 ]
mov rdx, r14
mulx r9, r14, r15
adcx r12, r10
movzx r9, r8b
adcx r9, rbp
mov r8, r14
clc
adcx r8, r15
adox rcx, [ rsp + 0x30 ]
mulx r10, r8, r14
adox r12, [ rsp + 0x50 ]
mov rdx, r14
mulx rdi, r14, r11
adcx r14, r13
setc r15b
clc
adcx r8, rdi
adox r9, [ rsp + 0x48 ]
mulx rdi, r13, rbx
seto dl
dec rbp
movzx r15, r15b
adox r15, rbp
adox rcx, r8
adcx r13, r10
mov r10, 0x0 
adcx rdi, r10
adox r13, r12
adox rdi, r9
movzx r12, dl
adox r12, r10
mov r15, r14
sub r15, 0x00000001
mov r8, rcx
sbb r8, r11
mov rdx, r13
mov r9, 0xffffffffffffffff 
sbb rdx, r9
mov r10, rdi
sbb r10, rbx
sbb r12, 0x00000000
cmovc r10, rdi
cmovc r15, r14
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x18 ], r10
mov [ r12 + 0x0 ], r15
cmovc rdx, r13
cmovc r8, rcx
mov [ r12 + 0x10 ], rdx
mov [ r12 + 0x8 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 216
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.5266
; seed 2446368916945389 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1505586 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=107, initial num_batches=31): 85893 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.05704954748516525
; number reverted permutation / tried permutation: 65287 / 89950 =72.581%
; number reverted decision / tried decision: 60441 / 90049 =67.120%
; validated in 3.785s
