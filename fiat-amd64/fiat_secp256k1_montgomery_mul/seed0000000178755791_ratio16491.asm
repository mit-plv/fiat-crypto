SECTION .text
	GLOBAL fiat_secp256k1_montgomery_mul
fiat_secp256k1_montgomery_mul:
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x10 ]
mov rdx, [ rax + 0x8 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rbp
test al, al
adox rcx, r12
adox r10, r8
mov rdx, [ rsi + 0x18 ]
mulx r8, r14, [ rax + 0x18 ]
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x58 ], r15
mulx r15, r12, r13
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r8
mulx r8, rdi, [ rsi + 0x10 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x40 ], rdi
mov [ rsp - 0x38 ], r8
mulx r8, rdi, r13
mov r13, rdi
adcx r13, r15
seto r15b
mov rdx, -0x2 
inc rdx
adox r12, rbp
adox r13, rcx
mov r12, rdi
adcx r12, r8
adcx rdi, r8
adox r12, r10
mov rdx, [ rax + 0x18 ]
mulx rcx, rbp, [ rsi + 0x0 ]
mov rdx, 0x0 
adcx r8, rdx
clc
mov r10, -0x1 
movzx r15, r15b
adcx r15, r10
adcx r11, rbp
mov rdx, [ rax + 0x8 ]
mulx rbp, r15, [ rsi + 0x8 ]
mov rdx, 0x0 
adcx rcx, rdx
adox rdi, r11
clc
adcx r15, rbx
adox r8, rcx
seto bl
mov r11, -0x3 
inc r11
adox r9, r13
mov r13, 0xd838091dd2253531 
mov rdx, r9
mulx rcx, r9, r13
adox r15, r12
mov rcx, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, r12, [ rax + 0x10 ]
adcx r12, rbp
mov rdx, [ rsi + 0x8 ]
mulx r10, rbp, [ rax + 0x18 ]
adcx rbp, r11
mov rdx, [ rsi + 0x18 ]
mulx r13, r11, [ rax + 0x0 ]
adox r12, rdi
adox rbp, r8
mov rdx, 0x0 
adcx r10, rdx
movzx rdi, bl
adox rdi, r10
mov rdx, [ rax + 0x10 ]
mulx r8, rbx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], r11
mulx r11, r10, [ rax + 0x8 ]
clc
adcx r10, r13
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x28 ], r10
mulx r10, r13, r9
adcx rbx, r11
adcx r14, r8
seto r8b
mov r11, -0x2 
inc r11
adox r13, rcx
mov rdx, [ rsi + 0x10 ]
mulx rcx, r13, [ rax + 0x8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x20 ], r14
mulx r14, r11, r9
mov r9, r11
setc dl
clc
adcx r9, r10
mov r10, r11
adcx r10, r14
adcx r11, r14
adox r9, r15
adox r10, r12
mov r15, 0x0 
adcx r14, r15
adox r11, rbp
adox r14, rdi
movzx r12, r8b
adox r12, r15
movzx rbp, dl
add rbp, [ rsp - 0x48 ]
xor r8, r8
adox r13, [ rsp - 0x38 ]
adcx r9, [ rsp - 0x40 ]
adcx r13, r10
mov r15, 0xd838091dd2253531 
mov rdx, r15
mulx rdi, r15, r9
mov rdx, [ rax + 0x10 ]
mulx r10, rdi, [ rsi + 0x10 ]
adox rdi, rcx
mov rdx, 0xffffffffffffffff 
mulx r8, rcx, r15
adcx rdi, r11
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], rbp
mulx rbp, r11, [ rax + 0x18 ]
adox r11, r10
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x10 ], rbx
mulx rbx, r10, r15
adcx r11, r14
mov r14, 0x0 
adox rbp, r14
mov r15, rcx
mov rdx, -0x3 
inc rdx
adox r15, rbx
mov rbx, rcx
adox rbx, r8
adcx rbp, r12
setc r12b
clc
adcx r10, r9
adox rcx, r8
adcx r15, r13
adox r8, r14
mov r10, -0x3 
inc r10
adox r15, [ rsp - 0x30 ]
adcx rbx, rdi
adcx rcx, r11
adcx r8, rbp
movzx r10, r12b
adcx r10, r14
mov r9, 0xd838091dd2253531 
mov rdx, r9
mulx r13, r9, r15
mov r13, 0xfffffffefffffc2f 
mov rdx, r9
mulx rdi, r9, r13
mov r11, 0xffffffffffffffff 
mulx rbp, r12, r11
adox rbx, [ rsp - 0x28 ]
mov rdx, r12
clc
adcx rdx, rdi
adox rcx, [ rsp - 0x10 ]
mov rdi, r12
adcx rdi, rbp
adcx r12, rbp
adcx rbp, r14
adox r8, [ rsp - 0x20 ]
adox r10, [ rsp - 0x18 ]
clc
adcx r9, r15
adcx rdx, rbx
adcx rdi, rcx
adcx r12, r8
adcx rbp, r10
seto r9b
adc r9b, 0x0
movzx r9, r9b
mov r15, rdx
sub r15, r13
mov rbx, rdi
sbb rbx, r11
mov rcx, r12
sbb rcx, r11
mov r8, rbp
sbb r8, r11
movzx r10, r9b
sbb r10, 0x00000000
cmovc rcx, r12
cmovc r8, rbp
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x10 ], rcx
cmovc rbx, rdi
mov [ r10 + 0x18 ], r8
mov [ r10 + 0x8 ], rbx
cmovc r15, rdx
mov [ r10 + 0x0 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.6491
; seed 4433084880473949 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1353922 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=96, initial num_batches=31): 81710 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06035059626773182
; number reverted permutation / tried permutation: 64981 / 89992 =72.208%
; number reverted decision / tried decision: 58252 / 90007 =64.719%
; validated in 3.843s
