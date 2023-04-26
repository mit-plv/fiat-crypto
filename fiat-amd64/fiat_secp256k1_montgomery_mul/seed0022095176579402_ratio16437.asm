SECTION .text
	GLOBAL fiat_secp256k1_montgomery_mul
fiat_secp256k1_montgomery_mul:
sub rsp, 168
mov rax, rdx
mov rdx, [ rdx + 0x10 ]
mulx r11, r10, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x48 ], r9
mov [ rsp - 0x40 ], r11
mulx r11, r9, [ rsi + 0x8 ]
xor rdx, rdx
adox rcx, r12
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x38 ], r9
mulx r9, r12, [ rsi + 0x10 ]
adox r15, r8
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x30 ], r12
mulx r12, r8, [ rsi + 0x0 ]
adox r8, rdi
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], r8
mulx r8, rdi, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x20 ], r15
mov [ rsp - 0x18 ], rcx
mulx rcx, r15, [ rsi + 0x18 ]
adcx r13, rbx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x10 ], r13
mulx r13, rbx, [ rax + 0x10 ]
adcx r15, r14
mov rdx, 0x0 
adox r12, rdx
mov r14, -0x3 
inc r14
adox rdi, r9
adox rbx, r8
mov rdx, [ rax + 0x18 ]
mulx r8, r9, [ rsi + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x8 ], r15
mulx r15, r14, [ rsi + 0x8 ]
adox r9, r13
mov rdx, 0xd838091dd2253531 
mov [ rsp + 0x0 ], r9
mulx r9, r13, rbp
seto r9b
mov rdx, -0x2 
inc rdx
adox r14, r11
adox r10, r15
mov rdx, [ rsi + 0x18 ]
mulx r15, r11, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x8 ], rbx
mov [ rsp + 0x10 ], rdi
mulx rdi, rbx, [ rax + 0x18 ]
adox rbx, [ rsp - 0x40 ]
mov rdx, 0x0 
adox rdi, rdx
adcx r11, rcx
movzx rcx, r9b
lea rcx, [ rcx + r8 ]
adc r15, 0x0
mov r8, 0xfffffffefffffc2f 
mov rdx, r8
mulx r9, r8, r13
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x18 ], r15
mov [ rsp + 0x20 ], r11
mulx r11, r15, r13
mov r13, r15
test al, al
adox r13, r9
adcx r8, rbp
adcx r13, [ rsp - 0x18 ]
mov r8, r15
adox r8, r11
adcx r8, [ rsp - 0x20 ]
adox r15, r11
adcx r15, [ rsp - 0x28 ]
mov rbp, 0x0 
adox r11, rbp
adcx r11, r12
mov r12, -0x3 
inc r12
adox r13, [ rsp - 0x38 ]
mov r9, 0xd838091dd2253531 
mov rdx, r9
mulx rbp, r9, r13
adox r14, r8
adox r10, r15
mov rbp, 0xfffffffefffffc2f 
mov rdx, rbp
mulx r8, rbp, r9
mov r15, 0xffffffffffffffff 
mov rdx, r9
mulx r12, r9, r15
adox rbx, r11
seto r11b
mov rdx, -0x2 
inc rdx
adox rbp, r13
movzx rbp, r11b
adcx rbp, rdi
mov rdi, r9
setc r13b
clc
adcx rdi, r8
mov r8, r9
adcx r8, r12
adox rdi, r14
adox r8, r10
adcx r9, r12
adox r9, rbx
mov r14, 0x0 
adcx r12, r14
adox r12, rbp
clc
adcx rdi, [ rsp - 0x30 ]
mov r10, 0xd838091dd2253531 
mov rdx, r10
mulx r11, r10, rdi
adcx r8, [ rsp + 0x10 ]
mov r11, 0xfffffffefffffc2f 
mov rdx, r10
mulx rbx, r10, r11
movzx rbp, r13b
adox rbp, r14
mulx r14, r13, r15
mov rdx, -0x2 
inc rdx
adox r10, rdi
mov r10, r13
seto dil
inc rdx
adox r10, rbx
adcx r9, [ rsp + 0x8 ]
adcx r12, [ rsp + 0x0 ]
mov rbx, r13
adox rbx, r14
adox r13, r14
adcx rcx, rbp
adox r14, rdx
dec rdx
movzx rdi, dil
adox rdi, rdx
adox r8, r10
setc bpl
clc
adcx r8, [ rsp - 0x48 ]
adox rbx, r9
mov rdi, 0xd838091dd2253531 
mov rdx, rdi
mulx r10, rdi, r8
mov rdx, r11
mulx r11, r10, rdi
mov rdx, rdi
mulx r9, rdi, r15
adox r13, r12
adcx rbx, [ rsp - 0x10 ]
adox r14, rcx
adcx r13, [ rsp - 0x8 ]
adcx r14, [ rsp + 0x20 ]
movzx r12, bpl
mov rcx, 0x0 
adox r12, rcx
adcx r12, [ rsp + 0x18 ]
mov rbp, rdi
mov rdx, -0x3 
inc rdx
adox rbp, r11
mov r11, rdi
adox r11, r9
adox rdi, r9
setc dl
clc
adcx r10, r8
adcx rbp, rbx
adcx r11, r13
adcx rdi, r14
adox r9, rcx
setc r10b
mov r8, rbp
mov rbx, 0xfffffffefffffc2f 
sub r8, rbx
mov r13, r11
sbb r13, r15
mov r14, rdi
sbb r14, r15
dec rcx
movzx r10, r10b
adox r10, rcx
adox r12, r9
movzx r10, dl
mov r9, 0x0 
adox r10, r9
mov rdx, r12
sbb rdx, r15
sbb r10, 0x00000000
cmovc r13, r11
cmovc r8, rbp
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x8 ], r13
mov [ r10 + 0x0 ], r8
cmovc rdx, r12
mov [ r10 + 0x18 ], rdx
cmovc r14, rdi
mov [ r10 + 0x10 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 168
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.6437
; seed 0022095176579402 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 9240 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=96, initial num_batches=31): 501 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.05422077922077922
; number reverted permutation / tried permutation: 398 / 513 =77.583%
; number reverted decision / tried decision: 353 / 486 =72.634%
; validated in 3.841s
