SECTION .text
	GLOBAL fiat_secp256k1_montgomery_square
fiat_secp256k1_montgomery_square:
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, r11
mov rbp, 0xfffffffefffffc2f 
mov rdx, rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rbx
mov [ rsp - 0x68 ], r13
xor r13, r13
adox rax, rcx
mov rcx, 0xffffffffffffffff 
mov rdx, rcx
mulx r13, rcx, rbx
mov rbx, rcx
adcx rbx, r12
mov r12, rcx
adcx r12, r13
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x10 ]
adox r14, r10
adcx rcx, r13
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, r10, [ rsi + 0x0 ]
mov rdx, 0x0 
adcx r13, rdx
clc
adcx rbp, r11
adcx rbx, rax
adox r10, r15
adox rdi, rdx
adcx r12, r14
mov rbp, -0x3 
inc rbp
adox r8, rbx
adcx rcx, r10
adcx r13, rdi
mov rdx, [ rsi + 0x8 ]
mulx rax, r11, rdx
setc dl
clc
adcx r11, r9
adox r11, r12
mov r9b, dl
mov rdx, [ rsi + 0x8 ]
mulx r14, r15, [ rsi + 0x10 ]
adcx r15, rax
mov rdx, 0xd838091dd2253531 
mulx r10, rbx, r8
mov r10, 0xfffffffefffffc2f 
mov rdx, r10
mulx rdi, r10, rbx
adox r15, rcx
mov r12, 0xffffffffffffffff 
mov rdx, r12
mulx rcx, r12, rbx
mov rax, r12
seto bl
inc rbp
adox rax, rdi
mov rdx, [ rsi + 0x18 ]
mulx rbp, rdi, [ rsi + 0x8 ]
adcx rdi, r14
mov rdx, 0x0 
adcx rbp, rdx
mov r14, r12
adox r14, rcx
adox r12, rcx
clc
adcx r10, r8
adox rcx, rdx
adcx rax, r11
dec rdx
movzx rbx, bl
adox rbx, rdx
adox r13, rdi
mov rdx, [ rsi + 0x0 ]
mulx r8, r10, [ rsi + 0x10 ]
adcx r14, r15
movzx rdx, r9b
adox rdx, rbp
adcx r12, r13
adcx rcx, rdx
seto r9b
adc r9b, 0x0
movzx r9, r9b
adox r10, rax
mov rdx, [ rsi + 0x18 ]
mulx rbx, r11, [ rsi + 0x0 ]
mov rdx, 0xd838091dd2253531 
mulx rdi, r15, r10
mov rdi, 0xfffffffefffffc2f 
mov rdx, rdi
mulx rbp, rdi, r15
mov rdx, [ rsi + 0x10 ]
mulx r13, rax, [ rsi + 0x8 ]
adcx rax, r8
adox rax, r14
mov rdx, 0xffffffffffffffff 
mulx r14, r8, r15
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], r11
mulx r11, r15, rdx
adcx r15, r13
adox r15, r12
mov rdx, [ rsi + 0x18 ]
mulx r13, r12, [ rsi + 0x10 ]
adcx r12, r11
adox r12, rcx
seto dl
mov rcx, -0x2 
inc rcx
adox rdi, r10
mov dil, dl
mov rdx, [ rsi + 0x18 ]
mulx r11, r10, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], r12
mulx r12, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], r15
mov [ rsp - 0x30 ], rax
mulx rax, r15, [ rsi + 0x18 ]
mov rdx, 0x0 
adcx r13, rdx
clc
adcx r15, rbx
adcx rcx, rax
seto bl
dec rdx
movzx r9, r9b
movzx rdi, dil
adox rdi, rdx
adox r13, r9
adcx r10, r12
mov r9, r8
seto dil
inc rdx
adox r9, rbp
mov rbp, r8
adox rbp, r14
adox r8, r14
adox r14, rdx
adc r11, 0x0
add bl, 0xFF
adcx r9, [ rsp - 0x30 ]
adox r9, [ rsp - 0x48 ]
adcx rbp, [ rsp - 0x38 ]
adcx r8, [ rsp - 0x40 ]
adcx r14, r13
movzx rbx, dil
adcx rbx, rdx
mov r12, 0xd838091dd2253531 
mov rdx, r12
mulx rax, r12, r9
mov rax, 0xfffffffefffffc2f 
mov rdx, r12
mulx r13, r12, rax
adox r15, rbp
adox rcx, r8
adox r10, r14
mov rdi, 0xffffffffffffffff 
mulx r8, rbp, rdi
adox r11, rbx
mov r14, rbp
clc
adcx r14, r13
seto bl
mov rdx, -0x2 
inc rdx
adox r12, r9
adox r14, r15
mov r12, rbp
adcx r12, r8
adox r12, rcx
adcx rbp, r8
mov r9, 0x0 
adcx r8, r9
adox rbp, r10
adox r8, r11
seto r13b
mov r15, r14
sub r15, rax
mov rcx, r12
sbb rcx, rdi
mov r10, rbp
sbb r10, rdi
mov r11, r8
sbb r11, rdi
movzx r9, r13b
movzx rbx, bl
lea r9, [ r9 + rbx ]
sbb r9, 0x00000000
cmovc r15, r14
cmovc r10, rbp
cmovc r11, r8
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x18 ], r11
cmovc rcx, r12
mov [ r9 + 0x0 ], r15
mov [ r9 + 0x8 ], rcx
mov [ r9 + 0x10 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.7409
; seed 0786023888339983 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1667474 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=189, initial num_batches=31): 135849 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.08146993596301952
; number reverted permutation / tried permutation: 65504 / 90173 =72.643%
; number reverted decision / tried decision: 56920 / 89826 =63.367%
; validated in 4.627s
