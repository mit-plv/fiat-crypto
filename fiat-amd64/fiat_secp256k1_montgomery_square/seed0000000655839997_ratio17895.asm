SECTION .text
	GLOBAL fiat_secp256k1_montgomery_square
fiat_secp256k1_montgomery_square:
mov rdx, [ rsi + 0x10 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x8 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, r11
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x10 ]
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r12
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], r14
mov [ rsp - 0x40 ], r13
mulx r13, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], r14
mov [ rsp - 0x30 ], r13
mulx r13, r14, [ rsi + 0x0 ]
add r8, rcx
adcx rax, r9
adcx r14, r10
mov rdx, 0xffffffffffffffff 
mulx rcx, r10, r12
adc r13, 0x0
mov r9, r10
add r9, rdi
mov r12, r10
adcx r12, rcx
adcx r10, rcx
mov rdi, -0x2 
inc rdi
adox r15, r11
adox r9, r8
mov r15, 0x0 
adcx rcx, r15
adox r12, rax
adox r10, r14
mov rdx, [ rsi + 0x8 ]
mulx r8, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mulx r14, rax, rdx
clc
adcx rbx, r9
adox rcx, r13
seto dl
mov r13, -0x3 
inc r13
adox rax, rbp
adcx rax, r12
adox r11, r14
mov bpl, dl
mov rdx, [ rsi + 0x8 ]
mulx r12, r9, [ rsi + 0x18 ]
adox r9, r8
adox r12, r15
mov rdx, 0xd838091dd2253531 
mulx r14, r8, rbx
adcx r11, r10
mov r14, 0xffffffffffffffff 
mov rdx, r14
mulx r10, r14, r8
mov r15, 0xfffffffefffffc2f 
mov rdx, r15
mulx r13, r15, r8
mov r8, r14
inc rdi
adox r8, r13
adcx r9, rcx
movzx rcx, bpl
adcx rcx, r12
setc bpl
clc
adcx r15, rbx
adcx r8, rax
mov r15, r14
adox r15, r10
adcx r15, r11
adox r14, r10
adox r10, rdi
adcx r14, r9
adcx r10, rcx
mov rdx, [ rsi + 0x10 ]
mulx rax, rbx, rdx
movzx rdx, bpl
adc rdx, 0x0
mov r12, rdx
mov rdx, [ rsi + 0x10 ]
mulx r13, r11, [ rsi + 0x8 ]
test al, al
adox r8, [ rsp - 0x40 ]
mov rdx, 0xd838091dd2253531 
mulx rbp, r9, r8
adcx r11, [ rsp - 0x48 ]
adox r11, r15
mov rdx, [ rsi + 0x8 ]
mulx rcx, rbp, [ rsi + 0x18 ]
adcx rbx, r13
mov rdx, [ rsi + 0x10 ]
mulx r13, r15, [ rsi + 0x18 ]
adox rbx, r14
mov rdx, 0xfffffffefffffc2f 
mulx rdi, r14, r9
adcx r15, rax
adox r15, r10
mov r10, 0x0 
adcx r13, r10
adox r13, r12
mov rax, 0xffffffffffffffff 
mov rdx, r9
mulx r12, r9, rax
clc
adcx rbp, [ rsp - 0x30 ]
mov rdx, [ rsi + 0x10 ]
mulx rax, r10, [ rsi + 0x18 ]
adcx r10, rcx
mov rdx, r9
seto cl
mov [ rsp - 0x28 ], r10
mov r10, -0x2 
inc r10
adox rdx, rdi
mov rdi, rdx
mov rdx, [ rsi + 0x18 ]
mov byte [ rsp - 0x20 ], cl
mulx rcx, r10, rdx
adcx r10, rax
seto dl
mov rax, -0x2 
inc rax
adox r14, r8
mov r14, 0x0 
adcx rcx, r14
adox rdi, r11
mov r8, r12
clc
movzx rdx, dl
adcx rdx, rax
adcx r8, r9
adcx r9, r12
adox r8, rbx
adox r9, r15
adcx r12, r14
clc
adcx rdi, [ rsp - 0x38 ]
adox r12, r13
mov r11, 0xd838091dd2253531 
mov rdx, r11
mulx rbx, r11, rdi
mov rbx, 0xfffffffefffffc2f 
mov rdx, r11
mulx r15, r11, rbx
adcx rbp, r8
adcx r9, [ rsp - 0x28 ]
movzx r13, byte [ rsp - 0x20 ]
adox r13, r14
adcx r10, r12
adcx rcx, r13
mov r8, 0xffffffffffffffff 
mulx r13, r12, r8
mov rdx, r12
mov rax, -0x3 
inc rax
adox rdx, r15
mov r15, r12
adox r15, r13
adox r12, r13
setc al
clc
adcx r11, rdi
adcx rdx, rbp
adcx r15, r9
adox r13, r14
adcx r12, r10
adcx r13, rcx
movzx r11, al
adc r11, 0x0
mov rdi, rdx
sub rdi, rbx
mov rbp, r15
sbb rbp, r8
mov r9, r12
sbb r9, r8
mov r10, r13
sbb r10, r8
sbb r11, 0x00000000
cmovc r10, r13
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x18 ], r10
cmovc r9, r12
mov [ r11 + 0x10 ], r9
cmovc rdi, rdx
mov [ r11 + 0x0 ], rdi
cmovc rbp, r15
mov [ r11 + 0x8 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.7895
; seed 3893646313374401 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1962193 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=94, initial num_batches=31): 121890 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06211927165166729
; number reverted permutation / tried permutation: 64728 / 89885 =72.012%
; number reverted decision / tried decision: 57730 / 90114 =64.063%
; validated in 3.641s
