SECTION .text
	GLOBAL fiat_secp256k1_montgomery_square
fiat_secp256k1_montgomery_square:
sub rsp, 168
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r11
mulx r11, rdi, [ rsi + 0x0 ]
xor rdx, rdx
adox r14, r11
adox rbx, r15
adcx r8, rcx
mov rdx, [ rsi + 0x8 ]
mulx r15, rcx, [ rsi + 0x18 ]
adox rcx, rbp
mov rdx, [ rsi + 0x0 ]
mulx r11, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], r8
mov [ rsp - 0x38 ], rbp
mulx rbp, r8, rdx
mov rdx, 0x0 
adox r15, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], r15
mov [ rsp - 0x28 ], rcx
mulx rcx, r15, [ rsi + 0x18 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x20 ], rbx
mov [ rsp - 0x18 ], r14
mulx r14, rbx, r12
adcx r15, r9
mov rdx, [ rsi + 0x10 ]
mulx r9, r14, [ rsi + 0x8 ]
adcx r8, rcx
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x10 ], r8
mulx r8, rcx, rbx
adc rbp, 0x0
xor rdx, rdx
adox r14, r11
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x8 ], rbp
mulx rbp, r11, [ rsi + 0x0 ]
adcx r11, r13
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x0 ], r15
mulx r15, r13, rdx
adox r13, r9
adcx rax, rbp
mov rdx, [ rsi + 0x18 ]
mulx rbp, r9, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x8 ], r13
mov [ rsp + 0x10 ], r14
mulx r14, r13, [ rsi + 0x18 ]
adox r13, r15
adcx r9, r10
mov rdx, 0xffffffffffffffff 
mulx r15, r10, rbx
mov rbx, 0x0 
adcx rbp, rbx
mov rdx, r10
clc
adcx rdx, r8
mov r8, r10
adcx r8, r15
adcx r10, r15
mov [ rsp + 0x18 ], r13
seto r13b
mov [ rsp + 0x20 ], rbp
mov rbp, -0x3 
inc rbp
adox rcx, r12
adcx r15, rbx
adox rdx, r11
clc
adcx rdi, rdx
movzx rcx, r13b
lea rcx, [ rcx + r14 ]
adox r8, rax
mov r12, 0xd838091dd2253531 
mov rdx, r12
mulx r11, r12, rdi
mov r11, 0xfffffffefffffc2f 
mov rdx, r12
mulx rax, r12, r11
adox r10, r9
adcx r8, [ rsp - 0x18 ]
adox r15, [ rsp + 0x20 ]
adcx r10, [ rsp - 0x20 ]
adcx r15, [ rsp - 0x28 ]
mov r14, 0xffffffffffffffff 
mulx r9, r13, r14
setc dl
movzx rdx, dl
adox rdx, [ rsp - 0x30 ]
mov rbp, r13
clc
adcx rbp, rax
mov rax, r13
adcx rax, r9
seto r14b
mov r11, -0x3 
inc r11
adox r12, rdi
adcx r13, r9
adox rbp, r8
setc r12b
clc
adcx rbp, [ rsp - 0x38 ]
adox rax, r10
adcx rax, [ rsp + 0x10 ]
movzx rdi, r12b
lea rdi, [ rdi + r9 ]
adox r13, r15
adox rdi, rdx
adcx r13, [ rsp + 0x8 ]
movzx r8, r14b
adox r8, rbx
adcx rdi, [ rsp + 0x18 ]
mov r10, 0xd838091dd2253531 
mov rdx, r10
mulx r15, r10, rbp
adcx rcx, r8
mov r15, 0xfffffffefffffc2f 
mov rdx, r10
mulx r9, r10, r15
mov r14, 0xffffffffffffffff 
mulx r8, r12, r14
mov rdx, -0x3 
inc rdx
adox r10, rbp
mov r10, r12
setc dl
clc
adcx r10, r9
mov rbp, r12
adcx rbp, r8
adcx r12, r8
adcx r8, rbx
adox r10, rax
clc
adcx r10, [ rsp - 0x48 ]
adox rbp, r13
adcx rbp, [ rsp - 0x40 ]
adox r12, rdi
adox r8, rcx
adcx r12, [ rsp + 0x0 ]
movzx rax, dl
adox rax, rbx
mov r13, 0xd838091dd2253531 
mov rdx, r13
mulx rdi, r13, r10
mov rdx, r13
mulx r13, rdi, r15
mulx r9, rcx, r14
mov rdx, rcx
mov r11, -0x3 
inc r11
adox rdx, r13
adcx r8, [ rsp - 0x10 ]
adcx rax, [ rsp - 0x8 ]
mov r13, rcx
adox r13, r9
adox rcx, r9
adox r9, rbx
mov r11, -0x3 
inc r11
adox rdi, r10
adox rdx, rbp
setc dil
seto r10b
mov rbp, rdx
sub rbp, r15
dec rbx
movzx r10, r10b
adox r10, rbx
adox r12, r13
adox rcx, r8
adox r9, rax
movzx r8, dil
mov rax, 0x0 
adox r8, rax
mov rdi, r12
sbb rdi, r14
mov r13, rcx
sbb r13, r14
mov r10, r9
sbb r10, r14
sbb r8, 0x00000000
cmovc rdi, r12
cmovc r13, rcx
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x10 ], r13
mov [ r8 + 0x8 ], rdi
cmovc rbp, rdx
mov [ r8 + 0x0 ], rbp
cmovc r10, r9
mov [ r8 + 0x18 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 168
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.7028
; seed 3113724269813028 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 11014 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=190, initial num_batches=31): 814 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.07390593789722172
; number reverted permutation / tried permutation: 363 / 500 =72.600%
; number reverted decision / tried decision: 326 / 499 =65.331%
; validated in 4.733s
