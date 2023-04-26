SECTION .text
	GLOBAL fiat_secp256k1_montgomery_square
fiat_secp256k1_montgomery_square:
sub rsp, 160
mov rdx, [ rsi + 0x18 ]
mulx r10, rax, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, rdx
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, r8
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x8 ]
xor rdx, rdx
adox r13, r12
mov r12, 0xfffffffefffffc2f 
mov rdx, r12
mov [ rsp - 0x58 ], r15
mulx r15, r12, rbx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r13
mulx r13, rdi, [ rsi + 0x0 ]
adcx r12, r8
setc dl
clc
adcx rdi, r9
mov r12b, dl
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x10 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x40 ], rbp
mov [ rsp - 0x38 ], rcx
mulx rcx, rbp, rbx
adcx r8, r13
mov rbx, rbp
setc r13b
clc
adcx rbx, r15
mov r15, rbp
adcx r15, rcx
adcx rbp, rcx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], r11
mov [ rsp - 0x28 ], rbp
mulx rbp, r11, rdx
mov rdx, 0x0 
adcx rcx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x20 ], rcx
mov [ rsp - 0x18 ], r15
mulx r15, rcx, [ rsi + 0x18 ]
clc
mov rdx, -0x1 
movzx r13, r13b
adcx r13, rdx
adcx r9, rcx
adox r11, r14
mov r14, 0x0 
adcx r15, r14
adox rax, rbp
adox r10, r14
mov rdx, [ rsi + 0x0 ]
mulx rbp, r13, [ rsi + 0x8 ]
add r12b, 0xFF
adcx rdi, rbx
adox r13, rdi
adcx r8, [ rsp - 0x18 ]
adcx r9, [ rsp - 0x28 ]
adcx r15, [ rsp - 0x20 ]
mov rdx, [ rsi + 0x8 ]
mulx rbx, r12, rdx
mov rdx, 0xd838091dd2253531 
mulx rdi, rcx, r13
seto dil
mov rdx, -0x3 
inc rdx
adox r12, rbp
seto bpl
dec r14
movzx rdi, dil
adox rdi, r14
adox r8, r12
mov rdx, [ rsi + 0x10 ]
mulx r12, rdi, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], r10
mulx r10, r14, [ rsi + 0x8 ]
setc dl
clc
mov [ rsp - 0x8 ], rax
mov rax, -0x1 
movzx rbp, bpl
adcx rbp, rax
adcx rbx, rdi
adox rbx, r9
mov r9b, dl
mov rdx, [ rsi + 0x0 ]
mulx rdi, rbp, [ rsi + 0x18 ]
adcx r14, r12
mov rdx, [ rsi + 0x8 ]
mulx rax, r12, [ rsi + 0x18 ]
mov rdx, 0x0 
adcx r10, rdx
adox r14, r15
clc
adcx r12, rdi
adcx rax, [ rsp - 0x30 ]
movzx r15, r9b
adox r15, r10
mov rdx, [ rsi + 0x18 ]
mulx rdi, r9, rdx
mov rdx, 0xfffffffefffffc2f 
mov [ rsp + 0x0 ], rax
mulx rax, r10, rcx
adcx r9, [ rsp - 0x38 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x8 ], r9
mov [ rsp + 0x10 ], r12
mulx r12, r9, rcx
mov rcx, 0x0 
adcx rdi, rcx
mov rdx, r9
clc
adcx rdx, rax
seto al
mov [ rsp + 0x18 ], rdi
mov rdi, -0x3 
inc rdi
adox r10, r13
mov r10, r9
adcx r10, r12
adcx r9, r12
adox rdx, r8
adcx r12, rcx
adox r10, rbx
adox r9, r14
adox r12, r15
clc
adcx rdx, [ rsp - 0x40 ]
mov r13, 0xd838091dd2253531 
mulx rbx, r8, r13
mov rbx, 0xfffffffefffffc2f 
xchg rdx, r8
mulx r15, r14, rbx
adcx r10, [ rsp - 0x48 ]
adcx r11, r9
adcx r12, [ rsp - 0x8 ]
movzx r9, al
adox r9, rcx
adcx r9, [ rsp - 0x10 ]
mov rax, -0x3 
inc rax
adox r14, r8
mov rax, 0xffffffffffffffff 
mulx r8, r14, rax
mov rdx, r14
setc dil
clc
adcx rdx, r15
mov r15, r14
adcx r15, r8
adox rdx, r10
adcx r14, r8
adcx r8, rcx
adox r15, r11
adox r14, r12
clc
adcx rbp, rdx
mov rdx, r13
mulx r10, r13, rbp
mov rdx, r13
mulx r13, r10, rbx
adcx r15, [ rsp + 0x10 ]
adox r8, r9
adcx r14, [ rsp + 0x0 ]
adcx r8, [ rsp + 0x8 ]
movzx r11, dil
adox r11, rcx
adcx r11, [ rsp + 0x18 ]
mulx rdi, r12, rax
mov r9, r12
mov rdx, -0x3 
inc rdx
adox r9, r13
mov r13, r12
adox r13, rdi
adox r12, rdi
setc dl
clc
adcx r10, rbp
adcx r9, r15
adcx r13, r14
adcx r12, r8
adox rdi, rcx
adcx rdi, r11
movzx r10, dl
adc r10, 0x0
mov rbp, r9
sub rbp, rbx
mov r15, r13
sbb r15, rax
mov r14, r12
sbb r14, rax
mov r8, rdi
sbb r8, rax
sbb r10, 0x00000000
cmovc r14, r12
cmovc r15, r13
cmovc r8, rdi
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x8 ], r15
mov [ r10 + 0x18 ], r8
mov [ r10 + 0x10 ], r14
cmovc rbp, r9
mov [ r10 + 0x0 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 160
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.6270
; seed 3812638854551674 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1329957 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=97, initial num_batches=31): 79916 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06008916077737852
; number reverted permutation / tried permutation: 66882 / 89983 =74.327%
; number reverted decision / tried decision: 58787 / 90016 =65.307%
; validated in 3.538s
