SECTION .text
	GLOBAL fiat_secp256k1_montgomery_square
fiat_secp256k1_montgomery_square:
sub rsp, 152
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x0 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rax
add r8, r13
mov rdx, [ rsi + 0x10 ]
mulx r13, r15, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r8
mulx r8, rdi, rdx
adcx r15, r9
mov rdx, -0x2 
inc rdx
adox rdi, rbp
mov rdx, [ rsi + 0x18 ]
mulx rbp, r9, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x40 ], r15
mov [ rsp - 0x38 ], r12
mulx r12, r15, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], rdi
mov [ rsp - 0x28 ], rbx
mulx rbx, rdi, [ rsi + 0x8 ]
adox r15, r8
adox rdi, r12
mov rdx, 0x0 
adox rbx, rdx
mov rdx, [ rsi + 0x8 ]
mulx r12, r8, [ rsi + 0x0 ]
adcx r9, r13
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x20 ], r9
mulx r9, r13, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], rbx
mov [ rsp - 0x10 ], rdi
mulx rdi, rbx, [ rsi + 0x0 ]
adc rbp, 0x0
add r13, rdi
adcx r11, r9
mov rdx, [ rsi + 0x10 ]
mulx rdi, r9, [ rsi + 0x18 ]
adcx r9, rcx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x8 ], rbp
mulx rbp, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x0 ], r9
mov [ rsp + 0x8 ], r11
mulx r11, r9, [ rsi + 0x10 ]
mov rdx, -0x2 
inc rdx
adox r8, r10
mov r10, 0x0 
adcx rdi, r10
adox r9, r12
adox rcx, r11
mov r12, 0xfffffffefffffc2f 
mov rdx, r12
mulx r11, r12, r14
mov r10, 0xffffffffffffffff 
mov rdx, r14
mov [ rsp + 0x10 ], rdi
mulx rdi, r14, r10
mov rdx, 0x0 
adox rbp, rdx
add r12, rax
mov r12, r14
mov rax, -0x3 
inc rax
adox r12, r11
mov r11, r14
adox r11, rdi
adox r14, rdi
adcx r12, r8
seto r8b
mov rax, -0x3 
inc rax
adox r12, [ rsp - 0x28 ]
mov rdx, 0xd838091dd2253531 
mulx r10, rax, r12
adcx r11, r9
mov r10, 0xfffffffefffffc2f 
mov rdx, rax
mulx r9, rax, r10
adcx r14, rcx
movzx rcx, r8b
lea rcx, [ rcx + rdi ]
adcx rcx, rbp
adox r11, [ rsp - 0x30 ]
adox r15, r14
adox rcx, [ rsp - 0x10 ]
mov rdi, 0xffffffffffffffff 
mulx r8, rbp, rdi
setc dl
movzx rdx, dl
adox rdx, [ rsp - 0x18 ]
mov r14, rbp
clc
adcx r14, r9
seto r9b
mov rdi, -0x2 
inc rdi
adox rax, r12
adox r14, r11
mov rax, rbp
adcx rax, r8
adcx rbp, r8
adox rax, r15
mov r12, 0x0 
adcx r8, r12
adox rbp, rcx
adox r8, rdx
movzx r11, r9b
adox r11, r12
add rbx, r14
adcx r13, rax
mov r15, 0xd838091dd2253531 
mov rdx, r15
mulx rcx, r15, rbx
mov rdx, r15
mulx r15, rcx, r10
mov r9, -0x3 
inc r9
adox rcx, rbx
adcx rbp, [ rsp + 0x8 ]
adcx r8, [ rsp + 0x0 ]
mov rcx, 0xffffffffffffffff 
mulx rax, r14, rcx
adcx r11, [ rsp + 0x10 ]
mov rbx, r14
setc dl
clc
adcx rbx, r15
adox rbx, r13
mov r13, r14
adcx r13, rax
adox r13, rbp
adcx r14, rax
adox r14, r8
adcx rax, r12
adox rax, r11
movzx r15, dl
adox r15, r12
xor rbp, rbp
adox rbx, [ rsp - 0x38 ]
mov r12, 0xd838091dd2253531 
mov rdx, r12
mulx r8, r12, rbx
adox r13, [ rsp - 0x48 ]
adox r14, [ rsp - 0x40 ]
mov rdx, r12
mulx r12, r8, r10
mulx rbp, r11, rcx
mov rdx, r11
adcx rdx, r12
mov r12, r11
adcx r12, rbp
adox rax, [ rsp - 0x20 ]
adcx r11, rbp
adox r15, [ rsp - 0x8 ]
seto r9b
inc rdi
adox r8, rbx
adox rdx, r13
adox r12, r14
adcx rbp, rdi
adox r11, rax
adox rbp, r15
movzx r8, r9b
adox r8, rdi
mov rbx, rdx
sub rbx, r10
mov r13, r12
sbb r13, rcx
mov r14, r11
sbb r14, rcx
mov rax, rbp
sbb rax, rcx
sbb r8, 0x00000000
cmovc r13, r12
cmovc rbx, rdx
cmovc r14, r11
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x10 ], r14
cmovc rax, rbp
mov [ r8 + 0x8 ], r13
mov [ r8 + 0x0 ], rbx
mov [ r8 + 0x18 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 152
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.8318
; seed 0812501995297280 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 964604 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=171, initial num_batches=31): 72988 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07566628378070171
; number reverted permutation / tried permutation: 76878 / 90024 =85.397%
; number reverted decision / tried decision: 64995 / 89975 =72.237%
; validated in 1.942s
