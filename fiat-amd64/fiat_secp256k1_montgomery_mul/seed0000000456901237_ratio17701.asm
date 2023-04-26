SECTION .text
	GLOBAL fiat_secp256k1_montgomery_mul
fiat_secp256k1_montgomery_mul:
mov rax, rdx
mov rdx, [ rdx + 0x8 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x0 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rbp
add r10, r12
mov rdx, [ rax + 0x8 ]
mulx r12, r14, [ rsi + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x0 ]
adcx rcx, r11
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x48 ], r9
mulx r9, r11, r13
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x40 ], r12
mov [ rsp - 0x38 ], r14
mulx r14, r12, r13
adcx r15, r8
mov r8, -0x2 
inc r8
adox r12, rbp
mov r12, 0x0 
adcx rdi, r12
mov rbp, r11
clc
adcx rbp, r14
mov r13, r11
adcx r13, r9
adox rbp, r10
adcx r11, r9
adox r13, rcx
adcx r9, r12
clc
adcx rbx, [ rsp - 0x38 ]
adox r11, r15
adox r9, rdi
mov rdx, [ rsi + 0x10 ]
mulx rcx, r10, [ rax + 0x10 ]
mov rdx, [ rax + 0x8 ]
mulx r15, r14, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx r12, rdi, [ rax + 0x0 ]
adcx r10, [ rsp - 0x40 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x30 ], rcx
mulx rcx, r8, [ rsi + 0x8 ]
setc dl
clc
adcx r14, r12
seto r12b
mov byte [ rsp - 0x28 ], dl
mov rdx, -0x2 
inc rdx
adox rdi, rbp
adox r14, r13
adcx r8, r15
adox r8, r11
mov rbp, 0xd838091dd2253531 
mov rdx, rbp
mulx r13, rbp, rdi
mov r13, 0xffffffffffffffff 
mov rdx, r13
mulx r11, r13, rbp
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x20 ], r10
mulx r10, r15, [ rsi + 0x8 ]
adcx r15, rcx
adox r15, r9
mov rdx, 0xfffffffefffffc2f 
mulx rcx, r9, rbp
mov rbp, r13
setc dl
clc
adcx rbp, rcx
movzx rcx, dl
lea rcx, [ rcx + r10 ]
movzx r10, r12b
adox r10, rcx
mov r12, r13
adcx r12, r11
adcx r13, r11
mov rdx, 0x0 
adcx r11, rdx
clc
adcx r9, rdi
adcx rbp, r14
adcx r12, r8
adcx r13, r15
adcx r11, r10
seto r9b
mov rdi, -0x3 
inc rdi
adox rbp, [ rsp - 0x48 ]
mov r14, 0xd838091dd2253531 
mov rdx, r14
mulx r8, r14, rbp
adox rbx, r12
mov r8, 0xfffffffefffffc2f 
mov rdx, r8
mulx r15, r8, r14
mov rcx, 0xffffffffffffffff 
mov rdx, r14
mulx r10, r14, rcx
movzx r12, r9b
mov rdx, 0x0 
adcx r12, rdx
mov r9, r14
clc
adcx r9, r15
mov rdx, [ rsi + 0x10 ]
mulx rdi, r15, [ rax + 0x18 ]
mov rdx, r14
adcx rdx, r10
adcx r14, r10
adox r13, [ rsp - 0x20 ]
setc cl
mov [ rsp - 0x18 ], r14
movzx r14, byte [ rsp - 0x28 ]
clc
mov [ rsp - 0x10 ], rdx
mov rdx, -0x1 
adcx r14, rdx
adcx r15, [ rsp - 0x30 ]
adox r15, r11
mov r14, 0x0 
adcx rdi, r14
adox rdi, r12
mov rdx, [ rsi + 0x18 ]
mulx r12, r11, [ rax + 0x8 ]
movzx rdx, cl
lea rdx, [ rdx + r10 ]
clc
adcx r8, rbp
adcx r9, rbx
adcx r13, [ rsp - 0x10 ]
adcx r15, [ rsp - 0x18 ]
adcx rdx, rdi
mov r8, rdx
mov rdx, [ rsi + 0x18 ]
mulx rbx, rbp, [ rax + 0x0 ]
seto dl
adc dl, 0x0
movzx rdx, dl
adox rbp, r9
mov r10b, dl
mov rdx, [ rax + 0x10 ]
mulx rdi, rcx, [ rsi + 0x18 ]
adcx r11, rbx
adcx rcx, r12
mov rdx, [ rsi + 0x18 ]
mulx r9, r12, [ rax + 0x18 ]
adcx r12, rdi
adcx r9, r14
adox r11, r13
adox rcx, r15
adox r12, r8
mov rdx, 0xd838091dd2253531 
mulx r15, r13, rbp
movzx r15, r10b
adox r15, r9
mov r8, 0xfffffffefffffc2f 
mov rdx, r8
mulx rbx, r8, r13
mov r10, 0xffffffffffffffff 
mov rdx, r13
mulx rdi, r13, r10
clc
adcx r8, rbp
mov r8, r13
seto bpl
mov r9, -0x3 
inc r9
adox r8, rbx
mov rdx, r13
adox rdx, rdi
adox r13, rdi
adcx r8, r11
adcx rdx, rcx
adcx r13, r12
adox rdi, r14
adcx rdi, r15
movzx r11, bpl
adc r11, 0x0
mov rcx, r8
mov r12, 0xfffffffefffffc2f 
sub rcx, r12
mov rbp, rdx
sbb rbp, r10
mov r15, r13
sbb r15, r10
mov rbx, rdi
sbb rbx, r10
sbb r11, 0x00000000
cmovc rbx, rdi
cmovc rbp, rdx
cmovc r15, r13
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x10 ], r15
mov [ r11 + 0x8 ], rbp
cmovc rcx, r8
mov [ r11 + 0x0 ], rcx
mov [ r11 + 0x18 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.7701
; seed 3458714380328221 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1797055 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=185, initial num_batches=31): 141735 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.0788707079082165
; number reverted permutation / tried permutation: 64753 / 89831 =72.083%
; number reverted decision / tried decision: 58745 / 90168 =65.151%
; validated in 4.992s
