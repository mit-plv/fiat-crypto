SECTION .text
	GLOBAL fiat_secp256k1_montgomery_mul
fiat_secp256k1_montgomery_mul:
sub rsp, 176
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, r10
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, r9
mov [ rsp - 0x60 ], r14
xor r14, r14
adox rcx, r11
mov r11, 0xffffffffffffffff 
mov rdx, r11
mulx r14, r11, r9
mov r9, r11
adcx r9, r13
mov r13, r11
adcx r13, r14
adcx r11, r14
mov [ rsp - 0x58 ], r15
mov r15, 0x0 
adcx r14, r15
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x48 ], rdi
mov [ rsp - 0x40 ], r15
mulx r15, rdi, [ rax + 0x10 ]
clc
adcx r12, r10
adox rdi, r8
adcx r9, rcx
adcx r13, rdi
adox rbx, r15
mov rdx, [ rsi + 0x10 ]
mulx r10, r12, [ rax + 0x8 ]
mov rdx, 0x0 
adox rbp, rdx
mov rdx, [ rax + 0x0 ]
mulx rcx, r8, [ rsi + 0x10 ]
mov rdx, -0x2 
inc rdx
adox r12, rcx
mov rdx, [ rax + 0x10 ]
mulx rdi, r15, [ rsi + 0x10 ]
adcx r11, rbx
mov rdx, [ rax + 0x0 ]
mulx rcx, rbx, [ rsi + 0x18 ]
adcx r14, rbp
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], rbx
mulx rbx, rbp, [ rax + 0x0 ]
adox r15, r10
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], r15
mulx r15, r10, [ rax + 0x18 ]
adox r10, rdi
mov rdx, 0x0 
adox r15, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x28 ], r15
mulx r15, rdi, [ rsi + 0x18 ]
mov rdx, -0x2 
inc rdx
adox rbp, r9
setc r9b
clc
adcx rdi, rcx
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x20 ], rdi
mulx rdi, rcx, [ rsi + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x18 ], r10
mov [ rsp - 0x10 ], r12
mulx r12, r10, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x8 ], r8
mov byte [ rsp + 0x0 ], r9b
mulx r9, r8, [ rsi + 0x18 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp + 0x8 ], r14
mov [ rsp + 0x10 ], r11
mulx r11, r14, rbp
mov r11, 0xfffffffefffffc2f 
mov rdx, r14
mov [ rsp + 0x18 ], rdi
mulx rdi, r14, r11
adcx r8, r15
adcx r10, r9
mov r15, 0x0 
adcx r12, r15
mov r9, 0xffffffffffffffff 
mulx r11, r15, r9
mov rdx, r15
clc
adcx rdx, rdi
mov rdi, r15
adcx rdi, r11
adcx r15, r11
mov r9, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x20 ], r12
mov [ rsp + 0x28 ], r10
mulx r10, r12, [ rax + 0x10 ]
mov rdx, 0x0 
adcx r11, rdx
clc
adcx rcx, rbx
adox rcx, r13
adcx r12, [ rsp + 0x18 ]
adox r12, [ rsp + 0x10 ]
adcx r10, [ rsp - 0x40 ]
mov r13, [ rsp - 0x48 ]
adcx r13, rdx
adox r10, [ rsp + 0x8 ]
clc
adcx r14, rbp
adcx r9, rcx
movzx r14, byte [ rsp + 0x0 ]
adox r14, r13
seto bl
mov rbp, -0x3 
inc rbp
adox r9, [ rsp - 0x8 ]
mov rcx, 0xd838091dd2253531 
mov rdx, rcx
mulx r13, rcx, r9
mov r13, 0xfffffffefffffc2f 
mov rdx, rcx
mulx rbp, rcx, r13
adcx rdi, r12
adcx r15, r10
adcx r11, r14
adox rdi, [ rsp - 0x10 ]
adox r15, [ rsp - 0x30 ]
adox r11, [ rsp - 0x18 ]
mov r12, 0xffffffffffffffff 
mulx r14, r10, r12
movzx rdx, bl
mov r12, 0x0 
adcx rdx, r12
adox rdx, [ rsp - 0x28 ]
mov rbx, r10
clc
adcx rbx, rbp
mov rbp, r10
adcx rbp, r14
adcx r10, r14
adcx r14, r12
clc
adcx rcx, r9
adcx rbx, rdi
adcx rbp, r15
adcx r10, r11
adcx r14, rdx
seto cl
mov r9, -0x3 
inc r9
adox rbx, [ rsp - 0x38 ]
mov rdi, 0xd838091dd2253531 
mov rdx, rdi
mulx r15, rdi, rbx
adox rbp, [ rsp - 0x20 ]
adox r8, r10
movzx r15, cl
adcx r15, r12
mov r11, 0xffffffffffffffff 
mov rdx, rdi
mulx rcx, rdi, r11
mulx r12, r10, r13
mov rdx, rdi
clc
adcx rdx, r12
mov r12, rdi
adcx r12, rcx
adcx rdi, rcx
mov r9, 0x0 
adcx rcx, r9
clc
adcx r10, rbx
adcx rdx, rbp
adcx r12, r8
adox r14, [ rsp + 0x28 ]
adcx rdi, r14
adox r15, [ rsp + 0x20 ]
adcx rcx, r15
seto r10b
adc r10b, 0x0
movzx r10, r10b
mov rbx, rdx
sub rbx, r13
mov rbp, r12
sbb rbp, r11
mov r8, rdi
sbb r8, r11
mov r14, rcx
sbb r14, r11
movzx r15, r10b
sbb r15, 0x00000000
cmovc r8, rdi
cmovc rbp, r12
cmovc rbx, rdx
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x10 ], r8
mov [ r15 + 0x8 ], rbp
cmovc r14, rcx
mov [ r15 + 0x18 ], r14
mov [ r15 + 0x0 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 176
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 2.0164
; seed 0839696940532223 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 944865 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=184, initial num_batches=31): 74772 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.0791351145401724
; number reverted permutation / tried permutation: 75878 / 90018 =84.292%
; number reverted decision / tried decision: 62704 / 89981 =69.686%
; validated in 1.893s
