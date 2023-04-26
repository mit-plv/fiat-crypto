SECTION .text
	GLOBAL fiat_secp256k1_montgomery_mul
fiat_secp256k1_montgomery_mul:
sub rsp, 144
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, 0xd838091dd2253531 
mulx r8, rcx, r10
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rax + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rax + 0x8 ]
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rcx
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x10 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r15
mulx r15, rdi, rcx
mov rcx, rdi
test al, al
adox rcx, r13
mov r13, rdi
adox r13, r15
adox rdi, r15
adcx rbx, r11
mov r11, 0x0 
adox r15, r11
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x40 ], r14
mulx r14, r11, [ rax + 0x10 ]
adcx r11, rbp
adcx r8, r14
adc r9, 0x0
test al, al
adox r12, r10
adox rcx, rbx
mov rdx, [ rsi + 0x8 ]
mulx r10, r12, [ rax + 0x0 ]
adcx r12, rcx
mov rdx, 0xd838091dd2253531 
mulx rbx, rbp, r12
adox r13, r11
adox rdi, r8
mov rdx, [ rax + 0x8 ]
mulx r14, rbx, [ rsi + 0x8 ]
setc dl
clc
adcx rbx, r10
mov r11b, dl
mov rdx, [ rsi + 0x8 ]
mulx rcx, r8, [ rax + 0x10 ]
adox r15, r9
mov rdx, [ rax + 0x18 ]
mulx r10, r9, [ rsi + 0x8 ]
adcx r8, r14
adcx r9, rcx
mov rdx, 0x0 
adcx r10, rdx
mov r14, 0xfffffffefffffc2f 
mov rdx, r14
mulx rcx, r14, rbp
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x38 ], r14
mov [ rsp - 0x30 ], r10
mulx r10, r14, rbp
mov rbp, r14
clc
adcx rbp, rcx
mov rcx, r14
adcx rcx, r10
adcx r14, r10
mov rdx, 0x0 
adcx r10, rdx
clc
mov rdx, -0x1 
movzx r11, r11b
adcx r11, rdx
adcx r13, rbx
adcx r8, rdi
mov rdx, [ rax + 0x8 ]
mulx rdi, r11, [ rsi + 0x18 ]
adcx r9, r15
mov rdx, [ rax + 0x0 ]
mulx r15, rbx, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x28 ], rbx
mov [ rsp - 0x20 ], r10
mulx r10, rbx, [ rsi + 0x18 ]
setc dl
movzx rdx, dl
adox rdx, [ rsp - 0x30 ]
clc
adcx r11, r15
seto r15b
mov [ rsp - 0x18 ], r11
mov r11, -0x2 
inc r11
adox r12, [ rsp - 0x38 ]
adcx rbx, rdi
mov r12, rdx
mov rdx, [ rax + 0x18 ]
mulx r11, rdi, [ rsi + 0x18 ]
adcx rdi, r10
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x10 ], rdi
mulx rdi, r10, [ rax + 0x0 ]
adox rbp, r13
mov rdx, 0x0 
adcx r11, rdx
adox rcx, r8
clc
adcx r10, rbp
mov rdx, [ rsi + 0x10 ]
mulx r8, r13, [ rax + 0x8 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x8 ], r11
mulx r11, rbp, r10
mov r11, 0xffffffffffffffff 
mov rdx, rbp
mov [ rsp + 0x0 ], rbx
mulx rbx, rbp, r11
adox r14, r9
adox r12, [ rsp - 0x20 ]
movzx r9, r15b
mov r11, 0x0 
adox r9, r11
mov r15, 0xfffffffefffffc2f 
mov [ rsp + 0x8 ], r9
mulx r9, r11, r15
mov rdx, -0x2 
inc rdx
adox r13, rdi
adcx r13, rcx
mov rdx, [ rax + 0x10 ]
mulx rcx, rdi, [ rsi + 0x10 ]
adox rdi, r8
adox rcx, [ rsp - 0x40 ]
adcx rdi, r14
mov rdx, [ rsp - 0x48 ]
mov r8, 0x0 
adox rdx, r8
mov r14, rbp
mov r15, -0x3 
inc r15
adox r14, r9
setc r9b
clc
adcx r11, r10
mov r11, rbp
adox r11, rbx
adcx r14, r13
setc r10b
clc
adcx r14, [ rsp - 0x28 ]
mov r13, 0xd838091dd2253531 
xchg rdx, r13
mulx r15, r8, r14
adox rbp, rbx
mov r15, 0x0 
adox rbx, r15
dec r15
movzx r10, r10b
adox r10, r15
adox rdi, r11
mov r11, 0xffffffffffffffff 
mov rdx, r8
mulx r10, r8, r11
adcx rdi, [ rsp - 0x18 ]
setc r15b
clc
mov r11, -0x1 
movzx r9, r9b
adcx r9, r11
adcx r12, rcx
adox rbp, r12
adcx r13, [ rsp + 0x8 ]
adox rbx, r13
seto cl
adc cl, 0x0
movzx rcx, cl
add r15b, 0x7F
adox rbp, [ rsp + 0x0 ]
adox rbx, [ rsp - 0x10 ]
movzx rcx, cl
movzx r9, cl
adox r9, [ rsp - 0x8 ]
mov r15, 0xfffffffefffffc2f 
mulx r13, r12, r15
mov rdx, r8
adcx rdx, r13
seto cl
inc r11
adox r12, r14
adox rdx, rdi
mov r12, r8
adcx r12, r10
adox r12, rbp
adcx r8, r10
adox r8, rbx
adcx r10, r11
adox r10, r9
movzx r14, cl
adox r14, r11
mov rdi, rdx
sub rdi, r15
mov rbp, r12
mov rbx, 0xffffffffffffffff 
sbb rbp, rbx
mov rcx, r8
sbb rcx, rbx
mov r9, r10
sbb r9, rbx
sbb r14, 0x00000000
cmovc rbp, r12
cmovc rcx, r8
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x8 ], rbp
cmovc rdi, rdx
mov [ r14 + 0x0 ], rdi
cmovc r9, r10
mov [ r14 + 0x18 ], r9
mov [ r14 + 0x10 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 144
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.9051
; seed 1940461457132185 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1366384 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=111, initial num_batches=31): 86786 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.0635150879986885
; number reverted permutation / tried permutation: 66591 / 90111 =73.899%
; number reverted decision / tried decision: 46873 / 89888 =52.146%
; validated in 2.866s
