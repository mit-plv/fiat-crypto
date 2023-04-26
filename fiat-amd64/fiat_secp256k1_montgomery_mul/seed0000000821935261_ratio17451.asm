SECTION .text
	GLOBAL fiat_secp256k1_montgomery_mul
fiat_secp256k1_montgomery_mul:
sub rsp, 136
mov rax, rdx
mov rdx, [ rdx + 0x8 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
mulx r8, rcx, [ rsi + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], r14
mov [ rsp - 0x40 ], r13
mulx r13, r14, [ rax + 0x8 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x38 ], rdi
mov [ rsp - 0x30 ], r15
mulx r15, rdi, rbp
mov r15, 0xffffffffffffffff 
mov rdx, r15
mov [ rsp - 0x28 ], r8
mulx r8, r15, rdi
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x20 ], r9
mov [ rsp - 0x18 ], r13
mulx r13, r9, rdi
mov rdi, r15
xor rdx, rdx
adox rdi, r13
adcx rcx, rbx
mov rbx, r15
adox rbx, r8
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], rcx
mulx rcx, r13, [ rax + 0x18 ]
adox r15, r8
mov rdx, 0x0 
adox r8, rdx
mov [ rsp - 0x8 ], rcx
mov rcx, -0x3 
inc rcx
adox r9, rbp
setc r9b
clc
adcx r10, r12
adox rdi, r10
mov rdx, [ rsi + 0x0 ]
mulx r12, rbp, [ rax + 0x10 ]
adcx rbp, r11
adox rbx, rbp
mov rdx, [ rax + 0x18 ]
mulx r10, r11, [ rsi + 0x0 ]
adcx r11, r12
adox r15, r11
mov rdx, 0x0 
adcx r10, rdx
adox r8, r10
mov rdx, [ rax + 0x0 ]
mulx rbp, r12, [ rsi + 0x8 ]
clc
adcx r12, rdi
mov rdx, 0xd838091dd2253531 
mulx r11, rdi, r12
seto r11b
inc rcx
adox r14, rbp
adcx r14, rbx
mov rdx, [ rax + 0x10 ]
mulx r10, rbx, [ rsi + 0x8 ]
adox rbx, [ rsp - 0x18 ]
mov rdx, [ rax + 0x18 ]
mulx rcx, rbp, [ rsi + 0x8 ]
adox rbp, r10
adcx rbx, r15
adcx rbp, r8
mov rdx, 0x0 
adox rcx, rdx
mov r15, 0xfffffffefffffc2f 
mov rdx, rdi
mulx r8, rdi, r15
movzx r10, r11b
adcx r10, rcx
mov r11, 0xffffffffffffffff 
mulx r15, rcx, r11
mov rdx, rcx
mov r11, -0x2 
inc r11
adox rdx, r8
mov r8, rcx
adox r8, r15
adox rcx, r15
setc r11b
clc
adcx rdi, r12
adcx rdx, r14
adcx r8, rbx
mov rdi, 0x0 
adox r15, rdi
adcx rcx, rbp
adcx r15, r10
mov r12, -0x3 
inc r12
adox rdx, [ rsp - 0x20 ]
adox r8, [ rsp - 0x10 ]
mov r14, 0xd838091dd2253531 
mulx rbp, rbx, r14
movzx rbp, r11b
adcx rbp, rdi
mov r11, 0xfffffffefffffc2f 
xchg rdx, r11
mulx rdi, r10, rbx
mov rdx, [ rsi + 0x10 ]
mulx r14, r12, [ rax + 0x10 ]
clc
mov rdx, -0x1 
movzx r9, r9b
adcx r9, rdx
adcx r12, [ rsp - 0x28 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x0 ], r13
mulx r13, r9, [ rsi + 0x10 ]
adcx r9, r14
adox r12, rcx
adox r9, r15
mov rdx, 0xffffffffffffffff 
mulx r15, rcx, rbx
mov rbx, 0x0 
adcx r13, rbx
mov r14, rcx
clc
adcx r14, rdi
mov rdi, rcx
adcx rdi, r15
adcx rcx, r15
setc dl
clc
adcx r10, r11
movzx r10, dl
lea r10, [ r10 + r15 ]
mov rdx, [ rsi + 0x18 ]
mulx r15, r11, [ rax + 0x8 ]
adcx r14, r8
adcx rdi, r12
adcx rcx, r9
adox r13, rbp
adcx r10, r13
seto dl
mov r8, -0x3 
inc r8
adox r14, [ rsp - 0x30 ]
mov rbp, 0xd838091dd2253531 
xchg rdx, rbp
mulx r9, r12, r14
setc r9b
clc
adcx r11, [ rsp - 0x38 ]
movzx r13, r9b
movzx rbp, bpl
lea r13, [ r13 + rbp ]
adox r11, rdi
adcx r15, [ rsp - 0x40 ]
mov rdi, 0xfffffffefffffc2f 
mov rdx, r12
mulx rbp, r12, rdi
adox r15, rcx
mov rcx, [ rsp + 0x0 ]
adcx rcx, [ rsp - 0x48 ]
mov r9, [ rsp - 0x8 ]
adcx r9, rbx
mov rbx, 0xffffffffffffffff 
mulx rdi, r8, rbx
mov rdx, r8
clc
adcx rdx, rbp
mov rbp, r8
adcx rbp, rdi
adcx r8, rdi
mov rbx, 0x0 
adcx rdi, rbx
adox rcx, r10
clc
adcx r12, r14
adcx rdx, r11
adcx rbp, r15
adcx r8, rcx
adox r9, r13
adcx rdi, r9
seto r12b
adc r12b, 0x0
movzx r12, r12b
mov r10, rdx
mov r14, 0xfffffffefffffc2f 
sub r10, r14
mov r13, rbp
mov r11, 0xffffffffffffffff 
sbb r13, r11
mov r15, r8
sbb r15, r11
mov rcx, rdi
sbb rcx, r11
movzx r9, r12b
sbb r9, 0x00000000
cmovc rcx, rdi
cmovc r15, r8
cmovc r13, rbp
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x8 ], r13
cmovc r10, rdx
mov [ r9 + 0x10 ], r15
mov [ r9 + 0x18 ], rcx
mov [ r9 + 0x0 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 136
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.7451
; seed 2535132922421286 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1802848 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=72, initial num_batches=31): 108085 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.05995236425921653
; number reverted permutation / tried permutation: 59152 / 90350 =65.470%
; number reverted decision / tried decision: 36042 / 89649 =40.203%
; validated in 3.705s
