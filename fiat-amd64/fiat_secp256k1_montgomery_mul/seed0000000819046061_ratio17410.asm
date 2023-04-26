SECTION .text
	GLOBAL fiat_secp256k1_montgomery_mul
fiat_secp256k1_montgomery_mul:
mov rax, rdx
mov rdx, [ rdx + 0x8 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, rcx
mov rbx, 0xffffffffffffffff 
mov rdx, rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, r9
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x10 ]
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, r9
xor r9, r9
adox r14, rcx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r14, [ rax + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, r9, [ rsi + 0x0 ]
adcx r10, r8
adcx r14, r11
mov rdx, rbx
seto r11b
mov r8, -0x2 
inc r8
adox rdx, r15
mov r15, rbx
adox r15, rbp
adox rbx, rbp
adcx r9, rcx
mov rcx, 0x0 
adox rbp, rcx
adc rdi, 0x0
add r11b, 0xFF
adcx r10, rdx
mov rdx, [ rax + 0x0 ]
mulx rcx, r11, [ rsi + 0x8 ]
adox r11, r10
adcx r15, r14
adcx rbx, r9
mov rdx, [ rax + 0x8 ]
mulx r9, r14, [ rsi + 0x8 ]
mov rdx, 0xd838091dd2253531 
mulx r8, r10, r11
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], r13
mulx r13, r8, [ rax + 0x10 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x40 ], r12
mov [ rsp - 0x38 ], rbp
mulx rbp, r12, r10
setc dl
clc
adcx r14, rcx
mov cl, dl
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x30 ], rbp
mov [ rsp - 0x28 ], r12
mulx r12, rbp, [ rsi + 0x8 ]
adcx r8, r9
adcx rbp, r13
mov rdx, 0x0 
adcx r12, rdx
adox r14, r15
adox r8, rbx
clc
mov r15, -0x1 
movzx rcx, cl
adcx rcx, r15
adcx rdi, [ rsp - 0x38 ]
adox rbp, rdi
mov rcx, 0xfffffffefffffc2f 
mov rdx, r10
mulx rbx, r10, rcx
setc r9b
clc
adcx rbx, [ rsp - 0x28 ]
mov rdx, [ rsp - 0x28 ]
mov r13, rdx
adcx r13, [ rsp - 0x30 ]
adcx rdx, [ rsp - 0x30 ]
movzx rdi, r9b
adox rdi, r12
setc r12b
clc
adcx r10, r11
adcx rbx, r14
mov r10, rdx
mov rdx, [ rsi + 0x10 ]
mulx r14, r11, [ rax + 0x0 ]
adcx r13, r8
seto dl
inc r15
adox r11, rbx
movzx r8, r12b
mov r9, [ rsp - 0x30 ]
lea r8, [ r8 + r9 ]
adcx r10, rbp
adcx r8, rdi
mov r9b, dl
mov rdx, [ rax + 0x8 ]
mulx r12, rbp, [ rsi + 0x10 ]
movzx rdx, r9b
adcx rdx, r15
mov r9, rdx
mov rdx, [ rax + 0x18 ]
mulx rbx, rdi, [ rsi + 0x10 ]
clc
adcx rbp, r14
adox rbp, r13
adcx r12, [ rsp - 0x40 ]
adcx rdi, [ rsp - 0x48 ]
mov rdx, 0xd838091dd2253531 
mulx r13, r14, r11
adcx rbx, r15
adox r12, r10
mov rdx, [ rax + 0x8 ]
mulx r10, r13, [ rsi + 0x18 ]
mov rdx, rcx
mulx r15, rcx, r14
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x20 ], r10
mov [ rsp - 0x18 ], r13
mulx r13, r10, r14
mov r14, r10
clc
adcx r14, r15
adox rdi, r8
mov r8, r10
adcx r8, r13
adcx r10, r13
mov r15, 0x0 
adcx r13, r15
adox rbx, r9
clc
adcx rcx, r11
mov rdx, [ rsi + 0x18 ]
mulx r11, rcx, [ rax + 0x0 ]
adcx r14, rbp
adcx r8, r12
adcx r10, rdi
adcx r13, rbx
seto dl
adc dl, 0x0
movzx rdx, dl
adox r11, [ rsp - 0x18 ]
mov r9b, dl
mov rdx, [ rax + 0x10 ]
mulx r12, rbp, [ rsi + 0x18 ]
adox rbp, [ rsp - 0x20 ]
adcx rcx, r14
adcx r11, r8
adcx rbp, r10
mov rdx, [ rsi + 0x18 ]
mulx rbx, rdi, [ rax + 0x18 ]
adox rdi, r12
mov rdx, 0xd838091dd2253531 
mulx r8, r14, rcx
mov r8, 0xfffffffefffffc2f 
mov rdx, r14
mulx r10, r14, r8
adox rbx, r15
mov r12, -0x3 
inc r12
adox r14, rcx
adcx rdi, r13
mov r14, 0xffffffffffffffff 
mulx rcx, r13, r14
movzx rdx, r9b
adcx rdx, rbx
mov r9, r13
setc bl
clc
adcx r9, r10
mov r10, r13
adcx r10, rcx
adcx r13, rcx
adox r9, r11
adox r10, rbp
adcx rcx, r15
adox r13, rdi
adox rcx, rdx
movzx r11, bl
adox r11, r15
mov rbp, r9
sub rbp, r8
mov rdi, r10
sbb rdi, r14
mov rbx, r13
sbb rbx, r14
mov rdx, rcx
sbb rdx, r14
sbb r11, 0x00000000
cmovc rdx, rcx
cmovc rdi, r10
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x8 ], rdi
cmovc rbp, r9
cmovc rbx, r13
mov [ r11 + 0x10 ], rbx
mov [ r11 + 0x18 ], rdx
mov [ r11 + 0x0 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.7410
; seed 0330632742082980 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2063892 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=87, initial num_batches=31): 128612 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.062315276186932264
; number reverted permutation / tried permutation: 62938 / 89762 =70.117%
; number reverted decision / tried decision: 57255 / 90237 =63.450%
; validated in 4.349s
