SECTION .text
	GLOBAL fiat_secp256k1_montgomery_square
fiat_secp256k1_montgomery_square:
sub rsp, 144
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, rdx
mov rdx, 0xd838091dd2253531 
mulx r9, r8, r11
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x8 ]
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, r8
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x48 ], r12
mov [ rsp - 0x40 ], rbp
mulx rbp, r12, r8
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x38 ], rbx
mulx rbx, r8, [ rsi + 0x10 ]
add rax, rcx
adcx r8, r10
mov rdx, r12
mov r10, -0x2 
inc r10
adox rdx, r14
adcx r15, rbx
mov rcx, r12
adox rcx, rbp
adox r12, rbp
mov r14, 0x0 
adox rbp, r14
mov rbx, rdx
mov rdx, [ rsi + 0x10 ]
mulx r10, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], r14
mov [ rsp - 0x28 ], rbp
mulx rbp, r14, [ rsi + 0x8 ]
adc rdi, 0x0
test al, al
adox r14, r10
adcx r13, r11
adcx rbx, rax
mov rdx, [ rsi + 0x10 ]
mulx r11, r13, [ rsi + 0x18 ]
adcx rcx, r8
adcx r12, r15
adox r9, rbp
adox r13, [ rsp - 0x38 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rax, [ rsi + 0x8 ]
mov rdx, 0x0 
adox r11, rdx
mov r15, -0x3 
inc r15
adox rax, rbx
mov r10, 0xd838091dd2253531 
mov rdx, rax
mulx rbp, rax, r10
mov rbp, rdx
mov rdx, [ rsi + 0x8 ]
mulx r15, rbx, rdx
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x20 ], r11
mulx r11, r10, rax
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x18 ], r13
mov [ rsp - 0x10 ], r9
mulx r9, r13, rax
adcx rdi, [ rsp - 0x28 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x8 ], r14
mulx r14, rax, [ rsi + 0x8 ]
setc dl
clc
adcx rbx, r8
adox rbx, rcx
adcx r15, [ rsp - 0x40 ]
adcx rax, [ rsp - 0x48 ]
mov rcx, 0x0 
adcx r14, rcx
adox r15, r12
mov r12, r13
clc
adcx r12, r11
mov r8, r13
adcx r8, r9
adcx r13, r9
adcx r9, rcx
clc
adcx r10, rbp
adcx r12, rbx
adox rax, rdi
movzx r10, dl
adox r10, r14
adcx r8, r15
adcx r13, rax
adcx r9, r10
mov rdx, [ rsi + 0x0 ]
mulx r11, rbp, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mulx rbx, rdi, rdx
mov rdx, [ rsi + 0x8 ]
mulx r15, r14, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mulx r10, rax, [ rsi + 0x10 ]
setc dl
clc
adcx r14, r11
adcx rax, r15
adcx rdi, r10
movzx r11, dl
adox r11, rcx
adc rbx, 0x0
add r12, [ rsp - 0x30 ]
mov rdx, 0xd838091dd2253531 
mulx r10, r15, r12
mov r10, 0xffffffffffffffff 
mov rdx, r15
mulx rcx, r15, r10
mov r10, 0xfffffffefffffc2f 
mov [ rsp + 0x0 ], rbx
mov [ rsp + 0x8 ], rdi
mulx rdi, rbx, r10
adcx r8, [ rsp - 0x8 ]
mov rdx, -0x2 
inc rdx
adox rbx, r12
adcx r13, [ rsp - 0x10 ]
adcx r9, [ rsp - 0x18 ]
adcx r11, [ rsp - 0x20 ]
mov rbx, r15
setc r12b
clc
adcx rbx, rdi
adox rbx, r8
mov rdi, r15
adcx rdi, rcx
adcx r15, rcx
adox rdi, r13
mov r8, 0x0 
adcx rcx, r8
adox r15, r9
adox rcx, r11
clc
adcx rbp, rbx
adcx r14, rdi
mov r13, 0xd838091dd2253531 
mov rdx, r13
mulx r9, r13, rbp
mov rdx, r13
mulx r13, r9, r10
adcx rax, r15
movzx r11, r12b
adox r11, r8
mov r12, 0xffffffffffffffff 
mulx rdi, rbx, r12
mov r15, rbx
mov rdx, -0x3 
inc rdx
adox r15, r13
mov r13, rbx
adox r13, rdi
adcx rcx, [ rsp + 0x8 ]
adcx r11, [ rsp + 0x0 ]
setc dl
clc
adcx r9, rbp
adcx r15, r14
adcx r13, rax
adox rbx, rdi
adox rdi, r8
adcx rbx, rcx
adcx rdi, r11
movzx r9, dl
adc r9, 0x0
mov rbp, r15
sub rbp, r10
mov r14, r13
sbb r14, r12
mov rax, rbx
sbb rax, r12
mov rcx, rdi
sbb rcx, r12
sbb r9, 0x00000000
cmovc r14, r13
cmovc rbp, r15
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x8 ], r14
cmovc rcx, rdi
mov [ r9 + 0x18 ], rcx
mov [ r9 + 0x0 ], rbp
cmovc rax, rbx
mov [ r9 + 0x10 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 144
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.8767
; seed 4289875456135400 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 895127 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=206, initial num_batches=31): 72874 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.08141191138240719
; number reverted permutation / tried permutation: 75481 / 89902 =83.959%
; number reverted decision / tried decision: 63427 / 90097 =70.399%
; validated in 1.725s
