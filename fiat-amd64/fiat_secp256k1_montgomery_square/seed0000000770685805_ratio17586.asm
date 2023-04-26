SECTION .text
	GLOBAL fiat_secp256k1_montgomery_square
fiat_secp256k1_montgomery_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, r11
mov rbp, 0xffffffffffffffff 
mov rdx, rbx
mov [ rsp - 0x70 ], r12
mulx r12, rbx, rbp
mov [ rsp - 0x68 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, rbp, [ rsi + 0x18 ]
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x48 ], rdi
mov [ rsp - 0x40 ], rbp
mulx rbp, rdi, r13
xor r13, r13
adox rax, rcx
mov rcx, rbx
adcx rcx, rbp
mov rdx, [ rsi + 0x10 ]
mulx r13, rbp, [ rsi + 0x0 ]
mov rdx, rbx
adcx rdx, r12
adcx rbx, r12
mov [ rsp - 0x38 ], r15
mov r15, 0x0 
adcx r12, r15
adox rbp, r10
mov r10, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], r14
mulx r14, r15, [ rsi + 0x0 ]
adox r15, r13
clc
adcx rdi, r11
adcx rcx, rax
adcx r10, rbp
adcx rbx, r15
mov rdi, 0x0 
adox r14, rdi
adcx r12, r14
mov rdx, [ rsi + 0x8 ]
mulx rax, r11, rdx
mov rdx, [ rsi + 0x18 ]
mulx rbp, r13, [ rsi + 0x8 ]
mov rdx, -0x3 
inc rdx
adox r8, rcx
mov r15, 0xd838091dd2253531 
mov rdx, r15
mulx rcx, r15, r8
setc cl
clc
adcx r11, r9
mov r9, 0xfffffffefffffc2f 
mov rdx, r15
mulx r14, r15, r9
adcx rax, [ rsp - 0x30 ]
adcx r13, [ rsp - 0x38 ]
adox r11, r10
mov r10, rdx
mov rdx, [ rsi + 0x10 ]
mulx r9, rdi, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x28 ], r9
mov [ rsp - 0x20 ], rdi
mulx rdi, r9, r10
mov r10, r9
setc dl
clc
adcx r10, r14
mov r14, r9
adcx r14, rdi
adcx r9, rdi
mov [ rsp - 0x18 ], r9
setc r9b
clc
adcx r15, r8
adox rax, rbx
adox r13, r12
adcx r10, r11
adcx r14, rax
movzx r15, dl
lea r15, [ r15 + rbp ]
mov rdx, [ rsi + 0x8 ]
mulx r12, rbx, [ rsi + 0x10 ]
movzx rdx, cl
adox rdx, r15
seto cl
mov rbp, -0x2 
inc rbp
adox r10, [ rsp - 0x20 ]
mov r8, 0xd838091dd2253531 
xchg rdx, r8
mulx rax, r11, r10
movzx rax, r9b
lea rax, [ rax + rdi ]
mov rdi, 0xffffffffffffffff 
mov rdx, r11
mulx r9, r11, rdi
adcx r13, [ rsp - 0x18 ]
adcx rax, r8
mov r15, rdx
mov rdx, [ rsi + 0x10 ]
mulx rbp, r8, rdx
movzx rdx, cl
mov rdi, 0x0 
adcx rdx, rdi
clc
adcx rbx, [ rsp - 0x28 ]
adcx r8, r12
adox rbx, r14
adox r8, r13
adcx rbp, [ rsp - 0x40 ]
mov r14, 0xfffffffefffffc2f 
xchg rdx, r14
mulx rcx, r12, r15
mov r15, [ rsp - 0x48 ]
adcx r15, rdi
adox rbp, rax
mov r13, r11
clc
adcx r13, rcx
mov rax, r11
adcx rax, r9
adcx r11, r9
adcx r9, rdi
clc
adcx r12, r10
adcx r13, rbx
mov rdx, [ rsi + 0x18 ]
mulx r10, r12, [ rsi + 0x8 ]
adcx rax, r8
adcx r11, rbp
adox r15, r14
mov rdx, [ rsi + 0x0 ]
mulx rbx, r14, [ rsi + 0x18 ]
adcx r9, r15
seto dl
mov r8, -0x3 
inc r8
adox r14, r13
setc cl
clc
adcx r12, rbx
mov bpl, dl
mov rdx, [ rsi + 0x18 ]
mulx r15, r13, rdx
mov rdx, [ rsi + 0x10 ]
mulx rdi, rbx, [ rsi + 0x18 ]
adox r12, rax
adcx rbx, r10
adcx r13, rdi
mov rdx, 0xd838091dd2253531 
mulx rax, r10, r14
mov rax, 0x0 
adcx r15, rax
mov rdi, 0xfffffffefffffc2f 
mov rdx, rdi
mulx rax, rdi, r10
clc
adcx rdi, r14
mov rdi, 0xffffffffffffffff 
mov rdx, rdi
mulx r14, rdi, r10
adox rbx, r11
adox r13, r9
movzx r11, cl
movzx rbp, bpl
lea r11, [ r11 + rbp ]
adox r15, r11
mov rbp, rdi
seto cl
inc r8
adox rbp, rax
mov r9, rdi
adox r9, r14
adox rdi, r14
mov r10, 0x0 
adox r14, r10
adcx rbp, r12
adcx r9, rbx
adcx rdi, r13
adcx r14, r15
setc r12b
mov rax, rbp
mov rbx, 0xfffffffefffffc2f 
sub rax, rbx
mov r13, r9
sbb r13, rdx
mov r11, rdi
sbb r11, rdx
movzx r15, r12b
movzx rcx, cl
lea r15, [ r15 + rcx ]
mov rcx, r14
sbb rcx, rdx
sbb r15, 0x00000000
cmovc rcx, r14
cmovc r11, rdi
cmovc r13, r9
cmovc rax, rbp
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x8 ], r13
mov [ r15 + 0x0 ], rax
mov [ r15 + 0x10 ], r11
mov [ r15 + 0x18 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.7586
; seed 3393796391765733 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1164163 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=110, initial num_batches=31): 74231 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06376340770149884
; number reverted permutation / tried permutation: 71771 / 90180 =79.586%
; number reverted decision / tried decision: 43276 / 89819 =48.181%
; validated in 2.698s
