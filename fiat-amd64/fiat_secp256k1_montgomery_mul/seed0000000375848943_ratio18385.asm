SECTION .text
	GLOBAL fiat_secp256k1_montgomery_mul
fiat_secp256k1_montgomery_mul:
sub rsp, 168
mov rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x10 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, rcx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x48 ], r14
mulx r14, rdi, [ rsi + 0x8 ]
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x40 ], r10
mov [ rsp - 0x38 ], r13
mulx r13, r10, r15
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x30 ], r11
mov [ rsp - 0x28 ], r14
mulx r14, r11, r15
test al, al
adox r10, rcx
mov r10, r11
adcx r10, r13
mov rcx, r11
adcx rcx, r14
adcx r11, r14
mov r15, 0x0 
adcx r14, r15
clc
adcx rbp, r8
adox r10, rbp
mov rdx, [ rax + 0x18 ]
mulx r13, r8, [ rsi + 0x0 ]
adcx r9, r12
adcx r8, rbx
adox rcx, r9
adox r11, r8
mov rdx, [ rax + 0x8 ]
mulx r12, rbx, [ rsi + 0x8 ]
mov rdx, [ rax + 0x10 ]
mulx r9, rbp, [ rsi + 0x8 ]
adcx r13, r15
mov rdx, [ rax + 0x18 ]
mulx r15, r8, [ rsi + 0x8 ]
clc
adcx rdi, r10
adox r14, r13
seto dl
mov r10, -0x2 
inc r10
adox rbx, [ rsp - 0x28 ]
adcx rbx, rcx
adox rbp, r12
adox r8, r9
mov rcx, 0xd838091dd2253531 
xchg rdx, rdi
mulx r9, r12, rcx
mov r9, 0x0 
adox r15, r9
mov r13, 0xfffffffefffffc2f 
xchg rdx, r12
mulx r10, r9, r13
adcx rbp, r11
adcx r8, r14
mov r11, rdx
mov rdx, [ rsi + 0x18 ]
mulx rcx, r14, [ rax + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x20 ], r8
mulx r8, r13, [ rax + 0x10 ]
movzx rdx, dil
adcx rdx, r15
mov rdi, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], rbp
mulx rbp, r15, [ rax + 0x0 ]
mov rdx, -0x2 
inc rdx
adox r14, rbp
adox r13, rcx
mov rcx, 0xffffffffffffffff 
mov rdx, rcx
mulx rbp, rcx, r11
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x10 ], r13
mulx r13, r11, [ rax + 0x8 ]
mov rdx, rcx
mov [ rsp - 0x8 ], r14
setc r14b
clc
adcx rdx, r10
mov r10, rcx
adcx r10, rbp
mov [ rsp + 0x0 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x18 ]
mov byte [ rsp + 0x8 ], r14b
mov [ rsp + 0x10 ], rdi
mulx rdi, r14, [ rax + 0x18 ]
adcx rcx, rbp
adox r14, r8
seto dl
mov r8, -0x2 
inc r8
adox r11, [ rsp - 0x30 ]
adox r13, [ rsp - 0x38 ]
mov r8, 0x0 
adcx rbp, r8
clc
adcx r9, r12
adcx r15, rbx
adcx r10, [ rsp - 0x18 ]
adcx rcx, [ rsp - 0x20 ]
adcx rbp, [ rsp + 0x10 ]
movzx r9, byte [ rsp + 0x8 ]
adcx r9, r8
clc
adcx r15, [ rsp - 0x40 ]
mov r12, 0xd838091dd2253531 
xchg rdx, r12
mulx r8, rbx, r15
adcx r11, r10
adcx r13, rcx
mov r8, 0xfffffffefffffc2f 
mov rdx, r8
mulx r10, r8, rbx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x18 ], rdi
mulx rdi, rcx, [ rax + 0x18 ]
adox rcx, [ rsp - 0x48 ]
adcx rcx, rbp
mov rdx, 0x0 
adox rdi, rdx
mov rbp, 0xffffffffffffffff 
mov rdx, rbx
mov byte [ rsp + 0x20 ], r12b
mulx r12, rbx, rbp
mov rdx, rbx
mov rbp, -0x2 
inc rbp
adox rdx, r10
mov r10, rbx
adox r10, r12
adcx rdi, r9
adox rbx, r12
mov r9, 0x0 
adox r12, r9
mov rbp, -0x3 
inc rbp
adox r8, r15
adox rdx, r11
adox r10, r13
setc r8b
clc
adcx rdx, [ rsp + 0x0 ]
adcx r10, [ rsp - 0x8 ]
adox rbx, rcx
adcx rbx, [ rsp - 0x10 ]
adox r12, rdi
mov r15, 0xd838091dd2253531 
mulx r13, r11, r15
movzx r13, r8b
adox r13, r9
adcx r14, r12
mov rcx, 0xfffffffefffffc2f 
xchg rdx, r11
mulx rdi, r8, rcx
mov r12, 0xffffffffffffffff 
mulx rbp, r9, r12
mov rdx, r9
mov r12, -0x2 
inc r12
adox rdx, rdi
mov rdi, r9
adox rdi, rbp
adox r9, rbp
movzx r12, byte [ rsp + 0x20 ]
mov rcx, [ rsp + 0x18 ]
lea r12, [ r12 + rcx ]
adcx r12, r13
setc cl
clc
adcx r8, r11
adcx rdx, r10
adcx rdi, rbx
adcx r9, r14
mov r8, 0x0 
adox rbp, r8
adcx rbp, r12
movzx r11, cl
adc r11, 0x0
mov r10, rdx
mov rbx, 0xfffffffefffffc2f 
sub r10, rbx
mov r13, rdi
mov r14, 0xffffffffffffffff 
sbb r13, r14
mov rcx, r9
sbb rcx, r14
mov r12, rbp
sbb r12, r14
sbb r11, 0x00000000
cmovc r12, rbp
cmovc r10, rdx
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x0 ], r10
cmovc r13, rdi
mov [ r11 + 0x8 ], r13
mov [ r11 + 0x18 ], r12
cmovc rcx, r9
mov [ r11 + 0x10 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 168
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.8385
; seed 4298934968286513 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1325859 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=113, initial num_batches=31): 83905 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06328350148846898
; number reverted permutation / tried permutation: 66674 / 90049 =74.042%
; number reverted decision / tried decision: 45917 / 89950 =51.047%
; validated in 2.915s
