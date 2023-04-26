SECTION .text
	GLOBAL fiat_p224_mul
fiat_p224_mul:
sub rsp, 224
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x48 ], r9
mov [ rsp - 0x40 ], r10
mulx r10, r9, r15
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], r14
mulx r14, r10, [ rax + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x30 ], r14
mov [ rsp - 0x28 ], r10
mulx r10, r14, [ rax + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x20 ], r13
mov [ rsp - 0x18 ], rbx
mulx rbx, r13, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x10 ], r12
mov [ rsp - 0x8 ], r10
mulx r10, r12, [ rax + 0x0 ]
xor rdx, rdx
adox r13, r10
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x0 ], r13
mulx r13, r10, [ rax + 0x10 ]
adcx rcx, r11
adox rbp, rbx
adcx r10, r8
mov rdx, [ rax + 0x18 ]
mulx r8, r11, [ rsi + 0x8 ]
adcx r11, r13
mov rdx, 0xffffffff00000000 
mulx r13, rbx, r9
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x8 ], rbp
mov [ rsp + 0x10 ], r12
mulx r12, rbp, r9
mov rdx, 0x0 
adcx r8, rdx
clc
adcx rbp, r13
mov r13, 0xffffffff 
mov rdx, r13
mov [ rsp + 0x18 ], r8
mulx r8, r13, r9
adcx r13, r12
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x20 ], r11
mulx r11, r12, [ rsi + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x28 ], r10
mov [ rsp + 0x30 ], rcx
mulx rcx, r10, [ rsi + 0x0 ]
mov rdx, 0x0 
adcx r8, rdx
clc
adcx r14, rdi
adcx r12, [ rsp - 0x8 ]
adcx r10, r11
mov rdx, [ rax + 0x18 ]
mulx r11, rdi, [ rsi + 0x10 ]
adox rdi, [ rsp - 0x10 ]
setc dl
clc
adcx r9, r15
adcx rbx, r14
adcx rbp, r12
adcx r13, r10
mov r9b, dl
mov rdx, [ rsi + 0x18 ]
mulx r14, r15, [ rax + 0x10 ]
mov rdx, 0x0 
adox r11, rdx
mov r12, [ rsp - 0x20 ]
mov r10, -0x3 
inc r10
adox r12, [ rsp - 0x18 ]
adox r15, [ rsp - 0x38 ]
adox r14, [ rsp - 0x28 ]
seto r10b
mov [ rsp + 0x38 ], r14
mov r14, -0x3 
inc r14
adox rbx, [ rsp - 0x40 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x40 ], r15
mulx r15, r14, rbx
movzx r15, r9b
lea r15, [ r15 + rcx ]
mulx r9, rcx, r14
adox rbp, [ rsp + 0x30 ]
adcx r8, r15
movzx r15, r10b
mov rdx, [ rsp - 0x30 ]
lea r15, [ r15 + rdx ]
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x48 ], r15
mulx r15, r10, r14
mov rdx, 0xffffffff 
mov [ rsp + 0x50 ], r12
mov [ rsp + 0x58 ], r11
mulx r11, r12, r14
setc dl
clc
adcx rcx, r15
adcx r12, r9
mov r9, 0x0 
adcx r11, r9
adox r13, [ rsp + 0x28 ]
clc
adcx r14, rbx
adcx r10, rbp
adox r8, [ rsp + 0x20 ]
adcx rcx, r13
movzx rdx, dl
movzx r14, dl
adox r14, [ rsp + 0x18 ]
seto bl
mov rbp, -0x3 
inc rbp
adox r10, [ rsp + 0x10 ]
adox rcx, [ rsp + 0x0 ]
mov rdx, 0xffffffffffffffff 
mulx r13, r15, r10
mulx r9, r13, r15
adcx r12, r8
mov r8, 0xffffffff00000000 
mov rdx, r15
mulx rbp, r15, r8
adcx r11, r14
movzx r14, bl
mov r8, 0x0 
adcx r14, r8
adox r12, [ rsp + 0x8 ]
adox rdi, r11
clc
adcx r13, rbp
adox r14, [ rsp + 0x58 ]
mov rbx, 0xffffffff 
mulx r11, rbp, rbx
adcx rbp, r9
adcx r11, r8
clc
adcx rdx, r10
adcx r15, rcx
adcx r13, r12
seto dl
mov r10, -0x3 
inc r10
adox r15, [ rsp - 0x48 ]
adcx rbp, rdi
adcx r11, r14
movzx rcx, dl
adcx rcx, r8
adox r13, [ rsp + 0x50 ]
mov r9, 0xffffffffffffffff 
mov rdx, r9
mulx r12, r9, r15
adox rbp, [ rsp + 0x40 ]
adox r11, [ rsp + 0x38 ]
mov r12, r9
clc
adcx r12, r15
mov r12, 0xffffffff00000000 
mov rdx, r9
mulx rdi, r9, r12
adcx r9, r13
adox rcx, [ rsp + 0x48 ]
mov r14, 0xffffffffffffffff 
mulx r13, r15, r14
seto r10b
mov rbx, -0x3 
inc rbx
adox r15, rdi
mov rdi, 0xffffffff 
mulx rbx, r8, rdi
adox r8, r13
mov rdx, 0x0 
adox rbx, rdx
adcx r15, rbp
adcx r8, r11
adcx rbx, rcx
movzx rbp, r10b
adc rbp, 0x0
mov r11, r9
sub r11, 0x00000001
mov r10, r15
sbb r10, r12
mov rcx, r8
sbb rcx, r14
mov r13, rbx
sbb r13, rdi
sbb rbp, 0x00000000
cmovc r13, rbx
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x18 ], r13
cmovc rcx, r8
mov [ rbp + 0x10 ], rcx
cmovc r10, r15
cmovc r11, r9
mov [ rbp + 0x0 ], r11
mov [ rbp + 0x8 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 224
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.6308
; seed 2588221006803591 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 958726 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=221, initial num_batches=31): 76535 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.0798298992621458
; number reverted permutation / tried permutation: 73201 / 89869 =81.453%
; number reverted decision / tried decision: 64345 / 90130 =71.391%
; validated in 1.75s
