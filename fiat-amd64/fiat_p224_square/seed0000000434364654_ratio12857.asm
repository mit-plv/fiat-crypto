SECTION .text
	GLOBAL fiat_p224_square
fiat_p224_square:
sub rsp, 168
mov rdx, [ rsi + 0x10 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rbx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
mov rdx, 0xffffffff 
mov [ rsp - 0x48 ], r11
mov [ rsp - 0x40 ], r8
mulx r8, r11, r14
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x38 ], rcx
mov [ rsp - 0x30 ], r8
mulx r8, rcx, r14
mov rdx, r14
mov [ rsp - 0x28 ], r11
xor r11, r11
adox rdx, rbx
mov rdx, [ rsi + 0x8 ]
mulx r11, rbx, [ rsi + 0x0 ]
adcx rbx, rbp
adcx rax, r11
adcx r15, r10
mov rdx, [ rsi + 0x10 ]
mulx rbp, r10, [ rsi + 0x8 ]
mov rdx, 0x0 
adcx rdi, rdx
clc
adcx r10, r9
adcx r12, rbp
mov rdx, [ rsi + 0x18 ]
mulx r11, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x20 ], r11
mulx r11, rbp, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x18 ], r12
mov [ rsp - 0x10 ], r10
mulx r10, r12, [ rsi + 0x0 ]
adox rcx, rbx
adcx r9, r13
setc dl
clc
adcx r12, rcx
mov r13b, dl
mov rdx, [ rsi + 0x8 ]
mulx rcx, rbx, rdx
setc dl
clc
adcx rbx, r10
mov r10, 0xffffffffffffffff 
xchg rdx, r10
mov [ rsp - 0x8 ], r9
mov byte [ rsp + 0x0 ], r13b
mulx r13, r9, r12
mov [ rsp + 0x8 ], rbx
mulx rbx, r13, r14
adcx rbp, rcx
mov rdx, [ rsi + 0x18 ]
mulx rcx, r14, [ rsi + 0x8 ]
adcx r14, r11
mov rdx, 0x0 
adcx rcx, rdx
clc
adcx r13, r8
adox r13, rax
adcx rbx, [ rsp - 0x28 ]
mov r8, [ rsp - 0x30 ]
adcx r8, rdx
adox rbx, r15
adox r8, rdi
mov rdx, [ rsi + 0x18 ]
mulx r15, rax, [ rsi + 0x8 ]
clc
adcx rax, [ rsp - 0x38 ]
mov rdx, [ rsi + 0x10 ]
mulx r11, rdi, [ rsi + 0x18 ]
mov rdx, r9
mov [ rsp + 0x10 ], rax
seto al
mov [ rsp + 0x18 ], r11
mov r11, -0x2 
inc r11
adox rdx, r12
adcx rdi, r15
setc dl
clc
movzx r10, r10b
adcx r10, r11
adcx r13, [ rsp + 0x8 ]
adcx rbp, rbx
adcx r14, r8
movzx r12, al
adcx r12, rcx
mov r10, 0xffffffff00000000 
xchg rdx, r10
mulx rbx, rcx, r9
adox rcx, r13
mov rax, 0xffffffffffffffff 
mov rdx, r9
mulx r8, r9, rax
setc r15b
clc
adcx r9, rbx
mov r13, 0xffffffff 
mulx r11, rbx, r13
adcx rbx, r8
adox r9, rbp
adox rbx, r14
mov rdx, 0x0 
adcx r11, rdx
clc
adcx rcx, [ rsp - 0x40 ]
adcx r9, [ rsp - 0x10 ]
adcx rbx, [ rsp - 0x18 ]
mov rdx, rax
mulx rbp, rax, rcx
mov rdx, rax
mulx rbp, rax, r13
adox r11, r12
mov r14, 0xffffffff00000000 
mulx r8, r12, r14
movzx r13, r15b
mov r14, 0x0 
adox r13, r14
mov r15, rdx
mov [ rsp + 0x20 ], rdi
mov rdi, -0x3 
inc rdi
adox r15, rcx
movzx r15, byte [ rsp + 0x0 ]
mov rcx, [ rsp - 0x20 ]
lea r15, [ r15 + rcx ]
adcx r11, [ rsp - 0x8 ]
adox r12, r9
adcx r15, r13
setc cl
clc
adcx r12, [ rsp - 0x48 ]
mov r9, 0xffffffffffffffff 
mulx r14, r13, r9
setc dl
clc
adcx r13, r8
adox r13, rbx
adcx rax, r14
mov rbx, 0x0 
adcx rbp, rbx
adox rax, r11
xchg rdx, r12
mulx r11, r8, r9
adox rbp, r15
xchg rdx, r9
mulx r15, r11, r8
mov rdx, [ rsi + 0x18 ]
mulx rbx, r14, rdx
clc
mov rdx, -0x1 
movzx r10, r10b
adcx r10, rdx
adcx r14, [ rsp + 0x18 ]
movzx r10, cl
mov rdx, 0x0 
adox r10, rdx
adc rbx, 0x0
add r12b, 0x7F
adox r13, [ rsp + 0x10 ]
adox rax, [ rsp + 0x20 ]
adox r14, rbp
mov rcx, 0xffffffff00000000 
mov rdx, r8
mulx r12, r8, rcx
adcx r11, r12
mov rbp, 0xffffffff 
mulx rdi, r12, rbp
adcx r12, r15
mov r15, 0x0 
adcx rdi, r15
clc
adcx rdx, r9
adcx r8, r13
adcx r11, rax
adox rbx, r10
adcx r12, r14
adcx rdi, rbx
seto dl
adc dl, 0x0
movzx rdx, dl
mov r9, r8
sub r9, 0x00000001
mov r10, r11
sbb r10, rcx
mov r13, r12
mov rax, 0xffffffffffffffff 
sbb r13, rax
mov r14, rdi
sbb r14, rbp
movzx rbx, dl
sbb rbx, 0x00000000
cmovc r14, rdi
cmovc r9, r8
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x18 ], r14
cmovc r13, r12
cmovc r10, r11
mov [ rbx + 0x8 ], r10
mov [ rbx + 0x0 ], r9
mov [ rbx + 0x10 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 168
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.2857
; seed 1613024154627716 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1389238 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=142, initial num_batches=31): 87952 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06330952651741459
; number reverted permutation / tried permutation: 69949 / 90417 =77.363%
; number reverted decision / tried decision: 48521 / 89582 =54.164%
; validated in 2.542s
