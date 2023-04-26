SECTION .text
	GLOBAL fiat_p224_square
fiat_p224_square:
sub rsp, 144
mov rdx, [ rsi + 0x10 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, rdx
xor rdx, rdx
adox r11, r9
adox rax, rcx
mov rdx, [ rsi + 0x0 ]
mulx r9, rcx, [ rsi + 0x18 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, r8
mov rbp, 0xffffffff00000000 
mov rdx, rbx
mov [ rsp - 0x70 ], r12
mulx r12, rbx, rbp
mov [ rsp - 0x68 ], r13
mov r13, 0xffffffffffffffff 
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, r13
mov rbp, 0xffffffff 
mov [ rsp - 0x50 ], rdi
mulx rdi, r13, rbp
mov rbp, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], rcx
mov [ rsp - 0x40 ], r9
mulx r9, rcx, [ rsi + 0x0 ]
adox rcx, r10
adcx r14, r12
mov rdx, [ rsi + 0x8 ]
mulx r12, r10, [ rsi + 0x0 ]
mov rdx, 0x0 
adox r9, rdx
adcx r13, r15
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], r9
mulx r9, r15, rdx
adc rdi, 0x0
xor rdx, rdx
adox r15, r12
adcx rbp, r8
mov rdx, [ rsi + 0x8 ]
mulx r8, rbp, [ rsi + 0x18 ]
adcx rbx, r11
mov rdx, [ rsi + 0x8 ]
mulx r12, r11, [ rsi + 0x10 ]
adox r11, r9
adox rbp, r12
seto dl
mov r9, -0x2 
inc r9
adox r10, rbx
movzx rbx, dl
lea rbx, [ rbx + r8 ]
adcx r14, rax
adox r15, r14
mov rax, 0xffffffffffffffff 
mov rdx, r10
mulx r8, r10, rax
adcx r13, rcx
adcx rdi, [ rsp - 0x38 ]
mov r8, r10
setc cl
clc
adcx r8, rdx
adox r11, r13
adox rbp, rdi
mov r8, 0xffffffff00000000 
mov rdx, r8
mulx r12, r8, r10
movzx r14, cl
adox r14, rbx
mov rdx, rax
mulx rbx, rax, r10
adcx r8, r15
seto r15b
inc r9
adox rax, r12
mov r13, 0xffffffff 
mov rdx, r13
mulx rcx, r13, r10
adox r13, rbx
adcx rax, r11
adox rcx, r9
mov rdx, [ rsi + 0x0 ]
mulx rdi, r10, [ rsi + 0x10 ]
mov rdx, -0x3 
inc rdx
adox r10, r8
mov rdx, [ rsi + 0x10 ]
mulx r12, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx r8, rbx, rdx
adcx r13, rbp
adcx rcx, r14
mov rdx, 0xffffffffffffffff 
mulx r14, rbp, r10
mulx r9, r14, rbp
movzx rdx, r15b
mov [ rsp - 0x30 ], rcx
mov rcx, 0x0 
adcx rdx, rcx
clc
adcx r11, rdi
adcx rbx, r12
adox r11, rax
mov r15, rdx
mov rdx, [ rsi + 0x10 ]
mulx rdi, rax, [ rsi + 0x18 ]
adcx rax, r8
mov rdx, 0xffffffff00000000 
mulx r8, r12, rbp
adcx rdi, rcx
clc
adcx r14, r8
mov rdx, [ rsi + 0x8 ]
mulx rcx, r8, [ rsi + 0x18 ]
mov rdx, 0xffffffff 
mov [ rsp - 0x28 ], rcx
mov [ rsp - 0x20 ], rdi
mulx rdi, rcx, rbp
adcx rcx, r9
mov r9, 0x0 
adcx rdi, r9
clc
adcx rbp, r10
adcx r12, r11
adox rbx, r13
seto bpl
mov r10, -0x3 
inc r10
adox r8, [ rsp - 0x40 ]
adcx r14, rbx
seto r13b
mov r11, -0x3 
inc r11
adox r12, [ rsp - 0x48 ]
seto r11b
dec r9
movzx rbp, bpl
adox rbp, r9
adox rax, [ rsp - 0x30 ]
adox r15, [ rsp - 0x20 ]
adcx rcx, rax
mov rdx, [ rsi + 0x18 ]
mulx rbx, rbp, [ rsi + 0x10 ]
adcx rdi, r15
seto dl
adc dl, 0x0
movzx rdx, dl
mov al, dl
mov rdx, [ rsi + 0x18 ]
mulx r9, r15, rdx
add r13b, 0x7F
adox rbp, [ rsp - 0x28 ]
mov rdx, 0xffffffffffffffff 
mulx r10, r13, r12
mov r10, 0xffffffff00000000 
mov rdx, r10
mov byte [ rsp - 0x18 ], al
mulx rax, r10, r13
mov rdx, 0xffffffff 
mov [ rsp - 0x10 ], r10
mov [ rsp - 0x8 ], rdi
mulx rdi, r10, r13
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x0 ], rdi
mov [ rsp + 0x8 ], r10
mulx r10, rdi, r13
adcx r13, r12
adox r15, rbx
setc r13b
clc
mov r12, -0x1 
movzx r11, r11b
adcx r11, r12
adcx r14, r8
adcx rbp, rcx
mov r8, 0x0 
adox r9, r8
mov r11, -0x3 
inc r11
adox rdi, rax
adox r10, [ rsp + 0x8 ]
adcx r15, [ rsp - 0x8 ]
movzx rcx, byte [ rsp - 0x18 ]
adcx rcx, r9
setc bl
clc
movzx r13, r13b
adcx r13, r12
adcx r14, [ rsp - 0x10 ]
mov rax, [ rsp + 0x0 ]
adox rax, r8
adcx rdi, rbp
adcx r10, r15
adcx rax, rcx
movzx r13, bl
adc r13, 0x0
mov rbp, r14
sub rbp, 0x00000001
mov r9, rdi
mov r15, 0xffffffff00000000 
sbb r9, r15
mov rbx, r10
sbb rbx, rdx
mov rcx, rax
mov r8, 0xffffffff 
sbb rcx, r8
sbb r13, 0x00000000
cmovc r9, rdi
cmovc rcx, rax
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x8 ], r9
mov [ r13 + 0x18 ], rcx
cmovc rbx, r10
mov [ r13 + 0x10 ], rbx
cmovc rbp, r14
mov [ r13 + 0x0 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 144
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.4039
; seed 4345332255559202 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1226061 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=154, initial num_batches=31): 79746 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06504244079209762
; number reverted permutation / tried permutation: 71444 / 90203 =79.204%
; number reverted decision / tried decision: 62269 / 89796 =69.345%
; validated in 2.934s
