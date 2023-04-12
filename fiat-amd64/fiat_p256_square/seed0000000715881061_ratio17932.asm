SECTION .text
	GLOBAL fiat_p256_square
fiat_p256_square:
sub rsp, 144
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r15
mulx r15, rdi, r12
mov rdx, 0xffffffff 
mov [ rsp - 0x40 ], r14
mov [ rsp - 0x38 ], r10
mulx r10, r14, r12
xor rdx, rdx
adox r8, r13
adcx r14, r15
adcx r10, rdx
clc
adcx rbx, rcx
mov rdx, [ rsi + 0x8 ]
mulx r13, rcx, [ rsi + 0x10 ]
adcx rcx, rbp
mov rdx, [ rsi + 0x8 ]
mulx r15, rbp, [ rsi + 0x18 ]
adcx rbp, r13
mov rdx, 0x0 
adcx r15, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], r15
mulx r15, r13, [ rsi + 0x0 ]
adox r13, r9
clc
adcx rdi, r12
mov rdx, [ rsi + 0x0 ]
mulx r9, rdi, [ rsi + 0x18 ]
adox rdi, r15
mov rdx, 0x0 
adox r9, rdx
mov r15, 0xffffffff00000001 
mov rdx, r15
mov [ rsp - 0x28 ], rax
mulx rax, r15, r12
adcx r14, r8
adcx r10, r13
mov r12, -0x2 
inc r12
adox r11, r14
mov r8, 0xffffffffffffffff 
mov rdx, r11
mulx r13, r11, r8
mov r14, 0xffffffff 
mulx r8, r12, r14
adox rbx, r10
adcx r15, rdi
adox rcx, r15
mov rdi, 0xffffffff00000001 
mulx r15, r10, rdi
mov rdi, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x20 ], r15
mulx r15, r14, [ rsi + 0x0 ]
adcx rax, r9
adox rbp, rax
mov rdx, [ rsi + 0x18 ]
mulx rax, r9, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], r14
mov [ rsp - 0x10 ], r10
mulx r10, r14, [ rsi + 0x10 ]
setc dl
clc
adcx r15, [ rsp - 0x28 ]
adcx r14, [ rsp - 0x38 ]
adcx r9, r10
mov r10, 0x0 
adcx rax, r10
movzx rdx, dl
movzx r10, dl
adox r10, [ rsp - 0x30 ]
clc
adcx r12, r13
mov r13, 0x0 
adcx r8, r13
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x8 ], rax
mulx rax, r13, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x0 ], r9
mov [ rsp + 0x8 ], r14
mulx r14, r9, [ rsi + 0x0 ]
clc
adcx r11, rdi
adcx r12, rbx
adcx r8, rcx
mov rdx, [ rsi + 0x10 ]
mulx rdi, r11, [ rsi + 0x8 ]
adcx rbp, [ rsp - 0x10 ]
adcx r10, [ rsp - 0x20 ]
seto dl
mov rbx, -0x2 
inc rbx
adox r11, r14
adox rdi, [ rsp - 0x40 ]
adox r13, [ rsp - 0x48 ]
seto cl
inc rbx
adox r9, r12
adox r11, r8
adox rdi, rbp
adox r13, r10
movzx r14, dl
adcx r14, rbx
mov rdx, 0xffffffffffffffff 
mulx r8, r12, r9
movzx rbp, cl
lea rbp, [ rbp + rax ]
clc
adcx r12, r9
adox rbp, r14
mov r12, 0xffffffff 
mov rdx, r9
mulx rax, r9, r12
seto r10b
mov rcx, -0x3 
inc rcx
adox r9, r8
adox rax, rbx
adcx r9, r11
adcx rax, rdi
mov r11, 0xffffffff00000001 
mulx r14, rdi, r11
adcx rdi, r13
mov rdx, -0x3 
inc rdx
adox r9, [ rsp - 0x18 ]
adcx r14, rbp
adox r15, rax
mov rdx, 0xffffffffffffffff 
mulx r8, r13, r9
mov rdx, r9
mulx rbp, r9, r12
movzx rax, r10b
adcx rax, rbx
clc
adcx r9, r8
adcx rbp, rbx
adox rdi, [ rsp + 0x8 ]
adox r14, [ rsp + 0x0 ]
clc
adcx r13, rdx
adcx r9, r15
adcx rbp, rdi
mulx r10, r13, r11
adcx r13, r14
adox rax, [ rsp - 0x8 ]
adcx r10, rax
seto dl
adc dl, 0x0
movzx rdx, dl
mov r15, r9
mov r8, 0xffffffffffffffff 
sub r15, r8
mov rdi, rbp
sbb rdi, r12
mov r14, r13
sbb r14, 0x00000000
mov rax, r10
sbb rax, r11
movzx rcx, dl
sbb rcx, 0x00000000
cmovc rdi, rbp
cmovc rax, r10
cmovc r14, r13
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x10 ], r14
cmovc r15, r9
mov [ rcx + 0x0 ], r15
mov [ rcx + 0x8 ], rdi
mov [ rcx + 0x18 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 144
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.7932
; seed 2176506572252894 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 883421 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=193, initial num_batches=31): 71657 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.0811130819846936
; number reverted permutation / tried permutation: 76781 / 89928 =85.381%
; number reverted decision / tried decision: 60102 / 90071 =66.727%
; validated in 1.049s
