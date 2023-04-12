SECTION .text
	GLOBAL fiat_p224_square
fiat_p224_square:
sub rsp, 176
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mulx r9, r8, rax
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x10 ]
add rbp, rcx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mulx r13, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rcx
mulx rcx, rdi, [ rsi + 0x0 ]
adcx r14, r12
mov rdx, -0x2 
inc rdx
adox rdi, r10
mov r10, 0xffffffff 
mov rdx, r10
mulx r12, r10, r8
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x40 ], r14
mov [ rsp - 0x38 ], rbp
mulx rbp, r14, [ rsi + 0x10 ]
adox r14, rcx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], r11
mulx r11, rcx, [ rsi + 0x0 ]
adox rcx, rbp
mov rdx, 0x0 
adox r11, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], r11
mulx r11, rbp, [ rsi + 0x10 ]
adcx rbp, r15
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x20 ], rbp
mulx rbp, r15, r8
adc r11, 0x0
mov rdx, r8
mov [ rsp - 0x18 ], r11
xor r11, r11
adox rdx, rax
adox r15, rdi
mov rdx, 0xffffffffffffffff 
mulx rdi, rax, r8
mov rdx, [ rsi + 0x0 ]
mulx r11, r8, [ rsi + 0x8 ]
adcx r8, r15
setc dl
clc
adcx rax, rbp
adcx r10, rdi
adox rax, r14
mov r14b, dl
mov rdx, [ rsi + 0x8 ]
mulx r15, rbp, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x10 ], rax
mulx rax, rdi, r8
mov rax, 0x0 
adcx r12, rax
clc
adcx rbp, r11
adcx r9, r15
mov rdx, [ rsi + 0x18 ]
mulx r15, r11, [ rsi + 0x8 ]
adcx r11, rbx
mov rdx, [ rsi + 0x18 ]
mulx rax, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x8 ], r11
mov [ rsp + 0x0 ], r9
mulx r9, r11, [ rsi + 0x10 ]
mov rdx, 0x0 
adcx r15, rdx
clc
adcx rbx, r13
adox r10, rcx
adcx r11, rax
mov rdx, [ rsi + 0x18 ]
mulx rcx, r13, rdx
adcx r13, r9
adox r12, [ rsp - 0x28 ]
mov rdx, 0xffffffff00000000 
mulx r9, rax, rdi
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x8 ], r13
mov [ rsp + 0x10 ], r11
mulx r11, r13, rdi
mov rdx, 0xffffffff 
mov [ rsp + 0x18 ], rbx
mov [ rsp + 0x20 ], r15
mulx r15, rbx, rdi
seto dl
mov [ rsp + 0x28 ], r12
mov r12, -0x2 
inc r12
adox r13, r9
adox rbx, r11
mov r9, 0x0 
adox r15, r9
adc rcx, 0x0
add r14b, 0xFF
adcx rbp, [ rsp - 0x10 ]
adcx r10, [ rsp + 0x0 ]
adox rdi, r8
adox rax, rbp
mov rdi, [ rsp + 0x28 ]
adcx rdi, [ rsp - 0x8 ]
movzx rdx, dl
movzx r8, dl
adcx r8, [ rsp + 0x20 ]
setc r14b
clc
adcx rax, [ rsp - 0x30 ]
mov rdx, 0xffffffffffffffff 
mulx rbp, r11, rax
mov rbp, 0xffffffff00000000 
mov rdx, r11
mulx r9, r11, rbp
adox r13, r10
adox rbx, rdi
adox r15, r8
adcx r13, [ rsp - 0x38 ]
adcx rbx, [ rsp - 0x40 ]
movzx r10, r14b
mov rdi, 0x0 
adox r10, rdi
mov r14, rdx
mov r8, -0x3 
inc r8
adox r14, rax
adox r11, r13
mov r14, 0xffffffffffffffff 
mulx r13, rax, r14
adcx r15, [ rsp - 0x20 ]
adcx r10, [ rsp - 0x18 ]
setc r8b
clc
adcx rax, r9
adox rax, rbx
mov r9, 0xffffffff 
mulx rdi, rbx, r9
adcx rbx, r13
mov rdx, 0x0 
adcx rdi, rdx
clc
adcx r11, [ rsp - 0x48 ]
mov rdx, r14
mulx r13, r14, r11
adcx rax, [ rsp + 0x18 ]
adox rbx, r15
adox rdi, r10
adcx rbx, [ rsp + 0x10 ]
mov rdx, rbp
mulx r13, rbp, r14
adcx rdi, [ rsp + 0x8 ]
movzx r15, r8b
mov r10, 0x0 
adox r15, r10
adcx rcx, r15
mov r8, 0xffffffffffffffff 
mov rdx, r14
mulx r15, r14, r8
mov r12, -0x3 
inc r12
adox r14, r13
mulx r10, r13, r9
setc r12b
clc
adcx rdx, r11
adox r13, r15
adcx rbp, rax
mov rdx, 0x0 
adox r10, rdx
adcx r14, rbx
adcx r13, rdi
adcx r10, rcx
movzx r11, r12b
adc r11, 0x0
mov rax, rbp
sub rax, 0x00000001
mov rbx, r14
mov rdi, 0xffffffff00000000 
sbb rbx, rdi
mov r12, r13
sbb r12, r8
mov rcx, r10
sbb rcx, r9
sbb r11, 0x00000000
cmovc rax, rbp
cmovc rcx, r10
cmovc r12, r13
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x10 ], r12
cmovc rbx, r14
mov [ r11 + 0x18 ], rcx
mov [ r11 + 0x0 ], rax
mov [ r11 + 0x8 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 176
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.5640
; seed 3194398325295672 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 942224 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=243, initial num_batches=31): 77657 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.08241883034182955
; number reverted permutation / tried permutation: 75469 / 90001 =83.854%
; number reverted decision / tried decision: 63512 / 89998 =70.570%
; validated in 1.578s
