SECTION .text
	GLOBAL fiat_p224_mul
fiat_p224_mul:
sub rsp, 176
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, r10
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x8 ]
test al, al
adox rcx, r11
adox r9, r8
mov rdx, [ rax + 0x18 ]
mulx r8, r11, [ rsi + 0x0 ]
adox r11, rbx
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], r15
mov [ rsp - 0x40 ], r14
mulx r14, r15, [ rax + 0x0 ]
mov rdx, 0x0 
adox r8, rdx
adcx rbx, r14
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], rbx
mulx rbx, r14, [ rax + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], r14
mov [ rsp - 0x28 ], r15
mulx r15, r14, [ rax + 0x10 ]
mov rdx, -0x2 
inc rdx
adox rbp, rbx
adox r14, r12
mov rdx, [ rax + 0x10 ]
mulx rbx, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x20 ], r14
mov [ rsp - 0x18 ], rbp
mulx rbp, r14, [ rax + 0x18 ]
adcx r12, rdi
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x10 ], r12
mulx r12, rdi, [ rsi + 0x18 ]
adox rdi, r15
adcx r14, rbx
mov rdx, 0x0 
adox r12, rdx
adc rbp, 0x0
mov r15, r13
xor rbx, rbx
adox r15, r10
mov rdx, 0xffffffff00000000 
mulx r10, r15, r13
adox r15, rcx
mov rdx, [ rsi + 0x8 ]
mulx rbx, rcx, [ rax + 0x0 ]
adcx rcx, r15
mov rdx, 0xffffffff 
mov [ rsp - 0x8 ], r12
mulx r12, r15, r13
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x0 ], rdi
mov [ rsp + 0x8 ], rbp
mulx rbp, rdi, rcx
mov [ rsp + 0x10 ], r14
mulx r14, rbp, r13
setc r13b
clc
adcx rbp, r10
adcx r15, r14
adox rbp, r9
adox r15, r11
mov r9, 0x0 
adcx r12, r9
adox r12, r8
clc
adcx rbx, [ rsp - 0x40 ]
seto r11b
dec r9
movzx r13, r13b
adox r13, r9
adox rbp, rbx
mov rdx, [ rsi + 0x8 ]
mulx r10, r8, [ rax + 0x10 ]
mov rdx, [ rax + 0x18 ]
mulx r14, r13, [ rsi + 0x8 ]
adcx r8, [ rsp - 0x48 ]
adox r8, r15
adcx r13, r10
mov rdx, 0xffffffff00000000 
mulx rbx, r15, rdi
mov r10, 0xffffffff 
mov rdx, rdi
mulx r9, rdi, r10
mov r10, 0xffffffffffffffff 
mov [ rsp + 0x18 ], r8
mov byte [ rsp + 0x20 ], r11b
mulx r11, r8, r10
setc r10b
clc
adcx r8, rbx
adcx rdi, r11
mov rbx, 0x0 
adcx r9, rbx
clc
adcx rdx, rcx
adcx r15, rbp
adox r13, r12
movzx rdx, r10b
lea rdx, [ rdx + r14 ]
movzx rcx, byte [ rsp + 0x20 ]
adox rcx, rdx
adcx r8, [ rsp + 0x18 ]
adcx rdi, r13
adcx r9, rcx
setc r12b
clc
adcx r15, [ rsp - 0x28 ]
mov rbp, 0xffffffffffffffff 
mov rdx, r15
mulx r14, r15, rbp
movzx r14, r12b
adox r14, rbx
adcx r8, [ rsp - 0x38 ]
adcx rdi, [ rsp - 0x10 ]
adcx r9, [ rsp + 0x10 ]
mov r10, r15
mov r11, -0x3 
inc r11
adox r10, rdx
adcx r14, [ rsp + 0x8 ]
mov r10, 0xffffffff00000000 
mov rdx, r15
mulx r13, r15, r10
adox r15, r8
setc cl
clc
adcx r15, [ rsp - 0x30 ]
mulx r8, r12, rbp
setc r11b
clc
adcx r12, r13
mov r13, 0xffffffff 
mulx rbp, rbx, r13
mov rdx, 0xffffffffffffffff 
mulx r10, r13, r15
mov r10, 0xffffffff 
mov rdx, r10
mov byte [ rsp + 0x28 ], r11b
mulx r11, r10, r13
adcx rbx, r8
mov r8, 0x0 
adcx rbp, r8
adox r12, rdi
adox rbx, r9
adox rbp, r14
mov rdi, 0xffffffff00000000 
mov rdx, rdi
mulx r9, rdi, r13
movzx r14, cl
adox r14, r8
mov rcx, 0xffffffffffffffff 
mov rdx, r13
mulx r8, r13, rcx
add r13, r9
adcx r10, r8
adc r11, 0x0
add byte [ rsp + 0x28 ], 0x7F
adox r12, [ rsp - 0x18 ]
adox rbx, [ rsp - 0x20 ]
adcx rdx, r15
adox rbp, [ rsp + 0x0 ]
adcx rdi, r12
adcx r13, rbx
adox r14, [ rsp - 0x8 ]
adcx r10, rbp
adcx r11, r14
seto dl
adc dl, 0x0
movzx rdx, dl
mov r15, rdi
sub r15, 0x00000001
mov r9, r13
mov r8, 0xffffffff00000000 
sbb r9, r8
mov r12, r10
sbb r12, rcx
mov rbx, r11
mov rbp, 0xffffffff 
sbb rbx, rbp
movzx r14, dl
sbb r14, 0x00000000
cmovc r15, rdi
cmovc rbx, r11
cmovc r12, r10
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x10 ], r12
cmovc r9, r13
mov [ r14 + 0x18 ], rbx
mov [ r14 + 0x8 ], r9
mov [ r14 + 0x0 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 176
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.6760
; seed 4458702625791816 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1070699 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=187, initial num_batches=31): 79633 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07437477759855944
; number reverted permutation / tried permutation: 76257 / 90101 =84.635%
; number reverted decision / tried decision: 63868 / 89898 =71.045%
; validated in 1.979s
