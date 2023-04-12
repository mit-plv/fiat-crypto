SECTION .text
	GLOBAL fiat_p256_mul
fiat_p256_mul:
sub rsp, 176
mov rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rax + 0x18 ]
mulx r8, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x10 ]
test al, al
adox r9, r11
adox rbp, rbx
adox rcx, r12
mov rdx, [ rsi + 0x18 ]
mulx rbx, r11, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x18 ]
adcx r12, rbx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x60 ], r14
mulx r14, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x8 ]
mov rdx, 0x0 
adox r8, rdx
mov [ rsp - 0x48 ], r12
mov r12, -0x3 
inc r12
adox r15, r14
mov rdx, [ rsi + 0x0 ]
mulx r12, r14, [ rax + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x40 ], r11
mov [ rsp - 0x38 ], r15
mulx r15, r11, r14
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], rbx
mov [ rsp - 0x28 ], r8
mulx r8, rbx, [ rax + 0x10 ]
adox rbx, rdi
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x20 ], rbx
mulx rbx, rdi, [ rsi + 0x18 ]
mov rdx, 0xffffffff 
mov [ rsp - 0x18 ], rcx
mov [ rsp - 0x10 ], rbp
mulx rbp, rcx, r14
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x8 ], r9
mov [ rsp + 0x0 ], r10
mulx r10, r9, [ rax + 0x18 ]
adcx rdi, r13
adox r9, r8
mov rdx, [ rsi + 0x18 ]
mulx r8, r13, [ rax + 0x18 ]
adcx r13, rbx
mov rdx, 0x0 
adox r10, rdx
adc r8, 0x0
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x8 ], r8
mulx r8, rbx, [ rax + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x10 ], r13
mov [ rsp + 0x18 ], rdi
mulx rdi, r13, [ rax + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x20 ], r10
mov [ rsp + 0x28 ], r9
mulx r9, r10, [ rax + 0x10 ]
add rcx, r15
adc rbp, 0x0
xor rdx, rdx
adox r11, r14
adcx rbx, r12
adox rcx, rbx
adcx r10, r8
adcx r13, r9
adcx rdi, rdx
clc
adcx rcx, [ rsp + 0x0 ]
adox rbp, r10
mov r11, 0xffffffffffffffff 
mov rdx, r11
mulx r12, r11, rcx
adcx rbp, [ rsp - 0x8 ]
mov r15, 0xffffffff00000001 
mov rdx, r15
mulx r8, r15, r14
adox r15, r13
adcx r15, [ rsp - 0x10 ]
adox r8, rdi
adcx r8, [ rsp - 0x18 ]
setc r14b
movzx r14, r14b
adox r14, [ rsp - 0x28 ]
mov r9, 0xffffffff 
mov rdx, rcx
mulx rbx, rcx, r9
clc
adcx rcx, r12
mov r10, 0x0 
adcx rbx, r10
clc
adcx r11, rdx
adcx rcx, rbp
adcx rbx, r15
mov r11, 0xffffffff00000001 
mulx rdi, r13, r11
seto dl
mov r12, -0x3 
inc r12
adox rcx, [ rsp - 0x30 ]
adox rbx, [ rsp - 0x38 ]
adcx r13, r8
adox r13, [ rsp - 0x20 ]
adcx rdi, r14
movzx rbp, dl
adcx rbp, r10
adox rdi, [ rsp + 0x28 ]
mov r15, 0xffffffffffffffff 
mov rdx, rcx
mulx r8, rcx, r15
mulx r10, r14, r9
clc
adcx r14, r8
mov r8, 0x0 
adcx r10, r8
clc
adcx rcx, rdx
adcx r14, rbx
adcx r10, r13
mulx rbx, rcx, r11
adcx rcx, rdi
adox rbp, [ rsp + 0x20 ]
adcx rbx, rbp
seto dl
mov r13, -0x3 
inc r13
adox r14, [ rsp - 0x40 ]
movzx r13, dl
adcx r13, r8
mov rdx, r14
mulx rdi, r14, r9
mulx r8, rbp, r15
clc
adcx r14, r8
mov r8, 0x0 
adcx rdi, r8
adox r10, [ rsp - 0x48 ]
clc
adcx rbp, rdx
adox rcx, [ rsp + 0x18 ]
adox rbx, [ rsp + 0x10 ]
adcx r14, r10
mulx r10, rbp, r11
adcx rdi, rcx
adcx rbp, rbx
adox r13, [ rsp + 0x8 ]
adcx r10, r13
seto dl
adc dl, 0x0
movzx rdx, dl
mov rcx, r14
sub rcx, r15
mov rbx, rdi
sbb rbx, r9
mov r13, rbp
sbb r13, 0x00000000
mov r8, r10
sbb r8, r11
movzx r12, dl
sbb r12, 0x00000000
cmovc rbx, rdi
cmovc rcx, r14
cmovc r8, r10
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x8 ], rbx
mov [ r12 + 0x18 ], r8
cmovc r13, rbp
mov [ r12 + 0x0 ], rcx
mov [ r12 + 0x10 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 176
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.9303
; seed 3185071681623804 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 914464 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=184, initial num_batches=31): 71538 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07822943276061169
; number reverted permutation / tried permutation: 75985 / 89644 =84.763%
; number reverted decision / tried decision: 63198 / 90355 =69.944%
; validated in 1.204s
