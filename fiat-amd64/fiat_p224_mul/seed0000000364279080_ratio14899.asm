SECTION .text
	GLOBAL fiat_p224_mul
fiat_p224_mul:
sub rsp, 152
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x10 ]
mov rdx, [ rax + 0x8 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
xor rdx, rdx
adox r9, r11
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x68 ], r13
mulx r13, r11, [ rsi + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x0 ]
adcx rcx, r15
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r14
adcx rbp, r8
mov rdx, [ rsi + 0x10 ]
mulx r8, rdi, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x48 ], r11
mov [ rsp - 0x40 ], r9
mulx r9, r11, [ rsi + 0x10 ]
adox r11, rbx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x38 ], r11
mulx r11, rbx, [ rax + 0x18 ]
adox rdi, r9
mov rdx, 0x0 
adox r8, rdx
adcx rbx, r12
mov r12, 0xffffffff00000000 
mov rdx, r15
mulx r9, r15, r12
adc r11, 0x0
mov r12, 0xffffffffffffffff 
mov [ rsp - 0x30 ], r8
mov [ rsp - 0x28 ], rdi
mulx rdi, r8, r12
mov r12, 0xffffffff 
mov [ rsp - 0x20 ], r10
mov [ rsp - 0x18 ], r11
mulx r11, r10, r12
xor r12, r12
adox r8, r9
adox r10, rdi
adox r11, r12
adcx rdx, r14
adcx r15, rcx
adcx r8, rbp
adcx r10, rbx
mov rdx, [ rax + 0x8 ]
mulx rcx, r14, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mulx rbx, rbp, [ rax + 0x10 ]
mov rdx, -0x3 
inc rdx
adox r14, r13
adcx r11, [ rsp - 0x18 ]
mov rdx, [ rsi + 0x8 ]
mulx r9, r13, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mulx r12, rdi, [ rsi + 0x8 ]
setc dl
clc
adcx r13, r12
mov r12b, dl
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x10 ], r14
mov [ rsp - 0x8 ], r11
mulx r11, r14, [ rsi + 0x18 ]
adox rbp, rcx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x0 ], rbp
mulx rbp, rcx, [ rsi + 0x8 ]
adox r14, rbx
adcx rcx, r9
seto dl
mov rbx, -0x2 
inc rbx
adox rdi, r15
movzx r15, dl
lea r15, [ r15 + r11 ]
mov rdx, [ rax + 0x18 ]
mulx r11, r9, [ rsi + 0x8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x8 ], r15
mulx r15, rbx, rdi
mov r15, 0xffffffff00000000 
mov rdx, rbx
mov [ rsp + 0x10 ], r14
mulx r14, rbx, r15
adox r13, r8
adcx r9, rbp
adox rcx, r10
mov r8, 0x0 
adcx r11, r8
adox r9, [ rsp - 0x8 ]
movzx r10, r12b
adox r10, r11
mov r12, 0xffffffffffffffff 
mulx r11, rbp, r12
clc
adcx rbp, r14
mov r14, 0xffffffff 
mulx r15, r8, r14
setc r14b
clc
adcx rdx, rdi
adcx rbx, r13
seto dl
mov rdi, -0x2 
inc rdi
adox rbx, [ rsp - 0x20 ]
adcx rbp, rcx
seto r13b
inc rdi
mov rcx, -0x1 
movzx r14, r14b
adox r14, rcx
adox r11, r8
adox r15, rdi
adcx r11, r9
adcx r15, r10
movzx r9, dl
adc r9, 0x0
add r13b, 0x7F
adox rbp, [ rsp - 0x40 ]
adox r11, [ rsp - 0x38 ]
adox r15, [ rsp - 0x28 ]
mov rdx, r12
mulx r10, r12, rbx
mulx r14, r10, r12
mov r8, 0xffffffff00000000 
mov rdx, r8
mulx r13, r8, r12
adcx r10, r13
adox r9, [ rsp - 0x30 ]
mov r13, 0xffffffff 
mov rdx, r12
mulx rdi, r12, r13
adcx r12, r14
seto r14b
inc rcx
adox rdx, rbx
adox r8, rbp
setc dl
clc
adcx r8, [ rsp - 0x48 ]
adox r10, r11
movzx rbx, dl
lea rbx, [ rbx + rdi ]
adox r12, r15
mov rbp, 0xffffffffffffffff 
mov rdx, rbp
mulx r11, rbp, r8
adox rbx, r9
mulx r15, r11, rbp
adcx r10, [ rsp - 0x10 ]
adcx r12, [ rsp + 0x0 ]
movzx r9, r14b
adox r9, rcx
adcx rbx, [ rsp + 0x10 ]
adcx r9, [ rsp + 0x8 ]
mov r14, rbp
mov rdi, -0x3 
inc rdi
adox r14, r8
mov r14, 0xffffffff00000000 
mov rdx, rbp
mulx r8, rbp, r14
adox rbp, r10
setc r10b
clc
adcx r11, r8
adox r11, r12
mulx r8, r12, r13
adcx r12, r15
adox r12, rbx
adcx r8, rcx
adox r8, r9
movzx rdx, r10b
adox rdx, rcx
mov r15, rbp
sub r15, 0x00000001
mov rbx, r11
sbb rbx, r14
mov r10, r12
mov r9, 0xffffffffffffffff 
sbb r10, r9
mov rcx, r8
sbb rcx, r13
sbb rdx, 0x00000000
cmovc rbx, r11
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x8 ], rbx
cmovc r10, r12
mov [ rdx + 0x10 ], r10
cmovc r15, rbp
mov [ rdx + 0x0 ], r15
cmovc rcx, r8
mov [ rdx + 0x18 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 152
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.4899
; seed 2784970562654697 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2192216 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=113, initial num_batches=31): 133342 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06082521065442456
; number reverted permutation / tried permutation: 65237 / 90221 =72.308%
; number reverted decision / tried decision: 57994 / 89778 =64.597%
; validated in 3.691s
