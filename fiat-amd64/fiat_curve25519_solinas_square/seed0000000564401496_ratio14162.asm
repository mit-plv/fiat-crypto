SECTION .text
	GLOBAL fiat_curve25519_solinas_square
fiat_curve25519_solinas_square:
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, [ rsi + 0x0 ]
add r11, r10
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r10, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rdx
adcx r8, rcx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mulx r13, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x10 ]
adcx rcx, r9
adcx r14, r13
mov rdx, -0x2 
inc rdx
adox r10, r8
mov r9, 0x0 
adcx r15, r9
clc
adcx rax, rax
adox rbx, rcx
mov r8, r9
adox r8, r14
mov r13, r9
adox r13, r15
seto cl
mov r14, -0x3 
inc r14
adox r12, rax
adcx r11, r11
mov rdx, [ rsi + 0x8 ]
mulx rax, r15, rdx
adcx r10, r10
adcx rbx, rbx
adcx r8, r8
mov rdx, [ rsi + 0x18 ]
mulx r14, r9, rdx
adox r15, r11
adox rax, r10
mov rdx, [ rsi + 0x10 ]
mulx r10, r11, rdx
adox r11, rbx
adox r10, r8
adcx r13, r13
adox r9, r13
mov rdx, 0x26 
mulx r8, rbx, r11
movzx r11, cl
mov r13, 0x0 
adcx r11, r13
movzx r13, cl
lea r13, [ r13 + r11 ]
adox r13, r14
mulx r14, rcx, r10
add rcx, r12
mulx r10, r12, r9
adcx r12, r15
mulx r9, r15, r13
adcx r15, rax
adc r9, 0x0
xor rax, rax
adox rbx, rbp
adox r8, rcx
adox r14, r12
adox r10, r15
adox r9, rax
mulx r11, rbp, r9
adcx rbp, rbx
mov r11, rax
adcx r11, r8
mov r13, rax
adcx r13, r14
mov [ rdi + 0x8 ], r11
mov [ rdi + 0x10 ], r13
mov rcx, rax
adcx rcx, r10
mov [ rdi + 0x18 ], rcx
mov r12, rax
cmovc r12, rdx
mov r15, -0x3 
inc r15
adox rbp, r12
mov [ rdi + 0x0 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.4162
; seed 3342048534826158 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 399729 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=542, initial num_batches=31): 65908 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.1648817073567342
; number reverted permutation / tried permutation: 75621 / 89922 =84.096%
; number reverted decision / tried decision: 53865 / 90077 =59.799%
; validated in 0.224s
