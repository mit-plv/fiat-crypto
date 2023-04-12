SECTION .text
	GLOBAL fiat_curve25519_solinas_mul
fiat_curve25519_solinas_mul:
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx r11, r10, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x48 ], r13
mov [ rsp - 0x40 ], r9
mulx r9, r13, [ rsi + 0x0 ]
test al, al
adox rcx, rdi
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x38 ], r13
mulx r13, rdi, [ rax + 0x8 ]
adox r10, r9
mov rdx, 0x0 
adox rbx, rdx
adcx rdi, rcx
adcx r8, r10
mov r9, rdx
adcx r9, rbx
mov rdx, [ rsi + 0x10 ]
mulx r10, rcx, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x30 ], r15
mulx r15, rbx, [ rax + 0x8 ]
mov rdx, -0x2 
inc rdx
adox rcx, r15
setc r15b
clc
adcx rbp, rcx
adox r10, rdi
mov rdx, [ rax + 0x10 ]
mulx rcx, rdi, [ rsi + 0x10 ]
adox rdi, r8
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x28 ], rcx
mulx rcx, r8, [ rsi + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x20 ], r8
mov [ rsp - 0x18 ], r12
mulx r12, r8, [ rsi + 0x18 ]
adox r8, r9
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x10 ], r12
mulx r12, r9, [ rax + 0x10 ]
movzx rdx, r15b
lea rdx, [ rdx + rcx ]
adcx r9, r10
adcx r13, rdi
mov r15, 0x0 
mov r10, r15
adox r10, rdx
mov rdx, [ rax + 0x18 ]
mulx rcx, rdi, [ rsi + 0x18 ]
adox rcx, r15
adcx r11, r8
mov rdx, r15
adcx rdx, r10
adcx rcx, r15
mov r8, rdx
mov rdx, [ rax + 0x0 ]
mulx r15, r10, [ rsi + 0x8 ]
test al, al
adox r10, r14
adcx rbx, r10
adox r15, rbp
adox r9, [ rsp - 0x18 ]
adcx r15, [ rsp - 0x30 ]
adcx r9, [ rsp - 0x38 ]
adox r13, [ rsp - 0x40 ]
adcx r12, r13
adox r11, [ rsp - 0x20 ]
adcx r11, [ rsp - 0x28 ]
mov rdx, 0x26 
mulx rbp, r14, r12
adox rdi, r8
adcx rdi, [ rsp - 0x10 ]
mulx r10, r8, r11
mov r13, 0x0 
adox rcx, r13
adcx rcx, r13
mulx r11, r12, rdi
xor rdi, rdi
adox r8, rbx
adox r12, r15
mulx rbx, r13, rcx
adcx r14, [ rsp - 0x48 ]
adox r13, r9
adox rbx, rdi
adcx rbp, r8
adcx r10, r12
adcx r11, r13
adc rbx, 0x0
mulx r9, r15, rbx
xor r9, r9
adox r15, r14
mov rdi, r9
adox rdi, rbp
mov rcx, r9
adox rcx, r10
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x8 ], rdi
mov r12, r9
adox r12, r11
mov r14, r9
cmovo r14, rdx
mov [ r8 + 0x18 ], r12
adcx r15, r14
mov [ r8 + 0x0 ], r15
mov [ r8 + 0x10 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.3993
; seed 0062535471188725 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 882250 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=195, initial num_batches=31): 74711 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.08468234627373193
; number reverted permutation / tried permutation: 56612 / 89875 =62.990%
; number reverted decision / tried decision: 46718 / 90124 =51.837%
; validated in 0.545s
