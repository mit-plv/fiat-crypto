SECTION .text
	GLOBAL fiat_curve25519_solinas_mul
fiat_curve25519_solinas_mul:
mov rax, rdx
mov rdx, [ rdx + 0x8 ]
mulx r11, r10, [ rsi + 0x18 ]
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x0 ]
test al, al
adox rcx, r14
adcx r9, rcx
adox r10, r12
adcx r8, r10
mov rdx, [ rax + 0x10 ]
mulx r14, r12, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx r10, rcx, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x18 ]
mov rdx, 0x0 
adox rdi, rdx
mov [ rsp - 0x48 ], r14
mov r14, rdx
adcx r14, rdi
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x40 ], rcx
mulx rcx, rdi, [ rsi + 0x0 ]
adc r10, 0x0
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x38 ], rbp
mov [ rsp - 0x30 ], r13
mulx r13, rbp, [ rax + 0x0 ]
test al, al
adox rbp, rcx
adox r13, r9
mov rdx, [ rsi + 0x10 ]
mulx rcx, r9, [ rax + 0x10 ]
adox r9, r8
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x28 ], rcx
mulx rcx, r8, [ rsi + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x20 ], rdi
mov [ rsp - 0x18 ], r15
mulx r15, rdi, [ rsi + 0x18 ]
adcx r8, rbp
adox rdi, r14
mov rdx, [ rax + 0x0 ]
mulx rbp, r14, [ rsi + 0x8 ]
adcx r12, r13
mov rdx, 0x0 
mov r13, rdx
adox r13, r10
adcx rbx, r9
mov rdx, [ rsi + 0x0 ]
mulx r9, r10, [ rax + 0x0 ]
setc dl
clc
adcx r14, r9
adcx rbp, r8
adcx rcx, r12
seto r8b
mov r12, -0x1 
inc r12
mov r9, -0x1 
movzx rdx, dl
adox rdx, r9
adox rdi, r11
adcx rbx, [ rsp - 0x18 ]
mov r11, r12
adox r11, r13
mov rdx, [ rsi + 0x18 ]
mulx r12, r13, [ rax + 0x18 ]
seto dl
inc r9
adox r14, [ rsp - 0x20 ]
movzx r9, r8b
lea r9, [ r9 + r12 ]
mov r8, 0x0 
movzx rdx, dl
lea r9, [ r9 + r8 ]
lea r9, [ r9 + rdx ]
adox rbp, [ rsp - 0x30 ]
adox rcx, [ rsp - 0x38 ]
adcx rdi, [ rsp - 0x40 ]
adox rbx, [ rsp - 0x48 ]
adox rdi, [ rsp - 0x28 ]
adcx r13, r11
adox r15, r13
adcx r9, r8
mov rdx, 0x26 
mulx r12, r11, r15
adox r9, r8
mulx r15, r13, rdi
xor rdi, rdi
adox r13, r14
mulx r14, r8, r9
adox r11, rbp
mulx r9, rbp, rbx
adcx rbp, r10
adox r8, rcx
adcx r9, r13
adcx r15, r11
adox r14, rdi
adcx r12, r8
adc r14, 0x0
mulx rcx, r10, r14
xor rcx, rcx
adox r10, rbp
mov rdi, rcx
adox rdi, r9
mov rbx, rcx
adox rbx, r15
mov r13, rcx
adox r13, r12
mov r11, rcx
cmovo r11, rdx
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x10 ], rbx
mov [ rbp + 0x8 ], rdi
adcx r10, r11
mov [ rbp + 0x0 ], r10
mov [ rbp + 0x18 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.5929
; seed 3372518405759626 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 596053 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=172, initial num_batches=31): 54273 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.09105398345449146
; number reverted permutation / tried permutation: 67094 / 90137 =74.436%
; number reverted decision / tried decision: 46661 / 89862 =51.925%
; validated in 0.341s
