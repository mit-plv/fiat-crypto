SECTION .text
	GLOBAL fiat_curve25519_solinas_mul
fiat_curve25519_solinas_mul:
sub rsp, 136
mov rax, rdx
mov rdx, [ rdx + 0x10 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], r13
mov [ rsp - 0x40 ], r12
mulx r12, r13, [ rax + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x38 ], r10
mov [ rsp - 0x30 ], rcx
mulx rcx, r10, [ rsi + 0x8 ]
xor rdx, rdx
adox r13, r8
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x28 ], rbx
mulx rbx, r8, [ rsi + 0x18 ]
adcx r8, r11
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x20 ], rcx
mulx rcx, r11, [ rsi + 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x18 ], r10
mov [ rsp - 0x10 ], r14
mulx r14, r10, [ rsi + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x8 ], r10
mov [ rsp + 0x0 ], rcx
mulx rcx, r10, [ rsi + 0x8 ]
adcx r11, r14
mov rdx, 0x0 
adcx rcx, rdx
clc
adcx r15, r8
adcx rbx, r11
adox r12, r15
mov rdx, [ rsi + 0x10 ]
mulx r14, r8, [ rax + 0x10 ]
mov rdx, 0x0 
mov r11, rdx
adcx r11, rcx
adox r8, rbx
setc cl
clc
adcx r9, r13
mov rdx, [ rax + 0x10 ]
mulx r15, r13, [ rsi + 0x8 ]
adcx r13, r12
mov rdx, [ rax + 0x18 ]
mulx r12, rbx, [ rsi + 0x10 ]
adox rbp, r11
movzx rdx, cl
lea rdx, [ rdx + r12 ]
mov rcx, 0x0 
mov r11, rcx
adox r11, rdx
adcx rdi, r8
adcx rbp, [ rsp + 0x0 ]
mov rdx, [ rax + 0x18 ]
mulx r12, r8, [ rsi + 0x18 ]
adox r12, rcx
mov rdx, rcx
adcx rdx, r11
adcx r12, rcx
mov r11, [ rsp - 0x10 ]
test al, al
adox r11, [ rsp - 0x18 ]
adox r9, [ rsp - 0x20 ]
adox r13, [ rsp - 0x28 ]
adox r10, rdi
adox rbx, rbp
adox r8, rdx
adcx r11, [ rsp - 0x30 ]
adcx r9, [ rsp - 0x38 ]
adox r12, rcx
adcx r13, [ rsp - 0x8 ]
adcx r15, r10
adcx r14, rbx
adcx r8, [ rsp - 0x40 ]
adcx r12, rcx
mov rdi, 0x26 
mov rdx, rdi
mulx rbp, rdi, r15
mulx rbx, r10, r14
test al, al
adox rdi, [ rsp - 0x48 ]
mulx r14, r15, r12
adcx r10, r11
adox rbp, r10
mulx r12, r11, r8
adcx r11, r9
adox rbx, r11
adcx r15, r13
adcx r14, rcx
adox r12, r15
adox r14, rcx
mulx r13, r9, r14
xor r13, r13
adox r9, rdi
mov rcx, r13
adox rcx, rbp
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x8 ], rcx
mov rdi, r13
adox rdi, rbx
mov r10, r13
adox r10, r12
mov rbp, r13
cmovo rbp, rdx
mov [ r8 + 0x10 ], rdi
mov [ r8 + 0x18 ], r10
adcx r9, rbp
mov [ r8 + 0x0 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 136
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.6397
; seed 0420530141196134 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 587655 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=170, initial num_batches=31): 54370 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.09252027124758574
; number reverted permutation / tried permutation: 69543 / 90161 =77.132%
; number reverted decision / tried decision: 47851 / 89838 =53.264%
; validated in 0.336s
